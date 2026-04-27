<!-- Thank you for filing a report! Please ensure you have filled out all -->
<!-- sections, as it help us to address the problem effectively. -->

<!-- NOTE: Please try to ensure the bug can be produced on the latest release of -->
<!-- Apalache. See https://github.com/apalache-mc/apalache/releases -->

## Impact

<!-- Whether this is blocking your work or whether you are able to proceed using -->
<!-- workarounds or alternative approaches. -->

## Input specification

```
---- MODULE AccordSpec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets, ExtraConfiguration, typedefs

(*

A TLA+ specification of the EPaxos* protocol from the following ........ paper:
Accord: Fast Geo-Distributed Transactions in Apache Cassandra
Benedict Elliott Smith, Fedor Ryabinin, Alexey Gotsman, and Pierre Sutra.

Link

This file contains the specification of the Accord protocol on a single shard,
corresponding to Figures 2 and 5 in the paper.

Author: Alexandre SIRET

*)



(***************************************************************************)
(* Constants : these are model checking parameters                         *)
(***************************************************************************)

CONSTANTS 
    \* @type: Set(Int);
    Proc,       \* The set of processes, all shards use same numbered processes
    \* @type: Set(Int);
    Id,         \* The set of command IDs
    \* @type: Int;
    F,         
    \* @type: Int;
    E,
    \* @type: Int;
    Bottom,     \* The bottom value for the command payload
    \* @type: Int;
    NoProc,      \* A special value representing no process
    \* @type: Int;
    Nop,           \* special Nop payload
    \* @type: Int;
    NumberOfRecoveryAttempts \* constant used to cap the amount of recovery attempts, this cap is per process command pair.
    \* The following constants are also imported from the ExtraConfiguration module. Look at the file for more details.
    \* ConflictPairs is used to define the conflict relation between transactions
    \* initTimestampConstant gives an initial timestamp value for each transaction

N == Cardinality(Proc)
Max(a, b) == IF a > b THEN a ELSE b
ASSUME N >= Max(2*E+F-1, 2*F+1)

\* Phase constants
InitialPhase == 1
PreAcceptedPhase == 2
AcceptedPhase == 3
CommittedPhase == 4
StablePhase == 5


\* @type: SPEED;
Fast == "Fast_OF_SPEED"
\* @type: SPEED;
Slow == "Slow_OF_SPEED"

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)


VARIABLES
    \* @type: Int -> Int -> Int;
    bal,           \* bal[p][id] = current ballot known by process p for transaction id
    \* @type: Int -> Int -> Int;
    phase,         \* phase[p][id] \in {InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase, StablePhase}
    \* @type: Int -> Int -> Int;
    txn,           \* txn[p][id] = command payload at p
    \* @type: Int -> Int -> Set(Int);
    dep,           \* dep[p][id] = final dependency set (accepted or committed)
    \* @type: Int -> Int -> $timestamp;
    ts,            \* ts[p][id] = timestamp at p, timestamp is a couple of (t, id) ts.t is the timestamp value, ts.id is it's id.
    \* @type: Int -> Int -> Int;
    abal,          \* abal[p][id] = the last ballot where p accepted a slow path value
    \* @type: Set($message);
    msgs,          \* set of network messages
    \* @type: Set(Int);
    submitted,     \* set of submitted command ids
    \* @type: Int -> Int;
    initCoord,     \* initCoord[id] = process that submitted id, it is the pair p
    \* @type: Seq($timestamp);
    initTimestamp, \* id's initial timestamp defined on submit using initTimestampConstant
    \* @type: Int -> Int -> Int;
    recovered,     \* recovered[p][id] = counter of times recovery is invoked
    
    \* the following variables are used in recovery to : 
    \*              -persist local state to the post waiting operation
    \*              -keep track of when we are allowed to trigger the post waiting operation
    \* @type: Int -> Int -> Set(<<Int,Int>>);
    Wvar,
    \* @type: Int -> Int -> Int;           
    TXvar,
    \* @type: Int -> Int -> Set(Int);
    Dvar,
    \* @type: Int -> Int -> Set(Int);
    Qvar,
    \* @type: Int -> Int -> Bool;
    postWaitingFlag,
    \* @type: Int -> Int -> Int;
    recoveryAttemptBal

vars == << bal, phase, txn, dep, ts, abal, msgs, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar >>

(***************************************************************************)
(* Init of all the variables                                               *)
(***************************************************************************)

Init == 
    /\ bal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ phase = [p \in Proc |-> [id \in Id |-> InitialPhase]]
    /\ txn = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\ dep = [p \in Proc |-> [id \in Id |-> {}]]
    /\ ts = [p \in Proc |-> [id \in Id |-> [t |-> 0, id |-> 0]]] 
    /\ abal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ msgs = {}
    /\ submitted = {}
    /\ initCoord = [id \in Id |-> NoProc]
    /\ recovered = [p \in Proc |-> [id \in Id |-> 0]]
    /\ Wvar = [p \in Proc |-> [id \in Id |-> {}]]
    /\ TXvar = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\ Dvar = [p \in Proc |-> [id \in Id |-> {}]]
    /\ postWaitingFlag = [p \in Proc |-> [id \in Id |-> FALSE]]
    /\ recoveryAttemptBal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ initTimestamp = initTimestampConstant
    /\ Qvar = [p \in Proc |-> [id \in Id |-> {}]]


(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)

\* Relation on timestamps
\* @type: ($timestamp, $timestamp) => Bool; 
LessThanTs(ts1, ts2) ==
    IF ts1.id = NoProc THEN TRUE
    ELSE IF ts2.id = NoProc THEN FALSE
    ELSE IF ts1.t < ts2.t THEN TRUE
    ELSE IF ts1.t > ts2.t THEN FALSE
    ELSE ts1.id < ts2.id

MaxTs(ts1, ts2) ==
    IF LessThanTs(ts1, ts2) THEN ts2 ELSE ts1

MaxTsInSet(S) ==
    CHOOSE ts1 \in S : \A ts2 \in S :
                            ts2 # ts1 => LessThanTs(ts2, ts1)

\* ConflictPairs is a model constant defined in ExtraConfiguration
Conflicts(id1, id2) ==
    <<id1, id2>> \in ConflictPairs \/ <<id2, id1>> \in ConflictPairs

IsQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - F
IsFastQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - E

\* This finds all commands that a process knows of, (checks in payload and in dependencies)
SeenIds(p) ==
    {id \in Id : 
        \/ txn[p][id] # Bottom
        \/ \E id2 \in Id : id \in dep[p][id2]}


(***************************************************************************)
(* State changing Actions                                                  *)
(***************************************************************************)

\* These operators are the insides of all the 'when received' a single message operations, this split allows handling self addressed
\* messages by  using the corresponding Apply and computation operations.
\* For example, after we submit a command, we :
\*        - send PreAccept messages to everyone except ourselves
\*        - apply the PreAccept operation on ourselves using ApplyPreAccept()
\*        - Compute the t and D values (see pseudocode) with PreAcceptComputations()
\*        - send PreAcceptOk(id, t, d) to ourselves.

PreAcceptComputations(p, q, id, tx, initTs) ==
    LET setOfConflictingTs == {ts[p][id2] : id2 \in { id2 \in Id : ts[p][id2].id # NoProc /\ Conflicts(id, id2)}}
        D == { id2 \in SeenIds(p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], initTs) ) }
    IN
    LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
    IN
    LET finalTs == MaxTs(initTs, [t |-> tval, id |-> q])
    IN
    [finalTs |-> finalTs, D |-> D]

ApplyPreAccept(p, id, tx, finalTs, D0) ==
    /\  bal[p][id] = 0
    /\  phase[p][id] = InitialPhase
    /\  txn' = [txn EXCEPT ![p][id] = tx]
    /\  phase' = [phase EXCEPT ![p][id] = PreAcceptedPhase]
    /\  ts' = [ts EXCEPT ![p][id] = finalTs]
    /\  dep' = [dep EXCEPT ![p][id] = D0]

AcceptComputations(p, id, t) ==
    LET Dq == { id2 \in SeenIds(p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], t)) }
    IN
    [Dq |-> Dq] 

ApplyAccept(p, b, id, t, D, tx) ==
    /\  bal[p][id] <= b
    /\  (b = 0 => phase[p][id] = PreAcceptedPhase)
    /\  IF b > 0 THEN txn'  = [txn  EXCEPT ![p][id] = tx] ELSE UNCHANGED txn
    /\  bal'  = [bal  EXCEPT ![p][id] = b]
    /\  abal' = [abal EXCEPT ![p][id] = b]
    /\  ts'   = [ts  EXCEPT ![p][id] = t]
    /\  dep'  = [dep  EXCEPT ![p][id] = D]
    /\  phase' = [phase EXCEPT ![p][id] = AcceptedPhase]

\* no local computations when receiving a commit message

ApplyCommit(p, b, id, t, D, tx, stable) ==
    /\ bal[p][id] = b
    /\ b = 0 => phase[p][id] \in {PreAcceptedPhase, AcceptedPhase}
    /\ IF b > 0 THEN txn'  = [txn  EXCEPT ![p][id] = tx] ELSE UNCHANGED txn
    /\ abal' = [abal EXCEPT ![p][id] = b]
    /\ ts'   = [ts  EXCEPT ![p][id] = t]
    /\ dep' = [dep EXCEPT ![p][id] = D]
    /\ IF stable THEN phase' = [phase EXCEPT ![p][id] = StablePhase] ELSE phase' = [phase EXCEPT ![p][id] = CommittedPhase]

\* no local computations when receiving a stable message

ApplyStable(p, b, id) ==
    /\ bal[p][id] = b
    /\ phase[p][id] = CommittedPhase
    /\ phase' = [phase EXCEPT ![p][id] = StablePhase]


RecoverComputations(p, id) ==
    LET D == IF phase[p][id] \notin {InitialPhase, PreAcceptedPhase} THEN dep[p][id]
             ELSE dep[p][id] \cup {id2 \in SeenIds(p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
    IN
    LET S == {id2 \in SeenIds(p) : (id2 # id /\ Conflicts(id, id2) /\ txn[p][id2] # Nop /\ id \notin dep[p][id2]
                                             /\ ( (phase[p][id2] \in {CommittedPhase, StablePhase} /\ LessThanTs(initTimestamp[id], ts[p][id2]))  
                                                  \/ (phase[p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id], initTimestamp[id2])) 
                                                )                    
                                   ) 
            }
        \* @type: Set(<<Int, Int>>);
        W == {<<id3, abal[p][id3]>> : 
                    id3 \in { id2 \in SeenIds(p) : 
                                    (id2 # id /\ Conflicts(id, id2) /\ txn[p][id2] # Nop /\ id \notin dep[p][id2] 
                                    /\  ((phase[p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) /\ LessThanTs(initTimestamp[id], ts[p][id2]))
                                          \/ (phase[p][id2] = PreAcceptedPhase /\ LessThanTs(initTimestamp[id2], initTimestamp[id]))
                                        )
                                    )}}
        WP == {id2 \in SeenIds(p) : id2 # id /\ Conflicts(id, id2) /\ phase[p][id2] = PreAcceptedPhase 
                                             /\ LessThanTs(initTimestamp[id], initTimestamp[id2]) /\ id \notin dep[p][id2] 
              }
    IN
    [D |-> D, S |-> S, W |-> W, WP |-> WP]

ApplyRecover(p, b, id, tx) ==
    /\  bal[p][id] < b
    /\  bal' = [bal  EXCEPT ![p][id] = b]
    /\  IF phase[p][id] = InitialPhase THEN  txn' = [txn  EXCEPT ![p][id] = tx] ELSE UNCHANGED txn

(***************************************************************************)
(* Message handling Actions                                                *)
(***************************************************************************)


(* Submit (lines 4-6) *)

Submit(p, id) ==
    /\  id \notin submitted
    /\  LET tx == id \* We use id as command payload, since the actual payload does not matter here.
            earlierInitTimestamps == { initTimestamp[id2] : id2 \in {id1 \in Id : initCoord[id1] = p /\ LessThanTs(initTimestamp[id], initTimestamp[id1])} }
        IN 
        LET initTimestampVal == IF earlierInitTimestamps = {} THEN initTimestamp[id].t ELSE MaxTsInSet(earlierInitTimestamps).t + 1
        IN
        LET newInitTimestamp == [id |-> p, t |-> initTimestampVal]
        IN
        \* making sure that this process has not already submitted a command with a greater timestamp than the one we are currently submitting.
        /\ initTimestamp' = [initTimestamp EXCEPT ![id] = newInitTimestamp]
        /\ submitted' = submitted \cup {id}
        /\ initCoord' = [initCoord EXCEPT ![id] = p]
        /\  LET computations == PreAcceptComputations(p, p, id, tx, newInitTimestamp)
            IN
            /\ ApplyPreAccept(p, id, tx, computations.finalTs, computations.D) \* slightly confusing here but computations.D is D0 here since this is the self addressed message.
            /\ msgs' = msgs \cup { PreAcceptMsg(p, q, id, tx, computations.D) : q \in Proc \ {p} } 
                            \cup { PreAcceptOKMsg(p, p, id, computations.finalTs, computations.D) }
    /\ UNCHANGED <<bal, abal, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar>> 


(* HandlePreAccept (lines 7-14) *)

HandlePreAccept(m) ==
    /\  VariantTag(m) = "PreAcceptMessage"
    /\  LET inner == UnwrapPreAccept(m)
        IN
        LET p  == inner.to
            q  == inner.from
            id == inner.body.id
            tx  == inner.body.tx
            D0 == inner.body.D0
        IN 
        LET computations == PreAcceptComputations(p, q, id, tx, initTimestamp[id])
        IN
        /\ ApplyPreAccept(p, id, tx, computations.finalTs, D0)
        /\ msgs' = (msgs \ {m}) \cup { PreAcceptOKMsg(p, q, id, computations.finalTs, computations.D) }
    /\ UNCHANGED <<bal, abal, submitted, initCoord, recovered, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Wvar, Qvar, initTimestamp>>



(* HandlePreAcceptOk (lines 15-23) *)

HandlePreAcceptOK(p, id) ==
    /\  bal[p][id] = 0
    /\  phase[p][id] = PreAcceptedPhase
    /\  LET  quorumOfMessages ==
            { m \in msgs :
                /\  VariantTag(m) = "PreAcceptOKMessage"
                /\  LET inner == UnwrapPreAcceptOK(m)
                    IN
                    /\ inner.body.id = id
                    /\ inner.to = p
            }
        IN
        /\  IsQuorumSized(quorumOfMessages)
        /\  LET largestFastQuorum ==
                { m \in quorumOfMessages : UnwrapPreAcceptOK(m).body.tq = initTimestamp[id]  }
            IN
            IF IsFastQuorumSized(largestFastQuorum) THEN
                    LET D == dep[p][id] \cup UNION { UnwrapPreAcceptOK(m).body.Dq : m \in largestFastQuorum }
                    IN
                    /\  ApplyCommit(p, 0, id, initTimestamp[id], D, txn[p][id], TRUE)             
                    /\  msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q, 0, id, initTimestamp[id], D, Fast, txn[p][id]) : q \in Proc \ {p} }
                                                          \cup { StableMsg(p, q, 0, id) : q \in Proc \ {p} }
                    /\  UNCHANGED bal
            ELSE     
                    LET D == UNION { UnwrapPreAcceptOK(m).body.Dq : m \in quorumOfMessages }
                        t == MaxTsInSet({ UnwrapPreAcceptOK(m).body.tq : m \in quorumOfMessages })
                    IN
                    LET computations == AcceptComputations(p, id, t)
                    IN 
                    /\  ApplyAccept(p, 0, id, t, D, txn[p][id])
                    /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, 0, id, t, D, txn[p][id]) : q \in Proc \ {p} } 
                                                          \cup { AcceptOKMsg(p, p, 0, id, computations.Dq) }
    /\ UNCHANGED <<submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar>>
       


(* HandleAccept (lines 24-32) *)                        

HandleAccept(m) ==
    /\  VariantTag(m) = "AcceptMessage"
    /\  LET inner == UnwrapAccept(m)
        IN
        LET p  == inner.to
            q  == inner.from
            b  == inner.body.b
            id == inner.body.id
            t  == inner.body.t
            D  == inner.body.D
            tx  == inner.body.tx
        IN
        LET computations == AcceptComputations(p, id, t)
        IN
        /\  ApplyAccept(p, b, id, t, D, tx)
        /\  msgs' = (msgs \ {m}) \cup { AcceptOKMsg(p, q, b, id, computations.Dq) }
    /\ UNCHANGED <<submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar>>

(* HandleAcceptOk (lines 33-35) *)

HandleAcceptOK(p, id) ==
    /\  phase[p][id] = AcceptedPhase
    /\  LET  quorumOfMessages == 
                { m \in msgs :
                    /\  VariantTag(m) = "AcceptOKMessage"
                    /\  LET inner == UnwrapAcceptOK(m)
                        IN
                        /\  inner.to = p
                        /\  inner.body.b = bal[p][id]
                        /\  inner.body.id = id
                }  
        IN
        /\  IsQuorumSized(quorumOfMessages)
        /\  LET D == dep[p][id] \cup UNION { UnwrapAcceptOK(m).body.Dq : m \in quorumOfMessages }
            IN
            /\  ApplyCommit(p, bal[p][id], id, ts[p][id], D, txn[p][id], FALSE)
            /\  msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q, bal[p][id], id, ts[p][id], D, Slow, txn[p][id]) : q \in Proc \ {p} } 
                                                  \cup { CommitOkMsg(p, p, bal[p][id], id) }
    /\ UNCHANGED <<bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar>>

(* HandleCommit (lines 36-43) *)

HandleCommit(m) ==
    /\  VariantTag(m) = "CommitMessage"
    /\  LET inner == UnwrapCommit(m)
        IN
        LET p  == inner.to
            q  == inner.from
            b  == inner.body.b
            id == inner.body.id
            tx == inner.body.tx
            D  == inner.body.D
            pathSpeed == inner.body.pathSpeed
            t == inner.body.t
       IN
       /\ ApplyCommit(p, b, id, t, D, tx, FALSE)
       /\ IF pathSpeed = Slow THEN msgs' = (msgs \ {m}) \cup { CommitOkMsg(p, q, b, id) }  ELSE msgs' = msgs \ {m}
       /\ UNCHANGED <<bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, initTimestamp>>




(* HandleCommitOk (lines 44-46) *)

HandleCommitOK(p, id) ==
    /\ phase[p][id] = CommittedPhase
    /\ LET  quorumOfMessages == 
            { m \in msgs :
                /\  VariantTag(m) = "CommitOKMessage"
                /\  LET inner == UnwrapCommitOK(m)
                    IN
                    /\ inner.to = p
                    /\ inner.body.b = bal[p][id]
                    /\ inner.body.id = id 
            }
        IN
        /\ IsQuorumSized(quorumOfMessages)
        /\ ApplyStable(p, bal[p][id], id)
        /\ msgs' = (msgs \ quorumOfMessages) \cup { StableMsg(p, q, bal[p][id], id) : q \in Proc \ {p} }
    /\ UNCHANGED << bal, txn, dep, ts, abal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar >>

(* HandleStable (lines 47-49) *)

HandleStable(m) ==
    /\  VariantTag(m) = "StableMessage"
    /\  LET inner == UnwrapStable(m)
        IN
        LET p  == inner.to
            q  == inner.from
            b  == inner.body.b
            id == inner.body.id
        IN
        /\ ApplyStable(p, b, id)
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<bal, submitted, initCoord, dep, abal, txn, ts, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar>>

(* StartRecover (lines 50-53) *)

StartRecover(p, id) ==
    /\ recovered[p][id] < NumberOfRecoveryAttempts
    /\ id \in SeenIds(p)
    /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE] 
    /\ recovered' = [recovered EXCEPT ![p][id] = recovered[p][id] + 1]
    \* Ballots owned by p are of the form k*N + p.
    /\  LET k == ((bal[p][id] - p + N) \div N) IN
        LET b == k * N + p
        IN
        /\  ApplyRecover(p, b, id, txn[p][id])
        /\  LET computations == RecoverComputations(p, id)
            IN
            LET D == computations.D
                S == computations.S
                W == computations.W
                WP == computations.WP
            IN
            IF S # {}
            THEN IF phase[p][id] # InitialPhase THEN msgs' =  msgs \cup { RecoverOkMsg(p, p, b, id, abal[p][id], txn[p][id], ts[p][id], D, phase[p][id], TRUE, W, WP) } \cup { RecoverMsg(p, q, b, id, txn[p][id]) : q \in Proc \ {p} }
                    ELSE                             msgs' =  msgs \cup { RecoverOkMsg(p, p, b, id, abal[p][id], Nop, ts[p][id], D, phase[p][id], TRUE, W, WP) }        \cup { RecoverMsg(p, q, b, id, Nop)        : q \in Proc \ {p} }
            ELSE IF phase[p][id] # InitialPhase THEN msgs' =  msgs \cup { RecoverOkMsg(p, p, b, id, abal[p][id], txn[p][id], ts[p][id], D, phase[p][id], FALSE, W, WP) }\cup { RecoverMsg(p, q, b, id, txn[p][id]) : q \in Proc \ {p} }
                    ELSE                             msgs' =  msgs \cup { RecoverOkMsg(p, p, b, id, abal[p][id], Nop, ts[p][id], D, phase[p][id], FALSE, W, WP) }       \cup { RecoverMsg(p, q, b, id, Nop)        : q \in Proc \ {p} }
    /\ UNCHANGED <<phase, dep, ts, abal, submitted, initCoord, Wvar, TXvar, Dvar, initTimestamp, Qvar, recoveryAttemptBal>>


(* HandleRecover (lines 53-64) *)

HandleRecover(m) ==
    /\  VariantTag(m) = "RecoverMessage"
    /\  LET inner == UnwrapRecover(m)
        IN
        LET p  == inner.to 
            q == inner.from
            b == inner.body.b
            id == inner.body.id
            tx == inner.body.tx
        IN 
        /\  LET computations == RecoverComputations(p, id)
            IN
            LET D == computations.D
                S == computations.S
                W == computations.W
                WP == computations.WP
            IN
            /\  ApplyRecover(p, b, id, tx)
            /\  IF S # {}
                THEN msgs' = (msgs \ {m})  \cup { RecoverOkMsg(p, q, b, id, abal[p][id], txn'[p][id], ts[p][id], D, phase[p][id], TRUE, W, WP) }
                ELSE msgs' = (msgs \ {m})  \cup { RecoverOkMsg(p, q, b, id, abal[p][id], txn'[p][id], ts[p][id], D, phase[p][id], FALSE, W, WP) }
    /\ UNCHANGED <<submitted, initCoord, dep, abal, ts, phase, recovered, TXvar, Dvar, postWaitingFlag, Wvar, recoveryAttemptBal, initTimestamp, Qvar>>

(* HandleRecoverOK (lines 65-76 + 82) *)

HandleRecoverOK(p, id) ==
    /\  LET quorumOfMessages ==
            { m \in msgs :
                /\  VariantTag(m) = "RecoverOKMessage"
                /\  LET inner == UnwrapRecoverOK(m)
                    IN
                    /\ inner.to = p 
                    /\ inner.body.id = id 
                    /\ inner.body.b = bal[p][id]
                    /\ abal[p][id] < inner.body.b 
            }
        IN
        LET innerMsgs == { UnwrapRecoverOK(m) : m \in quorumOfMessages }
        IN
        /\ IsQuorumSized(quorumOfMessages) 
        /\  LET Q == { UnwrapRecoverOK(m).from : m \in quorumOfMessages}
                Abals == { UnwrapRecoverOK(m).body.abalq : m \in quorumOfMessages }
                bmax == CHOOSE val \in Abals : \A val2 \in Abals : val >= val2
                U == { n \in innerMsgs : n.body.abalq = bmax }
            IN
            /\  IF (\E n \in U :
                        /\ n.body.phaseq  = StablePhase)
                THEN
                        /\  LET n == CHOOSE msg \in U :
                                        msg.body.phaseq = StablePhase
                            IN
                            /\ ApplyCommit(p, bal[p][id], id, n.body.tq, n.body.depq, n.body.txq, FALSE)
                            /\ ApplyStable(p, bal[p][id], id)
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q, bal[p][id], id, n.body.tq, n.body.depq, Fast, n.body.txq) : q \in Proc \ {p} }
                                                                 \cup { StableMsg(p, q, bal[p][id], id) : q \in Proc \ {p} }
                            /\ UNCHANGED <<bal, TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = CommittedPhase)
                THEN
                        /\  LET n == CHOOSE msg \in U :
                                        msg.body.phaseq = CommittedPhase
                            IN
                            /\ ApplyCommit(p, bal[p][id], id, n.body.tq, n.body.depq, n.body.txq, FALSE)
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q, bal[p][id], id, n.body.tq, n.body.depq, Slow, n.body.txq) : q \in Proc \ {p} } 
                                                                 \cup { CommitOkMsg(p, p, bal[p][id], id) }
                            /\ UNCHANGED <<bal , TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>  
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = AcceptedPhase)
                THEN    
                        /\  LET n == CHOOSE msg \in U :
                                msg.body.phaseq = AcceptedPhase
                            IN
                            LET computations == AcceptComputations(p, id, n.body.tq)
                            IN
                            /\ ApplyAccept(p, bal[p][id], id, n.body.tq, n.body.depq, n.body.txq) 
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, n.body.tq, n.body.depq, n.body.txq) : q \in Proc \ {p} } 
                                                                 \cup { AcceptOKMsg(p, p, bal[p][id], id, computations.Dq) }
                            /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (initCoord[id] \in Q)
                THEN 
                        /\  LET computations == AcceptComputations(p, id, ts[p][id])
                            IN
                            /\ ApplyAccept(p, bal[p][id], id, ts[p][id], dep[p][id], Nop)
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, ts[p][id], dep[p][id], Nop) : q \in Proc \ {p} } 
                                                                 \cup { AcceptOKMsg(p, p, bal[p][id], id, computations.Dq) } 
                        /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                ELSE IF (   LET Rmax == { n \in innerMsgs :
                                                /\ n.body.phaseq = PreAcceptedPhase
                                                /\ n.body.tq = initTimestamp[id] }
                            IN Cardinality(Rmax) >= Cardinality(innerMsgs) - E)
                        THEN
                        LET rejects == {m \in innerMsgs : m.body.rejectq = TRUE}
                        IN
                        IF (rejects # {} 
                            \/ ((Cardinality({m \in innerMsgs : m.body.phaseq = PreAcceptedPhase /\ m.body.tq = initTimestamp[id]}) = Cardinality(innerMsgs) - E)
                                /\ \E id2 \in UNION {m.body.WPq : m \in innerMsgs} : initCoord[id2] \notin Q ))
                        THEN 
                            /\  LET computations == AcceptComputations(p, id, ts[p][id])
                                IN
                                /\ ApplyAccept(p, bal[p][id], id, ts[p][id], dep[p][id], Nop)
                                /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, ts[p][id], dep[p][id], Nop) : q \in Proc \ {p} } 
                                                                     \cup { AcceptOKMsg(p, p, bal[p][id], id, computations.Dq) } 
                            /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                        ELSE 
                            LET n == CHOOSE msg \in innerMsgs : msg.body.phaseq = PreAcceptedPhase
                                Wall == UNION { (m.body.Wq \cup {<<id1, 0>> : id1 \in {id2 \in m.body.WPq : m.from = initCoord[id2]}}) : m \in innerMsgs }
                            IN
                            LET tx == n.body.txq
                                W == {<<id1, bal1>> \in Wall : \A <<id2, bal2>> \in Wall : bal2 <= bal1}
                                D == UNION {m.body.depq : m \in innerMsgs}
                            IN
                            /\ TXvar' = [TXvar EXCEPT  ![p][id] = tx]
                            /\ Wvar' = [Wvar EXCEPT  ![p][id] = W]
                            /\ Dvar' = [Dvar EXCEPT  ![p][id] = D]
                            /\ Qvar' = [Qvar EXCEPT  ![p][id] = Q]
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = TRUE]
                            /\ recoveryAttemptBal' = [recoveryAttemptBal EXCEPT ![p][id] = bal[p][id]]
                            /\ msgs' = msgs \ quorumOfMessages
                            /\ UNCHANGED <<bal, txn, abal, ts, dep, phase>>
                ELSE  
                    /\  LET computations == AcceptComputations(p, id, ts[p][id])
                        IN
                        /\ ApplyAccept(p, bal[p][id], id, ts[p][id], dep[p][id], Nop)
                        /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, bal[p][id], id, ts[p][id], dep[p][id], Nop) : q \in Proc \ {p} } 
                                                             \cup { AcceptOKMsg(p, p, bal[p][id], id, computations.Dq) } 
                        /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
    /\ UNCHANGED <<submitted, initCoord, recovered, initTimestamp >>
            
(* HandlePostWaiting (lines 78-81) *)
                    
HandlePostWaiting(p, id) ==
    /\  recoveryAttemptBal[p][id] = bal[p][id] \* I'm not getting the ballot of corresponding recovery attempt from messages here so I use this extra variable to check ballot.
    /\  postWaitingFlag[p][id] = TRUE
    /\  LET W == Wvar[p][id]
            b == bal[p][id] 
            tx == TXvar[p][id]
            D == Dvar[p][id]
            Q == Qvar[p][id]
            Case1 ==
                \E w \in W :
                    LET id1 == w[1]
                        bal1 == w[2]
                    IN /\ phase[p][id1] \in {CommittedPhase, StablePhase}
                    /\ abal[p][id1] >= bal1
                    /\ txn[p][id1] # Nop
                    /\ LessThanTs(initTimestamp[id], ts[p][id1])
                    /\ id \notin dep[p][id1]
            Case2 ==
                \A w \in W :
                    LET id1 == w[1]
                        bal1 == w[2]
                    IN /\ phase[p][id1] \in {CommittedPhase, StablePhase}
                    /\ abal[p][id1] >= bal1
                    /\ (txn[p][id1] = Nop \/ LessThanTs(ts[p][id1], initTimestamp[id]) \/ id \in dep[p][id1])
            Case3 ==
                (\E m \in VariantFilter("RecoverOKMessage", msgs) :
                    /\ m.from \notin Q
                    /\ (m.body.phaseq \in {StablePhase, CommittedPhase, AcceptedPhase} \/ m.from = initCoord[id]))
        IN 
        \/  /\ Case1
            /\  LET computations == AcceptComputations(p, id, ts[p][id])
                IN
                /\ ApplyAccept(p, bal[p][id], id, ts[p][id], dep[p][id], Nop)
                /\ msgs' = msgs \cup { AcceptMsg(p, q, bal[p][id], id, ts[p][id], dep[p][id], Nop) : q \in Proc \ {p} }
                                \cup { AcceptOKMsg(p, p, bal[p][id], id, computations.Dq) } 
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]

        \/  /\ Case2
            /\  LET computations == AcceptComputations(p, id, initTimestamp[id])
                IN
                /\ ApplyAccept(p, bal[p][id], id, initTimestamp[id], D, tx)
                /\ msgs' = msgs \cup { AcceptMsg(p, q, bal[p][id], id, initTimestamp[id], D, tx) : q \in Proc \ {p} }
                                \cup { AcceptOKMsg(p, p, bal[p][id], id, computations.Dq) }
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]

        \/  (\E m \in VariantFilter("RecoverOKMessage", msgs) :
                    /\ m.body.b = b
                    /\ m.body.id = id
                    /\ m.to = p
                    /\ m.from \notin Q
                    /\ (m.body.phaseq \in {StablePhase, CommittedPhase, AcceptedPhase} \/ m.from = initCoord[id])
                    /\  IF (m.body.phaseq = StablePhase) THEN
                            /\ ApplyCommit(p, b, id, m.body.tq, m.body.depq, m.body.txq, FALSE)
                            /\ ApplyStable(p, b, id)               
                            /\ msgs' = msgs \cup { CommitMsg(p, q, b, id, m.body.tq, m.body.depq, Fast, m.body.txq) : q \in Proc \ {p} }
                                            \cup { StableMsg(p, q, b, id) : q \in Proc \ {p} }
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]
                            /\ UNCHANGED bal
                        ELSE IF (m.body.phaseq = CommittedPhase) THEN   
                            /\ ApplyCommit(p, b, id, m.body.tq, m.body.depq, m.body.txq, FALSE)
                            /\ msgs' = msgs \cup { CommitMsg(p, q, b, id, m.body.tq, m.body.depq, Slow, m.body.txq) : q \in Proc \ {p} } 
                                            \cup { CommitOkMsg(p, p, b, id) }
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]
                            /\ UNCHANGED bal
                        ELSE IF (m.body.phaseq = AcceptedPhase) THEN 
                            LET computations == AcceptComputations(p, id, m.body.tq)
                            IN
                            /\ ApplyAccept(p, b, id, m.body.tq, m.body.depq, m.body.txq)
                            /\ msgs' = msgs \cup { AcceptMsg(p, q, b, id, m.body.tq, m.body.depq, m.body.txq) : q \in Proc \ {p} } 
                                            \cup { AcceptOKMsg(p, p, b, id, computations.Dq) }
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]
                        ELSE 
                            /\  LET computations == AcceptComputations(p, id, ts[p][id])
                                IN
                                /\ ApplyAccept(p, bal[p][id], id, ts[p][id], dep[p][id], Nop)
                                /\ msgs' = msgs \cup { AcceptMsg(p, q, bal[p][id], id, ts[p][id], dep[p][id], Nop) : q \in Proc \ {p} } 
                                                \cup { AcceptOKMsg(p, p, bal[p][id], id, computations.Dq) } 
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]
            )
        
        \* When none of the cases are correct, the model checker still has to be explicitly told that the next state is unchanged.
        \/  /\ ~Case1 /\ ~Case2 /\ ~Case3
            /\ UNCHANGED <<msgs, postWaitingFlag, bal, dep, phase, abal, txn, ts>>
                    
        
    /\ UNCHANGED <<submitted, initCoord, recovered, Wvar, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar>>


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)                 

Agreement ==
  \A id \in Id : \A p, q \in Proc :
    /\ phase[p][id] \in {CommittedPhase, StablePhase}
    /\ phase[q][id] \in {CommittedPhase, StablePhase}
    =>  /\ txn[p][id] = txn[q][id]
        /\ ts[p][id] = ts[q][id]

Ordering ==
  \A id1, id2 \in Id :
    \A p, q \in Proc :
      /\ phase[p][id1] = StablePhase
      /\ phase[q][id2] = CommittedPhase
      /\ txn[p][id1] # Nop
      /\ txn[q][id2] # Nop
      /\ Conflicts(id1, id2)
      /\ LessThanTs(ts[q][id2], ts[p][id1])
      => id2 \in dep[p][id1]

Next ==
    \/ \E m \in msgs :
        \/ HandlePreAccept(m) 
        \/ HandleAccept(m)
        \/ HandleCommit(m)
        \/ HandleStable(m)
        \/ HandleRecover(m)

    \/ \E p \in Proc, id \in Id :
        \/ Submit(p, id)
        \/ HandlePreAcceptOK(p, id) 
        \/ HandleAcceptOK(p, id) 
        \/ HandleCommitOK(p, id)
        \/ StartRecover(p, id)
        \/ HandleRecoverOK(p, id)
        \/ HandlePostWaiting(p, id)


Spec ==
    Init /\ [][Next]_vars

=========================================================================
````

## The command line parameters used to run the tool

```
--inv=Agreement --config=AccordSpec.cfg
```

## Expected behavior

<!-- What did you expect to see? -->

## Log files

<details>

```
2026-04-27T11:47:00,159 [main] INFO  a.f.a.t.Tool\$ - # APALACHE version: 0.56.1 | build: 70cdaf4
2026-04-27T11:47:00,177 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > AccordSpec.cfg: Loading TLC configuration
2026-04-27T11:47:00,225 [main] WARN  a.f.a.i.t.TlcConfigParserApalache\$ - TLC config option CHECK_DEADLOCK true will be ignored
2026-04-27T11:47:00,232 [main] WARN  a.f.a.i.p.o.OptionGroup\$ -   >  inv is set in TLC config but overridden via `inv` cli option or apalache.cfg; using Agreement
2026-04-27T11:47:00,233 [main] INFO  a.f.a.t.t.o.CheckCmd - Tuning: search.outputTraces=false
2026-04-27T11:47:00,406 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser
2026-04-27T11:47:00,950 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser [OK]
2026-04-27T11:47:00,951 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat
2026-04-27T11:47:00,951 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Running Snowcat .::.
2026-04-27T11:47:09,998 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Your types are purrfect!
2026-04-27T11:47:09,998 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > All expressions are typed
2026-04-27T11:47:09,998 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat [OK]
2026-04-27T11:47:09,999 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass
2026-04-27T11:47:10,161 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: Using SPECIFICATION Spec
2026-04-27T11:47:10,162 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: found INVARIANTS: Agreement
2026-04-27T11:47:10,165 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the initialization predicate to Init
2026-04-27T11:47:10,165 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the transition predicate to Next
2026-04-27T11:47:10,165 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the constant initialization predicate to CInit
2026-04-27T11:47:10,166 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Agreement
2026-04-27T11:47:10,172 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass [OK]
2026-04-27T11:47:10,172 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass
2026-04-27T11:47:10,173 [main] INFO  a.f.a.t.p.p.DesugarerPassImpl -   > Desugaring...
2026-04-27T11:47:10,198 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass [OK]
2026-04-27T11:47:10,198 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass
2026-04-27T11:47:10,199 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next
2026-04-27T11:47:10,508 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass [OK]
2026-04-27T11:47:10,508 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass
2026-04-27T11:47:10,508 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > Rewriting temporal operators...
2026-04-27T11:47:10,508 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > No temporal property specified, nothing to encode
2026-04-27T11:47:10,508 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass [OK]
2026-04-27T11:47:10,508 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass
2026-04-27T11:47:10,509 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next
2026-04-27T11:47:10,570 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass [OK]
2026-04-27T11:47:10,570 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass
2026-04-27T11:47:10,575 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing CInitPrimed for CInit'
2026-04-27T11:47:10,577 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing InitPrimed for Init'
2026-04-27T11:47:10,579 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass [OK]
2026-04-27T11:47:10,579 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #8: VCGen
2026-04-27T11:47:10,580 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Agreement
2026-04-27T11:47:10,586 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-04-27T11:47:10,587 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #8: VCGen [OK]
2026-04-27T11:47:10,588 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass
2026-04-27T11:47:10,588 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Before preprocessing: unique renaming
2026-04-27T11:47:10,601 [main] INFO  a.f.a.t.p.p.PreproPassImpl -  > Applying standard transformations:
2026-04-27T11:47:10,602 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > PrimePropagation
2026-04-27T11:47:10,610 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Desugarer
2026-04-27T11:47:10,622 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > UniqueRenamer
2026-04-27T11:47:10,666 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Normalizer
2026-04-27T11:47:10,692 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Keramelizer
2026-04-27T11:47:10,737 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > After preprocessing: UniqueRenamer
2026-04-27T11:47:10,790 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass [OK]
2026-04-27T11:47:10,790 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass
2026-04-27T11:47:10,856 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 1 initializing transitions
2026-04-27T11:47:10,958 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 70 transitions
2026-04-27T11:47:10,959 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found constant initializer CInit
2026-04-27T11:47:10,961 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Applying unique renaming
2026-04-27T11:47:11,042 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass [OK]
2026-04-27T11:47:11,043 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass
2026-04-27T11:47:11,048 [main] INFO  a.f.a.t.p.p.OptPassImpl -  > Applying optimizations:
2026-04-27T11:47:11,048 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-04-27T11:47:11,169 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ExprOptimizer
2026-04-27T11:47:11,243 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > SetMembershipSimplifier
2026-04-27T11:47:11,271 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-04-27T11:47:11,380 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass [OK]
2026-04-27T11:47:11,381 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass
2026-04-27T11:47:11,383 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Marking skolemizable existentials and sets to be expanded...
2026-04-27T11:47:11,384 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Skolemization
2026-04-27T11:47:11,395 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Expansion
2026-04-27T11:47:11,438 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Remove unused let-in defs
2026-04-27T11:47:11,462 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Running analyzers...
2026-04-27T11:47:11,467 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Introduced expression grades
2026-04-27T11:47:11,468 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass [OK]
2026-04-27T11:47:11,468 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #13: BoundedChecker
2026-04-27T11:47:11,492 [main] DEBUG a.f.a.t.b.s.Z3SolverContext - Creating Z3 solver context 0
2026-04-27T11:47:11,707 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Initializing CONSTANTS
2026-04-27T11:47:11,749 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #0, transition #0
2026-04-27T11:47:11,749 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,785 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0. Is it enabled?
2026-04-27T11:47:11,788 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0 is enabled
2026-04-27T11:47:11,788 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: Checking 1 state invariants
2026-04-27T11:47:11,789 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 0
2026-04-27T11:47:11,844 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 0 holds.
2026-04-27T11:47:11,849 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 0: picking a transition out of 1 transition(s)
2026-04-27T11:47:11,851 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #0
2026-04-27T11:47:11,851 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,854 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #0. Is it enabled?
2026-04-27T11:47:11,854 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #0 is disabled
2026-04-27T11:47:11,855 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #1
2026-04-27T11:47:11,855 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,856 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #1. Is it enabled?
2026-04-27T11:47:11,857 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #1 is disabled
2026-04-27T11:47:11,857 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #2
2026-04-27T11:47:11,857 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,858 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #2. Is it enabled?
2026-04-27T11:47:11,859 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #2 is disabled
2026-04-27T11:47:11,859 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #3
2026-04-27T11:47:11,859 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,860 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T11:47:11,860 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #4
2026-04-27T11:47:11,860 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,860 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T11:47:11,860 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #5
2026-04-27T11:47:11,860 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,861 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #5. Is it enabled?
2026-04-27T11:47:11,861 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #5 is disabled
2026-04-27T11:47:11,862 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #6
2026-04-27T11:47:11,862 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,863 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #6. Is it enabled?
2026-04-27T11:47:11,863 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #6 is disabled
2026-04-27T11:47:11,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #7
2026-04-27T11:47:11,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T11:47:11,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #8
2026-04-27T11:47:11,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T11:47:11,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #9
2026-04-27T11:47:11,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,866 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #9. Is it enabled?
2026-04-27T11:47:11,866 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #9 is disabled
2026-04-27T11:47:11,866 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #10
2026-04-27T11:47:11,866 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,868 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #10. Is it enabled?
2026-04-27T11:47:11,868 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #10 is disabled
2026-04-27T11:47:11,869 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #11
2026-04-27T11:47:11,869 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,870 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #11. Is it enabled?
2026-04-27T11:47:11,870 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #11 is disabled
2026-04-27T11:47:11,871 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #12
2026-04-27T11:47:11,871 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,872 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #12. Is it enabled?
2026-04-27T11:47:11,873 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #12 is disabled
2026-04-27T11:47:11,873 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #13
2026-04-27T11:47:11,873 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,877 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #13. Is it enabled?
2026-04-27T11:47:11,877 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #13 is disabled
2026-04-27T11:47:11,878 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #14
2026-04-27T11:47:11,878 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,880 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #14. Is it enabled?
2026-04-27T11:47:11,880 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #14 is disabled
2026-04-27T11:47:11,881 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #15
2026-04-27T11:47:11,881 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:11,882 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #15. Is it enabled?
2026-04-27T11:47:11,883 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #15 is disabled
2026-04-27T11:47:11,883 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #16
2026-04-27T11:47:11,883 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,033 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16. Is it enabled?
2026-04-27T11:47:12,039 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16 is enabled
2026-04-27T11:47:12,040 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: Checking 1 state invariants
2026-04-27T11:47:12,041 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 0
2026-04-27T11:47:12,066 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 0 holds.
2026-04-27T11:47:12,068 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #17
2026-04-27T11:47:12,069 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,132 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #17. Is it enabled?
2026-04-27T11:47:12,135 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #17 is disabled
2026-04-27T11:47:12,137 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #18
2026-04-27T11:47:12,137 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,144 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T11:47:12,145 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #19
2026-04-27T11:47:12,145 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,150 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T11:47:12,151 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #20
2026-04-27T11:47:12,151 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,156 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T11:47:12,156 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #21
2026-04-27T11:47:12,156 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,215 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #21. Is it enabled?
2026-04-27T11:47:12,219 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #21 is disabled
2026-04-27T11:47:12,221 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #22
2026-04-27T11:47:12,221 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,228 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T11:47:12,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #23
2026-04-27T11:47:12,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,234 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T11:47:12,235 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #24
2026-04-27T11:47:12,235 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,286 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #24. Is it enabled?
2026-04-27T11:47:12,289 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #24 is disabled
2026-04-27T11:47:12,291 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #25
2026-04-27T11:47:12,291 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,296 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T11:47:12,296 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #26
2026-04-27T11:47:12,296 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,370 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #26. Is it enabled?
2026-04-27T11:47:12,375 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #26 is disabled
2026-04-27T11:47:12,376 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #27
2026-04-27T11:47:12,377 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,393 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #27. Is it enabled?
2026-04-27T11:47:12,395 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #27 is disabled
2026-04-27T11:47:12,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #28
2026-04-27T11:47:12,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,550 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #28. Is it enabled?
2026-04-27T11:47:12,561 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #28 is disabled
2026-04-27T11:47:12,564 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #29
2026-04-27T11:47:12,564 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,678 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #29. Is it enabled?
2026-04-27T11:47:12,689 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #29 is disabled
2026-04-27T11:47:12,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #30
2026-04-27T11:47:12,693 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,799 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #30. Is it enabled?
2026-04-27T11:47:12,810 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #30 is disabled
2026-04-27T11:47:12,813 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #31
2026-04-27T11:47:12,813 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:12,972 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #31. Is it enabled?
2026-04-27T11:47:12,982 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #31 is disabled
2026-04-27T11:47:12,985 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #32
2026-04-27T11:47:12,985 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,130 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #32. Is it enabled?
2026-04-27T11:47:13,140 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #32 is disabled
2026-04-27T11:47:13,143 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #33
2026-04-27T11:47:13,143 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,240 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #33. Is it enabled?
2026-04-27T11:47:13,252 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #33 is disabled
2026-04-27T11:47:13,255 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #34
2026-04-27T11:47:13,255 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,356 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #34. Is it enabled?
2026-04-27T11:47:13,368 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #34 is disabled
2026-04-27T11:47:13,371 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #35
2026-04-27T11:47:13,371 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,524 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #35. Is it enabled?
2026-04-27T11:47:13,536 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #35 is disabled
2026-04-27T11:47:13,539 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #36
2026-04-27T11:47:13,539 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,541 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T11:47:13,542 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #37
2026-04-27T11:47:13,542 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,583 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #37. Is it enabled?
2026-04-27T11:47:13,588 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #37 is disabled
2026-04-27T11:47:13,589 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #38
2026-04-27T11:47:13,590 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,592 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T11:47:13,592 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #39
2026-04-27T11:47:13,592 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,634 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #39. Is it enabled?
2026-04-27T11:47:13,639 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #39 is disabled
2026-04-27T11:47:13,641 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #40
2026-04-27T11:47:13,641 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,643 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T11:47:13,644 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #41
2026-04-27T11:47:13,644 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,667 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #41. Is it enabled?
2026-04-27T11:47:13,670 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #41 is disabled
2026-04-27T11:47:13,671 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #42
2026-04-27T11:47:13,671 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,673 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T11:47:13,673 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #43
2026-04-27T11:47:13,673 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,700 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #43. Is it enabled?
2026-04-27T11:47:13,703 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #43 is disabled
2026-04-27T11:47:13,704 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #44
2026-04-27T11:47:13,704 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,738 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #44. Is it enabled?
2026-04-27T11:47:13,742 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #44 is disabled
2026-04-27T11:47:13,743 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #45
2026-04-27T11:47:13,743 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,805 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #45. Is it enabled?
2026-04-27T11:47:13,809 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #45 is disabled
2026-04-27T11:47:13,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #46
2026-04-27T11:47:13,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,857 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #46. Is it enabled?
2026-04-27T11:47:13,863 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #46 is disabled
2026-04-27T11:47:13,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #47
2026-04-27T11:47:13,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:13,962 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #47. Is it enabled?
2026-04-27T11:47:13,968 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #47 is disabled
2026-04-27T11:47:13,969 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #48
2026-04-27T11:47:13,969 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,022 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #48. Is it enabled?
2026-04-27T11:47:14,027 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #48 is disabled
2026-04-27T11:47:14,028 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #49
2026-04-27T11:47:14,029 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,098 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #49. Is it enabled?
2026-04-27T11:47:14,103 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #49 is disabled
2026-04-27T11:47:14,104 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #50
2026-04-27T11:47:14,104 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,128 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #50. Is it enabled?
2026-04-27T11:47:14,130 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #50 is disabled
2026-04-27T11:47:14,131 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #51
2026-04-27T11:47:14,132 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,184 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #51. Is it enabled?
2026-04-27T11:47:14,189 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #51 is disabled
2026-04-27T11:47:14,191 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #52
2026-04-27T11:47:14,191 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,240 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #52. Is it enabled?
2026-04-27T11:47:14,246 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #52 is disabled
2026-04-27T11:47:14,247 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #53
2026-04-27T11:47:14,248 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,299 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #53. Is it enabled?
2026-04-27T11:47:14,306 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #53 is disabled
2026-04-27T11:47:14,307 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #54
2026-04-27T11:47:14,307 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,354 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #54. Is it enabled?
2026-04-27T11:47:14,359 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #54 is disabled
2026-04-27T11:47:14,361 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #55
2026-04-27T11:47:14,361 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,367 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-04-27T11:47:14,368 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #56
2026-04-27T11:47:14,368 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,376 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #56. Is it enabled?
2026-04-27T11:47:14,377 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #56 is disabled
2026-04-27T11:47:14,377 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #57
2026-04-27T11:47:14,377 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,383 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-04-27T11:47:14,384 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #58
2026-04-27T11:47:14,384 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,390 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #58. Is it enabled?
2026-04-27T11:47:14,391 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #58 is disabled
2026-04-27T11:47:14,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #59
2026-04-27T11:47:14,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,396 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T11:47:14,397 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #60
2026-04-27T11:47:14,397 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,404 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #60. Is it enabled?
2026-04-27T11:47:14,405 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #60 is disabled
2026-04-27T11:47:14,405 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #61
2026-04-27T11:47:14,405 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,410 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T11:47:14,411 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #62
2026-04-27T11:47:14,411 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,417 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #62. Is it enabled?
2026-04-27T11:47:14,418 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #62 is disabled
2026-04-27T11:47:14,418 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #63
2026-04-27T11:47:14,418 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,424 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #63. Is it enabled?
2026-04-27T11:47:14,426 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #63 is disabled
2026-04-27T11:47:14,426 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #64
2026-04-27T11:47:14,426 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,433 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #64. Is it enabled?
2026-04-27T11:47:14,434 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #64 is disabled
2026-04-27T11:47:14,434 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #65
2026-04-27T11:47:14,434 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,440 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #65. Is it enabled?
2026-04-27T11:47:14,441 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #65 is disabled
2026-04-27T11:47:14,441 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #66
2026-04-27T11:47:14,441 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,542 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #66. Is it enabled?
2026-04-27T11:47:14,549 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #66 is disabled
2026-04-27T11:47:14,551 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #67
2026-04-27T11:47:14,551 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,596 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #67. Is it enabled?
2026-04-27T11:47:14,603 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #67 is disabled
2026-04-27T11:47:14,605 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #68
2026-04-27T11:47:14,605 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,613 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #68. Is it enabled?
2026-04-27T11:47:14,614 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #68 is disabled
2026-04-27T11:47:14,614 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #69
2026-04-27T11:47:14,615 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,621 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #69. Is it enabled?
2026-04-27T11:47:14,622 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #69 is disabled
2026-04-27T11:47:14,623 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 1: picking a transition out of 1 transition(s)
2026-04-27T11:47:14,623 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #0
2026-04-27T11:47:14,623 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,686 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0. Is it enabled?
2026-04-27T11:47:14,746 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0 is enabled
2026-04-27T11:47:14,747 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: Checking 1 state invariants
2026-04-27T11:47:14,747 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 0
2026-04-27T11:47:14,786 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 0 holds.
2026-04-27T11:47:14,787 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #1
2026-04-27T11:47:14,787 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,832 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #1. Is it enabled?
2026-04-27T11:47:14,839 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #1 is disabled
2026-04-27T11:47:14,840 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #2
2026-04-27T11:47:14,840 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,887 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #2. Is it enabled?
2026-04-27T11:47:14,894 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #2 is disabled
2026-04-27T11:47:14,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #3
2026-04-27T11:47:14,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,898 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T11:47:14,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #4
2026-04-27T11:47:14,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,902 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T11:47:14,902 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #5
2026-04-27T11:47:14,902 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:14,970 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #5. Is it enabled?
2026-04-27T11:47:14,976 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #5 is disabled
2026-04-27T11:47:14,979 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #6
2026-04-27T11:47:14,979 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,028 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #6. Is it enabled?
2026-04-27T11:47:15,032 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #6 is disabled
2026-04-27T11:47:15,033 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #7
2026-04-27T11:47:15,033 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,036 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T11:47:15,037 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #8
2026-04-27T11:47:15,037 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,040 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T11:47:15,040 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #9
2026-04-27T11:47:15,040 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,069 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #9. Is it enabled?
2026-04-27T11:47:15,074 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #9 is disabled
2026-04-27T11:47:15,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #10
2026-04-27T11:47:15,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,104 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #10. Is it enabled?
2026-04-27T11:47:15,108 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #10 is disabled
2026-04-27T11:47:15,109 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #11
2026-04-27T11:47:15,110 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,127 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #11. Is it enabled?
2026-04-27T11:47:15,130 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #11 is disabled
2026-04-27T11:47:15,131 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #12
2026-04-27T11:47:15,131 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,297 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #12. Is it enabled?
2026-04-27T11:47:15,315 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #12 is disabled
2026-04-27T11:47:15,319 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #13
2026-04-27T11:47:15,319 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,440 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #13. Is it enabled?
2026-04-27T11:47:15,457 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #13 is disabled
2026-04-27T11:47:15,461 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #14
2026-04-27T11:47:15,461 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,584 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #14. Is it enabled?
2026-04-27T11:47:15,602 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #14 is disabled
2026-04-27T11:47:15,606 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #15
2026-04-27T11:47:15,606 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,764 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #15. Is it enabled?
2026-04-27T11:47:15,780 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #15 is disabled
2026-04-27T11:47:15,784 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #16
2026-04-27T11:47:15,784 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,834 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #16. Is it enabled?
2026-04-27T11:47:15,881 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #16 is enabled
2026-04-27T11:47:15,882 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: Checking 1 state invariants
2026-04-27T11:47:15,882 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 0
2026-04-27T11:47:15,918 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 0 holds.
2026-04-27T11:47:15,920 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #17
2026-04-27T11:47:15,920 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:15,975 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #17. Is it enabled?
2026-04-27T11:47:15,999 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #17 is disabled
2026-04-27T11:47:16,001 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #18
2026-04-27T11:47:16,001 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,020 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T11:47:16,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #19
2026-04-27T11:47:16,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,030 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T11:47:16,032 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #20
2026-04-27T11:47:16,032 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,042 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T11:47:16,044 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #21
2026-04-27T11:47:16,044 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,114 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #21. Is it enabled?
2026-04-27T11:47:16,132 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #21 is disabled
2026-04-27T11:47:16,134 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #22
2026-04-27T11:47:16,134 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,156 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T11:47:16,158 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #23
2026-04-27T11:47:16,158 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,167 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T11:47:16,168 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #24
2026-04-27T11:47:16,168 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,226 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #24. Is it enabled?
2026-04-27T11:47:16,233 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #24 is disabled
2026-04-27T11:47:16,235 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #25
2026-04-27T11:47:16,235 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,245 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T11:47:16,247 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #26
2026-04-27T11:47:16,247 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,338 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #26. Is it enabled?
2026-04-27T11:47:16,346 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #26 is disabled
2026-04-27T11:47:16,348 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #27
2026-04-27T11:47:16,348 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,390 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #27. Is it enabled?
2026-04-27T11:47:16,394 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #27 is disabled
2026-04-27T11:47:16,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #28
2026-04-27T11:47:16,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,540 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #28. Is it enabled?
2026-04-27T11:47:16,606 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #28 is disabled
2026-04-27T11:47:16,610 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #29
2026-04-27T11:47:16,611 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,753 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #29. Is it enabled?
2026-04-27T11:47:16,792 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #29 is disabled
2026-04-27T11:47:16,796 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #30
2026-04-27T11:47:16,796 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:16,930 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30. Is it enabled?
2026-04-27T11:47:17,360 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30 is enabled
2026-04-27T11:47:17,364 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #31
2026-04-27T11:47:17,364 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:17,549 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #31. Is it enabled?
2026-04-27T11:47:17,670 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #31 is disabled
2026-04-27T11:47:17,675 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #32
2026-04-27T11:47:17,675 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:17,811 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #32. Is it enabled?
2026-04-27T11:47:17,868 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #32 is disabled
2026-04-27T11:47:17,873 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #33
2026-04-27T11:47:17,873 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,005 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #33. Is it enabled?
2026-04-27T11:47:18,093 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #33 is disabled
2026-04-27T11:47:18,098 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #34
2026-04-27T11:47:18,098 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,238 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #34. Is it enabled?
2026-04-27T11:47:18,331 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #34 is disabled
2026-04-27T11:47:18,336 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #35
2026-04-27T11:47:18,336 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,543 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #35. Is it enabled?
2026-04-27T11:47:18,638 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #35 is disabled
2026-04-27T11:47:18,644 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #36
2026-04-27T11:47:18,644 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,658 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T11:47:18,660 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #37
2026-04-27T11:47:18,660 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,712 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #37. Is it enabled?
2026-04-27T11:47:18,721 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #37 is disabled
2026-04-27T11:47:18,723 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #38
2026-04-27T11:47:18,723 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,738 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T11:47:18,740 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #39
2026-04-27T11:47:18,740 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,798 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #39. Is it enabled?
2026-04-27T11:47:18,808 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #39 is disabled
2026-04-27T11:47:18,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #40
2026-04-27T11:47:18,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,825 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T11:47:18,826 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #41
2026-04-27T11:47:18,826 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,867 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #41. Is it enabled?
2026-04-27T11:47:18,873 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #41 is disabled
2026-04-27T11:47:18,875 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #42
2026-04-27T11:47:18,875 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,890 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T11:47:18,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #43
2026-04-27T11:47:18,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:18,936 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #43. Is it enabled?
2026-04-27T11:47:18,942 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #43 is disabled
2026-04-27T11:47:18,944 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #44
2026-04-27T11:47:18,944 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,034 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #44. Is it enabled?
2026-04-27T11:47:19,043 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #44 is disabled
2026-04-27T11:47:19,047 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #45
2026-04-27T11:47:19,047 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,109 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #45. Is it enabled?
2026-04-27T11:47:19,119 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #45 is disabled
2026-04-27T11:47:19,121 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #46
2026-04-27T11:47:19,121 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,205 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #46. Is it enabled?
2026-04-27T11:47:19,218 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #46 is disabled
2026-04-27T11:47:19,221 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #47
2026-04-27T11:47:19,221 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,306 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #47. Is it enabled?
2026-04-27T11:47:19,319 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #47 is disabled
2026-04-27T11:47:19,321 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #48
2026-04-27T11:47:19,322 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,407 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #48. Is it enabled?
2026-04-27T11:47:19,421 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #48 is disabled
2026-04-27T11:47:19,424 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #49
2026-04-27T11:47:19,424 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,562 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #49. Is it enabled?
2026-04-27T11:47:19,580 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #49 is disabled
2026-04-27T11:47:19,583 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #50
2026-04-27T11:47:19,583 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,629 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #50. Is it enabled?
2026-04-27T11:47:19,635 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #50 is disabled
2026-04-27T11:47:19,637 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #51
2026-04-27T11:47:19,637 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,717 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #51. Is it enabled?
2026-04-27T11:47:19,732 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #51 is disabled
2026-04-27T11:47:19,735 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #52
2026-04-27T11:47:19,735 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,819 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #52. Is it enabled?
2026-04-27T11:47:19,836 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #52 is disabled
2026-04-27T11:47:19,839 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #53
2026-04-27T11:47:19,839 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:19,906 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #53. Is it enabled?
2026-04-27T11:47:19,919 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #53 is disabled
2026-04-27T11:47:19,921 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #54
2026-04-27T11:47:19,921 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,014 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #54. Is it enabled?
2026-04-27T11:47:20,023 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #54 is disabled
2026-04-27T11:47:20,025 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #55
2026-04-27T11:47:20,025 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,031 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-04-27T11:47:20,032 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #56
2026-04-27T11:47:20,032 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,083 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #56. Is it enabled?
2026-04-27T11:47:20,092 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #56 is disabled
2026-04-27T11:47:20,094 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #57
2026-04-27T11:47:20,094 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,101 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-04-27T11:47:20,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #58
2026-04-27T11:47:20,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,157 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #58. Is it enabled?
2026-04-27T11:47:20,167 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #58 is disabled
2026-04-27T11:47:20,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #59
2026-04-27T11:47:20,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,176 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T11:47:20,177 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #60
2026-04-27T11:47:20,177 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,214 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #60. Is it enabled?
2026-04-27T11:47:20,219 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #60 is disabled
2026-04-27T11:47:20,221 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #61
2026-04-27T11:47:20,221 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,227 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T11:47:20,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #62
2026-04-27T11:47:20,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,263 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #62. Is it enabled?
2026-04-27T11:47:20,269 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #62 is disabled
2026-04-27T11:47:20,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #63
2026-04-27T11:47:20,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,314 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #63. Is it enabled?
2026-04-27T11:47:20,323 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #63 is disabled
2026-04-27T11:47:20,325 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #64
2026-04-27T11:47:20,325 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,395 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #64. Is it enabled?
2026-04-27T11:47:20,412 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #64 is disabled
2026-04-27T11:47:20,415 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #65
2026-04-27T11:47:20,415 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,425 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #65. Is it enabled?
2026-04-27T11:47:20,427 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #65 is disabled
2026-04-27T11:47:20,428 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #66
2026-04-27T11:47:20,428 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,500 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #66. Is it enabled?
2026-04-27T11:47:20,514 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #66 is disabled
2026-04-27T11:47:20,517 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #67
2026-04-27T11:47:20,517 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,571 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #67. Is it enabled?
2026-04-27T11:47:20,582 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #67 is disabled
2026-04-27T11:47:20,585 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #68
2026-04-27T11:47:20,585 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,681 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #68. Is it enabled?
2026-04-27T11:47:20,689 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #68 is disabled
2026-04-27T11:47:20,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #69
2026-04-27T11:47:20,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,815 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #69. Is it enabled?
2026-04-27T11:47:20,829 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #69 is disabled
2026-04-27T11:47:20,832 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 2: picking a transition out of 3 transition(s)
2026-04-27T11:47:20,875 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #0
2026-04-27T11:47:20,875 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:20,946 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0. Is it enabled?
2026-04-27T11:47:21,517 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0 is enabled
2026-04-27T11:47:21,517 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 1 state invariants
2026-04-27T11:47:21,518 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-04-27T11:47:21,981 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-04-27T11:47:21,986 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #1
2026-04-27T11:47:21,986 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,065 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #1. Is it enabled?
2026-04-27T11:47:22,083 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #1 is disabled
2026-04-27T11:47:22,087 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #2
2026-04-27T11:47:22,087 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,181 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #2. Is it enabled?
2026-04-27T11:47:22,199 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #2 is disabled
2026-04-27T11:47:22,202 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #3
2026-04-27T11:47:22,203 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,211 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T11:47:22,214 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #4
2026-04-27T11:47:22,214 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T11:47:22,232 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #5
2026-04-27T11:47:22,232 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,303 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #5. Is it enabled?
2026-04-27T11:47:22,314 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #5 is disabled
2026-04-27T11:47:22,317 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #6
2026-04-27T11:47:22,317 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,362 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #6. Is it enabled?
2026-04-27T11:47:22,374 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #6 is disabled
2026-04-27T11:47:22,377 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #7
2026-04-27T11:47:22,377 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,385 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T11:47:22,387 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #8
2026-04-27T11:47:22,387 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,394 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T11:47:22,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #9
2026-04-27T11:47:22,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,442 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #9. Is it enabled?
2026-04-27T11:47:22,452 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #9 is disabled
2026-04-27T11:47:22,455 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #10
2026-04-27T11:47:22,455 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,503 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #10. Is it enabled?
2026-04-27T11:47:22,514 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #10 is disabled
2026-04-27T11:47:22,517 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #11
2026-04-27T11:47:22,517 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,602 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #11. Is it enabled?
2026-04-27T11:47:22,613 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #11 is disabled
2026-04-27T11:47:22,615 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #12
2026-04-27T11:47:22,616 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:22,767 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #12. Is it enabled?
2026-04-27T11:47:22,945 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #12 is disabled
2026-04-27T11:47:22,952 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #13
2026-04-27T11:47:22,952 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:23,095 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #13. Is it enabled?
2026-04-27T11:47:23,286 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #13 is disabled
2026-04-27T11:47:23,295 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #14
2026-04-27T11:47:23,295 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:23,451 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #14. Is it enabled?
2026-04-27T11:47:23,632 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #14 is disabled
2026-04-27T11:47:23,639 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #15
2026-04-27T11:47:23,639 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:23,844 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #15. Is it enabled?
2026-04-27T11:47:25,768 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #15 is enabled
2026-04-27T11:47:25,768 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 1 state invariants
2026-04-27T11:47:25,768 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-04-27T11:47:25,996 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-04-27T11:47:26,001 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #16
2026-04-27T11:47:26,001 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:26,050 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #16. Is it enabled?
2026-04-27T11:47:26,603 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #16 is enabled
2026-04-27T11:47:26,603 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 1 state invariants
2026-04-27T11:47:26,604 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-04-27T11:47:26,968 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-04-27T11:47:26,974 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #17
2026-04-27T11:47:26,974 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:27,075 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #17. Is it enabled?
2026-04-27T11:47:27,914 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #17 is enabled
2026-04-27T11:47:27,914 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 1 state invariants
2026-04-27T11:47:27,914 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-04-27T11:47:28,171 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-04-27T11:47:28,180 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #18
2026-04-27T11:47:28,180 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:28,194 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T11:47:28,196 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #19
2026-04-27T11:47:28,196 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:28,209 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T11:47:28,212 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #20
2026-04-27T11:47:28,212 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:28,225 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T11:47:28,227 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #21
2026-04-27T11:47:28,227 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:28,318 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #21. Is it enabled?
2026-04-27T11:47:28,892 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #21 is disabled
2026-04-27T11:47:28,901 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #22
2026-04-27T11:47:28,901 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:28,976 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T11:47:28,984 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #23
2026-04-27T11:47:28,984 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:28,999 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T11:47:29,002 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #24
2026-04-27T11:47:29,002 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:29,067 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #24. Is it enabled?
2026-04-27T11:47:29,096 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #24 is disabled
2026-04-27T11:47:29,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #25
2026-04-27T11:47:29,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:29,118 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T11:47:29,120 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #26
2026-04-27T11:47:29,120 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:29,189 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #26. Is it enabled?
2026-04-27T11:47:29,219 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #26 is disabled
2026-04-27T11:47:29,225 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #27
2026-04-27T11:47:29,225 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:29,265 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #27. Is it enabled?
2026-04-27T11:47:29,302 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #27 is disabled
2026-04-27T11:47:29,306 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #28
2026-04-27T11:47:29,306 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:29,493 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #28. Is it enabled?
2026-04-27T11:47:31,192 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #28 is disabled
2026-04-27T11:47:31,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #29
2026-04-27T11:47:31,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:31,378 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #29. Is it enabled?
2026-04-27T11:47:32,422 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #29 is disabled
2026-04-27T11:47:32,435 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #30
2026-04-27T11:47:32,435 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:32,577 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #30. Is it enabled?
2026-04-27T11:47:33,702 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #30 is enabled
2026-04-27T11:47:33,715 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #31
2026-04-27T11:47:33,715 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:33,847 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #31. Is it enabled?
2026-04-27T11:47:34,525 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #31 is disabled
2026-04-27T11:47:34,536 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #32
2026-04-27T11:47:34,536 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:34,677 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #32. Is it enabled?
2026-04-27T11:47:35,498 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #32 is disabled
2026-04-27T11:47:35,510 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #33
2026-04-27T11:47:35,510 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:35,723 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #33. Is it enabled?
2026-04-27T11:47:37,776 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #33 is disabled
2026-04-27T11:47:37,802 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #34
2026-04-27T11:47:37,802 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:37,953 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #34. Is it enabled?
2026-04-27T11:47:39,173 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #34 is disabled
2026-04-27T11:47:39,189 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #35
2026-04-27T11:47:39,189 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:39,331 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #35. Is it enabled?
2026-04-27T11:47:40,848 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #35 is disabled
2026-04-27T11:47:40,862 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #36
2026-04-27T11:47:40,862 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:40,893 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T11:47:40,897 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #37
2026-04-27T11:47:40,897 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:40,980 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #37. Is it enabled?
2026-04-27T11:47:40,996 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #37 is disabled
2026-04-27T11:47:41,001 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #38
2026-04-27T11:47:41,001 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:41,084 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T11:47:41,088 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #39
2026-04-27T11:47:41,088 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:41,174 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #39. Is it enabled?
2026-04-27T11:47:41,201 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #39 is disabled
2026-04-27T11:47:41,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #40
2026-04-27T11:47:41,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:41,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T11:47:41,247 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #41
2026-04-27T11:47:41,247 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:41,321 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #41. Is it enabled?
2026-04-27T11:47:41,336 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #41 is disabled
2026-04-27T11:47:41,341 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #42
2026-04-27T11:47:41,341 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:41,373 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T11:47:41,378 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #43
2026-04-27T11:47:41,378 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:41,453 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #43. Is it enabled?
2026-04-27T11:47:41,469 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #43 is disabled
2026-04-27T11:47:41,474 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #44
2026-04-27T11:47:41,474 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:41,607 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #44. Is it enabled?
2026-04-27T11:47:41,628 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #44 is disabled
2026-04-27T11:47:41,633 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #45
2026-04-27T11:47:41,633 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:41,729 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #45. Is it enabled?
2026-04-27T11:47:41,750 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #45 is disabled
2026-04-27T11:47:41,755 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #46
2026-04-27T11:47:41,755 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:41,869 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #46. Is it enabled?
2026-04-27T11:47:41,894 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #46 is disabled
2026-04-27T11:47:41,900 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #47
2026-04-27T11:47:41,900 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:42,060 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #47. Is it enabled?
2026-04-27T11:47:42,089 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #47 is disabled
2026-04-27T11:47:42,095 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #48
2026-04-27T11:47:42,095 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:42,258 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #48. Is it enabled?
2026-04-27T11:47:42,323 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #48 is disabled
2026-04-27T11:47:42,331 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #49
2026-04-27T11:47:42,331 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:42,466 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #49. Is it enabled?
2026-04-27T11:47:42,529 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #49 is disabled
2026-04-27T11:47:42,536 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #50
2026-04-27T11:47:42,536 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:42,627 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #50. Is it enabled?
2026-04-27T11:47:42,667 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #50 is disabled
2026-04-27T11:47:42,674 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #51
2026-04-27T11:47:42,674 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:42,842 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #51. Is it enabled?
2026-04-27T11:47:42,891 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #51 is disabled
2026-04-27T11:47:42,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #52
2026-04-27T11:47:42,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,021 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #52. Is it enabled?
2026-04-27T11:47:43,072 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #52 is disabled
2026-04-27T11:47:43,081 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #53
2026-04-27T11:47:43,081 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,167 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #53. Is it enabled?
2026-04-27T11:47:43,187 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #53 is disabled
2026-04-27T11:47:43,192 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #54
2026-04-27T11:47:43,192 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,253 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #54. Is it enabled?
2026-04-27T11:47:43,268 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #54 is disabled
2026-04-27T11:47:43,273 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #55
2026-04-27T11:47:43,273 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,279 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-04-27T11:47:43,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #56
2026-04-27T11:47:43,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,329 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #56. Is it enabled?
2026-04-27T11:47:43,342 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #56 is disabled
2026-04-27T11:47:43,346 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #57
2026-04-27T11:47:43,346 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,352 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-04-27T11:47:43,354 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #58
2026-04-27T11:47:43,354 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,404 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #58. Is it enabled?
2026-04-27T11:47:43,417 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #58 is disabled
2026-04-27T11:47:43,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #59
2026-04-27T11:47:43,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,427 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T11:47:43,429 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #60
2026-04-27T11:47:43,429 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,464 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #60. Is it enabled?
2026-04-27T11:47:43,473 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #60 is disabled
2026-04-27T11:47:43,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #61
2026-04-27T11:47:43,477 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,483 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T11:47:43,484 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #62
2026-04-27T11:47:43,484 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,523 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #62. Is it enabled?
2026-04-27T11:47:43,532 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #62 is disabled
2026-04-27T11:47:43,536 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #63
2026-04-27T11:47:43,536 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,627 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #63. Is it enabled?
2026-04-27T11:47:43,639 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #63 is disabled
2026-04-27T11:47:43,642 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #64
2026-04-27T11:47:43,643 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,724 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #64. Is it enabled?
2026-04-27T11:47:43,746 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #64 is disabled
2026-04-27T11:47:43,752 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #65
2026-04-27T11:47:43,752 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,765 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #65. Is it enabled?
2026-04-27T11:47:43,768 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #65 is disabled
2026-04-27T11:47:43,771 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #66
2026-04-27T11:47:43,771 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,850 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #66. Is it enabled?
2026-04-27T11:47:43,873 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #66 is disabled
2026-04-27T11:47:43,878 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #67
2026-04-27T11:47:43,878 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:43,940 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #67. Is it enabled?
2026-04-27T11:47:43,956 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #67 is disabled
2026-04-27T11:47:43,961 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #68
2026-04-27T11:47:43,961 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:44,015 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #68. Is it enabled?
2026-04-27T11:47:44,030 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #68 is disabled
2026-04-27T11:47:44,034 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #69
2026-04-27T11:47:44,034 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:44,120 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #69. Is it enabled?
2026-04-27T11:47:44,144 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #69 is disabled
2026-04-27T11:47:44,150 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 3: picking a transition out of 5 transition(s)
2026-04-27T11:47:44,236 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #0
2026-04-27T11:47:44,236 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:44,339 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #0. Is it enabled?
2026-04-27T11:47:47,115 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #0 is enabled
2026-04-27T11:47:47,116 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:47:47,116 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:47:52,909 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:47:52,927 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #1
2026-04-27T11:47:52,927 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:53,083 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #1. Is it enabled?
2026-04-27T11:47:53,278 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #1 is disabled
2026-04-27T11:47:53,284 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #2
2026-04-27T11:47:53,284 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:53,426 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #2. Is it enabled?
2026-04-27T11:47:53,450 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #2 is disabled
2026-04-27T11:47:53,458 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #3
2026-04-27T11:47:53,458 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:53,473 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T11:47:53,475 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #4
2026-04-27T11:47:53,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:53,490 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T11:47:53,493 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #5
2026-04-27T11:47:53,493 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:53,573 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #5. Is it enabled?
2026-04-27T11:47:53,628 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #5 is disabled
2026-04-27T11:47:53,635 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #6
2026-04-27T11:47:53,635 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:53,711 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #6. Is it enabled?
2026-04-27T11:47:55,916 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #6 is enabled
2026-04-27T11:47:55,917 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:47:55,917 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:47:56,777 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:47:56,791 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #7
2026-04-27T11:47:56,791 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:56,807 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T11:47:56,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #8
2026-04-27T11:47:56,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:56,823 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T11:47:56,826 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #9
2026-04-27T11:47:56,826 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:56,902 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #9. Is it enabled?
2026-04-27T11:47:56,924 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #9 is disabled
2026-04-27T11:47:56,930 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #10
2026-04-27T11:47:56,930 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:57,007 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #10. Is it enabled?
2026-04-27T11:47:57,027 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #10 is disabled
2026-04-27T11:47:57,033 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #11
2026-04-27T11:47:57,033 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:57,143 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #11. Is it enabled?
2026-04-27T11:47:57,737 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #11 is disabled
2026-04-27T11:47:57,748 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #12
2026-04-27T11:47:57,748 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:47:57,923 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #12. Is it enabled?
2026-04-27T11:48:06,505 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #12 is disabled
2026-04-27T11:48:06,522 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #13
2026-04-27T11:48:06,522 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:48:06,703 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #13. Is it enabled?
2026-04-27T11:48:10,047 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #13 is enabled
2026-04-27T11:48:10,072 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #14
2026-04-27T11:48:10,073 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:48:10,256 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #14. Is it enabled?
2026-04-27T11:48:19,767 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #14 is disabled
2026-04-27T11:48:19,791 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #15
2026-04-27T11:48:19,791 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:48:20,032 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #15. Is it enabled?
2026-04-27T11:48:24,870 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #15 is enabled
2026-04-27T11:48:24,871 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:48:24,871 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:48:28,372 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:48:28,389 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #16
2026-04-27T11:48:28,389 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:48:28,443 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #16. Is it enabled?
2026-04-27T11:48:34,875 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #16 is enabled
2026-04-27T11:48:34,876 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:48:34,876 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:48:40,798 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:48:40,818 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #17
2026-04-27T11:48:40,819 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:48:41,092 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #17. Is it enabled?
2026-04-27T11:48:43,691 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #17 is enabled
2026-04-27T11:48:43,692 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:48:43,692 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:49:03,904 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:49:03,941 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #18
2026-04-27T11:49:03,941 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:04,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T11:49:04,026 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #19
2026-04-27T11:49:04,026 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:04,071 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T11:49:04,076 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #20
2026-04-27T11:49:04,076 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:04,123 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T11:49:04,132 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #21
2026-04-27T11:49:04,132 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:04,379 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #21. Is it enabled?
2026-04-27T11:49:12,269 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #21 is enabled
2026-04-27T11:49:12,269 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:49:12,270 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:49:17,035 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:49:17,065 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #22
2026-04-27T11:49:17,065 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:17,306 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T11:49:17,341 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #23
2026-04-27T11:49:17,341 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:17,366 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T11:49:17,373 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #24
2026-04-27T11:49:17,373 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:17,474 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #24. Is it enabled?
2026-04-27T11:49:17,889 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #24 is disabled
2026-04-27T11:49:17,901 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #25
2026-04-27T11:49:17,901 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:17,930 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T11:49:17,935 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #26
2026-04-27T11:49:17,935 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:18,039 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #26. Is it enabled?
2026-04-27T11:49:18,423 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #26 is disabled
2026-04-27T11:49:18,443 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #27
2026-04-27T11:49:18,444 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:18,565 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #27. Is it enabled?
2026-04-27T11:49:18,938 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #27 is disabled
2026-04-27T11:49:18,957 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #28
2026-04-27T11:49:18,958 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:19,110 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #28. Is it enabled?
2026-04-27T11:49:53,443 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #28 is disabled
2026-04-27T11:49:53,484 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #29
2026-04-27T11:49:53,484 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:49:53,703 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #29. Is it enabled?
2026-04-27T11:50:01,180 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #29 is disabled
2026-04-27T11:50:01,217 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #30
2026-04-27T11:50:01,217 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:50:01,369 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #30. Is it enabled?
2026-04-27T11:50:13,624 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #30 is enabled
2026-04-27T11:50:13,677 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #31
2026-04-27T11:50:13,677 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:50:13,875 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #31. Is it enabled?
2026-04-27T11:50:20,771 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #31 is disabled
2026-04-27T11:50:20,808 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #32
2026-04-27T11:50:20,808 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:50:20,968 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #32. Is it enabled?
2026-04-27T11:50:34,379 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #32 is disabled
2026-04-27T11:50:34,406 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #33
2026-04-27T11:50:34,406 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:50:34,567 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #33. Is it enabled?
2026-04-27T11:50:37,633 [main] DEBUG a.f.a.i.p.PassChainExecutor - Adapted exception intercepted: 
at.forsyte.apalache.tla.bmcmt.SmtEncodingException: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
	at at.forsyte.apalache.tla.bmcmt.smt.Z3SolverContext.sat(Z3SolverContext.scala:557)
	at at.forsyte.apalache.tla.bmcmt.smt.Z3SolverContext.satOrTimeout(Z3SolverContext.scala:564)
	at at.forsyte.apalache.tla.bmcmt.smt.RecordingSolverContext.satOrTimeout(RecordingSolverContext.scala:205)
	at at.forsyte.apalache.tla.bmcmt.trex.TransitionExecutorImpl.sat(TransitionExecutorImpl.scala:349)
	at at.forsyte.apalache.tla.bmcmt.trex.FilteredTransitionExecutor.sat(FilteredTransitionExecutor.scala:181)
	at at.forsyte.apalache.tla.bmcmt.trex.ConstrainedTransitionExecutor.sat(ConstrainedTransitionExecutor.scala:127)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.\$anonfun\$prepareTransitionsAndCheckInvariants\$5(SeqModelChecker.scala:232)
	at scala.runtime.java8.JFunction1\$mcVI\$sp.apply(JFunction1\$mcVI\$sp.scala:18)
	at scala.collection.immutable.Range.foreach(Range.scala:256)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.prepareTransitionsAndCheckInvariants(SeqModelChecker.scala:213)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.makeStep(SeqModelChecker.scala:125)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.run(SeqModelChecker.scala:67)
	at at.forsyte.apalache.tla.bmcmt.passes.BoundedCheckerPassImpl.runIncrementalChecker(BoundedCheckerPassImpl.scala:164)
	at at.forsyte.apalache.tla.bmcmt.passes.BoundedCheckerPassImpl.execute(BoundedCheckerPassImpl.scala:116)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.exec(PassChainExecutor.scala:71)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.\$anonfun\$runPassOnModule\$3(PassChainExecutor.scala:60)
	at scala.util.Either.flatMap(Either.scala:360)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.\$anonfun\$runPassOnModule\$1(PassChainExecutor.scala:58)
	at scala.collection.LinearSeqOps.foldLeft(LinearSeq.scala:183)
	at scala.collection.LinearSeqOps.foldLeft\$(LinearSeq.scala:179)
	at scala.collection.immutable.List.foldLeft(List.scala:79)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.runOnPasses(PassChainExecutor.scala:51)
	at at.forsyte.apalache.infra.passes.PassChainExecutor.run(PassChainExecutor.scala:42)
	at at.forsyte.apalache.tla.tooling.opt.CheckCmd.run(CheckCmd.scala:137)
	at at.forsyte.apalache.tla.Tool\$.runCommand(Tool.scala:139)
	at at.forsyte.apalache.tla.Tool\$.run(Tool.scala:119)
	at at.forsyte.apalache.tla.Tool\$.main(Tool.scala:40)
	at at.forsyte.apalache.tla.Tool.main(Tool.scala)
2026-04-27T11:50:37,672 [main] ERROR a.f.a.t.Tool\$ - <unknown>: error when rewriting to SMT: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
at.forsyte.apalache.infra.AdaptedException: <unknown>: error when rewriting to SMT: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
	at at.forsyte.apalache.infra.passes.PassChainExecutor.run(PassChainExecutor.scala:47)
	at at.forsyte.apalache.tla.tooling.opt.CheckCmd.run(CheckCmd.scala:137)
	at at.forsyte.apalache.tla.Tool\$.runCommand(Tool.scala:139)
	at at.forsyte.apalache.tla.Tool\$.run(Tool.scala:119)
	at at.forsyte.apalache.tla.Tool\$.main(Tool.scala:40)
	at at.forsyte.apalache.tla.Tool.main(Tool.scala)
```
</details>

## System information

- Apalache version: `0.56.1 build 70cdaf4`
- OS: `Linux`
- JDK version: `21.0.10`

## Triage checklist (for maintainers)

<!-- This section is for maintainers -->

- [ ] Reproduce the bug on the main development branch.
- [ ] Add the issue to the apalache GitHub project.
- [ ] If the bug is high impact, ensure someone available is assigned to fix it.

