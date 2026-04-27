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
--inv=Agreement --config=AccordSpec.cfg --length=30
```

## Expected behavior

<!-- What did you expect to see? -->

## Log files

<details>

```
2026-04-27T11:51:32,348 [main] INFO  a.f.a.t.Tool\$ - # APALACHE version: 0.56.1 | build: 70cdaf4
2026-04-27T11:51:32,374 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > AccordSpec.cfg: Loading TLC configuration
2026-04-27T11:51:32,419 [main] WARN  a.f.a.i.t.TlcConfigParserApalache\$ - TLC config option CHECK_DEADLOCK true will be ignored
2026-04-27T11:51:32,426 [main] WARN  a.f.a.i.p.o.OptionGroup\$ -   >  inv is set in TLC config but overridden via `inv` cli option or apalache.cfg; using Agreement
2026-04-27T11:51:32,428 [main] INFO  a.f.a.t.t.o.CheckCmd - Tuning: search.outputTraces=false
2026-04-27T11:51:32,608 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser
2026-04-27T11:51:33,289 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser [OK]
2026-04-27T11:51:33,290 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat
2026-04-27T11:51:33,290 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Running Snowcat .::.
2026-04-27T11:51:42,028 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Your types are purrfect!
2026-04-27T11:51:42,028 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > All expressions are typed
2026-04-27T11:51:42,028 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat [OK]
2026-04-27T11:51:42,029 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass
2026-04-27T11:51:42,208 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: Using SPECIFICATION Spec
2026-04-27T11:51:42,209 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: found INVARIANTS: Agreement
2026-04-27T11:51:42,211 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the initialization predicate to Init
2026-04-27T11:51:42,212 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the transition predicate to Next
2026-04-27T11:51:42,212 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the constant initialization predicate to CInit
2026-04-27T11:51:42,212 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Agreement
2026-04-27T11:51:42,219 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass [OK]
2026-04-27T11:51:42,219 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass
2026-04-27T11:51:42,219 [main] INFO  a.f.a.t.p.p.DesugarerPassImpl -   > Desugaring...
2026-04-27T11:51:42,245 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass [OK]
2026-04-27T11:51:42,246 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass
2026-04-27T11:51:42,246 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next
2026-04-27T11:51:42,451 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass [OK]
2026-04-27T11:51:42,451 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass
2026-04-27T11:51:42,451 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > Rewriting temporal operators...
2026-04-27T11:51:42,451 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > No temporal property specified, nothing to encode
2026-04-27T11:51:42,451 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass [OK]
2026-04-27T11:51:42,451 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass
2026-04-27T11:51:42,452 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next
2026-04-27T11:51:42,498 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass [OK]
2026-04-27T11:51:42,498 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass
2026-04-27T11:51:42,500 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing CInitPrimed for CInit'
2026-04-27T11:51:42,501 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing InitPrimed for Init'
2026-04-27T11:51:42,501 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass [OK]
2026-04-27T11:51:42,501 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #8: VCGen
2026-04-27T11:51:42,501 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Agreement
2026-04-27T11:51:42,506 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-04-27T11:51:42,516 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #8: VCGen [OK]
2026-04-27T11:51:42,516 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass
2026-04-27T11:51:42,517 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Before preprocessing: unique renaming
2026-04-27T11:51:42,528 [main] INFO  a.f.a.t.p.p.PreproPassImpl -  > Applying standard transformations:
2026-04-27T11:51:42,529 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > PrimePropagation
2026-04-27T11:51:42,541 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Desugarer
2026-04-27T11:51:42,563 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > UniqueRenamer
2026-04-27T11:51:42,625 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Normalizer
2026-04-27T11:51:42,659 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Keramelizer
2026-04-27T11:51:42,694 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > After preprocessing: UniqueRenamer
2026-04-27T11:51:42,742 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass [OK]
2026-04-27T11:51:42,742 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass
2026-04-27T11:51:42,795 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 1 initializing transitions
2026-04-27T11:51:42,915 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 70 transitions
2026-04-27T11:51:42,917 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found constant initializer CInit
2026-04-27T11:51:42,921 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Applying unique renaming
2026-04-27T11:51:43,022 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass [OK]
2026-04-27T11:51:43,022 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass
2026-04-27T11:51:43,037 [main] INFO  a.f.a.t.p.p.OptPassImpl -  > Applying optimizations:
2026-04-27T11:51:43,038 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-04-27T11:51:43,157 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ExprOptimizer
2026-04-27T11:51:43,216 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > SetMembershipSimplifier
2026-04-27T11:51:43,230 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-04-27T11:51:43,320 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass [OK]
2026-04-27T11:51:43,321 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass
2026-04-27T11:51:43,324 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Marking skolemizable existentials and sets to be expanded...
2026-04-27T11:51:43,325 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Skolemization
2026-04-27T11:51:43,336 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Expansion
2026-04-27T11:51:43,365 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Remove unused let-in defs
2026-04-27T11:51:43,397 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Running analyzers...
2026-04-27T11:51:43,402 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Introduced expression grades
2026-04-27T11:51:43,403 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass [OK]
2026-04-27T11:51:43,403 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #13: BoundedChecker
2026-04-27T11:51:43,426 [main] DEBUG a.f.a.t.b.s.Z3SolverContext - Creating Z3 solver context 0
2026-04-27T11:51:43,648 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Initializing CONSTANTS
2026-04-27T11:51:43,696 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #0, transition #0
2026-04-27T11:51:43,696 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,726 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0. Is it enabled?
2026-04-27T11:51:43,728 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0 is enabled
2026-04-27T11:51:43,728 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: Checking 1 state invariants
2026-04-27T11:51:43,729 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 0
2026-04-27T11:51:43,765 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 0 holds.
2026-04-27T11:51:43,768 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 0: picking a transition out of 1 transition(s)
2026-04-27T11:51:43,770 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #0
2026-04-27T11:51:43,770 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,773 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #0. Is it enabled?
2026-04-27T11:51:43,773 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #0 is disabled
2026-04-27T11:51:43,774 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #1
2026-04-27T11:51:43,774 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,775 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #1. Is it enabled?
2026-04-27T11:51:43,776 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #1 is disabled
2026-04-27T11:51:43,776 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #2
2026-04-27T11:51:43,776 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,778 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #2. Is it enabled?
2026-04-27T11:51:43,778 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #2 is disabled
2026-04-27T11:51:43,778 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #3
2026-04-27T11:51:43,778 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T11:51:43,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #4
2026-04-27T11:51:43,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T11:51:43,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #5
2026-04-27T11:51:43,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,780 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #5. Is it enabled?
2026-04-27T11:51:43,780 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #5 is disabled
2026-04-27T11:51:43,781 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #6
2026-04-27T11:51:43,781 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,782 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #6. Is it enabled?
2026-04-27T11:51:43,782 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #6 is disabled
2026-04-27T11:51:43,782 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #7
2026-04-27T11:51:43,782 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,782 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T11:51:43,782 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #8
2026-04-27T11:51:43,782 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,783 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T11:51:43,783 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #9
2026-04-27T11:51:43,783 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,784 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #9. Is it enabled?
2026-04-27T11:51:43,784 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #9 is disabled
2026-04-27T11:51:43,784 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #10
2026-04-27T11:51:43,784 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,786 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #10. Is it enabled?
2026-04-27T11:51:43,786 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #10 is disabled
2026-04-27T11:51:43,786 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #11
2026-04-27T11:51:43,786 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,788 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #11. Is it enabled?
2026-04-27T11:51:43,788 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #11 is disabled
2026-04-27T11:51:43,788 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #12
2026-04-27T11:51:43,788 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,790 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #12. Is it enabled?
2026-04-27T11:51:43,791 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #12 is disabled
2026-04-27T11:51:43,791 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #13
2026-04-27T11:51:43,791 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,794 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #13. Is it enabled?
2026-04-27T11:51:43,794 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #13 is disabled
2026-04-27T11:51:43,794 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #14
2026-04-27T11:51:43,794 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,797 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #14. Is it enabled?
2026-04-27T11:51:43,797 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #14 is disabled
2026-04-27T11:51:43,797 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #15
2026-04-27T11:51:43,798 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,799 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #15. Is it enabled?
2026-04-27T11:51:43,800 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #15 is disabled
2026-04-27T11:51:43,800 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #16
2026-04-27T11:51:43,800 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:43,969 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16. Is it enabled?
2026-04-27T11:51:43,972 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16 is enabled
2026-04-27T11:51:43,973 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: Checking 1 state invariants
2026-04-27T11:51:43,974 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 0
2026-04-27T11:51:43,995 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 0 holds.
2026-04-27T11:51:43,996 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #17
2026-04-27T11:51:43,996 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,029 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #17. Is it enabled?
2026-04-27T11:51:44,031 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #17 is disabled
2026-04-27T11:51:44,032 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #18
2026-04-27T11:51:44,032 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,037 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T11:51:44,038 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #19
2026-04-27T11:51:44,038 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,043 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T11:51:44,043 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #20
2026-04-27T11:51:44,043 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,047 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T11:51:44,047 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #21
2026-04-27T11:51:44,047 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,079 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #21. Is it enabled?
2026-04-27T11:51:44,082 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #21 is disabled
2026-04-27T11:51:44,086 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #22
2026-04-27T11:51:44,086 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,101 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T11:51:44,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #23
2026-04-27T11:51:44,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,104 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T11:51:44,105 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #24
2026-04-27T11:51:44,105 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,173 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #24. Is it enabled?
2026-04-27T11:51:44,175 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #24 is disabled
2026-04-27T11:51:44,176 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #25
2026-04-27T11:51:44,176 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,179 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T11:51:44,180 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #26
2026-04-27T11:51:44,180 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,208 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #26. Is it enabled?
2026-04-27T11:51:44,210 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #26 is disabled
2026-04-27T11:51:44,211 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #27
2026-04-27T11:51:44,211 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,222 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #27. Is it enabled?
2026-04-27T11:51:44,223 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #27 is disabled
2026-04-27T11:51:44,223 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #28
2026-04-27T11:51:44,223 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,348 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #28. Is it enabled?
2026-04-27T11:51:44,353 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #28 is disabled
2026-04-27T11:51:44,355 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #29
2026-04-27T11:51:44,356 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,475 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #29. Is it enabled?
2026-04-27T11:51:44,479 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #29 is disabled
2026-04-27T11:51:44,481 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #30
2026-04-27T11:51:44,482 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,617 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #30. Is it enabled?
2026-04-27T11:51:44,622 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #30 is disabled
2026-04-27T11:51:44,625 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #31
2026-04-27T11:51:44,626 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,683 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #31. Is it enabled?
2026-04-27T11:51:44,686 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #31 is disabled
2026-04-27T11:51:44,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #32
2026-04-27T11:51:44,687 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,735 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #32. Is it enabled?
2026-04-27T11:51:44,739 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #32 is disabled
2026-04-27T11:51:44,740 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #33
2026-04-27T11:51:44,740 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,787 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #33. Is it enabled?
2026-04-27T11:51:44,790 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #33 is disabled
2026-04-27T11:51:44,792 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #34
2026-04-27T11:51:44,792 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,840 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #34. Is it enabled?
2026-04-27T11:51:44,843 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #34 is disabled
2026-04-27T11:51:44,844 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #35
2026-04-27T11:51:44,845 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,890 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #35. Is it enabled?
2026-04-27T11:51:44,894 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #35 is disabled
2026-04-27T11:51:44,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #36
2026-04-27T11:51:44,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,897 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T11:51:44,897 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #37
2026-04-27T11:51:44,898 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,924 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #37. Is it enabled?
2026-04-27T11:51:44,926 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #37 is disabled
2026-04-27T11:51:44,927 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #38
2026-04-27T11:51:44,927 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,928 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T11:51:44,929 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #39
2026-04-27T11:51:44,929 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,949 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #39. Is it enabled?
2026-04-27T11:51:44,951 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #39 is disabled
2026-04-27T11:51:44,952 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #40
2026-04-27T11:51:44,952 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,953 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T11:51:44,954 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #41
2026-04-27T11:51:44,954 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,968 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #41. Is it enabled?
2026-04-27T11:51:44,969 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #41 is disabled
2026-04-27T11:51:44,970 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #42
2026-04-27T11:51:44,970 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,971 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T11:51:44,971 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #43
2026-04-27T11:51:44,971 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:44,990 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #43. Is it enabled?
2026-04-27T11:51:44,992 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #43 is disabled
2026-04-27T11:51:44,992 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #44
2026-04-27T11:51:44,992 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,024 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #44. Is it enabled?
2026-04-27T11:51:45,026 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #44 is disabled
2026-04-27T11:51:45,027 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #45
2026-04-27T11:51:45,028 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,050 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #45. Is it enabled?
2026-04-27T11:51:45,052 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #45 is disabled
2026-04-27T11:51:45,054 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #46
2026-04-27T11:51:45,054 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,113 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #46. Is it enabled?
2026-04-27T11:51:45,115 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #46 is disabled
2026-04-27T11:51:45,116 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #47
2026-04-27T11:51:45,116 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,143 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #47. Is it enabled?
2026-04-27T11:51:45,145 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #47 is disabled
2026-04-27T11:51:45,146 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #48
2026-04-27T11:51:45,146 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,170 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #48. Is it enabled?
2026-04-27T11:51:45,172 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #48 is disabled
2026-04-27T11:51:45,172 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #49
2026-04-27T11:51:45,172 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,211 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #49. Is it enabled?
2026-04-27T11:51:45,214 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #49 is disabled
2026-04-27T11:51:45,215 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #50
2026-04-27T11:51:45,215 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,230 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #50. Is it enabled?
2026-04-27T11:51:45,231 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #50 is disabled
2026-04-27T11:51:45,231 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #51
2026-04-27T11:51:45,231 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,253 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #51. Is it enabled?
2026-04-27T11:51:45,255 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #51 is disabled
2026-04-27T11:51:45,256 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #52
2026-04-27T11:51:45,256 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,302 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #52. Is it enabled?
2026-04-27T11:51:45,305 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #52 is disabled
2026-04-27T11:51:45,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #53
2026-04-27T11:51:45,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,333 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #53. Is it enabled?
2026-04-27T11:51:45,336 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #53 is disabled
2026-04-27T11:51:45,337 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #54
2026-04-27T11:51:45,337 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,360 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #54. Is it enabled?
2026-04-27T11:51:45,362 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #54 is disabled
2026-04-27T11:51:45,363 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #55
2026-04-27T11:51:45,363 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,367 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-04-27T11:51:45,367 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #56
2026-04-27T11:51:45,367 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,372 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #56. Is it enabled?
2026-04-27T11:51:45,373 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #56 is disabled
2026-04-27T11:51:45,374 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #57
2026-04-27T11:51:45,374 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,378 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-04-27T11:51:45,379 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #58
2026-04-27T11:51:45,379 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,383 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #58. Is it enabled?
2026-04-27T11:51:45,385 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #58 is disabled
2026-04-27T11:51:45,386 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #59
2026-04-27T11:51:45,386 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,394 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T11:51:45,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #60
2026-04-27T11:51:45,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,401 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #60. Is it enabled?
2026-04-27T11:51:45,401 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #60 is disabled
2026-04-27T11:51:45,402 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #61
2026-04-27T11:51:45,402 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,405 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T11:51:45,405 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #62
2026-04-27T11:51:45,405 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,409 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #62. Is it enabled?
2026-04-27T11:51:45,410 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #62 is disabled
2026-04-27T11:51:45,411 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #63
2026-04-27T11:51:45,411 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,415 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #63. Is it enabled?
2026-04-27T11:51:45,416 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #63 is disabled
2026-04-27T11:51:45,416 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #64
2026-04-27T11:51:45,416 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,420 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #64. Is it enabled?
2026-04-27T11:51:45,420 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #64 is disabled
2026-04-27T11:51:45,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #65
2026-04-27T11:51:45,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,424 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #65. Is it enabled?
2026-04-27T11:51:45,425 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #65 is disabled
2026-04-27T11:51:45,425 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #66
2026-04-27T11:51:45,425 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,448 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #66. Is it enabled?
2026-04-27T11:51:45,451 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #66 is disabled
2026-04-27T11:51:45,452 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #67
2026-04-27T11:51:45,452 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,473 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #67. Is it enabled?
2026-04-27T11:51:45,475 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #67 is disabled
2026-04-27T11:51:45,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #68
2026-04-27T11:51:45,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,482 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #68. Is it enabled?
2026-04-27T11:51:45,483 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #68 is disabled
2026-04-27T11:51:45,483 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #69
2026-04-27T11:51:45,483 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,487 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #69. Is it enabled?
2026-04-27T11:51:45,488 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #69 is disabled
2026-04-27T11:51:45,488 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 1: picking a transition out of 1 transition(s)
2026-04-27T11:51:45,489 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #0
2026-04-27T11:51:45,489 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,521 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0. Is it enabled?
2026-04-27T11:51:45,529 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0 is enabled
2026-04-27T11:51:45,530 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: Checking 1 state invariants
2026-04-27T11:51:45,530 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 0
2026-04-27T11:51:45,539 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 0 holds.
2026-04-27T11:51:45,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #1
2026-04-27T11:51:45,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,601 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #1. Is it enabled?
2026-04-27T11:51:45,604 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #1 is disabled
2026-04-27T11:51:45,605 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #2
2026-04-27T11:51:45,605 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,628 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #2. Is it enabled?
2026-04-27T11:51:45,631 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #2 is disabled
2026-04-27T11:51:45,632 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #3
2026-04-27T11:51:45,632 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,635 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T11:51:45,635 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #4
2026-04-27T11:51:45,635 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,638 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T11:51:45,638 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #5
2026-04-27T11:51:45,638 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,657 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #5. Is it enabled?
2026-04-27T11:51:45,659 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #5 is disabled
2026-04-27T11:51:45,660 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #6
2026-04-27T11:51:45,660 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,679 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #6. Is it enabled?
2026-04-27T11:51:45,681 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #6 is disabled
2026-04-27T11:51:45,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #7
2026-04-27T11:51:45,683 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T11:51:45,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #8
2026-04-27T11:51:45,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,689 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T11:51:45,690 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #9
2026-04-27T11:51:45,690 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,709 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #9. Is it enabled?
2026-04-27T11:51:45,712 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #9 is disabled
2026-04-27T11:51:45,713 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #10
2026-04-27T11:51:45,713 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,731 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #10. Is it enabled?
2026-04-27T11:51:45,733 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #10 is disabled
2026-04-27T11:51:45,734 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #11
2026-04-27T11:51:45,734 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,747 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #11. Is it enabled?
2026-04-27T11:51:45,749 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #11 is disabled
2026-04-27T11:51:45,750 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #12
2026-04-27T11:51:45,750 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,789 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #12. Is it enabled?
2026-04-27T11:51:45,793 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #12 is disabled
2026-04-27T11:51:45,794 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #13
2026-04-27T11:51:45,794 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,836 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #13. Is it enabled?
2026-04-27T11:51:45,840 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #13 is disabled
2026-04-27T11:51:45,841 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #14
2026-04-27T11:51:45,841 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,880 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #14. Is it enabled?
2026-04-27T11:51:45,884 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #14 is disabled
2026-04-27T11:51:45,885 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #15
2026-04-27T11:51:45,886 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,948 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #15. Is it enabled?
2026-04-27T11:51:45,952 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #15 is disabled
2026-04-27T11:51:45,953 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #16
2026-04-27T11:51:45,953 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:45,974 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #16. Is it enabled?
2026-04-27T11:51:45,976 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #16 is disabled
2026-04-27T11:51:45,976 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #17
2026-04-27T11:51:45,976 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,004 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #17. Is it enabled?
2026-04-27T11:51:46,006 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #17 is disabled
2026-04-27T11:51:46,007 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #18
2026-04-27T11:51:46,007 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,015 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T11:51:46,016 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #19
2026-04-27T11:51:46,016 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T11:51:46,022 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #20
2026-04-27T11:51:46,022 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,028 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T11:51:46,028 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #21
2026-04-27T11:51:46,028 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,060 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #21. Is it enabled?
2026-04-27T11:51:46,064 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #21 is disabled
2026-04-27T11:51:46,065 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #22
2026-04-27T11:51:46,065 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,079 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T11:51:46,080 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #23
2026-04-27T11:51:46,080 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,085 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T11:51:46,086 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #24
2026-04-27T11:51:46,086 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,113 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #24. Is it enabled?
2026-04-27T11:51:46,116 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #24 is disabled
2026-04-27T11:51:46,116 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #25
2026-04-27T11:51:46,116 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,122 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T11:51:46,123 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #26
2026-04-27T11:51:46,123 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,169 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #26. Is it enabled?
2026-04-27T11:51:46,172 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #26 is disabled
2026-04-27T11:51:46,172 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #27
2026-04-27T11:51:46,172 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,193 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #27. Is it enabled?
2026-04-27T11:51:46,194 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #27 is disabled
2026-04-27T11:51:46,195 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #28
2026-04-27T11:51:46,195 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,250 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #28. Is it enabled?
2026-04-27T11:51:46,256 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #28 is disabled
2026-04-27T11:51:46,257 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #29
2026-04-27T11:51:46,257 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,308 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #29. Is it enabled?
2026-04-27T11:51:46,312 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #29 is disabled
2026-04-27T11:51:46,313 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #30
2026-04-27T11:51:46,313 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,351 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30. Is it enabled?
2026-04-27T11:51:46,362 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30 is enabled
2026-04-27T11:51:46,363 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #31
2026-04-27T11:51:46,363 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,400 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #31. Is it enabled?
2026-04-27T11:51:46,407 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #31 is disabled
2026-04-27T11:51:46,409 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #32
2026-04-27T11:51:46,409 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,463 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #32. Is it enabled?
2026-04-27T11:51:46,468 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #32 is disabled
2026-04-27T11:51:46,470 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #33
2026-04-27T11:51:46,470 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,536 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #33. Is it enabled?
2026-04-27T11:51:46,541 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #33 is disabled
2026-04-27T11:51:46,542 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #34
2026-04-27T11:51:46,542 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,619 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #34. Is it enabled?
2026-04-27T11:51:46,626 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #34 is disabled
2026-04-27T11:51:46,628 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #35
2026-04-27T11:51:46,628 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,665 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #35. Is it enabled?
2026-04-27T11:51:46,673 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #35 is disabled
2026-04-27T11:51:46,674 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #36
2026-04-27T11:51:46,675 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,712 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T11:51:46,714 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #37
2026-04-27T11:51:46,714 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,773 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #37. Is it enabled?
2026-04-27T11:51:46,776 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #37 is disabled
2026-04-27T11:51:46,777 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #38
2026-04-27T11:51:46,777 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,785 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T11:51:46,786 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #39
2026-04-27T11:51:46,786 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,815 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #39. Is it enabled?
2026-04-27T11:51:46,818 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #39 is disabled
2026-04-27T11:51:46,819 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #40
2026-04-27T11:51:46,819 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,827 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T11:51:46,828 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #41
2026-04-27T11:51:46,828 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,851 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #41. Is it enabled?
2026-04-27T11:51:46,853 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #41 is disabled
2026-04-27T11:51:46,854 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #42
2026-04-27T11:51:46,854 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,862 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T11:51:46,863 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #43
2026-04-27T11:51:46,863 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,887 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #43. Is it enabled?
2026-04-27T11:51:46,889 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #43 is disabled
2026-04-27T11:51:46,890 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #44
2026-04-27T11:51:46,890 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,928 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #44. Is it enabled?
2026-04-27T11:51:46,931 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #44 is disabled
2026-04-27T11:51:46,932 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #45
2026-04-27T11:51:46,932 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:46,961 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #45. Is it enabled?
2026-04-27T11:51:46,964 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #45 is disabled
2026-04-27T11:51:46,965 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #46
2026-04-27T11:51:46,965 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,029 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #46. Is it enabled?
2026-04-27T11:51:47,033 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #46 is disabled
2026-04-27T11:51:47,035 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #47
2026-04-27T11:51:47,035 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,071 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #47. Is it enabled?
2026-04-27T11:51:47,074 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #47 is disabled
2026-04-27T11:51:47,076 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #48
2026-04-27T11:51:47,076 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,113 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #48. Is it enabled?
2026-04-27T11:51:47,117 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #48 is disabled
2026-04-27T11:51:47,118 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #49
2026-04-27T11:51:47,118 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,160 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #49. Is it enabled?
2026-04-27T11:51:47,165 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #49 is disabled
2026-04-27T11:51:47,166 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #50
2026-04-27T11:51:47,166 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,193 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #50. Is it enabled?
2026-04-27T11:51:47,195 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #50 is disabled
2026-04-27T11:51:47,196 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #51
2026-04-27T11:51:47,196 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,234 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #51. Is it enabled?
2026-04-27T11:51:47,238 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #51 is disabled
2026-04-27T11:51:47,239 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #52
2026-04-27T11:51:47,239 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,294 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #52. Is it enabled?
2026-04-27T11:51:47,298 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #52 is disabled
2026-04-27T11:51:47,300 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #53
2026-04-27T11:51:47,300 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,327 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #53. Is it enabled?
2026-04-27T11:51:47,330 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #53 is disabled
2026-04-27T11:51:47,331 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #54
2026-04-27T11:51:47,331 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,354 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #54. Is it enabled?
2026-04-27T11:51:47,356 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #54 is disabled
2026-04-27T11:51:47,357 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #55
2026-04-27T11:51:47,357 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,360 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-04-27T11:51:47,360 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #56
2026-04-27T11:51:47,360 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,380 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #56. Is it enabled?
2026-04-27T11:51:47,383 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #56 is disabled
2026-04-27T11:51:47,383 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #57
2026-04-27T11:51:47,383 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,386 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-04-27T11:51:47,387 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #58
2026-04-27T11:51:47,387 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,408 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #58. Is it enabled?
2026-04-27T11:51:47,411 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #58 is disabled
2026-04-27T11:51:47,412 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #59
2026-04-27T11:51:47,412 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,415 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T11:51:47,416 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #60
2026-04-27T11:51:47,416 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,431 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #60. Is it enabled?
2026-04-27T11:51:47,433 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #60 is disabled
2026-04-27T11:51:47,434 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #61
2026-04-27T11:51:47,434 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T11:51:47,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #62
2026-04-27T11:51:47,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,453 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #62. Is it enabled?
2026-04-27T11:51:47,455 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #62 is disabled
2026-04-27T11:51:47,456 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #63
2026-04-27T11:51:47,456 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,474 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #63. Is it enabled?
2026-04-27T11:51:47,476 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #63 is disabled
2026-04-27T11:51:47,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #64
2026-04-27T11:51:47,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,504 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #64. Is it enabled?
2026-04-27T11:51:47,508 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #64 is disabled
2026-04-27T11:51:47,509 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #65
2026-04-27T11:51:47,509 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,514 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #65. Is it enabled?
2026-04-27T11:51:47,515 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #65 is disabled
2026-04-27T11:51:47,515 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #66
2026-04-27T11:51:47,515 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,543 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #66. Is it enabled?
2026-04-27T11:51:47,546 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #66 is disabled
2026-04-27T11:51:47,547 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #67
2026-04-27T11:51:47,547 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,571 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #67. Is it enabled?
2026-04-27T11:51:47,573 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #67 is disabled
2026-04-27T11:51:47,574 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #68
2026-04-27T11:51:47,574 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,615 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #68. Is it enabled?
2026-04-27T11:51:47,617 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #68 is disabled
2026-04-27T11:51:47,617 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #69
2026-04-27T11:51:47,617 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,650 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #69. Is it enabled?
2026-04-27T11:51:47,653 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #69 is disabled
2026-04-27T11:51:47,654 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 2: picking a transition out of 2 transition(s)
2026-04-27T11:51:47,689 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #0
2026-04-27T11:51:47,689 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,738 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0. Is it enabled?
2026-04-27T11:51:47,767 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0 is enabled
2026-04-27T11:51:47,768 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 1 state invariants
2026-04-27T11:51:47,768 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-04-27T11:51:47,786 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-04-27T11:51:47,787 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #1
2026-04-27T11:51:47,787 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,827 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #1. Is it enabled?
2026-04-27T11:51:47,834 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #1 is disabled
2026-04-27T11:51:47,835 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #2
2026-04-27T11:51:47,835 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,896 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #2. Is it enabled?
2026-04-27T11:51:47,901 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #2 is disabled
2026-04-27T11:51:47,902 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #3
2026-04-27T11:51:47,902 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,909 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T11:51:47,911 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #4
2026-04-27T11:51:47,911 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,920 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T11:51:47,922 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #5
2026-04-27T11:51:47,923 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:47,970 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #5. Is it enabled?
2026-04-27T11:51:47,977 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #5 is disabled
2026-04-27T11:51:47,978 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #6
2026-04-27T11:51:47,978 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,007 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #6. Is it enabled?
2026-04-27T11:51:48,013 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #6 is disabled
2026-04-27T11:51:48,015 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #7
2026-04-27T11:51:48,015 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T11:51:48,022 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #8
2026-04-27T11:51:48,022 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,027 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T11:51:48,028 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #9
2026-04-27T11:51:48,028 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,057 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #9. Is it enabled?
2026-04-27T11:51:48,062 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #9 is disabled
2026-04-27T11:51:48,064 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #10
2026-04-27T11:51:48,064 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,093 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #10. Is it enabled?
2026-04-27T11:51:48,097 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #10 is disabled
2026-04-27T11:51:48,099 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #11
2026-04-27T11:51:48,099 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,122 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #11. Is it enabled?
2026-04-27T11:51:48,127 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #11 is disabled
2026-04-27T11:51:48,129 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #12
2026-04-27T11:51:48,129 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,187 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #12. Is it enabled?
2026-04-27T11:51:48,198 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #12 is disabled
2026-04-27T11:51:48,201 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #13
2026-04-27T11:51:48,201 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,312 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #13. Is it enabled?
2026-04-27T11:51:48,330 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #13 is disabled
2026-04-27T11:51:48,332 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #14
2026-04-27T11:51:48,332 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,388 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #14. Is it enabled?
2026-04-27T11:51:48,400 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #14 is disabled
2026-04-27T11:51:48,402 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #15
2026-04-27T11:51:48,402 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,457 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #15. Is it enabled?
2026-04-27T11:51:48,621 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #15 is enabled
2026-04-27T11:51:48,621 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 1 state invariants
2026-04-27T11:51:48,621 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-04-27T11:51:48,648 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-04-27T11:51:48,650 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #16
2026-04-27T11:51:48,650 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,673 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #16. Is it enabled?
2026-04-27T11:51:48,676 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #16 is disabled
2026-04-27T11:51:48,677 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #17
2026-04-27T11:51:48,677 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,728 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #17. Is it enabled?
2026-04-27T11:51:48,873 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #17 is enabled
2026-04-27T11:51:48,874 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 1 state invariants
2026-04-27T11:51:48,874 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-04-27T11:51:48,896 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-04-27T11:51:48,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #18
2026-04-27T11:51:48,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,907 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T11:51:48,908 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #19
2026-04-27T11:51:48,908 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,916 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T11:51:48,917 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #20
2026-04-27T11:51:48,917 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,925 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T11:51:48,926 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #21
2026-04-27T11:51:48,926 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:48,996 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #21. Is it enabled?
2026-04-27T11:51:49,028 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #21 is disabled
2026-04-27T11:51:49,031 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #22
2026-04-27T11:51:49,031 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,056 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T11:51:49,061 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #23
2026-04-27T11:51:49,061 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,068 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T11:51:49,069 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #24
2026-04-27T11:51:49,069 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,103 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #24. Is it enabled?
2026-04-27T11:51:49,108 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #24 is disabled
2026-04-27T11:51:49,110 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #25
2026-04-27T11:51:49,110 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,119 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T11:51:49,120 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #26
2026-04-27T11:51:49,120 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,158 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #26. Is it enabled?
2026-04-27T11:51:49,163 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #26 is disabled
2026-04-27T11:51:49,165 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #27
2026-04-27T11:51:49,165 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,187 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #27. Is it enabled?
2026-04-27T11:51:49,189 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #27 is disabled
2026-04-27T11:51:49,191 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #28
2026-04-27T11:51:49,191 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,231 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #28. Is it enabled?
2026-04-27T11:51:49,238 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #28 is disabled
2026-04-27T11:51:49,240 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #29
2026-04-27T11:51:49,240 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,279 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #29. Is it enabled?
2026-04-27T11:51:49,285 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #29 is disabled
2026-04-27T11:51:49,287 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #30
2026-04-27T11:51:49,287 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,353 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #30. Is it enabled?
2026-04-27T11:51:49,587 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #30 is enabled
2026-04-27T11:51:49,590 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #31
2026-04-27T11:51:49,590 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,679 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #31. Is it enabled?
2026-04-27T11:51:49,697 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #31 is disabled
2026-04-27T11:51:49,699 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #32
2026-04-27T11:51:49,699 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,741 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #32. Is it enabled?
2026-04-27T11:51:49,748 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #32 is disabled
2026-04-27T11:51:49,750 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #33
2026-04-27T11:51:49,750 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,791 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #33. Is it enabled?
2026-04-27T11:51:49,797 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #33 is disabled
2026-04-27T11:51:49,799 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #34
2026-04-27T11:51:49,799 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,839 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #34. Is it enabled?
2026-04-27T11:51:49,869 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #34 is disabled
2026-04-27T11:51:49,871 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #35
2026-04-27T11:51:49,871 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,912 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #35. Is it enabled?
2026-04-27T11:51:49,932 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #35 is disabled
2026-04-27T11:51:49,934 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #36
2026-04-27T11:51:49,934 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,950 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T11:51:49,951 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #37
2026-04-27T11:51:49,951 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:49,993 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #37. Is it enabled?
2026-04-27T11:51:49,998 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #37 is disabled
2026-04-27T11:51:50,000 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #38
2026-04-27T11:51:50,000 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,016 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T11:51:50,018 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #39
2026-04-27T11:51:50,018 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,062 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #39. Is it enabled?
2026-04-27T11:51:50,068 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #39 is disabled
2026-04-27T11:51:50,070 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #40
2026-04-27T11:51:50,070 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,109 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T11:51:50,111 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #41
2026-04-27T11:51:50,111 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,160 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #41. Is it enabled?
2026-04-27T11:51:50,167 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #41 is disabled
2026-04-27T11:51:50,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #42
2026-04-27T11:51:50,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,203 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T11:51:50,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #43
2026-04-27T11:51:50,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,274 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #43. Is it enabled?
2026-04-27T11:51:50,280 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #43 is disabled
2026-04-27T11:51:50,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #44
2026-04-27T11:51:50,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,328 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #44. Is it enabled?
2026-04-27T11:51:50,334 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #44 is disabled
2026-04-27T11:51:50,335 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #45
2026-04-27T11:51:50,335 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,405 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #45. Is it enabled?
2026-04-27T11:51:50,411 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #45 is disabled
2026-04-27T11:51:50,414 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #46
2026-04-27T11:51:50,414 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,487 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #46. Is it enabled?
2026-04-27T11:51:50,494 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #46 is disabled
2026-04-27T11:51:50,497 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #47
2026-04-27T11:51:50,497 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,546 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #47. Is it enabled?
2026-04-27T11:51:50,553 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #47 is disabled
2026-04-27T11:51:50,555 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #48
2026-04-27T11:51:50,555 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,611 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #48. Is it enabled?
2026-04-27T11:51:50,620 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #48 is disabled
2026-04-27T11:51:50,622 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #49
2026-04-27T11:51:50,622 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,680 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #49. Is it enabled?
2026-04-27T11:51:50,688 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #49 is disabled
2026-04-27T11:51:50,690 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #50
2026-04-27T11:51:50,690 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,737 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #50. Is it enabled?
2026-04-27T11:51:50,745 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #50 is disabled
2026-04-27T11:51:50,747 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #51
2026-04-27T11:51:50,747 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,829 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #51. Is it enabled?
2026-04-27T11:51:50,843 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #51 is disabled
2026-04-27T11:51:50,845 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #52
2026-04-27T11:51:50,845 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,915 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #52. Is it enabled?
2026-04-27T11:51:50,928 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #52 is disabled
2026-04-27T11:51:50,931 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #53
2026-04-27T11:51:50,931 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,966 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #53. Is it enabled?
2026-04-27T11:51:50,971 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #53 is disabled
2026-04-27T11:51:50,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #54
2026-04-27T11:51:50,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:50,998 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #54. Is it enabled?
2026-04-27T11:51:51,002 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #54 is disabled
2026-04-27T11:51:51,004 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #55
2026-04-27T11:51:51,004 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,007 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-04-27T11:51:51,008 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #56
2026-04-27T11:51:51,008 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,032 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #56. Is it enabled?
2026-04-27T11:51:51,036 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #56 is disabled
2026-04-27T11:51:51,037 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #57
2026-04-27T11:51:51,037 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,041 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-04-27T11:51:51,041 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #58
2026-04-27T11:51:51,041 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,066 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #58. Is it enabled?
2026-04-27T11:51:51,070 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #58 is disabled
2026-04-27T11:51:51,071 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #59
2026-04-27T11:51:51,071 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,074 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T11:51:51,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #60
2026-04-27T11:51:51,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,094 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #60. Is it enabled?
2026-04-27T11:51:51,096 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #60 is disabled
2026-04-27T11:51:51,097 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #61
2026-04-27T11:51:51,097 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,100 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T11:51:51,101 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #62
2026-04-27T11:51:51,101 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,121 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #62. Is it enabled?
2026-04-27T11:51:51,125 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #62 is disabled
2026-04-27T11:51:51,126 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #63
2026-04-27T11:51:51,127 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,149 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #63. Is it enabled?
2026-04-27T11:51:51,152 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #63 is disabled
2026-04-27T11:51:51,153 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #64
2026-04-27T11:51:51,153 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,187 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #64. Is it enabled?
2026-04-27T11:51:51,193 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #64 is disabled
2026-04-27T11:51:51,195 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #65
2026-04-27T11:51:51,195 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,202 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #65. Is it enabled?
2026-04-27T11:51:51,203 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #65 is disabled
2026-04-27T11:51:51,204 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #66
2026-04-27T11:51:51,204 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,233 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #66. Is it enabled?
2026-04-27T11:51:51,238 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #66 is disabled
2026-04-27T11:51:51,240 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #67
2026-04-27T11:51:51,240 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,266 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #67. Is it enabled?
2026-04-27T11:51:51,270 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #67 is disabled
2026-04-27T11:51:51,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #68
2026-04-27T11:51:51,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,323 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #68. Is it enabled?
2026-04-27T11:51:51,327 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #68 is disabled
2026-04-27T11:51:51,328 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #69
2026-04-27T11:51:51,328 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,361 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #69. Is it enabled?
2026-04-27T11:51:51,367 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #69 is disabled
2026-04-27T11:51:51,369 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 3: picking a transition out of 4 transition(s)
2026-04-27T11:51:51,414 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #0
2026-04-27T11:51:51,415 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,465 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #0. Is it enabled?
2026-04-27T11:51:51,553 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #0 is disabled
2026-04-27T11:51:51,556 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #1
2026-04-27T11:51:51,556 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,603 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #1. Is it enabled?
2026-04-27T11:51:51,625 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #1 is disabled
2026-04-27T11:51:51,629 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #2
2026-04-27T11:51:51,629 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,680 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #2. Is it enabled?
2026-04-27T11:51:51,692 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #2 is disabled
2026-04-27T11:51:51,694 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #3
2026-04-27T11:51:51,694 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,705 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T11:51:51,707 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #4
2026-04-27T11:51:51,708 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,718 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T11:51:51,720 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #5
2026-04-27T11:51:51,720 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,763 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #5. Is it enabled?
2026-04-27T11:51:51,782 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #5 is disabled
2026-04-27T11:51:51,784 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #6
2026-04-27T11:51:51,784 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:51,828 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #6. Is it enabled?
2026-04-27T11:51:52,165 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #6 is enabled
2026-04-27T11:51:52,165 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:51:52,165 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:51:52,203 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:51:52,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #7
2026-04-27T11:51:52,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:52,217 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T11:51:52,219 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #8
2026-04-27T11:51:52,219 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:52,227 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T11:51:52,230 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #9
2026-04-27T11:51:52,230 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:52,305 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #9. Is it enabled?
2026-04-27T11:51:52,317 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #9 is disabled
2026-04-27T11:51:52,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #10
2026-04-27T11:51:52,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:52,362 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #10. Is it enabled?
2026-04-27T11:51:52,374 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #10 is disabled
2026-04-27T11:51:52,376 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #11
2026-04-27T11:51:52,376 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:52,414 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #11. Is it enabled?
2026-04-27T11:51:52,477 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #11 is disabled
2026-04-27T11:51:52,479 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #12
2026-04-27T11:51:52,480 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:52,551 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #12. Is it enabled?
2026-04-27T11:51:52,570 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #12 is disabled
2026-04-27T11:51:52,573 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #13
2026-04-27T11:51:52,573 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:52,644 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #13. Is it enabled?
2026-04-27T11:51:53,544 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #13 is enabled
2026-04-27T11:51:53,550 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #14
2026-04-27T11:51:53,550 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:53,620 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #14. Is it enabled?
2026-04-27T11:51:53,639 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #14 is disabled
2026-04-27T11:51:53,642 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #15
2026-04-27T11:51:53,642 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:53,713 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #15. Is it enabled?
2026-04-27T11:51:53,805 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #15 is disabled
2026-04-27T11:51:53,808 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #16
2026-04-27T11:51:53,808 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:53,832 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #16. Is it enabled?
2026-04-27T11:51:53,835 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #16 is disabled
2026-04-27T11:51:53,837 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #17
2026-04-27T11:51:53,837 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:53,988 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #17. Is it enabled?
2026-04-27T11:51:54,782 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #17 is enabled
2026-04-27T11:51:54,782 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:51:54,782 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:51:55,014 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:51:55,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #18
2026-04-27T11:51:55,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,033 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T11:51:55,035 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #19
2026-04-27T11:51:55,036 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,048 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T11:51:55,050 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #20
2026-04-27T11:51:55,050 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,063 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T11:51:55,065 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #21
2026-04-27T11:51:55,065 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,189 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #21. Is it enabled?
2026-04-27T11:51:55,435 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #21 is disabled
2026-04-27T11:51:55,439 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #22
2026-04-27T11:51:55,439 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T11:51:55,533 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #23
2026-04-27T11:51:55,533 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,546 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T11:51:55,547 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #24
2026-04-27T11:51:55,548 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,598 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #24. Is it enabled?
2026-04-27T11:51:55,603 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #24 is disabled
2026-04-27T11:51:55,606 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #25
2026-04-27T11:51:55,606 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,617 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T11:51:55,620 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #26
2026-04-27T11:51:55,620 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,673 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #26. Is it enabled?
2026-04-27T11:51:55,680 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #26 is disabled
2026-04-27T11:51:55,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #27
2026-04-27T11:51:55,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,721 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #27. Is it enabled?
2026-04-27T11:51:55,724 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #27 is disabled
2026-04-27T11:51:55,726 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #28
2026-04-27T11:51:55,726 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,788 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #28. Is it enabled?
2026-04-27T11:51:55,796 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #28 is disabled
2026-04-27T11:51:55,799 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #29
2026-04-27T11:51:55,799 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,841 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #29. Is it enabled?
2026-04-27T11:51:55,848 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #29 is disabled
2026-04-27T11:51:55,850 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #30
2026-04-27T11:51:55,850 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:55,892 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #30. Is it enabled?
2026-04-27T11:51:57,710 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #30 is enabled
2026-04-27T11:51:57,718 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #31
2026-04-27T11:51:57,719 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:57,758 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #31. Is it enabled?
2026-04-27T11:51:57,864 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #31 is disabled
2026-04-27T11:51:57,869 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #32
2026-04-27T11:51:57,869 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:57,912 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #32. Is it enabled?
2026-04-27T11:51:57,919 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #32 is disabled
2026-04-27T11:51:57,922 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #33
2026-04-27T11:51:57,922 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:57,962 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #33. Is it enabled?
2026-04-27T11:51:57,968 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #33 is disabled
2026-04-27T11:51:57,971 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #34
2026-04-27T11:51:57,971 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:58,013 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #34. Is it enabled?
2026-04-27T11:51:58,084 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #34 is disabled
2026-04-27T11:51:58,088 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #35
2026-04-27T11:51:58,088 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:58,129 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #35. Is it enabled?
2026-04-27T11:51:59,435 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #35 is enabled
2026-04-27T11:51:59,435 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:51:59,435 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:51:59,578 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:51:59,584 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #36
2026-04-27T11:51:59,584 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:59,610 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T11:51:59,613 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #37
2026-04-27T11:51:59,614 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:59,708 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #37. Is it enabled?
2026-04-27T11:51:59,895 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #37 is disabled
2026-04-27T11:51:59,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #38
2026-04-27T11:51:59,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:59,926 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T11:51:59,930 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #39
2026-04-27T11:51:59,930 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:51:59,998 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #39. Is it enabled?
2026-04-27T11:52:00,100 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #39 is disabled
2026-04-27T11:52:00,106 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #40
2026-04-27T11:52:00,106 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:00,135 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T11:52:00,138 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #41
2026-04-27T11:52:00,138 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:00,248 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #41. Is it enabled?
2026-04-27T11:52:00,421 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #41 is disabled
2026-04-27T11:52:00,429 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #42
2026-04-27T11:52:00,429 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:00,483 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T11:52:00,486 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #43
2026-04-27T11:52:00,486 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:00,549 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #43. Is it enabled?
2026-04-27T11:52:00,703 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #43 is disabled
2026-04-27T11:52:00,708 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #44
2026-04-27T11:52:00,708 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:00,778 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #44. Is it enabled?
2026-04-27T11:52:00,948 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #44 is disabled
2026-04-27T11:52:00,963 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #45
2026-04-27T11:52:00,963 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:01,049 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #45. Is it enabled?
2026-04-27T11:52:01,248 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #45 is disabled
2026-04-27T11:52:01,255 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #46
2026-04-27T11:52:01,255 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:01,373 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #46. Is it enabled?
2026-04-27T11:52:01,665 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #46 is disabled
2026-04-27T11:52:01,670 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #47
2026-04-27T11:52:01,670 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:01,749 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #47. Is it enabled?
2026-04-27T11:52:03,871 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #47 is enabled
2026-04-27T11:52:03,872 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 1 state invariants
2026-04-27T11:52:03,872 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T11:52:04,011 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T11:52:04,022 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #48
2026-04-27T11:52:04,022 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:04,107 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #48. Is it enabled?
2026-04-27T11:52:04,129 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #48 is disabled
2026-04-27T11:52:04,133 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #49
2026-04-27T11:52:04,133 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:04,239 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #49. Is it enabled?
2026-04-27T11:52:04,255 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #49 is disabled
2026-04-27T11:52:04,258 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #50
2026-04-27T11:52:04,258 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:04,339 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #50. Is it enabled?
2026-04-27T11:52:04,518 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #50 is disabled
2026-04-27T11:52:04,525 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #51
2026-04-27T11:52:04,526 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:04,607 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #51. Is it enabled?
2026-04-27T11:52:04,867 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #51 is disabled
2026-04-27T11:52:04,874 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #52
2026-04-27T11:52:04,874 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T11:52:04,990 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #52. Is it enabled?
2026-04-27T11:52:05,209 [main] DEBUG a.f.a.i.p.PassChainExecutor - Adapted exception intercepted: 
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
2026-04-27T11:52:05,251 [main] ERROR a.f.a.t.Tool\$ - <unknown>: error when rewriting to SMT: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
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

