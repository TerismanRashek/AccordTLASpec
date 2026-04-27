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
    [D |-> dep[p][id], S |-> S, W |-> W, WP |-> WP]

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
--config=AccordSpec.cfg --length=30
```

## Expected behavior

<!-- What did you expect to see? -->

## Log files

<details>

```
2026-04-27T12:27:24,855 [main] INFO  a.f.a.t.Tool\$ - # APALACHE version: 0.56.1 | build: 70cdaf4
2026-04-27T12:27:24,871 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > AccordSpec.cfg: Loading TLC configuration
2026-04-27T12:27:24,942 [main] WARN  a.f.a.i.t.TlcConfigParserApalache\$ - TLC config option CHECK_DEADLOCK true will be ignored
2026-04-27T12:27:24,956 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > Using inv predicate(s) Agreement, Ordering from the TLC config
2026-04-27T12:27:24,958 [main] INFO  a.f.a.t.t.o.SimulateCmd - Tuning: search.simulation.maxRun=100:search.simulation=true:search.outputTraces=false
2026-04-27T12:27:25,142 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser
2026-04-27T12:27:25,691 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser [OK]
2026-04-27T12:27:25,692 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat
2026-04-27T12:27:25,692 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Running Snowcat .::.
2026-04-27T12:27:34,583 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Your types are purrfect!
2026-04-27T12:27:34,584 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > All expressions are typed
2026-04-27T12:27:34,584 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat [OK]
2026-04-27T12:27:34,585 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass
2026-04-27T12:27:34,773 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: Using SPECIFICATION Spec
2026-04-27T12:27:34,776 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: found INVARIANTS: Agreement, Ordering
2026-04-27T12:27:34,781 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the initialization predicate to Init
2026-04-27T12:27:34,782 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the transition predicate to Next
2026-04-27T12:27:34,783 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the constant initialization predicate to CInit
2026-04-27T12:27:34,783 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Agreement
2026-04-27T12:27:34,783 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Ordering
2026-04-27T12:27:34,792 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass [OK]
2026-04-27T12:27:34,793 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass
2026-04-27T12:27:34,793 [main] INFO  a.f.a.t.p.p.DesugarerPassImpl -   > Desugaring...
2026-04-27T12:27:34,867 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass [OK]
2026-04-27T12:27:34,868 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass
2026-04-27T12:27:34,869 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next, Ordering
2026-04-27T12:27:35,102 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass [OK]
2026-04-27T12:27:35,103 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass
2026-04-27T12:27:35,103 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > Rewriting temporal operators...
2026-04-27T12:27:35,103 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > No temporal property specified, nothing to encode
2026-04-27T12:27:35,103 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass [OK]
2026-04-27T12:27:35,103 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass
2026-04-27T12:27:35,103 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next, Ordering
2026-04-27T12:27:35,152 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass [OK]
2026-04-27T12:27:35,153 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass
2026-04-27T12:27:35,155 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing CInitPrimed for CInit'
2026-04-27T12:27:35,155 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing InitPrimed for Init'
2026-04-27T12:27:35,156 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass [OK]
2026-04-27T12:27:35,156 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #8: VCGen
2026-04-27T12:27:35,156 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Agreement
2026-04-27T12:27:35,160 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-04-27T12:27:35,161 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Ordering
2026-04-27T12:27:35,161 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-04-27T12:27:35,162 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #8: VCGen [OK]
2026-04-27T12:27:35,162 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass
2026-04-27T12:27:35,162 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Before preprocessing: unique renaming
2026-04-27T12:27:35,167 [main] INFO  a.f.a.t.p.p.PreproPassImpl -  > Applying standard transformations:
2026-04-27T12:27:35,168 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > PrimePropagation
2026-04-27T12:27:35,177 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Desugarer
2026-04-27T12:27:35,187 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > UniqueRenamer
2026-04-27T12:27:35,223 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Normalizer
2026-04-27T12:27:35,245 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Keramelizer
2026-04-27T12:27:35,297 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > After preprocessing: UniqueRenamer
2026-04-27T12:27:35,358 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass [OK]
2026-04-27T12:27:35,358 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass
2026-04-27T12:27:35,413 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 1 initializing transitions
2026-04-27T12:27:35,495 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 70 transitions
2026-04-27T12:27:35,496 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found constant initializer CInit
2026-04-27T12:27:35,498 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Applying unique renaming
2026-04-27T12:27:35,618 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass [OK]
2026-04-27T12:27:35,619 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass
2026-04-27T12:27:35,626 [main] INFO  a.f.a.t.p.p.OptPassImpl -  > Applying optimizations:
2026-04-27T12:27:35,627 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-04-27T12:27:35,738 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ExprOptimizer
2026-04-27T12:27:35,808 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > SetMembershipSimplifier
2026-04-27T12:27:35,827 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-04-27T12:27:35,920 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass [OK]
2026-04-27T12:27:35,920 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass
2026-04-27T12:27:35,923 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Marking skolemizable existentials and sets to be expanded...
2026-04-27T12:27:35,923 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Skolemization
2026-04-27T12:27:35,933 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Expansion
2026-04-27T12:27:35,965 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Remove unused let-in defs
2026-04-27T12:27:35,994 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Running analyzers...
2026-04-27T12:27:35,998 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Introduced expression grades
2026-04-27T12:27:35,999 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass [OK]
2026-04-27T12:27:35,999 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #13: BoundedChecker
2026-04-27T12:27:36,021 [main] DEBUG a.f.a.t.b.s.Z3SolverContext - Creating Z3 solver context 0
2026-04-27T12:27:36,250 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Initializing CONSTANTS
2026-04-27T12:27:36,288 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #0, transition #0
2026-04-27T12:27:36,289 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:36,330 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0. Is it enabled?
2026-04-27T12:27:36,332 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0 is enabled
2026-04-27T12:27:36,332 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: Checking 2 state invariants
2026-04-27T12:27:36,333 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 0
2026-04-27T12:27:36,437 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 0 holds.
2026-04-27T12:27:36,441 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 1
2026-04-27T12:27:36,498 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 1 holds.
2026-04-27T12:27:36,499 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 0: randomly picked transition #0
2026-04-27T12:27:36,499 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 0: picking a transition out of 1 transition(s)
2026-04-27T12:27:36,501 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #67
2026-04-27T12:27:36,501 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:36,675 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #67. Is it enabled?
2026-04-27T12:27:36,682 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #67 is disabled
2026-04-27T12:27:36,685 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #31
2026-04-27T12:27:36,685 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,029 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #31. Is it enabled?
2026-04-27T12:27:37,039 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #31 is disabled
2026-04-27T12:27:37,042 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #36
2026-04-27T12:27:37,042 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,047 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T12:27:37,048 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #22
2026-04-27T12:27:37,048 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,053 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T12:27:37,053 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #30
2026-04-27T12:27:37,054 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,243 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #30. Is it enabled?
2026-04-27T12:27:37,252 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #30 is disabled
2026-04-27T12:27:37,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #62
2026-04-27T12:27:37,255 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,265 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #62. Is it enabled?
2026-04-27T12:27:37,266 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #62 is disabled
2026-04-27T12:27:37,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #20
2026-04-27T12:27:37,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,270 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T12:27:37,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #24
2026-04-27T12:27:37,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,325 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #24. Is it enabled?
2026-04-27T12:27:37,328 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #24 is disabled
2026-04-27T12:27:37,330 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #40
2026-04-27T12:27:37,330 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,333 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T12:27:37,334 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #48
2026-04-27T12:27:37,334 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,400 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #48. Is it enabled?
2026-04-27T12:27:37,405 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #48 is disabled
2026-04-27T12:27:37,406 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #7
2026-04-27T12:27:37,407 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,407 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T12:27:37,407 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #54
2026-04-27T12:27:37,407 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,460 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #54. Is it enabled?
2026-04-27T12:27:37,465 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #54 is disabled
2026-04-27T12:27:37,467 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #15
2026-04-27T12:27:37,467 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,469 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #15. Is it enabled?
2026-04-27T12:27:37,469 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #15 is disabled
2026-04-27T12:27:37,469 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #47
2026-04-27T12:27:37,469 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,571 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #47. Is it enabled?
2026-04-27T12:27:37,576 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #47 is disabled
2026-04-27T12:27:37,578 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #69
2026-04-27T12:27:37,578 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,587 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #69. Is it enabled?
2026-04-27T12:27:37,588 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #69 is disabled
2026-04-27T12:27:37,589 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #45
2026-04-27T12:27:37,589 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,647 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #45. Is it enabled?
2026-04-27T12:27:37,651 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #45 is disabled
2026-04-27T12:27:37,653 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #52
2026-04-27T12:27:37,653 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,748 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #52. Is it enabled?
2026-04-27T12:27:37,753 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #52 is disabled
2026-04-27T12:27:37,754 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #17
2026-04-27T12:27:37,754 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,788 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #17. Is it enabled?
2026-04-27T12:27:37,791 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #17 is disabled
2026-04-27T12:27:37,792 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #12
2026-04-27T12:27:37,792 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,793 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #12. Is it enabled?
2026-04-27T12:27:37,793 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #12 is disabled
2026-04-27T12:27:37,793 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #34
2026-04-27T12:27:37,793 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,887 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #34. Is it enabled?
2026-04-27T12:27:37,897 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #34 is disabled
2026-04-27T12:27:37,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #29
2026-04-27T12:27:37,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:37,983 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #29. Is it enabled?
2026-04-27T12:27:37,993 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #29 is disabled
2026-04-27T12:27:37,996 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #63
2026-04-27T12:27:37,996 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,003 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #63. Is it enabled?
2026-04-27T12:27:38,005 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #63 is disabled
2026-04-27T12:27:38,005 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #61
2026-04-27T12:27:38,005 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,010 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T12:27:38,011 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #51
2026-04-27T12:27:38,011 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,134 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #51. Is it enabled?
2026-04-27T12:27:38,139 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #51 is disabled
2026-04-27T12:27:38,140 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #59
2026-04-27T12:27:38,140 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,145 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T12:27:38,146 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #0
2026-04-27T12:27:38,147 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,147 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #0. Is it enabled?
2026-04-27T12:27:38,148 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #0 is disabled
2026-04-27T12:27:38,148 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #53
2026-04-27T12:27:38,148 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,204 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #53. Is it enabled?
2026-04-27T12:27:38,211 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #53 is disabled
2026-04-27T12:27:38,212 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #14
2026-04-27T12:27:38,212 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,213 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #14. Is it enabled?
2026-04-27T12:27:38,214 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #14 is disabled
2026-04-27T12:27:38,214 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #66
2026-04-27T12:27:38,214 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,312 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #66. Is it enabled?
2026-04-27T12:27:38,318 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #66 is disabled
2026-04-27T12:27:38,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #68
2026-04-27T12:27:38,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,327 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #68. Is it enabled?
2026-04-27T12:27:38,328 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #68 is disabled
2026-04-27T12:27:38,329 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #8
2026-04-27T12:27:38,329 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,329 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T12:27:38,329 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #10
2026-04-27T12:27:38,329 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,330 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #10. Is it enabled?
2026-04-27T12:27:38,330 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #10 is disabled
2026-04-27T12:27:38,331 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #1
2026-04-27T12:27:38,331 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,331 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #1. Is it enabled?
2026-04-27T12:27:38,331 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #1 is disabled
2026-04-27T12:27:38,332 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #6
2026-04-27T12:27:38,332 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,332 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #6. Is it enabled?
2026-04-27T12:27:38,332 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #6 is disabled
2026-04-27T12:27:38,332 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #19
2026-04-27T12:27:38,332 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,335 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T12:27:38,336 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #37
2026-04-27T12:27:38,336 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,372 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #37. Is it enabled?
2026-04-27T12:27:38,377 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #37 is disabled
2026-04-27T12:27:38,379 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #39
2026-04-27T12:27:38,379 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,424 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #39. Is it enabled?
2026-04-27T12:27:38,429 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #39 is disabled
2026-04-27T12:27:38,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #64
2026-04-27T12:27:38,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,438 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #64. Is it enabled?
2026-04-27T12:27:38,439 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #64 is disabled
2026-04-27T12:27:38,440 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #16
2026-04-27T12:27:38,440 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,484 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16. Is it enabled?
2026-04-27T12:27:38,492 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16 is enabled
2026-04-27T12:27:38,492 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: Checking 2 state invariants
2026-04-27T12:27:38,493 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 0
2026-04-27T12:27:38,512 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 0 holds.
2026-04-27T12:27:38,513 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 1
2026-04-27T12:27:38,541 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 1 holds.
2026-04-27T12:27:38,542 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: randomly picked transition #16
2026-04-27T12:27:38,543 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 1: picking a transition out of 1 transition(s)
2026-04-27T12:27:38,543 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #15
2026-04-27T12:27:38,543 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,712 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #15. Is it enabled?
2026-04-27T12:27:38,728 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #15 is disabled
2026-04-27T12:27:38,731 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #68
2026-04-27T12:27:38,731 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,779 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #68. Is it enabled?
2026-04-27T12:27:38,785 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #68 is disabled
2026-04-27T12:27:38,786 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #49
2026-04-27T12:27:38,787 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,917 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #49. Is it enabled?
2026-04-27T12:27:38,930 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #49 is disabled
2026-04-27T12:27:38,933 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #22
2026-04-27T12:27:38,933 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:38,966 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T12:27:38,969 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #52
2026-04-27T12:27:38,969 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,156 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #52. Is it enabled?
2026-04-27T12:27:39,167 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #52 is disabled
2026-04-27T12:27:39,170 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #7
2026-04-27T12:27:39,170 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,174 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T12:27:39,174 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #59
2026-04-27T12:27:39,174 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,179 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T12:27:39,181 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #27
2026-04-27T12:27:39,181 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,202 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #27. Is it enabled?
2026-04-27T12:27:39,205 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #27 is disabled
2026-04-27T12:27:39,206 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #12
2026-04-27T12:27:39,206 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,320 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #12. Is it enabled?
2026-04-27T12:27:39,336 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #12 is disabled
2026-04-27T12:27:39,339 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #47
2026-04-27T12:27:39,339 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,501 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #47. Is it enabled?
2026-04-27T12:27:39,512 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #47 is disabled
2026-04-27T12:27:39,514 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #23
2026-04-27T12:27:39,514 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,524 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T12:27:39,526 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #6
2026-04-27T12:27:39,526 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,559 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #6. Is it enabled?
2026-04-27T12:27:39,563 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #6 is disabled
2026-04-27T12:27:39,564 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #67
2026-04-27T12:27:39,564 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,632 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #67. Is it enabled?
2026-04-27T12:27:39,641 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #67 is disabled
2026-04-27T12:27:39,643 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #13
2026-04-27T12:27:39,643 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,779 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #13. Is it enabled?
2026-04-27T12:27:39,796 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #13 is disabled
2026-04-27T12:27:39,800 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #33
2026-04-27T12:27:39,800 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:39,930 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #33. Is it enabled?
2026-04-27T12:27:39,985 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #33 is disabled
2026-04-27T12:27:39,988 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #0
2026-04-27T12:27:39,989 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:40,041 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0. Is it enabled?
2026-04-27T12:27:40,076 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0 is enabled
2026-04-27T12:27:40,077 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: Checking 2 state invariants
2026-04-27T12:27:40,077 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 0
2026-04-27T12:27:40,124 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 0 holds.
2026-04-27T12:27:40,125 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 1
2026-04-27T12:27:40,187 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 1 holds.
2026-04-27T12:27:40,189 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: randomly picked transition #0
2026-04-27T12:27:40,189 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 2: picking a transition out of 1 transition(s)
2026-04-27T12:27:40,190 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #64
2026-04-27T12:27:40,190 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:40,325 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #64. Is it enabled?
2026-04-27T12:27:40,336 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #64 is disabled
2026-04-27T12:27:40,338 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #29
2026-04-27T12:27:40,338 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:40,458 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #29. Is it enabled?
2026-04-27T12:27:40,541 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #29 is disabled
2026-04-27T12:27:40,545 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #33
2026-04-27T12:27:40,545 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:40,669 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #33. Is it enabled?
2026-04-27T12:27:40,775 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #33 is disabled
2026-04-27T12:27:40,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #69
2026-04-27T12:27:40,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:40,857 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #69. Is it enabled?
2026-04-27T12:27:40,869 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #69 is disabled
2026-04-27T12:27:40,872 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #8
2026-04-27T12:27:40,872 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:40,876 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T12:27:40,877 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #10
2026-04-27T12:27:40,877 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:40,908 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #10. Is it enabled?
2026-04-27T12:27:40,912 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #10 is disabled
2026-04-27T12:27:40,914 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #21
2026-04-27T12:27:40,914 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,029 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #21. Is it enabled?
2026-04-27T12:27:41,071 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #21 is disabled
2026-04-27T12:27:41,074 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #22
2026-04-27T12:27:41,074 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,105 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T12:27:41,109 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #54
2026-04-27T12:27:41,109 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,158 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #54. Is it enabled?
2026-04-27T12:27:41,167 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #54 is disabled
2026-04-27T12:27:41,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #43
2026-04-27T12:27:41,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,220 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #43. Is it enabled?
2026-04-27T12:27:41,226 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #43 is disabled
2026-04-27T12:27:41,228 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #20
2026-04-27T12:27:41,228 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,239 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T12:27:41,240 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #26
2026-04-27T12:27:41,241 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,294 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #26. Is it enabled?
2026-04-27T12:27:41,302 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #26 is disabled
2026-04-27T12:27:41,304 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #13
2026-04-27T12:27:41,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,445 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #13. Is it enabled?
2026-04-27T12:27:41,466 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #13 is disabled
2026-04-27T12:27:41,470 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #45
2026-04-27T12:27:41,470 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,545 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #45. Is it enabled?
2026-04-27T12:27:41,555 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #45 is disabled
2026-04-27T12:27:41,557 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #34
2026-04-27T12:27:41,557 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,687 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #34. Is it enabled?
2026-04-27T12:27:41,807 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #34 is disabled
2026-04-27T12:27:41,812 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #6
2026-04-27T12:27:41,812 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,841 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #6. Is it enabled?
2026-04-27T12:27:41,846 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #6 is disabled
2026-04-27T12:27:41,848 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #47
2026-04-27T12:27:41,848 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,936 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #47. Is it enabled?
2026-04-27T12:27:41,950 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #47 is disabled
2026-04-27T12:27:41,953 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #59
2026-04-27T12:27:41,953 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,958 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T12:27:41,959 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #42
2026-04-27T12:27:41,959 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:41,978 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T12:27:41,980 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #15
2026-04-27T12:27:41,980 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:42,150 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #15. Is it enabled?
2026-04-27T12:27:42,173 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #15 is disabled
2026-04-27T12:27:42,177 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #9
2026-04-27T12:27:42,177 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:42,257 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #9. Is it enabled?
2026-04-27T12:27:42,265 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #9 is disabled
2026-04-27T12:27:42,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #41
2026-04-27T12:27:42,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:42,342 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #41. Is it enabled?
2026-04-27T12:27:42,348 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #41 is disabled
2026-04-27T12:27:42,350 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #4
2026-04-27T12:27:42,350 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:42,353 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T12:27:42,354 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #16
2026-04-27T12:27:42,354 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:42,414 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #16. Is it enabled?
2026-04-27T12:27:42,512 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #16 is enabled
2026-04-27T12:27:42,513 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 2 state invariants
2026-04-27T12:27:42,513 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-04-27T12:27:42,597 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-04-27T12:27:42,599 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 1
2026-04-27T12:27:42,723 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 1 holds.
2026-04-27T12:27:42,726 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: randomly picked transition #16
2026-04-27T12:27:42,726 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 3: picking a transition out of 1 transition(s)
2026-04-27T12:27:42,727 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #27
2026-04-27T12:27:42,727 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:42,797 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #27. Is it enabled?
2026-04-27T12:27:42,804 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #27 is disabled
2026-04-27T12:27:42,806 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #3
2026-04-27T12:27:42,806 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:42,812 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T12:27:42,813 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #36
2026-04-27T12:27:42,813 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:42,877 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T12:27:42,882 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #49
2026-04-27T12:27:42,883 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:43,042 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #49. Is it enabled?
2026-04-27T12:27:43,057 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #49 is disabled
2026-04-27T12:27:43,060 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #63
2026-04-27T12:27:43,060 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:43,104 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #63. Is it enabled?
2026-04-27T12:27:43,111 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #63 is disabled
2026-04-27T12:27:43,113 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #51
2026-04-27T12:27:43,113 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:43,252 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #51. Is it enabled?
2026-04-27T12:27:43,268 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #51 is disabled
2026-04-27T12:27:43,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #10
2026-04-27T12:27:43,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:43,311 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #10. Is it enabled?
2026-04-27T12:27:43,316 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #10 is disabled
2026-04-27T12:27:43,318 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #24
2026-04-27T12:27:43,318 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:43,415 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #24. Is it enabled?
2026-04-27T12:27:43,428 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #24 is disabled
2026-04-27T12:27:43,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #7
2026-04-27T12:27:43,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:43,436 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T12:27:43,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #32
2026-04-27T12:27:43,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:43,567 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #32. Is it enabled?
2026-04-27T12:27:43,809 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #32 is disabled
2026-04-27T12:27:43,816 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #28
2026-04-27T12:27:43,816 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:43,968 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #28. Is it enabled?
2026-04-27T12:27:44,396 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #28 is disabled
2026-04-27T12:27:44,402 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #59
2026-04-27T12:27:44,402 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:44,407 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T12:27:44,408 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #21
2026-04-27T12:27:44,408 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:44,549 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #21. Is it enabled?
2026-04-27T12:27:44,608 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #21 is disabled
2026-04-27T12:27:44,612 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #17
2026-04-27T12:27:44,612 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:44,671 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #17. Is it enabled?
2026-04-27T12:27:44,799 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #17 is enabled
2026-04-27T12:27:44,799 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 2 state invariants
2026-04-27T12:27:44,799 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-04-27T12:27:45,167 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-04-27T12:27:45,170 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 1
2026-04-27T12:27:45,383 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 1 holds.
2026-04-27T12:27:45,386 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: randomly picked transition #17
2026-04-27T12:27:45,386 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 4: picking a transition out of 1 transition(s)
2026-04-27T12:27:45,387 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #48
2026-04-27T12:27:45,387 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:45,679 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #48. Is it enabled?
2026-04-27T12:27:45,709 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #48 is disabled
2026-04-27T12:27:45,717 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #60
2026-04-27T12:27:45,717 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:45,770 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #60. Is it enabled?
2026-04-27T12:27:45,776 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #60 is disabled
2026-04-27T12:27:45,778 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #41
2026-04-27T12:27:45,778 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:45,999 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #41. Is it enabled?
2026-04-27T12:27:46,019 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #41 is disabled
2026-04-27T12:27:46,023 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #54
2026-04-27T12:27:46,023 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:46,077 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #54. Is it enabled?
2026-04-27T12:27:46,087 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #54 is disabled
2026-04-27T12:27:46,090 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #38
2026-04-27T12:27:46,090 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:46,223 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T12:27:46,235 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #44
2026-04-27T12:27:46,235 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:46,398 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #44. Is it enabled?
2026-04-27T12:27:46,414 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #44 is disabled
2026-04-27T12:27:46,418 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #21
2026-04-27T12:27:46,418 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:46,628 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #21. Is it enabled?
2026-04-27T12:27:46,692 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #21 is disabled
2026-04-27T12:27:46,698 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #7
2026-04-27T12:27:46,698 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:46,712 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T12:27:46,713 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #33
2026-04-27T12:27:46,713 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:46,869 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #33. Is it enabled?
2026-04-27T12:27:47,265 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #33 is disabled
2026-04-27T12:27:47,272 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #13
2026-04-27T12:27:47,272 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:47,413 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #13. Is it enabled?
2026-04-27T12:27:47,434 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #13 is disabled
2026-04-27T12:27:47,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #30
2026-04-27T12:27:47,438 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:47,560 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #30. Is it enabled?
2026-04-27T12:27:47,983 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #30 is enabled
2026-04-27T12:27:47,988 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: randomly picked transition #30
2026-04-27T12:27:47,989 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 5: picking a transition out of 1 transition(s)
2026-04-27T12:27:47,989 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #1
2026-04-27T12:27:47,989 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:48,073 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #1. Is it enabled?
2026-04-27T12:27:48,087 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #1 is disabled
2026-04-27T12:27:48,091 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #34
2026-04-27T12:27:48,091 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:48,281 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #34. Is it enabled?
2026-04-27T12:27:48,667 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #34 is disabled
2026-04-27T12:27:48,674 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #42
2026-04-27T12:27:48,674 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:48,825 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T12:27:48,839 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #8
2026-04-27T12:27:48,839 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:48,853 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T12:27:48,855 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #22
2026-04-27T12:27:48,855 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:49,020 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T12:27:49,045 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #68
2026-04-27T12:27:49,045 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:49,138 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #68. Is it enabled?
2026-04-27T12:27:49,149 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #68 is disabled
2026-04-27T12:27:49,153 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #27
2026-04-27T12:27:49,153 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:49,254 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #27. Is it enabled?
2026-04-27T12:27:49,268 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #27 is disabled
2026-04-27T12:27:49,272 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #25
2026-04-27T12:27:49,272 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:49,304 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T12:27:49,310 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #59
2026-04-27T12:27:49,310 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:49,315 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T12:27:49,316 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #35
2026-04-27T12:27:49,316 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:49,494 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #35. Is it enabled?
2026-04-27T12:27:50,446 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #35 is disabled
2026-04-27T12:27:50,455 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #53
2026-04-27T12:27:50,455 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:50,567 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #53. Is it enabled?
2026-04-27T12:27:50,584 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #53 is disabled
2026-04-27T12:27:50,588 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #58
2026-04-27T12:27:50,588 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:50,647 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #58. Is it enabled?
2026-04-27T12:27:50,659 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #58 is disabled
2026-04-27T12:27:50,662 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #66
2026-04-27T12:27:50,662 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:50,745 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #66. Is it enabled?
2026-04-27T12:27:50,762 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #66 is disabled
2026-04-27T12:27:50,766 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #26
2026-04-27T12:27:50,766 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:50,935 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #26. Is it enabled?
2026-04-27T12:27:50,960 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #26 is disabled
2026-04-27T12:27:50,965 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #16
2026-04-27T12:27:50,966 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:51,022 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #16. Is it enabled?
2026-04-27T12:27:51,039 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #16 is disabled
2026-04-27T12:27:51,043 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #50
2026-04-27T12:27:51,043 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:51,255 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #50. Is it enabled?
2026-04-27T12:27:51,367 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #50 is disabled
2026-04-27T12:27:51,373 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #19
2026-04-27T12:27:51,373 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:51,441 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T12:27:51,446 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #32
2026-04-27T12:27:51,447 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:51,599 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #32. Is it enabled?
2026-04-27T12:27:52,072 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #32 is disabled
2026-04-27T12:27:52,082 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #38
2026-04-27T12:27:52,082 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:52,158 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T12:27:52,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #18
2026-04-27T12:27:52,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:52,199 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T12:27:52,204 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #30
2026-04-27T12:27:52,204 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:52,327 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #30. Is it enabled?
2026-04-27T12:27:54,087 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #30 is enabled
2026-04-27T12:27:54,098 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: randomly picked transition #30
2026-04-27T12:27:54,098 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 6: picking a transition out of 1 transition(s)
2026-04-27T12:27:54,099 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #8
2026-04-27T12:27:54,099 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:54,117 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T12:27:54,121 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #3
2026-04-27T12:27:54,121 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:54,137 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T12:27:54,140 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #58
2026-04-27T12:27:54,140 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:54,247 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #58. Is it enabled?
2026-04-27T12:27:54,257 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #58 is disabled
2026-04-27T12:27:54,261 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #28
2026-04-27T12:27:54,261 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:54,423 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #28. Is it enabled?
2026-04-27T12:27:55,689 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #28 is disabled
2026-04-27T12:27:55,702 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #32
2026-04-27T12:27:55,702 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:55,860 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #32. Is it enabled?
2026-04-27T12:27:56,829 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #32 is disabled
2026-04-27T12:27:56,842 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #21
2026-04-27T12:27:56,842 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:57,385 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #21. Is it enabled?
2026-04-27T12:27:57,676 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #21 is disabled
2026-04-27T12:27:57,690 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #29
2026-04-27T12:27:57,690 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:57,816 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #29. Is it enabled?
2026-04-27T12:27:58,432 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #29 is disabled
2026-04-27T12:27:58,444 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #40
2026-04-27T12:27:58,444 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:58,681 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T12:27:58,707 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #18
2026-04-27T12:27:58,707 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:58,746 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T12:27:58,755 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #62
2026-04-27T12:27:58,755 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:58,802 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #62. Is it enabled?
2026-04-27T12:27:58,812 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #62 is disabled
2026-04-27T12:27:58,816 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #46
2026-04-27T12:27:58,816 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:59,094 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #46. Is it enabled?
2026-04-27T12:27:59,639 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #46 is disabled
2026-04-27T12:27:59,652 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #23
2026-04-27T12:27:59,652 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:59,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T12:27:59,700 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #6
2026-04-27T12:27:59,700 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:27:59,778 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #6. Is it enabled?
2026-04-27T12:28:01,701 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #6 is enabled
2026-04-27T12:28:01,702 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: Checking 2 state invariants
2026-04-27T12:28:01,702 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 7: Checking state invariant 0
2026-04-27T12:28:02,935 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: state invariant 0 holds.
2026-04-27T12:28:02,942 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 7: Checking state invariant 1
2026-04-27T12:28:03,705 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: state invariant 1 holds.
2026-04-27T12:28:03,716 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: randomly picked transition #6
2026-04-27T12:28:03,717 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 7: picking a transition out of 1 transition(s)
2026-04-27T12:28:03,718 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #18
2026-04-27T12:28:03,718 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:03,759 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T12:28:03,771 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #69
2026-04-27T12:28:03,771 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:03,862 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #69. Is it enabled?
2026-04-27T12:28:03,879 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #69 is disabled
2026-04-27T12:28:03,886 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #46
2026-04-27T12:28:03,886 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:04,180 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #46. Is it enabled?
2026-04-27T12:28:04,644 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #46 is disabled
2026-04-27T12:28:04,654 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #28
2026-04-27T12:28:04,654 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:04,781 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #28. Is it enabled?
2026-04-27T12:28:08,897 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #28 is disabled
2026-04-27T12:28:08,912 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #56
2026-04-27T12:28:08,912 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:08,974 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #56. Is it enabled?
2026-04-27T12:28:08,984 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #56 is disabled
2026-04-27T12:28:08,988 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #61
2026-04-27T12:28:08,989 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:08,995 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T12:28:08,996 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #62
2026-04-27T12:28:08,996 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:09,043 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #62. Is it enabled?
2026-04-27T12:28:09,050 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #62 is disabled
2026-04-27T12:28:09,054 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #32
2026-04-27T12:28:09,054 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:09,242 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #32. Is it enabled?
2026-04-27T12:28:10,475 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #32 is disabled
2026-04-27T12:28:10,490 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #34
2026-04-27T12:28:10,490 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:10,631 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #34. Is it enabled?
2026-04-27T12:28:11,838 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #34 is disabled
2026-04-27T12:28:11,853 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #14
2026-04-27T12:28:11,853 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:12,042 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #14. Is it enabled?
2026-04-27T12:28:13,161 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #14 is enabled
2026-04-27T12:28:13,161 [main] INFO  a.f.a.t.b.SeqModelChecker - State 8: Checking 2 state invariants
2026-04-27T12:28:13,161 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 8: Checking state invariant 0
2026-04-27T12:28:16,149 [main] INFO  a.f.a.t.b.SeqModelChecker - State 8: state invariant 0 holds.
2026-04-27T12:28:16,157 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 8: Checking state invariant 1
2026-04-27T12:28:17,928 [main] INFO  a.f.a.t.b.SeqModelChecker - State 8: state invariant 1 holds.
2026-04-27T12:28:17,943 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: randomly picked transition #14
2026-04-27T12:28:17,943 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 8: picking a transition out of 1 transition(s)
2026-04-27T12:28:17,945 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #4
2026-04-27T12:28:17,945 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:17,967 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T12:28:17,970 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #38
2026-04-27T12:28:17,970 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:18,117 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T12:28:18,134 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #67
2026-04-27T12:28:18,134 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:18,278 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #67. Is it enabled?
2026-04-27T12:28:18,292 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #67 is disabled
2026-04-27T12:28:18,299 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #14
2026-04-27T12:28:18,300 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:18,520 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #14. Is it enabled?
2026-04-27T12:28:21,570 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #14 is enabled
2026-04-27T12:28:21,570 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: Checking 2 state invariants
2026-04-27T12:28:21,571 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 9: Checking state invariant 0
2026-04-27T12:28:27,201 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: state invariant 0 holds.
2026-04-27T12:28:27,212 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 9: Checking state invariant 1
2026-04-27T12:28:28,954 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: state invariant 1 holds.
2026-04-27T12:28:28,971 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: randomly picked transition #14
2026-04-27T12:28:28,971 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 9: picking a transition out of 1 transition(s)
2026-04-27T12:28:28,973 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #20
2026-04-27T12:28:28,973 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:29,051 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T12:28:29,062 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #50
2026-04-27T12:28:29,062 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:29,420 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #50. Is it enabled?
2026-04-27T12:28:33,413 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #50 is disabled
2026-04-27T12:28:33,436 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #23
2026-04-27T12:28:33,436 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:33,482 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-04-27T12:28:33,491 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #60
2026-04-27T12:28:33,491 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:33,540 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #60. Is it enabled?
2026-04-27T12:28:33,549 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #60 is disabled
2026-04-27T12:28:33,556 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #67
2026-04-27T12:28:33,556 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:33,624 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #67. Is it enabled?
2026-04-27T12:28:33,640 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #67 is disabled
2026-04-27T12:28:33,647 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #53
2026-04-27T12:28:33,647 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:33,764 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #53. Is it enabled?
2026-04-27T12:28:33,786 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #53 is disabled
2026-04-27T12:28:33,793 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #25
2026-04-27T12:28:33,794 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:33,835 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T12:28:33,846 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #0
2026-04-27T12:28:33,846 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:33,971 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #0. Is it enabled?
2026-04-27T12:28:36,716 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #0 is enabled
2026-04-27T12:28:36,716 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: Checking 2 state invariants
2026-04-27T12:28:36,717 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 10: Checking state invariant 0
2026-04-27T12:28:44,292 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: state invariant 0 holds.
2026-04-27T12:28:44,303 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 10: Checking state invariant 1
2026-04-27T12:28:47,181 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: state invariant 1 holds.
2026-04-27T12:28:47,201 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: randomly picked transition #0
2026-04-27T12:28:47,201 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 10: picking a transition out of 1 transition(s)
2026-04-27T12:28:47,203 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #11, transition #37
2026-04-27T12:28:47,203 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:47,648 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 11: Transition #37. Is it enabled?
2026-04-27T12:28:52,826 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 11: Transition #37 is disabled
2026-04-27T12:28:52,848 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #11, transition #50
2026-04-27T12:28:52,848 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:53,252 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 11: Transition #50. Is it enabled?
2026-04-27T12:28:54,058 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 11: Transition #50 is disabled
2026-04-27T12:28:54,078 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #11, transition #30
2026-04-27T12:28:54,078 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:54,221 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 11: Transition #30. Is it enabled?
2026-04-27T12:28:58,411 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 11: Transition #30 is enabled
2026-04-27T12:28:58,445 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 11: randomly picked transition #30
2026-04-27T12:28:58,446 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 11: picking a transition out of 1 transition(s)
2026-04-27T12:28:58,447 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #12, transition #60
2026-04-27T12:28:58,447 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:58,503 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 12: Transition #60. Is it enabled?
2026-04-27T12:28:58,512 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 12: Transition #60 is disabled
2026-04-27T12:28:58,520 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #12, transition #43
2026-04-27T12:28:58,520 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:28:59,079 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 12: Transition #43. Is it enabled?
2026-04-27T12:29:06,026 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 12: Transition #43 is disabled
2026-04-27T12:29:06,059 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #12, transition #18
2026-04-27T12:29:06,060 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:29:06,287 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T12:29:06,319 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #12, transition #56
2026-04-27T12:29:06,319 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:29:06,388 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 12: Transition #56. Is it enabled?
2026-04-27T12:29:06,405 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 12: Transition #56 is disabled
2026-04-27T12:29:06,414 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #12, transition #30
2026-04-27T12:29:06,414 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:29:06,550 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 12: Transition #30. Is it enabled?
2026-04-27T12:29:09,302 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 12: Transition #30 is enabled
2026-04-27T12:29:09,340 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 12: randomly picked transition #30
2026-04-27T12:29:09,340 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 12: picking a transition out of 1 transition(s)
2026-04-27T12:29:09,342 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #69
2026-04-27T12:29:09,342 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:29:09,498 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #69. Is it enabled?
2026-04-27T12:29:09,528 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 13: Transition #69 is disabled
2026-04-27T12:29:09,537 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #1
2026-04-27T12:29:09,538 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:29:09,676 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #1. Is it enabled?
2026-04-27T12:29:09,707 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 13: Transition #1 is disabled
2026-04-27T12:29:09,717 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #12
2026-04-27T12:29:09,717 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:29:09,933 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #12. Is it enabled?
2026-04-27T12:29:22,257 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 13: Transition #12 is disabled
2026-04-27T12:29:22,288 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #41
2026-04-27T12:29:22,288 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:29:22,938 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #41. Is it enabled?
2026-04-27T12:29:42,383 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 13: Transition #41 is disabled
2026-04-27T12:29:42,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #65
2026-04-27T12:29:42,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:29:42,456 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #65. Is it enabled?
2026-04-27T12:29:42,462 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 13: Transition #65 is disabled
2026-04-27T12:29:42,468 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #33
2026-04-27T12:29:42,468 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:29:42,604 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #33. Is it enabled?
2026-04-27T12:29:49,342 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #33 is enabled
2026-04-27T12:29:49,343 [main] INFO  a.f.a.t.b.SeqModelChecker - State 13: Checking 2 state invariants
2026-04-27T12:29:49,343 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 13: Checking state invariant 0
2026-04-27T12:29:58,505 [main] INFO  a.f.a.t.b.SeqModelChecker - State 13: state invariant 0 holds.
2026-04-27T12:29:58,527 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 13: Checking state invariant 1
2026-04-27T12:30:03,318 [main] INFO  a.f.a.t.b.SeqModelChecker - State 13: state invariant 1 holds.
2026-04-27T12:30:03,351 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 13: randomly picked transition #33
2026-04-27T12:30:03,352 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 13: picking a transition out of 1 transition(s)
2026-04-27T12:30:03,353 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #27
2026-04-27T12:30:03,353 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:04,066 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #27. Is it enabled?
2026-04-27T12:30:04,147 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #27 is disabled
2026-04-27T12:30:04,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #36
2026-04-27T12:30:04,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:04,782 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T12:30:04,852 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #4
2026-04-27T12:30:04,852 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:04,882 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T12:30:04,889 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #24
2026-04-27T12:30:04,889 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:05,332 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #24. Is it enabled?
2026-04-27T12:30:05,388 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #24 is disabled
2026-04-27T12:30:05,411 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #67
2026-04-27T12:30:05,411 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:05,513 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #67. Is it enabled?
2026-04-27T12:30:05,528 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #67 is disabled
2026-04-27T12:30:05,538 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #39
2026-04-27T12:30:05,538 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:06,095 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #39. Is it enabled?
2026-04-27T12:30:08,469 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #39 is disabled
2026-04-27T12:30:08,497 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #21
2026-04-27T12:30:08,497 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:09,430 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #21. Is it enabled?
2026-04-27T12:30:24,709 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #21 is disabled
2026-04-27T12:30:24,760 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #19
2026-04-27T12:30:24,761 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:24,887 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T12:30:24,921 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #64
2026-04-27T12:30:24,922 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:25,050 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #64. Is it enabled?
2026-04-27T12:30:25,080 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #64 is disabled
2026-04-27T12:30:25,091 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #59
2026-04-27T12:30:25,092 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:25,098 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T12:30:25,099 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #38
2026-04-27T12:30:25,099 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:25,344 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T12:30:25,375 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #48
2026-04-27T12:30:25,375 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:26,066 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #48. Is it enabled?
2026-04-27T12:30:34,355 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #48 is disabled
2026-04-27T12:30:34,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #11
2026-04-27T12:30:34,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:34,507 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #11. Is it enabled?
2026-04-27T12:30:54,764 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #11 is disabled
2026-04-27T12:30:54,801 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #17
2026-04-27T12:30:54,801 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:30:55,193 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #17. Is it enabled?
2026-04-27T12:31:01,691 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #17 is disabled
2026-04-27T12:31:01,727 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #26
2026-04-27T12:31:01,727 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:31:02,174 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #26. Is it enabled?
2026-04-27T12:31:02,229 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #26 is disabled
2026-04-27T12:31:02,246 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #1
2026-04-27T12:31:02,246 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:31:02,399 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #1. Is it enabled?
2026-04-27T12:31:02,432 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #1 is disabled
2026-04-27T12:31:02,445 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #46
2026-04-27T12:31:02,445 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:31:02,941 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #46. Is it enabled?
2026-04-27T12:31:13,718 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #46 is disabled
2026-04-27T12:31:13,754 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #31
2026-04-27T12:31:13,754 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:31:13,900 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #31. Is it enabled?
2026-04-27T12:31:19,841 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #31 is disabled
2026-04-27T12:31:19,870 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #65
2026-04-27T12:31:19,871 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:31:19,910 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #65. Is it enabled?
2026-04-27T12:31:19,916 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #65 is disabled
2026-04-27T12:31:19,926 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #30
2026-04-27T12:31:19,926 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:31:20,081 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #30. Is it enabled?
2026-04-27T12:31:49,390 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #30 is disabled
2026-04-27T12:31:49,433 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #44
2026-04-27T12:31:49,433 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:31:49,951 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #44. Is it enabled?
2026-04-27T12:32:05,709 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #44 is disabled
2026-04-27T12:32:05,748 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #15
2026-04-27T12:32:05,748 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:06,020 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #15. Is it enabled?
2026-04-27T12:32:25,847 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #15 is disabled
2026-04-27T12:32:25,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #69
2026-04-27T12:32:25,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,004 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #69. Is it enabled?
2026-04-27T12:32:26,028 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #69 is disabled
2026-04-27T12:32:26,041 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #66
2026-04-27T12:32:26,041 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,128 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #66. Is it enabled?
2026-04-27T12:32:26,152 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #66 is disabled
2026-04-27T12:32:26,164 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #55
2026-04-27T12:32:26,164 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,171 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-04-27T12:32:26,172 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #3
2026-04-27T12:32:26,173 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,201 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T12:32:26,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #18
2026-04-27T12:32:26,207 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,284 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T12:32:26,302 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #40
2026-04-27T12:32:26,302 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,497 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T12:32:26,533 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #61
2026-04-27T12:32:26,533 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,539 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T12:32:26,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #7
2026-04-27T12:32:26,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,569 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T12:32:26,574 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #54
2026-04-27T12:32:26,574 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,640 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #54. Is it enabled?
2026-04-27T12:32:26,656 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #54 is disabled
2026-04-27T12:32:26,668 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #58
2026-04-27T12:32:26,668 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,816 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #58. Is it enabled?
2026-04-27T12:32:26,835 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #58 is disabled
2026-04-27T12:32:26,847 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #16
2026-04-27T12:32:26,847 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:26,908 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #16. Is it enabled?
2026-04-27T12:32:26,957 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #16 is disabled
2026-04-27T12:32:26,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #51
2026-04-27T12:32:26,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:27,530 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #51. Is it enabled?
2026-04-27T12:32:31,384 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #51 is disabled
2026-04-27T12:32:31,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #6
2026-04-27T12:32:31,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:31,545 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #6. Is it enabled?
2026-04-27T12:32:53,700 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #6 is disabled
2026-04-27T12:32:53,743 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #37
2026-04-27T12:32:53,743 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:54,220 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #37. Is it enabled?
2026-04-27T12:32:58,982 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #37 is disabled
2026-04-27T12:32:59,017 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #22
2026-04-27T12:32:59,017 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:32:59,704 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-04-27T12:32:59,887 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #9
2026-04-27T12:32:59,887 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:33:00,028 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #9. Is it enabled?
2026-04-27T12:33:00,059 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #9 is disabled
2026-04-27T12:33:00,074 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #20
2026-04-27T12:33:00,074 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:33:00,155 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-04-27T12:33:00,174 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #25
2026-04-27T12:33:00,174 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:33:00,234 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T12:33:00,251 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #68
2026-04-27T12:33:00,251 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:33:00,325 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #68. Is it enabled?
2026-04-27T12:33:00,341 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: Transition #68 is disabled
2026-04-27T12:33:00,356 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #14, transition #47
2026-04-27T12:33:00,356 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:33:00,897 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #47. Is it enabled?
2026-04-27T12:33:12,522 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 14: Transition #47 is enabled
2026-04-27T12:33:12,523 [main] INFO  a.f.a.t.b.SeqModelChecker - State 14: Checking 2 state invariants
2026-04-27T12:33:12,523 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 14: Checking state invariant 0
2026-04-27T12:33:26,494 [main] INFO  a.f.a.t.b.SeqModelChecker - State 14: state invariant 0 holds.
2026-04-27T12:33:26,519 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 14: Checking state invariant 1
2026-04-27T12:33:33,042 [main] INFO  a.f.a.t.b.SeqModelChecker - State 14: state invariant 1 holds.
2026-04-27T12:33:33,085 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 14: randomly picked transition #47
2026-04-27T12:33:33,085 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 14: picking a transition out of 1 transition(s)
2026-04-27T12:33:33,087 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #18
2026-04-27T12:33:33,088 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:33:33,415 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T12:33:33,457 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #65
2026-04-27T12:33:33,458 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:33:33,491 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #65. Is it enabled?
2026-04-27T12:33:33,499 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #65 is disabled
2026-04-27T12:33:33,512 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #0
2026-04-27T12:33:33,512 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:33:33,905 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #0. Is it enabled?
2026-04-27T12:34:04,837 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #0 is disabled
2026-04-27T12:34:04,885 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #32
2026-04-27T12:34:04,886 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:34:05,031 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #32. Is it enabled?
2026-04-27T12:34:12,828 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #32 is disabled
2026-04-27T12:34:12,862 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #48
2026-04-27T12:34:12,862 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:34:13,683 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #48. Is it enabled?
2026-04-27T12:34:57,575 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #48 is disabled
2026-04-27T12:34:57,633 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #38
2026-04-27T12:34:57,633 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:34:57,869 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T12:34:57,917 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #56
2026-04-27T12:34:57,917 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:34:57,989 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #56. Is it enabled?
2026-04-27T12:34:58,005 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #56 is disabled
2026-04-27T12:34:58,020 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #63
2026-04-27T12:34:58,020 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:34:58,093 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #63. Is it enabled?
2026-04-27T12:34:58,112 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #63 is disabled
2026-04-27T12:34:58,127 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #31
2026-04-27T12:34:58,127 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:34:58,269 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #31. Is it enabled?
2026-04-27T12:35:12,355 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #31 is disabled
2026-04-27T12:35:12,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #59
2026-04-27T12:35:12,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:35:12,402 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T12:35:12,404 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #36
2026-04-27T12:35:12,404 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:35:12,700 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-04-27T12:35:12,761 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #46
2026-04-27T12:35:12,761 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:35:13,351 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #46. Is it enabled?
2026-04-27T12:35:44,629 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #46 is disabled
2026-04-27T12:35:44,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #16
2026-04-27T12:35:44,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:35:44,751 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #16. Is it enabled?
2026-04-27T12:35:44,985 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #16 is disabled
2026-04-27T12:35:45,005 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #11
2026-04-27T12:35:45,005 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:35:45,143 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #11. Is it enabled?
2026-04-27T12:36:25,267 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #11 is disabled
2026-04-27T12:36:25,312 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #9
2026-04-27T12:36:25,312 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:36:25,479 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #9. Is it enabled?
2026-04-27T12:36:25,512 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #9 is disabled
2026-04-27T12:36:25,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #37
2026-04-27T12:36:25,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:36:26,163 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #37. Is it enabled?
2026-04-27T12:36:55,334 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #37 is disabled
2026-04-27T12:36:55,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #1
2026-04-27T12:36:55,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:36:55,568 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #1. Is it enabled?
2026-04-27T12:37:15,375 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #1 is disabled
2026-04-27T12:37:15,417 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #45
2026-04-27T12:37:15,417 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:37:16,011 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #45. Is it enabled?
2026-04-27T12:37:56,262 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #45 is disabled
2026-04-27T12:37:56,328 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #27
2026-04-27T12:37:56,328 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:37:56,716 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #27. Is it enabled?
2026-04-27T12:37:56,783 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #27 is disabled
2026-04-27T12:37:56,806 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #21
2026-04-27T12:37:56,806 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:37:57,973 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #21. Is it enabled?
2026-04-27T12:38:16,145 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #21 is disabled
2026-04-27T12:38:16,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #55
2026-04-27T12:38:16,230 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:38:16,239 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-04-27T12:38:16,241 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #3
2026-04-27T12:38:16,241 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:38:16,276 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T12:38:16,284 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #52
2026-04-27T12:38:16,284 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:38:16,978 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #52. Is it enabled?
2026-04-27T12:38:59,514 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #52 is disabled
2026-04-27T12:38:59,583 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #47
2026-04-27T12:38:59,583 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:39:00,198 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #47. Is it enabled?
2026-04-27T12:39:44,240 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #47 is disabled
2026-04-27T12:39:44,330 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #68
2026-04-27T12:39:44,330 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:39:44,409 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #68. Is it enabled?
2026-04-27T12:39:44,429 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #68 is disabled
2026-04-27T12:39:44,444 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #57
2026-04-27T12:39:44,445 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:39:44,451 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-04-27T12:39:44,452 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #51
2026-04-27T12:39:44,453 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:39:45,131 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #51. Is it enabled?
2026-04-27T12:40:38,099 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #51 is disabled
2026-04-27T12:40:38,158 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #67
2026-04-27T12:40:38,158 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:40:38,234 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #67. Is it enabled?
2026-04-27T12:40:38,253 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #67 is disabled
2026-04-27T12:40:38,269 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #39
2026-04-27T12:40:38,269 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:40:38,842 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #39. Is it enabled?
2026-04-27T12:41:18,993 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: Transition #39 is disabled
2026-04-27T12:41:19,057 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #15, transition #33
2026-04-27T12:41:19,058 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:41:19,202 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #33. Is it enabled?
2026-04-27T12:41:34,499 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 15: Transition #33 is enabled
2026-04-27T12:41:34,499 [main] INFO  a.f.a.t.b.SeqModelChecker - State 15: Checking 2 state invariants
2026-04-27T12:41:34,499 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 15: Checking state invariant 0
2026-04-27T12:42:01,169 [main] INFO  a.f.a.t.b.SeqModelChecker - State 15: state invariant 0 holds.
2026-04-27T12:42:01,212 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 15: Checking state invariant 1
2026-04-27T12:42:07,601 [main] INFO  a.f.a.t.b.SeqModelChecker - State 15: state invariant 1 holds.
2026-04-27T12:42:07,657 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 15: randomly picked transition #33
2026-04-27T12:42:07,658 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 15: picking a transition out of 1 transition(s)
2026-04-27T12:42:07,660 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #25
2026-04-27T12:42:07,660 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:42:07,734 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-04-27T12:42:07,756 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #6
2026-04-27T12:42:07,756 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:42:07,920 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #6. Is it enabled?
2026-04-27T12:42:47,736 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #6 is disabled
2026-04-27T12:42:47,802 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #1
2026-04-27T12:42:47,802 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:42:47,995 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #1. Is it enabled?
2026-04-27T12:43:04,326 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #1 is disabled
2026-04-27T12:43:04,371 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #38
2026-04-27T12:43:04,371 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:43:04,873 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-04-27T12:43:04,976 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #7
2026-04-27T12:43:04,977 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:43:05,100 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-04-27T12:43:05,114 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #66
2026-04-27T12:43:05,114 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:43:05,208 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #66. Is it enabled?
2026-04-27T12:43:05,249 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #66 is disabled
2026-04-27T12:43:05,269 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #46
2026-04-27T12:43:05,269 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:43:05,946 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #46. Is it enabled?
2026-04-27T12:43:51,778 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #46 is disabled
2026-04-27T12:43:51,854 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #31
2026-04-27T12:43:51,854 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:43:51,992 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #31. Is it enabled?
2026-04-27T12:43:59,211 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #31 is disabled
2026-04-27T12:43:59,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #3
2026-04-27T12:43:59,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:43:59,297 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-04-27T12:43:59,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #68
2026-04-27T12:43:59,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:43:59,383 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #68. Is it enabled?
2026-04-27T12:43:59,398 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #68 is disabled
2026-04-27T12:43:59,415 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #10
2026-04-27T12:43:59,415 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:43:59,625 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #10. Is it enabled?
2026-04-27T12:43:59,665 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #10 is disabled
2026-04-27T12:43:59,685 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #12
2026-04-27T12:43:59,685 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:43:59,946 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #12. Is it enabled?
2026-04-27T12:44:44,757 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #12 is disabled
2026-04-27T12:44:44,820 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #61
2026-04-27T12:44:44,820 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:44:44,832 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-04-27T12:44:44,833 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #16
2026-04-27T12:44:44,833 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:44:44,894 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #16. Is it enabled?
2026-04-27T12:44:44,916 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #16 is disabled
2026-04-27T12:44:44,939 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #63
2026-04-27T12:44:44,940 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:44:45,032 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #63. Is it enabled?
2026-04-27T12:44:45,046 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #63 is disabled
2026-04-27T12:44:45,063 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #39
2026-04-27T12:44:45,063 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:44:45,775 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #39. Is it enabled?
2026-04-27T12:44:57,256 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #39 is disabled
2026-04-27T12:44:57,318 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #65
2026-04-27T12:44:57,318 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:44:57,358 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #65. Is it enabled?
2026-04-27T12:44:57,365 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #65 is disabled
2026-04-27T12:44:57,379 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #58
2026-04-27T12:44:57,379 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:44:57,458 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #58. Is it enabled?
2026-04-27T12:44:57,475 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #58 is disabled
2026-04-27T12:44:57,492 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #21
2026-04-27T12:44:57,492 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:44:58,809 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #21. Is it enabled?
2026-04-27T12:45:17,355 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #21 is disabled
2026-04-27T12:45:17,459 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #67
2026-04-27T12:45:17,459 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:45:17,535 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #67. Is it enabled?
2026-04-27T12:45:17,549 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #67 is disabled
2026-04-27T12:45:17,565 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #50
2026-04-27T12:45:17,565 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:45:18,509 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #50. Is it enabled?
2026-04-27T12:45:27,334 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #50 is disabled
2026-04-27T12:45:27,396 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #64
2026-04-27T12:45:27,396 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:45:27,509 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #64. Is it enabled?
2026-04-27T12:45:27,534 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #64 is disabled
2026-04-27T12:45:27,552 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #48
2026-04-27T12:45:27,552 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:45:28,412 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #48. Is it enabled?
2026-04-27T12:46:03,333 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #48 is disabled
2026-04-27T12:46:03,408 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #26
2026-04-27T12:46:03,408 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:46:03,900 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #26. Is it enabled?
2026-04-27T12:46:06,172 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #26 is disabled
2026-04-27T12:46:06,215 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #40
2026-04-27T12:46:06,215 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:46:06,498 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-04-27T12:46:06,586 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #54
2026-04-27T12:46:06,586 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:46:06,658 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #54. Is it enabled?
2026-04-27T12:46:06,675 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #54 is disabled
2026-04-27T12:46:06,693 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #4
2026-04-27T12:46:06,693 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:46:06,736 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-04-27T12:46:06,745 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #57
2026-04-27T12:46:06,745 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:46:06,751 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-04-27T12:46:06,753 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #28
2026-04-27T12:46:06,753 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:46:06,938 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #28. Is it enabled?
2026-04-27T12:46:39,088 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #28 is disabled
2026-04-27T12:46:39,143 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #42
2026-04-27T12:46:39,143 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:46:39,414 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T12:46:39,491 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #2
2026-04-27T12:46:39,491 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:46:39,678 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #2. Is it enabled?
2026-04-27T12:47:29,353 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #2 is disabled
2026-04-27T12:47:29,412 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #44
2026-04-27T12:47:29,412 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:47:30,123 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #44. Is it enabled?
2026-04-27T12:48:22,963 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #44 is disabled
2026-04-27T12:48:23,046 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #59
2026-04-27T12:48:23,046 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:48:23,055 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T12:48:23,057 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #47
2026-04-27T12:48:23,057 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:48:23,824 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #47. Is it enabled?
2026-04-27T12:49:03,072 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #47 is disabled
2026-04-27T12:49:03,162 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #51
2026-04-27T12:49:03,162 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:49:03,896 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #51. Is it enabled?
2026-04-27T12:50:07,418 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #51 is disabled
2026-04-27T12:50:07,491 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #19
2026-04-27T12:50:07,492 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:50:07,641 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-04-27T12:50:07,669 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #49
2026-04-27T12:50:07,669 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:50:08,530 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #49. Is it enabled?
2026-04-27T12:51:06,889 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #49 is disabled
2026-04-27T12:51:06,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #24
2026-04-27T12:51:06,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:51:07,461 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #24. Is it enabled?
2026-04-27T12:51:19,851 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #24 is disabled
2026-04-27T12:51:19,914 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #45
2026-04-27T12:51:19,914 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:51:20,617 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #45. Is it enabled?
2026-04-27T12:52:00,894 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #45 is disabled
2026-04-27T12:52:00,974 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #15
2026-04-27T12:52:00,974 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:52:01,282 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #15. Is it enabled?
2026-04-27T12:52:51,318 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #15 is disabled
2026-04-27T12:52:51,382 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #30
2026-04-27T12:52:51,382 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:52:51,525 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #30. Is it enabled?
2026-04-27T12:53:11,154 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #30 is disabled
2026-04-27T12:53:11,215 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #43
2026-04-27T12:53:11,215 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:53:11,876 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #43. Is it enabled?
2026-04-27T12:54:00,885 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #43 is disabled
2026-04-27T12:54:00,956 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #18
2026-04-27T12:54:00,956 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:54:01,063 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-04-27T12:54:01,087 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #8
2026-04-27T12:54:01,087 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:54:01,167 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-04-27T12:54:01,177 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #35
2026-04-27T12:54:01,177 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:54:01,322 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #35. Is it enabled?
2026-04-27T12:54:39,997 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #35 is disabled
2026-04-27T12:54:40,055 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #60
2026-04-27T12:54:40,055 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:54:40,124 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #60. Is it enabled?
2026-04-27T12:54:40,135 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #60 is disabled
2026-04-27T12:54:40,152 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #11
2026-04-27T12:54:40,152 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:54:40,306 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #11. Is it enabled?
2026-04-27T12:56:32,571 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #11 is disabled
2026-04-27T12:56:32,628 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #56
2026-04-27T12:56:32,628 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:56:32,710 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #56. Is it enabled?
2026-04-27T12:56:32,729 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: Transition #56 is disabled
2026-04-27T12:56:32,748 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #16, transition #14
2026-04-27T12:56:32,748 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:56:33,015 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #14. Is it enabled?
2026-04-27T12:56:53,038 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 16: Transition #14 is enabled
2026-04-27T12:56:53,038 [main] INFO  a.f.a.t.b.SeqModelChecker - State 16: Checking 2 state invariants
2026-04-27T12:56:53,039 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 16: Checking state invariant 0
2026-04-27T12:57:41,799 [main] INFO  a.f.a.t.b.SeqModelChecker - State 16: state invariant 0 holds.
2026-04-27T12:57:41,851 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 16: Checking state invariant 1
2026-04-27T12:57:48,244 [main] INFO  a.f.a.t.b.SeqModelChecker - State 16: state invariant 1 holds.
2026-04-27T12:57:48,316 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 16: randomly picked transition #14
2026-04-27T12:57:48,316 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 16: picking a transition out of 1 transition(s)
2026-04-27T12:57:48,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #17, transition #1
2026-04-27T12:57:48,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:57:48,514 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 17: Transition #1. Is it enabled?
2026-04-27T12:58:01,347 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 17: Transition #1 is disabled
2026-04-27T12:58:01,397 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #17, transition #10
2026-04-27T12:58:01,397 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:58:01,658 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 17: Transition #10. Is it enabled?
2026-04-27T12:58:01,703 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 17: Transition #10 is disabled
2026-04-27T12:58:01,726 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #17, transition #35
2026-04-27T12:58:01,727 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:58:01,875 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 17: Transition #35. Is it enabled?
2026-04-27T12:58:33,993 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 17: Transition #35 is disabled
2026-04-27T12:58:34,053 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #17, transition #43
2026-04-27T12:58:34,053 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:58:34,810 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 17: Transition #43. Is it enabled?
2026-04-27T12:59:27,922 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 17: Transition #43 is disabled
2026-04-27T12:59:28,010 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #17, transition #41
2026-04-27T12:59:28,010 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T12:59:28,767 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 17: Transition #41. Is it enabled?
2026-04-27T13:00:24,327 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 17: Transition #41 is disabled
2026-04-27T13:00:24,412 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #17, transition #33
2026-04-27T13:00:24,412 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T13:00:24,557 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 17: Transition #33. Is it enabled?
2026-04-27T13:00:57,619 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 17: Transition #33 is disabled
2026-04-27T13:00:57,680 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #17, transition #59
2026-04-27T13:00:57,680 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T13:00:57,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-04-27T13:00:57,694 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #17, transition #42
2026-04-27T13:00:57,694 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T13:00:58,067 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-04-27T13:00:58,167 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #17, transition #52
2026-04-27T13:00:58,167 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T13:00:59,056 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 17: Transition #52. Is it enabled?
2026-04-27T13:01:22,980 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 17: Transition #52 is enabled
2026-04-27T13:01:22,981 [main] INFO  a.f.a.t.b.SeqModelChecker - State 17: Checking 2 state invariants
2026-04-27T13:01:22,982 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 17: Checking state invariant 0
2026-04-27T13:51:06,419 [main] INFO  a.f.a.t.b.SeqModelChecker - State 17: state invariant 0 holds.
2026-04-27T13:51:06,486 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 17: Checking state invariant 1
2026-04-27T13:52:09,787 [main] INFO  a.f.a.t.b.SeqModelChecker - State 17: state invariant 1 holds.
2026-04-27T13:52:09,885 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 17: randomly picked transition #52
2026-04-27T13:52:09,885 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 17: picking a transition out of 1 transition(s)
2026-04-27T13:52:09,888 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #18, transition #13
2026-04-27T13:52:09,888 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-04-27T13:52:10,235 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 18: Transition #13. Is it enabled?
2026-04-27T13:52:26,629 [main] DEBUG a.f.a.i.p.PassChainExecutor - Adapted exception intercepted: 
at.forsyte.apalache.tla.bmcmt.SmtEncodingException: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
	at at.forsyte.apalache.tla.bmcmt.smt.Z3SolverContext.sat(Z3SolverContext.scala:557)
	at at.forsyte.apalache.tla.bmcmt.smt.Z3SolverContext.satOrTimeout(Z3SolverContext.scala:564)
	at at.forsyte.apalache.tla.bmcmt.smt.RecordingSolverContext.satOrTimeout(RecordingSolverContext.scala:205)
	at at.forsyte.apalache.tla.bmcmt.trex.TransitionExecutorImpl.sat(TransitionExecutorImpl.scala:349)
	at at.forsyte.apalache.tla.bmcmt.trex.FilteredTransitionExecutor.sat(FilteredTransitionExecutor.scala:181)
	at at.forsyte.apalache.tla.bmcmt.trex.ConstrainedTransitionExecutor.sat(ConstrainedTransitionExecutor.scala:127)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.\$anonfun\$prepareTransitionsAndCheckInvariants\$5(SeqModelChecker.scala:232)
	at scala.runtime.java8.JFunction1\$mcVI\$sp.apply(JFunction1\$mcVI\$sp.scala:18)
	at scala.collection.immutable.List.foreach(List.scala:323)
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
2026-04-27T13:52:26,665 [main] ERROR a.f.a.t.Tool\$ - <unknown>: error when rewriting to SMT: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
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

