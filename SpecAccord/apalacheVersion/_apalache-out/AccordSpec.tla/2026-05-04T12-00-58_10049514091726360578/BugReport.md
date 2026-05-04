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
--config=AccordSpec.cfg
```

## Expected behavior

<!-- What did you expect to see? -->

## Log files

<details>

```
2026-05-04T12:00:58,939 [main] INFO  a.f.a.t.Tool\$ - # APALACHE version: 0.56.1 | build: 70cdaf4
2026-05-04T12:00:58,958 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > AccordSpec.cfg: Loading TLC configuration
2026-05-04T12:00:59,003 [main] WARN  a.f.a.i.t.TlcConfigParserApalache\$ - TLC config option CHECK_DEADLOCK true will be ignored
2026-05-04T12:00:59,010 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > Using inv predicate(s) Agreement, Ordering from the TLC config
2026-05-04T12:00:59,011 [main] INFO  a.f.a.t.t.o.CheckCmd - Tuning: search.outputTraces=false
2026-05-04T12:00:59,243 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser
2026-05-04T12:01:00,005 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser [OK]
2026-05-04T12:01:00,005 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat
2026-05-04T12:01:00,006 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Running Snowcat .::.
2026-05-04T12:01:08,605 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Your types are purrfect!
2026-05-04T12:01:08,605 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > All expressions are typed
2026-05-04T12:01:08,606 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat [OK]
2026-05-04T12:01:08,606 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass
2026-05-04T12:01:08,827 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: Using SPECIFICATION Spec
2026-05-04T12:01:08,829 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: found INVARIANTS: Agreement, Ordering
2026-05-04T12:01:08,832 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the initialization predicate to Init
2026-05-04T12:01:08,833 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the transition predicate to Next
2026-05-04T12:01:08,833 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the constant initialization predicate to CInit
2026-05-04T12:01:08,833 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Agreement
2026-05-04T12:01:08,833 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Ordering
2026-05-04T12:01:08,840 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass [OK]
2026-05-04T12:01:08,840 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass
2026-05-04T12:01:08,841 [main] INFO  a.f.a.t.p.p.DesugarerPassImpl -   > Desugaring...
2026-05-04T12:01:08,911 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass [OK]
2026-05-04T12:01:08,912 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass
2026-05-04T12:01:08,913 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next, Ordering
2026-05-04T12:01:09,147 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass [OK]
2026-05-04T12:01:09,148 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass
2026-05-04T12:01:09,148 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > Rewriting temporal operators...
2026-05-04T12:01:09,148 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > No temporal property specified, nothing to encode
2026-05-04T12:01:09,148 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass [OK]
2026-05-04T12:01:09,148 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass
2026-05-04T12:01:09,148 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next, Ordering
2026-05-04T12:01:09,222 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass [OK]
2026-05-04T12:01:09,223 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass
2026-05-04T12:01:09,226 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing CInitPrimed for CInit'
2026-05-04T12:01:09,228 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing InitPrimed for Init'
2026-05-04T12:01:09,229 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass [OK]
2026-05-04T12:01:09,229 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #8: VCGen
2026-05-04T12:01:09,230 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Agreement
2026-05-04T12:01:09,237 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-05-04T12:01:09,238 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Ordering
2026-05-04T12:01:09,239 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-05-04T12:01:09,240 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #8: VCGen [OK]
2026-05-04T12:01:09,240 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass
2026-05-04T12:01:09,240 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Before preprocessing: unique renaming
2026-05-04T12:01:09,248 [main] INFO  a.f.a.t.p.p.PreproPassImpl -  > Applying standard transformations:
2026-05-04T12:01:09,249 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > PrimePropagation
2026-05-04T12:01:09,262 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Desugarer
2026-05-04T12:01:09,284 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > UniqueRenamer
2026-05-04T12:01:09,323 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Normalizer
2026-05-04T12:01:09,377 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Keramelizer
2026-05-04T12:01:09,407 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > After preprocessing: UniqueRenamer
2026-05-04T12:01:09,445 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass [OK]
2026-05-04T12:01:09,445 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass
2026-05-04T12:01:09,502 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 1 initializing transitions
2026-05-04T12:01:09,588 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 70 transitions
2026-05-04T12:01:09,588 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found constant initializer CInit
2026-05-04T12:01:09,590 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Applying unique renaming
2026-05-04T12:01:09,654 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass [OK]
2026-05-04T12:01:09,654 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass
2026-05-04T12:01:09,671 [main] INFO  a.f.a.t.p.p.OptPassImpl -  > Applying optimizations:
2026-05-04T12:01:09,672 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-05-04T12:01:09,781 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ExprOptimizer
2026-05-04T12:01:09,883 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > SetMembershipSimplifier
2026-05-04T12:01:09,913 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-05-04T12:01:10,007 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass [OK]
2026-05-04T12:01:10,007 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass
2026-05-04T12:01:10,010 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Marking skolemizable existentials and sets to be expanded...
2026-05-04T12:01:10,010 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Skolemization
2026-05-04T12:01:10,019 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Expansion
2026-05-04T12:01:10,071 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Remove unused let-in defs
2026-05-04T12:01:10,091 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Running analyzers...
2026-05-04T12:01:10,096 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Introduced expression grades
2026-05-04T12:01:10,096 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass [OK]
2026-05-04T12:01:10,096 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #13: BoundedChecker
2026-05-04T12:01:10,119 [main] DEBUG a.f.a.t.b.s.Z3SolverContext - Creating Z3 solver context 0
2026-05-04T12:01:10,334 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Initializing CONSTANTS
2026-05-04T12:01:10,369 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #0, transition #0
2026-05-04T12:01:10,369 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,403 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0. Is it enabled?
2026-05-04T12:01:10,404 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0 is enabled
2026-05-04T12:01:10,404 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: Checking 2 state invariants
2026-05-04T12:01:10,405 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 0
2026-05-04T12:01:10,453 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 0 holds.
2026-05-04T12:01:10,456 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 1
2026-05-04T12:01:10,507 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 1 holds.
2026-05-04T12:01:10,509 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 0: picking a transition out of 1 transition(s)
2026-05-04T12:01:10,510 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #0
2026-05-04T12:01:10,510 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,515 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #0. Is it enabled?
2026-05-04T12:01:10,516 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #0 is disabled
2026-05-04T12:01:10,517 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #1
2026-05-04T12:01:10,517 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,520 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #1. Is it enabled?
2026-05-04T12:01:10,520 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #1 is disabled
2026-05-04T12:01:10,521 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #2
2026-05-04T12:01:10,521 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,524 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #2. Is it enabled?
2026-05-04T12:01:10,524 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #2 is disabled
2026-05-04T12:01:10,525 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #3
2026-05-04T12:01:10,525 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,525 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-04T12:01:10,525 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #4
2026-05-04T12:01:10,525 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,525 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-05-04T12:01:10,525 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #5
2026-05-04T12:01:10,525 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,526 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #5. Is it enabled?
2026-05-04T12:01:10,526 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #5 is disabled
2026-05-04T12:01:10,527 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #6
2026-05-04T12:01:10,527 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,528 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #6. Is it enabled?
2026-05-04T12:01:10,528 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #6 is disabled
2026-05-04T12:01:10,528 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #7
2026-05-04T12:01:10,528 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-04T12:01:10,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #8
2026-05-04T12:01:10,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-04T12:01:10,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #9
2026-05-04T12:01:10,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,530 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #9. Is it enabled?
2026-05-04T12:01:10,530 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #9 is disabled
2026-05-04T12:01:10,530 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #10
2026-05-04T12:01:10,530 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,531 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #10. Is it enabled?
2026-05-04T12:01:10,532 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #10 is disabled
2026-05-04T12:01:10,532 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #11
2026-05-04T12:01:10,532 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,533 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #11. Is it enabled?
2026-05-04T12:01:10,533 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #11 is disabled
2026-05-04T12:01:10,534 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #12
2026-05-04T12:01:10,534 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,535 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #12. Is it enabled?
2026-05-04T12:01:10,535 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #12 is disabled
2026-05-04T12:01:10,535 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #13
2026-05-04T12:01:10,535 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,536 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #13. Is it enabled?
2026-05-04T12:01:10,536 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #13 is disabled
2026-05-04T12:01:10,537 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #14
2026-05-04T12:01:10,537 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,538 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #14. Is it enabled?
2026-05-04T12:01:10,538 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #14 is disabled
2026-05-04T12:01:10,538 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #15
2026-05-04T12:01:10,538 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,539 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #15. Is it enabled?
2026-05-04T12:01:10,539 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #15 is disabled
2026-05-04T12:01:10,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #16
2026-05-04T12:01:10,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,661 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16. Is it enabled?
2026-05-04T12:01:10,668 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16 is enabled
2026-05-04T12:01:10,669 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: Checking 2 state invariants
2026-05-04T12:01:10,669 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 0
2026-05-04T12:01:10,692 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 0 holds.
2026-05-04T12:01:10,694 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 1
2026-05-04T12:01:10,735 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 1 holds.
2026-05-04T12:01:10,737 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #17
2026-05-04T12:01:10,737 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,800 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #17. Is it enabled?
2026-05-04T12:01:10,803 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #17 is disabled
2026-05-04T12:01:10,805 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #18
2026-05-04T12:01:10,805 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,811 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-05-04T12:01:10,812 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #19
2026-05-04T12:01:10,812 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,817 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-05-04T12:01:10,818 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #20
2026-05-04T12:01:10,818 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,823 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-05-04T12:01:10,824 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #21
2026-05-04T12:01:10,824 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,879 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #21. Is it enabled?
2026-05-04T12:01:10,883 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #21 is disabled
2026-05-04T12:01:10,884 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #22
2026-05-04T12:01:10,884 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,891 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-05-04T12:01:10,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #23
2026-05-04T12:01:10,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-05-04T12:01:10,896 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #24
2026-05-04T12:01:10,896 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,953 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #24. Is it enabled?
2026-05-04T12:01:10,957 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #24 is disabled
2026-05-04T12:01:10,959 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #25
2026-05-04T12:01:10,959 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:10,964 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-04T12:01:10,965 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #26
2026-05-04T12:01:10,965 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:11,023 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #26. Is it enabled?
2026-05-04T12:01:11,028 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #26 is disabled
2026-05-04T12:01:11,029 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #27
2026-05-04T12:01:11,029 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:11,048 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #27. Is it enabled?
2026-05-04T12:01:11,050 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #27 is disabled
2026-05-04T12:01:11,051 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #28
2026-05-04T12:01:11,051 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:11,188 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #28. Is it enabled?
2026-05-04T12:01:11,201 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #28 is disabled
2026-05-04T12:01:11,203 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #29
2026-05-04T12:01:11,203 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:11,313 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #29. Is it enabled?
2026-05-04T12:01:11,323 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #29 is disabled
2026-05-04T12:01:11,326 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #30
2026-05-04T12:01:11,326 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:11,468 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #30. Is it enabled?
2026-05-04T12:01:11,478 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #30 is disabled
2026-05-04T12:01:11,480 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #31
2026-05-04T12:01:11,481 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:11,570 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #31. Is it enabled?
2026-05-04T12:01:11,580 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #31 is disabled
2026-05-04T12:01:11,582 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #32
2026-05-04T12:01:11,583 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:11,675 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #32. Is it enabled?
2026-05-04T12:01:11,686 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #32 is disabled
2026-05-04T12:01:11,689 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #33
2026-05-04T12:01:11,689 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:11,788 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #33. Is it enabled?
2026-05-04T12:01:11,798 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #33 is disabled
2026-05-04T12:01:11,801 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #34
2026-05-04T12:01:11,801 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:11,893 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #34. Is it enabled?
2026-05-04T12:01:11,904 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #34 is disabled
2026-05-04T12:01:11,906 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #35
2026-05-04T12:01:11,907 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,054 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #35. Is it enabled?
2026-05-04T12:01:12,065 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #35 is disabled
2026-05-04T12:01:12,067 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #36
2026-05-04T12:01:12,067 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,070 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-04T12:01:12,070 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #37
2026-05-04T12:01:12,070 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,110 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #37. Is it enabled?
2026-05-04T12:01:12,115 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #37 is disabled
2026-05-04T12:01:12,117 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #38
2026-05-04T12:01:12,117 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,118 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-04T12:01:12,119 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #39
2026-05-04T12:01:12,119 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,160 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #39. Is it enabled?
2026-05-04T12:01:12,165 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #39 is disabled
2026-05-04T12:01:12,167 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #40
2026-05-04T12:01:12,167 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-05-04T12:01:12,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #41
2026-05-04T12:01:12,169 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,193 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #41. Is it enabled?
2026-05-04T12:01:12,196 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #41 is disabled
2026-05-04T12:01:12,197 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #42
2026-05-04T12:01:12,197 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,199 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:01:12,199 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #43
2026-05-04T12:01:12,199 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,226 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #43. Is it enabled?
2026-05-04T12:01:12,229 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #43 is disabled
2026-05-04T12:01:12,230 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #44
2026-05-04T12:01:12,230 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,265 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #44. Is it enabled?
2026-05-04T12:01:12,269 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #44 is disabled
2026-05-04T12:01:12,270 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #45
2026-05-04T12:01:12,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,307 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #45. Is it enabled?
2026-05-04T12:01:12,311 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #45 is disabled
2026-05-04T12:01:12,312 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #46
2026-05-04T12:01:12,312 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,368 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #46. Is it enabled?
2026-05-04T12:01:12,373 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #46 is disabled
2026-05-04T12:01:12,375 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #47
2026-05-04T12:01:12,375 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,459 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #47. Is it enabled?
2026-05-04T12:01:12,465 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #47 is disabled
2026-05-04T12:01:12,467 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #48
2026-05-04T12:01:12,467 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,514 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #48. Is it enabled?
2026-05-04T12:01:12,519 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #48 is disabled
2026-05-04T12:01:12,521 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #49
2026-05-04T12:01:12,521 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,571 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #49. Is it enabled?
2026-05-04T12:01:12,577 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #49 is disabled
2026-05-04T12:01:12,578 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #50
2026-05-04T12:01:12,579 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,600 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #50. Is it enabled?
2026-05-04T12:01:12,603 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #50 is disabled
2026-05-04T12:01:12,603 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #51
2026-05-04T12:01:12,604 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,652 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #51. Is it enabled?
2026-05-04T12:01:12,657 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #51 is disabled
2026-05-04T12:01:12,659 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #52
2026-05-04T12:01:12,659 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,709 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #52. Is it enabled?
2026-05-04T12:01:12,715 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #52 is disabled
2026-05-04T12:01:12,716 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #53
2026-05-04T12:01:12,716 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,766 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #53. Is it enabled?
2026-05-04T12:01:12,772 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #53 is disabled
2026-05-04T12:01:12,773 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #54
2026-05-04T12:01:12,773 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,819 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #54. Is it enabled?
2026-05-04T12:01:12,825 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #54 is disabled
2026-05-04T12:01:12,826 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #55
2026-05-04T12:01:12,826 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,832 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-04T12:01:12,833 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #56
2026-05-04T12:01:12,833 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,840 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #56. Is it enabled?
2026-05-04T12:01:12,842 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #56 is disabled
2026-05-04T12:01:12,842 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #57
2026-05-04T12:01:12,842 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,847 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-05-04T12:01:12,848 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #58
2026-05-04T12:01:12,848 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,854 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #58. Is it enabled?
2026-05-04T12:01:12,855 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #58 is disabled
2026-05-04T12:01:12,856 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #59
2026-05-04T12:01:12,856 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,860 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-04T12:01:12,861 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #60
2026-05-04T12:01:12,861 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,868 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #60. Is it enabled?
2026-05-04T12:01:12,869 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #60 is disabled
2026-05-04T12:01:12,869 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #61
2026-05-04T12:01:12,869 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,919 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-04T12:01:12,920 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #62
2026-05-04T12:01:12,920 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,927 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #62. Is it enabled?
2026-05-04T12:01:12,928 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #62 is disabled
2026-05-04T12:01:12,929 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #63
2026-05-04T12:01:12,929 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,936 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #63. Is it enabled?
2026-05-04T12:01:12,937 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #63 is disabled
2026-05-04T12:01:12,938 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #64
2026-05-04T12:01:12,938 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,946 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #64. Is it enabled?
2026-05-04T12:01:12,948 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #64 is disabled
2026-05-04T12:01:12,948 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #65
2026-05-04T12:01:12,948 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:12,955 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #65. Is it enabled?
2026-05-04T12:01:12,956 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #65 is disabled
2026-05-04T12:01:12,956 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #66
2026-05-04T12:01:12,956 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,020 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #66. Is it enabled?
2026-05-04T12:01:13,027 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #66 is disabled
2026-05-04T12:01:13,029 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #67
2026-05-04T12:01:13,029 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,083 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #67. Is it enabled?
2026-05-04T12:01:13,090 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #67 is disabled
2026-05-04T12:01:13,091 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #68
2026-05-04T12:01:13,091 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,100 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #68. Is it enabled?
2026-05-04T12:01:13,101 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #68 is disabled
2026-05-04T12:01:13,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #69
2026-05-04T12:01:13,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,110 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #69. Is it enabled?
2026-05-04T12:01:13,111 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #69 is disabled
2026-05-04T12:01:13,112 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 1: picking a transition out of 1 transition(s)
2026-05-04T12:01:13,113 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #0
2026-05-04T12:01:13,113 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,185 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0. Is it enabled?
2026-05-04T12:01:13,243 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0 is enabled
2026-05-04T12:01:13,243 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: Checking 2 state invariants
2026-05-04T12:01:13,243 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 0
2026-05-04T12:01:13,283 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 0 holds.
2026-05-04T12:01:13,284 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 1
2026-05-04T12:01:13,337 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 1 holds.
2026-05-04T12:01:13,338 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #1
2026-05-04T12:01:13,339 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,378 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #1. Is it enabled?
2026-05-04T12:01:13,384 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #1 is disabled
2026-05-04T12:01:13,385 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #2
2026-05-04T12:01:13,385 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,430 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #2. Is it enabled?
2026-05-04T12:01:13,437 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #2 is disabled
2026-05-04T12:01:13,438 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #3
2026-05-04T12:01:13,438 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,442 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-04T12:01:13,442 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #4
2026-05-04T12:01:13,442 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,445 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-05-04T12:01:13,446 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #5
2026-05-04T12:01:13,446 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,475 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #5. Is it enabled?
2026-05-04T12:01:13,479 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #5 is disabled
2026-05-04T12:01:13,480 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #6
2026-05-04T12:01:13,480 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,508 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #6. Is it enabled?
2026-05-04T12:01:13,512 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #6 is disabled
2026-05-04T12:01:13,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #7
2026-05-04T12:01:13,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,516 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-04T12:01:13,516 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #8
2026-05-04T12:01:13,517 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,519 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-04T12:01:13,520 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #9
2026-05-04T12:01:13,520 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,552 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #9. Is it enabled?
2026-05-04T12:01:13,556 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #9 is disabled
2026-05-04T12:01:13,557 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #10
2026-05-04T12:01:13,558 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,588 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #10. Is it enabled?
2026-05-04T12:01:13,592 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #10 is disabled
2026-05-04T12:01:13,594 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #11
2026-05-04T12:01:13,594 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,654 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #11. Is it enabled?
2026-05-04T12:01:13,657 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #11 is disabled
2026-05-04T12:01:13,658 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #12
2026-05-04T12:01:13,658 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,765 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #12. Is it enabled?
2026-05-04T12:01:13,782 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #12 is disabled
2026-05-04T12:01:13,785 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #13
2026-05-04T12:01:13,785 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:13,893 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #13. Is it enabled?
2026-05-04T12:01:13,909 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #13 is disabled
2026-05-04T12:01:13,912 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #14
2026-05-04T12:01:13,912 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,023 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #14. Is it enabled?
2026-05-04T12:01:14,039 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #14 is disabled
2026-05-04T12:01:14,042 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #15
2026-05-04T12:01:14,042 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,153 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #15. Is it enabled?
2026-05-04T12:01:14,169 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #15 is disabled
2026-05-04T12:01:14,173 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #16
2026-05-04T12:01:14,173 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,286 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #16. Is it enabled?
2026-05-04T12:01:14,334 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #16 is enabled
2026-05-04T12:01:14,335 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: Checking 2 state invariants
2026-05-04T12:01:14,335 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 0
2026-05-04T12:01:14,376 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 0 holds.
2026-05-04T12:01:14,378 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 1
2026-05-04T12:01:14,429 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 1 holds.
2026-05-04T12:01:14,430 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #17
2026-05-04T12:01:14,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,483 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #17. Is it enabled?
2026-05-04T12:01:14,515 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #17 is disabled
2026-05-04T12:01:14,517 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #18
2026-05-04T12:01:14,517 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,535 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-05-04T12:01:14,536 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #19
2026-05-04T12:01:14,537 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,545 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-05-04T12:01:14,547 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #20
2026-05-04T12:01:14,547 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,556 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-05-04T12:01:14,558 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #21
2026-05-04T12:01:14,558 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,622 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #21. Is it enabled?
2026-05-04T12:01:14,653 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #21 is disabled
2026-05-04T12:01:14,654 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #22
2026-05-04T12:01:14,655 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,676 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-05-04T12:01:14,679 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #23
2026-05-04T12:01:14,679 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,688 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-05-04T12:01:14,689 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #24
2026-05-04T12:01:14,689 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,746 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #24. Is it enabled?
2026-05-04T12:01:14,752 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #24 is disabled
2026-05-04T12:01:14,754 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #25
2026-05-04T12:01:14,754 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,764 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-04T12:01:14,765 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #26
2026-05-04T12:01:14,765 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,872 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #26. Is it enabled?
2026-05-04T12:01:14,879 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #26 is disabled
2026-05-04T12:01:14,881 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #27
2026-05-04T12:01:14,881 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:14,904 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #27. Is it enabled?
2026-05-04T12:01:14,907 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #27 is disabled
2026-05-04T12:01:14,908 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #28
2026-05-04T12:01:14,908 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:15,031 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #28. Is it enabled?
2026-05-04T12:01:15,092 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #28 is disabled
2026-05-04T12:01:15,095 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #29
2026-05-04T12:01:15,095 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:15,253 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #29. Is it enabled?
2026-05-04T12:01:15,308 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #29 is disabled
2026-05-04T12:01:15,312 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #30
2026-05-04T12:01:15,312 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:15,447 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30. Is it enabled?
2026-05-04T12:01:15,683 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30 is enabled
2026-05-04T12:01:15,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #31
2026-05-04T12:01:15,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:15,876 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #31. Is it enabled?
2026-05-04T12:01:15,940 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #31 is disabled
2026-05-04T12:01:15,944 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #32
2026-05-04T12:01:15,944 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:16,114 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #32. Is it enabled?
2026-05-04T12:01:16,176 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #32 is disabled
2026-05-04T12:01:16,181 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #33
2026-05-04T12:01:16,181 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:16,325 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #33. Is it enabled?
2026-05-04T12:01:16,426 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #33 is disabled
2026-05-04T12:01:16,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #34
2026-05-04T12:01:16,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:16,600 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #34. Is it enabled?
2026-05-04T12:01:16,675 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #34 is disabled
2026-05-04T12:01:16,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #35
2026-05-04T12:01:16,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:16,824 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #35. Is it enabled?
2026-05-04T12:01:16,914 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #35 is disabled
2026-05-04T12:01:16,919 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #36
2026-05-04T12:01:16,919 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:16,933 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-04T12:01:16,935 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #37
2026-05-04T12:01:16,935 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,047 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #37. Is it enabled?
2026-05-04T12:01:17,056 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #37 is disabled
2026-05-04T12:01:17,059 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #38
2026-05-04T12:01:17,059 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,073 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-04T12:01:17,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #39
2026-05-04T12:01:17,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,133 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #39. Is it enabled?
2026-05-04T12:01:17,143 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #39 is disabled
2026-05-04T12:01:17,146 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #40
2026-05-04T12:01:17,146 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,161 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-05-04T12:01:17,162 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #41
2026-05-04T12:01:17,163 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,204 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #41. Is it enabled?
2026-05-04T12:01:17,210 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #41 is disabled
2026-05-04T12:01:17,212 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #42
2026-05-04T12:01:17,212 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,227 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:01:17,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #43
2026-05-04T12:01:17,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,274 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #43. Is it enabled?
2026-05-04T12:01:17,283 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #43 is disabled
2026-05-04T12:01:17,285 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #44
2026-05-04T12:01:17,286 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,358 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #44. Is it enabled?
2026-05-04T12:01:17,366 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #44 is disabled
2026-05-04T12:01:17,368 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #45
2026-05-04T12:01:17,368 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,430 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #45. Is it enabled?
2026-05-04T12:01:17,439 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #45 is disabled
2026-05-04T12:01:17,441 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #46
2026-05-04T12:01:17,441 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,558 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #46. Is it enabled?
2026-05-04T12:01:17,572 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #46 is disabled
2026-05-04T12:01:17,574 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #47
2026-05-04T12:01:17,574 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,658 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #47. Is it enabled?
2026-05-04T12:01:17,671 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #47 is disabled
2026-05-04T12:01:17,674 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #48
2026-05-04T12:01:17,674 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,760 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #48. Is it enabled?
2026-05-04T12:01:17,776 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #48 is disabled
2026-05-04T12:01:17,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #49
2026-05-04T12:01:17,779 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,868 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #49. Is it enabled?
2026-05-04T12:01:17,883 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #49 is disabled
2026-05-04T12:01:17,886 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #50
2026-05-04T12:01:17,886 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:17,931 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #50. Is it enabled?
2026-05-04T12:01:17,937 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #50 is disabled
2026-05-04T12:01:17,938 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #51
2026-05-04T12:01:17,939 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,060 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #51. Is it enabled?
2026-05-04T12:01:18,074 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #51 is disabled
2026-05-04T12:01:18,078 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #52
2026-05-04T12:01:18,078 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,166 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #52. Is it enabled?
2026-05-04T12:01:18,184 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #52 is disabled
2026-05-04T12:01:18,187 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #53
2026-05-04T12:01:18,187 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,254 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #53. Is it enabled?
2026-05-04T12:01:18,267 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #53 is disabled
2026-05-04T12:01:18,270 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #54
2026-05-04T12:01:18,270 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,320 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #54. Is it enabled?
2026-05-04T12:01:18,330 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #54 is disabled
2026-05-04T12:01:18,332 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #55
2026-05-04T12:01:18,332 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,338 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-04T12:01:18,339 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #56
2026-05-04T12:01:18,339 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,381 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #56. Is it enabled?
2026-05-04T12:01:18,390 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #56 is disabled
2026-05-04T12:01:18,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #57
2026-05-04T12:01:18,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,397 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-05-04T12:01:18,398 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #58
2026-05-04T12:01:18,398 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,442 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #58. Is it enabled?
2026-05-04T12:01:18,451 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #58 is disabled
2026-05-04T12:01:18,453 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #59
2026-05-04T12:01:18,453 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,458 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-04T12:01:18,459 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #60
2026-05-04T12:01:18,459 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,489 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #60. Is it enabled?
2026-05-04T12:01:18,494 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #60 is disabled
2026-05-04T12:01:18,496 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #61
2026-05-04T12:01:18,496 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,501 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-04T12:01:18,502 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #62
2026-05-04T12:01:18,502 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,533 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #62. Is it enabled?
2026-05-04T12:01:18,539 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #62 is disabled
2026-05-04T12:01:18,541 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #63
2026-05-04T12:01:18,541 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,583 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #63. Is it enabled?
2026-05-04T12:01:18,591 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #63 is disabled
2026-05-04T12:01:18,593 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #64
2026-05-04T12:01:18,593 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,721 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #64. Is it enabled?
2026-05-04T12:01:18,738 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #64 is disabled
2026-05-04T12:01:18,742 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #65
2026-05-04T12:01:18,742 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,756 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #65. Is it enabled?
2026-05-04T12:01:18,758 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #65 is disabled
2026-05-04T12:01:18,759 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #66
2026-05-04T12:01:18,759 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,842 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #66. Is it enabled?
2026-05-04T12:01:18,858 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #66 is disabled
2026-05-04T12:01:18,861 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #67
2026-05-04T12:01:18,861 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,925 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #67. Is it enabled?
2026-05-04T12:01:18,936 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #67 is disabled
2026-05-04T12:01:18,938 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #68
2026-05-04T12:01:18,938 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:18,987 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #68. Is it enabled?
2026-05-04T12:01:18,996 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #68 is disabled
2026-05-04T12:01:18,998 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #69
2026-05-04T12:01:18,998 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:19,071 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #69. Is it enabled?
2026-05-04T12:01:19,087 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #69 is disabled
2026-05-04T12:01:19,090 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 2: picking a transition out of 3 transition(s)
2026-05-04T12:01:19,128 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #0
2026-05-04T12:01:19,128 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:19,195 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0. Is it enabled?
2026-05-04T12:01:19,584 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0 is enabled
2026-05-04T12:01:19,585 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 2 state invariants
2026-05-04T12:01:19,585 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-05-04T12:01:20,049 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-05-04T12:01:20,051 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 1
2026-05-04T12:01:20,517 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 1 holds.
2026-05-04T12:01:20,522 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #1
2026-05-04T12:01:20,522 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:20,588 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #1. Is it enabled?
2026-05-04T12:01:20,612 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #1 is disabled
2026-05-04T12:01:20,616 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #2
2026-05-04T12:01:20,616 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:20,675 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #2. Is it enabled?
2026-05-04T12:01:20,686 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #2 is disabled
2026-05-04T12:01:20,690 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #3
2026-05-04T12:01:20,690 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:20,698 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-04T12:01:20,699 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #4
2026-05-04T12:01:20,699 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:20,707 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-05-04T12:01:20,708 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #5
2026-05-04T12:01:20,708 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:20,815 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #5. Is it enabled?
2026-05-04T12:01:20,825 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #5 is disabled
2026-05-04T12:01:20,827 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #6
2026-05-04T12:01:20,827 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:20,870 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #6. Is it enabled?
2026-05-04T12:01:20,893 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #6 is disabled
2026-05-04T12:01:20,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #7
2026-05-04T12:01:20,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:20,903 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-04T12:01:20,905 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #8
2026-05-04T12:01:20,905 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:20,912 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-04T12:01:20,913 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #9
2026-05-04T12:01:20,913 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:20,958 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #9. Is it enabled?
2026-05-04T12:01:20,970 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #9 is disabled
2026-05-04T12:01:20,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #10
2026-05-04T12:01:20,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:21,022 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #10. Is it enabled?
2026-05-04T12:01:21,033 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #10 is disabled
2026-05-04T12:01:21,035 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #11
2026-05-04T12:01:21,035 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:21,068 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #11. Is it enabled?
2026-05-04T12:01:21,082 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #11 is disabled
2026-05-04T12:01:21,085 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #12
2026-05-04T12:01:21,085 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:01:21,231 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #12. Is it enabled?
2026-05-04T12:01:21,265 [main] DEBUG a.f.a.i.p.PassChainExecutor - Adapted exception intercepted: 
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
2026-05-04T12:01:21,322 [main] ERROR a.f.a.t.Tool\$ - <unknown>: error when rewriting to SMT: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
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

