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
--config=AccordSpec.cfg --length=10
```

## Expected behavior

<!-- What did you expect to see? -->

## Log files

<details>

```
2026-05-04T12:08:04,561 [main] INFO  a.f.a.t.Tool\$ - # APALACHE version: 0.56.1 | build: 70cdaf4
2026-05-04T12:08:04,577 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > AccordSpec.cfg: Loading TLC configuration
2026-05-04T12:08:04,623 [main] WARN  a.f.a.i.t.TlcConfigParserApalache\$ - TLC config option CHECK_DEADLOCK true will be ignored
2026-05-04T12:08:04,629 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > Using inv predicate(s) Agreement, Ordering from the TLC config
2026-05-04T12:08:04,630 [main] INFO  a.f.a.t.t.o.SimulateCmd - Tuning: search.simulation.maxRun=100:search.simulation=true:search.outputTraces=false
2026-05-04T12:08:04,811 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser
2026-05-04T12:08:05,537 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser [OK]
2026-05-04T12:08:05,537 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat
2026-05-04T12:08:05,537 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Running Snowcat .::.
2026-05-04T12:08:14,175 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Your types are purrfect!
2026-05-04T12:08:14,176 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > All expressions are typed
2026-05-04T12:08:14,176 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat [OK]
2026-05-04T12:08:14,176 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass
2026-05-04T12:08:14,318 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: Using SPECIFICATION Spec
2026-05-04T12:08:14,319 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: found INVARIANTS: Agreement, Ordering
2026-05-04T12:08:14,322 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the initialization predicate to Init
2026-05-04T12:08:14,322 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the transition predicate to Next
2026-05-04T12:08:14,322 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the constant initialization predicate to CInit
2026-05-04T12:08:14,322 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Agreement
2026-05-04T12:08:14,322 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Ordering
2026-05-04T12:08:14,328 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass [OK]
2026-05-04T12:08:14,328 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass
2026-05-04T12:08:14,328 [main] INFO  a.f.a.t.p.p.DesugarerPassImpl -   > Desugaring...
2026-05-04T12:08:14,352 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass [OK]
2026-05-04T12:08:14,352 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass
2026-05-04T12:08:14,353 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next, Ordering
2026-05-04T12:08:14,558 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass [OK]
2026-05-04T12:08:14,559 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass
2026-05-04T12:08:14,559 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > Rewriting temporal operators...
2026-05-04T12:08:14,559 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > No temporal property specified, nothing to encode
2026-05-04T12:08:14,559 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass [OK]
2026-05-04T12:08:14,559 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass
2026-05-04T12:08:14,559 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next, Ordering
2026-05-04T12:08:14,628 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass [OK]
2026-05-04T12:08:14,628 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass
2026-05-04T12:08:14,630 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing CInitPrimed for CInit'
2026-05-04T12:08:14,630 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing InitPrimed for Init'
2026-05-04T12:08:14,631 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass [OK]
2026-05-04T12:08:14,631 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #8: VCGen
2026-05-04T12:08:14,631 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Agreement
2026-05-04T12:08:14,635 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-05-04T12:08:14,636 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Ordering
2026-05-04T12:08:14,637 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-05-04T12:08:14,637 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #8: VCGen [OK]
2026-05-04T12:08:14,637 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass
2026-05-04T12:08:14,637 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Before preprocessing: unique renaming
2026-05-04T12:08:14,642 [main] INFO  a.f.a.t.p.p.PreproPassImpl -  > Applying standard transformations:
2026-05-04T12:08:14,643 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > PrimePropagation
2026-05-04T12:08:14,649 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Desugarer
2026-05-04T12:08:14,658 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > UniqueRenamer
2026-05-04T12:08:14,704 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Normalizer
2026-05-04T12:08:14,734 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Keramelizer
2026-05-04T12:08:14,769 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > After preprocessing: UniqueRenamer
2026-05-04T12:08:14,831 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass [OK]
2026-05-04T12:08:14,831 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass
2026-05-04T12:08:14,913 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 1 initializing transitions
2026-05-04T12:08:15,003 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 70 transitions
2026-05-04T12:08:15,005 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found constant initializer CInit
2026-05-04T12:08:15,009 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Applying unique renaming
2026-05-04T12:08:15,177 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass [OK]
2026-05-04T12:08:15,177 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass
2026-05-04T12:08:15,181 [main] INFO  a.f.a.t.p.p.OptPassImpl -  > Applying optimizations:
2026-05-04T12:08:15,182 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-05-04T12:08:15,344 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ExprOptimizer
2026-05-04T12:08:15,411 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > SetMembershipSimplifier
2026-05-04T12:08:15,432 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-05-04T12:08:15,568 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass [OK]
2026-05-04T12:08:15,569 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass
2026-05-04T12:08:15,574 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Marking skolemizable existentials and sets to be expanded...
2026-05-04T12:08:15,575 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Skolemization
2026-05-04T12:08:15,591 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Expansion
2026-05-04T12:08:15,640 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Remove unused let-in defs
2026-05-04T12:08:15,674 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Running analyzers...
2026-05-04T12:08:15,685 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Introduced expression grades
2026-05-04T12:08:15,686 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass [OK]
2026-05-04T12:08:15,686 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #13: BoundedChecker
2026-05-04T12:08:15,721 [main] DEBUG a.f.a.t.b.s.Z3SolverContext - Creating Z3 solver context 0
2026-05-04T12:08:15,951 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Initializing CONSTANTS
2026-05-04T12:08:15,989 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #0, transition #0
2026-05-04T12:08:15,989 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,024 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0. Is it enabled?
2026-05-04T12:08:16,026 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0 is enabled
2026-05-04T12:08:16,027 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: Checking 2 state invariants
2026-05-04T12:08:16,027 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 0
2026-05-04T12:08:16,078 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 0 holds.
2026-05-04T12:08:16,081 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 1
2026-05-04T12:08:16,131 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 1 holds.
2026-05-04T12:08:16,133 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 0: randomly picked transition #0
2026-05-04T12:08:16,133 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 0: picking a transition out of 1 transition(s)
2026-05-04T12:08:16,135 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #5
2026-05-04T12:08:16,136 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,138 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #5. Is it enabled?
2026-05-04T12:08:16,139 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #5 is disabled
2026-05-04T12:08:16,139 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #14
2026-05-04T12:08:16,139 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,141 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #14. Is it enabled?
2026-05-04T12:08:16,141 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #14 is disabled
2026-05-04T12:08:16,142 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #69
2026-05-04T12:08:16,142 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,170 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #69. Is it enabled?
2026-05-04T12:08:16,171 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #69 is disabled
2026-05-04T12:08:16,172 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #26
2026-05-04T12:08:16,172 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,265 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #26. Is it enabled?
2026-05-04T12:08:16,268 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #26 is disabled
2026-05-04T12:08:16,270 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #22
2026-05-04T12:08:16,270 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,280 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-05-04T12:08:16,280 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #57
2026-05-04T12:08:16,280 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,289 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-05-04T12:08:16,290 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #58
2026-05-04T12:08:16,290 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,301 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #58. Is it enabled?
2026-05-04T12:08:16,303 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #58 is disabled
2026-05-04T12:08:16,303 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #10
2026-05-04T12:08:16,303 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,304 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #10. Is it enabled?
2026-05-04T12:08:16,305 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #10 is disabled
2026-05-04T12:08:16,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #53
2026-05-04T12:08:16,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,399 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #53. Is it enabled?
2026-05-04T12:08:16,404 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #53 is disabled
2026-05-04T12:08:16,406 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #54
2026-05-04T12:08:16,406 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,471 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #54. Is it enabled?
2026-05-04T12:08:16,476 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #54 is disabled
2026-05-04T12:08:16,478 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #55
2026-05-04T12:08:16,478 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,486 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-04T12:08:16,487 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #3
2026-05-04T12:08:16,487 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,487 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-04T12:08:16,487 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #64
2026-05-04T12:08:16,487 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,497 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #64. Is it enabled?
2026-05-04T12:08:16,498 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #64 is disabled
2026-05-04T12:08:16,498 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #23
2026-05-04T12:08:16,498 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,502 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-05-04T12:08:16,502 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #56
2026-05-04T12:08:16,502 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,511 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #56. Is it enabled?
2026-05-04T12:08:16,512 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #56 is disabled
2026-05-04T12:08:16,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #40
2026-05-04T12:08:16,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,515 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-05-04T12:08:16,515 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #20
2026-05-04T12:08:16,515 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,519 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-05-04T12:08:16,519 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #13
2026-05-04T12:08:16,519 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,520 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #13. Is it enabled?
2026-05-04T12:08:16,521 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #13 is disabled
2026-05-04T12:08:16,521 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #48
2026-05-04T12:08:16,521 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,588 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #48. Is it enabled?
2026-05-04T12:08:16,593 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #48 is disabled
2026-05-04T12:08:16,595 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #27
2026-05-04T12:08:16,595 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,611 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #27. Is it enabled?
2026-05-04T12:08:16,613 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #27 is disabled
2026-05-04T12:08:16,613 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #43
2026-05-04T12:08:16,613 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,676 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #43. Is it enabled?
2026-05-04T12:08:16,679 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #43 is disabled
2026-05-04T12:08:16,680 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #15
2026-05-04T12:08:16,680 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,682 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #15. Is it enabled?
2026-05-04T12:08:16,682 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #15 is disabled
2026-05-04T12:08:16,683 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #59
2026-05-04T12:08:16,683 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,690 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-04T12:08:16,691 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #6
2026-05-04T12:08:16,691 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,691 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #6. Is it enabled?
2026-05-04T12:08:16,692 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #6 is disabled
2026-05-04T12:08:16,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #34
2026-05-04T12:08:16,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,809 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #34. Is it enabled?
2026-05-04T12:08:16,822 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #34 is disabled
2026-05-04T12:08:16,825 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #24
2026-05-04T12:08:16,825 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,867 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #24. Is it enabled?
2026-05-04T12:08:16,873 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #24 is disabled
2026-05-04T12:08:16,874 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #2
2026-05-04T12:08:16,874 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,875 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #2. Is it enabled?
2026-05-04T12:08:16,876 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #2 is disabled
2026-05-04T12:08:16,876 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #12
2026-05-04T12:08:16,876 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,877 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #12. Is it enabled?
2026-05-04T12:08:16,877 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #12 is disabled
2026-05-04T12:08:16,878 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #29
2026-05-04T12:08:16,878 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:16,983 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #29. Is it enabled?
2026-05-04T12:08:16,993 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #29 is disabled
2026-05-04T12:08:16,996 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #67
2026-05-04T12:08:16,996 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,050 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #67. Is it enabled?
2026-05-04T12:08:17,055 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #67 is disabled
2026-05-04T12:08:17,056 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #32
2026-05-04T12:08:17,057 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,200 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #32. Is it enabled?
2026-05-04T12:08:17,211 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #32 is disabled
2026-05-04T12:08:17,214 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #68
2026-05-04T12:08:17,214 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,224 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #68. Is it enabled?
2026-05-04T12:08:17,225 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #68 is disabled
2026-05-04T12:08:17,225 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #60
2026-05-04T12:08:17,225 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,232 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #60. Is it enabled?
2026-05-04T12:08:17,233 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #60 is disabled
2026-05-04T12:08:17,233 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #63
2026-05-04T12:08:17,233 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,240 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #63. Is it enabled?
2026-05-04T12:08:17,241 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #63 is disabled
2026-05-04T12:08:17,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #8
2026-05-04T12:08:17,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-04T12:08:17,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #38
2026-05-04T12:08:17,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,244 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-04T12:08:17,244 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #21
2026-05-04T12:08:17,244 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,277 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #21. Is it enabled?
2026-05-04T12:08:17,280 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #21 is disabled
2026-05-04T12:08:17,280 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #4
2026-05-04T12:08:17,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-05-04T12:08:17,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #62
2026-05-04T12:08:17,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,287 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #62. Is it enabled?
2026-05-04T12:08:17,288 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #62 is disabled
2026-05-04T12:08:17,289 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #19
2026-05-04T12:08:17,289 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,292 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-05-04T12:08:17,292 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #50
2026-05-04T12:08:17,292 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,315 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #50. Is it enabled?
2026-05-04T12:08:17,317 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #50 is disabled
2026-05-04T12:08:17,318 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #51
2026-05-04T12:08:17,318 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,369 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #51. Is it enabled?
2026-05-04T12:08:17,374 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #51 is disabled
2026-05-04T12:08:17,376 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #1
2026-05-04T12:08:17,376 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,377 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #1. Is it enabled?
2026-05-04T12:08:17,377 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #1 is disabled
2026-05-04T12:08:17,378 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #28
2026-05-04T12:08:17,378 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,501 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #28. Is it enabled?
2026-05-04T12:08:17,511 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #28 is disabled
2026-05-04T12:08:17,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #30
2026-05-04T12:08:17,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,618 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #30. Is it enabled?
2026-05-04T12:08:17,630 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #30 is disabled
2026-05-04T12:08:17,634 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #41
2026-05-04T12:08:17,634 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,665 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #41. Is it enabled?
2026-05-04T12:08:17,668 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #41 is disabled
2026-05-04T12:08:17,669 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #9
2026-05-04T12:08:17,669 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,670 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #9. Is it enabled?
2026-05-04T12:08:17,670 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #9 is disabled
2026-05-04T12:08:17,671 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #42
2026-05-04T12:08:17,671 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,672 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:08:17,673 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #65
2026-05-04T12:08:17,673 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,680 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #65. Is it enabled?
2026-05-04T12:08:17,681 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #65 is disabled
2026-05-04T12:08:17,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #36
2026-05-04T12:08:17,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,683 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-04T12:08:17,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #25
2026-05-04T12:08:17,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-04T12:08:17,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #31
2026-05-04T12:08:17,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,788 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #31. Is it enabled?
2026-05-04T12:08:17,798 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #31 is disabled
2026-05-04T12:08:17,800 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #47
2026-05-04T12:08:17,800 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,859 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #47. Is it enabled?
2026-05-04T12:08:17,864 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #47 is disabled
2026-05-04T12:08:17,866 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #35
2026-05-04T12:08:17,866 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:17,990 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #35. Is it enabled?
2026-05-04T12:08:18,000 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #35 is disabled
2026-05-04T12:08:18,002 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #17
2026-05-04T12:08:18,002 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,067 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #17. Is it enabled?
2026-05-04T12:08:18,070 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #17 is disabled
2026-05-04T12:08:18,071 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #39
2026-05-04T12:08:18,071 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,111 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #39. Is it enabled?
2026-05-04T12:08:18,116 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #39 is disabled
2026-05-04T12:08:18,117 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #0
2026-05-04T12:08:18,117 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,118 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #0. Is it enabled?
2026-05-04T12:08:18,118 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #0 is disabled
2026-05-04T12:08:18,118 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #49
2026-05-04T12:08:18,118 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,183 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #49. Is it enabled?
2026-05-04T12:08:18,188 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #49 is disabled
2026-05-04T12:08:18,189 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #45
2026-05-04T12:08:18,189 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,224 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #45. Is it enabled?
2026-05-04T12:08:18,228 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #45 is disabled
2026-05-04T12:08:18,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #33
2026-05-04T12:08:18,229 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,311 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #33. Is it enabled?
2026-05-04T12:08:18,321 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #33 is disabled
2026-05-04T12:08:18,323 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #16
2026-05-04T12:08:18,323 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,367 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16. Is it enabled?
2026-05-04T12:08:18,376 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16 is enabled
2026-05-04T12:08:18,377 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: Checking 2 state invariants
2026-05-04T12:08:18,377 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 0
2026-05-04T12:08:18,400 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 0 holds.
2026-05-04T12:08:18,401 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 1
2026-05-04T12:08:18,427 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 1 holds.
2026-05-04T12:08:18,428 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: randomly picked transition #16
2026-05-04T12:08:18,428 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 1: picking a transition out of 1 transition(s)
2026-05-04T12:08:18,429 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #18
2026-05-04T12:08:18,429 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,453 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-05-04T12:08:18,455 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #59
2026-05-04T12:08:18,455 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,461 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-04T12:08:18,462 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #9
2026-05-04T12:08:18,462 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,534 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #9. Is it enabled?
2026-05-04T12:08:18,538 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #9 is disabled
2026-05-04T12:08:18,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #15
2026-05-04T12:08:18,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,688 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #15. Is it enabled?
2026-05-04T12:08:18,707 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #15 is disabled
2026-05-04T12:08:18,711 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #56
2026-05-04T12:08:18,711 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,760 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #56. Is it enabled?
2026-05-04T12:08:18,767 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #56 is disabled
2026-05-04T12:08:18,769 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #55
2026-05-04T12:08:18,769 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,775 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-04T12:08:18,776 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #32
2026-05-04T12:08:18,776 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:18,909 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #32. Is it enabled?
2026-05-04T12:08:18,948 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #32 is disabled
2026-05-04T12:08:18,952 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #67
2026-05-04T12:08:18,952 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,041 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #67. Is it enabled?
2026-05-04T12:08:19,049 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #67 is disabled
2026-05-04T12:08:19,050 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #30
2026-05-04T12:08:19,051 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,181 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30. Is it enabled?
2026-05-04T12:08:19,307 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30 is enabled
2026-05-04T12:08:19,310 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: randomly picked transition #30
2026-05-04T12:08:19,310 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 2: picking a transition out of 1 transition(s)
2026-05-04T12:08:19,311 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #27
2026-05-04T12:08:19,311 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,385 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #27. Is it enabled?
2026-05-04T12:08:19,393 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #27 is disabled
2026-05-04T12:08:19,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #2
2026-05-04T12:08:19,396 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,491 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #2. Is it enabled?
2026-05-04T12:08:19,500 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #2 is disabled
2026-05-04T12:08:19,502 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #3
2026-05-04T12:08:19,502 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-04T12:08:19,514 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #20
2026-05-04T12:08:19,514 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,574 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-05-04T12:08:19,578 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #43
2026-05-04T12:08:19,578 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,679 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #43. Is it enabled?
2026-05-04T12:08:19,689 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #43 is disabled
2026-05-04T12:08:19,691 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #39
2026-05-04T12:08:19,691 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,808 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #39. Is it enabled?
2026-05-04T12:08:19,821 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #39 is disabled
2026-05-04T12:08:19,826 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #54
2026-05-04T12:08:19,827 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,888 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #54. Is it enabled?
2026-05-04T12:08:19,898 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #54 is disabled
2026-05-04T12:08:19,900 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #11
2026-05-04T12:08:19,900 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:19,930 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #11. Is it enabled?
2026-05-04T12:08:19,934 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #11 is disabled
2026-05-04T12:08:19,936 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #13
2026-05-04T12:08:19,936 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:20,065 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #13. Is it enabled?
2026-05-04T12:08:20,134 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #13 is disabled
2026-05-04T12:08:20,139 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #32
2026-05-04T12:08:20,139 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:20,338 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #32. Is it enabled?
2026-05-04T12:08:20,404 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #32 is disabled
2026-05-04T12:08:20,410 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #62
2026-05-04T12:08:20,410 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:20,446 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #62. Is it enabled?
2026-05-04T12:08:20,451 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #62 is disabled
2026-05-04T12:08:20,453 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #5
2026-05-04T12:08:20,453 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:20,491 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #5. Is it enabled?
2026-05-04T12:08:20,498 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #5 is disabled
2026-05-04T12:08:20,499 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #12
2026-05-04T12:08:20,499 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:20,625 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #12. Is it enabled?
2026-05-04T12:08:20,723 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #12 is disabled
2026-05-04T12:08:20,728 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #7
2026-05-04T12:08:20,728 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:20,736 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-04T12:08:20,737 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #17
2026-05-04T12:08:20,737 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:20,829 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #17. Is it enabled?
2026-05-04T12:08:20,858 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #17 is disabled
2026-05-04T12:08:20,860 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #50
2026-05-04T12:08:20,860 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:20,946 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #50. Is it enabled?
2026-05-04T12:08:21,022 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #50 is disabled
2026-05-04T12:08:21,024 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #52
2026-05-04T12:08:21,024 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:21,144 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #52. Is it enabled?
2026-05-04T12:08:21,200 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #52 is disabled
2026-05-04T12:08:21,204 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #47
2026-05-04T12:08:21,204 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:21,364 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #47. Is it enabled?
2026-05-04T12:08:21,383 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #47 is disabled
2026-05-04T12:08:21,386 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #25
2026-05-04T12:08:21,386 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:21,406 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-04T12:08:21,408 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #59
2026-05-04T12:08:21,408 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:21,414 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-04T12:08:21,415 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #61
2026-05-04T12:08:21,415 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:21,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-04T12:08:21,422 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #56
2026-05-04T12:08:21,422 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:21,472 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #56. Is it enabled?
2026-05-04T12:08:21,481 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #56 is disabled
2026-05-04T12:08:21,483 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #49
2026-05-04T12:08:21,483 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:21,609 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #49. Is it enabled?
2026-05-04T12:08:21,639 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #49 is disabled
2026-05-04T12:08:21,642 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #9
2026-05-04T12:08:21,643 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:21,688 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #9. Is it enabled?
2026-05-04T12:08:21,694 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #9 is disabled
2026-05-04T12:08:21,696 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #34
2026-05-04T12:08:21,696 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:21,874 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #34. Is it enabled?
2026-05-04T12:08:21,958 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #34 is disabled
2026-05-04T12:08:21,963 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #0
2026-05-04T12:08:21,963 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:22,030 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0. Is it enabled?
2026-05-04T12:08:22,187 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0 is enabled
2026-05-04T12:08:22,188 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 2 state invariants
2026-05-04T12:08:22,188 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-05-04T12:08:22,287 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-05-04T12:08:22,289 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 1
2026-05-04T12:08:22,380 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 1 holds.
2026-05-04T12:08:22,384 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: randomly picked transition #0
2026-05-04T12:08:22,385 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 3: picking a transition out of 1 transition(s)
2026-05-04T12:08:22,386 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #38
2026-05-04T12:08:22,386 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:22,430 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-04T12:08:22,435 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #42
2026-05-04T12:08:22,436 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:22,467 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:08:22,472 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #47
2026-05-04T12:08:22,472 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:22,625 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #47. Is it enabled?
2026-05-04T12:08:22,644 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #47 is disabled
2026-05-04T12:08:22,647 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #51
2026-05-04T12:08:22,647 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:22,771 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #51. Is it enabled?
2026-05-04T12:08:22,888 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #51 is disabled
2026-05-04T12:08:22,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #57
2026-05-04T12:08:22,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:22,899 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-05-04T12:08:22,900 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #52
2026-05-04T12:08:22,900 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:23,027 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #52. Is it enabled?
2026-05-04T12:08:23,115 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #52 is disabled
2026-05-04T12:08:23,119 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #37
2026-05-04T12:08:23,119 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:23,246 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #37. Is it enabled?
2026-05-04T12:08:23,263 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #37 is disabled
2026-05-04T12:08:23,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #39
2026-05-04T12:08:23,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:23,367 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #39. Is it enabled?
2026-05-04T12:08:23,384 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #39 is disabled
2026-05-04T12:08:23,387 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #44
2026-05-04T12:08:23,387 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:23,512 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #44. Is it enabled?
2026-05-04T12:08:23,527 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #44 is disabled
2026-05-04T12:08:23,530 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #66
2026-05-04T12:08:23,531 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:23,627 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #66. Is it enabled?
2026-05-04T12:08:23,646 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #66 is disabled
2026-05-04T12:08:23,649 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #58
2026-05-04T12:08:23,649 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:23,716 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #58. Is it enabled?
2026-05-04T12:08:23,728 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #58 is disabled
2026-05-04T12:08:23,731 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #14
2026-05-04T12:08:23,731 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:23,870 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #14. Is it enabled?
2026-05-04T12:08:24,095 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #14 is disabled
2026-05-04T12:08:24,101 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #61
2026-05-04T12:08:24,101 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:24,108 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-04T12:08:24,109 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #65
2026-05-04T12:08:24,109 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:24,121 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #65. Is it enabled?
2026-05-04T12:08:24,123 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #65 is disabled
2026-05-04T12:08:24,124 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #54
2026-05-04T12:08:24,124 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:24,181 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #54. Is it enabled?
2026-05-04T12:08:24,194 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #54 is disabled
2026-05-04T12:08:24,196 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #46
2026-05-04T12:08:24,196 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:24,366 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #46. Is it enabled?
2026-05-04T12:08:24,385 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #46 is disabled
2026-05-04T12:08:24,389 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #25
2026-05-04T12:08:24,389 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:24,407 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-04T12:08:24,413 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #0
2026-05-04T12:08:24,413 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:24,506 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #0. Is it enabled?
2026-05-04T12:08:24,830 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #0 is enabled
2026-05-04T12:08:24,831 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 2 state invariants
2026-05-04T12:08:24,831 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-05-04T12:08:24,999 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-05-04T12:08:25,003 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 1
2026-05-04T12:08:25,144 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 1 holds.
2026-05-04T12:08:25,148 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: randomly picked transition #0
2026-05-04T12:08:25,148 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 4: picking a transition out of 1 transition(s)
2026-05-04T12:08:25,149 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #45
2026-05-04T12:08:25,149 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:25,269 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #45. Is it enabled?
2026-05-04T12:08:25,288 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #45 is disabled
2026-05-04T12:08:25,292 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #5
2026-05-04T12:08:25,292 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:25,339 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #5. Is it enabled?
2026-05-04T12:08:25,347 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #5 is disabled
2026-05-04T12:08:25,349 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #2
2026-05-04T12:08:25,349 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:25,412 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #2. Is it enabled?
2026-05-04T12:08:25,423 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #2 is disabled
2026-05-04T12:08:25,427 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #63
2026-05-04T12:08:25,427 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:25,480 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #63. Is it enabled?
2026-05-04T12:08:25,489 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #63 is disabled
2026-05-04T12:08:25,492 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #31
2026-05-04T12:08:25,492 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:25,651 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #31. Is it enabled?
2026-05-04T12:08:25,917 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #31 is disabled
2026-05-04T12:08:25,926 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #6
2026-05-04T12:08:25,926 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:25,970 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #6. Is it enabled?
2026-05-04T12:08:25,977 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #6 is disabled
2026-05-04T12:08:25,979 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #17
2026-05-04T12:08:25,979 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:26,055 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #17. Is it enabled?
2026-05-04T12:08:26,385 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #17 is disabled
2026-05-04T12:08:26,388 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #35
2026-05-04T12:08:26,388 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:26,509 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #35. Is it enabled?
2026-05-04T12:08:26,840 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #35 is disabled
2026-05-04T12:08:26,846 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #51
2026-05-04T12:08:26,847 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:27,050 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #51. Is it enabled?
2026-05-04T12:08:27,154 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #51 is disabled
2026-05-04T12:08:27,159 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #14
2026-05-04T12:08:27,159 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:27,314 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #14. Is it enabled?
2026-05-04T12:08:27,664 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #14 is disabled
2026-05-04T12:08:27,672 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #54
2026-05-04T12:08:27,672 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:27,726 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #54. Is it enabled?
2026-05-04T12:08:27,735 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #54 is disabled
2026-05-04T12:08:27,738 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #42
2026-05-04T12:08:27,738 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:27,785 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:08:27,790 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #38
2026-05-04T12:08:27,791 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:27,825 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-04T12:08:27,830 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #40
2026-05-04T12:08:27,830 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:27,866 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-05-04T12:08:27,870 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #3
2026-05-04T12:08:27,870 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:27,877 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-04T12:08:27,878 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #41
2026-05-04T12:08:27,878 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:28,011 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #41. Is it enabled?
2026-05-04T12:08:28,022 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #41 is disabled
2026-05-04T12:08:28,025 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #47
2026-05-04T12:08:28,025 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:28,148 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #47. Is it enabled?
2026-05-04T12:08:28,170 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #47 is disabled
2026-05-04T12:08:28,174 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #15
2026-05-04T12:08:28,174 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:28,307 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #15. Is it enabled?
2026-05-04T12:08:28,568 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #15 is disabled
2026-05-04T12:08:28,577 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #68
2026-05-04T12:08:28,577 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:28,677 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #68. Is it enabled?
2026-05-04T12:08:28,685 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #68 is disabled
2026-05-04T12:08:28,687 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #11
2026-05-04T12:08:28,687 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:28,719 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #11. Is it enabled?
2026-05-04T12:08:28,724 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #11 is disabled
2026-05-04T12:08:28,726 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #48
2026-05-04T12:08:28,726 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:28,865 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #48. Is it enabled?
2026-05-04T12:08:28,893 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #48 is disabled
2026-05-04T12:08:28,898 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #46
2026-05-04T12:08:28,898 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:29,016 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #46. Is it enabled?
2026-05-04T12:08:29,038 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #46 is disabled
2026-05-04T12:08:29,043 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #25
2026-05-04T12:08:29,043 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:29,062 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-04T12:08:29,066 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #55
2026-05-04T12:08:29,066 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:29,071 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-04T12:08:29,072 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #44
2026-05-04T12:08:29,072 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:29,205 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #44. Is it enabled?
2026-05-04T12:08:29,223 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #44 is disabled
2026-05-04T12:08:29,227 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #20
2026-05-04T12:08:29,227 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:29,246 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-05-04T12:08:29,249 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #24
2026-05-04T12:08:29,249 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:29,323 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #24. Is it enabled?
2026-05-04T12:08:29,338 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #24 is disabled
2026-05-04T12:08:29,342 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #28
2026-05-04T12:08:29,342 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:29,466 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #28. Is it enabled?
2026-05-04T12:08:29,883 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #28 is disabled
2026-05-04T12:08:29,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #23
2026-05-04T12:08:29,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:29,909 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-05-04T12:08:29,913 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #12
2026-05-04T12:08:29,913 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:30,178 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #12. Is it enabled?
2026-05-04T12:08:30,531 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #12 is disabled
2026-05-04T12:08:30,538 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #60
2026-05-04T12:08:30,538 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:30,587 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #60. Is it enabled?
2026-05-04T12:08:30,594 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #60 is disabled
2026-05-04T12:08:30,597 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #39
2026-05-04T12:08:30,597 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:30,708 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #39. Is it enabled?
2026-05-04T12:08:30,730 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #39 is disabled
2026-05-04T12:08:30,734 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #67
2026-05-04T12:08:30,734 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:30,795 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #67. Is it enabled?
2026-05-04T12:08:30,809 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #67 is disabled
2026-05-04T12:08:30,812 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #21
2026-05-04T12:08:30,812 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:30,923 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #21. Is it enabled?
2026-05-04T12:08:31,045 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #21 is disabled
2026-05-04T12:08:31,050 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #8
2026-05-04T12:08:31,050 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:31,100 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-04T12:08:31,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #56
2026-05-04T12:08:31,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:31,149 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #56. Is it enabled?
2026-05-04T12:08:31,161 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #56 is disabled
2026-05-04T12:08:31,163 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #49
2026-05-04T12:08:31,163 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:31,301 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #49. Is it enabled?
2026-05-04T12:08:31,339 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #49 is disabled
2026-05-04T12:08:31,344 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #59
2026-05-04T12:08:31,344 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:31,352 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-04T12:08:31,353 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #9
2026-05-04T12:08:31,353 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:31,402 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #9. Is it enabled?
2026-05-04T12:08:31,411 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #9 is disabled
2026-05-04T12:08:31,413 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #0
2026-05-04T12:08:31,413 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:31,494 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #0. Is it enabled?
2026-05-04T12:08:31,527 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #0 is disabled
2026-05-04T12:08:31,531 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #52
2026-05-04T12:08:31,531 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:31,716 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #52. Is it enabled?
2026-05-04T12:08:31,771 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #52 is disabled
2026-05-04T12:08:31,777 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #69
2026-05-04T12:08:31,778 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:31,868 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #69. Is it enabled?
2026-05-04T12:08:31,888 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #69 is disabled
2026-05-04T12:08:31,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #64
2026-05-04T12:08:31,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:31,976 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #64. Is it enabled?
2026-05-04T12:08:31,997 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #64 is disabled
2026-05-04T12:08:32,002 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #4
2026-05-04T12:08:32,002 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:32,011 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-05-04T12:08:32,012 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #58
2026-05-04T12:08:32,012 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:32,065 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #58. Is it enabled?
2026-05-04T12:08:32,079 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #58 is disabled
2026-05-04T12:08:32,083 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #30
2026-05-04T12:08:32,083 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:32,266 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #30. Is it enabled?
2026-05-04T12:08:34,002 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #30 is enabled
2026-05-04T12:08:34,010 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: randomly picked transition #30
2026-05-04T12:08:34,010 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 5: picking a transition out of 1 transition(s)
2026-05-04T12:08:34,011 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #30
2026-05-04T12:08:34,011 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:34,141 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #30. Is it enabled?
2026-05-04T12:08:36,642 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #30 is enabled
2026-05-04T12:08:36,656 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: randomly picked transition #30
2026-05-04T12:08:36,656 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 6: picking a transition out of 1 transition(s)
2026-05-04T12:08:36,657 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #6
2026-05-04T12:08:36,657 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:36,729 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #6. Is it enabled?
2026-05-04T12:08:36,742 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #6 is disabled
2026-05-04T12:08:36,747 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #2
2026-05-04T12:08:36,747 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:36,883 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #2. Is it enabled?
2026-05-04T12:08:36,904 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #2 is disabled
2026-05-04T12:08:36,909 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #57
2026-05-04T12:08:36,909 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:36,915 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-05-04T12:08:36,916 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #60
2026-05-04T12:08:36,916 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:36,956 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #60. Is it enabled?
2026-05-04T12:08:36,964 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #60 is disabled
2026-05-04T12:08:36,966 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #31
2026-05-04T12:08:36,966 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:37,090 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #31. Is it enabled?
2026-05-04T12:08:37,499 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #31 is disabled
2026-05-04T12:08:37,511 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #65
2026-05-04T12:08:37,511 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:37,532 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #65. Is it enabled?
2026-05-04T12:08:37,535 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #65 is disabled
2026-05-04T12:08:37,537 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #16
2026-05-04T12:08:37,537 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:37,587 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #16. Is it enabled?
2026-05-04T12:08:40,456 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #16 is enabled
2026-05-04T12:08:40,457 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: Checking 2 state invariants
2026-05-04T12:08:40,457 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 7: Checking state invariant 0
2026-05-04T12:08:40,769 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: state invariant 0 holds.
2026-05-04T12:08:40,772 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 7: Checking state invariant 1
2026-05-04T12:08:41,290 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: state invariant 1 holds.
2026-05-04T12:08:41,299 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: randomly picked transition #16
2026-05-04T12:08:41,299 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 7: picking a transition out of 1 transition(s)
2026-05-04T12:08:41,300 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #29
2026-05-04T12:08:41,300 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:41,424 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #29. Is it enabled?
2026-05-04T12:08:42,037 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #29 is disabled
2026-05-04T12:08:42,046 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #53
2026-05-04T12:08:42,046 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:42,190 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #53. Is it enabled?
2026-05-04T12:08:42,209 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #53 is disabled
2026-05-04T12:08:42,213 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #52
2026-05-04T12:08:42,214 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:42,743 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #52. Is it enabled?
2026-05-04T12:08:44,231 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #52 is disabled
2026-05-04T12:08:44,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #61
2026-05-04T12:08:44,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:44,266 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-04T12:08:44,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #51
2026-05-04T12:08:44,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:44,799 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #51. Is it enabled?
2026-05-04T12:08:45,667 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #51 is disabled
2026-05-04T12:08:45,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #68
2026-05-04T12:08:45,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:45,747 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #68. Is it enabled?
2026-05-04T12:08:45,759 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #68 is disabled
2026-05-04T12:08:45,763 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #37
2026-05-04T12:08:45,763 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:46,314 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #37. Is it enabled?
2026-05-04T12:08:47,869 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #37 is disabled
2026-05-04T12:08:47,886 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #67
2026-05-04T12:08:47,886 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:47,955 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #67. Is it enabled?
2026-05-04T12:08:47,968 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #67 is disabled
2026-05-04T12:08:47,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #27
2026-05-04T12:08:47,972 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:48,365 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #27. Is it enabled?
2026-05-04T12:08:48,411 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #27 is disabled
2026-05-04T12:08:48,420 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #42
2026-05-04T12:08:48,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:48,738 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:08:48,778 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #46
2026-05-04T12:08:48,778 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:49,050 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #46. Is it enabled?
2026-05-04T12:08:50,592 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #46 is disabled
2026-05-04T12:08:50,605 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #21
2026-05-04T12:08:50,605 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:51,079 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #21. Is it enabled?
2026-05-04T12:08:52,005 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #21 is disabled
2026-05-04T12:08:52,020 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #43
2026-05-04T12:08:52,020 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:52,269 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #43. Is it enabled?
2026-05-04T12:08:52,945 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #43 is disabled
2026-05-04T12:08:52,954 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #0
2026-05-04T12:08:52,954 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:53,051 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #0. Is it enabled?
2026-05-04T12:08:54,622 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #0 is enabled
2026-05-04T12:08:54,623 [main] INFO  a.f.a.t.b.SeqModelChecker - State 8: Checking 2 state invariants
2026-05-04T12:08:54,623 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 8: Checking state invariant 0
2026-05-04T12:08:55,536 [main] INFO  a.f.a.t.b.SeqModelChecker - State 8: state invariant 0 holds.
2026-05-04T12:08:55,541 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 8: Checking state invariant 1
2026-05-04T12:08:56,165 [main] INFO  a.f.a.t.b.SeqModelChecker - State 8: state invariant 1 holds.
2026-05-04T12:08:56,178 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: randomly picked transition #0
2026-05-04T12:08:56,178 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 8: picking a transition out of 1 transition(s)
2026-05-04T12:08:56,179 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #45
2026-05-04T12:08:56,179 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:56,542 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #45. Is it enabled?
2026-05-04T12:08:58,520 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #45 is disabled
2026-05-04T12:08:58,534 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #32
2026-05-04T12:08:58,534 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:08:58,669 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #32. Is it enabled?
2026-05-04T12:09:00,448 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #32 is disabled
2026-05-04T12:09:00,462 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #14
2026-05-04T12:09:00,462 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:00,638 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #14. Is it enabled?
2026-05-04T12:09:03,358 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #14 is disabled
2026-05-04T12:09:03,376 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #28
2026-05-04T12:09:03,376 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:03,511 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #28. Is it enabled?
2026-05-04T12:09:05,206 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #28 is disabled
2026-05-04T12:09:05,222 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #65
2026-05-04T12:09:05,223 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:05,247 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #65. Is it enabled?
2026-05-04T12:09:05,251 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #65 is disabled
2026-05-04T12:09:05,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #41
2026-05-04T12:09:05,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:05,556 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #41. Is it enabled?
2026-05-04T12:09:06,566 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #41 is disabled
2026-05-04T12:09:06,577 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #30
2026-05-04T12:09:06,578 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:06,707 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #30. Is it enabled?
2026-05-04T12:09:10,070 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #30 is enabled
2026-05-04T12:09:10,092 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: randomly picked transition #30
2026-05-04T12:09:10,092 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 9: picking a transition out of 1 transition(s)
2026-05-04T12:09:10,094 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #42
2026-05-04T12:09:10,094 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:10,401 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:09:10,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #17
2026-05-04T12:09:10,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:10,654 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #17. Is it enabled?
2026-05-04T12:09:12,129 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #17 is enabled
2026-05-04T12:09:12,129 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: Checking 2 state invariants
2026-05-04T12:09:12,129 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 10: Checking state invariant 0
2026-05-04T12:09:14,615 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: state invariant 0 holds.
2026-05-04T12:09:14,623 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 10: Checking state invariant 1
2026-05-04T12:09:19,265 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: state invariant 1 holds.
2026-05-04T12:09:19,286 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: randomly picked transition #17
2026-05-04T12:09:19,286 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 10: picking a transition out of 1 transition(s)
2026-05-04T12:09:19,376 [main] INFO  a.f.a.t.b.SeqModelChecker - ----------------------------
2026-05-04T12:09:19,376 [main] INFO  a.f.a.t.b.SeqModelChecker - Symbolic runs left: 99
2026-05-04T12:09:19,376 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #0, transition #0
2026-05-04T12:09:19,376 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:19,386 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0. Is it enabled?
2026-05-04T12:09:19,390 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0 is enabled
2026-05-04T12:09:19,390 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: Checking 2 state invariants
2026-05-04T12:09:19,390 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 0
2026-05-04T12:09:19,401 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 0 holds.
2026-05-04T12:09:19,402 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 1
2026-05-04T12:09:19,415 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 1 holds.
2026-05-04T12:09:19,415 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 0: randomly picked transition #0
2026-05-04T12:09:19,416 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 0: picking a transition out of 1 transition(s)
2026-05-04T12:09:19,416 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #28
2026-05-04T12:09:19,416 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:19,492 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #28. Is it enabled?
2026-05-04T12:09:19,504 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #28 is disabled
2026-05-04T12:09:19,506 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #15
2026-05-04T12:09:19,506 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:19,507 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #15. Is it enabled?
2026-05-04T12:09:19,508 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #15 is disabled
2026-05-04T12:09:19,508 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #5
2026-05-04T12:09:19,508 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:19,508 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #5. Is it enabled?
2026-05-04T12:09:19,508 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #5 is disabled
2026-05-04T12:09:19,509 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #50
2026-05-04T12:09:19,509 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:19,526 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #50. Is it enabled?
2026-05-04T12:09:19,529 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #50 is disabled
2026-05-04T12:09:19,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #16
2026-05-04T12:09:19,529 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:19,563 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16. Is it enabled?
2026-05-04T12:09:19,573 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16 is enabled
2026-05-04T12:09:19,573 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: Checking 2 state invariants
2026-05-04T12:09:19,573 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 0
2026-05-04T12:09:19,592 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 0 holds.
2026-05-04T12:09:19,593 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 1
2026-05-04T12:09:19,621 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 1 holds.
2026-05-04T12:09:19,626 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: randomly picked transition #16
2026-05-04T12:09:19,627 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 1: picking a transition out of 1 transition(s)
2026-05-04T12:09:19,628 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #34
2026-05-04T12:09:19,629 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:19,770 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #34. Is it enabled?
2026-05-04T12:09:19,835 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #34 is disabled
2026-05-04T12:09:19,840 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #15
2026-05-04T12:09:19,840 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:19,949 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #15. Is it enabled?
2026-05-04T12:09:19,987 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #15 is disabled
2026-05-04T12:09:19,991 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #65
2026-05-04T12:09:19,992 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,005 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #65. Is it enabled?
2026-05-04T12:09:20,007 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #65 is disabled
2026-05-04T12:09:20,007 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #47
2026-05-04T12:09:20,007 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,092 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #47. Is it enabled?
2026-05-04T12:09:20,107 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #47 is disabled
2026-05-04T12:09:20,110 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #31
2026-05-04T12:09:20,110 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,222 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #31. Is it enabled?
2026-05-04T12:09:20,268 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #31 is disabled
2026-05-04T12:09:20,272 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #33
2026-05-04T12:09:20,272 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,395 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #33. Is it enabled?
2026-05-04T12:09:20,481 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #33 is disabled
2026-05-04T12:09:20,486 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #20
2026-05-04T12:09:20,486 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,502 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-05-04T12:09:20,504 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #13
2026-05-04T12:09:20,504 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,700 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #13. Is it enabled?
2026-05-04T12:09:20,722 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #13 is disabled
2026-05-04T12:09:20,725 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #66
2026-05-04T12:09:20,725 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,793 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #66. Is it enabled?
2026-05-04T12:09:20,808 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #66 is disabled
2026-05-04T12:09:20,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #39
2026-05-04T12:09:20,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,865 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #39. Is it enabled?
2026-05-04T12:09:20,875 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #39 is disabled
2026-05-04T12:09:20,877 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #7
2026-05-04T12:09:20,877 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,880 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-04T12:09:20,880 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #63
2026-05-04T12:09:20,880 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,920 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #63. Is it enabled?
2026-05-04T12:09:20,927 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #63 is disabled
2026-05-04T12:09:20,929 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #24
2026-05-04T12:09:20,929 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:20,995 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #24. Is it enabled?
2026-05-04T12:09:21,004 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #24 is disabled
2026-05-04T12:09:21,006 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #0
2026-05-04T12:09:21,006 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:21,078 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0. Is it enabled?
2026-05-04T12:09:21,112 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0 is enabled
2026-05-04T12:09:21,112 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: Checking 2 state invariants
2026-05-04T12:09:21,112 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 0
2026-05-04T12:09:21,157 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 0 holds.
2026-05-04T12:09:21,158 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 1
2026-05-04T12:09:21,206 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 1 holds.
2026-05-04T12:09:21,208 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: randomly picked transition #0
2026-05-04T12:09:21,209 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 2: picking a transition out of 1 transition(s)
2026-05-04T12:09:21,209 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #59
2026-05-04T12:09:21,209 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:21,215 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-04T12:09:21,216 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #1
2026-05-04T12:09:21,216 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:21,256 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #1. Is it enabled?
2026-05-04T12:09:21,264 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #1 is disabled
2026-05-04T12:09:21,265 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #17
2026-05-04T12:09:21,265 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:21,312 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #17. Is it enabled?
2026-05-04T12:09:21,358 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #17 is enabled
2026-05-04T12:09:21,359 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 2 state invariants
2026-05-04T12:09:21,359 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-05-04T12:09:21,439 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-05-04T12:09:21,441 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 1
2026-05-04T12:09:21,527 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 1 holds.
2026-05-04T12:09:21,531 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: randomly picked transition #17
2026-05-04T12:09:21,531 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 3: picking a transition out of 1 transition(s)
2026-05-04T12:09:21,532 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #52
2026-05-04T12:09:21,532 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:21,785 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #52. Is it enabled?
2026-05-04T12:09:21,812 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #52 is disabled
2026-05-04T12:09:21,818 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #5
2026-05-04T12:09:21,818 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:21,865 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #5. Is it enabled?
2026-05-04T12:09:21,875 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #5 is disabled
2026-05-04T12:09:21,877 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #68
2026-05-04T12:09:21,878 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:21,926 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #68. Is it enabled?
2026-05-04T12:09:21,935 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #68 is disabled
2026-05-04T12:09:21,937 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #34
2026-05-04T12:09:21,937 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,087 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #34. Is it enabled?
2026-05-04T12:09:22,270 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #34 is disabled
2026-05-04T12:09:22,277 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #51
2026-05-04T12:09:22,277 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,450 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #51. Is it enabled?
2026-05-04T12:09:22,477 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #51 is disabled
2026-05-04T12:09:22,481 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #15
2026-05-04T12:09:22,481 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,608 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #15. Is it enabled?
2026-05-04T12:09:22,638 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #15 is disabled
2026-05-04T12:09:22,642 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #8
2026-05-04T12:09:22,643 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,650 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-04T12:09:22,651 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #18
2026-05-04T12:09:22,651 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,719 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-05-04T12:09:22,726 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #20
2026-05-04T12:09:22,727 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,828 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-05-04T12:09:22,831 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #61
2026-05-04T12:09:22,832 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,837 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-04T12:09:22,837 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #10
2026-05-04T12:09:22,837 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,881 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #10. Is it enabled?
2026-05-04T12:09:22,889 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #10 is disabled
2026-05-04T12:09:22,890 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #60
2026-05-04T12:09:22,891 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,925 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #60. Is it enabled?
2026-05-04T12:09:22,930 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #60 is disabled
2026-05-04T12:09:22,932 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #58
2026-05-04T12:09:22,932 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:22,982 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #58. Is it enabled?
2026-05-04T12:09:22,992 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #58 is disabled
2026-05-04T12:09:22,994 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #2
2026-05-04T12:09:22,994 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:23,054 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #2. Is it enabled?
2026-05-04T12:09:23,065 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #2 is disabled
2026-05-04T12:09:23,067 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #29
2026-05-04T12:09:23,067 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:23,188 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #29. Is it enabled?
2026-05-04T12:09:23,385 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #29 is disabled
2026-05-04T12:09:23,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #42
2026-05-04T12:09:23,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:23,432 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:09:23,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #64
2026-05-04T12:09:23,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:23,510 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #64. Is it enabled?
2026-05-04T12:09:23,527 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #64 is disabled
2026-05-04T12:09:23,530 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #30
2026-05-04T12:09:23,531 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:23,665 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #30. Is it enabled?
2026-05-04T12:09:24,261 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #30 is enabled
2026-05-04T12:09:24,266 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: randomly picked transition #30
2026-05-04T12:09:24,267 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 4: picking a transition out of 1 transition(s)
2026-05-04T12:09:24,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #19
2026-05-04T12:09:24,267 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:24,349 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-05-04T12:09:24,359 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #10
2026-05-04T12:09:24,359 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:24,482 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #10. Is it enabled?
2026-05-04T12:09:24,492 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #10 is disabled
2026-05-04T12:09:24,495 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #1
2026-05-04T12:09:24,495 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:24,569 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #1. Is it enabled?
2026-05-04T12:09:24,584 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #1 is disabled
2026-05-04T12:09:24,587 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #33
2026-05-04T12:09:24,587 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:24,720 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #33. Is it enabled?
2026-05-04T12:09:25,105 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #33 is disabled
2026-05-04T12:09:25,113 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #12
2026-05-04T12:09:25,113 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:25,264 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #12. Is it enabled?
2026-05-04T12:09:25,743 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #12 is disabled
2026-05-04T12:09:25,753 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #18
2026-05-04T12:09:25,753 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:25,783 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-05-04T12:09:25,787 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #59
2026-05-04T12:09:25,787 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:25,792 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-04T12:09:25,793 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #39
2026-05-04T12:09:25,793 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:25,939 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #39. Is it enabled?
2026-05-04T12:09:25,960 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #39 is disabled
2026-05-04T12:09:25,964 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #5
2026-05-04T12:09:25,964 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:26,101 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #5. Is it enabled?
2026-05-04T12:09:26,113 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #5 is disabled
2026-05-04T12:09:26,116 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #65
2026-05-04T12:09:26,116 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:26,133 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #65. Is it enabled?
2026-05-04T12:09:26,136 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #65 is disabled
2026-05-04T12:09:26,137 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #63
2026-05-04T12:09:26,137 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:26,189 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #63. Is it enabled?
2026-05-04T12:09:26,200 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #63 is disabled
2026-05-04T12:09:26,203 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #31
2026-05-04T12:09:26,203 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:26,324 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #31. Is it enabled?
2026-05-04T12:09:26,634 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #31 is disabled
2026-05-04T12:09:26,642 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #58
2026-05-04T12:09:26,642 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:26,697 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #58. Is it enabled?
2026-05-04T12:09:26,707 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #58 is disabled
2026-05-04T12:09:26,710 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #54
2026-05-04T12:09:26,710 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:26,768 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #54. Is it enabled?
2026-05-04T12:09:26,778 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #54 is disabled
2026-05-04T12:09:26,781 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #51
2026-05-04T12:09:26,781 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:26,953 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #51. Is it enabled?
2026-05-04T12:09:27,110 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #51 is disabled
2026-05-04T12:09:27,116 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #48
2026-05-04T12:09:27,116 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:27,367 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #48. Is it enabled?
2026-05-04T12:09:27,425 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #48 is disabled
2026-05-04T12:09:27,432 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #21
2026-05-04T12:09:27,432 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:27,616 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #21. Is it enabled?
2026-05-04T12:09:27,686 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #21 is disabled
2026-05-04T12:09:27,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #44
2026-05-04T12:09:27,693 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:27,882 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #44. Is it enabled?
2026-05-04T12:09:27,910 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #44 is disabled
2026-05-04T12:09:27,915 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #66
2026-05-04T12:09:27,915 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:27,995 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #66. Is it enabled?
2026-05-04T12:09:28,016 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #66 is disabled
2026-05-04T12:09:28,019 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #64
2026-05-04T12:09:28,020 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:28,105 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #64. Is it enabled?
2026-05-04T12:09:28,127 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #64 is disabled
2026-05-04T12:09:28,131 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #52
2026-05-04T12:09:28,131 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:28,311 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #52. Is it enabled?
2026-05-04T12:09:28,430 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #52 is disabled
2026-05-04T12:09:28,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #9
2026-05-04T12:09:28,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:28,552 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #9. Is it enabled?
2026-05-04T12:09:28,564 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #9 is disabled
2026-05-04T12:09:28,567 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #53
2026-05-04T12:09:28,567 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:28,646 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #53. Is it enabled?
2026-05-04T12:09:28,666 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #53 is disabled
2026-05-04T12:09:28,669 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #24
2026-05-04T12:09:28,670 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:28,777 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #24. Is it enabled?
2026-05-04T12:09:28,798 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #24 is disabled
2026-05-04T12:09:28,802 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #7
2026-05-04T12:09:28,802 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:28,815 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-04T12:09:28,817 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #25
2026-05-04T12:09:28,817 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:28,843 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-04T12:09:28,847 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #34
2026-05-04T12:09:28,847 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:28,979 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #34. Is it enabled?
2026-05-04T12:09:29,352 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #34 is disabled
2026-05-04T12:09:29,360 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #32
2026-05-04T12:09:29,361 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:29,491 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #32. Is it enabled?
2026-05-04T12:09:29,766 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #32 is disabled
2026-05-04T12:09:29,775 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #13
2026-05-04T12:09:29,775 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:29,988 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #13. Is it enabled?
2026-05-04T12:09:32,151 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #13 is enabled
2026-05-04T12:09:32,164 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: randomly picked transition #13
2026-05-04T12:09:32,164 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 5: picking a transition out of 1 transition(s)
2026-05-04T12:09:32,166 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #24
2026-05-04T12:09:32,166 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:32,301 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #24. Is it enabled?
2026-05-04T12:09:32,322 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #24 is disabled
2026-05-04T12:09:32,326 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #16
2026-05-04T12:09:32,326 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:32,376 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #16. Is it enabled?
2026-05-04T12:09:35,854 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #16 is enabled
2026-05-04T12:09:35,854 [main] INFO  a.f.a.t.b.SeqModelChecker - State 6: Checking 2 state invariants
2026-05-04T12:09:35,854 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 6: Checking state invariant 0
2026-05-04T12:09:36,428 [main] INFO  a.f.a.t.b.SeqModelChecker - State 6: state invariant 0 holds.
2026-05-04T12:09:36,431 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 6: Checking state invariant 1
2026-05-04T12:09:36,829 [main] INFO  a.f.a.t.b.SeqModelChecker - State 6: state invariant 1 holds.
2026-05-04T12:09:36,839 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: randomly picked transition #16
2026-05-04T12:09:36,839 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 6: picking a transition out of 1 transition(s)
2026-05-04T12:09:36,841 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #52
2026-05-04T12:09:36,841 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:37,268 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #52. Is it enabled?
2026-05-04T12:09:38,386 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #52 is disabled
2026-05-04T12:09:38,409 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #55
2026-05-04T12:09:38,409 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:38,421 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-04T12:09:38,422 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #69
2026-05-04T12:09:38,422 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:38,514 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #69. Is it enabled?
2026-05-04T12:09:38,532 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #69 is disabled
2026-05-04T12:09:38,536 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #11
2026-05-04T12:09:38,536 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:38,596 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #11. Is it enabled?
2026-05-04T12:09:39,092 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #11 is disabled
2026-05-04T12:09:39,104 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #43
2026-05-04T12:09:39,105 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:39,454 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #43. Is it enabled?
2026-05-04T12:09:40,374 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #43 is disabled
2026-05-04T12:09:40,390 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #37
2026-05-04T12:09:40,390 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:40,758 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #37. Is it enabled?
2026-05-04T12:09:41,212 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #37 is disabled
2026-05-04T12:09:41,223 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #28
2026-05-04T12:09:41,223 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:41,353 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #28. Is it enabled?
2026-05-04T12:09:43,263 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #28 is disabled
2026-05-04T12:09:43,276 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #65
2026-05-04T12:09:43,276 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:43,300 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #65. Is it enabled?
2026-05-04T12:09:43,303 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #65 is disabled
2026-05-04T12:09:43,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #66
2026-05-04T12:09:43,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:43,383 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #66. Is it enabled?
2026-05-04T12:09:43,398 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #66 is disabled
2026-05-04T12:09:43,402 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #64
2026-05-04T12:09:43,402 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:43,488 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #64. Is it enabled?
2026-05-04T12:09:43,516 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #64 is disabled
2026-05-04T12:09:43,523 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #63
2026-05-04T12:09:43,523 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:43,579 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #63. Is it enabled?
2026-05-04T12:09:43,591 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #63 is disabled
2026-05-04T12:09:43,594 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #12
2026-05-04T12:09:43,594 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:43,761 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #12. Is it enabled?
2026-05-04T12:09:45,523 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #12 is disabled
2026-05-04T12:09:45,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #2
2026-05-04T12:09:45,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:45,637 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #2. Is it enabled?
2026-05-04T12:09:45,655 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #2 is disabled
2026-05-04T12:09:45,659 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #38
2026-05-04T12:09:45,659 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:45,906 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-04T12:09:45,934 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #36
2026-05-04T12:09:45,934 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:46,020 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-04T12:09:46,035 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #16
2026-05-04T12:09:46,035 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:46,088 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #16. Is it enabled?
2026-05-04T12:09:46,115 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #16 is disabled
2026-05-04T12:09:46,122 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #21
2026-05-04T12:09:46,123 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:46,456 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #21. Is it enabled?
2026-05-04T12:09:46,959 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #21 is disabled
2026-05-04T12:09:46,973 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #17
2026-05-04T12:09:46,973 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:47,111 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #17. Is it enabled?
2026-05-04T12:09:47,384 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #17 is disabled
2026-05-04T12:09:47,390 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #68
2026-05-04T12:09:47,390 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:47,454 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #68. Is it enabled?
2026-05-04T12:09:47,467 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #68 is disabled
2026-05-04T12:09:47,470 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #24
2026-05-04T12:09:47,470 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:47,650 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #24. Is it enabled?
2026-05-04T12:09:47,678 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #24 is disabled
2026-05-04T12:09:47,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #47
2026-05-04T12:09:47,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:47,933 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #47. Is it enabled?
2026-05-04T12:09:48,940 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #47 is disabled
2026-05-04T12:09:48,955 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #30
2026-05-04T12:09:48,955 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:49,095 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #30. Is it enabled?
2026-05-04T12:09:51,847 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #30 is enabled
2026-05-04T12:09:51,862 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: randomly picked transition #30
2026-05-04T12:09:51,862 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 7: picking a transition out of 1 transition(s)
2026-05-04T12:09:51,863 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #42
2026-05-04T12:09:51,864 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:52,139 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:09:52,166 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #8
2026-05-04T12:09:52,166 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:52,184 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-04T12:09:52,187 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #1
2026-05-04T12:09:52,187 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:52,288 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #1. Is it enabled?
2026-05-04T12:09:52,309 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #1 is disabled
2026-05-04T12:09:52,322 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #45
2026-05-04T12:09:52,322 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:52,686 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #45. Is it enabled?
2026-05-04T12:09:54,369 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #45 is disabled
2026-05-04T12:09:54,383 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #55
2026-05-04T12:09:54,383 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:54,394 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-04T12:09:54,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #68
2026-05-04T12:09:54,395 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:54,457 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #68. Is it enabled?
2026-05-04T12:09:54,468 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #68 is disabled
2026-05-04T12:09:54,471 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #12
2026-05-04T12:09:54,471 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:54,743 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #12. Is it enabled?
2026-05-04T12:09:56,245 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #12 is disabled
2026-05-04T12:09:56,259 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #52
2026-05-04T12:09:56,259 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:56,603 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #52. Is it enabled?
2026-05-04T12:09:58,009 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #52 is disabled
2026-05-04T12:09:58,029 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #34
2026-05-04T12:09:58,029 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:58,167 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #34. Is it enabled?
2026-05-04T12:09:59,207 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #34 is disabled
2026-05-04T12:09:59,220 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #30
2026-05-04T12:09:59,220 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:09:59,408 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #30. Is it enabled?
2026-05-04T12:10:02,474 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #30 is enabled
2026-05-04T12:10:02,492 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: randomly picked transition #30
2026-05-04T12:10:02,492 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 8: picking a transition out of 1 transition(s)
2026-05-04T12:10:02,494 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #54
2026-05-04T12:10:02,494 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:02,560 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #54. Is it enabled?
2026-05-04T12:10:02,572 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #54 is disabled
2026-05-04T12:10:02,576 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #35
2026-05-04T12:10:02,576 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:02,702 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #35. Is it enabled?
2026-05-04T12:10:04,196 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #35 is disabled
2026-05-04T12:10:04,212 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #36
2026-05-04T12:10:04,212 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:04,462 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-04T12:10:04,491 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #69
2026-05-04T12:10:04,491 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:04,659 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #69. Is it enabled?
2026-05-04T12:10:04,680 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #69 is disabled
2026-05-04T12:10:04,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #7
2026-05-04T12:10:04,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:04,709 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-04T12:10:04,721 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #15
2026-05-04T12:10:04,721 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:04,915 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #15. Is it enabled?
2026-05-04T12:10:11,761 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #15 is enabled
2026-05-04T12:10:11,761 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: Checking 2 state invariants
2026-05-04T12:10:11,761 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 9: Checking state invariant 0
2026-05-04T12:10:13,101 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: state invariant 0 holds.
2026-05-04T12:10:13,108 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 9: Checking state invariant 1
2026-05-04T12:10:14,462 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: state invariant 1 holds.
2026-05-04T12:10:14,475 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: randomly picked transition #15
2026-05-04T12:10:14,476 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 9: picking a transition out of 1 transition(s)
2026-05-04T12:10:14,477 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #56
2026-05-04T12:10:14,477 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:14,541 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #56. Is it enabled?
2026-05-04T12:10:14,553 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #56 is disabled
2026-05-04T12:10:14,558 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #37
2026-05-04T12:10:14,558 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:14,942 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #37. Is it enabled?
2026-05-04T12:10:16,192 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #37 is disabled
2026-05-04T12:10:16,205 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #53
2026-05-04T12:10:16,205 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:16,287 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #53. Is it enabled?
2026-05-04T12:10:16,303 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #53 is disabled
2026-05-04T12:10:16,309 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #27
2026-05-04T12:10:16,309 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:16,576 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #27. Is it enabled?
2026-05-04T12:10:16,613 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #27 is disabled
2026-05-04T12:10:16,620 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #16
2026-05-04T12:10:16,621 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:16,677 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #16. Is it enabled?
2026-05-04T12:10:16,698 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #16 is disabled
2026-05-04T12:10:16,704 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #11
2026-05-04T12:10:16,704 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:16,792 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #11. Is it enabled?
2026-05-04T12:10:18,273 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #11 is disabled
2026-05-04T12:10:18,286 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #33
2026-05-04T12:10:18,286 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:18,453 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #33. Is it enabled?
2026-05-04T12:10:21,164 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #33 is disabled
2026-05-04T12:10:21,185 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #57
2026-05-04T12:10:21,185 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:21,194 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-05-04T12:10:21,196 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #45
2026-05-04T12:10:21,196 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:21,570 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #45. Is it enabled?
2026-05-04T12:10:31,844 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #45 is disabled
2026-05-04T12:10:31,867 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #15
2026-05-04T12:10:31,867 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:32,074 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #15. Is it enabled?
2026-05-04T12:10:34,919 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #15 is enabled
2026-05-04T12:10:34,920 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: Checking 2 state invariants
2026-05-04T12:10:34,925 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 10: Checking state invariant 0
2026-05-04T12:10:38,138 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: state invariant 0 holds.
2026-05-04T12:10:38,148 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 10: Checking state invariant 1
2026-05-04T12:10:39,304 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: state invariant 1 holds.
2026-05-04T12:10:39,321 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: randomly picked transition #15
2026-05-04T12:10:39,321 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 10: picking a transition out of 1 transition(s)
2026-05-04T12:10:39,427 [main] INFO  a.f.a.t.b.SeqModelChecker - ----------------------------
2026-05-04T12:10:39,427 [main] INFO  a.f.a.t.b.SeqModelChecker - Symbolic runs left: 98
2026-05-04T12:10:39,427 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #0, transition #0
2026-05-04T12:10:39,427 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,437 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0. Is it enabled?
2026-05-04T12:10:39,441 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0 is enabled
2026-05-04T12:10:39,442 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: Checking 2 state invariants
2026-05-04T12:10:39,442 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 0
2026-05-04T12:10:39,453 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 0 holds.
2026-05-04T12:10:39,454 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 1
2026-05-04T12:10:39,467 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 1 holds.
2026-05-04T12:10:39,468 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 0: randomly picked transition #0
2026-05-04T12:10:39,468 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 0: picking a transition out of 1 transition(s)
2026-05-04T12:10:39,468 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #31
2026-05-04T12:10:39,468 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,545 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #31. Is it enabled?
2026-05-04T12:10:39,563 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #31 is disabled
2026-05-04T12:10:39,566 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #18
2026-05-04T12:10:39,567 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,571 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-05-04T12:10:39,571 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #17
2026-05-04T12:10:39,571 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,592 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #17. Is it enabled?
2026-05-04T12:10:39,595 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #17 is disabled
2026-05-04T12:10:39,596 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #69
2026-05-04T12:10:39,596 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,602 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #69. Is it enabled?
2026-05-04T12:10:39,603 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #69 is disabled
2026-05-04T12:10:39,604 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #29
2026-05-04T12:10:39,604 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,680 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #29. Is it enabled?
2026-05-04T12:10:39,694 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #29 is disabled
2026-05-04T12:10:39,697 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #11
2026-05-04T12:10:39,697 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,697 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #11. Is it enabled?
2026-05-04T12:10:39,698 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #11 is disabled
2026-05-04T12:10:39,698 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #36
2026-05-04T12:10:39,698 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,700 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-04T12:10:39,700 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #38
2026-05-04T12:10:39,700 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,701 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-04T12:10:39,702 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #33
2026-05-04T12:10:39,702 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,780 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #33. Is it enabled?
2026-05-04T12:10:39,796 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #33 is disabled
2026-05-04T12:10:39,799 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #65
2026-05-04T12:10:39,799 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,806 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #65. Is it enabled?
2026-05-04T12:10:39,807 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #65 is disabled
2026-05-04T12:10:39,808 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #54
2026-05-04T12:10:39,808 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,848 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #54. Is it enabled?
2026-05-04T12:10:39,854 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #54 is disabled
2026-05-04T12:10:39,855 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #67
2026-05-04T12:10:39,855 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,896 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #67. Is it enabled?
2026-05-04T12:10:39,902 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #67 is disabled
2026-05-04T12:10:39,904 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #62
2026-05-04T12:10:39,904 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,911 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #62. Is it enabled?
2026-05-04T12:10:39,912 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #62 is disabled
2026-05-04T12:10:39,913 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #68
2026-05-04T12:10:39,913 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:39,919 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #68. Is it enabled?
2026-05-04T12:10:39,920 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #68 is disabled
2026-05-04T12:10:39,921 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #34
2026-05-04T12:10:39,921 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,078 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #34. Is it enabled?
2026-05-04T12:10:40,092 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #34 is disabled
2026-05-04T12:10:40,095 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #53
2026-05-04T12:10:40,095 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,141 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #53. Is it enabled?
2026-05-04T12:10:40,148 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #53 is disabled
2026-05-04T12:10:40,150 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #4
2026-05-04T12:10:40,150 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,150 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-05-04T12:10:40,150 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #21
2026-05-04T12:10:40,150 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,178 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #21. Is it enabled?
2026-05-04T12:10:40,182 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #21 is disabled
2026-05-04T12:10:40,183 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #61
2026-05-04T12:10:40,183 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,188 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-04T12:10:40,188 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #15
2026-05-04T12:10:40,188 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,189 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #15. Is it enabled?
2026-05-04T12:10:40,189 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #15 is disabled
2026-05-04T12:10:40,189 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #45
2026-05-04T12:10:40,189 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,235 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #45. Is it enabled?
2026-05-04T12:10:40,248 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #45 is disabled
2026-05-04T12:10:40,250 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #0
2026-05-04T12:10:40,250 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,251 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #0. Is it enabled?
2026-05-04T12:10:40,251 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #0 is disabled
2026-05-04T12:10:40,251 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #42
2026-05-04T12:10:40,251 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:10:40,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #24
2026-05-04T12:10:40,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,283 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #24. Is it enabled?
2026-05-04T12:10:40,287 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #24 is disabled
2026-05-04T12:10:40,288 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #35
2026-05-04T12:10:40,288 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,368 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #35. Is it enabled?
2026-05-04T12:10:40,387 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #35 is disabled
2026-05-04T12:10:40,390 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #6
2026-05-04T12:10:40,390 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,391 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #6. Is it enabled?
2026-05-04T12:10:40,391 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #6 is disabled
2026-05-04T12:10:40,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #47
2026-05-04T12:10:40,392 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,440 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #47. Is it enabled?
2026-05-04T12:10:40,448 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #47 is disabled
2026-05-04T12:10:40,450 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #49
2026-05-04T12:10:40,450 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,498 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #49. Is it enabled?
2026-05-04T12:10:40,504 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #49 is disabled
2026-05-04T12:10:40,505 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #57
2026-05-04T12:10:40,505 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,510 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-05-04T12:10:40,510 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #52
2026-05-04T12:10:40,510 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,558 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #52. Is it enabled?
2026-05-04T12:10:40,564 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #52 is disabled
2026-05-04T12:10:40,566 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #23
2026-05-04T12:10:40,566 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,568 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-05-04T12:10:40,568 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #30
2026-05-04T12:10:40,568 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,647 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #30. Is it enabled?
2026-05-04T12:10:40,664 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #30 is disabled
2026-05-04T12:10:40,667 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #1
2026-05-04T12:10:40,667 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,668 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #1. Is it enabled?
2026-05-04T12:10:40,668 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #1 is disabled
2026-05-04T12:10:40,669 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #56
2026-05-04T12:10:40,669 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,676 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #56. Is it enabled?
2026-05-04T12:10:40,677 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #56 is disabled
2026-05-04T12:10:40,677 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #55
2026-05-04T12:10:40,677 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-04T12:10:40,683 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #19
2026-05-04T12:10:40,683 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,685 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-05-04T12:10:40,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #43
2026-05-04T12:10:40,686 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,708 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #43. Is it enabled?
2026-05-04T12:10:40,711 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #43 is disabled
2026-05-04T12:10:40,712 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #26
2026-05-04T12:10:40,712 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,742 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #26. Is it enabled?
2026-05-04T12:10:40,746 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #26 is disabled
2026-05-04T12:10:40,747 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #25
2026-05-04T12:10:40,747 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,749 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-04T12:10:40,749 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #3
2026-05-04T12:10:40,749 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,749 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-04T12:10:40,749 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #59
2026-05-04T12:10:40,749 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,754 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-04T12:10:40,754 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #51
2026-05-04T12:10:40,754 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,798 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #51. Is it enabled?
2026-05-04T12:10:40,804 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #51 is disabled
2026-05-04T12:10:40,806 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #20
2026-05-04T12:10:40,806 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,809 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-05-04T12:10:40,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #40
2026-05-04T12:10:40,810 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,811 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-05-04T12:10:40,811 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #5
2026-05-04T12:10:40,811 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,812 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #5. Is it enabled?
2026-05-04T12:10:40,812 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #5 is disabled
2026-05-04T12:10:40,813 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #39
2026-05-04T12:10:40,813 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,849 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #39. Is it enabled?
2026-05-04T12:10:40,855 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #39 is disabled
2026-05-04T12:10:40,857 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #46
2026-05-04T12:10:40,857 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,902 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #46. Is it enabled?
2026-05-04T12:10:40,909 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #46 is disabled
2026-05-04T12:10:40,910 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #58
2026-05-04T12:10:40,910 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,917 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #58. Is it enabled?
2026-05-04T12:10:40,918 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #58 is disabled
2026-05-04T12:10:40,919 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #14
2026-05-04T12:10:40,919 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,920 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #14. Is it enabled?
2026-05-04T12:10:40,920 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #14 is disabled
2026-05-04T12:10:40,920 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #27
2026-05-04T12:10:40,920 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,931 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #27. Is it enabled?
2026-05-04T12:10:40,932 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #27 is disabled
2026-05-04T12:10:40,933 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #13
2026-05-04T12:10:40,933 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,934 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #13. Is it enabled?
2026-05-04T12:10:40,934 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #13 is disabled
2026-05-04T12:10:40,935 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #63
2026-05-04T12:10:40,935 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,941 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #63. Is it enabled?
2026-05-04T12:10:40,942 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #63 is disabled
2026-05-04T12:10:40,943 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #50
2026-05-04T12:10:40,943 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:40,962 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #50. Is it enabled?
2026-05-04T12:10:40,965 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #50 is disabled
2026-05-04T12:10:40,966 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #44
2026-05-04T12:10:40,966 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,002 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #44. Is it enabled?
2026-05-04T12:10:41,007 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #44 is disabled
2026-05-04T12:10:41,008 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #9
2026-05-04T12:10:41,008 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,009 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #9. Is it enabled?
2026-05-04T12:10:41,009 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #9 is disabled
2026-05-04T12:10:41,009 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #41
2026-05-04T12:10:41,009 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,031 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #41. Is it enabled?
2026-05-04T12:10:41,034 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #41 is disabled
2026-05-04T12:10:41,035 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #2
2026-05-04T12:10:41,035 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,035 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #2. Is it enabled?
2026-05-04T12:10:41,036 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #2 is disabled
2026-05-04T12:10:41,036 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #7
2026-05-04T12:10:41,036 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,036 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-04T12:10:41,036 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #48
2026-05-04T12:10:41,036 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,081 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #48. Is it enabled?
2026-05-04T12:10:41,088 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #48 is disabled
2026-05-04T12:10:41,090 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #10
2026-05-04T12:10:41,090 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,090 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #10. Is it enabled?
2026-05-04T12:10:41,091 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #10 is disabled
2026-05-04T12:10:41,091 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #32
2026-05-04T12:10:41,091 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,174 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #32. Is it enabled?
2026-05-04T12:10:41,195 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #32 is disabled
2026-05-04T12:10:41,199 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #37
2026-05-04T12:10:41,199 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,232 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #37. Is it enabled?
2026-05-04T12:10:41,238 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #37 is disabled
2026-05-04T12:10:41,240 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #28
2026-05-04T12:10:41,240 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,448 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #28. Is it enabled?
2026-05-04T12:10:41,464 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #28 is disabled
2026-05-04T12:10:41,467 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #60
2026-05-04T12:10:41,467 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,474 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #60. Is it enabled?
2026-05-04T12:10:41,475 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #60 is disabled
2026-05-04T12:10:41,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #8
2026-05-04T12:10:41,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-04T12:10:41,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #66
2026-05-04T12:10:41,476 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,528 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #66. Is it enabled?
2026-05-04T12:10:41,537 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #66 is disabled
2026-05-04T12:10:41,539 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #12
2026-05-04T12:10:41,539 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,539 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #12. Is it enabled?
2026-05-04T12:10:41,540 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #12 is disabled
2026-05-04T12:10:41,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #64
2026-05-04T12:10:41,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,546 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #64. Is it enabled?
2026-05-04T12:10:41,547 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #64 is disabled
2026-05-04T12:10:41,548 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #16
2026-05-04T12:10:41,548 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,602 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16. Is it enabled?
2026-05-04T12:10:41,621 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16 is enabled
2026-05-04T12:10:41,621 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: Checking 2 state invariants
2026-05-04T12:10:41,621 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 0
2026-05-04T12:10:41,646 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 0 holds.
2026-05-04T12:10:41,647 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 1
2026-05-04T12:10:41,679 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 1 holds.
2026-05-04T12:10:41,681 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: randomly picked transition #16
2026-05-04T12:10:41,681 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 1: picking a transition out of 1 transition(s)
2026-05-04T12:10:41,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #0
2026-05-04T12:10:41,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:41,729 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0. Is it enabled?
2026-05-04T12:10:41,809 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #0 is enabled
2026-05-04T12:10:41,809 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: Checking 2 state invariants
2026-05-04T12:10:41,809 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 0
2026-05-04T12:10:41,885 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 0 holds.
2026-05-04T12:10:41,886 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 2: Checking state invariant 1
2026-05-04T12:10:41,939 [main] INFO  a.f.a.t.b.SeqModelChecker - State 2: state invariant 1 holds.
2026-05-04T12:10:41,942 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: randomly picked transition #0
2026-05-04T12:10:41,942 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 2: picking a transition out of 1 transition(s)
2026-05-04T12:10:41,943 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #33
2026-05-04T12:10:41,943 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:42,060 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #33. Is it enabled?
2026-05-04T12:10:42,235 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #33 is disabled
2026-05-04T12:10:42,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #54
2026-05-04T12:10:42,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:42,292 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #54. Is it enabled?
2026-05-04T12:10:42,302 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #54 is disabled
2026-05-04T12:10:42,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #34
2026-05-04T12:10:42,305 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:42,428 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #34. Is it enabled?
2026-05-04T12:10:42,552 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #34 is disabled
2026-05-04T12:10:42,564 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #39
2026-05-04T12:10:42,564 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:42,722 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #39. Is it enabled?
2026-05-04T12:10:42,736 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #39 is disabled
2026-05-04T12:10:42,739 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #48
2026-05-04T12:10:42,739 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:42,839 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #48. Is it enabled?
2026-05-04T12:10:42,858 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #48 is disabled
2026-05-04T12:10:42,862 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #37
2026-05-04T12:10:42,862 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:42,933 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #37. Is it enabled?
2026-05-04T12:10:42,945 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #37 is disabled
2026-05-04T12:10:42,948 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #8
2026-05-04T12:10:42,948 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:42,951 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-04T12:10:42,952 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #9
2026-05-04T12:10:42,952 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,084 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #9. Is it enabled?
2026-05-04T12:10:43,089 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #9 is disabled
2026-05-04T12:10:43,091 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #19
2026-05-04T12:10:43,091 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,112 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-05-04T12:10:43,115 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #10
2026-05-04T12:10:43,115 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,143 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #10. Is it enabled?
2026-05-04T12:10:43,148 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #10 is disabled
2026-05-04T12:10:43,150 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #0
2026-05-04T12:10:43,150 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,201 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0. Is it enabled?
2026-05-04T12:10:43,266 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #0 is enabled
2026-05-04T12:10:43,266 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 2 state invariants
2026-05-04T12:10:43,266 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-05-04T12:10:43,397 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-05-04T12:10:43,399 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 1
2026-05-04T12:10:43,497 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 1 holds.
2026-05-04T12:10:43,500 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: randomly picked transition #0
2026-05-04T12:10:43,500 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 3: picking a transition out of 1 transition(s)
2026-05-04T12:10:43,501 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #20
2026-05-04T12:10:43,501 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,518 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 20 produces partial assignment. Disabled.
2026-05-04T12:10:43,521 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #63
2026-05-04T12:10:43,521 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,561 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #63. Is it enabled?
2026-05-04T12:10:43,574 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #63 is disabled
2026-05-04T12:10:43,579 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #37
2026-05-04T12:10:43,579 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,642 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #37. Is it enabled?
2026-05-04T12:10:43,654 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #37 is disabled
2026-05-04T12:10:43,657 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #43
2026-05-04T12:10:43,657 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,710 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #43. Is it enabled?
2026-05-04T12:10:43,718 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #43 is disabled
2026-05-04T12:10:43,720 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #0
2026-05-04T12:10:43,720 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,772 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #0. Is it enabled?
2026-05-04T12:10:43,790 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: Transition #0 is disabled
2026-05-04T12:10:43,793 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #17
2026-05-04T12:10:43,793 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:43,840 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #17. Is it enabled?
2026-05-04T12:10:43,935 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #17 is enabled
2026-05-04T12:10:43,935 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 2 state invariants
2026-05-04T12:10:43,935 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-05-04T12:10:44,084 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-05-04T12:10:44,087 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 1
2026-05-04T12:10:44,231 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 1 holds.
2026-05-04T12:10:44,235 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: randomly picked transition #17
2026-05-04T12:10:44,235 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 4: picking a transition out of 1 transition(s)
2026-05-04T12:10:44,236 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #11
2026-05-04T12:10:44,236 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:44,269 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #11. Is it enabled?
2026-05-04T12:10:44,427 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #11 is disabled
2026-05-04T12:10:44,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #56
2026-05-04T12:10:44,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:44,478 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #56. Is it enabled?
2026-05-04T12:10:44,487 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #56 is disabled
2026-05-04T12:10:44,490 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #51
2026-05-04T12:10:44,490 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:44,752 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #51. Is it enabled?
2026-05-04T12:10:44,785 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #51 is disabled
2026-05-04T12:10:44,791 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #0
2026-05-04T12:10:44,792 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:44,863 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #0. Is it enabled?
2026-05-04T12:10:44,890 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #0 is disabled
2026-05-04T12:10:44,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #37
2026-05-04T12:10:44,895 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:45,060 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #37. Is it enabled?
2026-05-04T12:10:45,085 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #37 is disabled
2026-05-04T12:10:45,090 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #50
2026-05-04T12:10:45,090 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:45,307 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #50. Is it enabled?
2026-05-04T12:10:45,330 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #50 is disabled
2026-05-04T12:10:45,335 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #61
2026-05-04T12:10:45,335 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:45,341 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-04T12:10:45,342 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #7
2026-05-04T12:10:45,342 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:45,350 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-04T12:10:45,351 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #48
2026-05-04T12:10:45,351 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:45,564 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #48. Is it enabled?
2026-05-04T12:10:45,595 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #48 is disabled
2026-05-04T12:10:45,600 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #46
2026-05-04T12:10:45,600 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:45,788 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #46. Is it enabled?
2026-05-04T12:10:45,816 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #46 is disabled
2026-05-04T12:10:45,821 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #63
2026-05-04T12:10:45,821 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:45,867 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #63. Is it enabled?
2026-05-04T12:10:45,875 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #63 is disabled
2026-05-04T12:10:45,877 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #14
2026-05-04T12:10:45,877 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:46,070 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #14. Is it enabled?
2026-05-04T12:10:46,113 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #14 is disabled
2026-05-04T12:10:46,118 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #27
2026-05-04T12:10:46,119 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:46,261 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #27. Is it enabled?
2026-05-04T12:10:46,278 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #27 is disabled
2026-05-04T12:10:46,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #19
2026-05-04T12:10:46,281 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:46,391 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-05-04T12:10:46,399 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #21
2026-05-04T12:10:46,399 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:46,528 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #21. Is it enabled?
2026-05-04T12:10:46,591 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #21 is disabled
2026-05-04T12:10:46,597 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #31
2026-05-04T12:10:46,597 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:46,718 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #31. Is it enabled?
2026-05-04T12:10:47,077 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #31 is disabled
2026-05-04T12:10:47,087 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #41
2026-05-04T12:10:47,087 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:47,239 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #41. Is it enabled?
2026-05-04T12:10:47,251 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #41 is disabled
2026-05-04T12:10:47,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #65
2026-05-04T12:10:47,254 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:47,268 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #65. Is it enabled?
2026-05-04T12:10:47,271 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #65 is disabled
2026-05-04T12:10:47,272 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #39
2026-05-04T12:10:47,272 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:47,377 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #39. Is it enabled?
2026-05-04T12:10:47,397 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #39 is disabled
2026-05-04T12:10:47,400 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #22
2026-05-04T12:10:47,400 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:47,477 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-05-04T12:10:47,496 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #12
2026-05-04T12:10:47,496 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:47,619 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #12. Is it enabled?
2026-05-04T12:10:47,651 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #12 is disabled
2026-05-04T12:10:47,657 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #6
2026-05-04T12:10:47,657 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:47,702 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #6. Is it enabled?
2026-05-04T12:10:48,088 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #6 is enabled
2026-05-04T12:10:48,088 [main] INFO  a.f.a.t.b.SeqModelChecker - State 5: Checking 2 state invariants
2026-05-04T12:10:48,088 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 5: Checking state invariant 0
2026-05-04T12:10:48,449 [main] INFO  a.f.a.t.b.SeqModelChecker - State 5: state invariant 0 holds.
2026-05-04T12:10:48,453 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 5: Checking state invariant 1
2026-05-04T12:10:48,704 [main] INFO  a.f.a.t.b.SeqModelChecker - State 5: state invariant 1 holds.
2026-05-04T12:10:48,710 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: randomly picked transition #6
2026-05-04T12:10:48,710 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 5: picking a transition out of 1 transition(s)
2026-05-04T12:10:48,711 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #54
2026-05-04T12:10:48,711 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:48,763 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #54. Is it enabled?
2026-05-04T12:10:48,772 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #54 is disabled
2026-05-04T12:10:48,775 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #12
2026-05-04T12:10:48,775 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:48,963 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #12. Is it enabled?
2026-05-04T12:10:48,994 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #12 is disabled
2026-05-04T12:10:48,999 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #44
2026-05-04T12:10:48,999 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:49,104 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #44. Is it enabled?
2026-05-04T12:10:49,121 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #44 is disabled
2026-05-04T12:10:49,124 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #24
2026-05-04T12:10:49,124 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:49,203 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #24. Is it enabled?
2026-05-04T12:10:49,219 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #24 is disabled
2026-05-04T12:10:49,222 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #17
2026-05-04T12:10:49,222 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:49,297 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #17. Is it enabled?
2026-05-04T12:10:49,369 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #17 is disabled
2026-05-04T12:10:49,372 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #66
2026-05-04T12:10:49,372 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:49,493 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #66. Is it enabled?
2026-05-04T12:10:49,509 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #66 is disabled
2026-05-04T12:10:49,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #49
2026-05-04T12:10:49,513 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:49,665 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #49. Is it enabled?
2026-05-04T12:10:49,696 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #49 is disabled
2026-05-04T12:10:49,701 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #58
2026-05-04T12:10:49,701 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:49,748 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #58. Is it enabled?
2026-05-04T12:10:49,759 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #58 is disabled
2026-05-04T12:10:49,762 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #35
2026-05-04T12:10:49,762 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:49,886 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #35. Is it enabled?
2026-05-04T12:10:50,676 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #35 is disabled
2026-05-04T12:10:50,685 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #18
2026-05-04T12:10:50,685 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:50,707 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-05-04T12:10:50,710 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #56
2026-05-04T12:10:50,710 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:50,753 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #56. Is it enabled?
2026-05-04T12:10:50,761 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #56 is disabled
2026-05-04T12:10:50,763 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #39
2026-05-04T12:10:50,763 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:50,911 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #39. Is it enabled?
2026-05-04T12:10:50,927 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #39 is disabled
2026-05-04T12:10:50,930 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #46
2026-05-04T12:10:50,931 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:51,056 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #46. Is it enabled?
2026-05-04T12:10:51,081 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #46 is disabled
2026-05-04T12:10:51,086 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #2
2026-05-04T12:10:51,086 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:51,146 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #2. Is it enabled?
2026-05-04T12:10:51,158 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #2 is disabled
2026-05-04T12:10:51,161 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #47
2026-05-04T12:10:51,161 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:51,292 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #47. Is it enabled?
2026-05-04T12:10:51,314 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #47 is disabled
2026-05-04T12:10:51,318 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #45
2026-05-04T12:10:51,318 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:51,427 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #45. Is it enabled?
2026-05-04T12:10:51,442 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #45 is disabled
2026-05-04T12:10:51,446 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #21
2026-05-04T12:10:51,446 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:51,671 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #21. Is it enabled?
2026-05-04T12:10:51,794 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #21 is disabled
2026-05-04T12:10:51,799 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #0
2026-05-04T12:10:51,799 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:51,867 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #0. Is it enabled?
2026-05-04T12:10:51,891 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: Transition #0 is disabled
2026-05-04T12:10:51,894 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #30
2026-05-04T12:10:51,894 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:52,020 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #30. Is it enabled?
2026-05-04T12:10:53,423 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #30 is enabled
2026-05-04T12:10:53,430 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: randomly picked transition #30
2026-05-04T12:10:53,430 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 6: picking a transition out of 1 transition(s)
2026-05-04T12:10:53,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #57
2026-05-04T12:10:53,431 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:53,438 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-05-04T12:10:53,440 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #36
2026-05-04T12:10:53,440 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:53,563 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-04T12:10:53,577 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #26
2026-05-04T12:10:53,577 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:53,771 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #26. Is it enabled?
2026-05-04T12:10:53,796 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #26 is disabled
2026-05-04T12:10:53,801 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #64
2026-05-04T12:10:53,801 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:53,911 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #64. Is it enabled?
2026-05-04T12:10:53,935 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #64 is disabled
2026-05-04T12:10:53,940 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #42
2026-05-04T12:10:53,940 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:54,013 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-04T12:10:54,024 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #29
2026-05-04T12:10:54,024 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:54,145 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #29. Is it enabled?
2026-05-04T12:10:54,821 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #29 is disabled
2026-05-04T12:10:54,832 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #43
2026-05-04T12:10:54,833 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:54,977 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #43. Is it enabled?
2026-05-04T12:10:54,996 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #43 is disabled
2026-05-04T12:10:55,001 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #53
2026-05-04T12:10:55,001 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:55,078 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #53. Is it enabled?
2026-05-04T12:10:55,094 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #53 is disabled
2026-05-04T12:10:55,098 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #61
2026-05-04T12:10:55,098 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:55,104 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-04T12:10:55,106 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #35
2026-05-04T12:10:55,106 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:55,283 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #35. Is it enabled?
2026-05-04T12:10:56,708 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #35 is disabled
2026-05-04T12:10:56,719 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #17
2026-05-04T12:10:56,719 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:56,820 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #17. Is it enabled?
2026-05-04T12:10:56,899 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #17 is disabled
2026-05-04T12:10:56,904 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #32
2026-05-04T12:10:56,904 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:57,053 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #32. Is it enabled?
2026-05-04T12:10:57,893 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #32 is disabled
2026-05-04T12:10:57,905 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #68
2026-05-04T12:10:57,905 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:57,963 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #68. Is it enabled?
2026-05-04T12:10:57,973 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #68 is disabled
2026-05-04T12:10:57,977 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #41
2026-05-04T12:10:57,977 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:58,113 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #41. Is it enabled?
2026-05-04T12:10:58,132 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #41 is disabled
2026-05-04T12:10:58,137 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #21
2026-05-04T12:10:58,137 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:58,384 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #21. Is it enabled?
2026-05-04T12:10:58,473 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #21 is disabled
2026-05-04T12:10:58,479 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #25
2026-05-04T12:10:58,479 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:58,505 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-04T12:10:58,510 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #65
2026-05-04T12:10:58,510 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:58,526 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #65. Is it enabled?
2026-05-04T12:10:58,528 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: Transition #65 is disabled
2026-05-04T12:10:58,530 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #16
2026-05-04T12:10:58,530 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:10:58,579 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #16. Is it enabled?
2026-05-04T12:10:59,544 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #16 is enabled
2026-05-04T12:10:59,545 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: Checking 2 state invariants
2026-05-04T12:10:59,545 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 7: Checking state invariant 0
2026-05-04T12:11:00,467 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: state invariant 0 holds.
2026-05-04T12:11:00,472 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 7: Checking state invariant 1
2026-05-04T12:11:01,199 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: state invariant 1 holds.
2026-05-04T12:11:01,208 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: randomly picked transition #16
2026-05-04T12:11:01,208 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 7: picking a transition out of 1 transition(s)
2026-05-04T12:11:01,209 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #1
2026-05-04T12:11:01,209 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:01,297 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #1. Is it enabled?
2026-05-04T12:11:01,315 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #1 is disabled
2026-05-04T12:11:01,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #13
2026-05-04T12:11:01,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:01,492 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #13. Is it enabled?
2026-05-04T12:11:03,405 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #13 is enabled
2026-05-04T12:11:03,418 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: randomly picked transition #13
2026-05-04T12:11:03,419 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 8: picking a transition out of 1 transition(s)
2026-05-04T12:11:03,420 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #24
2026-05-04T12:11:03,420 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:03,745 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #24. Is it enabled?
2026-05-04T12:11:03,784 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #24 is disabled
2026-05-04T12:11:03,793 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #52
2026-05-04T12:11:03,793 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:04,205 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #52. Is it enabled?
2026-05-04T12:11:05,992 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #52 is disabled
2026-05-04T12:11:06,028 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #22
2026-05-04T12:11:06,028 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:06,358 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 22 produces partial assignment. Disabled.
2026-05-04T12:11:06,427 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #44
2026-05-04T12:11:06,427 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:06,685 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #44. Is it enabled?
2026-05-04T12:11:07,038 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #44 is disabled
2026-05-04T12:11:07,047 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #16
2026-05-04T12:11:07,047 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:07,098 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #16. Is it enabled?
2026-05-04T12:11:07,123 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #16 is disabled
2026-05-04T12:11:07,127 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #32
2026-05-04T12:11:07,127 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:07,259 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #32. Is it enabled?
2026-05-04T12:11:09,320 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #32 is disabled
2026-05-04T12:11:09,335 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #34
2026-05-04T12:11:09,336 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:09,481 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #34. Is it enabled?
2026-05-04T12:11:11,176 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #34 is disabled
2026-05-04T12:11:11,192 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #1
2026-05-04T12:11:11,192 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:11,286 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #1. Is it enabled?
2026-05-04T12:11:11,307 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #1 is disabled
2026-05-04T12:11:11,312 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #65
2026-05-04T12:11:11,312 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:11,332 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #65. Is it enabled?
2026-05-04T12:11:11,336 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #65 is disabled
2026-05-04T12:11:11,338 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #43
2026-05-04T12:11:11,338 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:11,597 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #43. Is it enabled?
2026-05-04T12:11:15,658 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #43 is enabled
2026-05-04T12:11:15,658 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: Checking 2 state invariants
2026-05-04T12:11:15,658 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 9: Checking state invariant 0
2026-05-04T12:11:26,634 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: state invariant 0 holds.
2026-05-04T12:11:26,644 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 9: Checking state invariant 1
2026-05-04T12:11:29,942 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: state invariant 1 holds.
2026-05-04T12:11:29,955 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: randomly picked transition #43
2026-05-04T12:11:29,955 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 9: picking a transition out of 1 transition(s)
2026-05-04T12:11:29,957 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #33
2026-05-04T12:11:29,957 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-04T12:11:30,120 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #33. Is it enabled?
2026-05-04T12:11:30,776 [main] DEBUG a.f.a.i.p.PassChainExecutor - Adapted exception intercepted: 
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
2026-05-04T12:11:30,818 [main] ERROR a.f.a.t.Tool\$ - <unknown>: error when rewriting to SMT: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
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

