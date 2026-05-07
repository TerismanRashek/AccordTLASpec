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

The bug is in recover computations, line 245, the dependencies must be recomputed when participating in recovery.
D has been replaced with dep[p][id] in the output record to recreate the bug.

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

WitnessAllStable == 
    ~\A p \in Proc, id \in Id :
        phase[p][id] = StablePhase

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
2026-05-07T10:15:04,663 [main] INFO  a.f.a.t.Tool\$ - # APALACHE version: 0.56.1 | build: 70cdaf4
2026-05-07T10:15:04,680 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > AccordSpec.cfg: Loading TLC configuration
2026-05-07T10:15:04,724 [main] WARN  a.f.a.i.t.TlcConfigParserApalache\$ - TLC config option CHECK_DEADLOCK true will be ignored
2026-05-07T10:15:04,730 [main] INFO  a.f.a.i.p.o.OptionGroup\$ -   > Using inv predicate(s) Agreement, Ordering from the TLC config
2026-05-07T10:15:04,731 [main] INFO  a.f.a.t.t.o.SimulateCmd - Tuning: search.simulation.maxRun=100:search.simulation=true:search.outputTraces=false
2026-05-07T10:15:04,898 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser
2026-05-07T10:15:05,502 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #0: SanyParser [OK]
2026-05-07T10:15:05,502 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat
2026-05-07T10:15:05,502 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Running Snowcat .::.
2026-05-07T10:15:13,729 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > Your types are purrfect!
2026-05-07T10:15:13,730 [main] INFO  a.f.a.t.p.t.EtcTypeCheckerPassImpl -  > All expressions are typed
2026-05-07T10:15:13,730 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #1: TypeCheckerSnowcat [OK]
2026-05-07T10:15:13,730 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass
2026-05-07T10:15:13,896 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: Using SPECIFICATION Spec
2026-05-07T10:15:13,898 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > AccordSpec.cfg: found INVARIANTS: Agreement, Ordering
2026-05-07T10:15:13,900 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the initialization predicate to Init
2026-05-07T10:15:13,900 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the transition predicate to Next
2026-05-07T10:15:13,901 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set the constant initialization predicate to CInit
2026-05-07T10:15:13,901 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Agreement
2026-05-07T10:15:13,901 [main] INFO  a.f.a.t.p.p.ConfigurationPassImpl -   > Set an invariant to Ordering
2026-05-07T10:15:13,907 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #2: ConfigurationPass [OK]
2026-05-07T10:15:13,908 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass
2026-05-07T10:15:13,908 [main] INFO  a.f.a.t.p.p.DesugarerPassImpl -   > Desugaring...
2026-05-07T10:15:13,933 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #3: DesugarerPass [OK]
2026-05-07T10:15:13,934 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass
2026-05-07T10:15:13,934 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next, Ordering
2026-05-07T10:15:14,158 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #4: InlinePass [OK]
2026-05-07T10:15:14,158 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass
2026-05-07T10:15:14,159 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > Rewriting temporal operators...
2026-05-07T10:15:14,159 [main] INFO  a.f.a.t.p.p.TemporalPassImpl -   > No temporal property specified, nothing to encode
2026-05-07T10:15:14,159 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #5: TemporalPass [OK]
2026-05-07T10:15:14,159 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass
2026-05-07T10:15:14,159 [main] INFO  a.f.a.t.p.p.InlinePassImpl - Leaving only relevant operators: Agreement, CInit, CInitPrimed, Init, InitPrimed, Next, Ordering
2026-05-07T10:15:14,247 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #6: InlinePass [OK]
2026-05-07T10:15:14,248 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass
2026-05-07T10:15:14,252 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing CInitPrimed for CInit'
2026-05-07T10:15:14,253 [main] INFO  a.f.a.t.p.a.PrimingPassImpl -   > Introducing InitPrimed for Init'
2026-05-07T10:15:14,253 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #7: PrimingPass [OK]
2026-05-07T10:15:14,253 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #8: VCGen
2026-05-07T10:15:14,254 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Agreement
2026-05-07T10:15:14,260 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-05-07T10:15:14,261 [main] INFO  a.f.a.t.b.p.VCGenPassImpl -   > Producing verification conditions from the invariant Ordering
2026-05-07T10:15:14,262 [main] INFO  a.f.a.t.b.VCGenerator -   > VCGen produced 1 verification condition(s)
2026-05-07T10:15:14,264 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #8: VCGen [OK]
2026-05-07T10:15:14,264 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass
2026-05-07T10:15:14,264 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Before preprocessing: unique renaming
2026-05-07T10:15:14,271 [main] INFO  a.f.a.t.p.p.PreproPassImpl -  > Applying standard transformations:
2026-05-07T10:15:14,271 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > PrimePropagation
2026-05-07T10:15:14,286 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Desugarer
2026-05-07T10:15:14,303 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > UniqueRenamer
2026-05-07T10:15:14,381 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Normalizer
2026-05-07T10:15:14,410 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > Keramelizer
2026-05-07T10:15:14,458 [main] INFO  a.f.a.t.p.p.PreproPassImpl -   > After preprocessing: UniqueRenamer
2026-05-07T10:15:14,539 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #9: PreprocessingPass [OK]
2026-05-07T10:15:14,540 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass
2026-05-07T10:15:14,599 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 1 initializing transitions
2026-05-07T10:15:14,701 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found 70 transitions
2026-05-07T10:15:14,701 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Found constant initializer CInit
2026-05-07T10:15:14,704 [main] INFO  a.f.a.t.p.a.TransitionPassImpl -   > Applying unique renaming
2026-05-07T10:15:14,817 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #10: TransitionFinderPass [OK]
2026-05-07T10:15:14,818 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass
2026-05-07T10:15:14,825 [main] INFO  a.f.a.t.p.p.OptPassImpl -  > Applying optimizations:
2026-05-07T10:15:14,826 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-05-07T10:15:14,945 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ExprOptimizer
2026-05-07T10:15:14,998 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > SetMembershipSimplifier
2026-05-07T10:15:15,014 [main] INFO  a.f.a.t.p.p.OptPassImpl -   > ConstSimplifier
2026-05-07T10:15:15,106 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #11: OptimizationPass [OK]
2026-05-07T10:15:15,107 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass
2026-05-07T10:15:15,109 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Marking skolemizable existentials and sets to be expanded...
2026-05-07T10:15:15,110 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Skolemization
2026-05-07T10:15:15,119 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Expansion
2026-05-07T10:15:15,167 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Remove unused let-in defs
2026-05-07T10:15:15,188 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -  > Running analyzers...
2026-05-07T10:15:15,193 [main] INFO  a.f.a.t.b.p.AnalysisPassImpl -   > Introduced expression grades
2026-05-07T10:15:15,194 [main] DEBUG a.f.a.i.p.PassChainExecutor - PASS #12: AnalysisPass [OK]
2026-05-07T10:15:15,194 [main] INFO  a.f.a.i.p.PassChainExecutor - PASS #13: BoundedChecker
2026-05-07T10:15:15,220 [main] DEBUG a.f.a.t.b.s.Z3SolverContext - Creating Z3 solver context 0
2026-05-07T10:15:15,441 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Initializing CONSTANTS
2026-05-07T10:15:15,479 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #0, transition #0
2026-05-07T10:15:15,480 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:15,512 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0. Is it enabled?
2026-05-07T10:15:15,514 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 0: Transition #0 is enabled
2026-05-07T10:15:15,514 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: Checking 2 state invariants
2026-05-07T10:15:15,514 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 0
2026-05-07T10:15:15,564 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 0 holds.
2026-05-07T10:15:15,567 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 0: Checking state invariant 1
2026-05-07T10:15:15,623 [main] INFO  a.f.a.t.b.SeqModelChecker - State 0: state invariant 1 holds.
2026-05-07T10:15:15,624 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 0: randomly picked transition #0
2026-05-07T10:15:15,624 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 0: picking a transition out of 1 transition(s)
2026-05-07T10:15:15,626 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #0
2026-05-07T10:15:15,626 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:15,629 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #0. Is it enabled?
2026-05-07T10:15:15,630 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #0 is disabled
2026-05-07T10:15:15,631 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #52
2026-05-07T10:15:15,631 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:15,778 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #52. Is it enabled?
2026-05-07T10:15:15,783 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #52 is disabled
2026-05-07T10:15:15,785 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #2
2026-05-07T10:15:15,786 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:15,788 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #2. Is it enabled?
2026-05-07T10:15:15,788 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #2 is disabled
2026-05-07T10:15:15,789 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #21
2026-05-07T10:15:15,789 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:15,847 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #21. Is it enabled?
2026-05-07T10:15:15,850 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #21 is disabled
2026-05-07T10:15:15,851 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #68
2026-05-07T10:15:15,851 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:15,865 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #68. Is it enabled?
2026-05-07T10:15:15,866 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #68 is disabled
2026-05-07T10:15:15,867 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #35
2026-05-07T10:15:15,867 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,029 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #35. Is it enabled?
2026-05-07T10:15:16,039 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #35 is disabled
2026-05-07T10:15:16,043 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #55
2026-05-07T10:15:16,043 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,054 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-07T10:15:16,055 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #48
2026-05-07T10:15:16,055 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,118 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #48. Is it enabled?
2026-05-07T10:15:16,123 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #48 is disabled
2026-05-07T10:15:16,125 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #34
2026-05-07T10:15:16,125 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,258 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #34. Is it enabled?
2026-05-07T10:15:16,268 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #34 is disabled
2026-05-07T10:15:16,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #56
2026-05-07T10:15:16,271 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,281 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #56. Is it enabled?
2026-05-07T10:15:16,282 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #56 is disabled
2026-05-07T10:15:16,283 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #4
2026-05-07T10:15:16,283 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,283 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 4 produces partial assignment. Disabled.
2026-05-07T10:15:16,283 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #27
2026-05-07T10:15:16,283 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,298 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #27. Is it enabled?
2026-05-07T10:15:16,300 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #27 is disabled
2026-05-07T10:15:16,301 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #1
2026-05-07T10:15:16,301 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,302 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #1. Is it enabled?
2026-05-07T10:15:16,302 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #1 is disabled
2026-05-07T10:15:16,303 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #65
2026-05-07T10:15:16,303 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,338 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #65. Is it enabled?
2026-05-07T10:15:16,339 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #65 is disabled
2026-05-07T10:15:16,339 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #50
2026-05-07T10:15:16,339 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,363 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #50. Is it enabled?
2026-05-07T10:15:16,365 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #50 is disabled
2026-05-07T10:15:16,366 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #38
2026-05-07T10:15:16,367 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,369 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-07T10:15:16,369 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #44
2026-05-07T10:15:16,369 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,415 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #44. Is it enabled?
2026-05-07T10:15:16,419 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #44 is disabled
2026-05-07T10:15:16,420 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #58
2026-05-07T10:15:16,420 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,430 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #58. Is it enabled?
2026-05-07T10:15:16,431 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #58 is disabled
2026-05-07T10:15:16,432 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #23
2026-05-07T10:15:16,432 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,435 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-05-07T10:15:16,435 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #12
2026-05-07T10:15:16,435 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,436 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #12. Is it enabled?
2026-05-07T10:15:16,437 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #12 is disabled
2026-05-07T10:15:16,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #6
2026-05-07T10:15:16,437 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,438 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #6. Is it enabled?
2026-05-07T10:15:16,438 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #6 is disabled
2026-05-07T10:15:16,439 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #39
2026-05-07T10:15:16,439 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,496 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #39. Is it enabled?
2026-05-07T10:15:16,501 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #39 is disabled
2026-05-07T10:15:16,503 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #41
2026-05-07T10:15:16,503 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,536 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #41. Is it enabled?
2026-05-07T10:15:16,539 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #41 is disabled
2026-05-07T10:15:16,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #28
2026-05-07T10:15:16,540 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,660 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #28. Is it enabled?
2026-05-07T10:15:16,670 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #28 is disabled
2026-05-07T10:15:16,673 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #10
2026-05-07T10:15:16,675 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,676 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #10. Is it enabled?
2026-05-07T10:15:16,676 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #10 is disabled
2026-05-07T10:15:16,677 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #40
2026-05-07T10:15:16,677 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,680 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-05-07T10:15:16,681 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #5
2026-05-07T10:15:16,681 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,681 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #5. Is it enabled?
2026-05-07T10:15:16,682 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #5 is disabled
2026-05-07T10:15:16,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #49
2026-05-07T10:15:16,682 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,738 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #49. Is it enabled?
2026-05-07T10:15:16,743 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #49 is disabled
2026-05-07T10:15:16,745 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #9
2026-05-07T10:15:16,745 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,746 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #9. Is it enabled?
2026-05-07T10:15:16,746 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #9 is disabled
2026-05-07T10:15:16,747 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #60
2026-05-07T10:15:16,747 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,754 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #60. Is it enabled?
2026-05-07T10:15:16,755 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #60 is disabled
2026-05-07T10:15:16,756 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #51
2026-05-07T10:15:16,756 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,831 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #51. Is it enabled?
2026-05-07T10:15:16,836 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #51 is disabled
2026-05-07T10:15:16,838 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #29
2026-05-07T10:15:16,838 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,967 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #29. Is it enabled?
2026-05-07T10:15:16,978 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #29 is disabled
2026-05-07T10:15:16,980 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #61
2026-05-07T10:15:16,980 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:16,986 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-07T10:15:16,987 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #17
2026-05-07T10:15:16,987 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,013 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #17. Is it enabled?
2026-05-07T10:15:17,016 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #17 is disabled
2026-05-07T10:15:17,017 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #25
2026-05-07T10:15:17,017 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,019 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-07T10:15:17,019 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #42
2026-05-07T10:15:17,019 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-07T10:15:17,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #36
2026-05-07T10:15:17,021 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,023 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-07T10:15:17,023 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #63
2026-05-07T10:15:17,023 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,030 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #63. Is it enabled?
2026-05-07T10:15:17,032 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #63 is disabled
2026-05-07T10:15:17,032 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #37
2026-05-07T10:15:17,032 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,069 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #37. Is it enabled?
2026-05-07T10:15:17,074 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #37 is disabled
2026-05-07T10:15:17,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #43
2026-05-07T10:15:17,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,100 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #43. Is it enabled?
2026-05-07T10:15:17,103 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #43 is disabled
2026-05-07T10:15:17,104 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #64
2026-05-07T10:15:17,104 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,111 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #64. Is it enabled?
2026-05-07T10:15:17,112 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #64 is disabled
2026-05-07T10:15:17,112 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #31
2026-05-07T10:15:17,112 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,205 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #31. Is it enabled?
2026-05-07T10:15:17,215 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #31 is disabled
2026-05-07T10:15:17,217 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #24
2026-05-07T10:15:17,217 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,245 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #24. Is it enabled?
2026-05-07T10:15:17,249 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #24 is disabled
2026-05-07T10:15:17,250 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #26
2026-05-07T10:15:17,250 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,282 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #26. Is it enabled?
2026-05-07T10:15:17,286 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #26 is disabled
2026-05-07T10:15:17,287 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #47
2026-05-07T10:15:17,287 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,382 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #47. Is it enabled?
2026-05-07T10:15:17,387 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #47 is disabled
2026-05-07T10:15:17,389 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #8
2026-05-07T10:15:17,389 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,390 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 8 produces partial assignment. Disabled.
2026-05-07T10:15:17,390 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #13
2026-05-07T10:15:17,390 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,391 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #13. Is it enabled?
2026-05-07T10:15:17,391 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: Transition #13 is disabled
2026-05-07T10:15:17,391 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #1, transition #16
2026-05-07T10:15:17,391 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,437 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16. Is it enabled?
2026-05-07T10:15:17,447 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 1: Transition #16 is enabled
2026-05-07T10:15:17,447 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: Checking 2 state invariants
2026-05-07T10:15:17,448 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 0
2026-05-07T10:15:17,465 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 0 holds.
2026-05-07T10:15:17,466 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 1: Checking state invariant 1
2026-05-07T10:15:17,495 [main] INFO  a.f.a.t.b.SeqModelChecker - State 1: state invariant 1 holds.
2026-05-07T10:15:17,496 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 1: randomly picked transition #16
2026-05-07T10:15:17,497 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 1: picking a transition out of 1 transition(s)
2026-05-07T10:15:17,497 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #43
2026-05-07T10:15:17,497 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,565 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #43. Is it enabled?
2026-05-07T10:15:17,571 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #43 is disabled
2026-05-07T10:15:17,573 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #40
2026-05-07T10:15:17,573 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,602 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-05-07T10:15:17,604 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #37
2026-05-07T10:15:17,604 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,674 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #37. Is it enabled?
2026-05-07T10:15:17,682 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #37 is disabled
2026-05-07T10:15:17,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #34
2026-05-07T10:15:17,684 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:17,876 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #34. Is it enabled?
2026-05-07T10:15:17,908 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #34 is disabled
2026-05-07T10:15:17,912 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #14
2026-05-07T10:15:17,912 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,027 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #14. Is it enabled?
2026-05-07T10:15:18,043 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #14 is disabled
2026-05-07T10:15:18,045 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #63
2026-05-07T10:15:18,046 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,089 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #63. Is it enabled?
2026-05-07T10:15:18,094 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #63 is disabled
2026-05-07T10:15:18,096 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #61
2026-05-07T10:15:18,096 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,101 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-07T10:15:18,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #50
2026-05-07T10:15:18,102 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,146 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #50. Is it enabled?
2026-05-07T10:15:18,151 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: Transition #50 is disabled
2026-05-07T10:15:18,153 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #18
2026-05-07T10:15:18,153 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,162 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-05-07T10:15:18,163 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #2, transition #30
2026-05-07T10:15:18,164 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,344 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30. Is it enabled?
2026-05-07T10:15:18,459 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 2: Transition #30 is enabled
2026-05-07T10:15:18,461 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 2: randomly picked transition #30
2026-05-07T10:15:18,461 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 2: picking a transition out of 1 transition(s)
2026-05-07T10:15:18,462 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #3
2026-05-07T10:15:18,462 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,472 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-07T10:15:18,474 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #28
2026-05-07T10:15:18,474 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,622 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #28. Is it enabled?
2026-05-07T10:15:18,673 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: Transition #28 is disabled
2026-05-07T10:15:18,678 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #40
2026-05-07T10:15:18,678 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,739 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-05-07T10:15:18,745 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #3, transition #15
2026-05-07T10:15:18,745 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:18,879 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #15. Is it enabled?
2026-05-07T10:15:19,091 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 3: Transition #15 is enabled
2026-05-07T10:15:19,092 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: Checking 2 state invariants
2026-05-07T10:15:19,092 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 0
2026-05-07T10:15:19,131 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 0 holds.
2026-05-07T10:15:19,133 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 3: Checking state invariant 1
2026-05-07T10:15:19,244 [main] INFO  a.f.a.t.b.SeqModelChecker - State 3: state invariant 1 holds.
2026-05-07T10:15:19,248 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 3: randomly picked transition #15
2026-05-07T10:15:19,249 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 3: picking a transition out of 1 transition(s)
2026-05-07T10:15:19,250 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #4, transition #47
2026-05-07T10:15:19,250 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:19,430 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #47. Is it enabled?
2026-05-07T10:15:19,701 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 4: Transition #47 is enabled
2026-05-07T10:15:19,702 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: Checking 2 state invariants
2026-05-07T10:15:19,702 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 0
2026-05-07T10:15:19,806 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 0 holds.
2026-05-07T10:15:19,809 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 4: Checking state invariant 1
2026-05-07T10:15:19,938 [main] INFO  a.f.a.t.b.SeqModelChecker - State 4: state invariant 1 holds.
2026-05-07T10:15:19,942 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 4: randomly picked transition #47
2026-05-07T10:15:19,944 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 4: picking a transition out of 1 transition(s)
2026-05-07T10:15:19,945 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #64
2026-05-07T10:15:19,945 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:20,054 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #64. Is it enabled?
2026-05-07T10:15:20,067 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #64 is disabled
2026-05-07T10:15:20,070 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #1
2026-05-07T10:15:20,070 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:20,187 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #1. Is it enabled?
2026-05-07T10:15:20,404 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #1 is disabled
2026-05-07T10:15:20,407 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #34
2026-05-07T10:15:20,408 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:20,541 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #34. Is it enabled?
2026-05-07T10:15:20,752 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #34 is disabled
2026-05-07T10:15:20,759 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #24
2026-05-07T10:15:20,759 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:20,943 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #24. Is it enabled?
2026-05-07T10:15:21,013 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #24 is disabled
2026-05-07T10:15:21,017 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #3
2026-05-07T10:15:21,017 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:21,031 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-07T10:15:21,033 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #43
2026-05-07T10:15:21,033 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:21,206 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #43. Is it enabled?
2026-05-07T10:15:21,243 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #43 is disabled
2026-05-07T10:15:21,248 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #12
2026-05-07T10:15:21,248 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:21,459 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #12. Is it enabled?
2026-05-07T10:15:21,622 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #12 is disabled
2026-05-07T10:15:21,629 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #37
2026-05-07T10:15:21,630 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:21,819 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #37. Is it enabled?
2026-05-07T10:15:21,875 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #37 is disabled
2026-05-07T10:15:21,883 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #59
2026-05-07T10:15:21,883 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:21,891 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-07T10:15:21,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #39
2026-05-07T10:15:21,892 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:22,128 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #39. Is it enabled?
2026-05-07T10:15:22,166 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #39 is disabled
2026-05-07T10:15:22,172 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #44
2026-05-07T10:15:22,172 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:22,410 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #44. Is it enabled?
2026-05-07T10:15:22,449 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #44 is disabled
2026-05-07T10:15:22,455 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #6
2026-05-07T10:15:22,455 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:22,516 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #6. Is it enabled?
2026-05-07T10:15:22,529 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: Transition #6 is disabled
2026-05-07T10:15:22,532 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #5, transition #2
2026-05-07T10:15:22,532 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:22,613 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #2. Is it enabled?
2026-05-07T10:15:23,778 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 5: Transition #2 is enabled
2026-05-07T10:15:23,779 [main] INFO  a.f.a.t.b.SeqModelChecker - State 5: Checking 2 state invariants
2026-05-07T10:15:23,779 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 5: Checking state invariant 0
2026-05-07T10:15:24,008 [main] INFO  a.f.a.t.b.SeqModelChecker - State 5: state invariant 0 holds.
2026-05-07T10:15:24,010 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 5: Checking state invariant 1
2026-05-07T10:15:24,283 [main] INFO  a.f.a.t.b.SeqModelChecker - State 5: state invariant 1 holds.
2026-05-07T10:15:24,289 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 5: randomly picked transition #2
2026-05-07T10:15:24,289 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 5: picking a transition out of 1 transition(s)
2026-05-07T10:15:24,290 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #6, transition #0
2026-05-07T10:15:24,290 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:24,375 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #0. Is it enabled?
2026-05-07T10:15:24,655 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 6: Transition #0 is enabled
2026-05-07T10:15:24,655 [main] INFO  a.f.a.t.b.SeqModelChecker - State 6: Checking 2 state invariants
2026-05-07T10:15:24,655 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 6: Checking state invariant 0
2026-05-07T10:15:24,870 [main] INFO  a.f.a.t.b.SeqModelChecker - State 6: state invariant 0 holds.
2026-05-07T10:15:24,874 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 6: Checking state invariant 1
2026-05-07T10:15:25,233 [main] INFO  a.f.a.t.b.SeqModelChecker - State 6: state invariant 1 holds.
2026-05-07T10:15:25,240 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 6: randomly picked transition #0
2026-05-07T10:15:25,240 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 6: picking a transition out of 1 transition(s)
2026-05-07T10:15:25,241 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #42
2026-05-07T10:15:25,241 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:25,425 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 42 produces partial assignment. Disabled.
2026-05-07T10:15:25,443 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #7, transition #2
2026-05-07T10:15:25,443 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:25,528 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #2. Is it enabled?
2026-05-07T10:15:25,877 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 7: Transition #2 is enabled
2026-05-07T10:15:25,877 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: Checking 2 state invariants
2026-05-07T10:15:25,877 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 7: Checking state invariant 0
2026-05-07T10:15:26,363 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: state invariant 0 holds.
2026-05-07T10:15:26,366 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 7: Checking state invariant 1
2026-05-07T10:15:26,845 [main] INFO  a.f.a.t.b.SeqModelChecker - State 7: state invariant 1 holds.
2026-05-07T10:15:26,854 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 7: randomly picked transition #2
2026-05-07T10:15:26,854 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 7: picking a transition out of 1 transition(s)
2026-05-07T10:15:26,855 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #51
2026-05-07T10:15:26,855 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:27,096 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #51. Is it enabled?
2026-05-07T10:15:27,171 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #51 is disabled
2026-05-07T10:15:27,179 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #17
2026-05-07T10:15:27,180 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:27,322 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #17. Is it enabled?
2026-05-07T10:15:27,697 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #17 is disabled
2026-05-07T10:15:27,705 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #18
2026-05-07T10:15:27,705 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:27,751 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 18 produces partial assignment. Disabled.
2026-05-07T10:15:27,757 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #10
2026-05-07T10:15:27,757 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:27,825 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #10. Is it enabled?
2026-05-07T10:15:27,835 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #10 is disabled
2026-05-07T10:15:27,839 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #31
2026-05-07T10:15:27,839 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:27,963 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #31. Is it enabled?
2026-05-07T10:15:28,728 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #31 is disabled
2026-05-07T10:15:28,742 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #53
2026-05-07T10:15:28,742 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:28,822 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #53. Is it enabled?
2026-05-07T10:15:28,835 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #53 is disabled
2026-05-07T10:15:28,840 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #59
2026-05-07T10:15:28,840 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:28,846 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 59 produces partial assignment. Disabled.
2026-05-07T10:15:28,848 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #40
2026-05-07T10:15:28,848 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:28,966 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 40 produces partial assignment. Disabled.
2026-05-07T10:15:28,978 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #38
2026-05-07T10:15:28,978 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:29,057 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-07T10:15:29,068 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #57
2026-05-07T10:15:29,068 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:29,074 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 57 produces partial assignment. Disabled.
2026-05-07T10:15:29,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #64
2026-05-07T10:15:29,075 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:29,163 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #64. Is it enabled?
2026-05-07T10:15:29,179 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #64 is disabled
2026-05-07T10:15:29,183 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #50
2026-05-07T10:15:29,183 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:29,403 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #50. Is it enabled?
2026-05-07T10:15:29,604 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #50 is disabled
2026-05-07T10:15:29,611 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #35
2026-05-07T10:15:29,612 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:29,803 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #35. Is it enabled?
2026-05-07T10:15:31,202 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: Transition #35 is disabled
2026-05-07T10:15:31,217 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #8, transition #26
2026-05-07T10:15:31,217 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:31,340 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #26. Is it enabled?
2026-05-07T10:15:32,045 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 8: Transition #26 is enabled
2026-05-07T10:15:32,046 [main] INFO  a.f.a.t.b.SeqModelChecker - State 8: Checking 2 state invariants
2026-05-07T10:15:32,046 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 8: Checking state invariant 0
2026-05-07T10:15:33,112 [main] INFO  a.f.a.t.b.SeqModelChecker - State 8: state invariant 0 holds.
2026-05-07T10:15:33,121 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 8: Checking state invariant 1
2026-05-07T10:15:33,919 [main] INFO  a.f.a.t.b.SeqModelChecker - State 8: state invariant 1 holds.
2026-05-07T10:15:33,929 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 8: randomly picked transition #26
2026-05-07T10:15:33,929 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 8: picking a transition out of 1 transition(s)
2026-05-07T10:15:33,930 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #61
2026-05-07T10:15:33,930 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:33,940 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 61 produces partial assignment. Disabled.
2026-05-07T10:15:33,942 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #28
2026-05-07T10:15:33,942 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:34,110 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #28. Is it enabled?
2026-05-07T10:15:35,893 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #28 is disabled
2026-05-07T10:15:35,907 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #65
2026-05-07T10:15:35,907 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:35,933 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #65. Is it enabled?
2026-05-07T10:15:35,937 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: Transition #65 is disabled
2026-05-07T10:15:35,940 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #9, transition #16
2026-05-07T10:15:35,940 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:35,993 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #16. Is it enabled?
2026-05-07T10:15:37,730 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 9: Transition #16 is enabled
2026-05-07T10:15:37,730 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: Checking 2 state invariants
2026-05-07T10:15:37,730 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 9: Checking state invariant 0
2026-05-07T10:15:40,340 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: state invariant 0 holds.
2026-05-07T10:15:40,352 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 9: Checking state invariant 1
2026-05-07T10:15:41,689 [main] INFO  a.f.a.t.b.SeqModelChecker - State 9: state invariant 1 holds.
2026-05-07T10:15:41,698 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 9: randomly picked transition #16
2026-05-07T10:15:41,698 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 9: picking a transition out of 1 transition(s)
2026-05-07T10:15:41,700 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #60
2026-05-07T10:15:41,700 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:41,749 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #60. Is it enabled?
2026-05-07T10:15:41,756 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #60 is disabled
2026-05-07T10:15:41,760 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #39
2026-05-07T10:15:41,760 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:42,267 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #39. Is it enabled?
2026-05-07T10:15:42,399 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #39 is disabled
2026-05-07T10:15:42,413 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #66
2026-05-07T10:15:42,414 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:42,504 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #66. Is it enabled?
2026-05-07T10:15:42,525 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #66 is disabled
2026-05-07T10:15:42,531 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #32
2026-05-07T10:15:42,531 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:42,667 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #32. Is it enabled?
2026-05-07T10:15:44,758 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #32 is disabled
2026-05-07T10:15:44,773 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #49
2026-05-07T10:15:44,773 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:45,388 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #49. Is it enabled?
2026-05-07T10:15:45,674 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #49 is disabled
2026-05-07T10:15:45,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #38
2026-05-07T10:15:45,692 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:45,992 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-07T10:15:46,026 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #34
2026-05-07T10:15:46,026 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:46,208 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #34. Is it enabled?
2026-05-07T10:15:47,675 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #34 is disabled
2026-05-07T10:15:47,693 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #27
2026-05-07T10:15:47,693 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:47,862 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #27. Is it enabled?
2026-05-07T10:15:48,189 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #27 is disabled
2026-05-07T10:15:48,198 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #62
2026-05-07T10:15:48,198 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:48,270 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #62. Is it enabled?
2026-05-07T10:15:48,279 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #62 is disabled
2026-05-07T10:15:48,283 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #19
2026-05-07T10:15:48,284 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:48,354 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 19 produces partial assignment. Disabled.
2026-05-07T10:15:48,362 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #51
2026-05-07T10:15:48,362 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:48,710 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #51. Is it enabled?
2026-05-07T10:15:48,856 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #51 is disabled
2026-05-07T10:15:48,869 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #63
2026-05-07T10:15:48,869 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:48,932 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #63. Is it enabled?
2026-05-07T10:15:48,944 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #63 is disabled
2026-05-07T10:15:48,949 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #6
2026-05-07T10:15:48,949 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:49,067 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #6. Is it enabled?
2026-05-07T10:15:49,083 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #6 is disabled
2026-05-07T10:15:49,089 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #3
2026-05-07T10:15:49,089 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:49,112 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 3 produces partial assignment. Disabled.
2026-05-07T10:15:49,115 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #36
2026-05-07T10:15:49,115 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:49,223 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-07T10:15:49,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #65
2026-05-07T10:15:49,242 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:49,265 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #65. Is it enabled?
2026-05-07T10:15:49,268 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #65 is disabled
2026-05-07T10:15:49,273 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #55
2026-05-07T10:15:49,273 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:49,279 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 55 produces partial assignment. Disabled.
2026-05-07T10:15:49,280 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #47
2026-05-07T10:15:49,280 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:49,592 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #47. Is it enabled?
2026-05-07T10:15:49,642 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #47 is disabled
2026-05-07T10:15:49,652 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #26
2026-05-07T10:15:49,652 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:49,889 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #26. Is it enabled?
2026-05-07T10:15:50,080 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: Transition #26 is disabled
2026-05-07T10:15:50,088 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #10, transition #0
2026-05-07T10:15:50,088 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:15:50,208 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #0. Is it enabled?
2026-05-07T10:15:54,089 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 10: Transition #0 is enabled
2026-05-07T10:15:54,089 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: Checking 2 state invariants
2026-05-07T10:15:54,090 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 10: Checking state invariant 0
2026-05-07T10:16:00,686 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: state invariant 0 holds.
2026-05-07T10:16:00,701 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 10: Checking state invariant 1
2026-05-07T10:16:02,898 [main] INFO  a.f.a.t.b.SeqModelChecker - State 10: state invariant 1 holds.
2026-05-07T10:16:02,917 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 10: randomly picked transition #0
2026-05-07T10:16:02,918 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 10: picking a transition out of 1 transition(s)
2026-05-07T10:16:02,919 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #11, transition #66
2026-05-07T10:16:02,919 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:03,005 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 11: Transition #66. Is it enabled?
2026-05-07T10:16:03,020 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 11: Transition #66 is disabled
2026-05-07T10:16:03,026 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #11, transition #25
2026-05-07T10:16:03,026 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:03,066 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 25 produces partial assignment. Disabled.
2026-05-07T10:16:03,073 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #11, transition #38
2026-05-07T10:16:03,073 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:03,263 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 38 produces partial assignment. Disabled.
2026-05-07T10:16:03,291 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #11, transition #9
2026-05-07T10:16:03,291 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:03,396 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 11: Transition #9. Is it enabled?
2026-05-07T10:16:04,834 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 11: Transition #9 is enabled
2026-05-07T10:16:04,834 [main] INFO  a.f.a.t.b.SeqModelChecker - State 11: Checking 2 state invariants
2026-05-07T10:16:04,834 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 11: Checking state invariant 0
2026-05-07T10:16:13,663 [main] INFO  a.f.a.t.b.SeqModelChecker - State 11: state invariant 0 holds.
2026-05-07T10:16:13,677 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 11: Checking state invariant 1
2026-05-07T10:16:20,072 [main] INFO  a.f.a.t.b.SeqModelChecker - State 11: state invariant 1 holds.
2026-05-07T10:16:20,101 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 11: randomly picked transition #9
2026-05-07T10:16:20,102 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 11: picking a transition out of 1 transition(s)
2026-05-07T10:16:20,104 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #12, transition #27
2026-05-07T10:16:20,104 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:20,333 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 12: Transition #27. Is it enabled?
2026-05-07T10:16:22,674 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 12: Transition #27 is enabled
2026-05-07T10:16:22,675 [main] INFO  a.f.a.t.b.SeqModelChecker - State 12: Checking 2 state invariants
2026-05-07T10:16:22,675 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 12: Checking state invariant 0
2026-05-07T10:16:35,211 [main] INFO  a.f.a.t.b.SeqModelChecker - State 12: state invariant 0 holds.
2026-05-07T10:16:35,229 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 12: Checking state invariant 1
2026-05-07T10:16:42,299 [main] INFO  a.f.a.t.b.SeqModelChecker - State 12: state invariant 1 holds.
2026-05-07T10:16:42,318 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 12: randomly picked transition #27
2026-05-07T10:16:42,318 [main] INFO  a.f.a.t.b.t.TransitionExecutorImpl - Step 12: picking a transition out of 1 transition(s)
2026-05-07T10:16:42,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #23
2026-05-07T10:16:42,320 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:42,371 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 23 produces partial assignment. Disabled.
2026-05-07T10:16:42,383 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #26
2026-05-07T10:16:42,384 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:42,764 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #26. Is it enabled?
2026-05-07T10:16:43,903 [main] INFO  a.f.a.t.b.SeqModelChecker - Step 13: Transition #26 is disabled
2026-05-07T10:16:43,919 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #7
2026-05-07T10:16:43,919 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:43,951 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 7 produces partial assignment. Disabled.
2026-05-07T10:16:43,956 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #36
2026-05-07T10:16:43,957 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:44,233 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Transition 36 produces partial assignment. Disabled.
2026-05-07T10:16:44,269 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Step #13, transition #11
2026-05-07T10:16:44,270 [main] DEBUG a.f.a.t.b.t.TransitionExecutorImpl - Translating to SMT
2026-05-07T10:16:44,378 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #11. Is it enabled?
2026-05-07T10:16:50,443 [main] DEBUG a.f.a.t.b.SeqModelChecker - Step 13: Transition #11 is enabled
2026-05-07T10:16:50,443 [main] INFO  a.f.a.t.b.SeqModelChecker - State 13: Checking 2 state invariants
2026-05-07T10:16:50,443 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 13: Checking state invariant 0
2026-05-07T10:17:03,458 [main] INFO  a.f.a.t.b.SeqModelChecker - State 13: state invariant 0 holds.
2026-05-07T10:17:03,478 [main] DEBUG a.f.a.t.b.SeqModelChecker - State 13: Checking state invariant 1
2026-05-07T10:17:10,135 [main] DEBUG a.f.a.i.p.PassChainExecutor - Adapted exception intercepted: 
at.forsyte.apalache.tla.bmcmt.SmtEncodingException: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
	at at.forsyte.apalache.tla.bmcmt.smt.Z3SolverContext.sat(Z3SolverContext.scala:557)
	at at.forsyte.apalache.tla.bmcmt.smt.Z3SolverContext.satOrTimeout(Z3SolverContext.scala:564)
	at at.forsyte.apalache.tla.bmcmt.smt.RecordingSolverContext.satOrTimeout(RecordingSolverContext.scala:205)
	at at.forsyte.apalache.tla.bmcmt.trex.TransitionExecutorImpl.sat(TransitionExecutorImpl.scala:349)
	at at.forsyte.apalache.tla.bmcmt.trex.FilteredTransitionExecutor.sat(FilteredTransitionExecutor.scala:181)
	at at.forsyte.apalache.tla.bmcmt.trex.ConstrainedTransitionExecutor.sat(ConstrainedTransitionExecutor.scala:127)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.\$anonfun\$checkInvariants\$2(SeqModelChecker.scala:371)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.\$anonfun\$checkInvariants\$2\$adapted(SeqModelChecker.scala:355)
	at scala.collection.IterableOnceOps.foreach(IterableOnce.scala:630)
	at scala.collection.IterableOnceOps.foreach\$(IterableOnce.scala:628)
	at scala.collection.AbstractIterable.foreach(Iterable.scala:936)
	at scala.collection.IterableOps\$WithFilter.foreach(Iterable.scala:906)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.checkInvariants(SeqModelChecker.scala:355)
	at at.forsyte.apalache.tla.bmcmt.SeqModelChecker.\$anonfun\$prepareTransitionsAndCheckInvariants\$5(SeqModelChecker.scala:251)
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
2026-05-07T10:17:10,206 [main] ERROR a.f.a.t.Tool\$ - <unknown>: error when rewriting to SMT: SMT 0: z3 reports UNKNOWN. Maybe, your specification is outside the supported logic.
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

