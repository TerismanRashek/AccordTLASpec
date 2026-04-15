---- MODULE AccordSpec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets, ExtraConfiguration


(*
This file contains the TLA + specification for Accord, It provides formal specification as well as
model checking capabilities to add an extra layer of certainty on the correctness of the algorithm.

Author : Alexandre SIRET
*)


(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)

\* variables are var[s][p][id] beacause we identify the specific process with both the shard id and the process id, and then we get the value for the command id. 
VARIABLES
    bal,           \* bal[s][p][id] = current ballot known by in shard s by process p for command id
    phase,         \* phase[s][p][id] ∈ {"none","preaccepted","accepted","committed"}
    txn,           \* txn[s][p][id] = command payload at p
    dep,           \* dep[s][p][id] = final dependency set (accepted or committed)
    ts,            \* ts[s][p][id] = timestamp at p, timestamp is a couple of (t, id) ts.t for timestamp, ts.id for id.
    abal,          \* abal[s][p][id] = last ballot where p accepted a slow-path value
    msgs,          \* multiset of network messages
    submitted,     \* set of submitted command ids
    initCoord,     \* initCoord[id] = process that submitted id, pair <<s,p>> (processes are identified by shard id + process id)
    initTimestamp, \* initTimestamp[id] 
    recovered,     \* var to limit amount of recovery attempts started
    
    \* the following variables are used in recovery to : 
    \*              -persist local state to the post waiting operation
    \*              -keep track of when we are allowed to trigger the post waiting operation
    Wvar,           
    TXvar,
    Dvar,
    Qvar,
    postWaitingFlag,
    recoveryAttemptBal,

    executed, \* set of  executed, executeWaitingFlag, relation commands at [s][p]
    executeWaitingFlag, \* flag to know when a process has already started executing id.
    relation

vars == << bal, phase, txn, dep, ts, abal, msgs, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar,  executed, executeWaitingFlag, relation >>


(***************************************************************************)
(* Constants :these are for the most part defined in the configuration file*)
(***************************************************************************)


CONSTANTS
    Shards,     \* The set of shards 
    Proc,       \* The set of processes, all shards use same numbered processes
    Id,         \* The set of command IDs
    F,         
    E,
    Bottom,     \* The bottom value for the command payload
    NoProc,      \* A special value representing no process
    Nop,           \* special Nop payload
    NumberOfRecoveryAttempts \* constant used to cap the amount of recovery attempts, this cap is per process command pair.
    \* The following constants are also imported from the ExtraConfiguration module. Look at the file for more details.
    \* idToShard[id] is the shards for transactions id.
    \* ConflictPairs is used to define the conflict relation between transactions
    \* initTimestampConstant gives an initial timestamp value for each transaction


\* Constants for Phases
InitialPhase == 1
PreAcceptedPhase == 2
AcceptedPhase == 3
CommittedPhase == 4
StablePhase == 5

\* Constants for Fast Slow or Medium Path
Fast == 0
Slow == 1
Medium == 2

\* Constants for message types
TypePreAccept == 1
TypePreAcceptOK == 2
TypeAccept == 3
TypeAcceptOK == 4
TypeCommit == 5
TypeCommitOK == 6
TypeStable == 7
TypeRecover == 8
TypeRecoverOK == 9
TypeRead == 10
TypeReadOk == 11
TypeApply == 12


(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)

N == Cardinality(Proc)
Nshards == Cardinality(Shards)

Max(a, b) == IF a > b THEN a ELSE b

\* Relations on timestamps 
LessThanTs(ts1, ts2) ==
    IF ts1.t < ts2.t THEN TRUE
    ELSE IF ts1.t > ts2.t THEN FALSE
    ELSE IF ts1.id[2] = ts2.id[2] THEN ts1.id[1] < ts2.id[1]
    ELSE ts1.id[2] < ts2.id[2]

MaxTs(ts1, ts2) ==
    IF LessThanTs(ts1, ts2) THEN ts2 ELSE ts1

MaxTsInSet(S) ==
    CHOOSE ts1 \in S : \A ts2 \in S :
                            ts2 # ts1 => LessThanTs(ts2, ts1)

\* uses the conflict pairs constant defined above, symmetrical of course
\* In general I use the id of the command as the payload (see submit operation)
Conflicts(id1, id2) ==
    <<id1, id2>> \in ConflictPairs \/ <<id2, id1>> \in ConflictPairs

IsQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - F
IsFastQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - E

\* both of these check that input set of messages has a quorum for each shard of command id.
IsQuorum(set, id) ==
    \A shard \in idToShard[id] :
        LET quorum == {m \in set : m.shardfrom = shard}
        IN 
        /\ IsQuorumSized(quorum)

IsFastQuorum(set, id) ==
    \A shard \in idToShard[id] :
        LET quorum == {m \in set : m.shardfrom = shard}
        IN 
        /\ IsFastQuorumSized(quorum)

\* This finds all commands that a process knows of, (checks in payload and in dependencies)
SeenIds(s, p) ==
    {id \in Id : 
        \/ txn[s][p][id] # Bottom
        \/ \E id2 \in Id : id \in dep[s][p][id2]}


ASSUME N >= Max(2*E+F-1, 2*F+1)

(***************************************************************************)
(* Init of all the variables                                               *)
(***************************************************************************)

Init == 
    /\ bal = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ phase = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> InitialPhase]]]
    /\ txn = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> Bottom]]]
    /\ dep = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ ts = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> [t |-> 0, id |-> <<0,NoProc>>]]] ]
    /\ abal = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ msgs = {}
    /\ submitted = {}
    /\ initCoord = [id \in Id |-> <<0, NoProc>>]
    /\ recovered = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ Wvar = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ TXvar = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> Bottom]]]
    /\ Dvar = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ postWaitingFlag = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> FALSE]]]
    /\ recoveryAttemptBal = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ initTimestamp = initTimestampConstant
    /\ Qvar = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ executed = [s \in Shards |-> [p \in Proc |-> {} ]]
    /\ executeWaitingFlag =  [s \in Shards |-> [p \in Proc |-> [id \in Id |-> FALSE]]]
    /\ relation = [id1 \in Id |-> [id2 \in Id |-> 0]]

(***************************************************************************)
(* Message constructors                                                    *)
(***************************************************************************)

\* this is the general message constructor, the message type, the sender process and receiving process, the body holds the rest of the
\* parameters specific to the message type. (Once again, to identify a process we need both the shard id : shardfrom, and the process id within that shard : from)
Message(type, shardfrom, from, shardto, to, body) ==
    [ type |-> type, shardfrom |-> shardfrom, from |-> from, to |-> to, shardto |-> shardto, body |-> body ]

PreAcceptMsg(sp, p, sq, q, id, tx, D0) ==
    Message(TypePreAccept, sp, p, sq, q,
        [ id  |-> id,
          tx |-> tx,
          D0 |-> D0 ])

PreAcceptOKMsg(sp, p, sq, q, id, tq, Dq) ==
    Message(TypePreAcceptOK, sp, p, sq, q,
        [ id  |-> id,
          tq |-> tq,
          Dq |-> Dq ])

AcceptMsg(sp, p, sq, q, b, id, t, D, tx, pathSpeed) ==
    Message(TypeAccept, sp, p, sq, q,
        [ id   |-> id,
          b  |-> b,
          t |-> t,
          tx |-> tx,
          D |-> D,
          pathSpeed |-> pathSpeed ])

AcceptOKMsg(sp, p, sq, q, b, id, Dq, pathSpeed) ==
    Message(TypeAcceptOK, sp, p, sq, q,
        [ id  |-> id,
          b |-> b,
          Dq |-> Dq,
          pathSpeed |-> pathSpeed ])

CommitMsg(sp, p, sq, q, b, id, t, D, fastOrSlow, tx) ==
    Message(TypeCommit, sp, p, sq, q,
        [ id   |-> id,
          b  |-> b,
          tx |-> tx,
          D |-> D,
          fastOrSlow |-> fastOrSlow,
          t |-> t ])

CommitOkMsg(sp, p, sq, q, b, id) ==
    Message(TypeCommitOK, sp, p, sq, q,
        [ id  |-> id,
          b |-> b ])

StableMsg(sp, p, sq, q, b, id) ==
    Message(TypeStable, sp, p, sq, q,
        [ id  |-> id,
          b |-> b ])

RecoverMsg(sp, p, sq, q, b, id, tx) ==
    Message(TypeRecover, sp, p, sq, q,
        [id   |-> id,
          b  |-> b,
          tx |-> tx])

RecoverOkMsg(sp, p, sq, q, b, id, abalq, txq, tq, depq, phaseq, rejectq, Wq, WPq) ==
    Message(TypeRecoverOK, sp, p, sq, q,
        [id   |-> id,
          b  |-> b,
          txq |-> txq,
          depq |-> depq,
          phaseq |-> phaseq,
          abalq |-> abalq,
          tq |-> tq,
          rejectq |-> rejectq,
          Wq |-> Wq,
          WPq |-> WPq ])

ReadMsg(sp, p, sq, q, id) ==
    Message(TypeRead, sp, p, sq, q, [id |-> id])

ReadOkMsg(sp, p, sq, q, id) ==
    Message(TypeReadOk, sp, p, sq, q, [id |-> id])

ApplyMsg(sp, p, sq, q, id) ==
    Message(TypeReadOk, sp, p, sq, q, [id |-> id])


(***************************************************************************)
(* State changing Actions                                                  *)
(***************************************************************************)

\* These operators are the insides of all the 'when received' a single message operations, this split allows me to handle self addressed
\* messages by calling the corresponding Apply operation. The computations operation is used for the resulting message we have to send.
\* For example, after we submit a command, we :
\*        - send PreAccept messages to everyone except ourselves
\*        - apply the PreAccept operation on ourselves
\*        - Compute the t and D values (see pseudocode)
\*        - send PreAcceptOk(id,t,D) to ourselves.

\* It's not possible to write a proper function that will apply the state change and also return the result of the computations in tla+, so I have a operator for the computations and another to describe the next state. 

PreAcceptComputations(s, p, sq, q, id, tx, initTs) ==
    LET setOfConflictingTs == {ts[s][p][id2] : id2 \in { id2 \in Id : ts[s][p][id2].id # <<0,NoProc>> /\ Conflicts(id, id2)}}
        D == { id2 \in SeenIds(s, p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], initTs) ) }
    IN
    LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
    IN
    LET finalTs == MaxTs(initTs, [t |-> tval, id |-> <<sq,q>>])
    IN
    [finalTs |-> finalTs, D |-> D] \* this is the record we get as output when we call this

ApplyPreAccept(sp, p, id, tx, finalTs, D0) ==
    /\  bal[sp][p][id] = 0
    /\  phase[sp][p][id] = InitialPhase
    /\  txn'   = [txn   EXCEPT ![sp][p][id] = tx]
    /\  phase' = [phase EXCEPT ![sp][p][id] = PreAcceptedPhase]
    /\  ts'    = [ts    EXCEPT ![sp][p][id] = finalTs]
    /\  dep'   = [dep   EXCEPT ![sp][p][id] = D0]

AcceptComputations(s, p, id, t) ==
    LET Dq == { id2 \in SeenIds(s, p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], t)) }
    IN
    [Dq |-> Dq] 

ApplyAccept(sp, p, b, id, t, D, tx) ==
    /\  bal[sp][p][id] <= b
    /\  (b = 0 => phase[sp][p][id] = PreAcceptedPhase)
    /\  IF b > 0 THEN txn'  = [txn  EXCEPT ![sp][p][id] = tx] ELSE UNCHANGED txn
    /\  bal'   = [bal   EXCEPT ![sp][p][id] = b]
    /\  abal'  = [abal  EXCEPT ![sp][p][id] = b]
    /\  ts'    = [ts    EXCEPT ![sp][p][id] = t]
    /\  dep'   = [dep   EXCEPT ![sp][p][id] = D]
    /\  phase' = [phase EXCEPT ![sp][p][id] = AcceptedPhase]

\* no local computations when receiving a commit message

ApplyCommit(sp, p, b, id, t, D, tx, stable) ==
    /\ bal[sp][p][id] = b
    /\ b = 0 => phase[sp][p][id] \in {PreAcceptedPhase, AcceptedPhase}
    /\ IF b > 0 THEN txn'  = [txn  EXCEPT ![sp][p][id] = tx] ELSE UNCHANGED txn
    /\ abal'  = [abal   EXCEPT ![sp][p][id] = b]
    /\ ts'    = [ts     EXCEPT ![sp][p][id] = t]
    /\ dep'   = [dep    EXCEPT ![sp][p][id] = D]
    /\ IF stable THEN phase' = [phase  EXCEPT ![sp][p][id] = StablePhase] ELSE phase' = [phase  EXCEPT ![sp][p][id] = CommittedPhase]

\* no local computations when receiving a stable message

ApplyStable(sp, p, b, id) ==
    /\ bal[sp][p][id] = b
    /\ phase[sp][p][id] = CommittedPhase
    /\ phase' = [phase EXCEPT ![sp][p][id] = StablePhase]

RecoverComputations(s, p, id) ==
    LET D == IF phase[s][p][id] \notin {InitialPhase, PreAcceptedPhase} THEN dep[s][p][id]
                ELSE dep[s][p][id] \cup {id2 \in SeenIds(s, p) : (Conflicts(id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
    IN
    LET S == {id2 \in SeenIds(s, p) : (id2 # id /\ Conflicts(id, id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2]
            /\(   (phase[s][p][id2] \in {CommittedPhase, StablePhase} /\ LessThanTs(initTimestamp[id], ts[s][p][id2]))  
                \/ (   phase[s][p][id2] = AcceptedPhase   /\   LessThanTs( initTimestamp[id] ,  initTimestamp[id2])) 
                )                    ) 
            }
        W == {<<id3,abal[s][p][id3]>> : id3 \in { id2 \in SeenIds(s, p) : (id2 # id /\ Conflicts(id, id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2] 
            /\ (  (phase[s][p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) /\ LessThanTs(initTimestamp[id], ts[s][p][id2]))
                \/ (phase[s][p][id2] = PreAcceptedPhase /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) )
                )
            )}}
        WP == {id2 \in SeenIds(s, p) : id2 # id /\ Conflicts(id, id2) /\ phase[s][p][id2] = PreAcceptedPhase 
                /\ LessThanTs(initTimestamp[id], initTimestamp[id2]) /\ id \notin dep[s][p][id2] }
    IN
    [D |-> D, S |-> S, W |-> W, WP |-> WP]

ApplyRecover(sp, p, b, id, tx) ==
        /\  bal[sp][p][id] < b
        /\  bal'  = [bal  EXCEPT ![sp][p][id] = b]
        /\  IF phase[sp][p][id] = InitialPhase THEN  txn'  = [txn  EXCEPT ![sp][p][id] = tx] ELSE UNCHANGED txn



(***************************************************************************)
(* Message handling Actions                                                *)
(***************************************************************************)

(* 1–3 Submit *)

Submit(s, p, id) ==
    /\  id \notin submitted
    \* I am checking that the initial coordinator is part of the shards for that transaction. It seems like a reasonable assumption,
    \* if I remove it, I would address a 'self sent message' that does not exist, altough this does not seem to actually create a bug (minimal testing was done). 
    /\  s \in idToShard[id] 
    /\  LET tx == id     \* I just use id as command payload, the actual payload does not matter here. Conflict relation is defined on these id integers.
            earlierInitTimestamps == {initTimestamp[id2] : id2 \in {id1 \in Id : initCoord[id1] = <<s,p>> /\ LessThanTs(initTimestamp[id], initTimestamp[id1])}}
        IN 
        \* making sure that this process has not already submitted a command with a greater timestamp than the one we are currently submitting.
        LET initTimestampVal == IF earlierInitTimestamps = {} THEN initTimestamp[id].t ELSE MaxTsInSet(earlierInitTimestamps).t + 1
        IN
        LET newInitTimestamp == [id |-> <<s,p>>, t |-> initTimestampVal]
        IN
        /\ initTimestamp' = [initTimestamp EXCEPT ![id] = newInitTimestamp]
        /\ submitted' = submitted \cup {id}
        /\ initCoord' = [initCoord EXCEPT ![id] = <<s,p>>]
        /\  LET computations == PreAcceptComputations(s, p, s, p, id, tx, newInitTimestamp)
            IN
            /\ ApplyPreAccept(s, p, id, tx, computations.finalTs, computations.D) \* slightly confusing here but computations.D is D0 here since this is the self addressed message.
            /\ msgs' = msgs \cup {PreAcceptMsg(s, p, to[1], to[2], id, tx, computations.D) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                            \cup {PreAcceptOKMsg(s, p, s, p, id, computations.finalTs, computations.D)}
    /\ UNCHANGED << bal, abal, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar,  executed, executeWaitingFlag, relation >> 


(* 4–12 HandlePreAccept  *)
                   
HandlePreAccept(m) ==
    /\  m.type = TypePreAccept
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            id == m.body.id
            tx  == m.body.tx
            D0 == m.body.D0
        IN 
        LET computations == PreAcceptComputations(s, p, sq, q, id, tx, initTimestamp[id])
        IN
        /\ ApplyPreAccept(s, p, id, tx, computations.finalTs, D0)
        /\ msgs' = (msgs \ {m}) \cup { PreAcceptOKMsg(s, p, sq, q, id, computations.finalTs, computations.D) }
    /\ UNCHANGED <<bal, abal, submitted, initCoord, recovered, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Wvar, Qvar, executed, executeWaitingFlag, relation, initTimestamp>>


(* 13–18 HandlePreAcceptOk *)

HandlePreAcceptOK(s, p, id) ==
    /\ bal[s][p][id] = 0
    /\ phase[s][p][id] = PreAcceptedPhase
    /\ LET quorumOfMessages ==
            {  m \in msgs :
                    /\ m.type = TypePreAcceptOK
                    /\ m.body.id = id
                    /\ m.to = p
                    /\ m.shardto = s 
            }
        IN
        /\  IsQuorum(quorumOfMessages, id) 
        /\  LET largestFastQuorum ==
                { m \in quorumOfMessages : m.body.tq = initTimestamp[id]  }
            IN
            IF IsFastQuorum(largestFastQuorum, id) THEN
                    LET D == dep[s][p][id] \cup UNION { m.body.Dq : m \in largestFastQuorum }
                    IN
                    /\ ApplyCommit(s, p, 0, id, initTimestamp[id], D, txn[s][p][id], TRUE)              
                    /\ msgs' = (msgs \ quorumOfMessages) \cup {CommitMsg(s, p, to[1], to[2], 0, id, initTimestamp[id], D, Fast, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                                                         \cup {StableMsg(s, p, to[1], to[2], 0, id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                    /\ UNCHANGED bal
            ELSE IF IsQuorum(largestFastQuorum, id) THEN
                    LET D == dep[s][p][id] \cup UNION {m.body.Dq : m \in largestFastQuorum}
                    IN
                    LET computations == AcceptComputations(s, p, id, initTimestamp[id])
                    IN 
                    /\ ApplyAccept(s, p, 0, id, initTimestamp[id], D, txn[s][p][id])
                    /\ msgs' = (msgs \ quorumOfMessages) \cup {AcceptMsg(s, p, to[1], to[2], 0, id, initTimestamp[id], D, txn[s][p][id], Medium) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  } 
                                                         \cup {AcceptOKMsg(s, p, s, p, 0, id, computations.Dq, Medium)}
            ELSE    
                /\  LET D == dep[s][p][id] \cup UNION { m.body.Dq : m \in quorumOfMessages }
                        t == MaxTsInSet({ m.body.tq : m \in quorumOfMessages })
                    IN
                    LET computations == AcceptComputations(s, p, id, t)
                    IN 
                    /\ ApplyAccept(s, p, 0, id, t, D, txn[s][p][id])
                    /\ msgs' = (msgs \ quorumOfMessages) \cup {AcceptMsg(s, p, to[1], to[2], 0, id, t, D, txn[s][p][id], Slow) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  } 
                                                         \cup {AcceptOKMsg(s, p, s, p, 0, id, computations.Dq, Slow)}
    /\ UNCHANGED <<submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar,  executed, executeWaitingFlag, relation  >>
       

(* 19–27 HandleAccept *)
                           
HandleAccept(m) ==
    /\ m.type = TypeAccept
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            b  == m.body.b
            id == m.body.id
            t  == m.body.t
            D  == m.body.D
            tx  == m.body.tx
            pathSpeed == m.body.pathSpeed
        IN
        LET computations == AcceptComputations(s, p, id, t)
        IN
        /\  ApplyAccept(s, p, b, id, t, D, tx)
        /\  msgs' = (msgs \ {m}) \cup {AcceptOKMsg(s, p, sq, q, b, id, computations.Dq, pathSpeed)}
    /\ UNCHANGED << submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar,  executed, executeWaitingFlag, relation  >>


(* 28–30 HandleAcceptOk *)

HandleAcceptOK(s, p, id) ==
    /\ phase[s][p][id] = AcceptedPhase
    /\ LET quorumOfMessages == { m \in msgs :
        /\ m.type = TypeAcceptOK
        /\ m.to = p
        /\ m.body.b = bal[s][p][id]
        /\ m.body.id = id
        /\ m.shardto = s }   
        IN
        /\ IsQuorum(quorumOfMessages, id)
        /\  LET D == dep[s][p][id] \cup UNION { m.body.Dq : m \in quorumOfMessages }
                n == CHOOSE m \in quorumOfMessages : TRUE
                pathSpeed == n.body.pathSpeed
            IN
            IF pathSpeed = Slow THEN
                /\ ApplyCommit(s, p, bal[s][p][id], id, ts[s][p][id], D, txn[s][p][id], FALSE)
                /\ msgs' = (msgs \ quorumOfMessages) \cup {CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], D, Slow, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  } 
                                                     \cup {CommitOkMsg(s, p, s, p, bal[s][p][id], id)} 
            ELSE 
                /\ ApplyCommit(s, p, bal[s][p][id], id, ts[s][p][id], D, txn[s][p][id], FALSE)
                /\ ApplyStable(s, p, bal[s][p][id], id)               
                /\ msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], D, Fast, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                                                     \cup { StableMsg(s, p, to[1], to[2], bal[s][p][id], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
    /\ UNCHANGED << bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar,  executed, executeWaitingFlag, relation >>


(* 31–38 HandleCommit *)

HandleCommit(m) ==
    /\ m.type = TypeCommit
    /\ LET  s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            b  == m.body.b
            id == m.body.id
            tx  == m.body.tx
            D  == m.body.D
            fastOrSlow == m.body.fastOrSlow
            t == m.body.t
       IN
       /\ ApplyCommit(s, p, b, id, t, D, tx, FALSE)
       /\ IF fastOrSlow = Slow THEN msgs' = (msgs \ {m}) \cup { CommitOkMsg(s, p, sq, q, b, id) } ELSE msgs' = msgs \ {m}
       /\ UNCHANGED << bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar,  executed, executeWaitingFlag, relation, initTimestamp >>


(* 42–44 HandleCommitOk *)

HandleCommitOK(s, p, id) ==
    /\  phase[s][p][id] = CommittedPhase
    /\  LET quorumOfMessages == { m \in msgs :
                                    /\ m.type = TypeCommitOK
                                    /\ m.to = p
                                    /\ m.body.b = bal[s][p][id]
                                    /\ m.body.id = id
                                    /\ m.shardto = s 
                               }   
        IN
        /\ IsQuorum(quorumOfMessages, id)
        /\ ApplyStable(s, p, bal[s][p][id], id)
        /\ msgs' = (msgs \ quorumOfMessages) \cup {StableMsg(s, p, to[1], to[2], bal[s][p][id], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
    /\ UNCHANGED << bal, txn, dep, ts, abal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar,  executed, executeWaitingFlag, relation >>

(* 39–41 HandleStable *)

HandleStable(m) ==
    /\ m.type = TypeStable
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            b  == m.body.b
            id == m.body.id
        IN
        /\ ApplyStable(s, p, b, id)
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED <<bal, submitted, initCoord, dep, abal, txn, ts, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar,  executed, executeWaitingFlag, relation >>


(* 45–48 StartRecover *)

StartRecover(s, p, id) ==
    /\ recovered[s][p][id] < NumberOfRecoveryAttempts
    /\ id \in SeenIds(s, p)
    /\ s \in idToShard[id]
    /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE] 
    /\ recovered' = [recovered EXCEPT ![s][p][id] = recovered[s][p][id] + 1]
    \* Ballots owned by p are of the form k*N + p. This k computation is just to get the smallest k * N + p larger than the current ballot
    \* Since 2 processes from different shards can have the same id I compute a new p unique id (N * Nshards of them in total) and use that.
    /\  LET Ntotal == N * Nshards IN
        LET pUnique == (s - 1) * N + p  IN
        LET k == ((bal[s][p][id] - pUnique) \div Ntotal) + 1 IN
        LET b == k * Ntotal + pUnique
        IN
        /\  LET computations == RecoverComputations(s, p, id)
            IN
            LET D == computations.D
                S == computations.S
                W == computations.W
                WP == computations.WP
            IN
            /\  ApplyRecover(s, p, b, id, txn[s][p][id])
            /\  IF S # {}
                THEN IF phase[s][p][id] # InitialPhase THEN msgs' =  msgs \cup {RecoverOkMsg(s, p, s, p, b, id, abal[s][p][id], txn[s][p][id], ts[s][p][id], D, phase[s][p][id], TRUE, W, WP)}  \cup { RecoverMsg(s, p, to[1], to[2], b, id, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ {<<s, p>>} }
                        ELSE                                msgs' =  msgs \cup {RecoverOkMsg(s, p, s, p, b, id, abal[s][p][id], Nop, ts[s][p][id], D, phase[s][p][id], TRUE, W, WP)}            \cup { RecoverMsg(s, p, to[1], to[2], b, id, Nop)           : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ {<<s, p>>} }
                ELSE IF phase[s][p][id] # InitialPhase THEN msgs' =  msgs \cup {RecoverOkMsg(s, p, s, p, b, id, abal[s][p][id], txn[s][p][id], ts[s][p][id], D, phase[s][p][id], FALSE, W, WP)} \cup { RecoverMsg(s, p, to[1], to[2], b, id, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ {<<s, p>>} }
                        ELSE                                msgs' =  msgs \cup {RecoverOkMsg(s, p, s, p, b, id, abal[s][p][id], Nop, ts[s][p][id], D, phase[s][p][id], FALSE, W, WP)}           \cup { RecoverMsg(s, p, to[1], to[2], b, id, Nop)           : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ {<<s, p>>} }
/\ UNCHANGED <<phase, dep, ts, abal, submitted, initCoord, Wvar, TXvar, Dvar, initTimestamp, Qvar,  executed, executeWaitingFlag, relation, recoveryAttemptBal>>


(* 49–60 HandleRecover *)

HandleRecover(m) ==
    /\  m.type = TypeRecover
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            b == m.body.b
            id == m.body.id
            tx == m.body.tx
        IN 
        /\  LET computations == RecoverComputations(s, p, id)
            IN
            LET D == computations.D
                S == computations.S
                W == computations.W
                WP == computations.WP
            IN
            /\  ApplyRecover(s, p, b, id, tx)
            /\  IF S # {}
                THEN msgs' = (msgs \ {m}) \cup {RecoverOkMsg(s, p, sq, q, b, id, abal[s][p][id], txn'[s][p][id], ts[s][p][id], D, phase[s][p][id], TRUE, W, WP)} 
                ELSE msgs' = (msgs \ {m}) \cup {RecoverOkMsg(s, p, sq, q, b, id, abal[s][p][id], txn'[s][p][id], ts[s][p][id], D, phase[s][p][id], FALSE, W, WP)}
    /\ UNCHANGED << submitted, initCoord, dep, abal, ts, phase, recovered, TXvar, Dvar, postWaitingFlag, Wvar, recoveryAttemptBal, initTimestamp, Qvar,  executed, executeWaitingFlag, relation  >>


(* 61–79 + 90-91 HandleRecoverOK *)

HandleRecoverOK(s, p, id) ==
    /\  LET quorumOfMessages ==
        { m \in msgs :
            /\ m.type = TypeRecoverOK
            /\ m.to = p 
            /\ m.body.id = id 
            /\ m.body.b = bal[s][p][id]
            /\ abal[s][p][id] < m.body.b
            /\ m.shardto = s  }
        IN
        /\ IsQuorum(quorumOfMessages, id) 
        /\  LET Q == { <<m.shardfrom,m.from>> : m \in quorumOfMessages  }
                Abals == { m.body.abalq : m \in quorumOfMessages }
                bmax == CHOOSE val \in Abals : \A val2 \in Abals : val >= val2
                U == { m \in quorumOfMessages : m.body.abalq = bmax }
            IN
            /\  IF (\E n \in U :
                        /\ n.body.phaseq  = StablePhase)
                THEN
                        /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = StablePhase
                            IN
                            /\ ApplyCommit(s, p, bal[s][p][id], id, n.body.tq, n.body.depq, n.body.txq, FALSE)
                            /\ ApplyStable(s, p, bal[s][p][id], id)
                            /\ msgs' = (msgs \ quorumOfMessages) \cup {CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, n.body.tq, n.body.depq, Fast, n.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                                                                 \cup {StableMsg(s, p, to[1], to[2], bal[s][p][id], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                            /\ UNCHANGED <<bal, TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = CommittedPhase)
                THEN
                        /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = CommittedPhase
                            IN
                            /\ ApplyCommit(s, p, bal[s][p][id], id, n.body.tq, n.body.depq, n.body.txq, FALSE)
                            /\ msgs' = (msgs \ quorumOfMessages) \cup {CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, n.body.tq, n.body.depq, Slow, n.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }} 
                                                                 \cup {CommitOkMsg(s, p, s, p, bal[s][p][id], id)}
                            /\ UNCHANGED <<bal , TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>  
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = AcceptedPhase)
                THEN    
                        /\  LET n == CHOOSE n \in U :
                                n.body.phaseq = AcceptedPhase
                            IN
                            LET computations == AcceptComputations(s, p, id, n.body.tq)
                            IN  
                            /\ ApplyAccept(s, p, bal[s][p][id], id, n.body.tq, n.body.depq, n.body.txq)
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, n.body.tq, n.body.depq, n.body.txq, Slow) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }} 
                                                                 \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq, Slow)}
                            /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (initCoord[id] \in Q)
                THEN 
                        LET computations == AcceptComputations(s, p, id, ts[s][p][id])
                        IN 
                        /\  ApplyAccept(s, p, bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop)            
                        /\  msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop, Slow) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } 
                                                              \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq, Slow)} 
                        /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                ELSE IF ( \A shard \in idToShard[id] :
                            LET Rmax == { n \in quorumOfMessages :
                                                /\ n.body.phaseq = PreAcceptedPhase
                                                /\ n.shardfrom = shard
                                                /\ n.body.tq = initTimestamp[id] }
                            IN Cardinality(Rmax) >= Cardinality({n \in quorumOfMessages : n.shardfrom = shard}) - E)
                        THEN
                        LET rejects == {m \in quorumOfMessages : m.body.rejectq = TRUE}
                        IN
                        IF (rejects # {} 
                            \/ (\E shard \in idToShard[id] :
                                    LET shardQuorum == {n \in quorumOfMessages : n.shardfrom = shard}
                                    IN ((Cardinality({m \in shardQuorum : m.body.phaseq = PreAcceptedPhase /\ m.body.tq = initTimestamp[id]}) = Cardinality(shardQuorum ) - E)
                                        /\ \E id2 \in UNION {m.body.WPq : m \in shardQuorum} : initCoord[id2] \notin Q ))
                           )   
                        THEN 
                            LET computations == AcceptComputations(s, p, id, ts[s][p][id])
                            IN 
                            /\ ApplyAccept(s, p, bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop)                    
                            /\ msgs' = (msgs\ quorumOfMessages) \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop, Slow) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }} 
                                                                \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq, Slow)} 
                            /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                        ELSE 
                            LET n == CHOOSE n \in quorumOfMessages : n.body.phaseq = PreAcceptedPhase
                                Wall == UNION {(m.body.Wq \cup {<<id1, 0>> : id1 \in {id2 \in m.body.WPq : <<m.shardfrom,m.from>> = initCoord[id2]}}) : m \in quorumOfMessages}
                            IN
                            LET tx == n.body.txq
                                W == {<<id1, bal1>> \in Wall : \A <<id2, bal2>> \in Wall : bal2 <= bal1}
                                D == UNION {m.body.depq : m \in quorumOfMessages}
                            IN
                            /\ TXvar' = [TXvar EXCEPT  ![s][p][id] = tx]
                            /\ Wvar'  = [Wvar  EXCEPT  ![s][p][id] = W]
                            /\ Dvar'  = [Dvar  EXCEPT  ![s][p][id] = D]
                            /\ Qvar'  = [Qvar  EXCEPT  ![s][p][id] = Q]
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = TRUE]
                            /\ recoveryAttemptBal' = [recoveryAttemptBal EXCEPT ![s][p][id] = bal[s][p][id]]
                            /\ msgs' = msgs \ quorumOfMessages
                            /\ UNCHANGED <<bal, txn, abal, ts, dep, phase>>
                ELSE  
                    LET computations == AcceptComputations(s, p, id, ts[s][p][id])
                    IN 
                    /\ ApplyAccept(s, p, bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop)
                    /\ msgs' =   (msgs \ quorumOfMessages)  \cup {AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop, Slow) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }} 
                                                            \cup {AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq, Slow)} 
                    /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
    /\ UNCHANGED <<submitted, initCoord, recovered, initTimestamp,  executed, executeWaitingFlag, relation >>

                 
(* 80–89 HandlePostWaiting *)
                    
HandlePostWaiting(s, p, id) ==
    /\  recoveryAttemptBal[s][p][id] = bal[s][p][id] \* I'm not getting the ballot of corresponding recovery attempt from messages here so I use this extra variable to check we havn't moved ballot.
    /\  postWaitingFlag[s][p][id] = TRUE
    /\  LET W == Wvar[s][p][id]
            b == bal[s][p][id] 
            tx == TXvar[s][p][id]
            D == Dvar[s][p][id]
            Q == Qvar[s][p][id]
            Case1 ==
                \E w \in W :
                    LET id1 == w[1]
                        bal1 == w[2]
                    IN /\ phase[s][p][id1] \in {CommittedPhase, StablePhase}
                    /\ abal[s][p][id1] >= bal1
                    /\ txn[s][p][id1] # Nop
                    /\ LessThanTs(initTimestamp[id], ts[s][p][id1])
                    /\ id \notin dep[s][p][id1]
            Case2 ==
                \A w \in W :
                    LET id1 == w[1]
                        bal1 == w[2]
                    IN /\ phase[s][p][id1] \in {CommittedPhase, StablePhase}
                    /\ abal[s][p][id1] >= bal1
                    /\ (txn[s][p][id1] = Nop \/ LessThanTs(ts[s][p][id1], initTimestamp[id]) \/ id \in dep[s][p][id1])
            Case3 ==
                (\E m \in msgs :
                    /\ m.type = TypeRecoverOK
                    /\ m.body.b = b
                    /\ m.body.id = id
                    /\ m.to = p
                    /\ <<m.shardfrom,m.from>> \notin Q
                    /\ (m.body.phaseq \in {StablePhase, CommittedPhase, AcceptedPhase} \/ <<m.shardfrom,m.from>> = initCoord[id]))
        IN 
        \/  /\  Case1
            /\  LET computations == AcceptComputations(s, p, id, ts[s][p][id])
                IN
                /\ ApplyAccept(s, p, bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop) 
                /\ msgs' = msgs \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop, Slow) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                                \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq, Slow)}
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]

        \/  /\  Case2
            /\  LET computations == AcceptComputations(s, p, id, initTimestamp[id])
                IN 
                /\ ApplyAccept(s, p, bal[s][p][id], id, initTimestamp[id], D, tx)
                /\ msgs' = msgs \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, initTimestamp[id], D, tx, Slow) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                                \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq, Slow)}
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
        \* If I use case 3 here the interpreter doesn't know what m is, which I need in the following. This begs the question why am I
        \* define the cases seperately in the first place : I need to specify that the state doesn't change when none of the 3 cases are verified. (at the end of this handler)
        \/  (\E m \in msgs :
                    /\ m.type = TypeRecoverOK
                    /\ m.body.b = b
                    /\ m.body.id = id
                    /\ m.to = p
                    /\ <<m.shardfrom,m.from>> \notin Q
                    /\ (m.body.phaseq \in {StablePhase, CommittedPhase, AcceptedPhase} \/ <<m.shardfrom,m.from>>  = initCoord[id])
                    /\  IF (m.body.phaseq = StablePhase) THEN
                            /\ ApplyCommit(s, p, b, id, m.body.tq, m.body.depq, m.body.txq, FALSE)
                            /\ ApplyStable(s, p, b, id)               
                            /\ msgs' = msgs \cup { CommitMsg(s, p, to[1], to[2], b, id, m.body.tq, m.body.depq, Fast, m.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                                            \cup { StableMsg(s, p, to[1], to[2], b, id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  }
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                            /\ UNCHANGED bal
                        ELSE IF (m.body.phaseq = CommittedPhase) THEN   
                            /\ ApplyCommit(s, p, b, id, m.body.tq, m.body.depq, m.body.txq, FALSE)
                            /\ msgs' = msgs \cup {CommitMsg(s, p, to[1], to[2], b, id, m.body.tq, m.body.depq, Slow, m.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } 
                                            \cup {CommitOkMsg(s, p, s, p, b, id)}
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                            /\ UNCHANGED bal
                        ELSE IF (m.body.phaseq = AcceptedPhase) THEN 
                            LET computations == AcceptComputations(s, p, id, m.body.tq)
                            IN 
                            /\ ApplyAccept(s, p, b, id, m.body.tq, m.body.depq, m.body.txq)
                            /\ msgs' = msgs \cup { AcceptMsg(s, p, to[1], to[2], b, id, m.body.tq, m.body.depq, m.body.txq, Slow) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } 
                                            \cup { AcceptOKMsg(s, p, s, p, b, id, computations.Dq, Slow)}
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                        ELSE 
                            LET computations == AcceptComputations(s, p, id, ts[s][p][id])
                            IN 
                            /\ ApplyAccept(s, p, bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop)
                            /\ msgs' = msgs \cup { AcceptMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], dep[s][p][id], Nop, Slow) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } 
                                            \cup { AcceptOKMsg(s, p, s, p, bal[s][p][id], id, computations.Dq, Slow)} 
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
            )

        \* If none of the cases are correct, the model checker still has to be explicitly told that the next state is unchanged.
        \/  /\ ~Case1 /\ ~Case2 /\ ~Case3
            /\ UNCHANGED << msgs, postWaitingFlag, bal, dep, phase, abal, txn, ts >>
                    
        
    /\ UNCHANGED << submitted, initCoord, recovered, Wvar, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar,  executed, executeWaitingFlag, relation >>

(***************************************************************************)
(* Execution                                                               *)
(***************************************************************************) 

StartExecute(s, p, id) ==
    /\ <<s,p>> = initCoord[id]
    /\ id \notin  executed[s][p]
    /\ phase[s][p][id] = StablePhase
    /\ txn[s][p][id] # Nop
    /\ executeWaitingFlag[s][p][id] = FALSE
    /\ msgs' = msgs \cup { ReadMsg(s, p, sq, p, id) : sq \in idToShard[id] }
    /\ executeWaitingFlag' = [executeWaitingFlag EXCEPT ![s][p][id] = TRUE]
    /\ UNCHANGED << bal, phase, txn, dep, ts, abal, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar,  executed, relation >>
    
HandleRead(m) ==
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            id == m.body.id
        IN
        /\ phase[s][p][id] = StablePhase
        /\ \A id2 \in dep[s][p][id] : id2 \in executed[s][p]
        /\ msgs' = (msgs \ {m}) \cup {ReadOkMsg(s, p, sq, q, id)}
    /\ UNCHANGED << bal, phase, txn, dep, ts, abal, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar,  executed, executeWaitingFlag, relation >>
    
HandleReadOk(s, p, id) ==
    /\ executeWaitingFlag[s][p][id] = TRUE
    /\  LET readOKs ==
        { m \in msgs :
            /\ m.type = TypeReadOk
            /\ m.to = p 
            /\ m.body.id = id 
            /\ m.shardto = s  }
        IN
        /\ Cardinality(readOKs) = Cardinality(idToShard[id]) \* check that we got answer from everyone.
        /\ msgs' = (msgs \ readOKs) \cup { ApplyMsg(s, p, to[1], to[2], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc }} 
    /\ UNCHANGED << bal, phase, txn, dep, ts, abal, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar,  executed, executeWaitingFlag, relation >>
            
HandleApply(m) == 
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            id == m.body.id
        IN
        /\ id \notin executed[s][p]
        /\ phase[s][p][id] = StablePhase
        /\ \A id2 \in dep[s][p][id] : id2 \in executed[s][p]
        /\ msgs' = msgs \ {m}
        /\ executed' = [executed EXCEPT ![s][p] = executed[s][p] \cup {id}]
        /\ relation' =
            [id1 \in Id |-> 
                [id2 \in Id |->
                IF id1 = id /\ (Conflicts(id, id2) \/ id2 \notin submitted) /\ relation[id1][id2] = 0 THEN 1
                ELSE IF id2 = id /\ (Conflicts(id1, id) \/ id1 \notin submitted) /\ relation[id1][id2] = 0 THEN 2
                ELSE relation[id1][id2]
                ]
            ]
    /\ UNCHANGED << bal, phase, txn, dep, ts, abal, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executeWaitingFlag >>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)                 

Agreement ==
  \A id \in Id : \A p, q \in Proc : \A s \in Shards :
    /\ phase[s][p][id] \in {CommittedPhase, StablePhase}
    /\ phase[s][q][id] \in {CommittedPhase, StablePhase}
    =>  /\ txn[s][p][id] = txn[s][q][id]
        /\ ts[s][p][id] = ts[s][q][id]

Ordering ==
  \A id1, id2 \in Id :
    \A p, q \in Proc : \A s \in Shards  :
      /\ phase[s][p][id1] = StablePhase
      /\ phase[s][q][id2] = CommittedPhase
      /\ txn[s][p][id1] # Nop
      /\ txn[s][q][id2] # Nop
      /\ Conflicts(id1, id2)
      /\ LessThanTs(ts[s][q][id2], ts[s][p][id1])
      => id2 \in dep[s][p][id1]

Edges ==
    { <<i, j>> \in Id \X Id : relation[i][j] = 1 }

RECURSIVE Reach(_,_)

Reach(i, j) ==
    \/ <<i, j>> \in Edges
    \/ \E k \in Id : <<i, k>> \in Edges /\ Reach(k, j)

Acyclicity ==
    \A i \in Id : ~Reach(i, i)
    
Next ==
    \/ \E m \in msgs :
        \/ HandlePreAccept(m) 
        \/ HandleAccept(m)
        \/ HandleCommit(m)
        \/ HandleStable(m)
        \/ HandleRecover(m)

        \/ HandleRead(m)
        \/ HandleApply(m)

    \/ \E s \in Shards, p \in Proc, id \in Id :
        \/ Submit(s, p, id)
        \/ HandlePreAcceptOK(s, p, id) 
        \/ HandleAcceptOK(s, p, id) 
        \/ HandleCommitOK(s, p, id)
        \/ StartRecover(s, p, id)
        \/ HandleRecoverOK(s, p, id)
        \/ HandlePostWaiting(s, p, id) 

        \/ StartExecute(s, p, id)
        \/ HandleReadOk(s, p, id)


Spec ==
    Init /\ [][Next]_<< vars >>

=========================================================================
