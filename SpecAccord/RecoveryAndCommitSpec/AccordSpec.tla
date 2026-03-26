---- MODULE AccordSpec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

VARIABLES
    bal,           \* bal[s][p][id] = current ballot known by in shard s by process p for command id
    phase,         \* phase[s][p][id] ∈ {"none","preaccepted","accepted","committed"}
    txn,           \* txn[s][p][id] = command payload at p
    dep,           \* dep[s][p][id] = final dependency set (accepted or committed)
    ts,            \* ts[s][p][id] = timestamp at p, timestamp is a couple of (t, id) ts.t for timestamp, ts.id for id.
    abal,          \* abal[s][p][id] = last ballot where p accepted a slow-path value
    msgs,           \* multiset of network messages
    submitted,      \* set of submitted command ids
    initCoord,      \* initCoord[id] = process that submitted id, pair <<s,p>>
    initTimestamp,
    recovered,       \* var to limit amount of recovery attempts started
    Wvar,
    TXvar,
    Dvar,
    Qvar,
    postWaitingFlag,
    recoveryAttemptBal,
    executed,    \* executed[p] is a set of ids executed by p
    relation     \* SMR relation to check acyclicity,  relation[id][id] is 0 (no relation) 1 (less than) 2 (greater than)
    
vars == << bal, phase, txn, dep, ts, abal, msgs, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, relation >>



CONSTANTS
    Shards,     \* The set of shards 
    Proc,       \* The set of processes, all shards use same numbered processes
    Id,         \* The set of command IDs
    F, 
    E,
    Bottom,     \* The bottom value for the command payload
    NoProc,      \* A special value representing no process
    Nop,
    NumberOfRecoveryAttempts

\*Phases
(* Initial = 1
   PreAccepted = 2
   Accepted = 3
   Committed = 4
   Stable = 5 *)
CONSTANTS 
    InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase, StablePhase

\* fast or slow path for commit messages
CONSTANTS
    Fast, Slow

ASSUME E<=F

Init == 
    /\ bal = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ phase = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> InitialPhase]]]
    /\ txn = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> Bottom]]]
    /\ dep = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ ts = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> [t |-> 0, id |-> 0]]] ]
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
    /\ initTimestamp = <<[id |-> NoProc, t |-> 0], [id |-> NoProc, t |-> 2], [id |-> NoProc , t |-> 1]>>
    /\ Qvar = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> {}]]]
    /\ executed = [s \in Shards |-> [p \in Proc |-> [id \in Id |-> 0]]]
    /\ relation = [id1 \in Id |-> [id2 \in Id |-> 0]]


N == Cardinality(Proc)

Max(a, b) == IF a > b THEN a ELSE b

LessThanTs(ts1,ts2) ==
    IF ts1.id = NoProc THEN TRUE
    ELSE IF ts2.id = NoProc THEN FALSE
    ELSE IF ts1.t < ts2.t THEN TRUE
    ELSE IF ts1.t > ts2.t THEN FALSE
    ELSE ts1.id < ts2.id

MaxTs(ts1, ts2) ==
    IF LessThanTs(ts1,ts2) THEN ts2 ELSE ts1

MaxTsInSet(S) ==
    CHOOSE ts1 \in S : \A ts2 \in S :
                            ts2 # ts1 => LessThanTs(ts2, ts1)


idToShard == [i \in {1,2,3} |->
                  CASE i = 1 -> {1,3}
                    [] i = 2 -> {1}
                    [] i = 3 -> {2,3}]

ConflictPairs == {
    <<1, 2>>,
    <<1, 3>>
}

ConflictingPayload(id1, id2) ==
    <<id1, id2>> \in ConflictPairs \/ <<id2, id1>> \in ConflictPairs

Conflicts(s, p, idGettingChecked, id2) ==
    IF txn[s][p][id2] = Bottom THEN
        FALSE
    ELSE
        ConflictingPayload(idGettingChecked, id2)


IsQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - F
IsFastQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - E

IsQuorum(set,id) ==
    \A shard \in idToShard[id] :
        LET quorum == {m \in set : m.shardfrom \in shard}
        IN 
        /\ IsQuorumSized(quorum)

IsFastQuorum(set,id) ==
    \A shard \in idToShard[id] :
        LET quorum == {m \in set : m.shardfrom \in shard}
        IN 
        /\ IsFastQuorumSized(quorum)

SeenIds(s,p) ==
    {id \in Id : 
        \/ txn[s][p][id] # Bottom
        \/ \E id2 \in Id : id \in dep[s][p][id2]}

        




ASSUME N >= Max(2*E+F-1, 2*F+1)


\* Message types
(* 1 = PreAccept
2 = PreAcceptOK
3 = Accept
4 = AcceptOK
5 = Commit
6 = CommitOK
7 = Stable
8 = Recover
9 = RecoverOK
*)
CONSTANTS 
TypePreAccept,
TypePreAcceptOK,
TypeAccept,     
TypeAcceptOK,    
TypeCommit,
TypeCommitOK,
TypeStable,
TypeRecover,
TypeRecoverOK 

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

AcceptMsg(sp, p, sq, q, b, id, t, D, tx) ==
    Message(TypeAccept, sp, p, sq, q,
        [ id   |-> id,
          b  |-> b,
          t |-> t,
          tx |-> tx,
          D |-> D ])

AcceptOKMsg(sp, p, sq, q, b, id, Dq) ==
    Message(TypeAcceptOK, sp, p, sq, q,
        [ id  |-> id,
          b |-> b,
          Dq |-> Dq ])

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

RecoverMsg(sp, p, sq, q,b,id,tx) ==
    Message(TypeRecover, sp, p, sq, q,
        [id   |-> id,
          b  |-> b,
          tx |-> tx])

RecoverOkMsg(sp, p, sq, q,b,id,abalq,txq,tq,depq,phaseq,rejectq,Wq,WPq) ==
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

(***************************************************************************)
(* State changing Actions                                                  *)
(***************************************************************************)

ApplyPreAccept(sp, p, id, tx, finalTs, D0) ==
    /\  bal[sp][p][id] = 0
    /\  phase[sp][p][id] = InitialPhase
    /\  txn' = [txn EXCEPT ![sp][p][id] = tx]
    /\  phase' = [phase EXCEPT ![sp][p][id] = PreAcceptedPhase]
    /\  ts' = [ts EXCEPT ![sp][p][id] = finalTs]
    /\  dep' = [dep EXCEPT ![sp][p][id] = D0]

ApplyAccept(sp, p, b,id,t,D,tx) ==
    /\  bal[sp][p][id] <= b
    /\  (b = 0 => phase[sp][p][id] = PreAcceptedPhase)
    /\  IF b > 0 THEN txn'  = [txn  EXCEPT ![sp][p][id] = tx] ELSE UNCHANGED txn
    /\  bal'  = [bal  EXCEPT ![sp][p][id] = b]
    /\  abal' = [abal EXCEPT ![sp][p][id] = b]
    /\  ts'   = [ts  EXCEPT ![sp][p][id] = t]
    /\  dep'  = [dep  EXCEPT ![sp][p][id] = D]
    /\  phase' = [phase EXCEPT ![sp][p][id] = AcceptedPhase]

ApplyCommit(sp, p, b,id,t,D,tx) ==
    /\ bal[sp][p][id] = b
    /\ b = 0 => phase[sp][p][id] \in {PreAcceptedPhase, AcceptedPhase}
    /\ IF b > 0 THEN txn'  = [txn  EXCEPT ![sp][p][id] = tx] ELSE UNCHANGED txn
    /\ abal' = [abal EXCEPT ![sp][p][id] = b]
    /\ ts'   = [ts  EXCEPT ![sp][p][id] = t]
    /\ dep' = [dep EXCEPT ![sp][p][id] = D]
    /\ phase' = [phase EXCEPT ![sp][p][id] = CommittedPhase]

ApplyStable(sp, p, b,id) ==
        /\ bal[sp][p][id] = b
        /\ phase[sp][p][id] = CommittedPhase
        /\ phase' = [phase EXCEPT ![sp][p][id] = StablePhase]

ApplyRecover(sp, p, b, id, tx) ==
        /\  bal[sp][p][id] < b
        /\  bal'  = [bal  EXCEPT ![sp][p][id] = b]
        /\  IF phase[sp][p][id] = InitialPhase THEN  txn'  = [txn  EXCEPT ![sp][p][id] = tx] ELSE UNCHANGED txn

    


(***************************************************************************)
(* Message handling Actions                                                  *)
(***************************************************************************)

(***************************************************************************)
(* 4–6 Submit                                                              *)
(***************************************************************************)

Submit(s, p, id) ==
    /\  id \notin submitted
    /\  LET tx == id \* I just use Id as command payload, the actual payload does not matter. Conflict relation is defined on these id integers.
            earlierInitTimestamps == {initTimestamp[id2] : id2 \in {id1 \in Id : initCoord[id1] = <<s,p>> /\ LessThanTs(initTimestamp[id],initTimestamp[id1])}}
        IN 
        /\ LET initTimestampVal == IF earlierInitTimestamps = {} THEN initTimestamp[id].t ELSE MaxTsInSet(earlierInitTimestamps).t + 1
            IN
            /\ initTimestamp' = [initTimestamp EXCEPT ![id] = [id |-> p, t |-> initTimestampVal]]
            /\ submitted' = submitted \cup {id}
            /\ initCoord' = [initCoord EXCEPT ![id] = <<s,p>>]
            /\ ts' = [ts EXCEPT ![s][p][id] = initTimestamp'[id]]
            \* This part has computations of the handle pre accept part because we have to immediately handle the self addressed message, this is a recurring pattern whenever we broadcast.
            /\  LET setOfConflictingTs == {ts[s][p][id2] : id2 \in { id2 \in Id : ts[s][p][id2].id # NoProc /\ Conflicts(s, p, id, id2)}}
                    D == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp'[id]) ) }
                IN
                /\  LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
                    IN
                    /\  LET finalTs == MaxTs(initTimestamp'[id], [t |-> tval, id |-> p])
                            
                        IN
                        /\ msgs' = msgs \cup { PreAcceptMsg(s, p, to[1], to[2], id, tx, D) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } \cup {PreAcceptOKMsg(s, p, s, p,id,finalTs,D)}
                        /\ ApplyPreAccept(s,p,id,tx,finalTs,D)
    /\ UNCHANGED << bal, abal, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, executed, relation >> 

(***************************************************************************)
(* 7–15 HandlePreAccept                                                    *)
(***************************************************************************)                    

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
        /\  LET setOfConflictingTs == {ts[s][p][id2] : id2 \in { id2 \in Id : ts[s][p][id2].id # NoProc /\ Conflicts(s, p, id, id2)}}
                D == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
                IN
                /\  txn' = [txn EXCEPT ![s][p][id] = tx]
                /\  LET finalTs == MaxTs(initTimestamp[id], [t |-> tval, id |-> q])
                    IN
                    /\ ApplyPreAccept(s,p,id,tx,finalTs,D0)
                    /\ msgs' = (msgs \cup { PreAcceptOKMsg(s, p, sq, q, id, finalTs, D) }) \ {m}
    /\ UNCHANGED << bal, abal, submitted, initCoord, recovered, postWaitingFlag, recoveryAttemptBal, initTimestamp, TXvar, Dvar, Wvar, Qvar, executed, relation>>


(***************************************************************************)
(* 16–23 HandlePreAcceptOk                                                      *)
(***************************************************************************)


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
        /\ IsQuorum(quorumOfMessages,id)
        \* I build the set of fast quorums from the messages, check if there is at least one, and CHOOSE it deterministically
        /\  LET largestFastQuorum ==
                { m \in quorumOfMessages : m.body.tq = initTimestamp[id]  }
            IN
            IF IsFastQuorum(largestFastQuorum,id) THEN
                    LET D == dep[s][p][id] \cup UNION { m.body.Dq : m \in largestFastQuorum }
                    IN
                    /\ ApplyCommit(s,p,0,id,initTimestamp[id],D,txn[s][p][id])
                    /\ ApplyStable(s,p,0,id)               
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(s, p, to[1], to[2], 0, id, initTimestamp[id], D, Fast, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                                                         \cup { StableMsg(s, p, to[1], to[2], 0, id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                    /\ UNCHANGED bal
            ELSE     
                /\  LET D == UNION { m.body.Dq : m \in quorumOfMessages }
                        t == MaxTsInSet({ m.body.tq : m \in quorumOfMessages })
                    IN
                    LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], t)) }
                    IN 
                    /\ ApplyAccept(s,p,0,id,t,D,txn[s][p][id])
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s, p, to[1], to[2], 0, id, t, D, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  } \cup {AcceptOKMsg(s,p,s,p,0,id,Dq)}
    /\ UNCHANGED <<  submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, relation  >>
       

(***************************************************************************)
(* 24–32 HandleAccept                                                      *)
(***************************************************************************)                            

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
        IN
        /\  ApplyAccept(s,p,b,id,t,D,tx)
        /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], t)) }
            IN
            /\ msgs' = (msgs \cup { AcceptOKMsg(s, p, sq, q, b, id, Dq) }) \ {m}
    /\ UNCHANGED << submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, relation  >>

(***************************************************************************)
(* 33–35 HandleAcceptOk                                                    *)
(***************************************************************************)

HandleAcceptOK(s, p, id) ==
    /\ phase[s][p][id] = AcceptedPhase
    /\ LET quorumOfMessages == { m \in msgs :
        /\ m.type = TypeAcceptOK
        /\ m.to = p
        /\ m.body.b = bal[s][p][id] \*Ballot precondition is here
        /\ m.body.id = id
        /\ m.shardto = s }   
        IN
        /\ IsQuorum(quorumOfMessages, id)
        /\  LET D == dep[s][p][id] \cup UNION { m.body.Dq : m \in quorumOfMessages }
            IN
            /\ msgs' = (msgs \cup {CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, ts[s][p][id], D, Slow, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  } \cup {CommitOkMsg(s,p,s,p,bal[s][p][id],id)}) \ quorumOfMessages
            /\ ApplyCommit(s, p, bal[s][p][id], id, ts[s][p][id], D, txn[s][p][id])
    /\ UNCHANGED << bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, relation >>

(***************************************************************************)
(* 36–44 HandleCommit                                                      *)
(***************************************************************************)

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
       /\ ApplyCommit(s,p,b,id,t,D,tx)
       /\ IF fastOrSlow = Slow THEN msgs' = (msgs \cup { CommitOkMsg(s,p,sq, q, b, id) } ) \ {m} ELSE msgs' = msgs \ {m}
       /\ UNCHANGED << bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, initTimestamp, executed, relation >>



(***************************************************************************)
(* 45–47 HandleCommitOk                                                    *)
(***************************************************************************)

HandleCommitOK(s, p, id) ==
    /\ phase[s][p][id] = CommittedPhase
    /\ LET quorumOfMessages == { m \in msgs :
        /\ m.type = TypeCommitOK
        /\ m.to = p
        /\ m.body.b = bal[s][p][id] \*Ballot precondition is here
        /\ m.body.id = id
        /\ m.shardto = s }   
        IN
        /\ IsQuorum(quorumOfMessages,id)
        /\ msgs' = (msgs \cup {StableMsg(s, p, to[1], to[2], bal[s][p][id], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  }) \ quorumOfMessages
        /\ ApplyStable(s,p,bal[s][p][id],id)
    /\ UNCHANGED << bal, txn, dep, ts, abal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, relation >>

(***************************************************************************)
(* 48–50 HandleStable                                                      *)
(***************************************************************************)

HandleStable(m) ==
    /\ m.type = TypeStable
    /\  LET s == m.shardto
            p  == m.to
            sq == m.shardfrom
            q  == m.from
            b  == m.body.b
            id == m.body.id
        IN
        /\ ApplyStable(s,p,b,id)
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED << bal, submitted, initCoord, dep, abal, txn, ts, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, relation >>

(***************************************************************************)
(* 51–54 StartRecover                                                      *)
(***************************************************************************)

StartRecover(s,p,id) ==
    /\ recovered[s][p][id] < NumberOfRecoveryAttempts
    /\ id \in SeenIds(s,p)
    /\ s \in idToShard[id]
    /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE] 
    /\ recovered' = [recovered EXCEPT ![s][p][id] = recovered[s][p][id] + 1]
    \* Ballots owned by p are of the form k*N + p.
    /\  LET k == ((bal[s][p][id] - p + N) \div N) IN
        LET b == k * N + p
        IN
        /\  ApplyRecover(s, p, b, id, txn[s][p][id])
        /\  LET D == IF phase[s][p][id] # InitialPhase THEN dep[s][p][id]
                     ELSE {id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET S == {id2 \in SeenIds(s,p) : (id2 # id /\ Conflicts(s, p, id, id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2]
                        /\(   (phase[s][p][id2] \in {CommittedPhase, StablePhase} /\ LessThanTs(initTimestamp[id], ts[s][p][id2]))  
                            \/ (   phase[s][p][id2] = AcceptedPhase   /\   LessThanTs( initTimestamp[id] ,  initTimestamp[id2])) 
                          )                    ) 
                        }
                    W == {<<id3,abal[s][p][id3]>> : id3 \in { id2 \in SeenIds(s,p) : (id2 # id /\ Conflicts(s, p, id, id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2] 
                        /\ (  (phase[s][p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) /\ LessThanTs(initTimestamp[id],ts[s][p][id2]))
                           \/ (phase[s][p][id2] = PreAcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) )
                           )
                        )}}
                    WP == {id2 \in SeenIds(s,p) : id2 # id /\ Conflicts(s, p, id, id2) /\ phase[s][p][id2] = PreAcceptedPhase 
                            /\ LessThanTs(initTimestamp[id],initTimestamp[id2]) /\ id \notin dep[s][p][id2] }
                IN
                IF S # {}
                THEN IF phase[s][p][id] # InitialPhase THEN msgs' = (msgs \cup {RecoverOkMsg(s,p,s,p,b,id,abal[s][p][id],txn[s][p][id],ts[s][p][id],D,phase[s][p][id],TRUE,W,WP)} \cup  { RecoverMsg(s,p,to[1], to[2],b,id,txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  })
                     ELSE msgs' =  msgs \cup {RecoverOkMsg(s,p,s,p,b,id,abal[s][p][id],txn[s][p][id],ts[s][p][id],D,phase[s][p][id],TRUE,W,WP)} \cup { RecoverMsg(s,p,to[1], to[2],b,id,Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                ELSE IF phase[s][p][id] # InitialPhase THEN msgs' = (msgs \cup {RecoverOkMsg(s,p,s,p,b,id,abal[s][p][id],txn[s][p][id],ts[s][p][id],D,phase[s][p][id],FALSE,W,WP)} \cup  { RecoverMsg(s,p,to[1], to[2],b,id,txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  })
                     ELSE msgs' =  msgs \cup {RecoverOkMsg(s,p,s,p,b,id,abal[s][p][id],txn[s][p][id],ts[s][p][id],D,phase[s][p][id],FALSE,W,WP)} \cup { RecoverMsg(s,p,to[1], to[2],b,id,Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  }
    /\ UNCHANGED <<phase, dep, ts, abal, submitted, initCoord, Wvar, TXvar, Dvar, initTimestamp, Qvar, recoveryAttemptBal, executed, relation>>

(***************************************************************************)
(* 55–68 HandleRecover                                                     *)
(***************************************************************************)

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
        /\  ApplyRecover(s, p, b, id, tx)
        /\  LET D == IF phase[s][p][id] \notin {InitialPhase,PreAcceptedPhase} THEN dep[s][p][id]
                     ELSE dep[s][p][id] \cup {id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET S == {id2 \in SeenIds(s,p) : (id2 # id /\ Conflicts(s, p, id, id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2]
                        /\(   (phase[s][p][id2] \in {CommittedPhase, StablePhase} /\ LessThanTs(initTimestamp[id], ts[s][p][id2]))  
                            \/ (   phase[s][p][id2] = AcceptedPhase   /\   LessThanTs( initTimestamp[id] ,  initTimestamp[id2])) 
                          )                    ) 
                        }
                    W == {<<id3,abal[s][p][id3]>> : id3 \in { id2 \in SeenIds(s,p) : (id2 # id /\ Conflicts(s, p, id, id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2] 
                        /\ (  (phase[s][p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) /\ LessThanTs(initTimestamp[id],ts[s][p][id2]))
                           \/ (phase[s][p][id2] = PreAcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) )
                           )
                        )}}
                    WP == {id2 \in SeenIds(s,p) : id2 # id /\ Conflicts(s, p, id, id2) /\ phase[s][p][id2] = PreAcceptedPhase 
                            /\ LessThanTs(initTimestamp[id],initTimestamp[id2]) /\ id \notin dep[s][p][id2] }
                IN
                IF S # {}
                THEN msgs' = (msgs \cup {RecoverOkMsg(s,p,sq,q,b,id,abal[s][p][id],txn'[s][p][id],ts[s][p][id],D,phase[s][p][id],TRUE,W,WP)}) \ {m} 
                ELSE msgs' = (msgs \cup {RecoverOkMsg(s,p,sq,q,b,id,abal[s][p][id],txn'[s][p][id],ts[s][p][id],D,phase[s][p][id],FALSE,W,WP)}) \ {m}
    /\ UNCHANGED << submitted, initCoord, dep, abal, ts, phase, recovered, TXvar, Dvar, postWaitingFlag, Wvar, recoveryAttemptBal, initTimestamp, Qvar, executed, relation  >>

(***************************************************************************)
(* 69–85 HandleRecoverOK                                                   *)
(***************************************************************************)

HandleRecoverOK(s, p, id) ==
    /\  LET quorumOfMessages ==
        { m \in msgs :
            /\ m.type = TypeRecoverOK
            /\ m.to = p 
            /\ m.body.id = id 
            /\ m.body.b = bal[s][p][id] \* ballot precondition is here
            /\ abal[s][p][id] < m.body.b
            /\ m.shardto = s  }
        IN
        /\ IsQuorum(quorumOfMessages,id) 
        /\  LET Q == { m.from : m \in quorumOfMessages}
                Abals == { m.body.abalq : m \in quorumOfMessages }
                bmax == CHOOSE val \in Abals : \A val2 \in Abals : val >= val2
                U == { m \in quorumOfMessages : m.body.abalq = bmax }
                \* Dq is used when sending an accept message, to treat the self addressed one because we need it when sending AcceptOK.
            IN
            /\  IF (\E n \in U :
                        /\ n.body.phaseq  = StablePhase)
                THEN
                        /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = StablePhase
                            IN
                            /\ msgs' = (msgs \cup {CommitMsg(s,p, to[1], to[2], bal[s][p][id], id, n.body.tq, n.body.depq, Fast, n.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                                             \cup {StableMsg(s,p, to[1], to[2], bal[s][p][id], id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  }) \ quorumOfMessages
                            /\ ApplyCommit(s, p, bal[s][p][id], id, n.body.tq, n.body.depq, n.body.txq)
                            /\ ApplyStable(s, p, bal[s][p][id], id)
                            /\ UNCHANGED <<bal, TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = CommittedPhase)
                THEN
                        /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = CommittedPhase
                            IN
                            LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], n.body.tq) ) }
                            IN 
                            /\ msgs' = (msgs \cup {CommitMsg(s, p, to[1], to[2], bal[s][p][id], id, n.body.tq, n.body.depq, Slow, n.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {CommitOkMsg(s,p,s,p,bal[s][p][id],id)}) \ quorumOfMessages
                            /\ ApplyCommit(s, p, bal[s][p][id], id, n.body.tq, n.body.depq, n.body.txq)
                            /\ UNCHANGED <<bal ,TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>  
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = AcceptedPhase)
                THEN    
                        /\  LET n == CHOOSE n \in U :
                                n.body.phaseq = AcceptedPhase
                            IN
                            /\  ApplyAccept(s,p,bal[s][p][id],id,n.body.tq,n.body.depq,n.body.txq)
                            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], n.body.tq) ) }
                                IN 
                                /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,n.body.tq,n.body.depq,n.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)}
                                /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (initCoord[id] \in Q)
                THEN 
                        /\ ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
                        /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                            IN
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)} 
                        /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                ELSE IF (   LET Rmax == { n \in quorumOfMessages :
                                                /\ n.body.phaseq = PreAcceptedPhase
                                                /\ n.body.tq = initTimestamp[id] }
                            IN Cardinality(Rmax) >= Cardinality(quorumOfMessages) - E)
                        THEN
                        LET rejects == {m \in quorumOfMessages : m.body.rejectq = TRUE}
                        IN
                        IF (rejects # {} 
                            \/ ((Cardinality({m \in quorumOfMessages : m.body.phaseq = PreAcceptedPhase /\ m.body.tq = initTimestamp[id]}) = Cardinality(quorumOfMessages) - E)
                                /\ \E id2 \in UNION {m.body.WPq : m \in quorumOfMessages} : initCoord[id2] \notin Q ))
                        THEN 
                            /\ ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
                            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                                IN
                                /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)} 
                            /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                        ELSE 
                            LET n == CHOOSE n \in quorumOfMessages : n.body.phaseq = PreAcceptedPhase
                                Wall == UNION {(m.body.Wq \cup {<<id1, 0>> : id1 \in {id2 \in m.body.WPq : m.from = initCoord[id2]}}) : m \in quorumOfMessages}
                            IN
                            LET tx == n.body.txq
                                W == {<<id1, bal1>> \in Wall : \A <<id2, bal2>> \in Wall : bal2 <= bal1}
                                D == UNION {m.body.depq : m \in quorumOfMessages}
                            IN
                            /\ TXvar' = [TXvar EXCEPT  ![s][p][id] = tx]
                            /\ Wvar' = [Wvar EXCEPT  ![s][p][id] = W]
                            /\ Dvar' = [Dvar EXCEPT  ![s][p][id] = D]
                            /\ Qvar' = [Qvar EXCEPT  ![s][p][id] = Q]
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = TRUE]
                            /\ recoveryAttemptBal' = [recoveryAttemptBal EXCEPT ![s][p][id] = bal[s][p][id]]
                            /\ msgs' = msgs \ quorumOfMessages
                            /\ UNCHANGED <<bal, txn, abal, ts, dep, phase>>
                ELSE  
                    /\ ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
                    /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                        IN
                        /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)} 
                        /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
    /\ UNCHANGED <<submitted, initCoord, recovered, initTimestamp, executed, relation >>
            
(***************************************************************************)
(* 86–95 HandlePostWaiting                                                 *)
(***************************************************************************)
                    
HandlePostWaiting(s, p, id) ==
    /\  recoveryAttemptBal[s][p][id] = bal[s][p][id] \* I'm not getting the ballot of corresponding recovery attempt from messages here so I use this extra variable to check ballot.
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
                    IN /\ phase[s][p][id1] \in {CommittedPhase,StablePhase}
                    /\ abal[s][p][id1] >= bal1
                    /\ txn[s][p][id1] # Nop
                    /\ LessThanTs(initTimestamp[id], ts[s][p][id1])
                    /\ id \notin dep[s][p][id1]
            Case2 ==
                \A w \in W :
                    LET id1 == w[1]
                        bal1 == w[2]
                    IN /\ phase[s][p][id1] \in {CommittedPhase,StablePhase}
                    /\ abal[s][p][id1] >= bal1
                    /\ txn[s][p][id1] # Nop
                    /\ (LessThanTs(ts[s][p][id1], initTimestamp[id]) \/ id \in dep[s][p][id1])
            Case3 ==
                (\E m \in msgs :
                    /\ m.type = TypeRecoverOK
                    /\ m.from \notin Q
                    /\ (m.body.phaseq \in {StablePhase,CommittedPhase,AcceptedPhase} \/ m.from = initCoord[id]))
        IN 
        \/  /\ Case1
            /\  ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                IN 
                /\ msgs' = msgs \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                            \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)}
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]

        \/  /\ Case2
            /\ ApplyAccept(s,p,bal[s][p][id],id,initTimestamp[id],D,tx)
            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                IN 
                /\ msgs' = msgs \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,initTimestamp[id],D,tx) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                            \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)}
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
        \/  (\E m \in msgs :
                    /\ m.type = TypeRecoverOK
                    /\ m.body.b = b
                    /\ m.body.id = id
                    /\ m.to = p
                    /\ m.from \notin Q
                    /\ (m.body.phaseq \in {StablePhase,CommittedPhase,AcceptedPhase} \/ m.from = initCoord[id])
                    /\  IF (m.body.phaseq = StablePhase) THEN
                            /\ ApplyCommit(s,p,b,id,m.body.tq,m.body.depq,m.body.txq)
                            /\ ApplyStable(s,p,b,id)               
                            /\ msgs' = msgs \cup { CommitMsg(s,p,to[1], to[2],b,id,m.body.tq,m.body.depq,Fast,m.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                                            \cup { StableMsg(s,p,to[1], to[2],b,id) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  }
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                            /\ UNCHANGED bal
                        ELSE IF (m.body.phaseq = CommittedPhase) THEN   
                            /\ msgs' = (msgs \cup {CommitMsg(s,p,to[1], to[2],b,id,m.body.tq,m.body.depq,Slow,m.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {CommitOkMsg(s,p,s,p,b,id)})
                            /\ ApplyCommit(s,p,b,id,m.body.tq,m.body.depq,m.body.txq)
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                            /\ UNCHANGED bal
                        ELSE IF (m.body.phaseq = AcceptedPhase) THEN 
                            LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2],m.body.tq)) }
                            IN 
                            /\ ApplyAccept(s,p,b,id,m.body.tq,m.body.depq,m.body.txq)
                            /\ msgs' = msgs \cup { AcceptMsg(s,p,to[1], to[2],b,id,m.body.tq,m.body.depq,m.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,b,id,Dq)}
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                        ELSE 
                            /\ ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
                            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(s, p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                                IN
                                /\ msgs' = msgs \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)} 
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
            )

        \/  /\ ~Case1 /\ ~Case2 /\ ~Case3
            /\ UNCHANGED << msgs, postWaitingFlag, bal, dep, phase, abal, txn, ts >>
                    
        
    /\ UNCHANGED << submitted, initCoord, recovered, Wvar, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar, executed, relation >>


(***************************************************************************)
(* Execution                                                               *)
(***************************************************************************)  

Execute(s,p,id) ==
    /\ executed[s][p][id] = 0
    /\ phase[s][p][id] = StablePhase
    /\ \A id2 \in dep[s][p][id] :
        /\ phase[s][p][id2] \in {CommittedPhase,StablePhase}
        /\ LessThanTs(ts[s][p][id2],ts[s][p][id]) => executed[s][p][id] # 0
    /\  LET S == {executed[s][p][id2] : id2 \in Id}
        IN  
        LET nextInOrder ==  (CHOOSE i \in S : \A j \in S : i >= j ) + 1
        IN 
        /\ executed' = [executed EXCEPT ![s][p][id] = nextInOrder]
    
    /\ relation' =
            [id1 \in Id |-> 
                [id2 \in Id |->
                IF id1 = id /\ (ConflictingPayload(id, id2) \/ id2 \notin submitted) /\ relation[id1][id2] = 0 THEN 1
                ELSE IF id2 = id /\ (ConflictingPayload(id, id1) \/ id1 \notin submitted) /\ relation[id1][id2] = 0 THEN 2
                ELSE relation[id1][id2]
                ]
            ]

    /\ UNCHANGED << bal, phase, txn, dep, ts, abal, msgs, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)                 

Agreement ==
  \A id \in Id : \A p, q \in Proc, s \in Shards :
    /\ phase[s][p][id] \in {CommittedPhase,StablePhase}
    /\ phase[s][q][id] \in {CommittedPhase,StablePhase}
    =>  /\ txn[s][p][id] = txn[s][q][id]
        /\ ts[s][p][id] = ts[s][q][id]

Ordering ==
  \A id1, id2 \in Id :
    \A p, q \in Proc, s \in Shards  :
      /\ phase[s][p][id1] = StablePhase
      /\ phase[s][q][id2] = CommittedPhase
      /\ txn[s][p][id1] # Nop
      /\ txn[s][q][id2] # Nop
      /\ ConflictingPayload(id1, id2)
      /\ LessThanTs(ts[s][q][id2],ts[s][p][id1])
      => id2 \in dep[s][p][id1]

PartialOrder == 
    \A id1, id2 \in Id :
        ConflictingPayload(id1,id2)
        =>  /\ \A p, q \in Proc, s \in Shards  :
                (txn[s][p][id1] # Nop /\ txn[s][p][id2] # Nop /\ txn[s][q][id1] # Nop /\ txn[s][q][id2] # Nop)
                => ((executed[s][p][id1] # 0 /\ executed[s][p][id2] # 0 /\ executed[s][q][id1] # 0 /\ executed[s][q][id2] # 0 )
                => (executed[s][p][id1] < executed[s][p][id2] => executed[s][q][id1] < executed[s][q][id2]) )

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

    \/ \E s \in Shards, p \in Proc, id \in Id :
        \/ Submit(s, p, id)
        \/ HandlePreAcceptOK(s, p, id) 
        \/ HandleAcceptOK(s, p, id) 
        \/ HandleCommitOK(s, p, id)
        \/ StartRecover(s, p,id)
        \/ HandleRecoverOK(s, p, id)
        \/ HandlePostWaiting(s, p, id)

        \/ Execute(s, p,id) 


Spec ==
    Init /\ [][Next]_<< vars >>

=========================================================================
