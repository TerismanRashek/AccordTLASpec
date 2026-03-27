---- MODULE AccordSpec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

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
    recoveryAttemptBal

vars == << bal, phase, txn, dep, ts, abal, msgs, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar >>


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

\*Phase constants
(* Initial = 1, PreAccepted = 2, Accepted = 3, Committed = 4, Stable = 5 *)
CONSTANTS 
    InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase, StablePhase

\* fast or slow path values for commit messages
CONSTANTS
    Fast, Slow

\* Constants for Message types
(* 1 = PreAccept, 2 = PreAcceptOK, 3 = Accept, 4 = AcceptOK, 5 = Commit, 6 = CommitOK, 7 = Stable, 8 = Recover, 9 = RecoverOK *)
CONSTANTS 
TypePreAccept, TypePreAcceptOK, TypeAccept, TypeAcceptOK, TypeCommit, TypeCommitOK, TypeStable, TypeRecover, TypeRecoverOK 

\* The next three constants cannot be parsed by the config file because it has a reduced grammar, they are defined here,
\* to change the configuration ( specifically to change the number/config of the transactions), the must be changed here.

\* constant that maps to each command that command's the set of shards,
idToShard == [i \in {1,2,3} |->
                  CASE i = 1 -> {1,2,3}
                    [] i = 2 -> {1,2}
                    [] i = 3 -> {3}]

\*constant to define the conflict relation,
ConflictPairs == {
    <<1, 2>>,
    <<1, 3>>
}

\* Constant to define initial timestamp values for the commands, injected into initTimestamp var, this value can be redefined on submission when necessary
\* (a single process can't submit a second command with a lower timestamp than the first), the id is defined on submission.
initTimestampConstant == <<[id |-> <<0, NoProc>>, t |-> 0], [id |-> <<0, NoProc>>, t |-> 2], [id |-> <<0, NoProc>> , t |-> 1]>>


(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)

N == Cardinality(Proc)
Nshards == Cardinality(Shards)

Max(a, b) == IF a > b THEN a ELSE b

\* Relations on timestamps 
LessThanTs(ts1,ts2) ==
    IF ts1.t < ts2.t THEN TRUE
    ELSE IF ts1.t > ts2.t THEN FALSE
    ELSE IF ts1.id[2] = ts2.id[2] THEN ts1.id[1] < ts2.id[1]
    ELSE ts1.id[2] < ts2.id[2]

MaxTs(ts1, ts2) ==
    IF LessThanTs(ts1,ts2) THEN ts2 ELSE ts1

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
IsQuorum(set,id) ==
    \A shard \in idToShard[id] :
        LET quorum == {m \in set : m.shardfrom = shard}
        IN 
        /\ IsQuorumSized(quorum)

IsFastQuorum(set,id) ==
    \A shard \in idToShard[id] :
        LET quorum == {m \in set : m.shardfrom = shard}
        IN 
        /\ IsFastQuorumSized(quorum)

\* This finds all commands that a process knows of, (checks in payload and in dependencies)
SeenIds(s,p) ==
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

\*These operations are the insides of all the 'when received' a single message operations, this split allows me to handle self addressed
\* messages by simply calling the corresponding Apply operation. 

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
(* Message handling Actions                                                *)
(***************************************************************************)


(* 1–3 Submit *)

Submit(s, p, id) ==
    /\  id \notin submitted
    \* I am checking that the initial coordinator is part of the shards of that transaction. It seems like a reasonable assumption,
    \* if I remove it, I would address a 'self sent message' that does not exist. This does not seem to actually create a bug(minimal testing was done) 
    /\  s \in idToShard[id] 
    /\  LET tx == id        \* I just use Id as command payload, the actual payload does not matter. Conflict relation is defined on these id integers.
            earlierInitTimestamps == {initTimestamp[id2] : id2 \in {id1 \in Id : initCoord[id1] = <<s,p>> /\ LessThanTs(initTimestamp[id],initTimestamp[id1])}}
        IN 
        \* making sure that this process has not already submitted a command with a greater timestamp than the one we are currently submitting.
        /\ LET initTimestampVal == IF earlierInitTimestamps = {} THEN initTimestamp[id].t ELSE MaxTsInSet(earlierInitTimestamps).t + 1
            IN
            /\ initTimestamp' = [initTimestamp EXCEPT ![id] = [id |-> <<s,p>>, t |-> initTimestampVal]]
            /\ submitted' = submitted \cup {id}
            /\ initCoord' = [initCoord EXCEPT ![id] = <<s,p>>]
            /\ ts' = [ts EXCEPT ![s][p][id] = initTimestamp'[id]]
            \* This part has computations of the handle pre accept part because we have to immediately handle the self addressed message (and send the resulting PreAcceptOk message), this is a recurring pattern whenever we broadcast and handle the self addressed message immediately.
            /\  LET setOfConflictingTs == {ts[s][p][id2] : id2 \in { id2 \in Id : ts[s][p][id2].id # <<0,NoProc>> /\ Conflicts(id,id2)}}
                    D == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp'[id]) ) }
                IN
                /\  LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
                    IN
                    /\  LET finalTs == MaxTs(initTimestamp'[id], [t |-> tval, id |-> <<s,p>>])
                            
                        IN
                        /\ ApplyPreAccept(s,p,id,tx,finalTs,D)
                        \* I send PreAcceptMsg to everyone except myself, for my message, I apply the operation and then send the PreAcceptOkMsg directly.
                        \* This pattern is the same at every point where we broadacst
                        /\ msgs' = msgs \cup { PreAcceptMsg(s, p, to[1], to[2], id, tx, D) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } } 
                                        \cup { PreAcceptOKMsg(s, p, s, p,id,finalTs,D)}
    /\ UNCHANGED << bal, abal, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar >> 


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
        /\  LET setOfConflictingTs == {ts[s][p][id2] : id2 \in { id2 \in Id : ts[s][p][id2].id # <<0,NoProc>> /\ Conflicts(id,id2)}}
                D == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
                IN 
                /\  txn' = [txn EXCEPT ![s][p][id] = tx]
                /\  LET finalTs == MaxTs(initTimestamp[id], [t |-> tval, id |-> <<sq,q>>])
                    IN
                    /\ ApplyPreAccept(s,p,id,tx,finalTs,D0)
                    /\ msgs' = (msgs \cup { PreAcceptOKMsg(s, p, sq, q, id, finalTs, D) }) \ {m}
    /\ UNCHANGED << bal, abal, submitted, initCoord, recovered, postWaitingFlag, recoveryAttemptBal, initTimestamp, TXvar, Dvar, Wvar, Qvar>>



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
                    LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], t)) }
                    IN 
                    /\ ApplyAccept(s,p,0,id,t,D,txn[s][p][id])
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s, p, to[1], to[2], 0, id, t, D, txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  } \cup {AcceptOKMsg(s,p,s,p,0,id,Dq)}
    /\ UNCHANGED <<  submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar  >>
       

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
        IN
        /\  ApplyAccept(s,p,b,id,t,D,tx)
        /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], t)) }
            IN
            /\ msgs' = (msgs \cup { AcceptOKMsg(s, p, sq, q, b, id, Dq) }) \ {m}
    /\ UNCHANGED << submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar  >>


(* 28–30 HandleAcceptOk *)

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
    /\ UNCHANGED << bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar >>


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
       /\ ApplyCommit(s,p,b,id,t,D,tx)
       /\ IF fastOrSlow = Slow THEN msgs' = (msgs \cup { CommitOkMsg(s,p,sq, q, b, id) } ) \ {m} ELSE msgs' = msgs \ {m}
       /\ UNCHANGED << bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, Qvar, initTimestamp >>


(* 42–44 HandleCommitOk *)

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
    /\ UNCHANGED << bal, txn, dep, ts, abal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar >>

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
        /\ ApplyStable(s,p,b,id)
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED << bal, submitted, initCoord, dep, abal, txn, ts, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar >>


(* 45–48 StartRecover *)

StartRecover(s,p,id) ==
    /\ recovered[s][p][id] < NumberOfRecoveryAttempts
    /\ id \in SeenIds(s,p)
    /\ s \in idToShard[id]
    /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE] 
    /\ recovered' = [recovered EXCEPT ![s][p][id] = recovered[s][p][id] + 1]
    \* Ballots owned by p are of the form k*N + p. This k computation is just to get the smallest k * N + p larger than the current ballot
    \* something quite suspiscious here : Since 2 processes from different shards can have the same id, the notion of ballot ownership by p breaks
    \* This doesn't create bugs with my logic because in the case that the current ballot is 'owned' by p (ie already of the form k * N + p),
    \* it will still take the next one. (Actually, I guess ballot ownership doesn't matter at all for safety, but simultaneous recovery attempts 
    \* on the same ballot (by different processes) can block each other, I should fix this then).
    /\  LET Ntotal == N * Nshards IN
        LET pUnique == (s - 1) * N + p  IN
        LET k == ((bal[s][p][id] - pUnique) \div Ntotal) + 1 IN
        LET b == k * Ntotal + pUnique
        IN
        /\  ApplyRecover(s, p, b, id, txn[s][p][id])
        /\  LET D == IF phase[s][p][id] # InitialPhase THEN dep[s][p][id]
                     ELSE {id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET S == {id2 \in SeenIds(s,p) : (id2 # id /\ Conflicts(id,id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2]
                        /\(   (phase[s][p][id2] \in {CommittedPhase, StablePhase} /\ LessThanTs(initTimestamp[id], ts[s][p][id2]))  
                            \/ (   phase[s][p][id2] = AcceptedPhase   /\   LessThanTs( initTimestamp[id] ,  initTimestamp[id2])) 
                          )                    ) 
                        }
                    W == {<<id3,abal[s][p][id3]>> : id3 \in { id2 \in SeenIds(s,p) : (id2 # id /\ Conflicts(id,id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2] 
                        /\ (  (phase[s][p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) /\ LessThanTs(initTimestamp[id],ts[s][p][id2]))
                           \/ (phase[s][p][id2] = PreAcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) )
                           )
                        )}}
                    WP == {id2 \in SeenIds(s,p) : id2 # id /\ Conflicts(id,id2) /\ phase[s][p][id2] = PreAcceptedPhase 
                            /\ LessThanTs(initTimestamp[id],initTimestamp[id2]) /\ id \notin dep[s][p][id2] }
                IN
                IF S # {}
                THEN IF phase[s][p][id] # InitialPhase THEN msgs' = (msgs \cup {RecoverOkMsg(s,p,s,p,b,id,abal[s][p][id],txn[s][p][id],ts[s][p][id],D,phase[s][p][id],TRUE,W,WP)} \cup  { RecoverMsg(s,p,to[1], to[2],b,id,txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  })
                     ELSE msgs' =  msgs \cup {RecoverOkMsg(s,p,s,p,b,id,abal[s][p][id],txn[s][p][id],ts[s][p][id],D,phase[s][p][id],TRUE,W,WP)} \cup { RecoverMsg(s,p,to[1], to[2],b,id,Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> } }
                ELSE IF phase[s][p][id] # InitialPhase THEN msgs' = (msgs \cup {RecoverOkMsg(s,p,s,p,b,id,abal[s][p][id],txn[s][p][id],ts[s][p][id],D,phase[s][p][id],FALSE,W,WP)} \cup  { RecoverMsg(s,p,to[1], to[2],b,id,txn[s][p][id]) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  })
                     ELSE msgs' =  msgs \cup {RecoverOkMsg(s,p,s,p,b,id,abal[s][p][id],txn[s][p][id],ts[s][p][id],D,phase[s][p][id],FALSE,W,WP)} \cup { RecoverMsg(s,p,to[1], to[2],b,id,Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }  }
    /\ UNCHANGED <<phase, dep, ts, abal, submitted, initCoord, Wvar, TXvar, Dvar, initTimestamp, Qvar, recoveryAttemptBal>>


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
        /\  ApplyRecover(s, p, b, id, tx)
        /\  LET D == IF phase[s][p][id] \notin {InitialPhase,PreAcceptedPhase} THEN dep[s][p][id]
                     ELSE dep[s][p][id] \cup {id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET S == {id2 \in SeenIds(s,p) : (id2 # id /\ Conflicts(id,id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2]
                        /\(   (phase[s][p][id2] \in {CommittedPhase, StablePhase} /\ LessThanTs(initTimestamp[id], ts[s][p][id2]))  
                            \/ (   phase[s][p][id2] = AcceptedPhase   /\   LessThanTs( initTimestamp[id] ,  initTimestamp[id2])) 
                          )                    ) 
                        }
                    W == {<<id3,abal[s][p][id3]>> : id3 \in { id2 \in SeenIds(s,p) : (id2 # id /\ Conflicts(id,id2) /\ txn[s][p][id2] # Nop /\ id \notin dep[s][p][id2] 
                        /\ (  (phase[s][p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) /\ LessThanTs(initTimestamp[id],ts[s][p][id2]))
                           \/ (phase[s][p][id2] = PreAcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) )
                           )
                        )}}
                    WP == {id2 \in SeenIds(s,p) : id2 # id /\ Conflicts(id,id2) /\ phase[s][p][id2] = PreAcceptedPhase 
                            /\ LessThanTs(initTimestamp[id],initTimestamp[id2]) /\ id \notin dep[s][p][id2] }
                IN
                IF S # {}
                THEN msgs' = (msgs \cup {RecoverOkMsg(s,p,sq,q,b,id,abal[s][p][id],txn'[s][p][id],ts[s][p][id],D,phase[s][p][id],TRUE,W,WP)}) \ {m} 
                ELSE msgs' = (msgs \cup {RecoverOkMsg(s,p,sq,q,b,id,abal[s][p][id],txn'[s][p][id],ts[s][p][id],D,phase[s][p][id],FALSE,W,WP)}) \ {m}
    /\ UNCHANGED << submitted, initCoord, dep, abal, ts, phase, recovered, TXvar, Dvar, postWaitingFlag, Wvar, recoveryAttemptBal, initTimestamp, Qvar  >>


(* 61–79 + 90-91 HandleRecoverOK *)

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
                            LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], n.body.tq) ) }
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
                            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], n.body.tq) ) }
                                IN 
                                /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,n.body.tq,n.body.depq,n.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)}
                                /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (initCoord[id] \in Q)
                THEN 
                        /\ ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
                        /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                            IN
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)} 
                        /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                ELSE IF ( \A shard \in idToShard[id] :
                            LET Rmax == { n \in quorumOfMessages :
                                                /\ n.body.phaseq = PreAcceptedPhase
                                                /\ n.shardfrom = shard
                                                /\ n.body.tq = initTimestamp[id] }
                            IN Cardinality(Rmax) >= Cardinality({n \in quorumOfMessages : n.shardfrom = s}) - E)
                        THEN
                        LET rejects == {m \in quorumOfMessages : m.body.rejectq = TRUE}
                        IN
                        IF (rejects # {} 
                            \/ (\E shard \in idToShard[id] :
                                    LET shardQuorum == {n \in quorumOfMessages : n.shardfrom = shard}
                                    IN (
                                        (Cardinality({m \in shardQuorum : m.body.phaseq = PreAcceptedPhase /\ m.body.tq = initTimestamp[id]}) = Cardinality(shardQuorum ) - E)
                                        /\ \E id2 \in UNION {m.body.WPq : m \in shardQuorum} : initCoord[id2] \notin Q ))
                                        )   
                        THEN 
                            /\ ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
                            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                                IN
                                /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)} 
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
                            /\ Wvar' = [Wvar EXCEPT  ![s][p][id] = W]
                            /\ Dvar' = [Dvar EXCEPT  ![s][p][id] = D]
                            /\ Qvar' = [Qvar EXCEPT  ![s][p][id] = Q]
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = TRUE]
                            /\ recoveryAttemptBal' = [recoveryAttemptBal EXCEPT ![s][p][id] = bal[s][p][id]]
                            /\ msgs' = msgs \ quorumOfMessages
                            /\ UNCHANGED <<bal, txn, abal, ts, dep, phase>>
                ELSE  
                    /\ ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
                    /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                        IN
                        /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)} 
                        /\ UNCHANGED <<TXvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
    /\ UNCHANGED <<submitted, initCoord, recovered, initTimestamp >>

                 
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
                    /\ m.body.b = b
                    /\ m.body.id = id
                    /\ m.to = p
                    /\ <<m.shardfrom,m.from>> \notin Q
                    /\ (m.body.phaseq \in {StablePhase,CommittedPhase,AcceptedPhase} \/ <<m.shardfrom,m.from>> = initCoord[id]))
        IN 
        \/  /\ Case1
            /\  ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                IN 
                /\ msgs' = msgs \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                            \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)}
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]

        \/  /\ Case2
            /\ ApplyAccept(s,p,bal[s][p][id],id,initTimestamp[id],D,tx)
            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                IN 
                /\ msgs' = msgs \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,initTimestamp[id],D,tx) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   }
                            \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)}
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
        \* If I use case 3 here the interpreter doesn't know what m is, which I need in the following. This begs the question why am I
        \* define the cases seperately in the first place : I need to specify that the state doesn't change when none of the 3 cases are verified. (at the end of this handler)
        \/  (\E m \in msgs :
                    /\ m.type = TypeRecoverOK
                    /\ m.body.b = b
                    /\ m.body.id = id
                    /\ m.to = p
                    /\ <<m.shardfrom,m.from>> \notin Q
                    /\ (m.body.phaseq \in {StablePhase,CommittedPhase,AcceptedPhase} \/ <<m.shardfrom,m.from>>  = initCoord[id])
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
                            LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2],m.body.tq)) }
                            IN 
                            /\ ApplyAccept(s,p,b,id,m.body.tq,m.body.depq,m.body.txq)
                            /\ msgs' = msgs \cup { AcceptMsg(s,p,to[1], to[2],b,id,m.body.tq,m.body.depq,m.body.txq) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,b,id,Dq)}
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
                        ELSE 
                            /\ ApplyAccept(s,p,bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop)
                            /\  LET Dq == { id2 \in SeenIds(s,p) : (Conflicts(id,id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                                IN
                                /\ msgs' = msgs \cup { AcceptMsg(s,p,to[1], to[2],bal[s][p][id],id,ts[s][p][id],dep[s][p][id],Nop) : to \in { <<sq, q>> : sq \in idToShard[id], q \in Proc } \ { <<s, p>> }   } \cup {AcceptOKMsg(s,p,s,p,bal[s][p][id],id,Dq)} 
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![s][p][id] = FALSE]
            )

        \/  /\ ~Case1 /\ ~Case2 /\ ~Case3
            /\ UNCHANGED << msgs, postWaitingFlag, bal, dep, phase, abal, txn, ts >>
                    
        
    /\ UNCHANGED << submitted, initCoord, recovered, Wvar, recoveryAttemptBal, TXvar, Dvar, initTimestamp, Qvar >>


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)                 

Agreement ==
  \A id \in Id : \A p, q \in Proc : \A s \in Shards :
    /\ phase[s][p][id] \in {CommittedPhase,StablePhase}
    /\ phase[s][q][id] \in {CommittedPhase,StablePhase}
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
      /\ LessThanTs(ts[s][q][id2],ts[s][p][id1])
      => id2 \in dep[s][p][id1]

        
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


Spec ==
    Init /\ [][Next]_<< vars >>

=========================================================================
