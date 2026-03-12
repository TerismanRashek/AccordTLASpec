---- MODULE AccordSpec ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

VARIABLES
    bal,           \* bal[p][id] = current ballot known by process p for command id
    phase,         \* phase[p][id] ∈ {"none","preaccepted","accepted","committed"}
    cmd,           \* cmd[p][id] = command payload at p
    dep,           \* dep[p][id] = final dependency set (accepted or committed)
    ts,            \* ts[p][id] = timestamp at p, timestamp is a couple of (t, id) ts.t for timestamp, ts.id for id.
    abal,          \* abal[p][id] = last ballot where p accepted a slow-path value
    msgs,           \* multiset of network messages
    submitted,      \* set of submitted command ids
    initCoord,      \* initCoord[id] = process that submitted id
    initTimestamp,
    recovered,       \* var to limit amount of recovery attempts started
    Wvar,
    Cvar,
    Dvar,
    Qvar,
    postWaitingFlag,
    recoveryAttemptBal

vars == << bal, phase, cmd, dep, ts, abal, msgs, submitted, initTimestamp, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar, Qvar >>



CONSTANTS 
    Proc,       \* The set of processes
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

ASSUME E<=F

Init == 
    /\ bal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ phase = [p \in Proc |-> [id \in Id |-> InitialPhase]]
    /\ cmd = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\ dep = [p \in Proc |-> [id \in Id |-> {}]]
    /\ ts = [p \in Proc |-> [id \in Id |-> [t |-> 0, id |-> 0]]] 
    /\ abal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ msgs = {}
    /\ submitted = {}
    /\ initCoord = [id \in Id |-> NoProc]
    /\ recovered = [p \in Proc |-> [id \in Id |-> 0]]
    /\ Wvar = [p \in Proc |-> [id \in Id |-> {}]]
    /\ Cvar = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\ Dvar = [p \in Proc |-> [id \in Id |-> {}]]
    /\ postWaitingFlag = [p \in Proc |-> [id \in Id |-> FALSE]]
    /\ recoveryAttemptBal = [p \in Proc |-> [id \in Id |-> 0]]
    /\ initTimestamp = <<[id |-> 1, t |-> 0], [id |-> 2, t |-> 2]>>
    /\ Qvar = [p \in Proc |-> [id \in Id |-> {}]]


N == Cardinality(Proc)



Max(a, b) == IF a > b THEN a ELSE b

LessThanTs(ts1,ts2) ==
    IF ts1.id = 0 THEN TRUE
    ELSE IF ts2.id = 0 THEN FALSE
    ELSE IF ts1.t < ts2.t THEN TRUE
    ELSE IF ts1.t > ts2.t THEN FALSE
    ELSE ts1.id < ts2.id

MaxTs(ts1, ts2) ==
    IF LessThanTs(ts1,ts2) THEN ts2 ELSE ts1

MaxTsInSet(S) ==
    CHOOSE ts1 \in S : \A ts2 \in S :
                            ts2 # ts1 => LessThanTs(ts2, ts1)


ConflictingPayload(id1, id2) ==
    \* IF id1 = 3 \/ id2 = 3 THEN TRUE
    \* ELSE FALSE
    id1 # id2

Conflicts(p, idGettingChecked, id2) ==
    IF cmd[p][id2] = Bottom THEN
        FALSE
    ELSE
        ConflictingPayload(idGettingChecked, id2)


IsQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - F
IsFastQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - E


SeenIds(p) ==
    {id \in Id : 
        \/ cmd[p][id] # Bottom
        \/ \E id2 \in Id : id \in dep[p][id2]}




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

Message(type, from, to, body) ==
    [ type |-> type, from |-> from, to |-> to, body |-> body ]

PreAcceptMsg(p, q, id, c, D0) ==
    Message(TypePreAccept, p, q,
        [ id  |-> id,
          c |-> c,
          D0 |-> D0 ])

PreAcceptOKMsg(p, q, id, tq, Dq) ==
    Message(TypePreAcceptOK, p, q,
        [ id  |-> id,
          tq |-> tq,
          Dq |-> Dq ])

AcceptMsg(p, q, b, id, t, D, c) ==
    Message(TypeAccept, p, q,
        [ id   |-> id,
          b  |-> b,
          t |-> t,
          c |-> c,
          D |-> D ])

AcceptOKMsg(p, q, b, id, Dq) ==
    Message(TypeAcceptOK, p, q,
        [ id  |-> id,
          b |-> b,
          Dq |-> Dq ])

CommitMsg(p, q, b, id, t, D, phaseq, c) ==
    Message(TypeCommit, p, q,
        [ id   |-> id,
          b  |-> b,
          c |-> c,
          D |-> D,
          phaseq |-> phaseq,
          t |-> t ])

CommitOkMsg(p, q, b, id) ==
    Message(TypeCommitOK, p, q,
        [ id  |-> id,
          b |-> b ])

StableMsg(p, q, b, id) ==
    Message(TypeStable, p, q,
        [ id  |-> id,
          b |-> b ])

RecoverMsg(p,q,b,id,c) ==
    Message(TypeRecover, p, q,
        [id   |-> id,
          b  |-> b,
          c |-> c])

RecoverOkMsg(p,q,b,id,abalq,cq,tq,depq,phaseq,rejectq,Wq,WPq) ==
    Message(TypeRecoverOK, p, q,
        [id   |-> id,
          b  |-> b,
          cq |-> cq,
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

ApplyPreAccept(p, q, id, c, finalTs, D0) ==
    /\  bal[p][id] = 0
    /\  phase[p][id] = InitialPhase
    /\  cmd' = [cmd EXCEPT ![p][id] = c]
    /\  phase' = [phase EXCEPT ![p][id] = PreAcceptedPhase]
    /\  ts' = [ts EXCEPT ![p][id] = finalTs]
    /\  dep' = [dep EXCEPT ![p][id] = D0]

ApplyAccept(p,q,b,id,t,D,c) ==
    /\  bal[p][id] <= b
    /\  (b = 0 => phase[p][id] = PreAcceptedPhase)
    /\  IF b > 0 THEN cmd'  = [cmd  EXCEPT ![p][id] = c] ELSE UNCHANGED cmd
    /\  bal'  = [bal  EXCEPT ![p][id] = b]
    /\  abal' = [abal EXCEPT ![p][id] = b]
    /\  ts'   = [ts  EXCEPT ![p][id] = t]
    /\  dep'  = [dep  EXCEPT ![p][id] = D]
    /\  phase' = [phase EXCEPT ![p][id] = AcceptedPhase]

ApplyCommit(p,q,b,id,t,D,phaseq,c) ==
    /\ bal[p][id] = b
    /\ b = 0 => phase[p][id] \in {PreAcceptedPhase, AcceptedPhase}
    /\ IF b > 0 THEN cmd'  = [cmd  EXCEPT ![p][id] = c] ELSE UNCHANGED cmd
    /\ abal' = [abal EXCEPT ![p][id] = b]
    /\ ts'   = [ts  EXCEPT ![p][id] = t]
    /\ dep' = [dep EXCEPT ![p][id] = D]
    /\ phase' = [phase EXCEPT ![p][id] = phaseq]

ApplyStable(p,q,b,id) ==
    /\ bal[p][id] = b
    /\ phase[p][id] = CommittedPhase
    /\ phase' = [phase EXCEPT ![p][id] = StablePhase]

ApplyRecover(p, q, b, id, c) ==
    /\  bal[p][id] < b
    /\  bal'  = [bal  EXCEPT ![p][id] = b]
    /\  IF phase[p][id] = InitialPhase THEN  cmd'  = [cmd  EXCEPT ![p][id] = c] ELSE UNCHANGED cmd

    


(***************************************************************************)
(* Message handling Actions                                                  *)
(***************************************************************************)

(***************************************************************************)
(* 4–6 Submit                                                              *)
(***************************************************************************)

Submit(p, id) ==
    /\  id \notin submitted
    /\  LET c == id \* I just use Id as command payload, the actual payload does not matter. Conflict relation is defined on these integer Ids.
            earlierInitTimestamps == {initTimestamp[id2] : id2 \in {id1 \in Id : initCoord[id1] = p /\ LessThanTs(initTimestamp[id1],initTimestamp[id])}}
        IN 
        /\ LET initTimestampVal == IF earlierInitTimestamps = {} THEN initTimestamp[id].t ELSE MaxTsInSet(earlierInitTimestamps).t + 1
            IN
            /\ initTimestamp' = [initTimestamp EXCEPT ![id] = [id |-> id, t |-> initTimestampVal]]
            /\ submitted' = submitted \cup {id}
            /\ initCoord' = [initCoord EXCEPT ![id] = p]
            /\ ts' = [ts EXCEPT ![p][id] = initTimestamp[id]]
            /\  LET setOfConflictingTs == {ts1 \in { ts[p][id2] : id2 \in Id} : ts1.id # 0 /\ Conflicts(p, id, ts1.id)}
                    D == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                IN
                /\  LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
                    IN
                    /\  LET finalTs == MaxTs(initTimestamp[id], [t |-> tval, id |-> id])
                        IN
                        /\ msgs' = msgs \cup { PreAcceptMsg(p, q, id, c, D) : q \in Proc \ {p} } \cup {PreAcceptOKMsg(p,p,id,finalTs,D)}
                        /\ ApplyPreAccept(p,p,id,c,finalTs,D)
    /\ UNCHANGED << bal, abal, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar, Qvar >> 

(***************************************************************************)
(* 7–15 HandlePreAccept                                                    *)
(***************************************************************************)                    

HandlePreAccept(m) ==
    /\  m.type = TypePreAccept
    /\  LET p  == m.to
            q  == m.from
            id == m.body.id
            c  == m.body.c
        IN 
        /\  LET setOfConflictingTs == {ts1 \in { ts[p][id2] : id2 \in Id} : ts1.id # 0 /\  Conflicts(p, id, ts1.id)}
                D == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
                IN
                /\  cmd' = [cmd EXCEPT ![p][id] = c]
                /\  LET finalTs == MaxTs(initTimestamp[id], [t |-> tval, id |-> id])
                    IN
                    /\ ApplyPreAccept(p,q,id,c,finalTs,D)
                    /\ msgs' = (msgs \cup { PreAcceptOKMsg(p, q, id, finalTs, D) }) \ {m}
    /\ UNCHANGED << bal, abal, submitted, initCoord, recovered, postWaitingFlag, recoveryAttemptBal, initTimestamp, Cvar, Dvar, Wvar, Qvar>>


(***************************************************************************)
(* 16–23 HandlePreAcceptOk                                                      *)
(***************************************************************************)


HandlePreAcceptOK(p, id) ==
    /\ bal[p][id] = 0
    /\ phase[p][id] = PreAcceptedPhase
    /\ LET quorumOfMessages ==
            {  m \in msgs :
                    /\ m.type = TypePreAcceptOK
                    /\ m.body.id = id
                    /\ m.to = p
            }
        IN
        /\ IsQuorumSized(quorumOfMessages)
        \* I build the set of fast quorums from the messages, check if there is at least one, and CHOOSE it deterministically
        /\  LET largestFastQuorum ==
                { m \in quorumOfMessages : m.body.tq = initTimestamp[id]  }
            IN
            IF IsFastQuorumSized(largestFastQuorum) THEN
                    LET D == dep[p][id] \cup UNION { m.body.Dq : m \in largestFastQuorum }
                    IN
                    /\ ApplyCommit(p,p,0,id,initTimestamp[id],D,StablePhase,cmd[p][id])               
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q, 0, id, initTimestamp[id], D, StablePhase, cmd[p][id]) : q \in Proc \ {p} }
                    /\ UNCHANGED bal
            ELSE     
                /\  LET D == UNION { m.body.Dq : m \in quorumOfMessages }
                        t == MaxTsInSet({ m.body.tq : m \in quorumOfMessages })
                    IN
                    LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], t)) }
                    IN 
                    /\ ApplyAccept(p,p,0,id,t,D,cmd[p][id])
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, 0, id, t, D, cmd[p][id]) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,0,id,Dq)}
    /\ UNCHANGED <<  submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar, initTimestamp, Qvar  >>
       

(***************************************************************************)
(* 24–32 HandleAccept                                                      *)
(***************************************************************************)                            

HandleAccept(m) ==
    /\ m.type = TypeAccept
    /\  LET p  == m.to
            q  == m.from
            b  == m.body.b
            id == m.body.id
            t  == m.body.t
            D  == m.body.D
            c  == m.body.c
        IN
        /\  ApplyAccept(p,q,b,id,t,D,c)
        /\  LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ MaxTs(initTimestamp[id2], t) = t) }
            IN
            /\ msgs' = (msgs \cup { AcceptOKMsg(p, q, b, id, Dq) }) \ {m}
    /\ UNCHANGED << submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar, initTimestamp, Qvar  >>

(***************************************************************************)
(* 33–35 HandleAcceptOk                                                    *)
(***************************************************************************)

HandleAcceptOK(p, id) ==
    /\ phase[p][id] = AcceptedPhase
    /\ LET quorumOfMessages == { m \in msgs :
        /\ m.type = TypeAcceptOK
        /\ m.to = p
        /\ m.body.b = bal[p][id] \*Ballot precondition is here
        /\ m.body.id = id }   
        IN
        /\ IsQuorumSized(quorumOfMessages)
        /\  LET D == dep[p][id] \cup UNION { m.body.Dq : m \in quorumOfMessages }
            IN
            /\ msgs' = (msgs \cup {CommitMsg(p, q, bal[p][id], id, ts[p][id], D, CommittedPhase, cmd[p][id]) : q \in Proc \ {p} } \cup {CommitOkMsg(p,p,bal[p][id],id)}) \ quorumOfMessages
            /\ ApplyCommit(p,p, bal[p][id], id, ts[p][id], D, CommittedPhase, cmd[p][id])
    /\ UNCHANGED << bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar, initTimestamp, Qvar >>

(***************************************************************************)
(* 36–44 HandleCommit                                                      *)
(***************************************************************************)

HandleCommit(m) ==
    /\ m.type = TypeCommit
    /\ LET p == m.to
           q == m.from
           b  == m.body.b
           id == m.body.id
           c  == m.body.c
           D  == m.body.D
           phaseq == m.body.phaseq
           t == m.body.t
       IN
       /\ ApplyCommit(p,q,b,id,t,D,phaseq,c)
       /\ IF phaseq = CommittedPhase THEN msgs' = (msgs \cup { CommitOkMsg(p, q, b, id) } ) \ {m} ELSE msgs' = msgs \ {m}
       /\ UNCHANGED << bal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar, Qvar, initTimestamp >>



(***************************************************************************)
(* 45–47 HandleCommitOk                                                    *)
(***************************************************************************)

HandleCommitOK(p, id) ==
    /\ phase[p][id] = CommittedPhase
    /\ LET quorumOfMessages == { m \in msgs :
        /\ m.type = TypeCommitOK
        /\ m.to = p
        /\ m.body.b = bal[p][id] \*Ballot precondition is here
        /\ m.body.id = id }   
        IN
        /\ IsQuorumSized(quorumOfMessages)
        /\ msgs' = (msgs \cup {StableMsg(p, q, bal[p][id], id) : q \in Proc \ {p} }) \ quorumOfMessages
        /\ ApplyStable(p,p,bal[p][id],id)
    /\ UNCHANGED << bal, cmd, dep, ts, abal, submitted, initCoord, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar, initTimestamp, Qvar >>

(***************************************************************************)
(* 48–50 HandleStable                                                      *)
(***************************************************************************)

HandleStable(m) ==
    /\ m.type = TypeStable
    /\  LET p == m.to
            q == m.from
            b  == m.body.b
            id == m.body.id
        IN
        /\ ApplyStable(p,q,b,id)
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED << bal, submitted, initCoord, dep, abal, cmd, ts, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar, initTimestamp, Qvar >>

(***************************************************************************)
(* 51–54 StartRecover                                                      *)
(***************************************************************************)

StartRecover(p,id) ==
    /\ recovered[p][id] < NumberOfRecoveryAttempts
    /\ id \in SeenIds(p)
    /\ cmd[p][id] # Bottom
    /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE] 
    /\ recovered' = [recovered EXCEPT ![p][id] = recovered[p][id] + 1]
    \* Ballots owned by p are of the form k*N + p.
    /\  LET  b == IF bal[p][id] = 0 THEN p ELSE bal[p][id] + Cardinality(Proc)
        IN
        IF phase[p][id] # InitialPhase THEN msgs' = msgs \cup { RecoverMsg(p,q,b,id,cmd[p][id]) : q \in Proc }
        ELSE msgs' = msgs \cup { RecoverMsg(p,q,b,id,Nop) : q \in Proc }
    /\ UNCHANGED <<bal, phase, cmd, dep, ts, abal, submitted, initCoord, Wvar, recoveryAttemptBal, Cvar, Dvar, initTimestamp, Qvar>>

(***************************************************************************)
(* 55–68 HandleRecover                                                     *)
(***************************************************************************)

HandleRecover(m) ==
    /\  m.type = TypeRecover
    /\  LET p == m.to 
            q == m.from
            b == m.body.b
            id == m.body.id
            c == m.body.c
        IN 
        /\  ApplyRecover(p, q, b, id, c)
        /\  LET D == IF phase[p][id] # InitialPhase THEN dep[p][id]
                     ELSE {id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET S == {id2 \in SeenIds(p) : (id2 # id /\ Conflicts(p, id, id2) /\ cmd[p][id2] # Nop /\ id \notin dep[p][id2]
                        /\(   (phase[p][id2] \in {CommittedPhase, StablePhase} /\ LessThanTs(initTimestamp[id], ts[p][id2]))  
                            \/ (   phase[p][id2] = AcceptedPhase   /\   LessThanTs( initTimestamp[id] ,  initTimestamp[id2])) 
                          )                    ) 
                        }
                    W == {<<id3,abal[p][id3]>> : id3 \in { id2 \in SeenIds(p) : (id2 # id /\ Conflicts(p, id, id2) /\ cmd[p][id2] # Nop /\ id \notin dep[p][id2] 
                        /\ (  (phase[p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) /\ LessThanTs(initTimestamp[id],ts[p][id2]))
                           \/ (phase[p][id2] = PreAcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id]) )
                           )
                        )}}
                    WP == {id2 \in SeenIds(p) : id2 # id /\ Conflicts(p, id, id2) /\ phase[p][id2] = PreAcceptedPhase 
                            /\ LessThanTs(initTimestamp[id],initTimestamp[id2]) /\ id \notin dep[p][id2] }
                IN
                IF S # {}
                THEN msgs' = (msgs \cup {RecoverOkMsg(p,q,b,id,abal[p][id],cmd'[p][id],ts[p][id],D,phase[p][id],TRUE,W,WP)}) \ {m} 
                ELSE msgs' = (msgs \cup {RecoverOkMsg(p,q,b,id,abal[p][id],cmd'[p][id],ts[p][id],D,phase[p][id],FALSE,W,WP)}) \ {m}
    /\ UNCHANGED << submitted, initCoord, dep, abal, ts, phase, recovered, Cvar, Dvar, postWaitingFlag, Wvar, recoveryAttemptBal, initTimestamp, Qvar  >>

(***************************************************************************)
(* 69–85 HandleRecoverOK                                                   *)
(***************************************************************************)

HandleRecoverOK(p, id) ==
    /\  LET quorumOfMessages ==
        { m \in msgs :
            /\ m.type = TypeRecoverOK
            /\ m.to = p 
            /\ m.body.id = id 
            /\ m.body.b = bal[p][id] \* ballot precondition is here
            /\ abal[p][id] < m.body.b  }
        IN
        /\ IsQuorumSized(quorumOfMessages) 
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
                            /\ msgs' = (msgs \cup {CommitMsg(p, q, bal[p][id], id, n.body.tq, n.body.depq, n.body.phaseq, n.body.cq) : q \in Proc \ {p} }) \ quorumOfMessages
                            /\ ApplyCommit(p, p, bal[p][id], id, n.body.tq, n.body.depq, n.body.phaseq, n.body.cq)
                            /\ UNCHANGED <<bal, Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = CommittedPhase)
                THEN
                        /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = CommittedPhase
                            IN
                            LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], n.body.tq) ) }
                            IN 
                            /\ msgs' = (msgs \cup {CommitMsg(p, q, bal[p][id], id, n.body.tq, n.body.depq, n.body.phaseq, n.body.cq) : q \in Proc \ {p} } \cup {CommitOkMsg(p,p,bal[p][id],id)}) \ quorumOfMessages
                            /\ ApplyCommit(p, p, bal[p][id], id, n.body.tq, n.body.depq, n.body.phaseq, n.body.cq)
                            /\ UNCHANGED <<bal ,Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>  
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = AcceptedPhase)
                THEN    
                        /\  LET n == CHOOSE n \in U :
                                n.body.phaseq = AcceptedPhase
                            IN
                            /\  ApplyAccept(p,p,bal[p][id],id,n.body.tq,n.body.depq,n.body.cq)
                            /\  LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], n.body.tq) ) }
                                IN 
                                /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p,q,bal[p][id],id,n.body.tq,n.body.depq,n.body.cq) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)}
                                /\ UNCHANGED <<Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>> 
                ELSE IF (initCoord[id] \in Q)
                THEN 
                        /\ ApplyAccept(p,p,bal[p][id],id,ts[p][id],dep[p][id],Nop)
                        /\  LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                            IN
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p,q,bal[p][id],id,ts[p][id],dep[p][id],Nop) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)} 
                        /\ UNCHANGED <<Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
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
                            /\ ApplyAccept(p,p,bal[p][id],id,ts[p][id],dep[p][id],Nop)
                            /\  LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                                IN
                                /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p,q,bal[p][id],id,ts[p][id],dep[p][id],Nop) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)} 
                            /\ UNCHANGED <<Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
                        ELSE 
                            LET n == CHOOSE n \in quorumOfMessages : n.body.phaseq = PreAcceptedPhase
                                Wall == UNION {(m.body.Wq \cup {<<id1, 0>> : id1 \in {id2 \in m.body.WPq : m.from = initCoord[id2]}}) : m \in quorumOfMessages}
                            IN
                            LET c == n.body.cq
                                W == {<<id1, bal1>> \in Wall : \A <<id2, bal2>> \in Wall : bal2 <= bal1}
                                D == UNION {m.body.depq : m \in quorumOfMessages}
                            IN
                            /\ Cvar' = [Cvar EXCEPT  ![p][id] = c]
                            /\ Wvar' = [Wvar EXCEPT  ![p][id] = W]
                            /\ Dvar' = [Dvar EXCEPT  ![p][id] = D]
                            /\ Qvar' = [Qvar EXCEPT  ![p][id] = Q]
                            /\ recoveryAttemptBal' = [recoveryAttemptBal EXCEPT ![p][id] = bal[p][id]]
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = TRUE]
                            /\ msgs' = msgs \ quorumOfMessages
                            /\ UNCHANGED <<bal, cmd, abal, ts, dep, phase>>
                ELSE  
                    /\ ApplyAccept(p,p,bal[p][id],id,ts[p][id],dep[p][id],Nop)
                    /\  LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                        IN
                        /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p,q,bal[p][id],id,ts[p][id],dep[p][id],Nop) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)} 
                        /\ UNCHANGED <<Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag, Qvar>>   
    /\ UNCHANGED <<submitted, initCoord, recovered, initTimestamp >>
            
(***************************************************************************)
(* 86–95 HandlePostWaiting                                                 *)
(***************************************************************************)
                    
HandlePostWaiting(p, id) ==
    /\  recoveryAttemptBal[p][id] = bal[p][id] \* I'm not getting the ballot of corresponding recovery attempt from messages here so I use this extra variable to check ballot.
    /\  postWaitingFlag[p][id] = TRUE
    /\  LET W == Wvar[p][id]
            b == bal[p][id] 
            c == Cvar[p][id]
            D == Dvar[p][id]
            Q == Qvar[p][id]
            Case1 ==
                \E w \in W :
                    LET id1 == w[1]
                        bal1 == w[2]
                    IN /\ phase[p][id1] \in {CommittedPhase,StablePhase}
                    /\ abal[p][id1] >= bal1
                    /\ cmd[p][id1] # Nop
                    /\ LessThanTs(initTimestamp[id], ts[p][id1])
                    /\ id \notin dep[p][id1]
            Case2 ==
                \A w \in W :
                    LET id1 == w[1]
                        bal1 == w[2]
                    IN /\ phase[p][id1] \in {CommittedPhase,StablePhase}
                    /\ abal[p][id1] >= bal1
                    /\ cmd[p][id1] # Nop
                    /\ (LessThanTs(ts[p][id1], initTimestamp[id]) \/ id \in dep[p][id1])
            Case3 ==
                (\E m \in msgs :
                    /\ m.type = TypeRecoverOK
                    /\ m.from \notin Q
                    /\ (m.body.phaseq \in {StablePhase,CommittedPhase,AcceptedPhase} \/ m.from = initCoord[id]))
        IN 
        \/  /\ Case1
            /\  ApplyAccept(p,p,bal[p][id],id,ts[p][id],dep[p][id],Nop)
            /\  LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                IN 
                /\ msgs' = msgs \cup { AcceptMsg(p,q,bal[p][id],id,ts[p][id],dep[p][id],Nop) : q \in Proc \ {p} }
                            \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)}
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]

        \/  /\ Case2
            /\ ApplyAccept(p,p,bal[p][id],id,initTimestamp[id],D,c)
            /\  LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                IN 
                /\ msgs' = msgs \cup { AcceptMsg(p,q,bal[p][id],id,initTimestamp[id],D,c) : q \in Proc \ {p} }
                            \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)}
                /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]
        \/  (\E m \in msgs :
                    /\ m.type = TypeRecoverOK
                    /\ m.body.b = b
                    /\ m.body.id = id
                    /\ m.to = p
                    /\ m.from \notin Q
                    /\ (m.body.phaseq \in {StablePhase,CommittedPhase,AcceptedPhase} \/ m.from = initCoord[id])
                    /\  IF (m.body.phaseq = StablePhase) THEN
                            /\ ApplyCommit(p,p,b,id,m.body.tq,m.body.depq,StablePhase,m.body.cq)               
                            /\ msgs' = msgs \cup { CommitMsg(p,q,b,id,m.body.tq,m.body.depq,StablePhase,m.body.cq) : q \in Proc \ {p} }
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]
                            /\ UNCHANGED bal
                        ELSE IF (m.body.phaseq = CommittedPhase) THEN   
                            /\ msgs' = (msgs \cup {CommitMsg(p,q,b,id,m.body.tq,m.body.depq,CommittedPhase,m.body.cq) : q \in Proc \ {p} } \cup {CommitOkMsg(p,p,b,id)})
                            /\ ApplyCommit(p,p,b,id,m.body.tq,m.body.depq,CommittedPhase,m.body.cq)
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]
                            /\ UNCHANGED bal
                        ELSE IF (m.body.phaseq = AcceptedPhase) THEN 
                            LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2],m.body.tq)) }
                            IN 
                            /\ ApplyAccept(p,p,b,id,m.body.tq,m.body.depq,m.body.cq)
                            /\ msgs' = msgs \cup { AcceptMsg(p,q,b,id,m.body.tq,m.body.depq,m.body.cq) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,b,id,Dq)}
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]
                        ELSE 
                            /\ ApplyAccept(p,p,bal[p][id],id,ts[p][id],dep[p][id],Nop)
                            /\  LET Dq == { id2 \in SeenIds(p) : (Conflicts(p, id, id2) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                                IN
                                /\ msgs' = msgs \cup { AcceptMsg(p,q,bal[p][id],id,ts[p][id],dep[p][id],Nop) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)} 
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]
            )

        \/  /\ ~Case1 /\ ~Case2 /\ ~Case3
            /\ UNCHANGED << msgs, postWaitingFlag, bal, dep, phase, abal, cmd, ts >>
                    
        
    /\ UNCHANGED << submitted, initCoord, recovered, Wvar, recoveryAttemptBal, Cvar, Dvar, initTimestamp, Qvar >>


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)                 

Agreement ==
  \A id \in Id : \A p, q \in Proc :
    /\ phase[p][id] \in {CommittedPhase,StablePhase}
    /\ phase[q][id] \in {CommittedPhase,StablePhase}
    =>  /\ cmd[p][id] = cmd[q][id]
        /\ ts[p][id] = ts[q][id]

Visibility ==
  \A id1, id2 \in Id :
    \A p, q \in Proc :
      /\ phase[p][id1] = StablePhase
      /\ phase[q][id2] = CommittedPhase
      /\ cmd[p][id1] # Nop
      /\ cmd[q][id2] # Nop
      /\ ConflictingPayload(id1, id2)
      /\ LessThanTs(ts[q][id2],ts[p][id1])
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
        \/ StartRecover(p,id)
        \/ HandleRecoverOK(p, id)
        \/ HandlePostWaiting(p, id)


Spec ==
    Init /\ [][Next]_<< vars >>

=========================================================================