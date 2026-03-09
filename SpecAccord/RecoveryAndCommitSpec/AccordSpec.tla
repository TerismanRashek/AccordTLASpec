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
    initTimestamp,  \* initTimestamp[id] = timestamp assigned by the coordinator when id is submitted

    recovered,       \* var to limit amount of recovery attempts started
    Wvar,
    Cvar,
    Dvar,
    postWaitingFlag,
    recoveryAttemptBal

vars == << bal, phase, cmd, dep, ts, abal, msgs, submitted, initCoord, initTimestamp, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar >>


CONSTANTS 
    Proc,       \* The set of processes
    Id,         \* The set of command IDs
    F, 
    E,
    Bottom,     \* The bottom value for the command payload
    NoProc,      \* A special value representing no process
    Nop,
    NumberOfRecoveryAttempts

ASSUME E<=F

N == Cardinality(Proc)

Max(a, b) == IF a > b THEN a ELSE b

LessThanTs(ts1,ts2) ==
    IF ts1.id = 0 \/ ts2.id = 0 THEN FALSE
    ELSE IF ts1.t < ts2.t THEN TRUE
    ELSE IF ts1.t > ts2.t THEN FALSE
    ELSE ts1.id < ts2.id

MaxTs(ts1, ts2) ==
    IF LessThanTs(ts1,ts2) THEN ts2 ELSE ts1

MaxTsInSet(S) ==
    CHOOSE ts1 \in S : \A ts2 \in S :
                            ts2 # ts1 => LessThanTs(ts2, ts1)

Conflicts(c1, c2) ==
    IF c1 = Bottom \/ c2 = Bottom THEN
        FALSE
    ELSE IF c1 = Nop \/ c2 = Nop THEN
        TRUE
    ELSE
        c1 # c2

ConflictingIds(p, c) ==
    { id \in Id :
        /\ Conflicts(cmd[p][id], c)
    }

IsQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - F
IsFastQuorumSized(set) == Cardinality(set) >= Cardinality(Proc) - E



ASSUME N >= Max(2*E+F+1, 2*F+1)

\*Phases
(* Initial = 1
   PreAccepted = 2
   Accepted = 3
   Committed = 4
   Stable = 5 *)
CONSTANTS 
    InitialPhase, PreAcceptedPhase, AcceptedPhase, CommittedPhase, StablePhase

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

PreAcceptMsg(p, q, id, c) ==
    Message(TypePreAccept, p, q,
        [ id  |-> id,
          c |-> c ])

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

RecoverOkMsg(p,q,b,id,abalq,cq,tq,depq,phaseq,rejectq,Wq) ==
    Message(TypeRecoverOK, p, q,
        [id   |-> id,
          b  |-> b,
          cq |-> cq,
          depq |-> depq,
          phaseq |-> phaseq,
          abalq |-> abalq,
          tq |-> tq,
          rejectq |-> rejectq,
          Wq |-> Wq ])

(***************************************************************************)
(* State changing Actions                                                  *)
(***************************************************************************)

ApplyPreAccept(p, q, id, c, finalTs) ==
    /\  bal[p][id] = 0
    /\  phase[p][id] = InitialPhase
    /\  cmd' = [cmd EXCEPT ![p][id] = c]
    /\  phase' = [phase EXCEPT ![p][id] = PreAcceptedPhase]
    /\  ts' = [ts EXCEPT ![p][id] = finalTs]

ApplyAccept(p,q,b,id,t,D,c) ==
    /\  bal[p][id] <= b
    /\  (bal[p][id] = 0 => phase[p][id] = PreAcceptedPhase)
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
    /\ phase' = [phase EXCEPT ![p][id] = CommittedPhase]

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
        IN
        /\ submitted' = submitted \cup {id}
        /\ initCoord' = [initCoord EXCEPT ![id] = p]
        /\ ts' = [ts EXCEPT ![p][id] = [t |-> 1, id |-> id]]
        /\ initTimestamp' = [initTimestamp EXCEPT ![id] = [t |-> 1, id |-> id]]
        /\  LET setOfConflictingTs == {ts1 \in { ts[p][id2] : id2 \in Id} : ts1.id # 0 /\ Conflicts(cmd[p][ts1.id], c)}
                D == { id2 \in Id : (Conflicts(cmd[p][id2], c) /\ LessThanTs(initTimestamp'[id2], initTimestamp'[id]) ) }
            IN
            /\  LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
                IN
                /\  LET finalTs == MaxTs(initTimestamp'[id], [t |-> tval, id |-> id])
                    IN
                    /\ msgs' = msgs \cup { PreAcceptMsg(p, q, id, c) : q \in Proc \ {p} } \cup {PreAcceptOKMsg(p,p,id,finalTs,D)}
                    /\ ApplyPreAccept(p,p,id,c,finalTs)
    /\ UNCHANGED << bal, dep, abal, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar >> 

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
        /\  LET setOfConflictingTs == {ts1 \in { ts[p][id2] : id2 \in Id} : ts1.id # 0 /\  Conflicts(cmd[p][ts1.id], c)}
                D == { id2 \in Id : (Conflicts(cmd[p][id2], c) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET tval == IF setOfConflictingTs = {} THEN 0 ELSE MaxTsInSet(setOfConflictingTs).t + 1
                IN
                /\  cmd' = [cmd EXCEPT ![p][id] = c]
                /\  LET finalTs == MaxTs(initTimestamp[id], [t |-> tval, id |-> id])
                    IN
                    /\ ApplyPreAccept(p,q,id,c,finalTs)
                    /\ msgs' = (msgs \cup { PreAcceptOKMsg(p, q, id, finalTs, D) }) \ {m}
    /\ UNCHANGED << bal, dep, abal, submitted, initCoord, initTimestamp, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar  >>


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
                    \* I am putting bottom because command doesn't matter here, but it's not clear.
                    LET D == UNION { m.body.Dq : m \in largestFastQuorum }
                    IN
                    /\ ApplyCommit(p,p,0,id,initTimestamp[id],D,StablePhase,cmd[p][id])               
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { CommitMsg(p, q, 0, id, initTimestamp[id], D, StablePhase, cmd[p][id]) : q \in Proc \ {p} }
                    /\ UNCHANGED bal
            ELSE     
                /\  LET D == UNION { m.body.Dq : m \in quorumOfMessages }
                        t == MaxTsInSet({ m.body.tq : m \in quorumOfMessages })
                    IN
                    LET Dq == { id2 \in Id : (Conflicts(cmd[p][id2], cmd[p][id]) /\ MaxTs(initTimestamp[id2], t) = t) }
                    IN 
                    /\ ApplyAccept(p,p,0,id,t,D,cmd[p][id])
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p, q, 0, id, t, D, cmd[p][id]) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,0,id,Dq)}
    /\ UNCHANGED <<  submitted, initCoord, initTimestamp, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar  >>
       

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
        /\  LET Dq == { id2 \in Id : (Conflicts(cmd[p][id2], c) /\ MaxTs(initTimestamp[id2], t) = t) }
            IN
            /\ msgs' = (msgs \cup { AcceptOKMsg(p, q, b, id, Dq) }) \ {m}
    /\ UNCHANGED << submitted, initCoord, initTimestamp, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar  >>

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
    /\ UNCHANGED << bal, submitted, initCoord, initTimestamp, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar >>

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
       /\ UNCHANGED << bal, submitted, initCoord, initTimestamp, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar >>



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
    /\ UNCHANGED << bal, cmd, dep, ts, abal, submitted, initCoord, initTimestamp, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar >>

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
        /\ UNCHANGED << bal, submitted, initCoord, initTimestamp, dep, abal, cmd, ts, recovered, Wvar, postWaitingFlag, recoveryAttemptBal, Cvar, Dvar >>

(***************************************************************************)
(* 51–54 StartRecover                                                      *)
(***************************************************************************)

StartRecover(p,id) ==
    /\ recovered[p][id] < NumberOfRecoveryAttempts
    /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE] 
    /\ recovered' = [recovered EXCEPT ![p][id] = recovered[p][id] + 1]
    \* Ballots owned by p are of the form k*N + p.
    /\  LET  b == IF bal[p][id] = 0 THEN p ELSE bal[p][id] + Cardinality(Proc)
        IN
        IF phase[p][id] # InitialPhase THEN msgs' = msgs \cup { RecoverMsg(p,q,b,id,cmd[p][id]) : q \in Proc }
        ELSE msgs' = msgs \cup { RecoverMsg(p,q,b,id,Nop) : q \in Proc }
    /\ UNCHANGED <<bal, phase, cmd, dep, ts, abal, submitted, initCoord, initTimestamp, Wvar, recoveryAttemptBal, Cvar, Dvar>>

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
                     ELSE {id2 \in Id : (Conflicts(cmd[p][id2], c) /\ LessThanTs(initTimestamp[id2], initTimestamp[id])) }
            IN
            /\  LET S == {id2 \in Id : (id2 # id /\ Conflicts(id2, id) /\ cmd[p][id2] # Nop /\ id \notin dep[p][id2]
                        /\(   (phase[p][id2] \in {CommittedPhase, StablePhase} /\ LessThanTs(initTimestamp[id], ts[p][id2]))  
                            \/ (   phase[p][id2] = AcceptedPhase   /\   LessThanTs( initTimestamp[id] ,  initTimestamp[id2])) 
                            )          ) 
                        }
                    W == {<<id3,abal[p][id3]>> : id3 \in { id2 \in Id : (id2 # id /\ Conflicts(id2, id) /\ cmd[p][id2] # Nop /\ id \notin dep[p][id2] 
                        /\ phase[p][id2] = AcceptedPhase /\ LessThanTs(initTimestamp[id2],initTimestamp[id])
                        /\ LessThanTs(initTimestamp[id],ts[p][id2])
                        )}}
                IN
                IF S # {}
                THEN msgs' = (msgs \cup {RecoverOkMsg(p,q,b,id,abal[p][id],cmd[p][id],ts[p][id],D,phase[p][id],TRUE,W)}) \ {m} 
                ELSE msgs' = (msgs \cup {RecoverOkMsg(p,q,b,id,abal[p][id],cmd[p][id],ts[p][id],D,phase[p][id],FALSE,W)}) \ {m}
    /\ UNCHANGED << submitted, initCoord, initTimestamp, dep, abal, ts, phase, recovered, Cvar, Dvar, postWaitingFlag, Wvar, recoveryAttemptBal  >>

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
                            /\ UNCHANGED <<bal, Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag>> 
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = CommittedPhase)
                THEN
                        /\  LET n == CHOOSE n \in U :
                                        n.body.phaseq = CommittedPhase
                            IN
                            LET Dq == { id2 \in Id : (Conflicts(cmd[p][id2], cmd[p][id]) /\ LessThanTs(initTimestamp[id2], n.body.tq) ) }
                            IN 
                            /\ msgs' = (msgs \cup {CommitMsg(p, q, bal[p][id], id, n.body.tq, n.body.depq, n.body.phaseq, n.body.cq) : q \in Proc \ {p} } \cup {CommitOkMsg(p,p,bal[p][id],id)}) \ quorumOfMessages
                            /\ ApplyCommit(p, p, bal[p][id], id, n.body.tq, n.body.depq, n.body.phaseq, n.body.cq)
                            /\ UNCHANGED <<bal ,Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag>>  
                ELSE IF (\E n \in U :
                        /\ n.body.phaseq = AcceptedPhase)
                THEN    
                        /\  LET n == CHOOSE n \in U :
                                n.body.phaseq = AcceptedPhase
                            IN
                            LET Dq == { id2 \in Id : (Conflicts(cmd[p][id2], cmd[p][id]) /\ LessThanTs(initTimestamp[id2], n.body.tq) ) }
                            IN 
                            /\ ApplyAccept(p,p,bal[p][id],id,n.body.tq,n.body.depq,n.body.cq)
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p,q,bal[p][id],id,n.body.tq,n.body.depq,n.body.cq) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)}
                            /\ UNCHANGED <<Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag>> 
                ELSE IF (   LET Rmax == { n \in quorumOfMessages :
                                                /\ n.body.phaseq = PreAcceptedPhase
                                                /\ n.body.tq = initTimestamp[id] }
                            IN Cardinality(Rmax) >= Cardinality(quorumOfMessages) - E)
                        THEN
                        LET rejects == {m \in quorumOfMessages : m.body.rejectq = TRUE}
                        IN
                        IF rejects # {}
                        THEN 
                            LET n == CHOOSE n \in rejects : TRUE
                            IN
                            LET Dq == { id2 \in Id : (Conflicts(cmd[p][id2], cmd[p][id]) /\ LessThanTs(initTimestamp[id2], n.body.tq) ) }
                            IN  
                            /\ ApplyAccept(p,p,bal[p][id],id,n.body.tq,n.body.depq,Nop)
                            /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p,q,bal[p][id],id,n.body.tq,n.body.depq,Nop) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)}
                            /\ UNCHANGED <<Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag>> 
                        ELSE 
                            LET n == CHOOSE n \in quorumOfMessages : n.body.phaseq = PreAcceptedPhase
                                Wall == UNION {m.body.Wq : m \in quorumOfMessages}
                            IN
                            LET c == n.body.cq
                                W == {<<id1, bal1>> \in Wall : \A <<id2, bal2>> \in Wall : bal2 <= bal1}
                                D == UNION {m.body.depq : m \in quorumOfMessages}
                            IN
                            /\ Cvar' = [Cvar EXCEPT  ![p][id] = c]
                            /\ Wvar' = [Wvar EXCEPT  ![p][id] = W]
                            /\ Dvar' = [Dvar EXCEPT  ![p][id] = D]
                            /\ recoveryAttemptBal' = [recoveryAttemptBal EXCEPT ![p][id] = bal[p][id]]
                            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = TRUE]
                            /\ UNCHANGED <<bal, cmd, abal, ts, dep, phase, msgs>>
                ELSE
                    LET Dq == { id2 \in Id : (Conflicts(cmd[p][id2], cmd[p][id]) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
                    IN  
                    /\ ApplyAccept(p,p,bal[p][id],id,ts[p][id],dep[p][id],Nop)
                    /\ msgs' = (msgs \ quorumOfMessages) \cup { AcceptMsg(p,q,bal[p][id],id,ts[p][id],dep[p][id],Nop) : q \in Proc \ {p} } \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)} 
                    /\ UNCHANGED <<Cvar, Wvar, Dvar, recoveryAttemptBal, postWaitingFlag>>   
    /\ UNCHANGED <<submitted, initCoord, initTimestamp, recovered >>
            
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
            Dq == { id2 \in Id : (Conflicts(cmd[p][id2], cmd[p][id]) /\ LessThanTs(initTimestamp[id2], initTimestamp[id]) ) }
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
        IN 
        \/  /\ Case1
            /\ ApplyAccept(p,p,bal[p][id],id,ts[p][id],dep[p][id],Nop)
            /\ msgs' = msgs \cup { AcceptMsg(p,q,bal[p][id],id,ts[p][id],dep[p][id],Nop) : q \in Proc \ {p} }
                        \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)}
            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]

        \/  /\ Case2
            /\ ApplyAccept(p,p,bal[p][id],id,initTimestamp[id],D,c)
            /\ msgs' = msgs \cup { AcceptMsg(p,q,bal[p][id],id,initTimestamp[id],D,c) : q \in Proc \ {p} }
                        \cup {AcceptOKMsg(p,p,bal[p][id],id,Dq)}
            /\ postWaitingFlag' = [postWaitingFlag EXCEPT ![p][id] = FALSE]

        \/  /\ ~Case1 /\ ~Case2
            /\ UNCHANGED << msgs, postWaitingFlag, bal, dep, phase, abal, cmd, ts >>
                    
        
    /\ UNCHANGED << submitted, initCoord, initTimestamp, recovered, Wvar, recoveryAttemptBal, Cvar, Dvar >>


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)                 

Agreement ==
  \A id \in Id :
    \A p, q \in Proc :
      /\ phase[p][id] = CommittedPhase
      /\ phase[q][id] = CommittedPhase
      => /\ dep[p][id] = dep[q][id]
         /\ cmd[p][id] = cmd[q][id]
         /\ ts[p][id] = ts[q][id]

Visibility ==
  \A id1, id2 \in Id : \A p, q \in Proc :
    /\ id1 # id2
    /\ cmd[p][id1] # Nop
    /\ cmd[q][id2] # Nop 
    /\ phase[p][id1] = CommittedPhase
    /\ phase[q][id2] = CommittedPhase
    /\ Conflicts(cmd[p][id1], cmd[q][id2])
    /\ LessThanTs(ts[p][id1], ts[q][id2])
    => \/ id1 \in dep[q][id2]

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
    /\ initTimestamp = [id \in Id |-> [t |-> 0, id |-> 0]]
    /\ recovered = [p \in Proc |-> [id \in Id |-> 0]]
    /\ Wvar = [p \in Proc |-> [id \in Id |-> 0]]
    /\ Cvar = [p \in Proc |-> [id \in Id |-> Bottom]]
    /\ Dvar = [p \in Proc |-> [id \in Id |-> {}]]
    /\ postWaitingFlag = [p \in Proc |-> [id \in Id |-> FALSE]]
    /\ recoveryAttemptBal = [p \in Proc |-> [id \in Id |-> 0]]



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