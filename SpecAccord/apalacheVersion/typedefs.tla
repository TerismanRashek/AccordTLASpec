----------------------------- MODULE typedefs -----------------------------
EXTENDS Variants


\* Type definitions:
\*
\* 
\*
\* Type proc Id, shard and PROC pair.
\* @typeAlias: procIdType = { shard: Int, proc: Int };
\* 
\* 
\* preAcceptMessages messages.
\* @typeAlias: preAcceptMessage = { type: Int, sp: Int, p: Int, sq: Int, q: Int, body: {id: Int, tx: Int, D0: Set(Int)} };
\*
\* preAcceptOKMessages.
\* @typeAlias: preAcceptOKMessage = { type: Int, sp: Int, p: Int, sq: Int, q: Int, body: {id: Int, tq: TIMESTAMP, Dq: Set(Int)} };
\*
\* AcceptMessages.
\* @typeAlias: acceptMessage = { type: Int, sp: Int, p: Int, sq: Int, q: Int, body: {id: Int, b: Int, t: TIMESTAMP, D: Set(Int), tx: Int, pathSpeed: SPEED} };
\*
\* AcceptOKMessages.
\* @typeAlias: acceptOKMessage = { type: Int, sp: Int, p: Int, sq: Int, q: Int, body: {id: Int, b: Int, Dq: Set(Int), pathSpeed: SPEED} };
\*
\* CommitMessages.
\* @typeAlias: commitMessage = { type: Int, sp: Int, p: Int, sq: Int, q: Int, body: {id: Int, b: Int, t: TIMESTAMP, D: Set(Int), pathSpeed: SPEED, tx: Int} };
\*
\* CommitOKMessages.
\* @typeAlias: commitOKMessage = { type: Int, sp: Int, p: Int, sq: Int, q: Int, body: {id: Int, b: Int} };
\* 
\* StableMessages.
\* @typeAlias: stableMessage = { type: Int, sp: Int, p: Int, sq: Int, q: Int, body: {id: Int, b: Int} };
\* 
\* RecoverMessages.
\* @typeAlias: recoverMessage = { type: Int, sp: Int, p: Int, sq: Int, q: Int, body: {id: Int, b: Int, tx: Int} };
\*
\* RecoverOKMessages.
\* @typeAlias: recoverOKMessage = { type: Int, sp: Int, p: Int, sq: Int, q: Int, body: {id: Int, b: Int, abalq: Int, txq: Int, tq: TIMESTAMP , depq: Set(Int), phaseq: PHASE, rejectq: Bool, Wq: Set(<<Int,Int>>), WPq: Set(Int)} };
\* 
\* type Message = $preAcceptMessage | $preAcceptOKMessage | $acceptMessage | $acceptOKMessage | $commitMessage | $commitOKMessage | $stableMessage | $recoverMessage | $recoverOKMessage;

TypeAliases == TRUE

\* Message types
TypePreAccept == 1
TypePreAcceptOK == 2
TypeAccept == 3
TypeAcceptOK == 4
TypeCommit == 5
TypeCommitOK == 6
TypeStable == 7
TypeRecover == 8
TypeRecoverOK == 9

\* @type: (Int, Int, Int, Int, Int, Int, Set(Int)) => $preAcceptMessage;
PreAcceptMsg(sp, p, sq, q, id, tx, D0) ==
    [type |-> TypePreAccept, sp |-> sp, p |-> p, sq |-> sq, q |-> q, body |->  [id |-> id, tx |-> tx, D0 |-> D0]]

\* @type: (Int, Int, Int, Int, Int, TIMESTAMP, Set(Int)) => $preAcceptOKMessage;
PreAcceptOKMsg(sp, p, sq, q, id, tq, Dq) ==
    [type |-> TypePreAcceptOK, sp |-> sp, p |-> p, sq |-> sq, q |-> q, body |->  [id |-> id, tq |-> tq, Dq |-> Dq]]

\* @type: (Int, Int, Int, Int, Int, Int, TIMESTAMP, Set(Int), Int, SPEED) => $acceptMessage;
AcceptMsg(sp, p, sq, q, b, id, t, D, tx, pathSpeed) ==
    [type |-> TypeAccept, sp |-> sp, p |-> p, sq |-> sq, q |-> q, body |->  [id |-> id, b |-> b, t |-> t, D |-> D, tx |-> tx, pathSpeed |-> pathSpeed]]

\* @type: (Int, Int, Int, Int, Int, Int, Set(Int), SPEED) => $acceptOKMessage;
AcceptOKMsg(sp, p, sq, q, b, id, Dq, pathSpeed) ==
    [type |-> TypeAcceptOK, sp |-> sp, p |-> p, sq |-> sq, q |-> q, body |->  [id |-> id, b |-> b, Dq |-> Dq, pathSpeed |-> pathSpeed]]

\* @type: (Int, Int, Int, Int, Int, Int, TIMESTAMP, Set(Int), SPEED, Int) => $commitMessage;
CommitMsg(sp, p, sq, q, b, id, t, D, pathSpeed, tx) ==
    [type |-> TypeCommit, sp |-> sp, p |-> p, sq |-> sq, q |-> q, body |->  [id |-> id, b |-> b, t |-> t, D |-> D, pathSpeed |-> pathSpeed, tx |-> tx]]

\* @type: (Int, Int, Int, Int, Int, Int) => $commitOKMessage;
CommitOkMsg(sp, p, sq, q, b, id) ==
    [type |-> TypeCommitOK, sp |-> sp, p |-> p, sq |-> sq, q |-> q, body |->  [id |-> id, b |-> b]]

\* @type: (Int, Int, Int, Int, Int, Int) => $stableMessage;
StableMsg(sp, p, sq, q, b, id) ==
    [type |-> TypeStable, sp |-> sp, p |-> p, sq |-> sq, q |-> q, body |->  [id |-> id, b |-> b]]

\* @type: (Int, Int, Int, Int, Int, Int, Int) => $recoverMessage;
RecoverMsg(sp, p, sq, q, b, id, tx) ==
    [type |-> TypeRecover, sp |-> sp, p |-> p, sq |-> sq, q |-> q, body |->  [id |-> id, b |-> b, tx |-> tx]]

\* @type: (Int, Int, Int, Int, Int, Int, Int, Int, TIMESTAMP , Set(Int), PHASE, Bool, Set(<<Int,Int>>), Set(Int)) => $recoverOKMessage;
RecoverOkMsg(sp, p, sq, q, b, id, abalq, txq, tq, depq, phaseq, rejectq, Wq, WPq) ==
    [type |-> TypeRecoverOK, sp |-> sp, p |-> p, sq |-> sq, q |-> q, body |->  [id |-> id, b |-> b, abalq |-> abalq, txq |-> txq, tq |-> tq, depq |-> depq, phaseq |-> phaseq, rejectq |-> rejectq, Wq |-> Wq, WPq |-> WPq]]



=============================================================================