----------------------------- MODULE typedefs -----------------------------
EXTENDS Variants

\* Type definitions:
\*
\* Timestamps.
\* @typeAlias: timestamp = {id : Int, t : Int};
\*
\* preAcceptMessage inner record.
\* @typeAlias: preAcceptMessage = { from: Int, to: Int, body: {id: Int, tx: Int, D0: Set(Int)} };
\*
\* preAcceptOKMessage inner record.
\* @typeAlias: preAcceptOKMessage = { from: Int, to: Int, body: {id: Int, tq: $timestamp, Dq: Set(Int)} };
\*
\* acceptMessage inner record.
\* @typeAlias: acceptMessage = { from: Int, to: Int, body: {id: Int, b: Int, t: $timestamp, D: Set(Int), tx: Int} };
\*
\* acceptOKMessage inner record.
\* @typeAlias: acceptOKMessage = { from: Int, to: Int, body: {id: Int, b: Int, Dq: Set(Int)} };
\*
\* commitMessage inner record.
\* @typeAlias: commitMessage = { from: Int, to: Int, body: {id: Int, b: Int, t: $timestamp, D: Set(Int), pathSpeed: SPEED, tx: Int} };
\*
\* commitOKMessage inner record.
\* @typeAlias: commitOKMessage = { from: Int, to: Int, body: {id: Int, b: Int} };
\*
\* stableMessage inner record.
\* @typeAlias: stableMessage = { from: Int, to: Int, body: {id: Int, b: Int} };
\*
\* recoverMessage inner record.
\* @typeAlias: recoverMessage = { from: Int, to: Int, body: {id: Int, b: Int, tx: Int} };
\*
\* recoverOKMessage inner record.
\* @typeAlias: recoverOKMessage = { from: Int, to: Int, body: {id: Int, b: Int, abalq: Int, txq: Int, tq: $timestamp, depq: Set(Int), phaseq: Int, rejectq: Bool, Wq: Set(<<Int,Int>>), WPq: Set(Int)} };
\*
\* Message type uses Variants module.
\* @typeAlias: message =
\*     PreAcceptMessage($preAcceptMessage)
\*   | PreAcceptOKMessage($preAcceptOKMessage)
\*   | AcceptMessage($acceptMessage)
\*   | AcceptOKMessage($acceptOKMessage)
\*   | CommitMessage($commitMessage)
\*   | CommitOKMessage($commitOKMessage)
\*   | StableMessage($stableMessage)
\*   | RecoverMessage($recoverMessage)
\*   | RecoverOKMessage($recoverOKMessage);

TypeAliases == TRUE

\* @type: (Int, Int, Int, Int, Set(Int)) => $message;
PreAcceptMsg(p, q, id, tx, D0) ==
    Variant("PreAcceptMessage",
        [from |-> p, to |-> q, body |-> [id |-> id, tx |-> tx, D0 |-> D0]])

\* @type: (Int, Int, Int, $timestamp, Set(Int)) => $message;
PreAcceptOKMsg(p, q, id, tq, Dq) ==
    Variant("PreAcceptOKMessage",
        [from |-> p, to |-> q, body |-> [id |-> id, tq |-> tq, Dq |-> Dq]])

\* @type: (Int, Int, Int, Int, $timestamp, Set(Int), Int) => $message;
AcceptMsg(p, q, b, id, t, D, tx) ==
    Variant("AcceptMessage",
        [from |-> p, to |-> q, body |-> [id |-> id, b |-> b, t |-> t, D |-> D, tx |-> tx]])

\* @type: (Int, Int, Int, Int, Set(Int)) => $message;
AcceptOKMsg(p, q, b, id, Dq) ==
    Variant("AcceptOKMessage",
        [from |-> p, to |-> q, body |-> [id |-> id, b |-> b, Dq |-> Dq]])

\* @type: (Int, Int, Int, Int, $timestamp, Set(Int), SPEED, Int) => $message;
CommitMsg(p, q, b, id, t, D, pathSpeed, tx) ==
    Variant("CommitMessage",
        [from |-> p, to |-> q, body |-> [id |-> id, b |-> b, t |-> t, D |-> D, pathSpeed |-> pathSpeed, tx |-> tx]])

\* @type: (Int, Int, Int, Int) => $message;
CommitOkMsg(p, q, b, id) ==
    Variant("CommitOKMessage",
        [from |-> p, to |-> q, body |-> [id |-> id, b |-> b]])

\* @type: (Int, Int, Int, Int) => $message;
StableMsg(p, q, b, id) ==
    Variant("StableMessage",
        [from |-> p, to |-> q, body |-> [id |-> id, b |-> b]])

\* @type: (Int, Int, Int, Int, Int) => $message;
RecoverMsg(p, q, b, id, tx) ==
    Variant("RecoverMessage",
        [from |-> p, to |-> q, body |-> [id |-> id, b |-> b, tx |-> tx]])

\* @type: (Int, Int, Int, Int, Int, Int, $timestamp, Set(Int), Int, Bool, Set(<<Int,Int>>), Set(Int)) => $message;
RecoverOkMsg(p, q, b, id, abalq, txq, tq, depq, phaseq, rejectq, Wq, WPq) ==
    Variant("RecoverOKMessage",
        [from |-> p, to |-> q, body |-> [id |-> id, b |-> b, abalq |-> abalq, txq |-> txq, tq |-> tq, depq |-> depq, phaseq |-> phaseq, rejectq |-> rejectq, Wq |-> Wq, WPq |-> WPq]])

\* @type: $message => $preAcceptMessage;
UnwrapPreAccept(m) == VariantGetUnsafe("PreAcceptMessage", m)

\* @type: $message => $preAcceptOKMessage;
UnwrapPreAcceptOK(m) == VariantGetUnsafe("PreAcceptOKMessage", m)

\* @type: $message => $acceptMessage;
UnwrapAccept(m) == VariantGetUnsafe("AcceptMessage", m)

\* @type: $message => $acceptOKMessage;
UnwrapAcceptOK(m) == VariantGetUnsafe("AcceptOKMessage", m)

\* @type: $message => $commitMessage;
UnwrapCommit(m) == VariantGetUnsafe("CommitMessage", m)

\* @type: $message => $commitOKMessage;
UnwrapCommitOK(m) == VariantGetUnsafe("CommitOKMessage", m)

\* @type: $message => $stableMessage;
UnwrapStable(m) == VariantGetUnsafe("StableMessage", m)

\* @type: $message => $recoverMessage;
UnwrapRecover(m) == VariantGetUnsafe("RecoverMessage", m)

\* @type: $message => $recoverOKMessage;
UnwrapRecoverOK(m) == VariantGetUnsafe("RecoverOKMessage", m)

=============================================================================