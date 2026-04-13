----------------------------- MODULE ExtraConfiguration -----------------------------
EXTENDS Naturals, Sequences

\*constant to define the conflict relation,
ConflictPairs == {
    <<1, 2>>,
    <<1, 3>>
}

\* Constant to define initial timestamp values for the commands, injected into initTimestamp var, this value can be redefined on submission when necessary
\* (a single process can't submit a second command with a lower timestamp than the first), the id is defined on submission.
initTimestampConstant == <<[id |-> 0, t |-> 0], [id |-> 0, t |-> 2], [id |-> 0 , t |-> 1]>>

=============================================================================