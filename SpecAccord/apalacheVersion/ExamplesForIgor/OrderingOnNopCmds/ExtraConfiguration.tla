----------------------------- MODULE ExtraConfiguration -----------------------------
EXTENDS Naturals, Sequences, typedefs

\* Model checking parameters


\* Conflict relation
\* @type: Set(<<Int, Int>>);
ConflictPairs == {
    <<1, 2>>,
    <<1, 3>>
}

\* Initial timestamp values
\* @type: Seq($timestamp);
initTimestampConstant == <<[id |-> 0, t |-> 0], [id |-> 0, t |-> 2], [id |-> 0 , t |-> 1]>>

=============================================================================