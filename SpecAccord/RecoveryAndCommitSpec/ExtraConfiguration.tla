----------------------------- MODULE ExtraConfiguration -----------------------------
EXTENDS Naturals, Sequences

\* Model checking parameters

\* Conflict relation
ConflictPairs == {
    <<1, 2>>
}

\* Initial timestamp values
initTimestampConstant == <<[id |-> 0, t |-> 0], [id |-> 0, t |-> 2], [id |-> 0 , t |-> 1]>>

=============================================================================