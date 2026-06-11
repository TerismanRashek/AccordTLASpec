----------------------------- MODULE ExtraConfiguration -----------------------------
EXTENDS Naturals, Sequences

\* Model checking parameters

\* Command to shards relation
idToShard == [i \in {1, 2} |->
                  CASE i = 1 -> {1}
                    [] i = 2 -> {1}]

\* Conflict relation
ConflictPairs == {
    <<1, 2>>
}

\* Initial timestamp values
initTimestampConstant == <<[id |-> <<0, 0>>, t |-> 1], [id |-> <<0, 0>>, t |-> 2], [id |-> <<0, 0>> , t |-> 3]>>

=============================================================================
