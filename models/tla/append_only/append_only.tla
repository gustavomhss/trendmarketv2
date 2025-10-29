---- MODULE append_only ----
EXTENDS Sequences, Naturals

CONSTANTS HashSet, Merkle

ASSUME Merkle \in [Seq(HashSet) -> HashSet]

VARIABLES root, batches

NullHash == Merkle(<< >>)

Init == /\ root = NullHash
        /\ batches = << >>

Append(batch) ==
    /\ batch \in HashSet
    /\ batches' = Append(batches, batch)
    /\ root' = Merkle(batches')

Next == \E batch \in HashSet : Append(batch)

Spec == Init /\ [][Next]_<<root, batches>>

TypeInvariant == /\ root \in HashSet
                 /\ batches \in Seq(HashSet)
                 /\ root = Merkle(batches)

MerkleRootMonotonic == [](root = Merkle(batches))
NoRollbackAction == Len(batches') >= Len(batches)
NoRollback == [] [NoRollbackAction]_<<root, batches>>

THEOREM Spec => []TypeInvariant

====
