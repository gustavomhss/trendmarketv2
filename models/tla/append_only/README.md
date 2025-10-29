# Append-only Merkle Model

This module models the append-only behaviour of the oracle Merkle accumulator. Run TLC with the provided configuration:

```bash
tlc2.TLC models/tla/append_only/append_only.tla -config models/tla/append_only/append_only.cfg
```

The configuration constrains the abstract hash universe to a finite set so TLC can exhaustively explore the state space. The invariants `MerkleRootMonotonic` and `NoRollback` ensure the Merkle root always reflects the accumulated batches and that no history rewrites occur.
