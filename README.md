# cure-kvstore-tla
TLA+ Spec for the Cure Key-Value Store

## Design Choices for TLA+ Spec
- Data Sharding
  - `Sharding` is a mapping from `Key` to `Partition`
    1. Random mapping in each model checking (not `CHOOSE`)
    2. As a part of model
- `Clock[p][d]`
- `Value`
  - does not matter
  - can be eliminated
