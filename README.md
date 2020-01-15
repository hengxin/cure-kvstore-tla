# cure-kvstore-tla
TLA+ Spec for the Cure Key-Value Store

## Design Choices for TLA+ Spec
- Data Sharding
  - `Sharding` is a mapping from `Key` to `Partition`
    1. Random mapping in each model checking (not `CHOOSE`; try `RandomElement`)
    2. As a part of model
- `Clock[p][d]`
  - `Tick` as an associated action; executed after each other action?
  - Tick as a separate action? (Seems Better!!!)
    - `Clock[p][d]`
    - `pvc[p][d]`
  - Change `<=` in the waiting condition of `UPDATE_REQUEST` to `<`?
  - Using `JavaTime`?
    - NO! This would introduce a global wall clock.
- `Value`
  - does not matter
  - can be eliminated
  - Now: `Value = {v}`
- Client-server interaction
  - using `msgs`
  - well-formedness of clients
- "wait until"
- `PMC`
  - not necessary for TLA+

## Progress
### 2020-01-15
- Message
  - +`REPLICATE`
  - +`HEARTBEAT`
- Clock
  - Tick as a separate action
    - `Clock[p][d]`
    - `pvc[p][d]`
  - Change `<=` in the waiting condition of `UPDATE_REQUEST` to `<`?
  - `tick` for `Heartbeat`
- CSS
### 2020-01-16
### 2020-01-17
