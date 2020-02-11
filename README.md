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
- [x] Message
  - +`REPLICATE`
  - +`HEARTBEAT`
- [x] Clock
  - Tick as a separate action
    - `Clock[p][d]`
    - `pvc[p][d]`
  - Change `<=` in the waiting condition of `UPDATE_REQUEST` to `<`?
  - `tick` for `Heartbeat`
- [x] Computing CSS
### 2020-01-16
- [x] email
  - [x] "latest version"
  - [x] FIFO channel for propagating updates
  - [x] `UpdateCSS`: `css[m][d][d]` not necessary?
### 2020-01-21
- [x] FIFO channel for propagating updates and heartbeats
  - `incoming[p][d]`
    - one incoming channel for each partition (NOW)
    - `d \in Datacenter` incoming channels for each partition
- [x] `UpdateCSS`: 
  - [x] Also computing `css[m][d][d]`, for simplicity 
- [x] `i # d` in Line 3 and Line 8
  - [x] Delete such conditions, for simplicity
### 2020-01-23
- [x] Fixing one (`pvc`) `'` problem
- [x] Fixing `pvc` updating error
### 2020-01-25
- [x] Delete `Clock == Nat`
- [x] Spec for CM: CausalMemory
  - [x] +`L[c]` for history
    - [x] Recording `L[c]` in `ReadRequest` & `UpdateRequest`
    - [x] +`OpTuple`
  - [x] causality order
    - [x] `so` order
    - [x] `write-into` order
- [x] Module `Relation`
  - [x] +`SeqToRel`
### 2020-01-26
- [x] Handling `NotVal` in `CM`
  - [x] Redefine `Valid(s)` with initial values for keys
- [x] Testing `CM`
  - [x] +state constraint: `\A c \in Client: Len(L[c]) <= 3`

### 2020-01-27
- [ ] Testing `CM`
  - [x] FIXME: `Range(seq)` duplicate elements in sequence
    - [x] +`c : Client, cnt : Nat` in `OpTuple`
- [ ] `CureKV`: 

### 2020-01-28
- [ ] `S[c]` for serialization

### 2020-01-29
- [ ] `n^5` checking algorithm for CM

### 2020-01-30
- [ ] CureKV

## TODO
- Version without Heartbeat
  - Check liveness
- Properties
  - Safety
    - `TypeOK`
    - `cvc[c]` non-decreasing 
    - `css[p][d]` non-decreasing
    - CM
  - Liveness


## TLA+
- [ ] googlegroup: "checking safety upon termination only?"
- [ ] CostModel:
> CostModel lookup failed for expression `<line 54, col 36 to line 54, col 67 of module Cure>`.
Reporting costs into `<line 52, col 22 to line 54, col 67 of module Cure>` instead 
(Safety and Liveness checking is unaffected. Please report a bug.)
