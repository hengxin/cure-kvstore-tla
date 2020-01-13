------------------------------ MODULE Cure ------------------------------- 
(*
  See ICDCS2016: "Cure: Strong Semantics Meets High Availability and Low Latency".
*)

EXTENDS Naturals, Sequences
--------------------------------------------------------------------------
CONSTANTS 
    Key,         \* the set of keys, ranged over by k \in Key
    Value,       \* the set of values, ranged over by v \in Value 
    Client,      \* the set of clients, ranged over by c \in Client
    Partition,   \* the set of partitions, ranged over by p \in Partition
    Datacenter,  \* the set of datacenters, ranged over by d \in Datacenter
    Sharding     \* the mapping from Key to Partition
    
ASSUME Sharding \in [Key -> Partition]
--------------------------------------------------------------------------
VARIABLES 
(* At the client side: *)
    cvc,  \* cvc[c]: the vector clock of client c \in Client
(* At the server side (each for partition p \in Partition in d \in Datacenter): *)
    clock,   \* clock[p][d]: the current clock
    pvc,     \* pvc[p][d]: the vector clock
    css,     \* css[p][d]: the stable snapshot
    PMC,     \* PMC[p][d]: matrix clock
    store,   \* store[p][d]: the kv store
    updates  \* updates[p][d]: the buffer of updates
    
vars == <<cvc, clock, pvc, css, PMC, store, updates>>
--------------------------------------------------------------------------
Clock == Nat
VC == [Datacenter -> Clock]  \* vector clock with an entry per datacenter d \in Datacenter
VCInit == [d \in Datacenter |-> 0]
KVTuple == [key : Key, val : Value, vc : VC]

TypeOK == 
    /\ cvc \in [Client -> VC]
    /\ clock \in [Partition -> [Datacenter -> Clock]]
    /\ pvc \in [Partition -> [Datacenter -> VC]]
    /\ css \in [Partition -> [Datacenter -> VC]]
    /\ PMC \in [Partition -> [Datacenter -> [Partition -> VC]]]
    /\ store \in [Partition -> [Datacenter -> SUBSET KVTuple]]
    /\ updates \in [Partition -> [Datacenter -> Seq(KVTuple)]]
--------------------------------------------------------------------------
Init ==
    /\ cvc = [c \in Client |-> VCInit]   
    /\ clock = [p \in Partition |-> [d \in Datacenter |-> 0]]
    /\ pvc = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ css = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ PMC = [p \in Partition |-> [d \in Datacenter |-> [q \in Partition |-> VCInit]]]
    /\ store = [p \in Partition |-> [d \in Datacenter |-> {}]]
    /\ updates = [p \in Partition |-> [d \in Datacenter |-> <<>>]]
--------------------------------------------------------------------------
(* Client operations at client c \in Client. *)
--------------------------------------------------------------------------
(* Server operations at partition p \in Partition in datacenter d \in Datacenter. *)
--------------------------------------------------------------------------
(* Spec *)
Next == TRUE

Spec == Init /\ [][Next]_vars
--------------------------------------------------------------------------
=============================================================================