------------------------------ MODULE Cure ------------------------------- 
(*
  See ICDCS2016: "Cure: Strong Semantics Meets High Availability and Low Latency".
*)

EXTENDS Naturals, Sequences, TLC
--------------------------------------------------------------------------
CONSTANTS 
    Key,         \* the set of keys, ranged over by k \in Key
    Value,       \* the set of values, ranged over by v \in Value 
    Client,      \* the set of clients, ranged over by c \in Client
    Partition,   \* the set of partitions, ranged over by p \in Partition
    Datacenter,  \* the set of datacenters, ranged over by d \in Datacenter
    KeySharding,      \* the mapping from Key to Partition
    ClientAttachment  \* the mapping from Client to Datacenter
    
ASSUME 
    /\ KeySharding \in [Key -> Partition]
    /\ ClientAttachment \in [Client -> Datacenter]
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
    updates, \* updates[p][d]: the buffer of updates
(* Client-server communication *)
    msgs  \* the set of messages in transit

cVars == <<cvc>>
sVars == <<clock, pvc, css, PMC, store, updates>>
mVars == <<msgs>>
vars == <<cvc, clock, pvc, css, PMC, store, updates, msgs>>
--------------------------------------------------------------------------
Clock == Nat
VC == [Datacenter -> Clock]  \* vector clock with an entry per datacenter d \in Datacenter
VCInit == [d \in Datacenter |-> 0]
KVTuple == [key : Key, val : Value, vc : VC]

Message ==
         [type : {"ReadRequest"}, key : Key, vc : VC, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"ReadReply"}, val : Value, vc : VC, c : Client]
    \cup [type : {"UpdateRequest"}, key : Key, val : Value, vc : VC, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"UpdateReply"}, ts : Clock, c : Client, d : Datacenter]

TypeOK == 
    /\ cvc \in [Client -> VC]
    /\ clock \in [Partition -> [Datacenter -> Clock]]
    /\ pvc \in [Partition -> [Datacenter -> VC]]
    /\ css \in [Partition -> [Datacenter -> VC]]
    /\ PMC \in [Partition -> [Datacenter -> [Partition -> VC]]]
    /\ store \in [Partition -> [Datacenter -> SUBSET KVTuple]]
    /\ updates \in [Partition -> [Datacenter -> Seq(KVTuple)]]
    /\ msgs \subseteq Message
--------------------------------------------------------------------------
Init ==
    /\ cvc = [c \in Client |-> VCInit]   
    /\ clock = [p \in Partition |-> [d \in Datacenter |-> 0]]
    /\ pvc = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ css = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ PMC = [p \in Partition |-> [d \in Datacenter |-> [q \in Partition |-> VCInit]]]
    /\ store = [p \in Partition |-> [d \in Datacenter |-> {}]]
    /\ updates = [p \in Partition |-> [d \in Datacenter |-> <<>>]]
    /\ msgs = {}
--------------------------------------------------------------------------
Max(a, b) == IF a < b THEN b ELSE a

Send(m) == msgs' = msgs \cup {m}

Ready2Issue(c) == \A m \in msgs: 
    m.type \in {"ReadRequest", "ReadReply", "UpdateRequest", "UpdateReply"} => m.c # c 
--------------------------------------------------------------------------
(* Client operations at client c \in Client. *)

Read(c, k) == \* c \in Client reads from k \in Key
    /\ Ready2Issue(c)
    /\ Send([type |-> "ReadRequest", key |-> k, vc |-> cvc[c], 
             c |-> c, p |-> KeySharding[k], d |-> ClientAttachment[c]])
    /\ UNCHANGED <<cVars, sVars>>

ReadReply(c) == \* c \in Client handles the reply to its read request
    /\ \E m \in msgs: 
        /\ m.type = "ReadReply" /\ m.c = c  \* such m is unique
        /\ cvc' = [d \in Datacenter |-> Max(m.vc[d], cvc[d])]
    /\ UNCHANGED <<sVars, mVars>>
    
Update(c, k, v) == \* c \in Client updates k \in Key with v \in Value
    /\ Ready2Issue(c)
    /\ Send([type |-> "UpdateRequest", key |-> k, val |-> v,
             vc |-> cvc[c], c |-> c, p |-> KeySharding[k], d |-> ClientAttachment[c]])
    /\ UNCHANGED <<cVars, sVars>>             
    
UpdateReply(c) == \* c \in Client handles the reply to its update request
    /\ \E m \in msgs:
        /\ m.type = "UpdateReply" /\ m.c = c \* such m is unique
        /\ cvc' = [cvc EXCEPT ![c][m.d] = m.ts]
    /\ UNCHANGED <<sVars, mVars>>
--------------------------------------------------------------------------
(* Server operations at partition p \in Partition in datacenter d \in Datacenter. *)

UpdateRequest(p, d) ==
    /\ \E m \in msgs:
        /\ m.type = "UpdateRequest" /\ m.p = p /\ m.d = d  \* such m may be not unique
        /\ m.vc[d] <= clock[p][d]  \* waiting condition
        /\ pvc' = [pvc EXCEPT ![p][d][d] = clock[p][d]]
        /\ css' = [css EXCEPT ![p][d] = 
            [dc \in Datacenter |-> IF dc = d THEN @[dc] ELSE Max(m.vc[dc], @[dc])]]
        /\ LET kv == [key |-> m.key, val |-> m.val, 
                       vc |-> [m.vc EXCEPT ![d] = clock[p][d]]]
           IN /\ store' = [store EXCEPT ![p][d] = @ \cup {kv}] 
              /\ updates' = [updates EXCEPT ![p][d] = @ \o <<kv>>]
              /\ Send([type |-> "UpdateReply", ts |-> clock[p][d], c |-> m.c, d |-> d])
    /\ UNCHANGED <<cVars, clock, PMC>>
--------------------------------------------------------------------------
Next == 
    \/ \E c \in Client, k \in Key: Read(c, k)
    \/ \E c \in Client, k \in Key, v \in Value: Update(c, k, v)
    \/ \E c \in Client: ReadReply(c) \/ UpdateReply(c)
    \/ \E p \in Partition, d \in Datacenter: UpdateRequest(p, d)

Spec == Init /\ [][Next]_vars
--------------------------------------------------------------------------
=============================================================================