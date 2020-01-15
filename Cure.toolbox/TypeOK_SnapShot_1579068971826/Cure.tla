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
    
NotVal == CHOOSE v : v \notin Value    
    
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
(* Clock management *)
    tick, \* tick[p][d]: toggle on clock ticks
(* Client-server communication *)
    msgs  \* the set of messages in transit

cVars == <<cvc>>
sVars == <<clock, pvc, css, PMC, store, updates, tick>>
mVars == <<msgs>>
vars == <<cvc, clock, pvc, css, PMC, store, updates, tick, msgs>>
--------------------------------------------------------------------------
Clock == Nat
VC == [Datacenter -> Clock]  \* vector clock with an entry per datacenter d \in Datacenter
VCInit == [d \in Datacenter |-> 0]
KVTuple == [key : Key, val : Value \cup {NotVal}, vc : VC]

Message ==
         [type : {"ReadRequest"}, key : Key, vc : VC, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"ReadReply"}, val : Value \cup {NotVal}, vc : VC, c : Client]
    \cup [type : {"UpdateRequest"}, key : Key, val : Value, vc : VC, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"UpdateReply"}, ts : Clock, c : Client, d : Datacenter]
    \* d \in Datacenter: the source datacenter; dd \in Datacenter: the destination datacenter
    \cup [type : {"Replicate"}, d : Datacenter, kvs : Seq(KVTuple), p : Partition, dd : Datacenter]
    \cup [type : {"Heartbeat"}, d : Datacenter, ts : Clock, p : Partition, dd : Datacenter]

TypeOK == 
    /\ cvc \in [Client -> VC]
    /\ clock \in [Partition -> [Datacenter -> Clock]]
    /\ pvc \in [Partition -> [Datacenter -> VC]]
    /\ css \in [Partition -> [Datacenter -> VC]]
    /\ PMC \in [Partition -> [Datacenter -> [Partition -> VC]]]
    /\ store \in [Partition -> [Datacenter -> SUBSET KVTuple]]
    /\ updates \in [Partition -> [Datacenter -> Seq(KVTuple)]]
    /\ tick \in [Partition -> [Datacenter -> BOOLEAN]]
    /\ msgs \subseteq Message
--------------------------------------------------------------------------
Init ==
    /\ cvc = [c \in Client |-> VCInit]   
    /\ clock = [p \in Partition |-> [d \in Datacenter |-> 0]]
    /\ pvc = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ css = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ PMC = [p \in Partition |-> [d \in Datacenter |-> [q \in Partition |-> VCInit]]]
    /\ store = [p \in Partition |-> [d \in Datacenter |-> 
                    [key : {k \in Key : KeySharding[k] = p}, val : {NotVal}, vc : {VCInit}]]]
    /\ updates = [p \in Partition |-> [d \in Datacenter |-> <<>>]]
    /\ tick = [p \in Partition |-> [d \in Datacenter |-> FALSE]]
    /\ msgs = {}
--------------------------------------------------------------------------
Max(a, b) == IF a < b THEN b ELSE a
Range(f) == {f[x]: x \in DOMAIN f}
Last(seq) == seq[Len(seq)]

Send(m) == msgs' = msgs \cup {m}
SendSet(ms) == msgs' = msgs \cup ms
SendAndDelete(sm, dm) == msgs' = (msgs \cup {sm}) \ {dm}

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
        /\ cvc' = [cvc EXCEPT ![c] = [d \in Datacenter |-> Max(m.vc[d], @[d])]]
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<sVars>>
    
Update(c, k, v) == \* c \in Client updates k \in Key with v \in Value
    /\ Ready2Issue(c)
    /\ Send([type |-> "UpdateRequest", key |-> k, val |-> v,
             vc |-> cvc[c], c |-> c, p |-> KeySharding[k], d |-> ClientAttachment[c]])
    /\ UNCHANGED <<cVars, sVars>>             
    
UpdateReply(c) == \* c \in Client handles the reply to its update request
    /\ \E m \in msgs:
        /\ m.type = "UpdateReply" /\ m.c = c \* such m is unique
        /\ cvc' = [cvc EXCEPT ![c][m.d] = m.ts]
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<sVars>>
--------------------------------------------------------------------------
(* Server operations at partition p \in Partition in datacenter d \in Datacenter. *)

ReadRequest(p, d) == \* handle a "ReadRequest"
    /\ \E m \in msgs:
        /\ m.type = "ReadRequest" /\ m.p = p /\ m.d = d  \* such m may be not unique
        /\ css' = [css EXCEPT ![p][d] = 
            [dc \in Datacenter |-> IF dc = d THEN @[dc] ELSE Max(m.vc[dc], @[dc])]]
        /\ LET kvs == {kv \in store[p][d]: 
                        /\ kv.key = m.key 
                        /\ \A dc \in Datacenter \ {d}: kv.vc[dc] <= css'[p][d][dc]}
               lkv == CHOOSE kv \in kvs:  \* choose the latest one (Existence? Uniqueness?)
                        \A akv \in kvs, dc \in Datacenter: akv.vc[dc] <= kv.vc[dc]
           IN SendAndDelete([type |-> "ReadReply", val |-> lkv.val, vc |-> lkv.vc, c |-> m.c], m)
    /\ UNCHANGED <<cVars, clock, pvc, PMC, store, updates, tick>>

UpdateRequest(p, d) == \* handle a "UpdateRequest"
    /\ \E m \in msgs:
        /\ m.type = "UpdateRequest" /\ m.p = p /\ m.d = d  \* such m may be not unique
        /\ m.vc[d] < clock[p][d]  \* waiting condition; ("<=" strengthed to "<")
        \* /\ pvc' = [pvc EXCEPT ![p][d][d] = clock[p][d]]
        /\ css' = [css EXCEPT ![p][d] = 
            [dc \in Datacenter |-> IF dc = d THEN @[dc] ELSE Max(m.vc[dc], @[dc])]]
        /\ LET kv == [key |-> m.key, val |-> m.val, 
                       vc |-> [m.vc EXCEPT ![d] = clock[p][d]]]
           IN /\ store' = [store EXCEPT ![p][d] = @ \cup {kv}] 
              /\ updates' = [updates EXCEPT ![p][d] = @ \o <<kv>>]
              /\ SendAndDelete([type |-> "UpdateReply", ts |-> clock[p][d], c |-> m.c, d |-> d], m)
    /\ UNCHANGED <<cVars, clock, pvc, PMC, tick>>
    
PropagateUpdates(p, d) == \* propagate buffered updates to other datacenters
    /\ IF updates[p][d] # <<>>
       THEN /\ SendSet([type : {"Replicate"}, d : {d}, kvs : {updates[p][d]}, p : {p}, dd : Datacenter \ {d}])
            /\ updates' = [updates EXCEPT ![p][d] = <<>>]
            /\ UNCHANGED <<tick>>
       ELSE /\ tick[p][d]
            /\ SendSet([type : {"Heartbeat"}, d : {d}, ts : {pvc[p][d][d]}, p : {p}, dd : Datacenter \ {d}])
            /\ tick' = [tick EXCEPT ![p][d] = FALSE]
            /\ UNCHANGED <<updates>>
    /\ UNCHANGED <<cVars, cvc, clock, pvc, css, PMC, store>>

Replicate(p, d) == \* handle a "Replicate"
    /\ \E m \in msgs:
        /\ m.type = "Replicate" /\ m.p = p /\ m.dd = d
        /\ store' = [store EXCEPT ![p][d] = @ \cup Range(m.kvs)]
        /\ pvc' = [pvc EXCEPT ![p][d] = Last(m.kvs).vc[m.d]]
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<cVars, cvc, clock, css, PMC, updates, tick>>
    
Heartbeat(p, d) == \* handle a "Heartbeat"    
    /\ \E m \in msgs:
        /\ m.type = "Heartbeat" /\ m.p = p /\ m.dd = d
        /\ pvc' = [pvc EXCEPT ![p][d][m.d] = m.ts]
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<cVars, cvc, clock, css, PMC, store, updates, tick>>        
--------------------------------------------------------------------------
(* Clock management at partition p \in Partition in datacenter d \in Datacenter *)
Tick(p, d) == \* clock[p][d] ticks
    /\ clock' = [clock EXCEPT ![p][d] = @ + 1]  \* TODO: using JavaTime?
    /\ pvc' = [pvc EXCEPT ![p][d][d] = clock'[p][d]]
    /\ tick' = [tick EXCEPT ![p][d] = TRUE]
    /\ UNCHANGED <<cVars, mVars, cvc, css, PMC, store, updates>>
--------------------------------------------------------------------------
Next == 
    \/ \E c \in Client, k \in Key: Read(c, k)
    \/ \E c \in Client, k \in Key, v \in Value: Update(c, k, v)
    \/ \E c \in Client: ReadReply(c) \/ UpdateReply(c)
    \/ \E p \in Partition, d \in Datacenter: 
        \/ ReadRequest(p, d) 
        \/ UpdateRequest(p, d)
        \/ PropagateUpdates(p, d)
        \/ Replicate(p, d)
        \/ Heartbeat(p, d)
        \/ Tick(p, d)

Spec == Init /\ [][Next]_vars
--------------------------------------------------------------------------
=============================================================================