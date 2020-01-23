------------------------------ MODULE Cure ------------------------------- 
(*
  See ICDCS2016: "Cure: Strong Semantics Meets High Availability and Low Latency".
*)
EXTENDS Naturals, Sequences
--------------------------------------------------------------------------
Max(a, b) == IF a < b THEN b ELSE a
Min(S) == CHOOSE a \in S: \A b \in S: a <= b 
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
    store,   \* store[p][d]: the kv store
(* communication: *)
    msgs, \* the set of messages in transit
    incoming \* fifo[p][d]: incomming FIFO channel; for propagating updates and heartbeats

cVars == <<cvc>>
sVars == <<clock, pvc, css, store>>
mVars == <<msgs, incoming>>
vars == <<cvc, clock, pvc, css, store, msgs, incoming>>
--------------------------------------------------------------------------
Clock == Nat
VC == [Datacenter -> Clock]  \* vector clock with an entry per datacenter d \in Datacenter
VCInit == [d \in Datacenter |-> 0]
Merge(vc1, vc2) == [d \in Datacenter |-> Max(vc1[d], vc2[d])]
KVTuple == [key : Key, val : Value \cup {NotVal}, vc : VC]

Message ==
         [type : {"ReadRequest"}, key : Key, vc : VC, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"ReadReply"}, val : Value \cup {NotVal}, vc : VC, c : Client]
    \cup [type : {"UpdateRequest"}, key : Key, val : Value, vc : VC, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"UpdateReply"}, ts : Clock, c : Client, d : Datacenter]
    \cup [type : {"Replicate"}, d : Datacenter, kv : KVTuple]
    \cup [type : {"Heartbeat"}, d : Datacenter, ts : Clock]

TypeOK == 
    /\ cvc \in [Client -> VC]
    /\ clock \in [Partition -> [Datacenter -> Clock]]
    /\ pvc \in [Partition -> [Datacenter -> VC]]
    /\ css \in [Partition -> [Datacenter -> VC]]
    /\ store \in [Partition -> [Datacenter -> SUBSET KVTuple]]
    /\ msgs \subseteq Message
    /\ incoming \in [Partition -> [Datacenter -> Seq(Message)]]
--------------------------------------------------------------------------
Init ==
    /\ cvc = [c \in Client |-> VCInit]   
    /\ clock = [p \in Partition |-> [d \in Datacenter |-> 0]]
    /\ pvc = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ css = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ store = [p \in Partition |-> [d \in Datacenter |-> 
                    [key : {k \in Key : KeySharding[k] = p}, val : {NotVal}, vc : {VCInit}]]]
    /\ msgs = {}
    /\ incoming = [p \in Partition |-> [d \in Datacenter |-> <<>>]]
--------------------------------------------------------------------------
Send(m) == msgs' = msgs \cup {m}
SendAndDelete(sm, dm) == msgs' = (msgs \cup {sm}) \ {dm}

CanIssue(c) == \A m \in msgs: 
    m.type \in {"ReadRequest", "ReadReply", "UpdateRequest", "UpdateReply"} => m.c # c 
--------------------------------------------------------------------------
(* Client operations at client c \in Client. *)

Read(c, k) == \* c \in Client reads from k \in Key
    /\ CanIssue(c)
    /\ Send([type |-> "ReadRequest", key |-> k, vc |-> cvc[c], 
             c |-> c, p |-> KeySharding[k], d |-> ClientAttachment[c]])
    /\ UNCHANGED <<cVars, sVars, incoming>>

ReadReply(c) == \* c \in Client handles the reply to its read request
    /\ \E m \in msgs: 
        /\ m.type = "ReadReply" /\ m.c = c  \* such m is unique due to well-formedness
        /\ cvc' = [cvc EXCEPT ![c] = Merge(m.vc, @)]
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<sVars, incoming>>
    
Update(c, k, v) == \* c \in Client updates k \in Key with v \in Value
    /\ CanIssue(c)
    /\ Send([type |-> "UpdateRequest", key |-> k, val |-> v,
             vc |-> cvc[c], c |-> c, p |-> KeySharding[k], d |-> ClientAttachment[c]])
    /\ UNCHANGED <<cVars, sVars, incoming>>             
    
UpdateReply(c) == \* c \in Client handles the reply to its update request
    /\ \E m \in msgs:
        /\ m.type = "UpdateReply" /\ m.c = c \* such m is unique due to well-formedness
        /\ cvc' = [cvc EXCEPT ![c][m.d] = m.ts]
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<sVars, incoming>>
--------------------------------------------------------------------------
(* Server operations at partition p \in Partition in datacenter d \in Datacenter. *)

ReadRequest(p, d) == \* handle a "ReadRequest"
    /\ \E m \in msgs:
        /\ m.type = "ReadRequest" /\ m.p = p /\ m.d = d
        /\ css' = [css EXCEPT ![p][d] = Merge(m.vc, @)]
        /\ LET kvs == {kv \in store[p][d]: 
                        /\ kv.key = m.key 
                        /\ \A dc \in Datacenter \ {d}: kv.vc[dc] <= css'[p][d][dc]}
               lkv == CHOOSE kv \in kvs:  \* choose the latest one (Existence? Uniqueness?)
                        \A akv \in kvs, dc \in Datacenter: akv.vc[dc] <= kv.vc[dc]
           IN SendAndDelete([type |-> "ReadReply", val |-> lkv.val, vc |-> lkv.vc, c |-> m.c], m)
    /\ UNCHANGED <<cVars, clock, pvc, store, incoming>>

UpdateRequest(p, d) == \* handle a "UpdateRequest"
    /\ \E m \in msgs:
        /\ m.type = "UpdateRequest" /\ m.p = p /\ m.d = d
        /\ m.vc[d] < clock[p][d]  \* waiting condition; ("<=" strengthed to "<")
        /\ css' = [css EXCEPT ![p][d] = Merge(m.vc, @)]
        /\ LET kv == [key |-> m.key, val |-> m.val, 
                       vc |-> [m.vc EXCEPT ![d] = clock[p][d]]]
           IN /\ store' = [store EXCEPT ![p][d] = @ \cup {kv}] 
              /\ SendAndDelete([type |-> "UpdateReply", ts |-> clock[p][d], c |-> m.c, d |-> d], m)
              /\ incoming' = [incoming EXCEPT ![p] = [dc \in Datacenter |-> 
                   IF dc = d THEN @[dc] ELSE Append(@[dc], [type |-> "Replicate", d |-> d, kv |-> kv])]]
    /\ UNCHANGED <<cVars, clock, pvc>>
    
Replicate(p, d) == \* handle a "Replicate"
    /\ incoming[p][d] # <<>>
    /\ LET m == Head(incoming[p][d])
       IN /\ m.type = "Replicate"
          /\ store' = [store EXCEPT ![p][d] = @ \cup {m.kv}]
          /\ pvc' = [pvc EXCEPT ![p][d][m.d] = m.kv.vc[m.d]]
          /\ incoming' = [incoming EXCEPT ![p][d] = Tail(@)]
    /\ UNCHANGED <<cVars, cvc, clock, css, msgs>>
    
Heartbeat(p, d) == \* handle a "Heartbeat"    
    /\ incoming[p][d] # <<>>
    /\ LET m == Head(incoming[p][d])
       IN /\ m.type = "Heartbeat" 
          /\ pvc' = [pvc EXCEPT ![p][d][m.d] = m.ts]
          /\ incoming' = [incoming EXCEPT ![p][d] = Tail(@)]
    /\ UNCHANGED <<cVars, cvc, clock, css, store, msgs>>        
--------------------------------------------------------------------------
(* Clock management at partition p \in Partition in datacenter d \in Datacenter *)
Tick(p, d) == \* clock[p][d] ticks
    /\ clock' = [clock EXCEPT ![p][d] = @ + 1]
    /\ pvc' = [pvc EXCEPT ![p][d][d] = clock'[p][d]]
    /\ incoming' = [incoming EXCEPT ![p] = [dc \in Datacenter |-> 
         IF dc = d THEN @[dc] ELSE Append(@[dc], [type |-> "Heartbeat", d |-> d, ts |-> pvc'[p][d][d]])]]
    /\ UNCHANGED <<cVars, cvc, css, store, msgs>>
    
UpdateCSS(p, d) == \* update css[p][d]
    /\ css' = [css EXCEPT ![p][d] = 
                [dc \in Datacenter |-> Min({pvc[pp][d][dc] : pp \in Partition})]]    
    /\ UNCHANGED <<cVars, mVars, clock, pvc, store>>                                       
--------------------------------------------------------------------------
Next == 
    \/ \E c \in Client, k \in Key: Read(c, k)
    \/ \E c \in Client, k \in Key, v \in Value: Update(c, k, v)
    \/ \E c \in Client: ReadReply(c) \/ UpdateReply(c)
    \/ \E p \in Partition, d \in Datacenter: 
        \/ ReadRequest(p, d) 
        \/ UpdateRequest(p, d)
        \/ Replicate(p, d)
        \/ Heartbeat(p, d)
        \/ Tick(p, d)
        \/ UpdateCSS(p, d)

Spec == Init /\ [][Next]_vars
=============================================================================