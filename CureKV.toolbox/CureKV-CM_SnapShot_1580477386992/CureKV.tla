------------------------------- MODULE CureKV -------------------------------
(*
See ICDCS2016: "Cure: Strong Semantics Meets High Availability and Low Latency".
*)
EXTENDS Naturals, FiniteSets, TLC, SequenceUtils, RelationUtils, MathUtils
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

KeysOnPartition == [p \in Partition |-> {k \in Key: KeySharding[k] = p}]
--------------------------------------------------------------------------
VARIABLES 
(* At the client side: *)
    cvc,  \* cvc[c]: the vector clock of client c \in Client
(* At the server side (each for partition p \in Partition in d \in Datacenter): *)
    clock,   \* clock[p][d]: the current clock
    pvc,     \* pvc[p][d]: the vector clock
    css,     \* css[p][d]: the stable snapshot
    store,   \* store[p][d]: the kv store (represented by a map)
    remote,  \* remote[p][d]: the set of remote updates that have not been applied yet
(* history: *)
    L, \* L[c]: local history at client c \in Client
(* communication: *)
    msgs, \* the set of messages in transit
    incoming \* incoming[p][d]: incoming FIFO channel for propagating updates and heartbeats

cVars == <<cvc>>
sVars == <<clock, pvc, css, store, remote, L>>
mVars == <<msgs, incoming>>
vars == <<cvc, clock, pvc, css, store, remote, L, msgs, incoming>>
--------------------------------------------------------------------------
VC == [Datacenter -> Nat]  \* vector clock with an entry per datacenter d \in Datacenter
VCInit == [d \in Datacenter |-> 0]
Merge(vc1, vc2) == [d \in Datacenter |-> Max(vc1[d], vc2[d])]

DC == Cardinality(Datacenter)
DCIndex == CHOOSE f \in [1 .. DC -> Datacenter] : Injective(f)
LTE(vc1, vc2) == \* less-than-or-equal-to comparator for vector clocks 
    LET RECURSIVE LTEHelper(_, _, _) 
        LTEHelper(vc1h, vc2h, index) == 
            IF index > DC THEN TRUE \* EQ
            ELSE LET d == DCIndex[index]
                 IN  CASE vc1h[d] < vc2h[d] -> TRUE  \* LT
                       [] vc1h[d] > vc2h[d] -> FALSE \* GT
                       [] OTHER -> LTEHelper(vc1h, vc2h, index + 1)
    IN  LTEHelper(vc1, vc2, 1)

KVTuple == [key : Key, val : Value \cup {NotVal}, vc : VC]
OpTuple == [type : {"R", "W"}, kv : KVTuple, c : Client, cnt : Nat]
    
Message ==
         [type : {"ReadRequest"}, key : Key, vc : VC, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"ReadReply"}, val : Value \cup {NotVal}, vc : VC, c : Client]
    \cup [type : {"UpdateRequest"}, key : Key, val : Value, vc : VC, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"UpdateReply"}, ts : Nat, c : Client, d : Datacenter]
    \cup [type : {"Replicate"}, d : Datacenter, kv : KVTuple]
    \cup [type : {"Heartbeat"}, d : Datacenter, ts : Nat]

Send(m) == msgs' = msgs \cup {m}
SendAndDelete(sm, dm) == msgs' = (msgs \cup {sm}) \ {dm}

TypeOK == 
    /\ cvc \in [Client -> VC]
    /\ clock \in [Partition -> [Datacenter -> Nat]]
    /\ pvc \in [Partition -> [Datacenter -> VC]]
    /\ css \in [Partition -> [Datacenter -> VC]]
    /\ store \in [Partition -> [Datacenter -> [Key -> KVTuple]]]
    /\ remote \in [Partition -> [Datacenter -> SUBSET KVTuple]]
    /\ msgs \subseteq Message
    /\ incoming \in [Partition -> [Datacenter -> Seq(Message)]]
    /\ L \in [Client -> Seq(OpTuple)]
--------------------------------------------------------------------------
Init ==
    /\ cvc = [c \in Client |-> VCInit]   
    /\ clock = [p \in Partition |-> [d \in Datacenter |-> 0]]
    /\ pvc = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ css = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ store = [p \in Partition |-> [d \in Datacenter |-> 
                    [k \in KeysOnPartition[p] |-> [key |-> k, val |-> NotVal, vc |-> VCInit]]]]
    /\ remote = [p \in Partition |-> [d \in Datacenter |-> {}]]
    /\ msgs = {}
    /\ incoming = [p \in Partition |-> [d \in Datacenter |-> <<>>]]
    /\ L = [c \in Client |-> <<>>]
--------------------------------------------------------------------------
(* Client operations at client c \in Client. *)

CanIssue(c) == \A m \in msgs: \* to ensure well-formedness of clients
    m.type \in {"ReadRequest", "ReadReply", "UpdateRequest", "UpdateReply"} => m.c # c 

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

Apply(p, d) == \* apply remote updates which become stable due to up-to-date css[p][d]
    LET keys == {kv.key: kv \in remote[p][d]}
        kvs == [k \in keys |-> {kv \in remote[p][d]: 
                                    /\ kv.key = k 
                                    /\ \A dc \in Datacenter \ {d}: kv.vc[dc] <= css'[p][d][dc]}]
    IN  /\ store' = [store EXCEPT ![p][d] = [k \in KeysOnPartition[p] |->
                               IF k \in keys /\ kvs[k] # {}
                               THEN CHOOSE kv \in kvs[k]: \A akv \in kvs[k]: LTE(akv.vc, kv.vc)
                               ELSE @[k]]]
        /\ remote' = [remote EXCEPT ![p][d] = @ \ (UNION (Range(kvs)))]

ReadRequest(p, d) == \* handle a "ReadRequest"
    /\ \E m \in msgs:
        /\ m.type = "ReadRequest" /\ m.p = p /\ m.d = d
        /\ css' = [css EXCEPT ![p][d] = Merge(m.vc, @)]
        /\ LET kv == store[p][d][m.key]
           IN /\ SendAndDelete([type |-> "ReadReply", val |-> kv.val, vc |-> kv.vc, c |-> m.c], m)
              /\ Apply(p, d)
              /\ L' = [L EXCEPT ![m.c] = Append(@, [type |-> "R", kv |-> kv, c |-> m.c, cnt |-> Len(@) + 1])]
    /\ UNCHANGED <<cVars, clock, pvc, incoming>>

UpdateRequest(p, d) == \* handle a "UpdateRequest"
    /\ \E m \in msgs:
        /\ m.type = "UpdateRequest" /\ m.p = p /\ m.d = d
        /\ m.vc[d] < clock[p][d]  \* waiting condition; ("<=" strengthed to "<")
        /\ css' = [css EXCEPT ![p][d] = Merge(m.vc, @)]
        /\ LET kv == [key |-> m.key, val |-> m.val, 
                       vc |-> [m.vc EXCEPT ![d] = clock[p][d]]]
           IN /\ store' = [store EXCEPT ![p][d][m.key] = kv] \* TODO: Apply???
              /\ SendAndDelete([type |-> "UpdateReply", ts |-> clock[p][d], c |-> m.c, d |-> d], m)
              /\ incoming' = [incoming EXCEPT ![p] = [dc \in Datacenter |-> 
                   IF dc = d THEN @[dc] ELSE Append(@[dc], [type |-> "Replicate", d |-> d, kv |-> kv])]]
              /\ L' = [L EXCEPT ![m.c] = Append(@, [type |-> "W", kv |-> kv, c |-> m.c, cnt |-> Len(@) + 1])]
    /\ UNCHANGED <<cVars, clock, pvc, remote>>
    
Replicate(p, d) == \* handle a "Replicate"
    /\ incoming[p][d] # <<>>
    /\ LET m == Head(incoming[p][d])
       IN /\ m.type = "Replicate"
          /\ remote' = [remote EXCEPT ![p][d] = @ \cup {m.kv}]
          /\ pvc' = [pvc EXCEPT ![p][d][m.d] = m.kv.vc[m.d]]
          /\ incoming' = [incoming EXCEPT ![p][d] = Tail(@)]
    /\ UNCHANGED <<cVars, cvc, clock, css, store, L, msgs>>
    
Heartbeat(p, d) == \* handle a "Heartbeat"    
    /\ incoming[p][d] # <<>>
    /\ LET m == Head(incoming[p][d])
       IN /\ m.type = "Heartbeat" 
          /\ pvc' = [pvc EXCEPT ![p][d][m.d] = m.ts]
          /\ incoming' = [incoming EXCEPT ![p][d] = Tail(@)]
    /\ UNCHANGED <<cVars, cvc, clock, css, store, remote, L, msgs>>        
--------------------------------------------------------------------------
(* Clock management at partition p \in Partition in datacenter d \in Datacenter *)
Tick(p, d) == \* clock[p][d] ticks
    /\ clock' = [clock EXCEPT ![p][d] = @ + 1]
    /\ pvc' = [pvc EXCEPT ![p][d][d] = clock'[p][d]]
    /\ incoming' = [incoming EXCEPT ![p] = [dc \in Datacenter |-> 
         IF dc = d THEN @[dc] ELSE Append(@[dc], [type |-> "Heartbeat", d |-> d, ts |-> pvc'[p][d][d]])]]
    /\ UNCHANGED <<cVars, cvc, css, store, remote, L, msgs>>
    
UpdateCSS(p, d) == \* update css[p][d]
    /\ css' = [css EXCEPT ![p][d] = 
                [dc \in Datacenter |-> SetMin({pvc[pp][d][dc] : pp \in Partition})]]    
    /\ Apply(p, d)
    /\ UNCHANGED <<cVars, mVars, clock, pvc, L>>                                       
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
--------------------------------------------------------------------------
Valid(s) == \* Is s a valid serialization?
    LET RECURSIVE ValidHelper(_, _)
        ValidHelper(seq, kvs) ==
            IF seq = <<>> THEN TRUE
            ELSE LET op == Head(seq)
                 IN  IF op.type = "W"                                 \* overwritten
                     THEN ValidHelper(Tail(seq), op.kv.key :> op.kv.vc @@ kvs)
                     ELSE /\ op.kv.vc = kvs[op.kv.key]
                          /\ ValidHelper(Tail(seq), kvs)
    IN  ValidHelper(s, [k \in Key |-> VCInit])  \* with initial values

CM == \* causal memory consistency model; see Ahamad@DC'1995
    LET ops == UNION {Range(L[c]): c \in Client}
        rops == {op \in ops: op.type = "R"}
        wops == {op \in ops: op.type = "W"}
        so == UNION {SeqToRel(L[c]): c \in Client} \* session order
        rf == {<<w, r>> \in wops \X rops: w.kv.key = r.kv.key /\ w.kv.vc = r.kv.vc}
        co == TC(so \cup rf) \* causality order
    IN  \A c \in Client: 
            \E sc \in PermutationsOf(L[c] \o SetToSeq(wops)):
                /\ Valid(sc)
                /\ Respect(sc, co)
                
THEOREM Spec => []CM                
=============================================================================
\* Modification History
\* Last modified Thu Jan 30 23:55:36 CST 2020 by hengxin
\* Created Tue Jan 28 21:28:25 CST 2020 by hengxin