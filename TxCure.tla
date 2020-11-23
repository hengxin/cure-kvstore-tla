------------------------------- MODULE TxCure -------------------------------
(*
  Transactional Cure Protocol without Strong Transactions.

  TODO:

  - Values are irrelevant.
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
--------------------------------------------------------------------------
VARIABLES 
(* At the client side: *)
    cvc,    \* cvc[c]: vector clock of client c \in Client
    tid,    \* tid[c]: transaction identifier of the current ongoing transaction of client c \in Client
    coord,  \* coord[c]: coordinator (partition) of the current ongoing transaction of client c \in Client
(* At the server side (each for partition p \in Partition in d \in Datacenter): *)
    rs,         \* rs[p][d][tid][i]: read set of transaction tid, indexed by partition i \in Partition
    ws,         \* ws[p][d][tid][i]: write set of transaction tid, indexed by partition i \in Partition
    seq,        \* seq[p][d]: seq number
    opLog,      \* opLog[p][d]: log
    clock,      \* clock[p][d]: current clock
    knownVC,    \* knownVC[p][d]: vector clock
    stableVC,   \* stableVC[p][d]: stable snapshot
    uniformVC,  \* uniformVC[p][d]: uniform snapshot
    snapshotVC, \* snapshotVC[p][d][t]: snapshot vector clock of transaction t
(* history: *)
    L, \* L[c]: local history at client c \in Client
(* communication: *)
    msgs, \* the set of messages in transit
    incoming \* incoming[p][d]: incoming FIFO channel for propagating updates and heartbeats

cVars == <<cvc, tid, coord>>
sVars == <<opLog, clock, knownVC, stableVC, uniformVC, snapshotVC>>
mVars == <<msgs, incoming>>
hVars == <<L>>
vars == <<cVars, sVars, mVars, hVars>>
--------------------------------------------------------------------------
Tid == [seq : Nat, p : Partition, d : Datacenter] \* transaction identifier

VC == [Datacenter -> Nat]  \* vector clock with an entry per datacenter d \in Datacenter
VCInit == [d \in Datacenter |-> 0]
Merge(vc1, vc2) == [d \in Datacenter |-> Max(vc1[d], vc2[d])] \* TODO: except d?

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
         [type : {"StartRequest"}, vc : VC, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"StartReply"}, tid : Tid, vc : VC, c : Client]
    \cup [type : {"ReadRequest"}, tid : Tid, key : Key, c : Client, p : Partition, d : Datacenter]
    \cup [type : {"ReadReply"}, val : Value \cup {NotVal}, c : Client] \* val is irrelevant
    \cup [type : {"UpdateRequest"}, tid : Tid, key : Key, val : Value, c : Client, p : Partition, d : Datacenter] \* val is irrelevant
    \cup [type : {"UpdateReply"}, c : Client]
    \cup [type : {"CommitRequest"}, tid : Tid, c : Client, p : Partition, d : Datacenter] \* val is irrelevant
    \cup [type : {"CommitReply"}, vc : VC, c : Client]
    \cup [type : {"Replicate"}, d : Datacenter, kv : KVTuple]
    \cup [type : {"Heartbeat"}, d : Datacenter, ts : Nat]

Send(m) == msgs' = msgs \cup {m}
SendAndDelete(sm, dm) == msgs' = (msgs \cup {sm}) \ {dm}

TypeOK == 
    /\ cvc \in [Client -> VC]
    /\ clock \in [Partition -> [Datacenter -> Nat]]
    /\ knownVC \in [Partition -> [Datacenter -> VC]]
    /\ stableVC \in [Partition -> [Datacenter -> VC]]
    /\ uniformVC \in [Partition -> [Datacenter -> VC]]
    /\ snapshotVC \in [Partition -> [Datacenter -> [Tid -> VC]]]
    /\ opLog \in [Partition -> [Datacenter -> SUBSET KVTuple]]
    /\ msgs \subseteq Message
    /\ incoming \in [Partition -> [Datacenter -> Seq(Message)]]
    /\ L \in [Client -> Seq(OpTuple)]
--------------------------------------------------------------------------
Init ==
    /\ cvc = [c \in Client |-> VCInit]
    /\ clock = [p \in Partition |-> [d \in Datacenter |-> 0]]
    /\ knownVC = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ stableVC = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ uniformVC = [p \in Partition |-> [d \in Datacenter |-> VCInit]]
    /\ snapshotVC = [p \in Partition |-> [d \in Datacenter |-> [t \in Tid |-> VCInit]]]
    /\ opLog = [p \in Partition |-> [d \in Datacenter |-> 
                    [key : {k \in Key : KeySharding[k] = p}, val : {NotVal}, vc : {VCInit}]]]
    /\ msgs = {}
    /\ incoming = [p \in Partition |-> [d \in Datacenter |-> <<>>]]
    /\ L = [c \in Client |-> <<>>]
--------------------------------------------------------------------------
(* Client operations at client c \in Client. *)

CanIssue(c) == \A m \in msgs: \* to ensure well-formedness of clients
    m.type \in {"StartRequest", "StartReply",
        "ReadRequest", "ReadReply", 
        "UpdateRequest", "UpdateReply"
        "CommitRequest", "CommitReply"} => m.c # c 

Start(c) == \* c \in Client starts a transaction
    /\ CanIssue(c)
    /\ \E p \in Partition:
        /\ coord' = [coord EXCEPT ![c] = p]
        /\ Send([type |-> "StartRequest", vc |-> cvc[c],
                    c |-> c, p |-> p, d |-> ClientAttachment[c]])
    /\ UNCHANGED <<cvc, tid, sVars, incoming, hVars>>

StartReply(c) == \* c \in Client handles the reply to its start request
    /\ \E m \in msgs:
        /\ m.type = "StartReply" /\ m.c = c \* such m is unique due to well-formedness
        /\ cvc' = [cvc EXCEPT ![c] = m.snapshotVC]
        /\ tid' = [tid EXCEPT ![c] = m.tid]
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<coord, sVars, incoming, hVars>>

Read(c, k) == \* c \in Client reads from k \in Key
    /\ CanIssue(c)
    /\ Send([type |-> "ReadRequest", tid |-> tid[c], key |-> k, 
                c |-> c, p |-> coord[c], d |-> ClientAttachment[c]])
    /\ UNCHANGED <<cVars, sVars, incoming, hVars>>

ReadReply(c) == \* c \in Client handles the reply to its read request
    /\ \E m \in msgs: 
        /\ m.type = "ReadReply" /\ m.c = c  \* such m is unique due to well-formedness
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<cVars, sVars, incoming, hVars>>
    
Update(c, k, v) == \* c \in Client updates k \in Key with v \in Value
    /\ CanIssue(c)
    /\ Send([type |-> "UpdateRequest", tid |-> tid[c], key |-> k, val |-> v,
                c |-> c, p |-> coord[c], d |-> ClientAttachment[c]])
    /\ UNCHANGED <<cVars, sVars, incoming, hVars>>
    
UpdateReply(c) == \* c \in Client handles the reply to its update request
    /\ \E m \in msgs:
        /\ m.type = "UpdateReply" /\ m.c = c \* such m is unique due to well-formedness
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<cVars, sVars, incoming, hVars>>

Commit(c) == \* c \in Client commits the ongoing transaction tid[c]
    /\ CanIssue(c)
    /\ Send([type |-> "CommitRequest", tid |-> tid[c],
                c |-> c, p |-> coord[c], d |-> ClientAttachment[c]])
    /\ UNCHANGED <<cVars, sVars, incoming, hVars>>
    
CommitReply(c) == \* c \in Client handles the reply to its commit request
    /\ \E m \in msgs:
        /\ m.type = "CommitReply" /\ m.c = c \* such m is unique due to well-formedness
        /\ cvc' = [cvc EXCEPT !c = [m.vc]]
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<tid, coord, sVars, incoming, hVars>>
--------------------------------------------------------------------------
(* Server operations at partition p \in Partition in datacenter d \in Datacenter. *)

StartRequest(p, d) == \* handle a "StartRequest" 
    /\ \E m \in msgs:
        /\ m.type = "StartRequest" /\ m.p = p /\ m.d = d
        /\ uniformVC' = [uniformVC EXCEPT ![p][d] = Merge(m.vc, @)]
        /\ seq' = [seq EXCEPT ![p][d] = @ + 1]
        /\ LET t == [seq |-> seq, p |-> p, d |-> d]
            IN /\ snapshotVC' = [snapshotVC EXCEPT 
                    ![p][d][t] = [dc \in Datacenter |-> 
                                    IF dc = d 
                                    THEN Max(m.vc[d], uniformVC[p][d][d]) 
                                    ELSE uniformVC'[p][d][d]]]
               /\ SendAndDelete([type |-> "StartReply", tid |-> t, 
                                   vc |-> snapshotVC'[p][d][t]], c |-> m.c], m)
    /\ UNCHANGED <<cVars, clock, knownVC, stableVC, opLog, incoming>>

ReadRequest(p, d) == \* handle a "ReadRequest"
    /\ \E m \in msgs:
        /\ m.type = "ReadRequest" /\ m.p = p /\ m.d = d
        /\ SendAndDelete([type |-> "ReadReply", val |-> lkv.val, vc |-> lkv.vc, c |-> m.c], m)
        \* /\ L' = [L EXCEPT ![m.c] = Append(@, [type |-> "R", kv |-> lkv, c |-> m.c, cnt |-> Len(@) + 1])]
    /\ UNCHANGED <<cVars, clock, knownVC, opLog, incoming>>

UpdateRequest(p, d) == \* handle a "UpdateRequest"
    /\ \E m \in msgs:
        /\ m.type = "UpdateRequest" /\ m.p = p /\ m.d = d
        /\ ws' = [ws EXCEPT ![p][d][m.tid][KeySharding[m.key]][m.key] = m.val]
        /\ SendAndDelete([type |-> "UpdateReply", c |-> m.c], m)
        \* /\ L' = [L EXCEPT ![m.c] = Append(@, [type |-> "W", kv |-> kv, c |-> m.c, cnt |-> Len(@) + 1])]
    /\ UNCHANGED <<cVars, clock, knownVC>>
    
Replicate(p, d) == \* handle a "Replicate"
    /\ incoming[p][d] # <<>>
    /\ LET m == Head(incoming[p][d])
       IN /\ m.type = "Replicate"
          /\ opLog' = [opLog EXCEPT ![p][d] = @ \cup {m.kv}]
          /\ knownVC' = [knownVC EXCEPT ![p][d][m.d] = m.kv.vc[m.d]]
          /\ incoming' = [incoming EXCEPT ![p][d] = Tail(@)]
    /\ UNCHANGED <<cVars, cvc, clock, stableVC, L, msgs>>
    
Heartbeat(p, d) == \* handle a "Heartbeat"    
    /\ incoming[p][d] # <<>>
    /\ LET m == Head(incoming[p][d])
       IN /\ m.type = "Heartbeat" 
          /\ knownVC' = [knownVC EXCEPT ![p][d][m.d] = m.ts]
          /\ incoming' = [incoming EXCEPT ![p][d] = Tail(@)]
    /\ UNCHANGED <<cVars, cvc, clock, stableVC, opLog, L, msgs>>        
--------------------------------------------------------------------------
(* Clock management at partition p \in Partition in datacenter d \in Datacenter *)
Tick(p, d) == \* clock[p][d] ticks
    /\ clock' = [clock EXCEPT ![p][d] = @ + 1]
    /\ knownVC' = [knownVC EXCEPT ![p][d][d] = clock'[p][d]]
    /\ incoming' = [incoming EXCEPT ![p] = [dc \in Datacenter |-> 
         IF dc = d THEN @[dc] ELSE Append(@[dc], [type |-> "Heartbeat", d |-> d, ts |-> knownVC'[p][d][d]])]]
    /\ UNCHANGED <<cVars, cvc, stableVC, opLog, L, msgs>>
    
UpdateCSS(p, d) == \* update stableVC[p][d]
    /\ stableVC' = [stableVC EXCEPT ![p][d] = 
                [dc \in Datacenter |-> SetMin({knownVC[pp][d][dc] : pp \in Partition})]]    
    /\ UNCHANGED <<cVars, mVars, clock, knownVC, opLog, L>>                                       
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
\* Modification History
\* Last modified Mon Nov 23 16:11:35 CST 2020 by hengxin
\* Created Fri Nov 20 18:51:11 CST 2020 by hengxin