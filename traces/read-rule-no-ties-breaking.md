@!@!@STARTMSG 2262:0 @!@!@
TLC2 Version 2.14 of 10 July 2019
@!@!@ENDMSG 2262 @!@!@
@!@!@STARTMSG 2187:0 @!@!@
Running breadth-first search Model-Checking with fp 21 and seed 838354587627879458 with 9 workers on 12 cores with 15241MB heap and 34279MB offheap memory [pid: 28728] (Linux 4.15.0-66-generic amd64, AdoptOpenJDK 11.0.3 x86_64, OffHeapDiskFPSet, DiskStateQueue).
@!@!@ENDMSG 2187 @!@!@
@!@!@STARTMSG 2220:0 @!@!@
Starting SANY...
@!@!@ENDMSG 2220 @!@!@
Parsing file /home/hengxin/hfwei/github-projects-public/cure-kvstore-tla/Cure.toolbox/TypeOK/MC.tla
Parsing file /home/hengxin/hfwei/github-projects-public/cure-kvstore-tla/Cure.toolbox/TypeOK/Cure.tla
Parsing file /home/hengxin/Software/toolbox/plugins/org.lamport.tlatools_1.0.0.201907102009/tla2sany/StandardModules/TLC.tla
Parsing file /home/hengxin/Software/toolbox/plugins/org.lamport.tlatools_1.0.0.201907102009/tla2sany/StandardModules/Naturals.tla
Parsing file /home/hengxin/Software/toolbox/plugins/org.lamport.tlatools_1.0.0.201907102009/tla2sany/StandardModules/Sequences.tla
Parsing file /usr/local/lib/tlaps/FiniteSets.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module Cure
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module MC
@!@!@STARTMSG 2219:0 @!@!@
SANY finished.
@!@!@ENDMSG 2219 @!@!@
@!@!@STARTMSG 2185:0 @!@!@
Starting... (2020-01-23 15:11:21)
@!@!@ENDMSG 2185 @!@!@
<< "$!@$!@$!@$!@$!",
   ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) @@
     p2 :> (d1 :> (d1 :> 0 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) ) >>
@!@!@STARTMSG 2189:0 @!@!@
Computing initial states...
@!@!@ENDMSG 2189 @!@!@
@!@!@STARTMSG 2190:0 @!@!@
Finished computing initial states: 1 distinct state generated at 2020-01-23 15:11:25.
@!@!@ENDMSG 2190 @!@!@
@!@!@STARTMSG 2200:0 @!@!@
Progress(11) at 2020-01-23 15:11:28: 155,164 states generated (155,164 s/min), 32,854 distinct states found (32,854 ds/min), 20,939 states left on queue.
@!@!@ENDMSG 2200 @!@!@
@!@!@STARTMSG 2200:0 @!@!@
Progress(15) at 2020-01-23 15:12:28: 8,528,846 states generated (8,373,682 s/min), 1,494,036 distinct states found (1,461,182 ds/min), 865,557 states left on queue.
@!@!@ENDMSG 2200 @!@!@
@!@!@STARTMSG 1000:1 @!@!@
TLC threw an unexpected exception.
This was probably caused by an error in the spec or model.
See the User Output or TLC Console for clues to what happened.
The exception was a java.lang.RuntimeException
: Attempted to compute the value of an expression of form
CHOOSE x \in S: P, but no element of S satisfied P.
line 118, col 23 to line 119, col 82 of module Cure
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 2121:1 @!@!@
The behavior up to this point is:
@!@!@ENDMSG 2121 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
1: <Initial predicate>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 0 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 0 @@ d2 :> 0) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = {}
/\ incoming = (p1 :> (d1 :> <<>> @@ d2 :> <<>>) @@ p2 :> (d1 :> <<>> @@ d2 :> <<>>))
/\ pvc = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
2: <Update line 97, col 5 to line 100, col 43 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 0 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 0 @@ d2 :> 0) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [ d |-> d1,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c1,
    p |-> p1 ] }
/\ incoming = (p1 :> (d1 :> <<>> @@ d2 :> <<>>) @@ p2 :> (d1 :> <<>> @@ d2 :> <<>>))
/\ pvc = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
3: <Update line 97, col 5 to line 100, col 43 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 0 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 0 @@ d2 :> 0) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [ d |-> d1,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c1,
    p |-> p1 ],
  [ d |-> d2,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c2,
    p |-> p1 ] }
/\ incoming = (p1 :> (d1 :> <<>> @@ d2 :> <<>>) @@ p2 :> (d1 :> <<>> @@ d2 :> <<>>))
/\ pvc = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
4: <Tick line 155, col 5 to line 159, col 49 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 0 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 0) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [ d |-> d1,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c1,
    p |-> p1 ],
  [ d |-> d2,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c2,
    p |-> p1 ] }
/\ incoming = ( p1 :> (d1 :> <<>> @@ d2 :> <<[d |-> d1, type |-> "Heartbeat", ts |-> 1]>>) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
5: <UpdateRequest line 124, col 5 to line 134, col 38 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 0 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 0) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [d |-> d1, type |-> "UpdateReply", c |-> c1, ts |-> 1],
  [ d |-> d2,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c2,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :> <<>> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
6: <UpdateReply line 103, col 5 to line 107, col 36 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 1 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 0) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [ d |-> d2,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c2,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :> <<>> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
7: <Read line 84, col 5 to line 87, col 43 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 1 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 0) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [ d |-> d1,
    key |-> k1,
    vc |-> (d1 :> 1 @@ d2 :> 0),
    type |-> "ReadRequest",
    c |-> c1,
    p |-> p1 ],
  [ d |-> d2,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c2,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :> <<>> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
8: <Tick line 155, col 5 to line 159, col 49 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 1 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 1) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [ d |-> d1,
    key |-> k1,
    vc |-> (d1 :> 1 @@ d2 :> 0),
    type |-> "ReadRequest",
    c |-> c1,
    p |-> p1 ],
  [ d |-> d2,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c2,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :> <<[d |-> d2, type |-> "Heartbeat", ts |-> 1]>> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
9: <Heartbeat line 146, col 5 to line 151, col 56 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 1 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :> {[key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 1) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [ d |-> d1,
    key |-> k1,
    vc |-> (d1 :> 1 @@ d2 :> 0),
    type |-> "ReadRequest",
    c |-> c1,
    p |-> p1 ],
  [ d |-> d2,
    key |-> k1,
    val |-> v,
    vc |-> (d1 :> 0 @@ d2 :> 0),
    type |-> "UpdateRequest",
    c |-> c2,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :> <<>> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
10: <UpdateRequest line 124, col 5 to line 134, col 38 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 1 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 0 @@ d2 :> 1)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 1) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [d |-> d2, type |-> "UpdateReply", c |-> c2, ts |-> 1],
  [ d |-> d1,
    key |-> k1,
    vc |-> (d1 :> 1 @@ d2 :> 0),
    type |-> "ReadRequest",
    c |-> c1,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :>
            << [ d |-> d2,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 0 @@ d2 :> 1) ] ] >> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
11: <Replicate line 137, col 5 to line 143, col 49 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 1 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 0 @@ d2 :> 1)],
              [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 0 @@ d2 :> 1)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 1) @@ p2 :> (d1 :> 0 @@ d2 :> 0))
/\ msgs = { [d |-> d2, type |-> "UpdateReply", c |-> c2, ts |-> 1],
  [ d |-> d1,
    key |-> k1,
    vc |-> (d1 :> 1 @@ d2 :> 0),
    type |-> "ReadRequest",
    c |-> c1,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :> <<>> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
12: <Tick line 155, col 5 to line 159, col 49 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 1 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 0 @@ d2 :> 1)],
              [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 0 @@ d2 :> 1)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 1) @@ p2 :> (d1 :> 0 @@ d2 :> 1))
/\ msgs = { [d |-> d2, type |-> "UpdateReply", c |-> c2, ts |-> 1],
  [ d |-> d1,
    key |-> k1,
    vc |-> (d1 :> 1 @@ d2 :> 0),
    type |-> "ReadRequest",
    c |-> c1,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :> <<>> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<[d |-> d2, type |-> "Heartbeat", ts |-> 1]>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
13: <Heartbeat line 146, col 5 to line 151, col 56 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 1 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 0 @@ d2 :> 1)],
              [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 0 @@ d2 :> 1)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 1) @@ p2 :> (d1 :> 0 @@ d2 :> 1))
/\ msgs = { [d |-> d2, type |-> "UpdateReply", c |-> c2, ts |-> 1],
  [ d |-> d1,
    key |-> k1,
    vc |-> (d1 :> 1 @@ d2 :> 0),
    type |-> "ReadRequest",
    c |-> c1,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :> <<>> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
14: <UpdateCSS line 162, col 5 to line 164, col 52 of module Cure>
/\ css = ( p1 :> (d1 :> (d1 :> 0 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 0) @@ d2 :> (d1 :> 0 @@ d2 :> 0)) )
/\ cvc = (c1 :> (d1 :> 1 @@ d2 :> 0) @@ c2 :> (d1 :> 0 @@ d2 :> 0))
/\ store = ( p1 :>
      ( d1 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 0 @@ d2 :> 1)],
              [key |-> k1, val |-> v, vc |-> (d1 :> 1 @@ d2 :> 0)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } @@
        d2 :>
            { [key |-> k1, val |-> v, vc |-> (d1 :> 0 @@ d2 :> 1)],
              [key |-> k1, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)] } ) @@
  p2 :>
      ( d1 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} @@
        d2 :> {[key |-> k2, val |-> NotVal, vc |-> (d1 :> 0 @@ d2 :> 0)]} ) )
/\ clock = (p1 :> (d1 :> 1 @@ d2 :> 1) @@ p2 :> (d1 :> 0 @@ d2 :> 1))
/\ msgs = { [d |-> d2, type |-> "UpdateReply", c |-> c2, ts |-> 1],
  [ d |-> d1,
    key |-> k1,
    vc |-> (d1 :> 1 @@ d2 :> 0),
    type |-> "ReadRequest",
    c |-> c1,
    p |-> p1 ] }
/\ incoming = ( p1 :>
      ( d1 :> <<>> @@
        d2 :>
            << [d |-> d1, type |-> "Heartbeat", ts |-> 1],
               [ d |-> d1,
                 type |-> "Replicate",
                 kv |->
                     [ key |-> k1,
                       val |-> v,
                       vc |-> (d1 :> 1 @@ d2 :> 0) ] ] >> ) @@
  p2 :> (d1 :> <<>> @@ d2 :> <<>>) )
/\ pvc = ( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) )

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2103:1 @!@!@
The error occurred when TLC was evaluating the nested
expressions at the following positions:
0. Line 112, column 5 to line 121, column 55 in Cure
1. Line 112, column 8 to line 120, column 97 in Cure
2. Line 113, column 9 to line 120, column 97 in Cure
3. Line 113, column 12 to line 113, column 55 in Cure
4. Line 113, column 12 to line 113, column 44 in Cure
5. Line 113, column 12 to line 113, column 33 in Cure
6. Line 113, column 38 to line 113, column 44 in Cure
7. Line 113, column 49 to line 113, column 55 in Cure
8. Line 114, column 12 to line 114, column 55 in Cure
9. Line 115, column 12 to line 120, column 97 in Cure
10. Line 120, column 15 to line 120, column 97 in Cure
11. Line 76, column 26 to line 76, column 56 in Cure
12. Line 76, column 34 to line 76, column 56 in Cure
13. Line 76, column 35 to line 76, column 48 in Cure
14. Line 76, column 45 to line 76, column 48 in Cure
15. Line 76, column 46 to line 76, column 47 in Cure
16. Line 120, column 29 to line 120, column 93 in Cure
17. Line 120, column 60 to line 120, column 66 in Cure
18. Line 120, column 60 to line 120, column 62 in Cure
19. Line 118, column 23 to line 119, column 82 in Cure


@!@!@ENDMSG 2103 @!@!@
@!@!@STARTMSG 2201:0 @!@!@
The coverage statistics at 2020-01-23 15:12:48
@!@!@ENDMSG 2201 @!@!@
@!@!@STARTMSG 2773:0 @!@!@
<Init line 65, col 1 to line 65, col 4 of module Cure>: 2:2
@!@!@ENDMSG 2773 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 66, col 5 to line 73, col 67 of module Cure: 2
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<Read line 83, col 1 to line 83, col 10 of module Cure>: 4256:674557
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 78, col 16 to line 79, col 86 of module Cure: 156872
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 79, col 5 to line 79, col 75 of module Cure: 4322379
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 79, col 80 to line 79, col 86 of module Cure: 4840064
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 79, col 80 to line 79, col 82 of module Cure: 4322379
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 79, col 86 to line 79, col 86 of module Cure: 4322379
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 78, col 25 to line 78, col 28 of module Cure: 3383581
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 84, col 17 to line 84, col 17 of module Cure: 3226709
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 85, col 8 to line 86, col 71 of module Cure: 674557
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 87, col 8 to line 87, col 43 of module Cure: 674557
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<ReadReply line 89, col 1 to line 89, col 12 of module Cure>: 664:132668
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 91, col 12 to line 91, col 31 of module Cure: 2841688
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 91, col 12 to line 91, col 17 of module Cure: 2709020
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 91, col 36 to line 91, col 42 of module Cure: 398004
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 91, col 36 to line 91, col 38 of module Cure: 265336
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 91, col 42 to line 91, col 42 of module Cure: 265336
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 92, col 12 to line 92, col 52 of module Cure: 132668
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 93, col 12 to line 93, col 29 of module Cure: 132668
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 90, col 17 to line 90, col 20 of module Cure: 1691785
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 94, col 8 to line 94, col 36 of module Cure: 132668
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<Update line 96, col 1 to line 96, col 15 of module Cure>: 4674:674552
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 78, col 16 to line 79, col 86 of module Cure: 156869
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 79, col 5 to line 79, col 75 of module Cure: 4322376
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 79, col 80 to line 79, col 86 of module Cure: 4840059
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 79, col 80 to line 79, col 82 of module Cure: 4322376
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 79, col 86 to line 79, col 86 of module Cure: 4322376
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 78, col 25 to line 78, col 28 of module Cure: 3383575
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 97, col 17 to line 97, col 17 of module Cure: 3226706
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 98, col 8 to line 99, col 86 of module Cure: 674552
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 100, col 8 to line 100, col 43 of module Cure: 674552
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<UpdateReply line 102, col 1 to line 102, col 14 of module Cure>: 7373:256523
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 104, col 12 to line 104, col 33 of module Cure: 2965543
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 104, col 12 to line 104, col 17 of module Cure: 2709020
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 104, col 38 to line 104, col 44 of module Cure: 769568
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 104, col 38 to line 104, col 40 of module Cure: 513045
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 104, col 44 to line 104, col 44 of module Cure: 513045
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 105, col 12 to line 105, col 47 of module Cure: 256523
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 106, col 12 to line 106, col 29 of module Cure: 256523
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 103, col 17 to line 103, col 20 of module Cure: 1691785
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 107, col 8 to line 107, col 36 of module Cure: 256523
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<ReadRequest line 111, col 1 to line 111, col 17 of module Cure>: 29462:539929
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 113, col 12 to line 113, col 33 of module Cure: 5957915
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 113, col 12 to line 113, col 17 of module Cure: 5417986
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 113, col 38 to line 113, col 44 of module Cure: 2699634
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 113, col 38 to line 113, col 40 of module Cure: 2159705
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 113, col 44 to line 113, col 44 of module Cure: 2159705
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 113, col 49 to line 113, col 55 of module Cure: 1619785
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 113, col 49 to line 113, col 51 of module Cure: 1079856
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 113, col 55 to line 113, col 55 of module Cure: 1079856
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 114, col 12 to line 114, col 55 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 114, col 19 to line 114, col 55 of module Cure: 539931
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 76, col 26 to line 76, col 56 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 76, col 34 to line 76, col 56 of module Cure: 539931
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 76, col 35 to line 76, col 48 of module Cure: 539931
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 76, col 53 to line 76, col 56 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 120, col 29 to line 120, col 93 of module Cure: 539931
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 120, col 60 to line 120, col 66 of module Cure: 539931
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 120, col 60 to line 120, col 62 of module Cure: 539931
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||line 118, col 23 to line 119, col 82 of module Cure: 539931
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||line 119, col 25 to line 119, col 82 of module Cure: 540685
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||line 119, col 60 to line 119, col 82 of module Cure: 1175774
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||line 119, col 36 to line 119, col 38 of module Cure: 540685
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2775:0 @!@!@
  ||||||line 115, col 23 to line 117, col 83 of module Cure: 540685:2786051
@!@!@ENDMSG 2775 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||line 116, col 25 to line 117, col 82 of module Cure: 610334
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||line 115, col 31 to line 115, col 41 of module Cure: 540685
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||line 119, col 48 to line 119, col 57 of module Cure: 540685
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||line 118, col 37 to line 118, col 39 of module Cure: 539931
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2775:0 @!@!@
  |||||line 115, col 23 to line 117, col 83 of module Cure: 539931:551453
@!@!@ENDMSG 2775 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||line 116, col 25 to line 117, col 82 of module Cure: 597453
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||line 115, col 31 to line 115, col 41 of module Cure: 539931
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 120, col 76 to line 120, col 81 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 120, col 76 to line 120, col 78 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||line 118, col 23 to line 119, col 82 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||line 119, col 25 to line 119, col 82 of module Cure: 540679
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||line 119, col 60 to line 119, col 82 of module Cure: 1175758
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||line 119, col 36 to line 119, col 38 of module Cure: 540679
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2775:0 @!@!@
  ||||||line 115, col 23 to line 117, col 83 of module Cure: 540679:2786027
@!@!@ENDMSG 2775 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||line 116, col 25 to line 117, col 82 of module Cure: 610316
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||line 115, col 31 to line 115, col 41 of module Cure: 540679
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||line 119, col 48 to line 119, col 57 of module Cure: 540679
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||line 118, col 37 to line 118, col 39 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2775:0 @!@!@
  |||||line 115, col 23 to line 117, col 83 of module Cure: 539929:551445
@!@!@ENDMSG 2775 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||line 116, col 25 to line 117, col 82 of module Cure: 597447
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||line 115, col 31 to line 115, col 41 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 120, col 84 to line 120, col 92 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 120, col 96 to line 120, col 96 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 112, col 17 to line 112, col 20 of module Cure: 3383543
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 121, col 8 to line 121, col 55 of module Cure: 539929
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<UpdateRequest line 123, col 1 to line 123, col 19 of module Cure>: 29215:293774
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 125, col 12 to line 125, col 35 of module Cure: 5711756
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 125, col 12 to line 125, col 17 of module Cure: 5417982
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 125, col 40 to line 125, col 46 of module Cure: 1995309
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 125, col 40 to line 125, col 42 of module Cure: 1701535
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 125, col 46 to line 125, col 46 of module Cure: 1701535
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 125, col 51 to line 125, col 57 of module Cure: 1144545
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 125, col 51 to line 125, col 53 of module Cure: 850771
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 125, col 57 to line 125, col 57 of module Cure: 850771
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 126, col 12 to line 126, col 32 of module Cure: 293774
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 126, col 12 to line 126, col 18 of module Cure: 425385
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 126, col 22 to line 126, col 32 of module Cure: 425385
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 127, col 12 to line 127, col 55 of module Cure: 293774
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 130, col 15 to line 133, col 104 of module Cure: 293774
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 124, col 17 to line 124, col 20 of module Cure: 3383541
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 134, col 8 to line 134, col 38 of module Cure: 293774
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<Replicate line 136, col 1 to line 136, col 15 of module Cure>: 12788:114381
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 137, col 8 to line 137, col 28 of module Cure: 3497920
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 137, col 8 to line 137, col 21 of module Cure: 3383539
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 137, col 25 to line 137, col 28 of module Cure: 3383539
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 139, col 14 to line 139, col 33 of module Cure: 2255464
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 139, col 14 to line 139, col 19 of module Cure: 2141083
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 140, col 14 to line 140, col 60 of module Cure: 114381
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 141, col 14 to line 141, col 60 of module Cure: 114381
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 142, col 14 to line 142, col 60 of module Cure: 114381
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 143, col 8 to line 143, col 49 of module Cure: 114381
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<Heartbeat line 145, col 1 to line 145, col 15 of module Cure>: 438919:2026702
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 146, col 8 to line 146, col 28 of module Cure: 5410240
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 146, col 8 to line 146, col 21 of module Cure: 3383538
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 146, col 25 to line 146, col 28 of module Cure: 3383538
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 148, col 14 to line 148, col 33 of module Cure: 4167784
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 148, col 14 to line 148, col 19 of module Cure: 2141082
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 149, col 14 to line 149, col 52 of module Cure: 2026702
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 150, col 14 to line 150, col 60 of module Cure: 2026702
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 151, col 8 to line 151, col 56 of module Cure: 2026702
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<Tick line 154, col 1 to line 154, col 10 of module Cure>: 991082:3383536
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 155, col 8 to line 155, col 46 of module Cure: 3383536
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 156, col 8 to line 156, col 52 of module Cure: 3383536
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 157, col 8 to line 158, col 105 of module Cure: 3383536
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 159, col 8 to line 159, col 49 of module Cure: 3383536
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<UpdateCSS line 161, col 1 to line 161, col 15 of module Cure>: 463902:3383533
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 162, col 8 to line 163, col 81 of module Cure: 3383533
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 164, col 8 to line 164, col 52 of module Cure: 3383533
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2774:0 @!@!@
<TypeOK line 56, col 1 to line 56, col 6 of module Cure>
@!@!@ENDMSG 2774 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 57, col 5 to line 63, col 63 of module Cure: 1982336
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2202:0 @!@!@
End of statistics.
@!@!@ENDMSG 2202 @!@!@
@!@!@STARTMSG 2200:0 @!@!@
Progress(15) at 2020-01-23 15:12:48: 11,480,106 states generated (7,749,497 s/min), 1,982,336 distinct states found (1,338,150 ds/min), 1,136,454 states left on queue.
@!@!@ENDMSG 2200 @!@!@
@!@!@STARTMSG 2199:0 @!@!@
11480106 states generated, 1982336 distinct states found, 1136454 states left on queue.
@!@!@ENDMSG 2199 @!@!@
@!@!@STARTMSG 2186:0 @!@!@
Finished in 88887ms at (2020-01-23 15:12:48)
@!@!@ENDMSG 2186 @!@!@
