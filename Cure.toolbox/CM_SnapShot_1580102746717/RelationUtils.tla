------------------------------- MODULE RelationUtils -------------------------------
(*
Relation related operators.
*)
EXTENDS Naturals, Sequences, FunctionUtils
----------------------------------------------------------------------------
(*
Basic definitions.
*)
Dom(R) == {a : <<a, b>> \in R} \* Domain of R
Ran(R) == {b : <<a, b>> \in R} \* Range of R
Support(R) == Dom(R) \cup Ran(R) \* Support of R
(*
Basic operations.
*)
Inverse(R) == {<<b, a>> : <<a, b>> \in R} \* Inverse of R
R | S == R \cap S \times S \* Restriction of R on S
    
R ** T == \* Composition of R and T
    LET SR == Support(R) 
        ST == Support(T) 
    IN  {<<r, t>> \in SR \X ST: \E s \in SR \cap ST: (<<r, s>> \in R) /\ (<<s, t>> \in T)}

GT(R, a) == {b \in Ran(R): <<a, b>> \in R}
LT(R, b) == {a \in Dom(R): <<a, b>> \in R}
(*
The following definition is from 
https://github.com/jameshfisher/tlaplus/blob/master/examples/TransitiveClosure/TransitiveClosure.tla
It also contains several other methods for computing TC.
*)
TC(R) == \* Transitive closure of R
    LET S == Support(R) 
        RECURSIVE TCR(_)
        TCR(T) == IF T = {} 
                  THEN R
                  ELSE LET r == CHOOSE s \in T : TRUE
                           RR == TCR(T \ {r})
                       IN  RR \cup {<<s, t>> \in S \X S : 
                                      <<s, r>> \in RR /\ <<r, t>> \in RR}
    IN  TCR(S)
(*
Example: SeqToRel(<<1, 2, 3>>) = {<<1, 2>>, <<1, 3>>, <<2, 3>>}
*)
SeqToRel(s) == \* Transform a (total order) sequence to a relation
    LET RECURSIVE SeqRel(_, _)
        SeqRel(seq, rel) ==
            IF Len(seq) <= 1
            THEN rel
            ELSE LET h == Head(seq)
                     t == Tail(seq)
                 IN  SeqRel(t, rel \cup {<<h, r>> : r \in Range(t)})
    IN  SeqRel(s, {})
(*
Basic properties.
*)
Reflexive(S, R) == \forall a \in S: <<a, a>> \in R \* is R reflexive?
    
Transitive(R) == \* Is R transitive?
    LET S == Support(R)     
    IN  \forall a, b, c \in S: (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R
    
Respect(R, T) == T \subseteq R \* Does R respect T?
=============================================================================
\* Modification History
\* Last modified Sat Jan 25 15:55:08 CST 2020 by hengxin
\* Created Tue Sep 18 19:16:04 CST 2018 by hengxin