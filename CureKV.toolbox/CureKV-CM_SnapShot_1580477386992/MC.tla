---- MODULE MC ----
EXTENDS CureKV, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
k1, k2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v
----

\* MV CONSTANT definitions Client
const_1580399994693223000 == 
{c1, c2}
----

\* MV CONSTANT definitions Datacenter
const_1580399994693224000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_1580399994693225000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_1580399994693226000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_1580399994693227000 == 
{v}
----

\* SYMMETRY definition
symm_1580399994693228000 == 
Permutations(const_1580399994693223000) \union Permutations(const_1580399994693224000) \union Permutations(const_1580399994693225000) \union Permutations(const_1580399994693226000)
----

\* CONSTANT definitions @modelParameterConstants:1KeySharding
const_1580399994693229000 == 
k1 :> p1 @@ k2 :> p2
----

\* CONSTANT definitions @modelParameterConstants:2ClientAttachment
const_1580399994693230000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1580399994693232000 ==
\A c \in Client: Len(L[c]) <= 3
----
=============================================================================
\* Modification History
\* Created Thu Jan 30 23:59:54 CST 2020 by hengxin
