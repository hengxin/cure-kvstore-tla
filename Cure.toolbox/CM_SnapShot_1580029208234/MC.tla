---- MODULE MC ----
EXTENDS Cure, TLC

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

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Datacenter
const_1580029207130147000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_1580029207130148000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_1580029207130149000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_1580029207130150000 == 
{v}
----

\* MV CONSTANT definitions Client
const_1580029207130151000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1580029207130152000 == 
Permutations(const_1580029207130147000) \union Permutations(const_1580029207130148000) \union Permutations(const_1580029207130149000) \union Permutations(const_1580029207130151000)
----

\* CONSTANT definitions @modelParameterConstants:0ClientAttachment
const_1580029207130153000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:4KeySharding
const_1580029207130154000 == 
k1 :> p1 @@ k2 :> p2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1580029207130156000 ==
\A c \in Client: Len(L[c]) <= 3
----
=============================================================================
\* Modification History
\* Created Sun Jan 26 17:00:07 CST 2020 by hengxin
