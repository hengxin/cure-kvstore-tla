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
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Datacenter
const_157892252677242000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_157892252677243000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_157892252677244000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_157892252677245000 == 
{v1, v2}
----

\* MV CONSTANT definitions Client
const_157892252677246000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_157892252677247000 == 
Permutations(const_157892252677242000) \union Permutations(const_157892252677243000) \union Permutations(const_157892252677244000) \union Permutations(const_157892252677245000) \union Permutations(const_157892252677246000)
----

\* CONSTANT definitions @modelParameterConstants:2Sharding
const_157892252677248000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Mon Jan 13 21:35:26 CST 2020 by hengxin
