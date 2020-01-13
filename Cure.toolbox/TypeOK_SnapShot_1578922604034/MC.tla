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
const_157892260101450000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_157892260101451000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_157892260101452000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_157892260101453000 == 
{v1, v2}
----

\* MV CONSTANT definitions Client
const_157892260101454000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_157892260101455000 == 
Permutations(const_157892260101450000) \union Permutations(const_157892260101451000) \union Permutations(const_157892260101452000) \union Permutations(const_157892260101453000) \union Permutations(const_157892260101454000)
----

\* CONSTANT definitions @modelParameterConstants:2Sharding
const_157892260101456000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Mon Jan 13 21:36:41 CST 2020 by hengxin
