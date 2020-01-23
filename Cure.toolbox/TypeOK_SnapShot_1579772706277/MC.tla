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
const_157977201247222000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_157977201247223000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_157977201247224000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_157977201247225000 == 
{v}
----

\* MV CONSTANT definitions Client
const_157977201247226000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_157977201247227000 == 
Permutations(const_157977201247222000) \union Permutations(const_157977201247223000) \union Permutations(const_157977201247224000) \union Permutations(const_157977201247226000)
----

\* CONSTANT definitions @modelParameterConstants:0ClientAttachment
const_157977201247228000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:4KeySharding
const_157977201247229000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Thu Jan 23 17:33:32 CST 2020 by hengxin
