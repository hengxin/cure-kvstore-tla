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
const_15800247817572000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_15800247817573000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_15800247817584000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_15800247817585000 == 
{v}
----

\* MV CONSTANT definitions Client
const_15800247817586000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_15800247817587000 == 
Permutations(const_15800247817572000) \union Permutations(const_15800247817573000) \union Permutations(const_15800247817584000) \union Permutations(const_15800247817586000)
----

\* CONSTANT definitions @modelParameterConstants:0ClientAttachment
const_15800247817588000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:4KeySharding
const_15800247817589000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Sun Jan 26 15:46:21 CST 2020 by hengxin
