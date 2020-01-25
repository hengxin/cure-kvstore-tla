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
const_157993665740671000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_157993665740672000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_157993665740673000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_157993665740674000 == 
{v}
----

\* MV CONSTANT definitions Client
const_157993665740675000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_157993665740676000 == 
Permutations(const_157993665740671000) \union Permutations(const_157993665740672000) \union Permutations(const_157993665740673000) \union Permutations(const_157993665740675000)
----

\* CONSTANT definitions @modelParameterConstants:0ClientAttachment
const_157993665740677000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:4KeySharding
const_157993665740678000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Sat Jan 25 15:17:37 CST 2020 by hengxin
