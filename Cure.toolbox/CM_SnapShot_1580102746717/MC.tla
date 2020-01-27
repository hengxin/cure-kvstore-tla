---- MODULE MC ----
EXTENDS Cure, TLC

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
const_1580102743636197000 == 
{c1, c2}
----

\* MV CONSTANT definitions Datacenter
const_1580102743636198000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_1580102743636199000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_1580102743636200000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_1580102743636201000 == 
{v}
----

\* SYMMETRY definition
symm_1580102743636202000 == 
Permutations(const_1580102743636197000) \union Permutations(const_1580102743636198000) \union Permutations(const_1580102743636199000) \union Permutations(const_1580102743636200000)
----

\* CONSTANT definitions @modelParameterConstants:1KeySharding
const_1580102743636203000 == 
k1 :> p1 @@ k2 :> p2
----

\* CONSTANT definitions @modelParameterConstants:2ClientAttachment
const_1580102743636204000 == 
c1 :> d1 @@ c2 :> d2
----

=============================================================================
\* Modification History
\* Created Mon Jan 27 13:25:43 CST 2020 by hengxin
