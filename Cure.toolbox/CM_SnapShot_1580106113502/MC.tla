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
const_158010610116612000 == 
{c1, c2}
----

\* MV CONSTANT definitions Datacenter
const_158010610116613000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_158010610116614000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_158010610116615000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_158010610116616000 == 
{v}
----

\* SYMMETRY definition
symm_158010610116617000 == 
Permutations(const_158010610116612000) \union Permutations(const_158010610116613000) \union Permutations(const_158010610116614000) \union Permutations(const_158010610116615000)
----

\* CONSTANT definitions @modelParameterConstants:1KeySharding
const_158010610116618000 == 
k1 :> p1 @@ k2 :> p2
----

\* CONSTANT definitions @modelParameterConstants:2ClientAttachment
const_158010610116619000 == 
c1 :> d1 @@ c2 :> d2
----

=============================================================================
\* Modification History
\* Created Mon Jan 27 14:21:41 CST 2020 by hengxin
