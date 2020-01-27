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
const_15801059855942000 == 
{c1, c2}
----

\* MV CONSTANT definitions Datacenter
const_15801059855943000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_15801059855944000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_15801059855945000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_15801059855946000 == 
{v}
----

\* SYMMETRY definition
symm_15801059855947000 == 
Permutations(const_15801059855942000) \union Permutations(const_15801059855943000) \union Permutations(const_15801059855944000) \union Permutations(const_15801059855945000)
----

\* CONSTANT definitions @modelParameterConstants:1KeySharding
const_15801059855948000 == 
k1 :> p1 @@ k2 :> p2
----

\* CONSTANT definitions @modelParameterConstants:2ClientAttachment
const_15801059855949000 == 
c1 :> d1 @@ c2 :> d2
----

=============================================================================
\* Modification History
\* Created Mon Jan 27 14:19:45 CST 2020 by hengxin
