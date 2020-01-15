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
v1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Datacenter
const_157908477038412000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_157908477038413000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_157908477038414000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_157908477038415000 == 
{v1}
----

\* MV CONSTANT definitions Client
const_157908477038416000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_157908477038417000 == 
Permutations(const_157908477038412000) \union Permutations(const_157908477038413000) \union Permutations(const_157908477038414000) \union Permutations(const_157908477038416000)
----

\* CONSTANT definitions @modelParameterConstants:5ClientAttachment
const_157908477038418000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:6KeySharding
const_157908477038419000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Wed Jan 15 18:39:30 CST 2020 by hengxin
