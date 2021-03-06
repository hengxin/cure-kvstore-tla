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
const_158011300760022000 == 
{c1, c2}
----

\* MV CONSTANT definitions Datacenter
const_158011300760023000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_158011300760024000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_158011300760025000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_158011300760026000 == 
{v}
----

\* SYMMETRY definition
symm_158011300760027000 == 
Permutations(const_158011300760022000) \union Permutations(const_158011300760023000) \union Permutations(const_158011300760024000) \union Permutations(const_158011300760025000)
----

\* CONSTANT definitions @modelParameterConstants:1KeySharding
const_158011300760028000 == 
k1 :> p1 @@ k2 :> p2
----

\* CONSTANT definitions @modelParameterConstants:2ClientAttachment
const_158011300760029000 == 
c1 :> d1 @@ c2 :> d2
----

=============================================================================
\* Modification History
\* Created Mon Jan 27 16:16:47 CST 2020 by hengxin
