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
const_158011155466722000 == 
{c1, c2}
----

\* MV CONSTANT definitions Datacenter
const_158011155466723000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_158011155466724000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_158011155466725000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_158011155466726000 == 
{v}
----

\* SYMMETRY definition
symm_158011155466727000 == 
Permutations(const_158011155466722000) \union Permutations(const_158011155466723000) \union Permutations(const_158011155466724000) \union Permutations(const_158011155466725000)
----

\* CONSTANT definitions @modelParameterConstants:1KeySharding
const_158011155466728000 == 
k1 :> p1 @@ k2 :> p2
----

\* CONSTANT definitions @modelParameterConstants:2ClientAttachment
const_158011155466729000 == 
c1 :> d1 @@ c2 :> d2
----

=============================================================================
\* Modification History
\* Created Mon Jan 27 15:52:34 CST 2020 by hengxin
