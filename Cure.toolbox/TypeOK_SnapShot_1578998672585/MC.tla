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
const_1578987021328358000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_1578987021328359000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_1578987021328360000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_1578987021328361000 == 
{v1}
----

\* MV CONSTANT definitions Client
const_1578987021328362000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1578987021328363000 == 
Permutations(const_1578987021328358000) \union Permutations(const_1578987021328359000) \union Permutations(const_1578987021328360000) \union Permutations(const_1578987021328362000)
----

\* CONSTANT definitions @modelParameterConstants:5ClientAttachment
const_1578987021328364000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:6KeySharding
const_1578987021328365000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Tue Jan 14 15:30:21 CST 2020 by hengxin
