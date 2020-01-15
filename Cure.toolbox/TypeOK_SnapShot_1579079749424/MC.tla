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
const_1579069142915418000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_1579069142915419000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_1579069142915420000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_1579069142915421000 == 
{v1}
----

\* MV CONSTANT definitions Client
const_1579069142915422000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1579069142915423000 == 
Permutations(const_1579069142915418000) \union Permutations(const_1579069142915419000) \union Permutations(const_1579069142915420000) \union Permutations(const_1579069142915422000)
----

\* CONSTANT definitions @modelParameterConstants:5ClientAttachment
const_1579069142915424000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:6KeySharding
const_1579069142915425000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Wed Jan 15 14:19:02 CST 2020 by hengxin
