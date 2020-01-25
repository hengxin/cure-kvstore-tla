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
const_157993122876452000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_157993122876453000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_157993122876454000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_157993122876455000 == 
{v}
----

\* MV CONSTANT definitions Client
const_157993122876456000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_157993122876457000 == 
Permutations(const_157993122876452000) \union Permutations(const_157993122876453000) \union Permutations(const_157993122876454000) \union Permutations(const_157993122876456000)
----

\* CONSTANT definitions @modelParameterConstants:0ClientAttachment
const_157993122876458000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:4KeySharding
const_157993122876459000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Sat Jan 25 13:47:08 CST 2020 by hengxin
