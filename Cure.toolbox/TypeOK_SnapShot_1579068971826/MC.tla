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
const_1579068964799408000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_1579068964799409000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_1579068964799410000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_1579068964799411000 == 
{v1}
----

\* MV CONSTANT definitions Client
const_1579068964799412000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1579068964799413000 == 
Permutations(const_1579068964799408000) \union Permutations(const_1579068964799409000) \union Permutations(const_1579068964799410000) \union Permutations(const_1579068964799412000)
----

\* CONSTANT definitions @modelParameterConstants:5ClientAttachment
const_1579068964799414000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:6KeySharding
const_1579068964799415000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Wed Jan 15 14:16:04 CST 2020 by hengxin
