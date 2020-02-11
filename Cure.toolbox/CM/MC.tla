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
const_1580115177628201000 == 
{c1, c2}
----

\* MV CONSTANT definitions Datacenter
const_1580115177628202000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_1580115177628203000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_1580115177628204000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_1580115177628205000 == 
{v}
----

\* SYMMETRY definition
symm_1580115177628206000 == 
Permutations(const_1580115177628201000) \union Permutations(const_1580115177628202000) \union Permutations(const_1580115177628203000) \union Permutations(const_1580115177628204000)
----

\* CONSTANT definitions @modelParameterConstants:1KeySharding
const_1580115177628207000 == 
k1 :> p1 @@ k2 :> p2
----

\* CONSTANT definitions @modelParameterConstants:2ClientAttachment
const_1580115177628208000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1580115177628210000 ==
\A c \in Client: Len(L[c]) <= 5
----
=============================================================================
\* Modification History
\* Created Mon Jan 27 16:52:57 CST 2020 by hengxin
