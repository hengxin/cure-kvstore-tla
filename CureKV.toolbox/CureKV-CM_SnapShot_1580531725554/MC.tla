---- MODULE MC ----
EXTENDS CureKV, TLC

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
k1, k2, k3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v
----

\* MV CONSTANT definitions Client
const_1580480140947245000 == 
{c1, c2}
----

\* MV CONSTANT definitions Datacenter
const_1580480140947246000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_1580480140947247000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_1580480140947248000 == 
{k1, k2, k3}
----

\* MV CONSTANT definitions Value
const_1580480140947249000 == 
{v}
----

\* SYMMETRY definition
symm_1580480140947250000 == 
Permutations(const_1580480140947245000) \union Permutations(const_1580480140947246000) \union Permutations(const_1580480140947247000) \union Permutations(const_1580480140947248000)
----

\* CONSTANT definitions @modelParameterConstants:1KeySharding
const_1580480140947251000 == 
k1 :> p1 @@ k2 :> p2 @@ k3 :> p1
----

\* CONSTANT definitions @modelParameterConstants:2ClientAttachment
const_1580480140947252000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1580480140947254000 ==
\A c \in Client: Len(L[c]) <= 3
----
=============================================================================
\* Modification History
\* Created Fri Jan 31 22:15:40 CST 2020 by hengxin
