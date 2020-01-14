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
const_1578986793635348000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_1578986793635349000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_1578986793635350000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_1578986793635351000 == 
{v1}
----

\* MV CONSTANT definitions Client
const_1578986793635352000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1578986793635353000 == 
Permutations(const_1578986793635348000) \union Permutations(const_1578986793635349000) \union Permutations(const_1578986793635350000) \union Permutations(const_1578986793635352000)
----

\* CONSTANT definitions @modelParameterConstants:5ClientAttachment
const_1578986793635354000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:6KeySharding
const_1578986793635355000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Tue Jan 14 15:26:33 CST 2020 by hengxin
