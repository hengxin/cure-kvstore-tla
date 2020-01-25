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
const_157993116320742000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_157993116320743000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_157993116320744000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_157993116320745000 == 
{v}
----

\* MV CONSTANT definitions Client
const_157993116320746000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_157993116320747000 == 
Permutations(const_157993116320742000) \union Permutations(const_157993116320743000) \union Permutations(const_157993116320744000) \union Permutations(const_157993116320746000)
----

\* CONSTANT definitions @modelParameterConstants:0ClientAttachment
const_157993116320748000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:4KeySharding
const_157993116320749000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Sat Jan 25 13:46:03 CST 2020 by hengxin
