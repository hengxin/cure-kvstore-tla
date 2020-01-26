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
const_157994428339181000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_157994428339182000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_157994428339183000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_157994428339184000 == 
{v}
----

\* MV CONSTANT definitions Client
const_157994428339185000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_157994428339186000 == 
Permutations(const_157994428339181000) \union Permutations(const_157994428339182000) \union Permutations(const_157994428339183000) \union Permutations(const_157994428339185000)
----

\* CONSTANT definitions @modelParameterConstants:0ClientAttachment
const_157994428339187000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:4KeySharding
const_157994428339188000 == 
k1 :> p1 @@ k2 :> p2
----

=============================================================================
\* Modification History
\* Created Sat Jan 25 17:24:43 CST 2020 by hengxin
