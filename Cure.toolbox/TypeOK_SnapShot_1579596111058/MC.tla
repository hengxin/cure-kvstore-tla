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
const_157959575837697000 == 
{d1, d2}
----

\* MV CONSTANT definitions Partition
const_157959575837698000 == 
{p1, p2}
----

\* MV CONSTANT definitions Key
const_157959575837699000 == 
{k1, k2}
----

\* MV CONSTANT definitions Value
const_1579595758376100000 == 
{v}
----

\* MV CONSTANT definitions Client
const_1579595758376101000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1579595758376102000 == 
Permutations(const_157959575837697000) \union Permutations(const_157959575837698000) \union Permutations(const_157959575837699000) \union Permutations(const_1579595758376101000)
----

\* CONSTANT definitions @modelParameterConstants:5ClientAttachment
const_1579595758376103000 == 
c1 :> d1 @@ c2 :> d2
----

\* CONSTANT definitions @modelParameterConstants:6KeySharding
const_1579595758376104000 == 
k1 :> p1 @@ k2 :> p2
----

\* Constant expression definition @modelExpressionEval
const_expr_1579595758376106000 == 
( p1 :> (d1 :> (d1 :> 1 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) @@
  p2 :> (d1 :> (d1 :> 0 @@ d2 :> 1) @@ d2 :> (d1 :> 0 @@ d2 :> 1)) )
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1579595758376106000>>)
----

=============================================================================
\* Modification History
\* Created Tue Jan 21 16:35:58 CST 2020 by hengxin
