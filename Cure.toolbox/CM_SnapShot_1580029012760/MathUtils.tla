---------------------- MODULE MathUtils ----------------------
EXTENDS Naturals

PosInt == Nat \ {0}

Min(x, y) == IF x <= y THEN x ELSE y
Max(x, y) == IF x <= y THEN y ELSE x

SetMin(s) == CHOOSE a \in s: \A b \in s: a <= b
SetMax(s) == CHOOSE a \in s: \A b \in s: b <= a
=============================================================================
\* Modification History
\* Last modified Sun Jan 26 15:28:33 CST 2020 by hengxin
\* Created Fri Jul 06 13:08:50 CST 2018 by hengxin