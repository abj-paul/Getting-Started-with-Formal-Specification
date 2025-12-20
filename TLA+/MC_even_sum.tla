------------------------ MODULE MC_even_sum -----------------------
EXTENDS even_sum
CONSTANT MaxNat
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
ASSUME T1
====================================================================
