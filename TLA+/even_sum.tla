--------MODULE even_sum ---------
EXTENDS Naturals, TLAPS

Even(x) == x % 2 = 0
Odd(x) == x % 2 = 1

\* Z3 can solve it in a single step
THEOREM \A x \in Nat : Even(x+x)
BY Z3 DEF Even

=================================
