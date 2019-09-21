# ZFC-coq
An implementation of set theory in coq based on ZFC axioms.

## Goal
The standard coq library is based on type system. And this make two problems:
* Mathematicians usually use set theory for formalizing and make fundamentals of mathematics.
* Type system harm reuseablity of codes and proofs. For example, 1 of type nat is diffrent thing from 1 of type Z and 1 of type Q
so there is a plus function for nat ( Nat.add ) and for Z and for Q and ... and every theorem should be reproved and
every function should be redefined. But in set theory, N can defined as a subset of Z and Z ⊆ Q and Q ⊆ R and
... . And we can define a plus function at R and use it for N , Z , Q , ... .
