# Normalization by evaluation in the delay monad (formalized in Agda)

Based on

* James Chapman. 2009. **Type Checking and Normalization.**
Ph.D. thesis, School of Computer Science, University of Nottingham.

* Andreas Abel and James Chapman. 2014.
**Normalization by evaluation in the delay monad: A case study for
coinduction via copatterns and sized types.**
In MSFP'14, volume 153 of EPTCS, pages 51--67.
<http://arxiv.org/abs/1406.2059v1>

There are 2 subprojects:

* CombinatoryCalculus
* LambdaCalculus

The Agda code in `LambdaCalculus` has been produced by refactoring
<http://www2.tcs.ifi.lmu.de/~abel/eptcs14.lagda>.

Note that the paper Abel and Chapman (2014) doesn't provide the
proofs of soundness and completeness. Thus they have been produced
by refactoring the code in
 <https://github.com/sergei-romanenko/chapman-big-step-normalization>
(without using horrible annotations **{-# TERMINATING #-}**).

The Agda code in `CombinatoryCalculus` can be considered as a simplification
of the code in `LambdaCalculus`. Again, there are given proofs of
soundness and completeness that don't make use of **{-# TERMINATING #-}**.
