# lia4mathcomp
Preprocessing goals featuring mathcomp style operations before applying the lia tactic.

As of version 8.5, Coq's standard decision procedures for arithmetic like lia or omega still hard-wire the type of numbers (nat, Z, Q) and the definition of the operations (addition, ..) and predicates (<=, ...) with the ones of the standard library.

This small library uses a brute-force strategy to convert the (relevant) hypothesese and conclusion of a goal stated with the
definition of the [mathcomp](https://github.com/math-comp/math-comp) library to an equivalent shape that the lia tactic can process, and then apply this tactic.

It depdends on the [rat](https://github.com/math-comp/math-comp/blob/master/mathcomp/algebra/rat.v) library because it is supposed to succeed on goals like:

Lemma foo (x : int) : 1 / 2%:R < x -> 0 < x.
intlia.
Qed.

This file was originally written by Assia Mahboubi and Thomas Sibut-Pinote, while working on a [proof]( https://hal.inria.fr/hal-00984057) of the irrationality of zeta(3).
