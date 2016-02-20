# lia4mathcomp
Preprocessing goals featuring mathcomp style operations before applying the lia/omega tactics, while waiting for a better modularity in these standard tools.

As of version 8.5, Coq's standard decision procedures for arithmetic like lia or omega hard-wire the type of numbers (nat, Z, Q) and the definition of the operations (addition, ..) and predicates (<=, ...) with the ones of the standard library.

This small library provides conversion tools to translate the (relevant) hypothesese and conclusion of a goal stated with the definition of the [mathcomp](https://github.com/math-comp/math-comp) library to an equivalent shape that the lia and omega tactics can process.

Tactics ssrnatlia and ssrnatomega aims at solving problems of linear arithemtic on type nat, expressed using the boolean comparison predicates and operations defined in the [ssrnat](https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/ssrnat.v) library, and possibly Prop conjunctions and disjunctions. Indeed, hypotheses like (x < y) && (1 < x) will not be taken into account because of the boolean conjunction (but one can try the propify_bool_connectives pre-processing first).

Tactic intlia aims at solving problems of linear arithemtic on type int, expressed using the boolean comparison predicates and operations defined in the [ssrint](https://github.com/math-comp/math-comp/blob/master/mathcomp/algebra/ssrint.v) library,  their generic notations, and  possibly Prop conjunctions and disjunctions.

The library also provide other experimental and/or brute force preprocessing tools.

It depends on the [rat](https://github.com/math-comp/math-comp/blob/master/mathcomp/algebra/rat.v) library because it is supposed to succeed on goals like:

Lemma foo (x : int) : 1 / 2%:R < x -> 0 < x.
intlia.
Qed.

File test_lia_tactics displays a few examples.

This file was originally written by Assia Mahboubi and Thomas Sibut-Pinote, while working on a [proof]( https://hal.inria.fr/hal-00984057) of the irrationality of zeta(3).
