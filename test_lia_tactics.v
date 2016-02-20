Require Import ZArith.
Require Import Psatz.

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path div choice.
From mathcomp
Require Import fintype tuple finfun bigop prime finset binomial.
From mathcomp
Require Import ssralg ssrnum ssrint rat.

Require Import lia_tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma test_nat1 (x y : nat) :  x < y -> x < y + 1.
Proof.
ssrnatlia.
Qed.

Lemma test_nat2 (x y : nat) :  x < y -> 0 < y.
Proof.
ssrnatlia.
Qed.

Lemma test_nat3 (x y : nat) :  x == y -> 1 < y -> 0 < x.
Proof.
try ssrnatlia.
ssrnatomega.
Qed.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Lemma test_int1 (x y : int) :  x < y -> x < y + 1.
Proof.
intlia.
Qed.


Lemma test_int2 (x : int) : 1 / 2%:R < x -> 0 < x.
intlia.
Qed.

Lemma test_int3 (x : int) : x > 0 /\ x < 2 -> x = 1.
intlia.
Qed.

Lemma test_int4 (x : int) : (x > 0) && (x < 2) -> x = 1.
propify_bool_connectives.
intlia.
Qed.