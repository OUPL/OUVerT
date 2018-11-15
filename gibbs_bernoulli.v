Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.
Require Import Coq.Classes.RelationClasses.

Require Import QArith Reals Rpower Ranalysis Fourier Lra.

Require Import dist.

Lemma ln_minus_1 x : 0 < x -> ln x <= x - 1.
Proof.
  intros Hx.
  apply expfacts.exp_le_inv.
  rewrite exp_ln; auto.
Admitted.

Lemma ln_div x y : 0 < x -> 0 < y -> ln (x / y) = ln x - ln y.
Proof.
  intros Hx Hy.
  rewrite ln_mult; auto.
  rewrite ln_Rinv; auto.
  apply Rinv_0_lt_compat; auto.
Qed.

Lemma ln_ratio_neg x y : 0 < x -> 0 < y -> ln (x / y) = - ln (y / x).
Proof. intros Hn Hd; repeat rewrite ln_div; auto; lra. Qed.

Definition RE_b p q :=
  p * ln (p / q) + (1 - p) * ln ((1 - p) / (1 - q)).

Definition neg_RE_b p q :=
  p * ln (q / p) + (1 - p) * ln ((1 - q) / (1 - p)).

Lemma neg_RE_b_neg p q :
  0 < p < 1 ->
  0 < q < 1 ->
  - RE_b p q = neg_RE_b p q.
Proof.
  intros Hp Hq.
  unfold neg_RE_b.
  rewrite ln_ratio_neg; try lra.
  rewrite [ln ((1 - q) / _)] ln_ratio_neg; try lra.
  unfold RE_b; lra.
Qed.

Lemma neg_RE_b_le_0 p q :
  0 < p < 1 ->
  0 < q < 1 ->
  neg_RE_b p q <= 0.
Proof.
  intros Hp Hq.
  unfold neg_RE_b.
  apply Rle_trans with (r2 := p*((q/p) - 1) + (1-p)*(((1-q)/(1-p)) - 1)).
  { apply Rfourier_le_le; try lra.
    { apply Rmult_le_compat_l; try lra.
      apply ln_minus_1.
      apply Rdiv_lt_0_compat; lra. }
    apply ln_minus_1.
    apply Rdiv_lt_0_compat; lra. }
  - right; field; lra.
Qed.


Theorem gibbs_Bernoulli :
  forall (p q:R) (p_ax:0<p<1) (q_ax:0<q<1),
  0 <= RE_Bernoulli p q.
Proof.
  intros p q Hp Hq.
  apply Ropp_le_cancel.
  rewrite RE_Bernoulli_def.
  rewrite neg_RE_b_neg; auto.
  rewrite Ropp_0.
  apply neg_RE_b_le_0; auto.
Qed.
