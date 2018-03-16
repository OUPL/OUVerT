Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import QArith Reals Rpower Ranalysis Fourier MVT.

Lemma ln_le (x y : R) : (0 < x -> x <= y -> ln x <= ln y)%R.
Proof.
  move=> H0; case=> H.
  left; apply: ln_increasing=> //.
  by right; subst x.
Qed.

(* The construction of the derivability proof is needed to apply
   the compositional rules in the next two proofs *)
Definition aux_const x : derivable_pt (fun x => (exp x - (1 +x))%R) x :=
  derivable_pt_minus exp (Rplus 1) x (derivable_pt_exp x)
    (derivable_pt_plus (fun _ : R => 1%R) id x (derivable_pt_const 1 x)
    (derivable_pt_id x)).

Lemma aux_neg y (H :(y < 0)%R) :
    (derive (fun x => (exp x - (1 + x))%R) aux_const y < 0)%R.
Proof.
    rewrite /derive /aux_const
            derive_pt_minus
            derive_pt_exp
            derive_pt_plus
            derive_pt_const
            derive_pt_id.
    apply Rlt_minus.
    rewrite -exp_0 Rplus_0_l.
    apply exp_increasing => //.
Qed.

Lemma aux_pos y (H :(0 <= y)%R) :
    (derive (fun x => (exp x - (1 + x))%R) aux_const y >= 0)%R.
  Proof.
    rewrite /derive /aux_const
            derive_pt_minus
            derive_pt_exp
            derive_pt_plus
            derive_pt_const
            derive_pt_id.
    apply Rge_minus.
    rewrite -exp_0 Rplus_0_l.
    apply Rle_ge.
    case: H => H;
    first by left; apply exp_increasing => //.
    right. f_equal => //.
Qed.

Lemma ln_Taylor_upper' x : ((1 + x) <= exp x)%R.
  Proof.
    apply Rge_le.
    apply Rminus_ge.
    set f := fun x => (exp x - (1 + x))%R.
    have H0 : (f x = exp x - (1 + x))%R => //.
    rewrite -H0; clear H0.
    have H0 : (f 0 = 0)%R by
      rewrite /f exp_0 Rplus_0_r;
      apply Rminus_diag_eq => //.
    rewrite -H0.
    case: (Rtotal_order x 0) => H.
    {
      left.
      apply (MVT_cor1 f x 0 aux_const) in H.
      case: H => c; case => H1 H2.
      rewrite H0 !Rminus_0_l in H1.
      rewrite H0.
      have H3 :  (x < 0)%R
        by case: H2 =>  H2 H3; apply (Rlt_trans x c 0) => //.
      apply Ropp_eq_compat in H1.
      rewrite Ropp_involutive in H1.
      rewrite H1.
      apply Rlt_gt.
      rewrite Ropp_mult_distr_l.
      apply Rmult_lt_0_compat.
      apply Ropp_0_gt_lt_contravar.
      apply Rlt_gt.
      apply aux_neg.
      case: H2 => //.
      fourier.
    }
    {
      case: H => H;
      first by subst; rewrite /f Rplus_0_r exp_0; right => //.
      apply (MVT_cor1 f 0 x aux_const) in H.
      case: H => c; case => H1 H2.
      rewrite H0 !Rminus_0_r in H1.
      rewrite H0.
      have H3 :  (0 < x)%R
        by case: H2 =>  H2 H3; apply (Rlt_trans 0 c x) => //.
      rewrite H1.
      apply Rle_ge.
      rewrite -(Rmult_0_l x).
      apply Rmult_le_compat.
      right => //.
      left => //.
      apply Rge_le.
      apply aux_pos.
      left. case: H2 => //.
      right => //.
    }
Qed.

Lemma ln_Taylor_upper x : (x < 1)%R ->  (ln (1 - x) <= -x)%R.
Proof.
    intros h.
    rewrite /ln.
    case_eq (Rlt_dec 0 (1-x)); move => h1 h2;
    last by apply False_rec; apply h1; fourier.
    rewrite /Rln => /=.
    destruct (ln_exists (1 - x) h1) as [x0 e0].
    apply Rplus_le_reg_l with (r := 1%R).
    rewrite /Rminus in e0.
    rewrite e0.
    apply ln_Taylor_upper'.
Qed.

Lemma deriv_aux_lower :
  derivable (fun x : R => ((1 - x) * exp (x + x ^ 2))%R).
Proof.
    rewrite /derivable => x.
    apply derivable_pt_mult.
    apply derivable_pt_minus.
    apply derivable_pt_const.
    apply derivable_pt_id.
    set f1 := fun x => (x + x ^2)%R.
    set f2 := fun x => exp x.
    have H : (fun x0 : R => exp (x0 + x0 ^ 2))
              = Ranalysis1.comp f2 f1 => //.
    rewrite H.
    apply derivable_pt_comp.
    rewrite /f1.
    apply derivable_pt_plus.
    apply derivable_pt_id.
    apply derivable_pt_mult.
    apply derivable_pt_id.
    apply derivable_pt_mult.
    apply derivable_pt_id.
    apply derivable_pt_const.
    apply derivable_pt_exp.
Defined.

Lemma ln_Taylor_lower_aux_lt_0 x (H : (x < 0)%R) :
  (derive_pt (fun x : R => ((1 - x) * exp (x + x ^ 2))%R)
    x (deriv_aux_lower x) < 0)%R.
Proof.
    rewrite /deriv_aux_lower
            derive_pt_mult
            derive_pt_minus
            derive_pt_const
            derive_pt_id
            (* Need to eliminate the substitution in the above proof *)
            /ssr_have /eq_rec_r /eq_rec /eq_rect => /=.
    rewrite derive_pt_comp
            derive_pt_exp
            derive_pt_plus
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_const.
    ring_simplify.
    set Y :=  exp (x + x * (x * 1)).
    have H0 : (- 2* Y * x ^ 2 + Y * x = Y * ( x * (-2 * x + 1)))%R
      by ring.
    rewrite H0.
    rewrite  -(Rmult_0_r Y).
    apply Rmult_lt_compat_l.
    apply exp_pos.
    rewrite  -(Rmult_0_r x).
    apply Rmult_lt_gt_compat_neg_l => //.
    fourier.
Qed.

Lemma ln_Taylor_lower_aux_gt_0
    x (H0 : (0 < x)%R) (H1 : (x <= 1/2)%R) :
    (derive_pt (fun x : R => ((1 - x) * exp (x + x ^ 2))%R)
      x (deriv_aux_lower x) >= 0)%R.
Proof.
    rewrite /deriv_aux_lower
            derive_pt_mult
            derive_pt_minus
            derive_pt_const
            derive_pt_id
            (* Need to eliminate the substitution in the above proof *)
            /ssr_have /eq_rec_r /eq_rec /eq_rect => /=.
    rewrite derive_pt_comp
            derive_pt_exp
            derive_pt_plus
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_mult
            derive_pt_id
            derive_pt_const.
    ring_simplify.
    set Y :=  exp (x + x * (x * 1)).
    have H2 : (- 2* Y * x ^ 2 + Y * x = Y * ( x * (-2 * x + 1)))%R
      by ring.
    rewrite H2.
    rewrite  -(Rmult_0_r Y).
    apply Rmult_ge_compat_l.
    left.
    apply exp_pos.
    rewrite  -(Rmult_0_r x).
    apply Rmult_ge_compat_l => //. fourier. fourier.
Qed.

Lemma ln_Taylor_lower x : (x <= 1/2 -> -x - x^2 <= ln (1 - x))%R.
Proof. 
    intros H.
    rewrite -[(-x - x^2)%R] ln_exp.
    apply ln_le; first by apply exp_pos.
    have h : ((- x - x ^2) = - (x + x^2))%R by field.
      rewrite h. clear h.
    apply (Rmult_le_reg_r (/exp (- (x + x ^ 2))));
      first by apply Rinv_0_lt_compat; apply exp_pos.
    rewrite Rinv_r;
      last by move: (exp_pos (- (x + x ^ 2))%R) => H0 H1; fourier.
    rewrite exp_Ropp Rinv_involutive;
      last by move: (exp_pos (x + x^2)%R) => H0 H1; fourier.
    set F := fun x => ((1 - x) * exp (x + x^2))%R.
    have H0 : (F x = (1 - x) * exp (x + x ^ 2))%R => //.
    rewrite -H0; clear H0.
    have H1 : (F 0 = 1)%R. rewrite /F.
    have H0 : (0 + 0^2 = 0)%R by ring.
      rewrite H0; ring_simplify; apply exp_0; clear H0.
    rewrite -H1.
    apply Rminus_le.
    case: (Rtotal_order 0 x) => H2; last case: H2 => H2.
    {
      move: (MVT_cor1 F 0 x deriv_aux_lower H2) => H3.
      destruct H3 as [c [H3 [H4 H5]]].
      have h : (F 0 - F x = - (F x - F 0))%R. ring.
      rewrite h H3. apply Rge_le. clear h.
      rewrite Rminus_0_r.
      apply Ropp_0_le_ge_contravar.
      apply Rmult_le_pos; last by fourier.
      apply Rge_le.
      apply ln_Taylor_lower_aux_gt_0 => //.
      fourier.
    }
    {
      right. subst. ring.
    }
    {
      move: (MVT_cor1 F x 0 deriv_aux_lower H2) => H3.
      destruct H3 as [c [H3 [H4 H5]]].
      rewrite H3.
      rewrite Rminus_0_l.
      rewrite -(Rmult_0_r (derive_pt F c (deriv_aux_lower c))%R).
      apply Rmult_le_compat_neg_l; last by fourier.
      left.
      apply ln_Taylor_lower_aux_lt_0 => //.
    }
Qed.

Lemma exp_Taylor_lower x : (x <= 1/2 -> exp(-x - x^2) <= 1 - x)%R.
Proof.
    move => H.
    move: (ln_Taylor_lower H); case.
    { move => H2; left.
      rewrite -[(1 - _)%R]exp_ln.
      { apply: exp_increasing.
        apply: H2. }
      fourier. }
    move => ->; rewrite exp_ln; fourier.
Qed.

Lemma exp_mult x y : exp (x * INR y) = exp x ^ y.
Proof.
  apply: ln_inv; try apply: exp_pos.
  { apply: pow_lt; apply: exp_pos. }
  rewrite ln_exp; elim: y => //.
  { simpl; rewrite Rmult_0_r ln_1 //. }
  move => n IH /=; rewrite ln_mult; try apply: exp_pos.
  { rewrite -IH; clear IH; case: n.
    { by rewrite Rmult_1_r ln_exp /= Rmult_0_r Rplus_0_r. }
    by move => n; rewrite ln_exp // Rmult_plus_distr_l Rmult_1_r Rplus_comm. }
  apply: pow_lt; apply: exp_pos.    
Qed.

Lemma exp_le_inv : forall x y : R, exp x <= exp y -> x <= y.
Proof.
  intros. inversion H.
  left. apply exp_lt_inv; auto.
  right. apply exp_inv. auto. 
Qed.

Lemma ln_upper_01_aux_bot c : 
  0 = 1 - 0 + 0 * exp c - exp (c * 0).
Proof.
  rewrite Rmult_0_r exp_0. ring.
Qed.

Lemma ln_upper_01_aux_mid c : 
  0 <= 1 - (1/2) + (1/2) * exp c - exp (c * (1/2)).
Proof.
Admitted.

Lemma ln_upper_01_aux_top c : 
  0 = 1 - 1 + 1 * exp c - exp (c * 1).
Proof.
  rewrite Rmult_1_r Rmult_1_l. ring.
Qed.

Lemma ln_upper_01_aux_deriv c :
  derivable (fun x => 1 - x + x * exp c - exp (c * x)).
Proof.
  apply derivable_minus.
  apply derivable_plus.
  apply derivable_minus.
  apply derivable_const.
  apply derivable_id.
  apply derivable_mult.
  apply derivable_id.
  apply derivable_const.
  apply derivable_comp.
  apply derivable_mult.
  apply derivable_const.
  apply derivable_id.
  apply derivable_exp.
Qed.

Lemma ln_upper_01 x c :
  0 < x < 1 ->
  c * x <= ln (1 - x + x * exp c).
Proof.
  intros.
  apply exp_le_inv.
  rewrite exp_ln.
  move: (Rtotal_order x (1/2)) => H0.
  apply Rge_le.
  apply Rminus_ge.
  apply Rle_ge.
  set f := fun x => 1 - x + x * exp c - exp (c * x).
  replace (1 - x + x * exp c - exp (c * x)) with (f x).
  destruct H0 as [Hup | [Hhalf | Hdown]]; intros.
  + replace 0 with (f 0). left.
    eapply derive_increasing_interv with
      (a:= 0) (b := 1/2) (pr := ln_upper_01_aux_deriv c).
    fourier.
    intros. admit.
    split; fourier.
    split. destruct H. fourier. fourier. destruct H; auto.    
    rewrite {2} (ln_upper_01_aux_bot c) /f. auto. 
  + subst. rewrite /f. apply (ln_upper_01_aux_mid c).
  + replace 0 with (f 1). admit.
    rewrite (ln_upper_01_aux_top c) /f. auto. 
  + rewrite /f; auto.
  + admit.
Admitted. (*TODO: Sam? :-)*)

Lemma exp_upper_01 x c :
  0 <= x <= 1 ->
  exp (c * x) <= 1 - x + x * exp c.
Proof.
  case => H1 H2; case: H1 => H1x; last first.
  { subst x; rewrite Rmult_0_r exp_0 /Rminus Ropp_0 Rplus_0_r Rmult_0_l Rplus_0_r.
    apply: Rle_refl. }
  case: H2 => H2x; last first.
  { subst x; rewrite Rmult_1_r Rmult_1_l; fourier. }
  have Hx: 0 < 1 - x + x * exp c.
  { rewrite -[0]Rplus_0_l; apply: Rplus_lt_compat; try fourier.
    apply: Rmult_lt_0_compat => //; apply: exp_pos. }
  move: (ln_upper_01 c (conj H1x H2x)); case.
  { move/exp_increasing => H; left; apply: Rlt_le_trans; first by apply: H.
    rewrite exp_ln //; apply: Rle_refl. }
  move => ->; rewrite exp_ln //; apply: Rle_refl.
Qed.  

