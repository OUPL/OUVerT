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

Lemma derive_decreasing_interv : 
  forall (a b : R) (f : R -> R) (pr : derivable f),
    a < b -> 
    (forall t : R, a < t < b -> derive_pt f t (pr t) < 0) ->
       forall x y : R, a <= x <= b -> a <= y <= b -> x < y -> f y < f x.
Proof.
  intros. apply Ropp_lt_cancel.
  set g := comp Ropp f.
  replace (- f x) with (g x); auto.
  replace (- f y) with (g y); auto.
  eapply (derive_increasing_interv a b g _ H); auto.
  intros. rewrite /g.
  erewrite derive_pt_opp.
  apply Ropp_lt_cancel. ring_simplify. apply H0. auto.
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


Lemma ln_upper_01_aux_deriv_at_pt c x :
  @derive_pt (fun x => 1 - x + x * exp c - exp (c * x))
               x (ln_upper_01_aux_deriv c x)
  = -1 + exp c - c*exp (c * x).
Proof.
  erewrite pr_nu_var2.
  erewrite derive_pt_minus.
  2: (intros; reflexivity).
  erewrite pr_nu_var2.
  erewrite derive_pt_plus.
  2: (intros; reflexivity).
  erewrite pr_nu_var2.
  erewrite derive_pt_minus.
  2: (intros; reflexivity).
  erewrite null_derivative_0.
  2: constructor. 
  erewrite derive_pt_id. ring_simplify.
  erewrite pr_nu_var.
  erewrite derive_pt_mult.
  2: reflexivity.
  erewrite derive_pt_id. ring_simplify.
  erewrite null_derivative_0.
  2: constructor.
  ring_simplify.
  erewrite pr_nu_var2.
  erewrite derive_pt_comp.
  Focus 2.
  intros. assert (exp (c * h) = (comp exp (fun x=> c * x)) h) by auto.
  rewrite H. reflexivity.
  erewrite derive_pt_exp.
  erewrite pr_nu_var2.
  erewrite derive_pt_scal.
  2: (intros; reflexivity).
  erewrite derive_pt_id. ring.
  Unshelve.
  apply derivable_pt_plus. apply derivable_pt_minus.
  apply derivable_pt_const. apply derivable_pt_id.
  apply derivable_pt_mult. apply derivable_pt_id.
  apply derivable_pt_const. apply derivable_pt_comp.
  apply derivable_pt_scal. apply derivable_pt_id...
  apply derivable_pt_exp. apply derivable_pt_minus.
  apply derivable_pt_const. apply derivable_pt_id.
  apply derivable_pt_mult. apply derivable_pt_id.
  apply derivable_pt_const. apply derivable_const.
  apply derivable_const. apply derivable_pt_mult.
  apply derivable_const. apply derivable_id.
Qed.

Lemma ln_upper_01_aux_bot c : 
  0 = 1 - 0 + 0 * exp c - exp (c * 0).
Proof.
  rewrite Rmult_0_r exp_0. ring.
Qed.

Lemma ln_upper_01_aux_top c : 
  0 = 1 - 1 + 1 * exp c - exp (c * 1).
Proof.
  rewrite Rmult_1_r Rmult_1_l. ring.
Qed.

Lemma ln_upper_01_aux_deriv_at_top c : 
  0 <= @derive_pt (fun x => 1 - x + x * exp c - exp (c * x))
             0 (ln_upper_01_aux_deriv c 0).
Proof.
  rewrite ln_upper_01_aux_deriv_at_pt.
  rewrite Rmult_0_r exp_0. ring_simplify.
  move: (ln_Taylor_upper' c) => H. fourier.
Qed.

Lemma ln_upper_01_aux_deriv_at_bot c : 
  0 >= @derive_pt (fun x => 1 - x + x * exp c - exp (c * x))
             1(ln_upper_01_aux_deriv c 1).
Proof.
  rewrite ln_upper_01_aux_deriv_at_pt.
  rewrite Rmult_1_r.
  suffices: exp c <= 1 + (c * exp c); first by
    (intros; fourier).
  move: (Rtotal_order c 0) => H1.
  destruct H1 as [H1 | [H1 | H1]].
  {
    suffices: ((1 -c) * exp c <= 1). intros H2.
    ring_simplify in H2.
    apply (Rplus_le_compat_l (c * exp c)) in H2.
    ring_simplify in H2. fourier.
    apply (Rle_trans _ ((exp (- c)) * (exp c)) _).
    apply Rmult_le_compat_r. apply Rlt_le. apply exp_pos.
    apply ln_Taylor_upper'. rewrite <- exp_plus.
    right. replace (-c + c) with 0. apply exp_0. ring.
  }
  { subst. right. rewrite exp_0. ring. }
  {
    suffices: (0 <= 1 + c * exp c - exp c); first by (intros; fourier).
    set f:= (fun x => 1 + x * exp x - exp x).
    replace 0 with (f 0); last by (rewrite /f exp_0; ring).
    replace (1 + c * exp c - exp c) with (f c); last by reflexivity.
    apply Rgt_lt in H1. left.
    eapply (@derive_increasing_interv 0 c f _ H1); try split; try fourier.
    intros. rewrite /f.
    erewrite pr_nu_var2.
    erewrite derive_pt_plus.
    2: intros; reflexivity.
    erewrite pr_nu_var2.
    erewrite derive_pt_plus.
    2: intros; reflexivity.
    erewrite pr_nu_var.
    erewrite derive_pt_const.
    2: reflexivity.
    erewrite pr_nu_var.
    erewrite derive_pt_mult.
    2: reflexivity.
    erewrite derive_pt_id.
    erewrite derive_pt_exp.
    erewrite pr_nu_var.
    erewrite derive_pt_opp.
    2: reflexivity.
    erewrite derive_pt_exp.
    ring_simplify.
    apply Rmult_lt_0_compat.
    apply exp_pos.
    inversion H; fourier.
  }
  Unshelve.
  rewrite /f.
  all:
    repeat (try apply derivable_plus;
            try apply derivable_id;
            try apply derivable_mult;
            try apply derivable_opp;  
            try apply derivable_exp;
            try apply derivable_const).
  Qed.

Lemma ln_upper_01_aux_deriv_2 c :
  derivable (fun x => - 1 + exp c - c * exp (c * x)).
Proof.
  eapply derivable_plus.
  eapply derivable_plus;
  eapply derivable_const.
  eapply derivable_opp.
  eapply derivable_scal.
  eapply derivable_comp.
  eapply derivable_scal.
  eapply derivable_id.
  eapply derivable_exp.
Qed.

(* move me to numerics *)
Lemma square_pos :
  forall c, c <> 0 -> 0 < c^2.
Proof.
  intros. replace (c ^ 2) with (c * c) by ring.
  move: (Rtotal_order 0 c) => H0.
  destruct H0 as [H0 | [H0 | H0]].
  - apply Rmult_lt_0_compat; fourier.
  - congruence.
  - replace (c * c) with ((- c) * (- c)) by ring.
    apply Rmult_lt_0_compat; fourier.
Qed.

Lemma ln_upper_01_aux_deriv_2_decreasing c :
  c <> 0 -> 
  strict_decreasing (fun x => - 1 + exp c - c * exp (c * x)).
Proof.
  intros cNeq.
  apply negative_derivative with (pr := ln_upper_01_aux_deriv_2 c).
  intros.
  erewrite pr_nu_var2.
  erewrite derive_pt_plus.
    2: reflexivity.
  erewrite pr_nu_var2.
  erewrite derive_pt_plus.
    2: reflexivity.
  erewrite pr_nu_var.
  erewrite derive_pt_const.
    2: reflexivity.
  erewrite pr_nu_var.
  erewrite derive_pt_const.
    2: reflexivity.
  erewrite pr_nu_var.
  erewrite derive_pt_opp.
    2: reflexivity.
  erewrite pr_nu_var.
  erewrite derive_pt_scal.
    2: reflexivity.
  erewrite pr_nu_var.
  erewrite derive_pt_comp.
    Focus 2.
    replace (fun h : R => exp (c * h)) with (fun h : R => (comp exp (Rmult c)) h).
    all: reflexivity.
  erewrite pr_nu_var.
  erewrite derive_pt_exp.
    2: reflexivity.
  erewrite pr_nu_var.
  erewrite derive_pt_scal.
    2: reflexivity.
  erewrite derive_pt_id.
  ring_simplify.
  suffices: 0 < c ^ 2 * exp (c * x).
  intros H. apply Ropp_0_lt_gt_contravar in H. apply Rgt_lt.
  ring_simplify in H. fourier.
  apply Rmult_lt_0_compat.
  apply square_pos. auto.
  apply exp_pos.
  Unshelve.
  all:
    repeat (try apply derivable_plus;
            try apply derivable_id;
            try apply derivable_mult;
            try apply derivable_opp;
            try apply derivable_comp;
            try apply derivable_exp;
            try apply derivable_const).
Qed.

Lemma ln_upper_01 x c :
  0 < x < 1 ->
  c * x <= ln (1 - x + x * exp c).
Proof.
  intros.  
  apply exp_le_inv.
  rewrite exp_ln.
  case: (Req_EM_T c 0); intros.
  {
    subst. rewrite Rmult_0_l exp_0. fourier.
  }
  {
    suffices: (0 <= 1 - x + x * exp c - exp (c * x)).
    intros. fourier.
    set f := fun x => 1 - x + x * exp c - exp (c * x).
    set f' := fun x => -1 + exp c - c * exp (c * x).
    replace (1 - x + x * exp c - exp (c * x)) with (f x); last by auto.
    move: (Rolle f 0 1) => H_rolle.
    assert (0 < 1) as duh by fourier. 
    assert (f 0 = f 1) as H_bounds by
      (rewrite /f -(ln_upper_01_aux_bot c) -(ln_upper_01_aux_top c); auto).
    specialize (H_rolle
                (fun x _ => ln_upper_01_aux_deriv c x)
                (fun x _ => (derivable_continuous_pt _ x (ln_upper_01_aux_deriv c x)))
                duh H_bounds).
    destruct H_rolle as [z [z_bounds z_deriv]].
    clear duh H_bounds.
    move: (Rtotal_order x z) => H0.
    destruct H0 as [H0 | [H0 | H0]].
    + replace 0 with (f 0).
        2: rewrite /f; rewrite  <- (ln_upper_01_aux_bot c); auto.
      apply Rlt_le.
      inversion H.
      eapply derive_increasing_interv with
        (a := 0) (b := z) (pr := ln_upper_01_aux_deriv c); try split; try fourier.
      intros.
      rewrite ln_upper_01_aux_deriv_at_pt.
      rewrite ln_upper_01_aux_deriv_at_pt in z_deriv.
      move: (ln_upper_01_aux_deriv_2_decreasing b) => H4.
      rewrite <- z_deriv. apply H4. inversion H3. auto.
    + replace 0 with (f 0).
        2: rewrite /f; rewrite  <- (ln_upper_01_aux_bot c); auto.
      apply Rlt_le.
      inversion H.
      eapply derive_increasing_interv with
        (a := 0) (b := z) (pr := ln_upper_01_aux_deriv c); try split; try fourier.
      intros.
      rewrite ln_upper_01_aux_deriv_at_pt.
      rewrite ln_upper_01_aux_deriv_at_pt in z_deriv.
      move: (ln_upper_01_aux_deriv_2_decreasing b) => H4.
      rewrite <- z_deriv. apply H4. inversion H3. auto.
    + replace 0 with (f 1).
        2: rewrite /f; rewrite  <- (ln_upper_01_aux_top c); auto.
      apply Rlt_le.
      inversion H. apply Rgt_lt in H0.
      eapply derive_decreasing_interv with
        (a := z) (b := 1) (pr := ln_upper_01_aux_deriv c); try split; try fourier.
      intros.
      rewrite ln_upper_01_aux_deriv_at_pt.
      rewrite ln_upper_01_aux_deriv_at_pt in z_deriv.
      move: (ln_upper_01_aux_deriv_2_decreasing b) => H4.
      rewrite <- z_deriv. apply H4. inversion H3. auto.
  }
  {
    replace (1 - x + x * exp c) with (1 - (x * (1 - exp c))); last by ring.
    assert (1 - exp c < 1).
    {
      move: (exp_pos c) => H0. fourier. 
    }
    move: (Rtotal_order (1 - exp c) 0) => H1.
    apply Rlt_Rminus.
    destruct H1 as [H1 | [H1 | H1]].
    * inversion H. apply (@Rlt_trans _ 0 _).
      apply Ropp_lt_cancel.
      assert (- ( 1 - exp c ) > 0) by fourier.
      replace (- (x * (1 - exp c))) with (x * - (1 - exp c)); last by ring. 
      replace (- 0) with 0; last by ring.
      apply Rmult_lt_0_compat; fourier. fourier. 
    * rewrite H1. fourier.
    * replace 1 with (1 * 1) at 2. inversion H. 
      apply Rmult_le_0_lt_compat; fourier. ring.
  }
Qed.

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


(* Lemmas in support of Gibbs' inequality. *)

Lemma exp_minus_1_minus_x_at_1 :
  exp (1-1) - 1 = 0.
Proof.
  replace (exp (1-1)) with 1. field.
  rewrite <- exp_0 at 1. f_equal. field.
Qed.

Lemma derivable_exp_minus_1_minus_x  : derivable (fun x => exp(x-1) -x). 
Proof.
  rewrite /derivable => x.
  apply derivable_pt_minus.
  replace (fun x0 : R => exp (x0 -1)) with
    (comp (fun x => exp x) (fun x => x - 1)).
  apply derivable_pt_comp.
  apply derivable_pt_minus.
  apply derivable_pt_id.
  apply derivable_pt_const.
  apply derivable_pt_exp. auto.
  apply derivable_pt_id.
Defined.

Lemma deriv_at_point_exp_minus_1_minus_x : 
  forall x pf,
    derive_pt (fun x => exp(x-1) -x) x pf = exp(x-1) -1.
Proof.
  intros. rewrite (pr_nu _ _ _ (derivable_exp_minus_1_minus_x x)).
  rewrite /derivable_exp_minus_1_minus_x.
  rewrite derive_pt_minus
          derive_pt_comp
          derive_pt_minus
          derive_pt_id
          derive_pt_const 
          derive_pt_exp.
  field.
Qed.

Lemma deriv_at_point_exp_minus_1_minus_x_deriv_on_0_1 :
  forall x pf, 0 < x < 1 -> derive_pt (fun x => exp(x-1) - x) x pf < 0.
Proof.
  intros. rewrite deriv_at_point_exp_minus_1_minus_x.
  suffices: (exp (x - 1) < 1).
  intros. fourier.
  replace 1 with (exp 0) at 2.
  apply exp_increasing. destruct H. fourier.
  apply exp_0.
Qed.

Lemma deriv_at_point_exp_minus_1_minus_x_deriv_on_1_inf :
  forall x pf, 1 < x -> 0 < derive_pt (fun x => exp(x-1) - x) x pf.
Proof.
  intros. rewrite deriv_at_point_exp_minus_1_minus_x.
  suffices: (1 < exp (x - 1)).
  intros. fourier.
  replace 1 with (exp 0) at 1.
  apply exp_increasing. fourier.
  apply exp_0.
Qed.

Lemma exp_minus_1_minus_x :
  forall x, 0 < x -> 0 <= exp(x - 1) - x.
Proof.
  intros.
  case: (Rtotal_order x 1).
  - intros. rewrite <- exp_minus_1_minus_x_at_1. left.
    set (f := fun x => exp (x - 1) - x).
    replace (exp (1 - 1) - 1) with (f 1); try auto.
    replace (exp (x - 1) - x) with (f x); try auto.
    assert (0 < 1) by fourier.
    eapply (derive_decreasing_interv H0).
    intros. apply deriv_at_point_exp_minus_1_minus_x_deriv_on_0_1.
    auto. split; fourier.
    split; fourier. auto.
  - intros. destruct b. subst. right.
    replace (exp (1-1)) with 1. field.
    rewrite <- exp_0 at 1. f_equal. field.
  - intros. rewrite <- exp_minus_1_minus_x_at_1. left.
    set (f := fun x => exp (x - 1) - x).
    replace (exp (1 - 1) - 1) with (f 1); try auto.
    replace (exp (x - 1) - x) with (f x); try auto.
    assert (1 < x + 1) by fourier.
    eapply (derive_increasing_interv _ _ f _ H1).
    intros. apply deriv_at_point_exp_minus_1_minus_x_deriv_on_1_inf.
    destruct H2; fourier. split; fourier. split; fourier. fourier.
  Unshelve.
    all: apply derivable_exp_minus_1_minus_x.
Qed.
