Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import QArith Reals Rpower Ranalysis Fourier Lra.

Require Import bigops numerics expfacts dist axioms.

Section relative_entropy_lemmas.
  Variables p eps : R.
  Variable p_range : 0 < p < 1.
  Variable eps_range : 0 < eps < 1 - p.

  Lemma RE_Bernoulli_bounded_below : 
    RE_Bernoulli (p + eps) p >= 2 * eps^2.
  Proof.
    have p_eps_ax: 0<p+eps<1 by lra.
    move: (pinsker_Bernoulli p_eps_ax p_range) => H.
    have Hx: TV_Bernoulli (p+eps) p = eps.
    { rewrite TV_Bernoulli_eq.
      have ->: Rabs (p + eps - p) = Rabs eps.
      { f_equal; lra. }
      case: eps_range => H1 H2; rewrite Rabs_right => //; lra. }
    have H2: RE_Bernoulli (p + eps) p / 2 >= eps*eps.
    { move: H; rewrite Hx; clear Hx.
      move: (gibbs_Bernoulli p_eps_ax p_range).
      move: (RE_Bernoulli _ _)=>X HX.
      have: 0 <= X/2 by lra.
      move: (X/2) => Y HX2 H2.
      have: sqrt Y*sqrt Y >= eps*eps.
      { case: eps_range => Hx Hy.
        apply: Rmult_ge_compat => //; lra. }
      rewrite sqrt_sqrt => //. }
    lra.
  Qed.
End relative_entropy_lemmas.

Section chernoff_geq.
  Variable T : finType.
  Variables d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.

  (* The distribution function corresponding to m samples of d *)
  Definition d_prod (_ : 'I_m) := d.
  
  Variable f : 'I_m -> T -> R.
  Variable f_range : forall i x, 0 <= f i x <= 1.
  Definition identically_distributed := forall i j : 'I_m, expValR d (f i) = expValR d (f j).  
  Variable f_identically_distributed : identically_distributed.
  (* Mutual independence of the f's: 
     -The expected value of the product of a function of the f_i's is equal to 
      the product of the expected value of the same function of the f_i's.
     -NOTE: this is a stronger assumption than pairwise independence. *)
  Definition mutual_independence :=
    forall g : R -> R, 
    expValR (prodR d_prod) (fun p => big_product (enum 'I_m) (fun i => g (f i (p i)))) =
    big_product (enum 'I_m) (fun i => expValR d (fun x => g (f i x))).
  Variable f_independent : mutual_independence.

  Definition mR := INR m.
  Lemma mR_gt0 : (0 < mR)%R.
  Proof. by apply: lt_0_INR; apply/ltP. Qed.
  Lemma mR_neq0 : (mR <> 0)%R.
  Proof. by move: mR_gt0 => H H2; rewrite H2 in H; move: (Rlt_asym _ _ H). Qed.
  
  Definition i0 : 'I_m := Ordinal m_gt0.
  Definition p := expValR d (f i0).
  Variable p_nontrivial : 0 < p < 1. (*required to construct lambda_min*)  
  
  Lemma expVal_independence c :
    expValR (prodR d_prod) (fun p => big_product (enum 'I_m) (fun i => exp (c * f i (p i)))) =
    big_product (enum 'I_m) (fun i => expValR d (fun x => exp (c * f i x))).
  Proof.
    set (g x := exp (c * x)).
    change
      (expValR (prodR d_prod)
        (fun p => big_product (enum 'I_m) (fun i : ordinal_finType m => g (f i (p i)))) =
      big_product (enum 'I_m)
        (fun i : ordinal_finType m => expValR d (fun x => g (f i x)))).
    by rewrite f_independent.
  Qed.

  Variable eps : R.
  Variable eps_gt0 : 0 < eps.
  Variable eps_lt_1p : eps < 1 - p.
  (*This above assumption, which is required to show that lambda_min > 0, 
    is strange in the sense that it limits the values epsilon we can choose 
    to (0, 1-p).*)
  
  Definition q := p + eps.

  Lemma lt_p_q : p < q.
  Proof.
    rewrite /q; rewrite -[p]Rplus_0_r.
    have ->: p + 0 + eps = p + eps by rewrite Rplus_0_r.
    apply: Rplus_le_lt_compat => //.
    apply: Rle_refl.
  Qed.

  Lemma lt_p_p2_eps : 0 < p - (p*(p + eps)).
  Proof.
    apply: Rlt_Rminus; rewrite Rmult_plus_distr_l.
    apply: (@Rlt_le_trans _ (p*p + p*(1-p)) _).
    { apply: Rplus_lt_compat_l.
      apply Rmult_lt_compat_l => //.
      by case: p_nontrivial. }
    rewrite Rmult_plus_distr_l Rmult_1_r [p + _]Rplus_comm -Rplus_assoc.
    rewrite -Ropp_mult_distr_r Rplus_opp_r Rplus_0_l; apply: Rle_refl. 
  Qed.
  
  Lemma p_leq1 : p <= 1.
  Proof.
    rewrite /p/expValR -d_dist; apply: big_sum_le; last first.
    move => c Hin; rewrite -[d c]Rmult_1_r.
    have ->: d c * 1 * f i0 c = d c * f i0 c by rewrite Rmult_1_r.
    apply: Rmult_le_compat => //.
    { by case: (f_range i0 c). }
    { by apply: Rle_refl. }
    by case: (f_range i0 c).
  Qed.
  
  Section LAMBDA.
  Variable lambda : R.
  Variable lambda_gt0 : 0 < lambda.
  
  Lemma expValR_linear_approx : 
    exp (-lambda * mR * q) *
    big_product (enum 'I_m)
      (fun i => expValR d (fun x => exp (lambda * f i x))) <=
    exp (-lambda * mR * q) *
    big_product (enum 'I_m)
      (fun i => expValR d (fun x => 1 - f i x + f i x * exp lambda)).
  Proof.
    apply: Rmult_le_compat_l; first by left; apply: exp_pos.
    apply: big_product_le.
    { move => c Hin; apply: expValR_ge0; first by left; apply: exp_pos.
      by apply: d_nonneg. }
    { move => i Hin; apply: expValR_ge0 => x.
      { rewrite -[0]Rplus_0_l; apply: Rplus_le_compat.
        { case: (f_range i x) => _ Hleq; fourier. }
        case: (f_range i x) => H _; rewrite -[0](Rmult_0_r 0).
        apply: Rmult_le_compat; try solve[apply: Rle_refl|by []].
        left; apply: exp_pos. }
      by apply: d_nonneg. }
    move => c Hin; apply: big_sum_le => x Hinx; apply: Rmult_le_compat_l.
    { by apply: d_nonneg. }
    by apply: exp_upper_01.
  Qed.

  Lemma expValR_simpl i :
    expValR d (fun x => 1 - f i x + f i x * exp lambda) =
    1 - p + p * exp lambda.
  Proof.
    rewrite 2!expValR_linear/expValR => //.
    have ->: big_sum (enum T) (fun x => d x * 1)
           = big_sum (enum T) (fun x => d x).
    { by apply: big_sum_ext => // x; apply: Rmult_1_r. }
    have ->:
       big_sum (enum T) (fun x => d x * - f i x) =
      -big_sum (enum T) (fun x => d x * f i x).
    { rewrite -big_sum_nmul; apply: big_sum_ext => // x.
      by rewrite Ropp_mult_distr_r_reverse. }
    have ->:
       big_sum (enum T) (fun x => d x * (f i x * exp lambda)) =
       big_sum (enum T) (fun x => exp lambda * (d x * f i x)).
    { by apply big_sum_ext => // x; rewrite -Rmult_assoc Rmult_comm. }
    f_equal.
    { rewrite /p/expValR/Rminus; f_equal; f_equal => /=; rewrite /d_prod /=.
      apply: d_dist.
      apply: f_identically_distributed. }
    rewrite big_sum_scalar Rmult_comm; f_equal.
    rewrite /p/expValR/Rminus.
    move: f_identically_distributed; rewrite /identically_distributed.
    by move/(_ i i0); rewrite /expValR.
  Qed.    
  
  Lemma big_product_expValR_simpl_aux : 
    big_product
      (enum 'I_m)
      (fun i => expValR d (fun x => 1 - f i x + f i x * exp lambda)) =
    big_product (enum 'I_m) (fun i => 1 - p + p * exp lambda).
  Proof. by apply: big_product_ext => // p; rewrite expValR_simpl. Qed.
    
  Lemma big_product_expValR_simpl :
    big_product
      (enum 'I_m)
      (fun i => expValR d (fun x => 1 - f i x + f i x * exp lambda)) =
    (1 - p + p * exp lambda) ^ m.
  Proof. by rewrite big_product_expValR_simpl_aux big_product_constant size_enum_ord. Qed.  

  Definition phi := ln (exp (-lambda*q) * (1 - p + p * exp lambda)).

  Lemma one_minus_p_gt0 : p<>1 -> 0 < 1 - p.
  Proof.
    by move => p_neq1; move: p_leq1; case => H; try fourier.
  Qed.
  
  Lemma one_minus_p_etc_gt0 : 0 < 1 - p + p * exp lambda.
  Proof.
    case: (Req_dec p 1).
    { move => ->; move: (exp_pos lambda) => H; fourier. }
    move => p_neq1; move: (one_minus_p_gt0 p_neq1) => H.
    apply: Rplus_lt_le_0_compat => //.
    apply: Rmult_le_pos.
    { by apply: expValR_ge0 => x; case: (f_range i0 x). }
    left; apply: exp_pos.
  Qed.    
  
  Lemma phi_simpl :
    exp (phi * mR) = exp (-lambda * mR * q) * (1 - p + p * exp lambda) ^ m.
  Proof.
    rewrite /phi ln_mult; last first.
    { apply: one_minus_p_etc_gt0. }
    { apply: exp_pos. }
    rewrite ln_exp Rmult_plus_distr_r exp_plus; f_equal.
    { by rewrite Rmult_assoc [q * mR]Rmult_comm Rmult_assoc. }
    rewrite exp_mult exp_ln => //.
    apply: one_minus_p_etc_gt0. 
  Qed.

  (** The probability that phat is greater than or equal to q: *)
  Definition phat_ge_q : R := conv (fun _ => d) f q.
  
  Lemma probOfR_phat_q :
    phat_ge_q <=
    exp (-lambda * mR * q) *
    big_product (enum 'I_m)
      (fun i => expValR d (fun x => exp (lambda * f i x))).
  Proof.
    rewrite -expVal_independence /phat_ge_q /conv.
    have H: 0 < lambda * mR.
    { apply: Rmult_lt_0_compat => //; apply: mR_gt0. }
    rewrite (probOfR_q_exp _ _ _ H); apply: Rle_trans; [apply markovR_exp|].
    { apply: Rmult_lt_0_compat => //.
      rewrite /q/p; rewrite -(Rplus_0_r 0); apply: Rplus_le_lt_compat => //.
      apply: expValR_ge0 => //.
      by move => x; case: (f_range i0 x). }
    { move => x; rewrite -(Rmult_0_r 0); apply: Rmult_le_compat; try apply: Rle_refl.
      { by left. }
      apply: Rmult_le_pos.
      { rewrite -[/INR m]Rmult_1_l.
        apply: Rle_mult_inv_pos; try fourier.
        by apply: lt_0_INR; apply/ltP. }
      by apply: big_sum_ge0 => x0; case: (f_range x0 (x x0)). }
    { move => x; apply: prodR_nonneg => //. }
    have ->: -(lambda * mR * q) = -lambda * mR * q.
    { by rewrite 2!Ropp_mult_distr_l. }
    apply Rmult_le_compat_l; first by left; apply: exp_pos.
    apply: big_sum_le => c H2; apply: Rmult_le_compat_l.
    { apply: prodR_nonneg => //. }
    have ->:
      lambda * mR * (/mR * big_sum (enum 'I_m) (fun i => f i (c i)))
    = lambda * big_sum (enum 'I_m) (fun i => f i (c i)).
    { rewrite Rmult_assoc -[mR * _]Rmult_assoc Rinv_r; last first.
      { apply: mR_neq0. }
      rewrite Rmult_1_l //. }
    rewrite big_sum_mult_left -big_product_exp_sum; apply: Rle_refl.
  Qed.

  Lemma probOfR_phat_q_bound : 
    phat_ge_q <= 
    exp (-lambda * mR * q) *
    big_product (enum 'I_m)
      (fun i => expValR d (fun x => 1 - f i x + f i x * exp lambda)).
  Proof.
    apply: Rle_trans; first by apply: probOfR_phat_q.
    apply: expValR_linear_approx.
  Qed.
  
  Lemma chernoff0 : phat_ge_q <= exp (phi * mR).
  Proof.
    apply: Rle_trans; first by apply: probOfR_phat_q_bound.
    rewrite big_product_expValR_simpl phi_simpl; f_equal; apply: Rle_refl.
  Qed.
  End LAMBDA.  

  Lemma chernoff0_lambda_ge0 (lambda:R) (lambda_ge0 : 0 <= lambda) :
    phat_ge_q <= exp (phi lambda * mR).
  Proof.
    case: lambda_ge0; first by move => Hlt; apply: chernoff0.
    rewrite phi_simpl => <-; rewrite exp_0 Rmult_1_r.
    have ->: -0 * mR * q = 0 by lra.
    have ->: 1 - p + p = 1 by lra.
    rewrite exp_0 /phat_ge_q /conv; apply: Rle_trans.
    { apply: probOfR_le_1; [by apply: prodR_dist|by apply: prodR_nonneg]. }
    by rewrite pow1 Rmult_1_r; apply: Rle_refl.
  Qed.    
  
  Definition lambda_min := ln ((q * (1 - p)) / ((1 - q) * p)).

  Lemma lambda_min_gt0 : 0 < lambda_min.
  Proof.
    apply: exp_lt_inv; rewrite exp_0 /lambda_min.
    have Hlt: 1 < q * (1 - p) / ((1 - q) * p).
    { rewrite Rmult_minus_distr_l Rmult_1_r.
      rewrite [(1-q)*p]Rmult_comm Rmult_minus_distr_l Rmult_1_r.
      rewrite Rmult_comm /q; move: lt_p_p2_eps; move: (p*(p+eps)) => r H.
      apply: (Rmult_lt_reg_r (p-r)) => //.
      rewrite Rmult_1_l Rmult_assoc Rinv_l; last first.
      { move => H2; rewrite H2 in H; apply: (Rlt_irrefl _ H). }
      rewrite Rmult_1_r; apply: Rplus_lt_compat_r; fourier. }
    rewrite exp_ln => //.
    apply: Rlt_trans; last by apply: Hlt.
    fourier.
  Qed. 
  
  Lemma phi_lambda_min :
    phi lambda_min = -(RE_Bernoulli (p + eps) p).
  Proof.
    rewrite /phi/lambda_min RE_Bernoulli_def.
    have H1: 0 < 1 - p + p * exp (ln (q * (1 - p) / ((1 - q) * p))).
    { have H: 0 < 1 - p by fourier.
      apply: Rlt_le_trans; first by apply: H.
      rewrite -{1}[1-p]Rplus_0_r; apply: Rplus_le_compat_l.
      case: p_nontrivial => H1 H2; apply: Rmult_le_pos; [fourier|]. 
      by apply: Rlt_le; apply: exp_pos. }
    simpl; rewrite ln_mult; [|by apply: exp_pos|] => //.
    case: p_nontrivial => X1 X2.
    have H8: p <> 0.
    { lra. }
    have H6: q <> 0.
    { rewrite /q; lra. }
    have H10: / p <> 0.
    { by apply: Rinv_neq_0_compat. }
    have H7: 1 - p <> 0.
    { lra. }
    have H11: 1 - q <> 0.
    { rewrite /q; lra. }
    have H9: / (1 - q) <> 0.
    { by rewrite /q; apply: Rinv_neq_0_compat. }
    have H3: q * (1 - p) <> 0.
    { rewrite /q; apply: Rmult_integral_contrapositive; split; lra. }
    have H4: / ((1 - q) * p) <> 0.
    { rewrite /q; apply: Rinv_neq_0_compat; apply: Rmult_integral_contrapositive.
      split; lra. }
    have H5: (1 - q) * p <> 0.
    { rewrite /q; apply: Rmult_integral_contrapositive; split; lra. }
    have H12: / (1 - q) * / p <> 0.
    { apply: Rmult_integral_contrapositive; split; lra. }
    have H2: 0 < q * (1 - p) / ((1 - q) * p).
    { apply: Rmult_lt_0_compat.
      { rewrite /q; apply: Rmult_lt_0_compat; lra. }
      rewrite /q; apply: Rinv_0_lt_compat.
      apply: Rmult_lt_0_compat; lra. }
    rewrite ln_exp exp_ln -/q // -ln_Rinv //.
    have ->: / (q * (1 - p) / ((1 - q) * p)) = (p * (1 - q)) / (q * (1 - p)).
    { rewrite !Rinv_mult_distr // !Rinv_involutive // /Rdiv Rinv_mult_distr //.
      by rewrite [(p * _) * _]Rmult_comm [p * _]Rmult_comm. }
    rewrite [ln _ * q]Rmult_comm.
    have ->:
      1 - p + p * (q * (1 - p) / ((1 - q) * p)) =
      (1 - q) * (1 - p) / (1 - q) + q * (1 - p) / (1 - q).
    { have X: 1 - p = (1 - q) * (1 - p) / (1 - q).
      { rewrite /Rdiv [_ * /(1 - q)]Rmult_comm -Rmult_assoc -(Rinv_l_sym (1-q)) //.
        by rewrite Rmult_1_l. }
      rewrite {1}X; f_equal; rewrite /Rdiv [p * _]Rmult_comm Rinv_mult_distr //.
      rewrite Rmult_assoc [_ * /p * p]Rmult_assoc -(Rinv_l_sym p) // Rmult_1_r //. }
    have ->: (1 - q) * (1 - p) / (1 - q) + q * (1 - p) / (1 - q) = (1 - p) / (1 - q).
    { rewrite -Rdiv_plus_distr.
      have ->: (1 - q) * (1 - p) + q * (1 - p) = 1 - p.
      { have ->: (1 - q) * (1 - p) = 1 - p - q + p * q by lra.
        rewrite Rmult_minus_distr_l Rmult_1_r [q*p]Rmult_comm /Rminus.
        rewrite [_ + p*q]Rplus_comm -Rplus_assoc Rplus_comm.
        rewrite [p * q + _ + q]Rplus_assoc -[-_ + _]Rplus_assoc Rplus_opp_l Rplus_0_l.
        rewrite Rplus_assoc Rplus_opp_l Rplus_0_r //. }
      by []. }
    have H13: 0 < p * (1 - q) / (q * (1 - p)).
    { apply: Rmult_lt_0_compat.
      { apply: Rmult_lt_0_compat => //; rewrite /q; lra. }
      apply: Rinv_0_lt_compat; apply: Rmult_lt_0_compat; rewrite /q; lra. }
    have H14: 0 < (1 - p) / (1 - q).
    { apply: Rmult_lt_0_compat; rewrite /q; [lra|].
      apply: Rinv_0_lt_compat; lra. }
    have ->:
      q * ln (p * (1 - q) / (q * (1 - p))) + ln ((1 - p) / (1 - q)) =
      (q - 1) * ln (p * (1 - q) / (q * (1 - p))) +
      ln ( (p * (1 - q) / (q * (1 - p))) * ((1 - p) / (1 - q)) ).
    { rewrite ln_mult // -Rplus_assoc; f_equal; lra. }
    have H15: 0 < p / q.
    { apply: Rmult_lt_0_compat => //; apply Rinv_0_lt_compat; rewrite /q; lra. }
    have H16: 0 < (1 - q) / (1 - p).
    { apply: Rmult_lt_0_compat; rewrite /q; [lra|].
      apply: Rinv_0_lt_compat; lra. }
    have X3: p * (1 - q) / (q * (1 - p)) = (p / q) * ((1 - q) / (1 - p)).
    { rewrite /Rdiv [p * (1 - q) * _]Rmult_assoc [(1 - q) * _]Rmult_comm -Rmult_assoc.
      rewrite Rinv_mult_distr // -Rmult_assoc; lra. }    
    have ->: ln (p * (1 - q) / (q * (1 - p))) = ln (p / q) + ln ((1 - q) / (1 - p)).
    { rewrite X3 ln_mult //. }
    have ->: p * (1 - q) / (q * (1 - p)) * ((1 - p) / (1 - q)) = p / q.
    { rewrite X3 Rmult_assoc.
      set (A := ((_ / _) * (_ / _))); have ->: A = 1.
      { rewrite /A /Rdiv Rmult_assoc -[/_ * _]Rmult_assoc Rinv_l // Rmult_1_l Rinv_r //. }
      by rewrite Rmult_1_r. }
    have ->:
      (q - 1) * (ln (p / q) + ln ((1 - q) / (1 - p))) + ln (p / q) =
      q * ln (p / q) + (q - 1) * ln ((1 - q) / (1 - p)) by lra.
    rewrite -[q * _ + _ * _]Ropp_involutive Ropp_plus_distr; f_equal.
    rewrite Ropp_mult_distr_l.
    have ->: - q * ln (p / q) = q * - ln (p / q) by lra.
    rewrite -ln_Rinv //.
    have H18: / q <> 0.
    { by rewrite /q; apply: Rinv_neq_0_compat. }
    have ->: /(p / q) = q / p.
    { rewrite Rinv_mult_distr // Rinv_involutive // Rmult_comm //. }
    f_equal.
    rewrite Ropp_mult_distr_l Ropp_plus_distr Ropp_involutive Rplus_comm //.
  Qed.

  Lemma chernoff1 : phat_ge_q <= exp (-(RE (Bernoulli.t (p + eps)) (Bernoulli.t p)) * mR).
  Proof.
    rewrite -phi_lambda_min; apply: chernoff0.
    by apply: lambda_min_gt0.
  Qed. 

  Lemma chernoff_geq : phat_ge_q <= exp (-2%R * eps^2 * mR).
  Proof.
    apply: Rle_trans; first by apply: chernoff1.
    rewrite -3!Ropp_mult_distr_l !exp_Ropp; apply: Rinv_le_contravar.
    { apply: exp_pos. }
    have H: (RE_Bernoulli (p + eps) p >= 2%R * eps^2).
    { apply: RE_Bernoulli_bounded_below.
      case: p_nontrivial => H1 H2.
      split => //; apply: Rlt_le => //. lra. }
    case: H => H2.
    { left; apply: exp_increasing; simpl.
      rewrite -!Rmult_assoc; apply: (Rmult_lt_compat_r mR).
      { apply: mR_gt0. }
      apply: Rgt_lt.
      by rewrite /RE_Bernoulli/p_dist/q_dist/= -!Rmult_assoc in H2. }
    rewrite /RE_Bernoulli/p_dist/q_dist in H2; rewrite H2.
    apply: Rle_refl.
  Qed.
End chernoff_geq.

Section chernoff_leq.
  Variable T : finType.
  Variables d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.

  Notation d_prod := (@d_prod T d m).
  
  Variable f : 'I_m -> T -> R.
  Variable f_range : forall i x, 0 <= f i x <= 1.
  Variable f_identically_distributed : identically_distributed d f.
  Variable f_independent : mutual_independence d f.

  Definition f_neg (i : 'I_m) (t : T) := 1 - f i t.

  Lemma f_neg_range : forall i x, 0 <= f_neg i x <= 1.
  Proof. move => i x; case: (f_range i x) => H1 H2; split; rewrite /f_neg; fourier. Qed.
  Lemma f_neg_identically_distributed : identically_distributed d f_neg.
  Proof.
    move => i j; rewrite /f_neg; move: (f_identically_distributed i j) => H.
    rewrite 2!expValR_linear; f_equal.
    by rewrite 2!expValR_Ropp H.
  Qed.
  Lemma f_neg_independent : mutual_independence d f_neg.
  Proof. by move => g; rewrite (f_independent (fun x => g (1 - x))). Qed.

  Variable eps : R.
  Variable eps_gt0 : 0 < eps.
  Variable eps_lt_1p : eps < 1 - p d m_gt0 f_neg.
  Variable p_nontrivial : 0 < p d m_gt0 f < 1. 
  
  Definition p_neg := p d m_gt0 f_neg.

  Lemma p_neg_one_minus_p : p_neg = 1 - p d m_gt0 f.
  Proof.
    rewrite /p_neg /p /f_neg; rewrite expValR_linear expValR_Ropp /Rminus; f_equal.
    apply: expValR_one => //.
  Qed.    
  
  Lemma p_neg_nontrivial : 0 < p_neg < 1.
  Proof. rewrite p_neg_one_minus_p; case: p_nontrivial => H1 H2; split; fourier. Qed.
  
  Lemma chernoff_leq : phat_ge_q d m_gt0 f_neg eps <= exp (-2%R * eps^2 * mR m).
  Proof.
    apply: chernoff_geq => //.
    { apply: f_neg_range. }
    { apply: f_neg_identically_distributed. }
    { apply: f_neg_independent. }
    { apply: p_neg_nontrivial. }
  Qed.
End chernoff_leq.

Section chernoff_onesided.
  Variable T : finType.
  Variables d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.

  Notation d_prod := (@d_prod T d m).
  
  Variable f : 'I_m -> T -> R.
  Variable f_range : forall i x, 0 <= f i x <= 1.
  Variable f_identically_distributed : identically_distributed d f.
  Variable f_independent : mutual_independence d f.

  Variable eps : R.
  Variable eps_gt0 : 0 < eps.
  (*NOTE: the following assumptions are required to prove \lambda_min > 0*)  
  Variable eps_lt_1p : eps < 1 - p d m_gt0 f.
  Variable p_nontrivial : 0 < p d m_gt0 f < 1.
  (*END: the following assumptions*)    
  
  Lemma chernoff_aux1 :
    phat_ge_q d m_gt0 f eps <= exp (-2%R * eps^2 * mR m).
  Proof.
    apply: Rle_trans; [apply: chernoff_geq => //|].
    apply: Rle_refl.
  Qed.

  Definition p_hat x := / (mR m) * big_sum (enum 'I_m) (fun i => f i (x i)).
  Definition p_exp := p d m_gt0 f.
  
  Lemma chernoff :
    probOfR (prodR (fun _ => d)) (fun x => Rle_lt_dec (p_exp + eps) (p_hat x)) <=
    exp (-2%R * eps^2 * mR m).
  Proof.
    apply: Rle_trans; last by apply: chernoff_aux1.
    apply: Rle_refl.
  Qed.    
End chernoff_onesided.

Section chernoff_twosided.
  Variable T : finType.
  Variables d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.

  Notation d_prod := (@d_prod T d m).
  
  Variable f : 'I_m -> T -> R.
  Variable f_range : forall i x, 0 <= f i x <= 1.
  Variable f_identically_distributed : identically_distributed d f.
  Variable f_independent : mutual_independence d f.

  Variable eps delt : R.
  Variable eps_gt0 : 0 < eps.
  Variable delt_gt0 : 0 < delt.
  (*NOTE: the following assumptions are required to prove \lambda_min > 0*)
  Variable eps_lt_p : eps < p d m_gt0 f.  
  Variable delt_lt_1p : delt < 1 - p d m_gt0 f.
  Variable p_nontrivial : 0 < p d m_gt0 f < 1.
  (*END: the following assumptions*)  

  Definition min_eps_delt := Rmin eps delt.

  Lemma Rle_0_min_eps_delt : 0 <= min_eps_delt.
  Proof. by rewrite /min_eps_delt /Rmin; case: (Rle_dec _ _) => H; apply: Rlt_le. Qed.

  Lemma Rlt_min_eps_delt_delt : min_eps_delt <> delt -> min_eps_delt < delt.
  Proof. by rewrite /min_eps_delt /Rmin; case: (Rle_dec _ _); first by case. Qed.

  Lemma Rlt_min_eps_delt_eps : min_eps_delt <> eps -> min_eps_delt < eps.
  Proof.
    rewrite /min_eps_delt /Rmin; case: (Rle_dec _ _) => //.
    move/Rnot_le_gt => H1 H2; fourier.
  Qed.    
  
  Lemma Rle_exp_delt_min : exp (- (2) * delt ^ 2 * mR m) <= exp (- (2) * min_eps_delt ^ 2 * mR m).
  Proof.    
    rewrite !Ropp_mult_distr_l_reverse 2!exp_Ropp; apply: Rinv_le_contravar.
    { apply: exp_pos. }
    case: (Req_dec (exp (2 * min_eps_delt ^ 2 * mR m)) (exp (2 * delt ^ 2 * mR m))).
    { by move => ->; apply: Rle_refl. }
    move => Hneq; left; apply: exp_increasing; apply: Rmult_lt_compat_r; first by apply: mR_gt0.
    apply: Rmult_lt_compat_l; first by fourier.
    rewrite -!tech_pow_Rmult /= 2!Rmult_1_r; apply: Rmult_le_0_lt_compat.
    { apply: Rle_0_min_eps_delt. }
    { apply: Rle_0_min_eps_delt. }      
    { by apply: Rlt_min_eps_delt_delt => Heq; rewrite Heq in Hneq; apply: Hneq. }
    by apply: Rlt_min_eps_delt_delt => Heq; rewrite Heq in Hneq; apply: Hneq.
  Qed.    

  Lemma Rle_exp_eps_min : exp (- (2) * eps ^ 2 * mR m) <= exp (- (2) * min_eps_delt ^ 2 * mR m).
  Proof.    
    rewrite !Ropp_mult_distr_l_reverse 2!exp_Ropp; apply: Rinv_le_contravar.
    { apply: exp_pos. }
    case: (Req_dec (exp (2 * min_eps_delt ^ 2 * mR m)) (exp (2 * eps ^ 2 * mR m))).
    { by move => ->; apply: Rle_refl. }
    move => Hneq; left; apply: exp_increasing; apply: Rmult_lt_compat_r; first by apply: mR_gt0.
    apply: Rmult_lt_compat_l; first by fourier.
    rewrite -!tech_pow_Rmult /= 2!Rmult_1_r; apply: Rmult_le_0_lt_compat.
    { apply: Rle_0_min_eps_delt. }
    { apply: Rle_0_min_eps_delt. }      
    { by apply: Rlt_min_eps_delt_eps => Heq; rewrite Heq in Hneq; apply: Hneq. }
    by apply: Rlt_min_eps_delt_eps => Heq; rewrite Heq in Hneq; apply: Hneq.
  Qed.    
  
  Lemma chernoff_twosided_aux1 :
    phat_ge_q d m_gt0 f delt + phat_ge_q d m_gt0 (f_neg f) eps <=
    2 * exp (-2%R * min_eps_delt^2 * mR m).
  Proof.
    rewrite double; apply: Rplus_le_compat.
    { apply: Rle_trans; [apply: chernoff_geq => //|]; apply: Rle_exp_delt_min. }
    apply: Rle_trans; [apply: chernoff_leq => //|]; last first.
    { apply: Rle_exp_eps_min. }
    rewrite -p_neg_one_minus_p /p_neg => //.
    have ->: p d m_gt0 (f_neg (T:=T) (f_neg (T:=T) f)) = p d m_gt0 f.
    { rewrite /p/expValR; apply: big_sum_ext => // x; f_equal.
      by rewrite /f_neg /Rminus Ropp_minus_distr' Rplus_comm Rplus_assoc Rplus_opp_l Rplus_0_r. }
    by apply: eps_lt_p.
  Qed.

  (*This bound unifies epsilon=delta*)
  Lemma chernoff_twosided_aux2 (Heq : eps = delt) :
    phat_ge_q d m_gt0 f eps + phat_ge_q d m_gt0 (f_neg f) eps <=
    2 * exp (-2%R * eps^2 * mR m).
  Proof.
    have Heq2: eps = min_eps_delt.
    { rewrite /min_eps_delt/Rmin; subst delt; case: (Rle_dec _ _) => //. }
    rewrite {3}Heq2; apply: Rle_trans; last by apply: chernoff_twosided_aux1.
    by rewrite Heq; apply: Rle_refl.
  Qed.

  Notation p_exp := (p_exp d m_gt0 f).
  Notation p_hat := (p_hat f).
  
  Lemma chernoff_twosided (Heq : eps = delt) :
    probOfR (prodR (fun _ => d)) (fun x => Rle_lt_dec eps (Rabs (p_exp - p_hat x))) <=
    2 * exp (-2%R * eps^2 * mR m).
  Proof.
    apply: Rle_trans; last by apply: (chernoff_twosided_aux2 Heq).
    rewrite /phat_ge_q/conv/probOfR/q/= 3!big_sum_sumP; clear delt delt_gt0 delt_lt_1p Heq.
    rewrite big_mkcond.
    set (b1 := \big[bigops.Rplus/0]_(i | Rle_lt_dec _ _) _).
    set (b2 := \big[bigops.Rplus/0]_(i | Rle_lt_dec _ _) _).
    have ->: b1 = \big[bigops.Rplus/0]_(i:{ffun 'I_m->T})
       (if is_left (Rle_lt_dec (p (T:=T) d m_gt0 f + eps)
                               (/ INR m * big_sum (enum 'I_m) (fun i1 : 'I_m => f i1 (i i1))))
        then prodR (T:=T) (fun _ : 'I_m => d) i else 0).
    { by rewrite /b1 big_mkcond. }
    have ->: b2 = \big[bigops.Rplus/0]_(i:{ffun 'I_m->T})
       (if is_left (Rle_lt_dec (p (T:=T) d m_gt0 (f_neg (T:=T) f) + eps)
                               (/ INR m * big_sum (enum 'I_m) (fun i1 : 'I_m => f_neg (T:=T) f i1 (i i1))))
        then prodR (T:=T) (fun _ : 'I_m => d) i else 0).
    { by rewrite /b2 big_mkcond. }
    clear b1 b2.
    set (b1 := \big[bigops.Rplus/0]_i (if _ then _ else _)).
    set (b2 := \big[bigops.Rplus/0]_i (if _ then _ else _)).
    set (b3 := \big[bigops.Rplus/0]_i (if _ then _ else _)).
    have ->: b2 + b3 = bigops.Rplus b2 b3 by [].
    rewrite /b2 /b3 -big_split /b1 -!big_sum_sumP; apply: big_sum_le => x /= Hin.
    set (dP := prodR _); case: (Rle_lt_dec _ _) => Hle /=; last first.
    { apply: Rplus_le_le_0_compat.
      { case: (is_left _); [by apply: prodR_nonneg |fourier]. }
      case: (is_left _); [by apply: prodR_nonneg |fourier]. }
    (*have: eps <= |p-p_hat|*)
    case: (Rle_lt_dec p_exp (p_hat x)); last first => Hle2.
    { (*Case 1: p_hat < p*)
      have Hle3: eps <= p_exp - p_hat x.
      { move: Hle; rewrite Rabs_minus_sym /Rabs; case: (Rcase_abs _) => //= Hx Hy; fourier. }
      have Hle4: p_hat x + eps <= p_exp by fourier.
      case: (Rle_lt_dec (p _ _ f + _) _) => Hle5 /=.
      { rewrite -{1}[dP x]Rplus_0_l; apply: Rplus_le_compat; first by apply: prodR_nonneg.
        case: (Rle_lt_dec _ _) => /= y; [fourier|].
        exfalso; rewrite /p_hat/mR/p_exp in Hle4; move: Hle4 Hle5.
        move: (p _ _ _) => X; move: (/_ * _) => Y => H1 H2; fourier. }
      rewrite Rplus_0_l; case: (Rle_lt_dec (_ + _)) => /= Hle6; first by apply: Rle_refl.
      have Hle7:
        / INR m * big_sum (enum 'I_m) (fun i1 : 'I_m => f_neg (T:=T) f i1 (x i1)) <
        p_neg (T:=T) d m_gt0 f + eps.
      { apply: Hle6. } clear Hle6.
      exfalso; rewrite p_neg_one_minus_p in Hle7 => //.
      have H8: p_hat x < p (T:=T) d m_gt0 f + eps by []. clear Hle5.
      have H9: 1 - p_hat x < 1 - p (T:=T) d m_gt0 f + eps.
      { apply: Rle_lt_trans; last by apply: Hle7.
        rewrite /p_hat /f_neg big_sum_plus big_sum_nmul big_sum_constant size_enum_ord.
        rewrite Rmult_1_r Rmult_plus_distr_l Rinv_l; last first.
        { move => Heq; move: (mR_gt0 m_gt0); rewrite /mR Heq => Hlt; fourier. }
        rewrite -Ropp_mult_distr_r; apply: Rle_refl. }
      have H10: eps > p_exp - p_hat x. 
      { clear - H8 H9; move: H8 H9; rewrite /p_exp; move: (p _ _) => p_exp => H1 H2.
        fourier. }
      fourier. }
    (*Case 2: p_hat >= p*)
    { have Hle3: eps <= p_hat x - p_exp.
      { move: Hle; rewrite Rabs_minus_sym /Rabs; case: (Rcase_abs _) => //= Hx Hy; fourier. }
      have Hle4: p_exp + eps <= p_hat x by fourier.
      case: (Rle_lt_dec (p _ _ f + _) _) => Hle5 /=.
      { rewrite -{1}[dP x]Rplus_0_r; apply: Rplus_le_compat_l.
        case: (Rle_lt_dec _ _) => /= y; [|fourier].
          by apply: prodR_nonneg. }
      exfalso; rewrite /p_hat/mR/p_exp in Hle4; move: Hle4 Hle5.
      move: (p _ _ _) => X; move: (/_ * _) => Y => H1 H2; fourier. }
  Qed.
End chernoff_twosided.

