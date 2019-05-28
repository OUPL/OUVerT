Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.
Require Import QArith Reals Rpower Ranalysis Fourier Lra.

Require Import bigops numerics expfacts dist chernoff.

Section learning.
  Variables A B : finType.

  Variable d : A*B -> R.
  Variable d_dist : big_sum (enum [finType of A*B]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable m : nat. (*The number of training samples*)
  Variable m_gt0 : (0 < m)%nat.  
  Notation mR := (INR m).
  Definition i0 : 'I_m := Ordinal m_gt0.  

  (** Training sets *)
  Definition training_set : finType := [finType of {ffun 'I_m -> [finType of A*B]}].

  Section error_RV.
    Variable Hyp : finType.    
    (** The (hypothesis-indexed) set of random variables being evaluated *)
    Variable X : Hyp -> 'I_m -> A*B -> R.
    Variable X_range : forall h i x, 0 <= X h i x <= 1.
    
    (** The empirical average of h on T *)
    Definition empVal (T : training_set) (h : Hyp) := 
      (big_sum (enum 'I_m) (fun i => X h i (T i))) / mR.

    (** The expected value in D of X h *)
    Definition expVal (h : Hyp) := expValR d (X h i0).
    Variable expVal_nontrivial : forall h : Hyp, 0 < expVal h < 1.

    Lemma chernoff_bound_h
        (h : Hyp)
        (Hid : identically_distributed d (X h))        
        (eps : R) (eps_gt0 : 0 < eps) (Hyp_eps : eps < 1 - expVal h) :
    probOfR
      (prodR (fun _ : 'I_m => d))
      [pred T : training_set | Rle_lt_dec (expVal h + eps) (empVal T h)] <=
    exp (-2%R * eps^2 * mR).
    Proof.
      have ->: expVal h = p_exp d m_gt0 (X h) by [].
      set (P := probOfR _ _).
      have ->: P =
        probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
         (prodR (T:=prod_finType A B) (fun _ : 'I_m => d))
         (fun T => Rle_lt_dec (p_exp (T:=prod_finType A B) d m_gt0 (X h) + eps) (p_hat (X h) T)).
      { rewrite /probOfR; apply: big_sum_ext => //=; apply eq_in_filter => /= T Hin.
        have ->: empVal T h = p_hat (X h) T by rewrite /p_hat/empVal Rmult_comm.
        by []. }
      apply: chernoff => //; by case: (expVal_nontrivial h).
    Qed.      

    Definition eps_Hyp (eps : R) : finType := 
      [finType of {h : Hyp | Rlt_le_dec eps (1 - expVal h)}].

    Variable identical : forall h : Hyp, identically_distributed d (X h).

    Lemma chernoff_bound1 (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d))
              [pred T:training_set
              | [exists i : 'I_#|eps_Hyp eps|,
                 let: h := projT1 (enum_val i)
                 in Rle_lt_dec (expVal h + eps) (empVal T h)]]
      <= INR #|eps_Hyp eps| * exp (-2%R * eps^2 * mR).
    Proof.
      set (P := fun i:'I_#|eps_Hyp eps| => 
                  [pred T : training_set |
                   let: h := projT1 (enum_val i)
                   in Rle_lt_dec (expVal h + eps) (empVal T h)]).
      change (probOfR (prodR (fun _ => d))
                      [pred T:training_set | [exists i : 'I_#|eps_Hyp eps|, P i T]] 
              <= INR #|eps_Hyp eps| * exp (-2%R * eps^2 * mR)).
      apply: Rle_trans; [apply: union_bound|].
      { by apply: prodR_nonneg. }
      have Hle:
        \big[Rplus/0]_(i in 'I_#|eps_Hyp eps|)
         probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
         (prodR (T:=prod_finType A B) (fun _ : 'I_m => d)) [eta P i]
        <= \big[Rplus/0]_(i in 'I_#|eps_Hyp eps|) (exp (-2%R * eps^2 * mR)).
      { rewrite -2!big_sum_sumP; apply big_sum_le => c Hin.
        apply chernoff_bound_h => //; case: (enum_val c) => //= => x p.
        case: (Rlt_le_dec eps (1 - expVal x)) p => //. }
      apply: Rle_trans; first by apply: Hle.
      rewrite big_const card_ord; elim: #|eps_Hyp eps|.
      { rewrite !Rmult_0_l; apply: Rle_refl. }
      move => n H; rewrite iterS.
      have ->:
        INR n.+1 * exp (- (2) * eps ^ 2 * mR) 
      = (exp (- (2) * eps ^ 2 * mR)) + INR n * exp (- (2) * eps ^ 2 * mR).
      { by rewrite S_INR Rmult_assoc Rmult_plus_distr_r Rmult_1_l Rplus_comm. }
      apply: Rplus_le_compat_l => //.
    Qed.

    Lemma chernoff_bound2 (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d))
              [pred T:training_set
              | [exists h : eps_Hyp eps,
                 Rle_lt_dec (expVal (sval h) + eps) (empVal T (sval h))]]
      <= INR #|eps_Hyp eps| * exp (-2%R * eps^2 * mR).
    Proof.
      apply: Rle_trans; last by apply: chernoff_bound1.
      apply: probOfR_le; first by apply: prodR_nonneg.
      move => j /=; case/existsP => h H.
      by apply/existsP; exists (enum_rank h); rewrite enum_rankK.
    Qed.
    
    Lemma empVal_le1 T h : empVal T h <= 1.
    Proof.
      rewrite /empVal; set (f := big_sum _ _).
      have H: f <= mR.
      { have H1: f <= big_sum (enum 'I_m) (fun _ => 1).
        { rewrite /f; apply: big_sum_le => /= i _.
          by case: (X_range h i (T i)). }
        apply: Rle_trans; first by apply: H1.
        rewrite big_sum_constant Rmult_1_r; apply: le_INR.
        rewrite size_enum_ord; apply/leP => //. }
      have H1: f / mR <= mR / mR.
      { rewrite /Rdiv; apply: Rmult_le_compat_r => //.
        rewrite -[/mR]Rmult_1_l; apply: Rle_mult_inv_pos.
        fourier.
        have ->: 0 = INR 0 by [].
        apply: lt_INR; apply/ltP => //. }
      apply: Rle_trans; first by apply: H1.
      rewrite /Rdiv Rinv_r; first by apply: Rle_refl.
      apply: not_0_INR => Heq; move: m_gt0; rewrite Heq //.
    Qed.
    
    Lemma chernoff_bound3
          (learn : training_set -> Hyp) (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d))
        [pred T:training_set | 
         let: h := learn T in 
         Rlt_le_dec (expVal h + eps) (empVal T h)]
      <= INR #|eps_Hyp eps| * exp (-2%R * eps^2 * mR).
    Proof.
      apply: Rle_trans; last by apply: chernoff_bound2.
      apply: probOfR_le; first by apply: prodR_nonneg.
      move => T /= H; apply/existsP.
      rewrite /eps_Hyp.
      have X1: expVal (learn T) + eps < empVal T (learn T).
      { move: H.
        case: (Rlt_le_dec (expVal (learn T) + eps) (empVal T (learn T))) => //. }
      move: (empVal_le1 T (learn T)) => X2.
      have X3: eps < 1 - expVal (learn T) by fourier.
      have X4: Rlt_le_dec eps (1 - expVal (learn T)).
      { case: (Rlt_le_dec eps (1 - expVal (learn T))) => //.
        move => b; fourier. }
      exists (exist _ (learn T) X4) => /=.
      case: (Rle_lt_dec (expVal (learn T) + eps) (empVal T (learn T))) => //.
      move => b; fourier.
    Qed.
      
    Lemma eps_Hyp_card eps : (#|eps_Hyp eps| <= #|Hyp|)%nat.
    Proof.
      rewrite /eps_Hyp /= card_sig; apply: leq_trans; first by apply: subset_leq_card.
      by rewrite cardsT.
    Qed.    

    Lemma chernoff_bound
          (learn : training_set -> Hyp) (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d))
        [pred T:training_set | 
         let: h := learn T in 
         Rlt_le_dec (expVal h + eps) (empVal T h)]
      <= INR #|Hyp| * exp (-2%R * eps^2 * mR).
    Proof.
      apply: Rle_trans; first by apply: chernoff_bound3.
      apply Rmult_le_compat_r; first by apply: Rlt_le; apply: exp_pos.
      apply: le_INR; apply/leP; apply: eps_Hyp_card.
    Qed.      
    
    Lemma chernoff_bound_holdout
          (h : Hyp) (eps : R) (eps_gt0 : 0 < eps) (eps_lt : eps < 1 - expVal h) :
      probOfR (prodR (fun _ : 'I_m => d))
        [pred T:training_set | 
         Rlt_le_dec (expVal h + eps) (empVal T h)]
      <= exp (-2%R * eps^2 * mR).
    Proof.
      apply: Rle_trans; last by apply: (@chernoff_bound_h h _ eps _ _).
      apply: probOfR_le.
      { move => x; apply: prodR_nonneg => _ y; apply: d_nonneg. }
      move => x /=; case: (Rlt_le_dec _ _) => // H1 _.
      case: (Rle_lt_dec _ _) => // H2; fourier. 
    Qed.      

    Definition eps_Hyp_condition_twosided (eps : R) :=
      [pred h : Hyp | Rlt_le_dec eps (Rmin (expVal h) (1 - expVal h))].
    
    Lemma chernoff_twosided_bound_h
        (h : Hyp)
        (Hid : identically_distributed d (X h))        
        (eps : R) (eps_gt0 : 0 < eps) (Hyp_eps : eps_Hyp_condition_twosided eps h) :
    probOfR
      (prodR (fun _ : 'I_m => d))
      [pred T : training_set | Rle_lt_dec eps (Rabs (expVal h - empVal T h))] <=
    2 * exp (-2%R * eps^2 * mR).
    Proof.
      have eps_range : eps < Rmin (expVal h) (1 - expVal h).
      { rewrite /eps_Hyp_condition_twosided /= in Hyp_eps.
        move: Hyp_eps; case: (Rlt_le_dec _ _) => //. }
      have eps_range1 : eps < 1 - expVal h.
      { apply: Rlt_le_trans; [by apply: eps_range|by apply: Rmin_r]. }
      have eps_range2 : eps < expVal h.
      { apply: Rlt_le_trans; [by apply: eps_range|by apply: Rmin_l]. }    
      have H1: expVal h = p_exp d m_gt0 (X h) by [].
      have H2:
        probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
                (prodR (T:=prod_finType A B) (fun _ : 'I_m => d))
                (fun T : training_set =>
                   Rle_lt_dec eps (Rabs (p_exp (T:=prod_finType A B) d m_gt0 (X h) - empVal T h))) = 
        probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
                (prodR (T:=prod_finType A B) (fun _ : 'I_m => d))
                (fun T => Rle_lt_dec eps (Rabs (p_exp (T:=prod_finType A B) d m_gt0 (X h) - p_hat (X h) T))).
      { rewrite /probOfR; apply: big_sum_ext => //=; apply eq_in_filter => T Hin.
        have ->: empVal T h = p_hat (X h) T.
        { rewrite /p_hat /empVal; rewrite Rmult_comm //. }
      by []. }
      rewrite H1 H2.
      apply: chernoff_twosided => //; try fourier.
      { move: H1; rewrite /p_exp => <- //. }
      move: H1; rewrite /p_exp => <- //.
    Qed.

    Definition eps_Hyp_twosided (eps : R) : finType := 
      [finType of {h : Hyp | eps_Hyp_condition_twosided eps h}].

    Lemma eps_Hyp_twosided_inhabited :
      forall h : Hyp,
      exists eps, 0 < eps /\ eps_Hyp_condition_twosided eps h.
    Proof.
      move => h; rewrite /eps_Hyp_condition_twosided.
      exists ((Rmin (expVal h) (1 - expVal h))/2); split.
      { apply: Rlt_mult_inv_pos; [|fourier].
        case: (expVal_nontrivial h) => H1 H2.
        apply: Rmin_glb_lt => //; fourier. }
      rewrite /= /is_true; case Hlt: (Rlt_le_dec _ _) => // [H].
      move {Hlt}; move: H; set (Z := Rmin _ _) => H; elimtype False.
      have H1: Z / 2 < Z.
      { rewrite /Rdiv -{2}[Z]Rmult_1_r; apply: Rmult_lt_compat_l.
        { rewrite /Z; apply: Rmin_pos; first by case: (expVal_nontrivial h).
          case: (expVal_nontrivial h) => H1 H2; fourier. }
        fourier. }
      apply: (RIneq.Rle_not_lt _ _ H H1).
    Qed.    
    
    Lemma chernoff_twosided_bound_eps_Hyp (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d))
              [pred T:training_set
              | [exists i : 'I_#|eps_Hyp_twosided eps|,
                 let: h := projT1 (enum_val i)
                 in Rle_lt_dec eps (Rabs (expVal h - empVal T h))]]
      <= 2 * INR #|eps_Hyp_twosided eps| * exp (-2%R * eps^2 * mR).
    Proof.
      set (P := fun i:'I_#|eps_Hyp_twosided eps| => 
                  [pred T : training_set |
                   let: h := projT1 (enum_val i)
                   in Rle_lt_dec eps (Rabs (expVal h - empVal T h))]).
      change (probOfR (prodR (fun _ => d))
                      [pred T:training_set | [exists i : 'I_#|eps_Hyp_twosided eps|, P i T]] 
              <= 2 * INR #|eps_Hyp_twosided eps| * exp (-2%R * eps^2 * mR)).
      apply: Rle_trans; [apply: union_bound|].
      { by apply: prodR_nonneg. }
      rewrite [2 * _]Rmult_comm.
      have Hle:
        \big[Rplus/0]_(i in 'I_#|eps_Hyp_twosided eps|)
         probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
         (prodR (T:=prod_finType A B) (fun _ : 'I_m => d)) [eta P i]
        <= \big[Rplus/0]_(i in 'I_#|eps_Hyp_twosided eps|) (2 * exp (-2%R * eps^2 * mR)).
      { rewrite -2!big_sum_sumP; apply big_sum_le => c Hin.
        apply chernoff_twosided_bound_h => //.
        case: (enum_val c) => //. }
      apply: Rle_trans; first by apply: Hle.
      rewrite big_const card_ord; elim: #|eps_Hyp_twosided eps|.
      { rewrite !Rmult_0_l; apply: Rle_refl. }
      move => n H; rewrite iterS.
      have ->:
        INR n.+1 * 2 * exp (- (2) * eps ^ 2 * mR) 
      = (2 * exp (- (2) * eps ^ 2 * mR)) + INR n * 2 * exp (- (2) * eps ^ 2 * mR).
      { rewrite S_INR Rmult_assoc Rmult_plus_distr_r Rmult_1_l Rplus_comm; f_equal.
          by rewrite -Rmult_assoc. }
      apply: Rplus_le_compat_l => //.
    Qed.

    Lemma eps_Hyp_twosided_card eps : (#|eps_Hyp_twosided eps| <= #|Hyp|)%nat.
    Proof.
      rewrite /eps_Hyp_twosided /= card_sig; apply: leq_trans; first by apply: subset_leq_card.
      by rewrite cardsT.
    Qed.    
    
    Lemma chernoff_twosided_bound1 (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d))
              [pred T:training_set
              | [exists i : 'I_#|eps_Hyp_twosided eps|,
                 let: h := projT1 (enum_val i)
                 in Rle_lt_dec eps (Rabs (expVal h - empVal T h))]]
      <= 2 * INR #|Hyp| * exp (-2%R * eps^2 * mR).
    Proof.
      apply: Rle_trans; first by apply: chernoff_twosided_bound_eps_Hyp.
      apply: Rmult_le_compat_r; first by apply: Rlt_le; apply: exp_pos.
      apply: Rmult_le_compat_l; first by fourier.
      apply: le_INR; apply/leP; apply: eps_Hyp_twosided_card.
    Qed.

    Lemma chernoff_twosided_bound2 (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d))
              [pred T:training_set
              | [exists h : eps_Hyp_twosided eps,
                 Rle_lt_dec eps (Rabs (expVal (projT1 h) - empVal T (projT1 h)))]]
      <= 2 * INR #|Hyp| * exp (-2%R * eps^2 * mR).
    Proof.
      apply: Rle_trans; last by apply: chernoff_twosided_bound1.
      apply: probOfR_le; first by apply: prodR_nonneg.
      move => j /=; case/existsP => h H.
      by apply/existsP; exists (enum_rank h); rewrite enum_rankK.
    Qed.
  End error_RV.

  Section zero_one_accuracy.
    Variable Params : finType. (*the type of parameters*)
    Variable predict : Params -> A -> B. (*the prediction function*)

    Definition accuracy01 (p : Params) (i : 'I_m) (xy : A*B) : R :=
      let: (x,y) := xy in if predict p x == y then 1%R else 0%R.    
    Definition loss01 (p : Params) (i : 'I_m) (xy : A*B) : R :=
      1 - accuracy01 p i xy.

    (*For any function from training_set to Params, assuming joint independence
      and that the target class isn't perfectly representable:*)
    Variable learn : training_set -> Params.
    Variable not_perfectly_learnable : forall p : Params, 0 < expVal accuracy01 p < 1.

    (*we get the the following result for any eps: the probability that 
      the expected accuracy of h is more than eps lower than the empirical 
      accuracy of h on T is less than |Params| * exp(-2eps*m), 
      where m is the number of training examples in T.*)
    Lemma chernoff_bound_accuracy01 (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d)) 
              [pred T:training_set
              | let: h := learn T in 
                Rlt_le_dec (expVal accuracy01 h + eps) (empVal accuracy01 T h)]
      <= INR #|Params| * exp (-2%R * eps^2 * mR).
    Proof.
      apply chernoff_bound => // p i x; rewrite /accuracy01; case: x => a b.
      case: (predict p a == b)%B; split; fourier. 
    Qed.

    (*Here's the holdout version of the above lemma (the additional condition 
      on epsilon appears to fall out -- cf. Mulzer's tutorial on Chernoff bound proofs).*)
    Lemma chernoff_bound_accuracy01_holdout
          (h : Params) (eps : R) (eps_gt0 : 0 < eps) (eps_lt : eps < 1 - expVal accuracy01 h) :
      probOfR (prodR (fun _ : 'I_m => d)) 
              [pred T:training_set
              | Rlt_le_dec (expVal accuracy01 h + eps) (empVal accuracy01 T h)]
      <= exp (-2%R * eps^2 * mR).
    Proof.
      apply: Rle_trans; last first.
      { apply: chernoff_bound_holdout => //; last by apply: eps_lt.
        move => hx i x; rewrite /accuracy01; case: x => a b.
        case: (predict _ _ == _)%B; split; fourier. }
      apply: Rle_refl.
    Qed.      
  End zero_one_accuracy.
End learning.


  