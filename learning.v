Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import FunctionalExtensionality.

Import GRing.Theory Num.Def Num.Theory.
Require Import QArith Reals Rpower Ranalysis Fourier.

Require Import bigops numerics expfacts dist chernoff.

Section learning.
  Variables A B : finType.
  Variable rty : numDomainType.

  Definition Hyp : finType := [finType of {ffun A -> B}].

  Variable d : A*B -> R.
  Variable d_dist : big_sum (enum [finType of A*B]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable m : nat. (*The number of training samples*)
  Variable m_gt0 : (0 < m)%nat.  
  Notation mR := (INR m).
  Definition i0 : 'I_m := Ordinal m_gt0.  

  (** Training sets *)
  Definition training_set := [finType of {ffun 'I_m -> [finType of A*B]}].

  Section error_RV.
    (** The (hypothesis-indexed) set random variables being evaluated *)
    Variable X : Hyp -> 'I_m -> A*B -> R.
    Variable X_range : forall h i x, 0 <= X h i x <= 1.
    
    (** The empirical error of h on T *)
    Definition empErr (T : training_set) (h : Hyp) :=
      (big_sum (enum 'I_m) (fun i => X h i (T i))) / mR.

    (** The expected error of h on D *)
    Definition expErr (h : Hyp) := expValR d (X h i0).
    Variable expErr_nontrivial : forall h : Hyp, 0 < expErr h < 1.
    
    Definition Hyp_eps_condition (eps : R) :=
      [pred h : Hyp | Rlt_le_dec eps (Rmin (expErr h) (1 - expErr h))].
    
    Lemma chernoff_bound_h
        (h : Hyp)
        (Hind : mutual_independence (T:=prod_finType A B) d (X h))
        (Hid : identically_distributed d (X h))        
        (eps : R) (eps_gt0 : 0 < eps) (Hyp_eps : Hyp_eps_condition eps h) :
    probOfR
      (prodR (fun _ : 'I_m => d))
      [pred T : training_set | Rle_lt_dec eps (Rabs (expErr h - empErr T h))] <=
    2 * exp (-2%R * eps^2 * mR).
    Proof.
      have eps_range : eps < Rmin (expErr h) (1 - expErr h).
      { rewrite /Hyp_eps_condition /= in Hyp_eps.
        move: Hyp_eps; case: (Rlt_le_dec _ _) => //. }
      have eps_range1 : eps < 1 - expErr h.
      { apply: Rlt_le_trans; [by apply: eps_range|by apply: Rmin_r]. }
      have eps_range2 : eps < expErr h.
      { apply: Rlt_le_trans; [by apply: eps_range|by apply: Rmin_l]. }    
      have H1: expErr h = p_exp d m_gt0 (X h) by [].
      have H2:
        probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
                (prodR (T:=prod_finType A B) (fun _ : 'I_m => d))
                (fun T : training_set =>
                   Rle_lt_dec eps (Rabs (p_exp (T:=prod_finType A B) d m_gt0 (X h) - empErr T h))) = 
        probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
                (prodR (T:=prod_finType A B) (fun _ : 'I_m => d))
                (fun T => Rle_lt_dec eps (Rabs (p_exp (T:=prod_finType A B) d m_gt0 (X h) - p_hat (X h) T))).
      { rewrite /probOfR; apply: big_sum_ext => //=; apply eq_in_filter => T Hin.
        have ->: empErr T h = p_hat (X h) T.
        { rewrite /p_hat /empErr; rewrite Rmult_comm //. }
      by []. }
      rewrite H1 H2.
      apply: chernoff => //; try fourier.
      { move: H1; rewrite /p_exp => <- //. }
      move: H1; rewrite /p_exp => <- //.
    Qed.

    Definition eps_Hyp (eps : R) : finType := 
      [finType of {h : Hyp | Hyp_eps_condition eps h}].

    Lemma eps_Hyp_inhabited :
      forall h : Hyp,
      exists eps, 0 < eps /\ Hyp_eps_condition eps h.
    Proof.
      move => h; rewrite /Hyp_eps_condition.
      exists ((Rmin (expErr h) (1 - expErr h))/2); split.
      { apply: Rlt_mult_inv_pos; [|fourier].
        case: (expErr_nontrivial h) => H1 H2.
        apply: Rmin_glb_lt => //; fourier. }
      rewrite /= /is_true; case Hlt: (Rlt_le_dec _ _) => // [H].
      move {Hlt}; move: H; set (Z := Rmin _ _) => H; elimtype False.
      have H1: Z / 2 < Z.
      { rewrite /Rdiv -{2}[Z]Rmult_1_r; apply: Rmult_lt_compat_l.
        { rewrite /Z; apply: Rmin_pos; first by case: (expErr_nontrivial h).
          case: (expErr_nontrivial h) => H1 H2; fourier. }
        fourier. }
      apply: (RIneq.Rle_not_lt _ _ H H1).
    Qed.    
    
    Lemma eps_Hyp_card eps : (#|eps_Hyp eps| <= #|Hyp|)%nat.
    Proof.
      rewrite /eps_Hyp /= card_sig; apply: leq_trans; first by apply: subset_leq_card.
      by rewrite cardsT.
    Qed.    

    (** assume X_i are iid *)
    Variable identical : forall h : Hyp, identically_distributed d (X h).
    Variable independent : forall h : Hyp, mutual_independence d (X h).
    
    Lemma chernoff_bound_eps_Hyp (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d))
              [pred T:training_set
              | [exists i : 'I_#|eps_Hyp eps|,
                 let: h := projT1 (enum_val i)
                 in Rle_lt_dec eps (Rabs (expErr h - empErr T h))]]
      <= 2 * INR #|eps_Hyp eps| * exp (-2%R * eps^2 * mR).
    Proof.
      set (P := fun i:'I_#|eps_Hyp eps| => 
                  [pred T : training_set |
                   let: h := projT1 (enum_val i)
                   in Rle_lt_dec eps (Rabs (expErr h - empErr T h))]).
      change (probOfR (prodR (fun _ => d))
                      [pred T:training_set | [exists i : 'I_#|eps_Hyp eps|, P i T]] 
              <= 2 * INR #|eps_Hyp eps| * exp (-2%R * eps^2 * mR)).
      apply: Rle_trans; [apply: union_bound|].
      { by apply: prodR_nonneg. }
      rewrite [2 * _]Rmult_comm.
      have Hle:
        \big[Rplus/0]_(i in 'I_#|eps_Hyp eps|)
         probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
         (prodR (T:=prod_finType A B) (fun _ : 'I_m => d)) [eta P i]
        <= \big[Rplus/0]_(i in 'I_#|eps_Hyp eps|) (2 * exp (-2%R * eps^2 * mR)).
      { rewrite -2!big_sum_sumP; apply big_sum_le => c Hin.
        apply chernoff_bound_h => //.
        case: (enum_val c) => //. }
      apply: Rle_trans; first by apply: Hle.
      rewrite big_const card_ord; elim: #|eps_Hyp eps|.
      { rewrite !Rmult_0_l; apply: Rle_refl. }
      move => n H; rewrite iterS.
      have ->:
        INR n.+1 * 2 * exp (- (2) * eps ^ 2 * mR) 
      = (2 * exp (- (2) * eps ^ 2 * mR)) + INR n * 2 * exp (- (2) * eps ^ 2 * mR).
      { rewrite S_INR Rmult_assoc Rmult_plus_distr_r Rmult_1_l Rplus_comm; f_equal.
          by rewrite -Rmult_assoc. }
      apply: Rplus_le_compat_l => //.
    Qed.

    Lemma chernoff_bound (eps : R) (eps_gt0 : 0 < eps) :
      probOfR (prodR (fun _ : 'I_m => d))
              [pred T:training_set
              | [exists i : 'I_#|eps_Hyp eps|,
                 let: h := projT1 (enum_val i)
                 in Rle_lt_dec eps (Rabs (expErr h - empErr T h))]]
      <= 2 * INR #|Hyp| * exp (-2%R * eps^2 * mR).
    Proof.
      apply: Rle_trans; first by apply: chernoff_bound_eps_Hyp.
      apply: Rmult_le_compat_r; first by apply: Rlt_le; apply: exp_pos.
      apply: Rmult_le_compat_l; first by fourier.
      apply: le_INR; apply/leP; apply: eps_Hyp_card.
    Qed.
  End error_RV.

  Section zero_one_loss.
    Definition loss01 (h : Hyp) (i : 'I_m) (xy : A*B) : R :=
      let: (x,y) := xy in if h x == y then 0%R else 1%R.

      Lemma chernoff_bound_loss01
        (eps : R) (eps_gt0 : 0 < eps)
        (not_perfectly_learnable : forall h : Hyp, 0 < expErr loss01 h < 1)
        (ind : forall h : Hyp, mutual_independence d (loss01 h)) :
      probOfR (prodR (fun _ : 'I_m => d))
              [pred T:training_set
              | [exists i : 'I_#|eps_Hyp loss01 eps|,
                 let: h := projT1 (enum_val i)
                 in Rle_lt_dec eps (Rabs (expErr loss01 h - empErr loss01 T h))]]
      <= 2 * INR #|Hyp| * exp (-2%R * eps^2 * mR).
    Proof.
      apply: chernoff_bound => //.
      move => h i x; rewrite /loss01; case: x => a b.
      case: (h a == b)%B; split; fourier. 
    Qed.
  End zero_one_loss.
End learning.
  
  