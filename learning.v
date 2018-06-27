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

  Definition Hyp := {ffun A -> B}.

  Variable d : A*B -> R.
  Variable d_dist : big_sum (enum [finType of A*B]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable m : nat. (*The number of training samples*)
  Variable m_gt0 : (0 < m)%nat.  
  Notation mR := (INR m).
  Definition i0 : 'I_m := Ordinal m_gt0.  

  (** Training sets *)
  Definition training_set := [finType of {ffun 'I_m -> [finType of A*B]}].

  Definition X (h : Hyp) (i : 'I_m) (xy : A*B) : R :=
    let: (x,y) := xy in if h x == y then 1%R else 0%R.
  
  (** The empirical error of h on T *)
  Definition empErr (T : training_set) (h : Hyp) :=
    (big_sum (enum 'I_m) (fun i => X h i (T i))) / mR.

  (** The expected error of h on D *)
  Definition expErr (h : Hyp) := expValR d (X h i0).
  Variable expErr_nontrivial : forall h : Hyp, 0 < expErr h < 1.

  (** assume X_i are iid *)
  Variable identical : forall h : Hyp, identically_distributed d (X h).
  Variable independent : forall h : Hyp, mutual_independence d (X h).

  Lemma chernoff_bound_h
        (h : Hyp) (eps : R) (eps_gt0 : 0 < eps)
        (eps_range1 : eps < 1 - expErr h)
        (eps_range2 : eps < expErr h) :
    probOfR
      (prodR (fun _ : 'I_m => d))
      (fun T : training_set => Rle_lt_dec eps (Rabs (expErr h - empErr T h))) <=
    2 * exp (-2%R * eps^2 * mR).
  Proof.
    have H1: expErr h = p_exp d m_gt0 (X h) by [].
    have H2:
      probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
        (prodR (T:=prod_finType A B) (fun _ : 'I_m => d))
        (fun T : training_set => Rle_lt_dec eps (Rabs (p_exp (T:=prod_finType A B) d m_gt0 (X h) - empErr T h))) = 
      probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
        (prodR (T:=prod_finType A B) (fun _ : 'I_m => d))
        (fun T => Rle_lt_dec eps (Rabs (p_exp (T:=prod_finType A B) d m_gt0 (X h) - p_hat (X h) T))).
    { rewrite /probOfR; apply: big_sum_ext => //=; apply eq_in_filter => T Hin.
      have ->: empErr T h = p_hat (X h) T.
      { rewrite /p_hat /empErr; rewrite Rmult_comm //. }
      by []. }
    rewrite H1 H2.
    apply: chernoff => //; try fourier.
    { move => i x; rewrite /X; case: x; split; case: (h a == b)%B; fourier. }
    { move: H1; rewrite /p_exp => <- //. }
    move: H1; rewrite /p_exp => <- //.
  Qed.

  Lemma chernoff_bound (eps : R) (eps_gt0 : 0 < eps) :
    probOfR (prodR (fun _ : 'I_m => d))
            [pred T:training_set
            | [exists i : 'I_#|Hyp|,
                 let: h := enum_val i 
                 in Rle_lt_dec eps (Rabs (expErr h - empErr T h))]]
    <= 2 * INR #|Hyp| * exp (-2%R * eps^2 * mR).
  Proof.
    set (P := fun i:'I_#|Hyp| => 
         [pred T : training_set |
         let: h := enum_val i in Rle_lt_dec eps (Rabs (expErr h - empErr T h))]).
    change (probOfR (prodR (fun _ => d)) [pred T:training_set | [exists i : 'I_#|Hyp|, P i T]] 
            <= 2 * INR #|Hyp| * exp (-2%R * eps^2 * mR)).
    apply: Rle_trans; [apply: union_bound|].
    { by apply: prodR_nonneg. }
    rewrite [2 * _]Rmult_comm.
    have Hle:
       \big[Rplus/0]_(i in 'I_#|Hyp|)
         probOfR (T:=finfun_of_finType (ordinal_finType m) (prod_finType A B))
         (prodR (T:=prod_finType A B) (fun _ : 'I_m => d)) [eta P i]
    <= \big[Rplus/0]_(i in 'I_#|Hyp|) (2 * exp (-2%R * eps^2 * mR)).
    { rewrite -2!big_sum_sumP; apply big_sum_le => c Hin.
      apply chernoff_bound_h => //.
      admit. (*WTF? Same weird epsilon assumption.*)
      admit. (*WTF? Same weird epsilon assumption.*) }
    apply: Rle_trans; first by apply: Hle.
    rewrite big_const card_ord; elim: #|Hyp|.
    { rewrite !Rmult_0_l; apply: Rle_refl. }
    move => n H; rewrite iterS.
    have ->:
      INR n.+1 * 2 * exp (- (2) * eps ^ 2 * mR) 
    = (2 * exp (- (2) * eps ^ 2 * mR)) + INR n * 2 * exp (- (2) * eps ^ 2 * mR).
    { rewrite S_INR Rmult_assoc Rmult_plus_distr_r Rmult_1_l Rplus_comm; f_equal.
      by rewrite -Rmult_assoc. }
    apply: Rplus_le_compat_l => //.
  Admitted.
End learning.  
  
  