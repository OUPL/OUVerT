Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.
Require Import QArith Reals Rpower Ranalysis Fourier.

Require Import bigops numerics expfacts dist.

Section learning.
  Variables A B : finType.
  Variable rty : numDomainType.

  Definition Hyp := {ffun A -> B}.

  Variable d : A*B -> R.
  Variable d_dist : big_sum (enum [finType of A*B]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable m : nat. (*The number of training samples*)
  Variable m_gt0 : (0 < m)%nat.  
  Definition mR := INR m.
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

  Lemma chernoff_bound_h (h : Hyp) (eps : R) (eps_range : 0 < eps < 1 - expErr h) :
    phat_ge_q d m_gt0 (X h) eps <= exp (-2%R * eps^2 * mR).
  Proof.
    apply: chernoff2 => //.
    { move => i x; case: x => a b; rewrite /X.
      case: (h a == b)%B; split; fourier. }
    { by apply: (expErr_nontrivial h). }
    { by case: eps_range. }
    by case: eps_range.
  Qed.
  
  Lemma chernoff_bound_aux (eps : R) (eps_range : 0 < eps) :
    probOfR (prodR (fun _ => d))
            [pred T:training_set
            | [exists i : 'I_#|Hyp|,
                let: h := enum_val i in Rle_lt_dec (expErr h + eps) (empErr T h)]]
    <= 2 * INR #|Hyp| * exp (-2%R * eps^2 * mR).
  Proof.
    set (P := fun i:'I_#|Hyp| => 
           [pred T : training_set | let: h := enum_val i in Rle_lt_dec (expErr h + eps) (empErr T h)]).
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
      admit. }
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
  Qed.    
End learning.  
  
  