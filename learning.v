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

  Definition Hyp := A -> B.

  Variable d : A*B -> R.
  Variable d_dist : big_sum (enum [finType of A*B]) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Variable h : Hyp.

  Variable m : nat. (*The number of training samples*)
  Variable m_gt0 : (0 < m)%nat.  
  Definition mR := INR m.
  Definition i0 : 'I_m := Ordinal m_gt0.  

  Definition X (i : 'I_m) : A*B -> R :=
    fun xy => let: (x,y) := xy in if h x == y then 1%R else 0%R.

  (** The training set *)
  Variable T : 'I_m -> A*B.
  
  (** The empirical error of h on T *)
  Definition empErr := (big_sum (enum 'I_m) (fun i => X i (T i))) / mR.

  (** The expected error of h on D *)
  Definition expErr := expValR d (X i0).
  Variable expErr_nontrivial : 0 < expErr < 1.

  (** assume X_i are iid *)
  Variable identical : identically_distributed d X.
  Variable independent : mutual_independence d X.

  Lemma chernoff_bound (eps : R) : 0 < eps < 1 - expErr -> 
    phat_ge_q d m_gt0 X eps <=
    exp (-(RE (fun _:(A*B) => expErr + eps) (fun _ => expErr)) * mR).
  Proof.
    move => H; apply: chernoff1 => //.
    { move => i x; case: x => a b; rewrite /X.
      case: (h a == b)%B; split; fourier. }
    { by case: H. }
    by case: H.
  Qed.  
End learning.  
  
  