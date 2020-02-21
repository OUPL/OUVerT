Set Implicit Arguments.
Unset Strict Implicit.

Require Import NArith QArith Qreals Reals Fourier.



Require Import OUVerT.dyadic.
Import List.
Import ListNotations.

Require Import Lra Lia.


Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.


Import GRing.Theory Num.Def Num.Theory.



(** This file defines conversions between Ssreflect/MathComp and
    Coq Standard Library implementations of various numeric types, 
    such as: 
      - int <-> Z
      - rat <-> Q
      - rat -> R
 *)

Delimit Scope Numeric_scope with Num.
Local Open Scope Numeric_scope.

Lemma Nat_le_exists_diff: forall m n : nat, Peano.le m n -> exists p, addn m p = n.
Proof.
  intros.
  exists (subn n m).
  rewrite subnKC; auto.
  assert(reflect (m <= n)%coq_nat (m <= n)%N).
    apply leP; auto.
  inversion H0. auto. exfalso. auto. 
Qed.

Module Numerics.


  Class Numeric (T:Type) :=
    mkNumeric {
        plus: T -> T -> T where "n + m" := (plus n m) : Numeric_scope;
        neg : T->T where "- n" := (neg n) : Num;
        mult: T -> T -> T where "n * m" := (mult n m) : Num;
        pow_nat: T -> nat -> T;
        to_R : T -> R;

        of_nat: nat -> T;
        plus_id: T;
        mult_id: T;

        lt: T->T->Prop where "n < m" := (lt n m) : Num;
        ltb: T->T->bool;

        eqb: T->T->bool;

    }.

  Infix "+" := plus : Numeric_scope.
  Notation "- n" := (neg n) : Numeric_scope.
  Infix "*" := mult : Numeric_scope.
  Infix "<" := lt : Numeric_scope.


  Notation "1" := Numerics.mult_id : Numeric_scope.
  Notation "0" := Numerics.plus_id : Numeric_scope.

  Class Numeric_Props (T:Type) `{numeric_t : Numeric T} :=
    mkNumericProps {

        plus_id_lt_mult_id: plus_id < mult_id;
        
        mult_plus_id_l: forall t : T, plus_id * t = plus_id;
        of_nat_plus_id: of_nat O = plus_id;
        of_nat_succ_l: forall n : nat, of_nat (S n) = mult_id + of_nat n;
        plus_comm : forall r1 r2, r1 + r2 = r2 + r1;
        plus_assoc : forall r1 r2 r3, r1 + (r2 + r3) = r1 + r2 + r3;
        plus_neg_r : forall r, r + - r = plus_id;
        plus_id_l : forall r, plus_id + r = r;
        mult_comm : forall r1 r2, r1 * r2 = r2 * r1;
        mult_assoc : forall r1 r2 r3, r1 * (r2 * r3) = r1 * r2 * r3;
        mult_id_l : forall r, mult_id * r = r;
        mult_plus_distr_l : forall r1 r2 r3, r1 * (r2 + r3) = r1 * r2 + r1 * r3;
        lt_asym : forall r1 r2, r1 < r2 -> ~ r2 < r1;
        lt_trans : forall r1 r2 r3, r1 < r2 -> r2 < r3 -> r1 < r3;
        plus_lt_compat_l : forall r r1 r2, r1 < r2 -> r + r1 < r + r2;
        mult_lt_compat_l : forall r r1 r2, plus_id < r -> (r1 < r2 <-> r * r1 < r * r2);

        pow_natO: forall t, pow_nat t O = mult_id;
        pow_nat_rec: forall t n, pow_nat t (S n) = t * pow_nat t n;

        to_R_plus: forall t1 t2 : T, Rplus (to_R t1) (to_R t2) = to_R (t1 + t2);
        to_R_mult: forall t1 t2 : T, Rmult (to_R t1) (to_R t2) = to_R (t1 * t2);
        to_R_lt: forall t1 t2 : T, t1 < t2 <-> Rlt (to_R t1) (to_R t2);
        to_R_neg: forall t : T, Ropp (to_R t) = to_R (- t);
        to_R_inj: forall n m : T, to_R n = to_R m -> n = m;
      
        total_order_T : forall r1 r2, {r1 < r2} + {r1 = r2} + {r2 < r1};

        eqb_true_iff: forall n m, eqb n m <-> n = m;
        ltb_true_iff: forall n m, ltb n m <-> n < m;

      }.
      Ltac to_R_distr := 
    repeat (
      try (rewrite <- to_R_mult);
      try (rewrite <- to_R_plus);
      try (rewrite <- to_R_neg)
    ).

  Section use_Numeric.


    Context {Nt:Type} `{H : Numeric Nt} .
  

    Definition le (n m : Nt) : Prop := n < m \/ n = m.
    Infix "<=" := le : Numeric_scope.

    Definition leb (x y : Nt) : bool :=
    orb (ltb x y) (eqb x y).



    Lemma le_lt_or_eq: forall n m : Nt, n < m \/ n = m <-> n <= m .
    Proof. 
      split; auto.
    Qed.

    Definition minus (n m : Nt) := n + - m.


    Context  `{NtProps : Numeric_Props (numeric_t := H) Nt}.

    Lemma eqb_false_iff: forall n m, eqb n m = false <-> n <> m.
    Proof.
      intros n m.
      split; intros.
      {
        unfold not. intros.
        rewrite <- eqb_true_iff in H1.
        rewrite H0 in H1. inversion H1.
      }
      destruct (eqb n m) eqn:e; auto.
      exfalso.
      by apply eqb_true_iff in e.
    Qed.
      

    Lemma ltb_false_iff: forall n m, ltb n m = false <-> ~ n < m.
    Proof.
      intros n m.
      split; intros.
      {
        unfold not.
        intros.
        apply ltb_true_iff in H1.
        by rewrite H0 in H1.
      }
      destruct (ltb n m) eqn:e; auto.
      by apply ltb_true_iff in e.
    Qed.
    
    Lemma le_lt_dec: forall x y : Nt, {x <= y} + {y < x}.
    Proof.
      intros.
      destruct (total_order_T x y); auto.
      destruct s.
      { left. left. auto. }
      left. right. auto.
    Qed.

    Lemma plus_mult_distr_r: forall r1 r2 r3, (r2 + r3) * r1 = r2 * r1 + r3 * r1.
    Proof.
      intros.
      rewrite mult_comm.
      rewrite mult_plus_distr_l.
      rewrite mult_comm.
      rewrite -> mult_comm with r1 r3.
      auto.
    Qed.

    Program Definition numeric_ring :=  @mk_rt Nt plus_id mult_id plus mult minus neg eq plus_id_l 
      plus_comm plus_assoc mult_id_l mult_comm mult_assoc _ _ plus_neg_r.
    Next Obligation.
      apply plus_mult_distr_r.
    Qed.

    Add Ring NT_RING : numeric_ring.

    Lemma lt_irrefl: forall n : Nt, ~ n < n.
    Proof.
      unfold not.
      intros.
      assert (~ n < n).
      { apply lt_asym in H0. auto. }
      apply H1. auto.
    Qed.


    Lemma plus_assoc_reverse : forall r1 r2 r3, r1 + r2 + r3 = r1 + (r2 + r3).
    Proof. intros. rewrite plus_assoc. auto. Qed.

    Lemma mult_plus_id_r: forall t : Nt, t * plus_id  = plus_id.
    Proof. intros. rewrite mult_comm. apply mult_plus_id_l. Qed.

    Lemma lt_not_eq: forall r1 r2 : Nt, r1 < r2 -> r1 <> r2.
    Proof.
      unfold not.
      intros.
      rewrite H1 in H0.
      apply lt_irrefl in H0.
      auto.
    Qed.

    Lemma eq_dec: forall t1 t2 : Nt, {t1 = t2} + {t1 <> t2}.
    Proof. 
      intros.
      destruct (total_order_T t1 t2).
      {
        destruct s; auto.
        apply lt_not_eq in l. auto.
      }
      right.
      apply lt_not_eq in l. auto.
    Qed.


    Lemma le_not_lt: forall n m : Nt, (n <= m)-> ~ (m < n).
    Proof.
      intros.
      unfold not.
      intros.
      unfold le in H0.
      destruct H0.
      { apply lt_asym in H1. apply H1. auto. }
      rewrite H0 in H1.
      apply lt_irrefl in H1.
      inversion H1.
    Qed.

    Lemma plus_neg_l: forall t1, (-t1) + t1 = plus_id.
    Proof.
      intros.
      rewrite plus_comm.
      apply plus_neg_r.
    Qed.

    Lemma plus_id_r: forall t : Nt, t + plus_id = t.
    Proof.
      intros.
      rewrite plus_comm.
      apply plus_id_l.
    Qed.


    Lemma nat1_mult_id: of_nat (S O) = mult_id.
    Proof.
      rewrite of_nat_succ_l.
      rewrite of_nat_plus_id.
      rewrite plus_id_r.
      auto.
    Qed.

  
    Lemma double_neg: forall t : Nt, - - t = t.
    Proof.
      intros.
      rewrite <- plus_id_l.
      rewrite <- plus_neg_l with (- t).
      rewrite <- plus_assoc.
      rewrite plus_neg_l.
      rewrite plus_id_r.
      auto.
    Qed.

    Lemma neg_plus_id: -plus_id = plus_id.
    Proof.
      assert(-plus_id = -plus_id + plus_id).
      { rewrite plus_id_r. auto. }
      rewrite H0.
      rewrite plus_neg_l.
      auto.
    Qed.
      
    Lemma plus_lt_compat_r : forall r r1 r2, r1 < r2 -> r1 + r < r2 + r.
    Proof.
      intros.
      rewrite plus_comm.
      rewrite -> plus_comm with r2 r.
      apply plus_lt_compat_l.
      auto.
    Qed.  
 
    Lemma mult_lt_compat_r : forall r r1 r2, plus_id < r -> (r1 < r2 <-> r1 * r < r2 * r).
    Proof.
      intros.
      rewrite mult_comm.
      rewrite -> mult_comm with r2 r.
      apply mult_lt_compat_l; auto.
    Qed.

    Lemma plus_elim_l: forall t1 t2 t3: Nt, t1 + t2 = t1 + t3 -> t2 = t3.
    Proof.
      intros.
      rewrite <- plus_id_l.
      rewrite <- plus_neg_l with t1.
      rewrite <- plus_assoc.
      rewrite <- H0.
      rewrite plus_assoc.
      rewrite plus_neg_l.
      rewrite plus_id_l.
      auto.
    Qed.

    Lemma plus_elim_r: forall t1 t2 t3: Nt, t2 + t1 = t3 + t1 -> t2 = t3.
    Proof.
      intros.
      rewrite plus_comm in H0.
      rewrite -> plus_comm with t3 t1 in H0.
      apply plus_elim_l in H0.
      auto.
    Qed.    

    Lemma neg_pos_neg: forall t1 : Nt, plus_id < t1 <-> - t1 < plus_id.
    Proof.
      intros.
      split; intros.
      {
        apply plus_lt_compat_l with (-t1) plus_id t1 in H0.
        rewrite plus_neg_l in H0.
        rewrite plus_id_r in H0.
        auto.
      }
      apply plus_lt_compat_l with t1 (-t1) plus_id in H0.
      rewrite plus_neg_r in H0.
      rewrite plus_id_r in H0.
      auto.
    Qed.


    Lemma plus_neg_distr: forall n m : Nt, - (n + m) = -n + -m.
    Proof.
      intros.
      apply plus_elim_r with m.
      rewrite <- plus_assoc.
      rewrite plus_neg_l.
      rewrite plus_id_r.
      apply plus_elim_r with n.
      rewrite plus_neg_l.
      rewrite <- plus_assoc.
      rewrite -> plus_comm with n m.
      apply plus_neg_l.
    Qed.

    

    Lemma mult_id_r: forall n : Nt, n * 1 = n.
    Proof.
      intros.
      rewrite mult_comm.
      apply mult_id_l.
    Qed.
    

    Lemma neg_mult_distr_l: forall n m : Nt, - (n * m) = -n * m.
    Proof.
      intros.
      apply plus_elim_r with (n * m).
      rewrite plus_neg_l.
      rewrite <- plus_mult_distr_r.
      rewrite plus_neg_l.
      rewrite mult_plus_id_l.
      auto.
    Qed.

    Lemma neg_mult_distr_r: forall n m : Nt, - (n * m) = n * -m.
    Proof.
      intros.
      rewrite -> mult_comm with n (-m).
      rewrite <- neg_mult_distr_l.
      rewrite mult_comm.
      auto.
    Qed.


    Lemma mult_elim_pos: forall t1 t2 t3 : Nt, plus_id < t1 -> t1 * t2 = t1 * t3 -> t2 = t3.      
    Proof.
      intros.
      destruct total_order_T with t2 t3.
      {
        destruct s; auto.
        apply mult_lt_compat_l with t1 t2 t3 in l; auto.
        rewrite H1 in l.
        apply lt_irrefl in l.
        inversion l.
      }
      apply mult_lt_compat_l with t1 t3 t2 in l; auto.
      rewrite H1 in l.
      apply lt_irrefl in l.
      inversion l.
    Qed.

    Lemma mult_elim_l: forall t1 t2 t3 : Nt, plus_id <> t1 -> t1 * t2 = t1 * t3 -> t2 = t3.      
    Proof.
      intros.
      destruct total_order_T with t1 plus_id.
      {
        destruct s; auto.
        {           
          apply mult_elim_pos with (-t1).
          { apply neg_pos_neg. rewrite double_neg. auto. }
          repeat rewrite <- neg_mult_distr_l.
          rewrite H1.
          auto.
        }
        exfalso.
        apply H0.
        auto.
      }
      apply mult_elim_pos with t1; auto.
    Qed.

    Lemma  lt_le_dec: forall t1 t2 : Nt, {t1 < t2} + {t2 <= t1}.
    Proof.
      intros.
      unfold le.
      destruct total_order_T with t1 t2; auto.
      destruct s; auto.
    Qed.


    Definition abs (x : Nt) : Nt :=
    if leb plus_id x then x else -x.


    Definition min (x y : Nt) : Nt :=
    if leb x y then x else y.
      

    Lemma le_lt_weak: forall (n m : Nt), n < m -> n <= m.
    Proof.
      intros.
      unfold le.
      left.
      apply H0.
    Qed.

    Hint Resolve le_lt_weak.

    Lemma lt_not_le: forall n m : Nt, (n < m) -> ~ (m <= n).
    Proof.
      unfold not.
      intros. 
      apply le_not_lt in H0; auto.
    Qed.

    Lemma le_refl: forall t, t <= t.
    Proof.
      intros.
      unfold le.
      auto.
    Qed.

    Hint Immediate le_refl.
    

    Hint Resolve ltb_true_iff.
    Hint Resolve ltb_false_iff.

    Lemma leb_true_iff: forall x y : Nt, leb x y <-> x <= y.
    Proof.
      intros.
      unfold leb.
      split; intros.
      {
        apply orb_prop in H0.
        destruct H0.
          left. by apply ltb_true_iff.
        right. by apply eqb_true_iff.
      }
      destruct H0.
      {
        apply ltb_true_iff in H0.
        by rewrite H0.
      }
      apply eqb_true_iff in H0.
      rewrite H0.
      destruct (ltb x y); auto.
    Qed.

    Hint Resolve leb_true_iff.

    Lemma leb_false_iff: forall x y : Nt, leb x y = false <-> ~ x <= y.
    Proof.
      intros.
      unfold not.
      split; intros.
      {
        apply leb_true_iff in H1. by rewrite H1 in H0.
      }
      destruct (leb x y) eqn:e; auto.
      apply leb_true_iff in e. apply H0 in e. inversion e.
    Qed.

    Hint Resolve leb_false_iff.

    Lemma not_lt_le: forall n m : Nt, ~ (n < m) -> m <= n.
    Proof.
      intros.
      destruct le_lt_dec with n m; auto.
      unfold le in l.
      destruct l; auto.
      { exfalso; auto. }
      rewrite H1. auto.
    Qed.
      
    Lemma not_le_lt: forall n m : Nt, ~ (n <= m) -> m < n.
    Proof.
      intros.
      destruct lt_le_dec with n m.
      { apply le_lt_weak in l. exfalso; auto. }
      unfold le in l.
      destruct l; auto.
      rewrite H1 in H0.
      exfalso.
      auto.
    Qed.

    Lemma leb_refl: forall n : Nt, leb n n = true.
    Proof.
      intros. auto.
      apply leb_true_iff.
      apply le_refl.
    Qed.

    Hint Resolve leb_refl.

    Lemma ltb_irrefl: forall n : Nt, ltb n n = false.
    Proof.
      intros.
      apply ltb_false_iff.
      apply lt_irrefl.
    Qed.

    Lemma eqb_refl: forall n : Nt, eqb n n.
    Proof. intros. rewrite eqb_true_iff. auto. Qed.
          
    Lemma eqb_symm: forall n m: Nt, eqb n m = eqb m n.
    Proof.
      intros.
      destruct (eqb n m) eqn:e.
      { apply eqb_true_iff in e. rewrite e. rewrite eqb_refl. auto. }
      apply eqb_false_iff in e.
      assert (m <> n). unfold not. intros. apply e. auto.
      apply eqb_false_iff in H0.
      auto.
    Qed.

    Hint Resolve ltb_irrefl.
    Hint Resolve plus_le_compat_l.
    Hint Resolve plus_le_compat_r.
    Hint Resolve plus_lt_compat_l.
    Hint Resolve plus_le_compat_r.


    Lemma plus_lt_compat: forall t1 t2 t3 t4, t1 < t2 -> t3 < t4 -> (t1 + t3) < (t2 + t4).
    Proof.
      intros.
      apply plus_lt_compat_l with t3 t1 t2 in H0.
      apply plus_lt_compat_l with t2 t3 t4 in H1.
      apply lt_trans with (t2 + t3); auto.
      rewrite plus_comm.
      rewrite -> plus_comm with t2 t3.
      auto.
    Qed.

    Lemma plus_lt_le_compat: forall t1 t2 t3 t4, t1 < t2 -> t3  <= t4 -> (t1 + t3 ) < (t2 + t4).
    Proof.
      intros.
      destruct H1.
      { apply plus_lt_compat; auto. }
      rewrite H1.
      rewrite plus_comm.
      rewrite -> plus_comm with t2 t4.
      auto.
    Qed.

    Lemma plus_le_lt_compat: forall t1 t2 t3 t4, t1 <= t2 -> t3  < t4 -> (t1 + t3 ) < (t2 + t4).
    Proof.
      intros.
      rewrite plus_comm.
      rewrite -> plus_comm with t2 t4.
      apply plus_lt_le_compat; auto.
    Qed.


    Lemma plus_le_compat: forall t1 t2 t3 t4,  t1 <= t2 ->  t3 <= t4 -> (t1 + t3) <= (t2 + t4).
    Proof.
      intros.
      unfold le in *.
      destruct H1; destruct H0.
      { left. apply plus_lt_compat; auto. }
      { left. apply plus_le_lt_compat; auto. unfold le. right. auto. }
      { left. apply plus_lt_le_compat; auto. unfold le. right. auto. }
      right.
      rewrite H0.
      rewrite H1.
      auto.
    Qed.

    Lemma lt_le_trans: forall x y z : Nt, x < y -> y <= z -> x < z.
    Proof.
      intros.
      rewrite <- plus_id_r.
      rewrite <- plus_id_r with x.
      rewrite <- plus_neg_r with y.
      repeat rewrite plus_assoc.
      rewrite -> plus_comm with z y.
      apply plus_lt_le_compat.
      2 : { apply le_refl. }
      apply plus_lt_le_compat; auto.
    Qed.    

    Lemma le_not_eq_lt: forall x y : Nt, x <= y -> x <> y -> x < y.
    Proof.
      intros.
      unfold le in H0.
      destruct H0; intuition.
    Qed.

    Lemma le_trans: forall x y z : Nt, x <= y -> y <= z -> x <= z.
    Proof.
      intros.
      destruct eq_dec with x y.
      { rewrite e. apply H1. }
      apply le_lt_weak.
      apply lt_le_trans with y; auto.
      apply le_not_eq_lt; auto.
    Qed.

    Hint Resolve mult_plus_id_l.
    Hint Resolve mult_plus_id_r.
    Hint Resolve mult_id_l.
    Hint Resolve mult_id_r.
    Hint Resolve plus_id_l.
    Hint Resolve plus_id_r.

    
    Lemma mult_le_compat_l: forall x y z : Nt, plus_id <= x -> y <= z -> x * y <= x * z.
    Proof.
      intros.
      unfold le in *.
      destruct H0.
      2: {right. rewrite <- H0. repeat rewrite mult_plus_id_l. auto. }
      destruct H1.
      { left. apply mult_lt_compat_l; auto. }
      right.
      rewrite H1.
      auto.
    Qed.

    
      
    Lemma mult_le_compat_l_reverse: forall x y z : Nt, plus_id < x -> x * y <= x* z -> y <= z.
    Proof.
      intros.
      unfold le in *.
      destruct H1.
      {
        left.
        rewrite mult_lt_compat_l; auto.
          apply H1.
        auto.
      }
      right.
      assert (0 <> x). apply lt_not_eq. auto.
      apply mult_elim_l with x; auto.
    Qed.

    Lemma mult_le_compat_r: forall x y z : Nt, plus_id <= x -> y <= z -> y * x <= z * x.
    Proof.
      intros.
      rewrite mult_comm.
      rewrite -> mult_comm with z x.
      apply mult_le_compat_l; auto.
    Qed.

    Lemma mult_le_compat_r_reverse: forall x y z : Nt, plus_id < x -> y * x <= z * x -> y <= z.
    Proof.
      intros.
      rewrite mult_comm in H1.
      rewrite -> mult_comm with z x in H1.
      apply mult_le_compat_l_reverse with x; auto.
    Qed.

    Lemma le_both_eq: forall x y : Nt, x <= y -> y <= x -> x = y.
    Proof.
      intros.
      destruct H0; auto.
      apply lt_not_le in H0.
      exfalso. auto.
    Qed.

    Lemma neg_neg_pos: forall t1 : Nt, t1 < 0 <-> 0 < - t1.
    Proof.
      intros.
      split; intros.
      { apply neg_pos_neg. rewrite double_neg.  auto. }
      apply neg_pos_neg in H0. rewrite double_neg in H0. auto.
    Qed.

    Hint Resolve plus_mult_distr_r.


    Lemma n_plus_n_eq_2n: forall n : Nt, n + n = (1 + 1) * n.
    Proof.
      intros. auto 20.
      rewrite plus_mult_distr_r.
      rewrite mult_id_l.
      auto.
    Qed.


    Lemma lt_neg: forall n m : Nt, n < m <-> - m < - n.
    Proof.
      intros.
      split; intros.
      {
        apply plus_lt_compat_l with (-n) n m in H0.
        rewrite plus_neg_l in H0.
        apply plus_lt_compat_r with (-m) 0 (-n + m) in H0.
        rewrite <- plus_assoc in H0.
        rewrite plus_neg_r in H0.
        rewrite plus_id_r in H0.
        rewrite plus_id_l in H0.
        auto.
      }
      apply plus_lt_compat_l with n (-m) (-n) in H0.
      rewrite plus_neg_r in H0.
      apply plus_lt_compat_r with m (n + -m) 0 in H0.
      rewrite <- plus_assoc in H0.
      rewrite plus_neg_l in H0.
      rewrite plus_id_r in H0.
      rewrite plus_id_l in H0.
      auto. 
    Qed.


    Lemma le_lt_trans: forall x y z : Nt, x <= y -> y < z -> x < z.
    Proof.
      intros.
      unfold le in H0.
      destruct H0.
        apply lt_trans with y; auto.
      rewrite H0. auto.
    Qed.

    Lemma neg_eq: forall n m : Nt, -n = -m -> n = m.
    Proof.
      intros.
      rewrite -> plus_elim_r with (-n) n m; auto.
      rewrite plus_neg_r.
      rewrite -> plus_elim_r with (-m) 0 (m + - n); auto.
      rewrite -> plus_comm with m (- n).
      rewrite <- plus_assoc.
      rewrite plus_neg_r.
      rewrite plus_id_l.
      rewrite plus_id_r.
      rewrite H0.
      auto.
    Qed.
      
    Lemma mult_le_compat:  forall r1 r2 r3 r4,plus_id <= r1 -> plus_id <= r3 -> r1  <= r2 -> r3 <= r4 ->
             (r1 *  r3) <= (r2 *  r4).
    Proof.
      intros.
      destruct total_order_T with r2 0;
        try (destruct s); try (
        unfold le in H0,H1;
        destruct H0; destruct H1; try (
          apply mult_le_compat_l with r2 r3 r4 in H3; 
            try (unfold le; auto; fail);
          apply mult_le_compat_l with r3 r1 r2 in H2;
            try (unfold le; auto; fail);
          apply le_trans with (r3 * r2);
            rewrite mult_comm; auto; fail); fail
      ).
      unfold le in H0.
      destruct H0.
      {
        exfalso.
        apply lt_irrefl with 0.
        apply lt_le_trans with r1; auto.
        apply le_trans with r2; auto.
      }
      rewrite <- H0 in H2.
      exfalso.
      apply lt_irrefl with 0.
      apply le_lt_trans with r2; auto.
    Qed.

    Lemma mult_lt_0_compat: forall r1 r2 : Nt, 0 < r1 -> 0 < r2 -> 0 < r1 * r2.
    Proof.
      intros.
      apply mult_lt_compat_l with r1 0 r2 in H1; auto.
      rewrite mult_plus_id_r in H1.
      auto.
    Qed.

    Lemma plus_le_compat_l : forall r r1 r2, r1 <= r2 -> r + r1 <= r + r2.
    Proof.
      unfold le.
      intros.
      destruct H0.
      { left. apply plus_lt_compat_l. auto. }
      rewrite H0.
      auto.
    Qed.

    Lemma plus_le_compat_r : forall r r1 r2, r1 <= r2 -> r1 + r <= r2 + r.
    Proof.
      intros.
      rewrite plus_comm.
      rewrite -> plus_comm with r2 r.
      apply plus_le_compat_l.
      auto.
    Qed.

    Lemma plus_le_compat_l_reverse : forall r r1 r2, r + r1 <= r + r2 -> r1 <= r2 .
    Proof.
      intros.
      apply plus_le_compat_l with (-r) (r + r1) (r + r2) in H0.
      repeat rewrite plus_assoc in H0.
      rewrite plus_neg_l in H0.
      repeat rewrite plus_id_l in H0.
      auto.
    Qed.

    Lemma plus_le_compat_r_reverse : forall r r1 r2, r1 + r <= r2 + r -> r1 <= r2 .
    Proof.
      intros.
      rewrite plus_comm in H0.
      rewrite -> plus_comm with r2 r in H0.
      apply plus_le_compat_l_reverse in H0.
      auto.
    Qed.


    Lemma mult_simpl_l: forall n m p : Nt, n = m -> p * n = p * m.
    Proof. intros. rewrite H0. auto. Qed.

    Lemma mult_simpl_r: forall n m p : Nt, n = m -> n * p = m * p.
    Proof. intros. rewrite H0. auto. Qed.

    Lemma plus_simpl_l: forall n m p : Nt, n = m -> p + n = p + m.
    Proof. intros. rewrite H0. auto. Qed.

    Lemma plus_simpl_r: forall n m p : Nt, n = m -> n + p = m + p.
    Proof. intros. rewrite H0. auto. Qed.


    Lemma abs_mult_pos_l: forall n m : Nt, 0 <= n -> abs (n * m) = n * abs m.
    Proof.
      intros.
      unfold abs.
      destruct (leb 0 m) eqn:e.
      {
        apply leb_true_iff in e.
        apply mult_le_compat_l with n 0 m in e; auto.
        rewrite mult_plus_id_r in e.
        apply leb_true_iff in e.
        rewrite e.
        auto.
      }
      apply leb_false_iff in e.
      apply not_le_lt in e.
      destruct H0.
      2: { 
        rewrite <- H0. 
        repeat rewrite mult_plus_id_l.
        rewrite leb_refl.
        auto.
      }
      apply mult_lt_compat_l with n m 0 in e; auto.
      rewrite <- mult_plus_id_l with 0 in e.
      repeat rewrite mult_plus_id_r in e.
      apply lt_not_le in e.
      apply leb_false_iff in e.
      rewrite e.
      rewrite neg_mult_distr_r.
      auto.
    Qed.

  Lemma abs_mult_pos_r: forall n m : Nt, 0 <= n -> abs (m * n) = abs m * n.
  Proof. intros. rewrite mult_comm. rewrite abs_mult_pos_l; auto. apply mult_comm. Qed. 
    
  Lemma le_abs: forall n : Nt, n <= abs n.
  Proof. 
    intros.
    unfold abs.
    destruct (leb 0 n) eqn:e.
      apply le_refl.
    apply plus_le_compat_l_reverse with n.
    rewrite plus_neg_r.
    rewrite <- plus_id_l.
    apply leb_false_iff in e.
    apply not_le_lt in e.
    apply le_lt_weak in e.
    apply plus_le_compat; auto.
  Qed.


  Lemma le_neg: forall n m : Nt, - n <= -m <-> m <= n.
  Proof.
    unfold le.
    intros.
    split; intros;
      destruct H0;
      try (apply lt_neg in H0; auto; fail);
      try (apply neg_eq in H0);
      try (rewrite H0);
      auto.
    Qed.

  Lemma abs_neg: forall n : Nt, abs (-n) = abs n.
  Proof.
    intros.
    unfold abs.
    destruct (leb 0 (- n) ) eqn:e.
    {
      apply leb_true_iff in e.
      rewrite <- neg_plus_id in e.
      rewrite -> le_neg in e.
      unfold le in e.
      destruct e.
      {
        apply lt_not_le in H0.
        apply leb_false_iff in H0.
        rewrite H0.
        auto.
      }
      rewrite H0.
      destruct (leb 0 0); auto.
      apply neg_plus_id.
    }
    apply leb_false_iff in e.
    apply not_le_lt in e.
    rewrite <- neg_plus_id in e.
    apply lt_neg in e.
    apply le_lt_weak in e.
    apply leb_true_iff in e.
    rewrite e.
    apply double_neg.
  Qed.

  Lemma abs_posb: forall n : Nt, leb 0 n -> abs n = n.
  Proof. intros. unfold abs. rewrite H0. auto. Qed.

  Lemma abs_negb: forall n : Nt, leb 0 n = false -> abs n = - n.
  Proof. intros. unfold abs. rewrite H0. auto. Qed.

  Lemma abs_plus_le: forall n m : Nt, abs (n + m) <= abs n + abs m.
  Proof.
    intros.
    destruct (leb 0 (n + m)) eqn:e_nm.
    {
      rewrite abs_posb; auto.
      apply plus_le_compat; apply le_abs.
    }
    rewrite abs_negb; auto.
    rewrite plus_neg_distr.
    apply plus_le_compat; rewrite <- abs_neg; apply le_abs.
  Qed.

  Lemma pow_nat_add: forall (n m : nat) (x : Nt), pow_nat x (n + m) = pow_nat x n * pow_nat x m.
  Proof.
    intros.
    induction m.
      rewrite pow_natO. rewrite mult_id_r. rewrite addn0. auto.
    rewrite addnS.
    repeat rewrite pow_nat_rec.
    rewrite IHm.
    rewrite mult_assoc.
    rewrite -> mult_comm with x (pow_nat x n).
    rewrite mult_assoc.
    auto.
  Qed.

  Lemma neg_mult_comm: forall (n m : Nt), -n * m = n * - m.
  Proof.
    intros.
    rewrite <- neg_mult_distr_l.
    rewrite neg_mult_distr_r.
    auto.
  Qed.

  Lemma abs_ge_0: forall n : Nt, 0 <= abs n.
  Proof.
    intros.
    unfold abs. 
    destruct (leb 0 n) eqn:e.
      apply leb_true_iff. auto.
    apply leb_false_iff in e.
    apply not_le_lt in e.
    apply le_neg.
    rewrite double_neg.
    rewrite neg_plus_id.
    apply le_lt_weak.
    auto.
  Qed.

  Lemma abs_0: abs 0 = 0.
  Proof. unfold abs. destruct (leb 0 0); auto. rewrite neg_plus_id. auto. Qed.
    

  Lemma pow_ge_0: forall (n : Nt) (m : nat), 0 <= n -> 0 <= pow_nat n m .
  Proof.
    intros.
    induction m.
    { rewrite pow_natO. apply le_lt_weak. apply plus_id_lt_mult_id. }
    rewrite pow_nat_rec.
    rewrite <- mult_plus_id_l with 0.
    apply mult_le_compat; auto; apply le_refl.
  Qed.

  Lemma pow_0_nat: forall n : nat, pow_nat 0 (S n) = 0.
  Proof.
    intros.
    rewrite pow_nat_rec.
    apply mult_plus_id_l.
  Qed.

  Lemma pow_gt_0: forall (n : Nt) (m : nat), 0 < n -> 0 < pow_nat n m .
  Proof.
    intros.
    induction m.
    { rewrite pow_natO. apply plus_id_lt_mult_id. }
    rewrite pow_nat_rec.
    apply mult_lt_0_compat; auto.
  Qed.

  Lemma pow_le_1: forall (n : Nt) (m : nat), 0 <= n /\ n <= 1 -> pow_nat n m <= 1. 
  Proof.
    intros.
    induction m.
      rewrite pow_natO. apply le_refl.
    rewrite pow_nat_rec.
    destruct H0.
    rewrite <- mult_id_l.
    apply mult_le_compat; auto.
    apply pow_ge_0.
    auto.
  Qed.

  Lemma plus_le_l_to_r: forall x y z : Nt, x + y <= z <-> x <= z + - y.
  Proof.
    intros.
    split; intros.
    {
      apply plus_le_compat_r with (-y) _ _ in H0.
      rewrite <- plus_assoc in H0.
      rewrite plus_neg_r in H0.
      rewrite plus_id_r in H0.
      auto.
    }
    apply plus_le_compat_r with y _ _ in H0.
    rewrite <- plus_assoc in H0.
    rewrite plus_neg_l in H0.
    rewrite plus_id_r in H0.
    auto.
  Qed.

  Lemma plus_le_r_to_l: forall x y z : Nt, x <= z + y <-> x + - y <= z.
  Proof.
    intros.
    split; intros.
    { rewrite plus_le_l_to_r. rewrite double_neg. auto. }
    apply plus_le_l_to_r in H0.
    rewrite double_neg in H0.
    auto.
  Qed.
  

  Lemma abs_triangle: forall (x y z : Nt), abs ( x + - z ) <= abs (x + - y) + abs (y + - z).
  Proof.
    intros.
    rewrite <- plus_id_r with (x + -z).
    rewrite <- plus_neg_l with y.
    repeat rewrite <- plus_assoc.
    rewrite -> plus_assoc with (-z) (-y) y.
    rewrite -> plus_comm with (-z) _.
    rewrite <- plus_assoc.
    rewrite -> plus_comm with (-z) _.
    rewrite plus_assoc.
    apply abs_plus_le.
  Qed.

  Lemma plus_id_unique: forall n m : Nt, n + m = n -> m = 0.
  Proof.
    intros.
    apply plus_elim_l with n.
    rewrite plus_id_r.
    auto.
  Qed.

  Lemma to_R_plus_id: to_R 0 = IZR Z0.
  Proof.
    rewrite <- Rplus_opp_r with (to_R 0).
    rewrite to_R_neg.
    rewrite to_R_plus.
    rewrite plus_id_l.
    rewrite neg_plus_id.
    auto.
  Qed.

  Lemma to_R_neq: forall n m : Nt, n <> m <-> to_R n <> to_R m.
  Proof.
    intros.
    split; unfold not; intros.
      apply H0. apply to_R_inj. auto.
    apply H0.
    rewrite H1.
    auto.
  Qed.    
      

  Lemma plus_id_neq_mult_id: 0 <> 1.
  Proof.
    unfold not.
    intros.
    apply lt_irrefl with 1.
    assert (0 < 1).
      apply plus_id_lt_mult_id.
    rewrite H0 in H1.
    auto.
  Qed.


  Lemma mult_id_neq_plus_id: 1 <> 0.
  Proof.
    unfold not.
    intros.
    apply plus_id_neq_mult_id.
    rewrite H0.
    auto.
  Qed.

  Lemma to_R_mult_id: to_R 1 = IZR (Zpos xH).
  Proof.
    assert( forall x y : R, Rmult x y = x -> x = IZR Z0 \/ y = IZR (Zpos xH)).
    {
      intros.
      destruct (Req_dec x 0).
        rewrite H1. auto.
      right.
      assert ( Rmult (Rinv x) (Rmult x y) = Rmult (Rinv x)  x).
      { rewrite H0. auto. }
      rewrite Rinv_l in H2; auto.
      rewrite <- Rmult_assoc in H2.
      rewrite Rinv_l in H2; auto.
      rewrite Rmult_1_l in H2.
      auto.
    }
    destruct H0 with (to_R 1) (to_R 1); auto.
    { rewrite to_R_mult. rewrite mult_id_l. auto. }
    rewrite <- to_R_plus_id in H1.
    apply to_R_inj in H1.
    exfalso.
    apply mult_id_neq_plus_id.
    auto.
  Qed.

  Lemma to_R_of_nat: forall n : nat, to_R (of_nat n) = INR n.
  Proof.
    intros.
    induction n.
      rewrite of_nat_plus_id. simpl. apply to_R_plus_id.
    rewrite of_nat_succ_l.
    rewrite <- to_R_plus.
    rewrite IHn.
    rewrite S_INR.
    rewrite to_R_mult_id.
    apply Rplus_comm.
  Qed.

  Lemma to_R_inv_r: forall (n m : Nt), m <> 0 -> Rmult (to_R (n * m)) (Rinv (to_R m)) = to_R n.
  Proof.
    intros.
    rewrite <- to_R_mult.
    rewrite Rmult_assoc.
    rewrite Rinv_r.
    2: { rewrite <- to_R_plus_id. rewrite <- to_R_neq. auto. }
    rewrite <- Rmult_1_r.
    auto.
  Qed.

  Lemma to_R_div_eq_iff_r: forall (n m p : Nt), m <> 0 -> 
    n * m = p <-> to_R n = Rdiv (to_R p) (to_R m).
  Proof.
    intros.
    split; intros.
    {
      rewrite <- H1.
      unfold Rdiv.
      rewrite to_R_inv_r; auto.
    }
    apply to_R_inj.
    rewrite <- to_R_mult.
    rewrite <- Rmult_1_r with (to_R p).
    rewrite <- Rinv_l with (to_R m); auto.
    2: { rewrite <- to_R_plus_id. apply to_R_neq. auto. }
    rewrite <- Rmult_assoc.
    unfold Rdiv in H1.
    rewrite <- H1.
    auto.
  Qed.

  Lemma to_R_div_lt_iff_r: forall (n m p : Nt), 0 < m -> 
    n * m < p <-> Rlt (to_R n) (Rdiv (to_R p) (to_R m)).
  Proof.
    intros.
    assert (to_R m <> IZR 0).
    { 
      rewrite <- to_R_plus_id. 
      rewrite <- to_R_neq.
      apply lt_not_eq in H0.     
      auto.
    } 
    split; intros.
    {
      unfold Rdiv.
      rewrite <- Rmult_1_r with (to_R n).
      rewrite <- Rinv_r with (to_R m); auto.
      rewrite <- Rmult_assoc.
      apply Rmult_lt_compat_r.
      {
        apply Rinv_0_lt_compat.
        rewrite <- to_R_plus_id.
        apply to_R_lt.
        auto.
      } 
      rewrite to_R_mult.
      apply to_R_lt.
      auto.
    }
    unfold Rdiv in H2.
    rewrite to_R_lt.
    rewrite <- to_R_mult.
    rewrite <- Rmult_1_r with (to_R p).
    rewrite <- Rinv_l with (to_R m); auto.
    rewrite <- Rmult_assoc.
    apply Rmult_lt_compat_r; auto.
    rewrite <- to_R_plus_id.
    apply to_R_lt.
    auto.
  Qed.

  Lemma to_R_div_le_iff_r: forall (n m p : Nt), 0 < m ->
    n * m <= p <-> Rle (to_R n) (Rdiv (to_R p) (to_R m)).
  Proof.
    intros.
    unfold Rle.
    unfold le.
    split; intros.
    {
      destruct H1.
        apply to_R_div_lt_iff_r in H1; auto.
      apply to_R_div_eq_iff_r in H1; auto.
      apply lt_not_eq in H0.
      auto.
    }
    destruct H1.
      apply to_R_div_lt_iff_r in H1; auto.
    apply to_R_div_eq_iff_r in H1; auto.
    apply lt_not_eq in H0.
    auto.
  Qed.

  Lemma to_R_neg_div_distr_l: forall (n m : Nt), m <> 0 -> Ropp (Rdiv (to_R n) (to_R m)) = Rdiv (to_R (-n)) (to_R m).
  Proof.
    intros.
    unfold Rdiv.
    rewrite Ropp_mult_distr_l.
    rewrite to_R_neg.
    auto.
  Qed.

  Lemma to_R_neg_div_distr_r: forall (n m : Nt), m <> 0 -> Ropp (Rdiv (to_R n) (to_R m)) = Rdiv (to_R (n)) (to_R (-m)). 
  Proof.
    intros.
    unfold Rdiv.
    rewrite Ropp_mult_distr_r.
    rewrite Ropp_inv_permute; auto.
      rewrite to_R_neg. auto.
    rewrite <- to_R_plus_id.
    apply to_R_neq.
    auto.
  Qed.


  Lemma to_R_div_le_neg_l: forall (n m p : Nt), m < 0 ->
    n * m <= p <-> Rle (Rdiv (to_R p) (to_R m)) (to_R n) .
  Proof.
    intros.
    split; intros.
    { 
      apply Ropp_le_cancel.
      rewrite to_R_neg_div_distr_r; auto.
      2: { apply lt_not_eq. auto. }
      rewrite to_R_neg.      
      rewrite <- to_R_div_le_iff_r.
        rewrite <- neg_mult_distr_l.
        rewrite <- neg_mult_distr_r.
        rewrite double_neg.
        auto.
      rewrite <- neg_plus_id.      
      rewrite <- lt_neg.
      auto.
    }
    rewrite <- double_neg with (n * m).
    rewrite neg_mult_distr_l.
    rewrite neg_mult_distr_r.
    rewrite to_R_div_le_iff_r.
    2: { rewrite <- neg_plus_id. rewrite <- lt_neg. auto. }
    rewrite <- to_R_neg.
    rewrite <- to_R_neg_div_distr_r.
    2: { apply lt_not_eq. auto. }
    apply Ropp_le_contravar.
    auto.
  Qed.

  Lemma to_R_div_le_neg_r: forall (n m p : Nt), m < 0 ->
    p <= n * m <-> Rle  (to_R n) (Rdiv (to_R p) (to_R m)) .
  Proof.
    intros.
    split; intros.
    {
      rewrite <- le_neg in H1.
      rewrite neg_mult_distr_l in H1.
      rewrite -> to_R_div_le_neg_l in H1; auto.
      rewrite <- to_R_neg_div_distr_l in H1.
      2: { apply lt_not_eq. auto. }      
      rewrite <- to_R_neg in H1.
      apply Ropp_le_cancel in H1.
      auto.
    }    
    rewrite <- le_neg.
    rewrite neg_mult_distr_l.
    rewrite -> to_R_div_le_neg_l; auto.
    rewrite <- to_R_neg_div_distr_l.
    2: { apply lt_not_eq. auto. }      
    rewrite <- to_R_neg.
    apply Ropp_le_contravar.
    auto.
  Qed.

  Lemma plus_simpl_lr: forall (n m p q : Nt),
    n = m -> p = q -> n + p = m + q.
  Proof. intros. rewrite H0. rewrite H1. auto. Qed.

  Lemma mult_simpl_lr: forall (n m p q : Nt),
    n = m -> p = q -> n * p = m * q.
  Proof. intros. rewrite H0. rewrite H1. auto. Qed.

  Lemma abs_0_same: forall x y : Nt, abs (x + - y) = 0 <-> x = y.
  Proof.
    intros.
    split; intros.
    2: { rewrite H0. rewrite plus_neg_r. unfold abs. destruct (leb 0 0). auto. apply neg_plus_id. }
    unfold abs in H0.
    destruct (leb 0 (x + - y)) eqn:e.
    {
      rewrite <- plus_id_l.
      rewrite <- H0.
      rewrite <- plus_assoc.
      rewrite plus_neg_l.
      auto.
    }
    rewrite plus_neg_distr in H0.
    rewrite double_neg in H0.
    rewrite <- plus_id_r with x.
    rewrite <- H0.
    rewrite plus_assoc.
    rewrite plus_neg_r. 
    auto.
  Qed.
       
  Lemma to_R_le: forall (t1 t2 : Nt), t1 <= t2 <-> (Rle (to_R t1) (to_R t2)).
  Proof.
    intros.
    split; intros.
    {
      destruct H0.
      { unfold Rle. left. rewrite <- to_R_lt. auto. }
      rewrite H0.
      apply Rle_refl.
    }
    unfold Rle in H0.
    destruct H0.
    { rewrite <- to_R_lt in H0. apply le_lt_weak. auto. }
    apply to_R_inj in H0.
    rewrite H0.
    auto.
  Qed.

  Lemma to_R_ltb_true_iff: forall t1 t2 : Nt, ltb t1 t2  <-> Rlt (to_R t1) (to_R t2).
  Proof.
    intros.
    split; intros.
    { apply ltb_true_iff in H0. apply to_R_lt. auto. }
    apply ltb_true_iff.
    apply to_R_lt.
    auto.
  Qed.

  Lemma to_R_leb_true_iff: forall t1 t2 : Nt, leb t1 t2  <-> Rle (to_R t1) (to_R t2).
  Proof.
    intros.
    split; intros.
    { apply leb_true_iff in H0. apply to_R_le. auto. }
    apply leb_true_iff.
    apply to_R_le.
    auto.
  Qed.
 
  Lemma to_R_ltb_false_iff: forall t1 t2 : Nt, ltb t1 t2 = false  <-> ~ Rlt (to_R t1) (to_R t2).
  Proof.
    intros.
    split; intros;
      try (apply ltb_false_iff in H0);
      try (apply ltb_false_iff); 
      unfold not; intros; apply H0; apply to_R_lt; auto.
  Qed.

  Lemma to_R_leb_false_iff: forall t1 t2 : Nt, leb t1 t2 = false  <-> ~ Rle (to_R t1) (to_R t2).
  Proof.
    intros.
    split; intros;
      try (apply leb_false_iff in H0);
      try (apply leb_false_iff); 
      unfold not; intros; apply H0; apply to_R_le; auto.
  Qed.

  

  Lemma leb_ltb_or_eqb: forall t1 t2 : Nt, leb t1 t2 = ltb t1 t2 || eqb t1 t2.
  Proof.
    intros.
    destruct (leb t1 t2) eqn:e.
    {
      apply leb_true_iff in e.
      destruct e.
      { apply ltb_true_iff in H0. rewrite H0. auto. }
      rewrite H0.
      rewrite eqb_refl.      
      rewrite orb_true_r.
      auto.
    }
    apply leb_false_iff in e.
    assert (ltb t1 t2 = false).
      apply ltb_false_iff. unfold not. intros. apply le_lt_weak in H0. auto.
    rewrite H0.
    apply not_le_lt in e.
    apply lt_not_eq in e.
    apply eqb_false_iff in e.
    rewrite eqb_symm.
    rewrite e.
    auto.
  Qed.

  Lemma to_R_abs: forall n : Nt, to_R (abs n) = Rabs (to_R n).
  Proof.
    intros.
    unfold abs.
    destruct (leb 0 n) eqn:e.
    {
      apply leb_true_iff in e.
      apply to_R_le in e.
      rewrite to_R_plus_id in e.
      apply Rabs_pos_eq in e.
      rewrite e.
      auto.
    }
    apply leb_false_iff in e.
    apply not_le_lt in e.
    apply le_lt_weak in e.
    apply to_R_le in e.
    rewrite to_R_plus_id in e.
    apply Rabs_left1 in e.
    rewrite e.
    rewrite to_R_neg.
    auto.
  Qed.

  Lemma to_R_pow_nat: forall x n, to_R (pow_nat x n) = (to_R x) ^ n.
  Proof.
    intros.
    induction n.
    { simpl. rewrite pow_natO. apply to_R_mult_id. }
    simpl.
    rewrite pow_nat_rec.
    rewrite <- to_R_mult.
    rewrite IHn.
    auto.
  Qed.

  Lemma pow_nat_ge1_le: forall x n m,  1 <= x -> Nat.le n m -> pow_nat x n <= pow_nat x m.
  Proof. 
    intros.
    assert(forall m', pow_nat x n <=  pow_nat x (n+m')).
    { 
      intros. induction m'. rewrite addn0. auto.
      rewrite addnS.
      rewrite <- mult_id_l with (pow_nat x n).
      rewrite pow_nat_rec.
      apply mult_le_compat; auto.
        apply le_lt_weak. apply plus_id_lt_mult_id.
      apply pow_ge_0.
      apply le_trans with 1; auto.
      apply le_lt_weak. apply plus_id_lt_mult_id.
    }
    destruct Nat_le_exists_diff with n m; auto.
    rewrite <- H3.
    apply H2.
  Qed.

  Lemma pow_nat_le1_le: forall x n m, 0 < x -> x <= 1 -> Nat.le n m -> pow_nat x m <= pow_nat x n.
  Proof. 
    intros.
    assert(forall m', pow_nat x (n+m') <=  pow_nat x n).
    { 
      intros. induction m'. rewrite addn0. auto.
      rewrite addnS.
      rewrite <- mult_id_l with (pow_nat x n).
      rewrite pow_nat_rec.
      apply mult_le_compat; auto.
      apply pow_ge_0. auto.
    }
    destruct Nat_le_exists_diff with n m; auto.
    rewrite <- H4.
    apply H3.
  Qed.

  Lemma lt_diff_pos: forall x y : Nt, x < y -> 0 < (y + - x).
  Proof. 
    intros.
    rewrite <- plus_neg_r with x.
    apply plus_lt_compat_r. auto.
  Qed. 

  Lemma min_comm: forall x y : Nt, min x y = min y x.
  Proof. 
    intros. unfold min.
    destruct (total_order_T x y).
    {
      destruct s.
      2: { rewrite e. auto. }
      assert(leb y x = false).
        apply leb_false_iff. apply lt_not_le. auto.
      rewrite H0.
      apply le_lt_weak in l.
      apply leb_true_iff in l. rewrite l. auto.
    }
    assert(leb x y = false).
    { apply leb_false_iff. apply lt_not_le. auto. }
    rewrite H0. apply le_lt_weak in l. apply leb_true_iff in l. rewrite l. auto.
  Qed.

  Lemma ge_min_l: forall x y : Nt, min x y <= x.
  Proof. 
    intros.
    unfold min. 
    destruct (total_order_T x y).
    {
      destruct s.
      2:{  rewrite e. destruct (leb y y); auto. }
      apply le_lt_weak in l.
      apply leb_true_iff in l. rewrite l. auto.
    }
    apply le_lt_weak.
    apply le_lt_trans with y; auto.
    apply lt_not_le in l. apply leb_false_iff in l.
    rewrite l. auto.
  Qed.

  Lemma ge_min_r: forall x y : Nt, min x y <= y.
  Proof. intros. rewrite min_comm. apply ge_min_l. Qed.

  Lemma min_id: forall x : Nt, min x x = x.
  Proof. intros. unfold min. destruct (leb x x); auto. Qed.

  Lemma min_cases: forall x y : Nt, min x y = x \/ min x y = y.
  Proof. intros. unfold min. destruct (leb x y); auto. Qed.

  End use_Numeric.



(**Req_EM_T**)
Program Instance Numeric_D: Numerics.Numeric (DRed.t) :=
  @Numerics.mkNumeric
    DRed.t
    DRed.add
    DRed.opp
    DRed.mult
    DRed.natPow
    (fun x => Q2R (D_to_Q x))
    DRed.of_nat
    DRed.t0
    DRed.t1
    Dlt
    DRed.lt_le_dec
    DRed.eq_dec
.

Program Instance Numeric_Props_D: @Numerics.Numeric_Props DRed.t Numeric_D:=
    @Numerics.mkNumericProps
    DRed.t
    Numeric_D
    DRed.lt_t0_t1
    DRed.mult0L
    DRed.of_natO
    DRed.of_nat_succ_l

    
    DRed.addC
    DRed.addA
    _
    DRed.add0l
    DRed.multC
    DRed.multA
    DRed.mult1L
    DRed.multDistrL
    DRed.lt_asym
    DRed.lt_trans
    DRed.plus_lt_compat_l
    DRed.mult_lt_compat_l
    DRed.natPowO
    DRed.natPowRec
    _
    _
    _
    _
    _
    DRed.total_order_T
    _
    _
.
Next Obligation.
  intros. rewrite DRed.addC. apply DRed.addOppL. Qed.
Next Obligation.
  intros;rewrite <- Q2R_plus;apply Qeq_eqR; rewrite DRed.addP; apply Qeq_refl. Qed.
Next Obligation.
  intros; rewrite <- Q2R_mult; apply Qeq_eqR; rewrite DRed.multP; apply Qeq_refl. Qed.
Next Obligation.
  intros. split;intros. apply Qlt_Rlt. auto. apply Rlt_Qlt. auto. Qed.
Next Obligation.
  intros. rewrite <- Q2R_opp. apply Qeq_eqR. rewrite DRed.oppP. apply Qeq_refl. Qed.
Next Obligation.
  intros. apply eqR_Qeq in H. apply DRed.Dred_eq; auto. Qed.
Next Obligation.
  split; intros.
  { 
    destruct (DRed.eq_dec n m); auto.
    by exfalso.
  }
  rewrite H.
  destruct (DRed.eq_dec m m); auto.
Qed.
Next Obligation.
  split; intros.
  {
    destruct (DRed.lt_le_dec n m); auto.
    by exfalso.
  }
  destruct (DRed.lt_le_dec n m); auto.
  exfalso.
  by apply DRed.le_not_lt in H.
Qed.



Delimit Scope R_scope with R_s.
Local Open Scope R_scope.


Program Instance Numeric_R: Numeric R :=
  @Numerics.mkNumeric
    R
    Rplus
    Ropp
    Rmult
    pow
    (fun x => x)
    INR
    (IZR Z0)
    (IZR (Zpos xH))
    Rlt
    _
    _
.
Next Obligation.
    destruct (Raxioms.total_order_T H H0).
      destruct s.
        exact true.
      exact false.
    exact false.
Defined.
Next Obligation.
    destruct (Raxioms.total_order_T H H0).
      destruct s.
        exact false.
      exact true.
    exact false.
Defined.

Program Instance Numeric_Props_R: @Numerics.Numeric_Props R Numeric_R:=
  @Numerics.mkNumericProps
    R
    Numeric_R
    _
    Rmult_0_l
    _
    _
    Rplus_comm
    _
    Rplus_opp_r
    Rplus_0_l
    Rmult_comm
    _
    Rmult_1_l
    Rmult_plus_distr_l
    Rlt_asym
    Rlt_trans
    Rplus_lt_compat_l
    _
    _
    _

    _
    _
    _
    _
    _
    Raxioms.total_order_T
    _
    _
.
Next Obligation. lra. Qed.
Next Obligation.
  rewrite -> Rplus_comm with 1 _.
  destruct n; auto.
  simpl. rewrite Rplus_0_l. auto.
Qed.
Next Obligation. lra. Qed.
Next Obligation. lra. Qed. 
Next Obligation. 
  split; intros.
    apply Rmult_lt_compat_l; auto.
  rewrite <- Rmult_1_r.  
  rewrite <- Rmult_1_r with r1.
  rewrite -> Rinv_r_sym with r.
  2:{ apply Rlt_not_eq in H. auto. }
  repeat rewrite <- Rmult_assoc.
  apply Rmult_lt_compat_r.
    apply Rinv_0_lt_compat. auto.
  repeat rewrite -> Rmult_comm with _ r.
  auto.
Qed.
Next Obligation. lra. Qed.
Next Obligation. 
  unfold Numeric_R_obligation_2.
  destruct (Raxioms.total_order_T n m).
  {
    destruct s.
    {
      split; auto.
        intros. inversion H.
      intros.
      rewrite H in r.
      by apply Rlt_irrefl in r.
    }
    rewrite e.
    by split.
  }
  split; intros.
    inversion H.
  rewrite H in r.
  by apply Rlt_irrefl in r.
Qed.
Next Obligation.
  unfold Numeric_R_obligation_1.
  destruct (Raxioms.total_order_T n m).
  {
    destruct s.
      by split.
    split; intros.
      inversion H.
    rewrite e in H. 
    by apply Rlt_irrefl in H.
  }
  split; intros.
    inversion H.
  apply Rlt_not_le in H.
  exfalso. apply H.
  by left.
Qed.

Lemma to_R_R: forall x : R, to_R x = x.
Proof. intros. simpl. auto. Qed.


(**Undelimit Scope R_scope.
Close Scope R_scope.**)
(**Local Open Scope Z_scope.**)
Delimit Scope Z_scope with Z.


Program Instance Numeric_z : Numerics.Numeric Z :=
  @Numerics.mkNumeric
    Z
    Z.add
    Z.opp
    Z.mul
    Zpower_nat
    IZR
    Z.of_nat
    Z0
    (Zpos (1)%positive)

    Z.lt
    Z.ltb
    Z.eqb.


Program Instance Numeric_Props_z : @Numerics.Numeric_Props Z Numeric_z :=
  @Numerics.mkNumericProps
    Z
    Numeric_z
    _
    Z.mul_0_l
    _
    _
    Z.add_comm
    Z.add_assoc
    Z.add_opp_diag_r
    Z.add_0_l

    Z.mul_comm
    Z.mul_assoc
    Z.mul_1_l
    Z.mul_add_distr_l   
    Zlt_asym
    Z.lt_trans
    _
    _
    _
    _

    _
    _
    _
    _
    eq_IZR
    _
    Z.eqb_eq
    Z.ltb_lt
.
Next Obligation. lia. Qed.
Next Obligation. 
  fold (Z.of_nat n.+1).
  rewrite Nat2Z.inj_succ.
  destruct (Z.of_nat n); auto.
  simpl.
  destruct p; auto.
Qed.
Next Obligation. lia. Qed.
Next Obligation.
  split; intros.
    apply Zmult_lt_compat_l; auto.
  apply Zmult_gt_0_lt_reg_r with r.
    apply Z.lt_gt. auto.
  repeat rewrite -> Zmult_comm with _ r.
  auto.
Qed.
Next Obligation. rewrite plus_IZR. auto. Qed.
Next Obligation. rewrite mult_IZR. auto. Qed. 
Next Obligation. 
  split.
     apply IZR_lt.
  apply lt_IZR.
Qed.
Next Obligation. rewrite opp_IZR. auto. Qed.
Next Obligation.
  destruct Z_dec' with r1 r2; auto.
  destruct s; auto.
Qed.
    
    
 

  Delimit Scope R_scope with R_s.

  Infix "+" := Numerics.plus : Numeric_scope.
  Notation "- n" := (Numerics.neg n) : Numeric_scope.
  Infix "*" := Numerics.mult : Numeric_scope.
  Infix "<" := Numerics.lt : Numeric_scope.
  Infix "<=" := Numerics.le : Numeric_scope.
  Notation "1" := Numerics.mult_id : Numeric_scope.
  Notation "0" := Numerics.plus_id : Numeric_scope.
  Delimit Scope Numeric_scope with Num.
  Local Open Scope Numeric_scope.

  Section use_Numeric2.
  Context {Nt:Type} {H : Numeric Nt} `{NtProps : Numeric_Props (numeric_t := H) Nt}.

  Lemma to_R_eqb: forall (n m : Nt), eqb n m = eqb (to_R n) (to_R m).
  Proof.
    intros.
    destruct (eqb n m) eqn:e.
    { apply eqb_true_iff in e. rewrite e. rewrite eqb_refl. auto. }
    apply eqb_false_iff in e.
    assert (to_R n <> to_R m).
      unfold not. intros. apply e. apply to_R_inj. auto.
    apply eqb_false_iff in H0.
    auto.
  Qed.
  
  Lemma to_R_ltb: forall (n m : Nt), ltb n m = ltb (to_R n) (to_R m).
  Proof.
    intros.
    destruct (ltb (to_R n) (to_R m)) eqn:e.
    { apply ltb_true_iff in e. apply to_R_lt in e. apply ltb_true_iff in e. auto. }
    apply ltb_false_iff in e.
    apply not_lt_le in e.
    apply to_R_le in e.
    apply le_not_lt in e.
    apply ltb_false_iff in e.
    auto.
  Qed.

  Lemma to_R_leb: forall (n m : Nt), leb n m = leb (to_R n) (to_R m).
  Proof.
    intros.
    repeat rewrite leb_ltb_or_eqb.    
    rewrite to_R_ltb.
    rewrite to_R_eqb.
    auto.
  Qed.

  Lemma R_abs_same: forall x : R, abs x = Rabs x.
  Proof.
    intros.
    unfold abs. 
    simpl.
    destruct (le_lt_dec 0 x).
    { 
      rewrite Rabs_right.
        apply leb_true_iff in l. rewrite l. auto.
      unfold Rge.
      unfold Rgt.
      destruct l; auto.
    }
    rewrite Rabs_left; auto.
      apply lt_not_le in l. apply leb_false_iff in l. rewrite l. auto.
  Qed.

  Lemma R_dist_same: forall x y : R, abs (x + - y) = R_dist x y.
  Proof. intros. unfold R_dist. rewrite R_abs_same. auto. Qed.

  Lemma R_lt_same: forall x y : R, x < y <-> Rlt x y. 
  Proof. intros. split; auto. Qed.

  Lemma R_le_same: forall x y : R, x <= y <-> Rle x y. 
  Proof. intros. split; auto. Qed.

  Lemma Zlt_iff: forall (x y : Z), (x < y)%Z <-> lt x y.
  Proof. intros. split; auto. Qed.

  Lemma Zle_iff: forall (x y : Z), (x <= y)%Z <-> le x y.
  Proof. 
    intros.
    split; intros.
    { 
      apply Zle_lt_or_eq in H0.
      unfold le.
      destruct H0; auto. 
    }
    destruct H0; auto.
      apply Zlt_le. auto.
    rewrite H0. apply Z.le_refl.
  Qed.

 
  Definition of_Z (i : Z) : Nt :=
    match i with
    | Z0 => plus_id
    | Zpos p => of_nat (Pos.to_nat p)
    | Zneg p => neg ( of_nat (Pos.to_nat p))
    end.

End use_Numeric2.

Definition log (x y : R) := Rdiv (ln y) (ln x).
    
Lemma ln_pow: forall (x : R) (n : nat), 0 < x -> ln (x ^ n) = INR n * ln x.
Proof. 
  intros.
  induction n; auto.
    simpl. rewrite Rmult_0_l. apply ln_1.
  simpl in IHn.
  assert(INR n.+1 = INR n + 1)%R_s.
  {
    simpl.
    destruct n; auto.
    simpl.
    rewrite Rplus_0_l.
    auto.
  }
  rewrite H0.
  simpl.
  rewrite ln_mult; auto.
  {            
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    rewrite IHn.
    apply Rplus_comm.
  }
  assert( 0 < Numerics.pow_nat x n). apply Numerics.pow_gt_0. auto.
  apply H1.
Qed.

Lemma ln_le_inv: forall x y : R, (0 < x)%R_s -> (0 < y)%R_s -> (ln x <= ln y)%R_s -> (x <= y)%R_s.
Proof.
  intros.
  destruct H1.
  { unfold Rle. left. apply ln_lt_inv; auto. }
  unfold Rle. right. apply ln_inv; auto.
Qed.

Lemma log_pow: forall (x y : R) (n : nat), 0 < x -> 0 < y -> log x (y ^ n) = INR n * log x y.
Proof.
  intros.
  unfold log.
  rewrite ln_pow; auto. 
  unfold Rdiv.
  rewrite Rmult_assoc.
  auto.
Qed.
  
Lemma log_base: forall (x : R), 0 < x -> 1 <> x -> log x x = 1.
Proof.
  intros.
  unfold log.
  unfold Rdiv.
  rewrite Rinv_r; auto.
  unfold not.
  intros.
  apply H0.
  rewrite <- ln_1 in H1.
  apply ln_inv; auto.      
  assert (Numerics.to_R 0 < Numerics.to_R 1)%R_s. simpl. apply Rlt_0_1. 
  apply H2.
Qed.

Lemma log_1: forall (x : R), 0 < x -> 1 <> x -> log x 1 = 0.
Proof.
  intros.
  unfold log.
  rewrite ln_1.
  unfold Rdiv.
  rewrite Rmult_0_l.
  auto.
Qed.

Lemma log_base_pow_nat: forall (x : R) (n : nat),  0 < x -> 1 <> x ->  log x (x ^ n) = INR n.
Proof.
  intros.
  rewrite log_pow; auto.
  rewrite log_base; auto.
  apply Numerics.mult_id_r.
Qed.

Lemma log_inv: forall (x y z : R), 0 < x -> 1 <> x -> 0 < y -> 0 < z -> log x y = log x z -> y = z.
Proof.
  intros.
  unfold log in H1.
  unfold Rdiv in H1.
  apply ln_inv; auto.
  unfold log in H3.
  rewrite <- Rmult_1_r.       
  rewrite <- Rmult_1_r with (ln y).
  assert (ln x <> 0)%R_s.
    unfold not. intros. apply H0. rewrite <- ln_1 in H4. apply ln_inv; auto.
    apply Rlt_0_1.  
  rewrite <- Rinv_l with (ln x); auto.
  repeat rewrite <- Rmult_assoc.
  unfold Rdiv in H3.
  rewrite H3. auto.
Qed.

(**forall (v : value_func p_props) (n m : nat),
   (1 + - discount) *
   value_dist p_props (value_iteration_rec p_props discount v n)
     (value_iteration_rec p_props discount v (n + m)) <=
   value_dist p_props v (value_iteration_step p_props discount v) *
   pow_nat discount n**)

Lemma log_lt_inv:  forall (x y z : R), 1 < x -> 0 < y -> 0 < z -> log x y < log x z -> y < z.
Proof.
  intros.
  unfold log in H2.
  assert (ln x <> 0%R_s).
  { unfold not.
    intros.
    rewrite <- ln_1 in H3.
    apply ln_inv in H3; auto.
      rewrite H3 in H. apply Numerics.lt_irrefl in H. auto.
      apply Rlt_trans with 1; auto. apply Rlt_0_1.
    apply Rlt_0_1.
  }
  unfold Rdiv in H2.
  rewrite <- mult_lt_compat_r in H2.
    apply ln_lt_inv; auto.
  apply Rinv_0_lt_compat.
  rewrite <- ln_1.
  apply ln_increasing; auto.
  apply Rlt_0_1.
Qed.


Lemma log_le_inv:  forall (x y z : R), 1 < x -> 0 < y -> 0 < z -> log x y <= log x z -> y <= z.
Proof.
  intros.
  unfold Numerics.le.
  destruct H2.
    apply log_lt_inv in H2; auto.
  apply log_inv in H2; auto.
    apply Numerics.lt_trans with 1; auto. apply Rlt_0_1.
  apply Numerics.lt_not_eq. auto.
Qed.

Lemma gt0_lt1_inv_gt1: forall x : R, 0 < x -> x < 1 -> 1 < Rinv x.
Proof.
  intros.
  assert (1 = 1%R_s). auto.
  rewrite H1.
  rewrite <- Rinv_l with 1.
  2: { apply Numerics.lt_not_eq in H0. simpl. auto. }
  rewrite Rmult_1_r.
  apply Rinv_lt_contravar; auto.
  rewrite Rmult_1_r.
  auto.
Qed.

Lemma log_lt1_lt_inv:  forall (x y z : R), 0 < x -> x < 1 -> 0 < y -> 0 < z -> log x y < log x z -> z < y.
Proof.
  intros.
  apply log_lt_inv with (Rinv x); auto.
    apply gt0_lt1_inv_gt1; auto.
  unfold log in *.
  repeat rewrite ln_Rinv; auto.
  unfold Rdiv in *.
  rewrite <- Ropp_inv_permute; auto.
  2: {
    unfold not. intros.
    rewrite <- ln_1 in H4.
    apply ln_inv in H4; auto.
      rewrite H4 in H0. apply Numerics.lt_irrefl in H0. auto.
    apply Rlt_0_1.
  }
  repeat rewrite <- Ropp_mult_distr_r.
  apply Ropp_gt_lt_contravar.
  auto.
Qed.

Lemma log_lt1_le_inv:  forall (x y z : R), 0 < x -> x < 1 -> 0 < y -> 0 < z -> log x y <= log x z -> z <= y.
Proof.
  intros.
  unfold Numerics.le.
  destruct H3.
    apply log_lt1_lt_inv in H3; auto.
  apply log_inv in H3; auto.
  apply Numerics.lt_not_eq in H0.
  auto.
Qed.

  Lemma exists_pow_le: forall x y : R, 0 < x -> x < 1 -> 0 < y -> exists n, x ^ n <= y.
  Proof.
    intros.
    exists (Z.to_nat (up (log x y))).
    apply log_lt1_le_inv with x; auto.
      apply pow_lt. auto. 
    rewrite log_base_pow_nat; auto.
    2:{ apply lt_not_eq in H0. auto. }
    rewrite INR_IZR_INZ.
    destruct (le_lt_dec 0 (up (log x y))).
    {
      rewrite Z2Nat.id; auto.
      2: { apply Zle_iff. auto. }
      apply Rge_le.
      unfold Rge.
      left.
      apply archimed.
    }
    apply le_lt_weak.
    apply lt_le_trans with 0.
    {
      apply lt_trans with (IZR (up (log x y))).
        apply Rgt_lt. apply archimed.
      apply IZR_lt. auto.
    }
    apply IZR_le.
    apply Nat2Z.is_nonneg.
  Qed.

  Lemma exists_pow_lt: forall x y : R, 0 <= x -> x < 1 -> 0 < y -> exists n, x ^ n < y.
  Proof.
    intros.
    destruct H.
    2: { exists (S O). rewrite <- H. rewrite pow_1. auto. } 
    destruct exists_pow_le with x y; auto.
    exists x0.+1.
    apply lt_le_trans with (x ^ x0); auto.
    simpl.
    rewrite <- mult_id_l.
    apply Rmult_lt_compat_r; auto.
    apply pow_lt. auto.
  Qed.    

  Lemma R_plus_id_same: plus_id = 0%R_s.
  Proof. auto. Qed.

  Lemma R_mult_id_same: mult_id = 1%R_s.
  Proof. auto. Qed.


  Section use_Numeric3.
  Context {Nt : Type } `{Numeric_Props Nt}.

  Lemma exists_pow_nat_le: forall x y : Nt, 0 < x -> x < 1 -> 0 < y -> exists n, Numerics.pow_nat x n <= y.
  Proof.
    intros.
    destruct exists_pow_le with (to_R x) (to_R y); auto.
    { simpl; rewrite <- to_R_plus_id; apply to_R_lt; auto. }
    { simpl; rewrite <- to_R_mult_id; apply to_R_lt; auto. }
    { simpl; rewrite <- to_R_plus_id; apply to_R_lt; auto. }
    exists x0.
    rewrite <- to_R_pow_nat in H3.
    apply to_R_le.
    auto.
  Qed.
  
  Lemma exists_pow_nat_lt: forall x y : Nt, 0 <= x -> x < 1 -> 0 < y -> exists n, Numerics.pow_nat x n < y.
  Proof.
    intros.
    destruct exists_pow_lt with (to_R x) (to_R y); auto; simpl;
      try rewrite <- to_R_plus_id; try rewrite <- to_R_mult_id;
      try rewrite <- to_R_le; try rewrite <- to_R_lt; auto.
    exists x0.
    rewrite <- to_R_pow_nat in H3.
    apply to_R_lt.
    auto.
  Qed.


  End use_Numeric3.


End Numerics.

Infix "+" := Numerics.plus : Numeric_scope.
Notation "- n" := (Numerics.neg n) : Numeric_scope.
Infix "*" := Numerics.mult : Numeric_scope.
Infix "<" := Numerics.lt : Numeric_scope.
Infix "<=" := Numerics.le : Numeric_scope.
Notation "1" := Numerics.mult_id : Numeric_scope.
Notation "0" := Numerics.plus_id : Numeric_scope.



Close Scope Numeric_scope.
Undelimit Scope Numeric_scope.


Section int_to_Z.
  Variable i : int.

  Definition int_to_nat i :=
    match i with
    | Posz n => n
    | Negz n => S n
    end.

  Definition int_to_positive : positive :=
    match i with
    | Posz n => Pos.of_nat n
    | Negz n => Pos.of_succ_nat n
    end.

  Definition int_to_Z : Z :=
    match i with
    | Posz n => Z.of_nat n
    | Negz n => Z.neg (Pos.of_succ_nat n)
    end.

  Lemma posint_to_positive (H : (0< i)%R) :
    Z.pos int_to_positive = int_to_Z.
  Proof.
    rewrite /int_to_positive /int_to_Z.
    case: i H=> //.
    move=> n H.
    rewrite -positive_nat_Z.
    f_equal.
    rewrite Nat2Pos.id=> //.
    by move=> H2; rewrite H2 in H.
  Qed.
End int_to_Z.


Lemma pos_of_succ_nat_mul n m :
  (Pos.of_succ_nat n * Pos.of_succ_nat m)%positive =
  Pos.of_succ_nat (m + (n * m.+1)%Nrec).
Proof.
  elim: n=> //=.
  by rewrite addn0.
  move=> n IH.
  rewrite Pos.mul_succ_l IH.
  rewrite -mulnE mulnS.
  rewrite 3!Pos.of_nat_succ.
  by rewrite -Nat2Pos.inj_add.
Qed.

Lemma opp_posz_negz (n : nat) : GRing.opp (Posz (n.+1)) = Negz n.
Proof. by elim: n. Qed.

Lemma pos_sub_pred p : Z.pos_sub p 1 = Z.pred (Z.pos p).
Proof.
  set (P := fun p0 => Z.pos_sub p0 1 = Z.pred (Z.pos p0)).
  change (P p).
  by apply: positive_ind.
Qed.  

Lemma pos_sub_succ1 m : 
  Z.pos_sub (Pos.of_succ_nat m.+1) 1 = Z.pos (Pos.of_succ_nat m).
Proof.
  rewrite pos_sub_pred.
  rewrite 2!Zpos_P_of_succ_nat.
  rewrite -!Zpred_succ /=.
  by rewrite Zpos_P_of_succ_nat.
Qed.

Lemma pos_sub_succ m n :  
  Z.pos_sub (Pos.succ (Pos.of_succ_nat m)) (Pos.of_succ_nat n) =
  Z.succ (Z.pos_sub (Pos.of_succ_nat m) (Pos.of_succ_nat n)).
Proof.
  rewrite -Pos2Z.add_pos_neg.
  rewrite Pos2Z.inj_succ.
  by rewrite Z.add_comm Z.add_succ_r.
Qed.

Lemma pos_sub_1succ n : 
  Z.pos_sub 1 (Pos.succ (Pos.of_succ_nat n)) =
  Z.neg (Pos.of_succ_nat n).
Proof.
  elim: n=> //= n IH.
  rewrite -Z.pos_sub_opp.
  rewrite -[Pos.succ (Pos.of_succ_nat n)]Pos2SuccNat.id_succ.
  by rewrite pos_sub_succ1.
Qed.
    
Lemma pos_of_succ_nat_sub n m :
  Z.pos_sub (Pos.of_succ_nat n) (Pos.of_succ_nat m) =
  int_to_Z (Posz n - Posz m).
Proof.
  elim: n m=> //= m.
  rewrite sub0r.
  case: m=> [//|m'].
  rewrite opp_posz_negz. simpl.
  rewrite -SuccNat2Pos.inj_succ.
  rewrite -Z.pos_sub_opp.
  rewrite -Pos2Z.opp_pos.
  f_equal.
  rewrite pos_sub_pred.
  rewrite Zpos_P_of_succ_nat.
  by rewrite -Zpred_succ.
  move=> IH n /=.
  rewrite pos_sub_succ.
  rewrite IH.
  rewrite /int_to_Z.
  rewrite intS.
  rewrite -addrA.
  case: (Posz m - Posz n)%R=> n'.
  { by rewrite /= Zpos_P_of_succ_nat. }
  move {IH m n}.
  elim: n'=> // n /= IH.
  have H: (subn n.+1 1 = n) by move {IH}; elim: n.
  by rewrite H pos_sub_1succ.
Qed.  

Lemma pos_of_succ_nat_plus n m : 
  (Pos.of_succ_nat n + Pos.of_succ_nat m)%positive =
  Pos.succ (Pos.of_succ_nat (n + m)).
Proof.
  elim: n m=> // m.
  rewrite add0n.
  rewrite Pos.of_nat_succ.
  by rewrite Pos.add_1_l.
  move=> IH m'.
  simpl.
  rewrite Pos.add_succ_l.
  by rewrite IH.
Qed.

Lemma int_to_Z_add_sub s r :
  int_to_Z (s + Negz r) = int_to_Z (s - (Posz r.+1)).
Proof. by elim: s. Qed.

Lemma int_to_Z_plus (s r : int) :
  Zplus (int_to_Z s) (int_to_Z r) = int_to_Z (s + r).
Proof.
  case: s=> sn.
  case: r=> rn.
  simpl.
  by rewrite -Nat2Z.inj_add.
  { simpl.
    rewrite /Z.of_nat.
    case: sn=> [|sn'].
    { by rewrite add0r Zplus_0_l. }
    rewrite Pos2Z.add_pos_neg.
    rewrite int_to_Z_add_sub.
    rewrite subzSS.
    by rewrite pos_of_succ_nat_sub.
  }
  case: r=> rn.
  { simpl.
    rewrite /Z.of_nat.
    case: rn=> [|rn'].
    by simpl; rewrite subn0.
    rewrite pos_of_succ_nat_sub.
    symmetry; rewrite addrC.
    rewrite int_to_Z_add_sub.
    by rewrite subzSS.
  }
  simpl.
  f_equal.
  by rewrite pos_of_succ_nat_plus.
Qed.

Lemma of_succ_nat_of_nat_plus_1 (n : nat):
  Pos.of_succ_nat n = Pos.of_nat (n + 1).
Proof.
  elim n. auto.
  move => n' IHn /=.
  case H: ((n' + 1)%Nrec).
  by rewrite -addnE addn1 in H; congruence.
  by rewrite -H -addnE IHn.
Qed.

Lemma le_plus_minus_r (a : nat):
  (0 < a)%N ->
  a = (a - 1 + 1)%N.
Proof. move => H. by rewrite addnC subnKC. Qed.

Lemma int_to_positive_mul_1 (a b : nat) (H : (a <> 0)%N) :
  (a * b.+1)%N = ((a * b.+1 - 1).+1)%N.
Proof.
   rewrite -[(_ * _ - 1).+1] addn1 -le_plus_minus_r //. rewrite muln_gt0.
   apply /andP. split; auto. rewrite lt0n. apply /eqP. auto.
Qed.

Lemma foiln (a b c d : nat) :
  ((a + b) * (c + d) = a * c + b * c + a * d + b * d)%N.
Proof. by rewrite mulnDr mulnDl mulnDl addnA. Qed.

Lemma int_to_positive_mul (s r : int) :
  s <> Posz(0%N) ->
  r <> Posz(0%N) ->
  int_to_positive (s * r) = Pos.mul (int_to_positive s) (int_to_positive r).
Proof.
  case: s=> sn; move => Hs.
  - case: r=> rn; move => Hr.
    + simpl. rewrite Nat2Pos.inj_mul //; auto.
    + rewrite /GRing.mul /=. 
      have H0: ((sn * rn.+1)%N = ((sn * rn.+1 - 1).+1)%N).
      { apply: int_to_positive_mul_1. auto. }
      rewrite H0 -NegzE /= of_succ_nat_of_nat_plus_1 addn1 -H0.
      rewrite Nat2Pos.inj_mul; auto.
      rewrite of_succ_nat_of_nat_plus_1 addn1 //.
  - case: r=> rn; move => Hr.
      + rewrite /GRing.mul /=. 
        have H0: ((rn * sn.+1)%N = ((rn * sn.+1 - 1).+1)%N).
        { apply: int_to_positive_mul_1. auto. }
        rewrite H0 -NegzE /= of_succ_nat_of_nat_plus_1 addn1 -H0 mulnC.
        rewrite Nat2Pos.inj_mul; auto.
        rewrite of_succ_nat_of_nat_plus_1 addn1 //.
      + rewrite /GRing.mul /=.
        case H0: ((rn + (sn * rn.+1)%Nrec)%coq_nat).
        * have ->: ((rn = 0)%N).
          { rewrite -mulnE in H0. omega. }
          have ->: ((sn = 0)%N).
          { rewrite -mulnE -addn1 in H0.
            case H1: (sn == 0%N).
            move: H1 => /eqP H1. apply H1.
            move: H1 => /eqP /eqP H1. rewrite -lt0n in H1.
            have H2: ((0 < rn + sn * (rn + 1))%N).
            { rewrite addn_gt0. apply /orP. right. rewrite muln_gt0.
              apply /andP. split. auto. rewrite addn1 //. }
            have H3: ((rn + sn * (rn + 1))%N = 0%N). apply H0.
            rewrite H3 in H2. inversion H2. }
            by [].
        * rewrite -H0 -mulnE -Nat2Pos.inj_succ -add1n addnC.
          rewrite !of_succ_nat_of_nat_plus_1 -add1n -Nat2Pos.inj_mul.
          rewrite mulnDr muln1 addnC 2!addnA.
          have ->: (Pos.of_nat ((sn + 1) * (rn + 1))%coq_nat =
                    Pos.of_nat ((sn + 1) * (rn + 1))) by [].
          rewrite foiln mul1n !muln1 addnC addnA [(1 + _)%N] addnC.
          rewrite addnA -addnA [(1 + _)%N] addnC addnA //.
          by rewrite addn1.
          by rewrite addn1.
          rewrite -mulnE in H0. by rewrite addn1 H0.
Qed.

Lemma int_to_positive_inj_pos s r :
  @ltr int_numDomainType
       (GRing.zero (Num.NumDomain.zmodType int_numDomainType)) s ->
  @ltr int_numDomainType
       (GRing.zero (Num.NumDomain.zmodType int_numDomainType)) r ->
  int_to_positive s = int_to_positive r ->
  s = r.
Proof.
  rewrite /int_to_positive.
  case: s; case: r => n1 n2 pf1 pf2 H.
  have ->: (n2 = n1).
  { apply Nat2Pos.inj => //. by destruct n2. by destruct n1. }
  by [].
  inversion pf2. inversion pf1.
  apply SuccNat2Pos.inj in H.
  by rewrite H.
Qed.

Lemma int_to_Z_mul (s r : int) :
  Zmult (int_to_Z s) (int_to_Z r) = int_to_Z (s * r).
Proof.
  case: s=> sn.
  case: r=> rn.
  simpl.
  by rewrite -Nat2Z.inj_mul.
  { simpl.
    rewrite /Z.of_nat.
    case: sn=> [//=|sn'].
    rewrite mulrC /=.
    f_equal.
    by rewrite pos_of_succ_nat_mul.
  }
  case: r=> rn.
  { simpl.
    rewrite /Z.of_nat.
    case: rn=> [//=|rn'].
    rewrite mulrC /=.
    f_equal.
    rewrite pos_of_succ_nat_mul.
    rewrite -mulnE.
    rewrite 2!mulnS.
    rewrite mulnC.
    rewrite addnA.
    rewrite [(rn' + sn)%N]addnC.
    by rewrite -addnA.
  }
  simpl.
  f_equal.
  by rewrite pos_of_succ_nat_mul.
Qed.

Lemma Zneg_Zlt r s :
  Pos.gt r s -> 
  Z.lt (Zneg r) (Zneg s).
Proof.
  rewrite /Pos.gt.
  by rewrite /Z.lt /= => ->.
Qed.  

Lemma Zlt_Zneg r s :
  Z.lt (Zneg r) (Zneg s) ->
  Pos.gt r s.
Proof.
  rewrite /Pos.gt.
  rewrite /Z.lt /=.
  case: (r ?= s)%positive => //.
Qed.  

Lemma Psucc_gt r s :
  Pos.gt (Pos.of_succ_nat r) (Pos.of_succ_nat s) ->
  (r > s)%coq_nat.
Proof.
  rewrite /Pos.gt -SuccNat2Pos.inj_compare /gt -nat_compare_gt.
  omega.
Qed.

Lemma Zneg_Zle r s :
  Pos.ge r s -> 
  Z.le (Zneg r) (Zneg s).
Proof.
  rewrite /Pos.ge /Z.le /= => H; rewrite /CompOpp.
  by move: H; case: (r ?= s)%positive.
Qed.

Lemma int_to_Z_lt (s r : int) :
  ltr s r ->
  Z.lt (int_to_Z s) (int_to_Z r).
Proof.
  case: s=> sn; case: r=> rn //.
  { simpl.
    move=> H; apply: inj_lt.
    rewrite /ltr /= in H.
    by apply/leP.
  }
  { simpl=> H.
    have H2: (Z.lt (Z.neg (Pos.of_succ_nat sn)) 0).
    { by apply: Zlt_neg_0. }
    apply: Z.lt_le_trans.
    apply: H2.
      by apply: Zle_0_nat.
  }
  simpl.
  rewrite /ltr /= => H.
  apply: Zneg_Zlt.
  move: (inj_lt _ _ (leP H)).
  rewrite 2!Pos.of_nat_succ => H2.
  rewrite /Pos.gt.
  rewrite -Nat2Pos.inj_compare=> //.
  move: H.
  move/leP. 
  simpl.
  by rewrite Nat.compare_gt_iff.
Qed.  

Lemma int_to_Z_inj (a b : int) :
  int_to_Z a = int_to_Z b ->
  a = b.
Proof.
  rewrite /int_to_Z.
  case a=>n; case b=>n0; move => H.
  apply Nat2Z.inj_iff in H. auto.
  have H1: (Z.le 0 (Z.of_nat n)).
  { apply Nat2Z.is_nonneg. }
  have H2: (Z.lt (Z.neg (Pos.of_succ_nat n0)) 0).
  { apply Zlt_neg_0. }
  omega.
  have H1: (Z.le 0 (Z.of_nat n0)).
  { apply Nat2Z.is_nonneg. }
  have H2: (Z.lt (Z.neg (Pos.of_succ_nat n)) 0).
  { apply Zlt_neg_0. }
  omega.
  inversion H. apply SuccNat2Pos.inj_iff in H1. auto.
Qed.

Lemma lt_int_to_Z (s r : int) :
  Z.lt (int_to_Z s) (int_to_Z r) ->
  ltr s r.  
Proof.
  case: s=> sn; case: r=> rn //.
  { by rewrite /= -Nat2Z.inj_lt /ltr /=; case: (@ltP sn rn). }
  { simpl=> H.
    have H2: (Z.lt (Z.neg (Pos.of_succ_nat sn)) 0).
    { by apply: Zlt_neg_0. }
    have H3: (Z.lt (Z.of_nat sn) 0)%Z.
    { apply: Z.lt_trans; first by apply: H.
        by []. }
    clear - H3; case: sn H3 => //. } 
  simpl.
  rewrite /ltr /= => H.
  have H2: (sn > rn)%coq_nat. 
  { move: (Zlt_Zneg H).
    apply: Psucc_gt. }
  clear - H2.
  apply/ltP; omega.
Qed.


Lemma le_int_to_Z (s r : int) :
  Z.le (int_to_Z s) (int_to_Z r) ->
  ler s r.  
Proof.
  
  move/Zle_lt_or_eq; case; first by move/lt_int_to_Z; apply/ltrW.
  move/int_to_Z_inj => -> //.
Qed.  

Lemma int_to_Z_le (s r : int) :
  ler s r ->
  Z.le (int_to_Z s) (int_to_Z r).
Proof.
  case: s=> sn; case: r=> rn //.
  { simpl.
    move=> H; apply: inj_le.
    by apply/leP.
  }
  { simpl=> H.
    have H2: (Z.le (Z.neg (Pos.of_succ_nat sn)) 0).
    { by apply: Pos2Z.neg_is_nonpos. }
    apply: Z.le_trans.
    apply: H2.
    by apply: Zle_0_nat.
  }
  simpl.
  rewrite /ler /= => H.
  apply: Zneg_Zle.
  move: (inj_le _ _ (leP H)).
  rewrite 2!Pos.of_nat_succ => H2.
  rewrite /Pos.ge.
  rewrite -Nat2Pos.inj_compare=> //.
  move: H.
  move/leP. 
  simpl.
  by rewrite Nat.compare_ge_iff.
Qed.  

Section rat_to_Q.
  Variable r : rat.
  
  Definition rat_to_Q : Q :=
    let: (n, d) := valq r in
    Qmake (int_to_Z n) (int_to_positive d).
End rat_to_Q.

Section rat_to_Q_lemmas.
  Local Open Scope ring_scope.
  Delimit Scope R with R_ssr.  
  Delimit Scope R_scope with R.

  Lemma rat_to_Q0 : rat_to_Q 0 = inject_Z 0.
  Proof. by []. Qed.
  
  Lemma Z_of_nat_pos_of_nat (a : nat):
    (0 < a)%N ->
    Z.of_nat a =
    Z.pos (Pos.of_nat a).
  Proof.
    rewrite /Z.of_nat. case: a. move => H. inversion H.
    move => n H. rewrite of_succ_nat_of_nat_plus_1. rewrite addn1.
      by [].
  Qed.

  Lemma int_to_Z_pos_of_nat (a : nat):
    (0 < a)%N ->
    int_to_Z (Posz a) =
    Z.pos (Pos.of_nat a).
  Proof.
    case: a. move => H. inversion H.
    move => n H. by rewrite -Z_of_nat_pos_of_nat.
  Qed.

  Lemma int_to_Z_pos_of_nat_mul (a : int) (b : nat) (H : (0 < b)%N):
    Zmult (int_to_Z a) (Z.pos (Pos.of_nat b)) = int_to_Z (a * Posz b).
  Proof.
    rewrite -int_to_Z_pos_of_nat //. by rewrite int_to_Z_mul.
  Qed.

  Lemma int_to_Z_inj_iff (a b : int) :
    int_to_Z a = int_to_Z b <-> a = b.
  Proof.
    split. apply: int_to_Z_inj. move => H. by rewrite H. Qed.

  Lemma int_to_Z_opp (i : int) :
    int_to_Z (- i) = Z.opp (int_to_Z i).
  Proof.
    have ->: - i = -1 * i by rewrite mulNr mul1r.
    have ->: (Z.opp (int_to_Z i) = Zmult (Zneg xH) (int_to_Z i)).
    { by rewrite Z.opp_eq_mul_m1 Z.mul_comm. }
    rewrite -int_to_Z_mul. f_equal.
  Qed.

  Lemma pos_muln (a b : nat) :
    Posz a * Posz b = Posz (muln a b).
  Proof. by []. Qed.

  Lemma le_0_pos_num_gcdn (a b : int) (H : 0 < a) :
    (0 < `|a| %/ gcdn `|b| `|a|)%N.
  Proof.
    rewrite divn_gt0.
    {
      apply dvdn_leq => //.
      rewrite absz_gt0.
      rewrite ltr_neqAle in H.
      case/andP: H => H1 H4.
      apply/eqP.
      move/eqP: H1 => H1 H5.
      symmetry in H5. contradiction.
      by apply: dvdn_gcdr.
    }
    {
      rewrite gcdn_gt0. apply/orP; right.
      rewrite absz_gt0.
      rewrite ltr_neqAle in H.
      case/andP: H => H1 H4.
      apply/eqP.
      move/eqP: H1 => H1 H5.
      symmetry in H5. contradiction.
    }
  Qed.

  Lemma le_0_neg_num_gcdn (a b : int) (H : 0 < b) (H2 : a < 0) :
    (0 < `|a| %/ gcdn `|a| `|b|)%N.
  Proof.
    rewrite divn_gt0.
    {
      case: (dvdn_gcdl `|a| `|b|)%N => H3.
      apply dvdn_leq => //.
      rewrite absz_gt0.
      rewrite ltr_neqAle in H2.
      case/andP: H2 => //.
    }
    {
      rewrite gcdn_gt0. apply/orP; right.
      rewrite absz_gt0.
      rewrite ltr_neqAle in H.
      case/andP: H => H1 H4.
      apply/eqP.
      move/eqP: H1 => H1 H5.
      symmetry in H5. contradiction.
    }
  Qed.

  Lemma int_to_positive_to_Z (a : int) :
    0 < a ->
    Z.pos (int_to_positive a) = int_to_Z a.
  Proof.
    rewrite /int_to_positive.
    rewrite /int_to_Z.
    case: a=> an H.
      by rewrite Z_of_nat_pos_of_nat.
      inversion H.
  Qed.

  Lemma rat_to_Q_fracq_pos_leib (x y : int) :
    0 < y ->
    coprime `|x| `|y| ->
      (rat_to_Q (fracq (x,y))) = (int_to_Z x # int_to_positive y).
  Proof.
    move=> H0 H1.
    rewrite /fracq /rat_to_Q /=.
    rewrite gtr_eqF => //=.
    rewrite ltr_gtF => //=.
    rewrite /int_to_Z.
    case_eq x => n H2 => /=.
    {
      have H: gcdn n `|y| == 1%N.
      {
        rewrite /coprime in H1.
        apply /eqP.
        move/eqP: H1 => H1.
        rewrite -H1. subst => //.
      }
      move/eqP: H => H.
      rewrite H !div.divn1 mul1n.
      f_equal => //.
      induction y => //.
    }
    {
      rewrite NegzE in H2.
      have H: gcdn n.+1 `|y| == 1%N.
      {
        rewrite /coprime in H1.
        apply /eqP.
        move/eqP: H1 => H1.
        rewrite -H1. subst => //.
      }
      move/eqP: H => H.
      rewrite H !div.divn1 expr1z => /=.
      f_equal. do 2 f_equal.
      rewrite /muln_rec Nat.mul_1_r => //.
      induction y => //.
    }
  Qed.
  
  Lemma rat_to_Q_fracq_pos (x y : int) :
    0 < y -> 
    Qeq (rat_to_Q (fracq (x, y))) (int_to_Z x # int_to_positive y).
  Proof.
    move=> H.
    rewrite /fracq /rat_to_Q /=.
    have ->: (y == 0) = false.
    { rewrite lt0r in H. move: H => /andP [H1 H2].
      apply /eqP. apply /eqP. apply H1. }
    rewrite -int_to_Z_mul.
    have ->: y < 0 = false.
    { rewrite ltrNge in H. move: H => /negP H. apply /negP. auto. }
    simpl.
    case H2: (x < 0).
    { rewrite /nat_of_bool.
      rewrite expr1z.
      rewrite /Qeq /Qnum /Qden.
      rewrite posint_to_positive => //.
      rewrite Z_of_nat_pos_of_nat; last by apply: le_0_neg_num_gcdn.
      rewrite int_to_Z_pos_of_nat_mul; last by apply: le_0_neg_num_gcdn.
      rewrite int_to_Z_mul.
      rewrite -int_to_Z_pos_of_nat; last by apply: le_0_pos_num_gcdn.
      rewrite int_to_Z_mul.
      apply int_to_Z_inj_iff.
      rewrite [_%N * y] mulrC mulrA [y * -1] mulrC -mulrA.
      have H1: (`|y| = y%N) by apply: gtz0_abs.
      rewrite -{1}H1.
      have H3: ((@normr int_numDomainType y) = absz y) by [].
      rewrite H3 /=. rewrite pos_muln -muln_divCA_gcd.
      rewrite mulN1r -pos_muln -mulNr.
      have H4: (`|x| = - x).
      { apply ltz0_abs. by apply: H2. }
      have H5: ((@normr int_numDomainType x) = absz x) by [].
      by rewrite -H5 H4 opprK. }
    rewrite /nat_of_bool /Qeq /Qnum /Qden expr0z.
    apply negbT in H2. rewrite -lerNgt in H2.
    move: H2. case: x => xn H2; last by inversion H2.
    { rewrite lez_nat leq_eqVlt in H2.
      move: H2 => /orP [H2|H2].
      move: H2 => /eqP H2. subst.
      rewrite div0n /= //.
      rewrite Z_of_nat_pos_of_nat;
        last by rewrite gcdnC; apply: le_0_pos_num_gcdn.
      rewrite !int_to_Z_pos_of_nat_mul;
        try (rewrite gcdnC; apply: le_0_pos_num_gcdn => //);
        try (apply le_0_pos_num_gcdn => //).
      rewrite mul1r.
      rewrite int_to_positive_to_Z //.
      rewrite int_to_Z_mul.
      rewrite int_to_Z_inj_iff.
      rewrite mulrC.
      have H1: (`|y| = y%N) by apply: gtz0_abs.
      rewrite -{1}H1.
      have H3: ((@normr int_numDomainType y) = absz y) by [].
      rewrite H3 /=. rewrite 2!pos_muln. 
      by rewrite -muln_divCA_gcd. }
  Qed.

  Lemma lt_and_P_ne_0 (x : int) P :
    (0 < x) && P ->
    x <> 0.
  Proof.
    move => /andP [H0 H1].
    case H2: (x == 0).
    move: H2 => /eqP H2. by rewrite H2 in H0.
    by move: H2 => /eqP H2.
  Qed.
    
  Lemma rat_to_Q_plus (r s : rat) :
    Qeq (rat_to_Q (r + s)) (Qplus (rat_to_Q r) (rat_to_Q s)).
  Proof.
    rewrite /GRing.add /= /addq /addq_subdef.
    case: r; case=> a b /= H.
    case: s; case=> c d /= H2.
    have H3: (0 < b * d).
    { case: (andP H) => X _.
      case: (andP H2) => Y _.
      apply: mulr_gt0 => //. }
    rewrite rat_to_Q_fracq_pos => //.
    rewrite /rat_to_Q /=.
    rewrite /Qplus /=.
    rewrite int_to_positive_mul.
    rewrite -int_to_Z_plus.
    rewrite -2!int_to_Z_mul.
    rewrite posint_to_positive.
    rewrite posint_to_positive.
    by [].
    by case: (andP H).
    by case: (andP H2).
    apply: lt_and_P_ne_0 H.
    apply: lt_and_P_ne_0 H2.
  Qed.
  
  Lemma rat_to_Q_mul (r s : rat) :
    Qeq (rat_to_Q (r * s)) (Qmult (rat_to_Q r) (rat_to_Q s)).
  Proof.
    rewrite /GRing.mul /= /mulq /mulq_subdef /=.
    case: r; case => a b /= i.
    case: s; case => a' b' /= i'.
    have H3: (0 < b * b').
    { case: (andP i) => X _.
      case: (andP i') => Y _.
      apply: mulr_gt0 => //. }
    rewrite rat_to_Q_fracq_pos => //.
    rewrite /rat_to_Q /=.
    rewrite /Qmult /=.
    rewrite int_to_positive_mul.
    by rewrite -int_to_Z_mul.
    apply: lt_and_P_ne_0 i.
    apply: lt_and_P_ne_0 i'.
  Qed.

  Lemma rat_to_Q_lt' r s :
    Qlt (rat_to_Q r) (rat_to_Q s) -> r < s.
  Proof.
    rewrite /Qlt /rat_to_Q; case: r => x y /=; case: s => z w /=.
    case: x y => x1 z2 /= y; case: z w => z1 x2 /= w.
    case: (andP y) => H1 H2.
    case: (andP w) => H3 H4.    
    rewrite int_to_positive_to_Z => //.
    rewrite int_to_positive_to_Z => //.
    rewrite /ltr /= /lt_rat /numq /denq /=.
    rewrite 2!int_to_Z_mul.
    apply: lt_int_to_Z.
  Qed.

  Lemma lt_rat_to_Q r s :
    r < s -> Qlt (rat_to_Q r) (rat_to_Q s).
  Proof.
    rewrite /Qlt /rat_to_Q; case: r => x y /=; case: s => z w /=.
    case: x y => x1 z2 /= y; case: z w => z1 x2 /= w.
    case: (andP y) => H1 H2.
    case: (andP w) => H3 H4.    
    rewrite int_to_positive_to_Z => //.
    rewrite int_to_positive_to_Z => //.
    rewrite /ltr /= /lt_rat /numq /denq /=.
    rewrite 2!int_to_Z_mul.
    apply: int_to_Z_lt.
  Qed.

  Lemma le_rat_to_Q r s :
    r <= s -> Qle (rat_to_Q r) (rat_to_Q s).
Proof.
  intros.
  rewrite ler_eqVlt in H.
  case/orP: H.
  move/eqP => H.
  rewrite H. apply Qle_refl.
  move => H.
  apply Qlt_le_weak.
  apply lt_rat_to_Q => //.
Qed.

End rat_to_Q_lemmas.    

Section rat_to_R.
  Variable r : rat.

  Definition rat_to_R : R := Q2R (rat_to_Q r).
End rat_to_R.

Section rat_to_R_lemmas.
  Local Open Scope ring_scope.
  Delimit Scope R_scope with R.
  
  Lemma rat_to_R0 : rat_to_R 0 = 0%R.
  Proof. by rewrite /rat_to_R /rat_to_Q /= /Q2R /= Rmult_0_l. Qed.

  Lemma rat_to_R1 : rat_to_R 1 = 1%R.
  Proof. by rewrite /rat_to_R /rat_to_Q /= /Q2R /= Rmult_1_l Rinv_1. Qed.

  Lemma rat_to_R2 : rat_to_R 2%:R = 2%R.
  Proof. by rewrite /rat_to_R /rat_to_Q /= /Q2R /= Rinv_1 Rmult_1_r. Qed.
  
  Lemma rat_to_R_lt (r s : rat) :
    lt_rat r s ->
    (rat_to_R r < rat_to_R s)%R.
  Proof.
    move=> H.
    rewrite /rat_to_R /rat_to_Q /=.
    apply: Qlt_Rlt.
    rewrite /Qlt.
    case: r H; case=> r1 r2 /= H1.
    case: s; case=> s1 s2 /= H2.
    rewrite /lt_rat /numq /denq /= => H3.
    case: (andP H1)=> H1a _.
    case: (andP H2)=> H2a _.
    rewrite !posint_to_positive=> //.
    rewrite 2!int_to_Z_mul.
    by apply: int_to_Z_lt.
  Qed.

  Lemma rat_to_R_le (r s : rat) :
    le_rat r s ->
    (rat_to_R r <= rat_to_R s)%R.
  Proof.
    move=> H.
    rewrite /rat_to_R /rat_to_Q /=.
    apply: Qle_Rle.
    rewrite /Qle.
    case: r H; case=> r1 r2 /= H1.
    case: s; case=> s1 s2 /= H2.
    rewrite /le_rat /numq /denq /= => H3.
    case: (andP H1)=> H1a _.
    case: (andP H2)=> H2a _.
    rewrite !posint_to_positive=> //.
    rewrite 2!int_to_Z_mul.
    by apply: int_to_Z_le.
  Qed.

  Lemma rat_to_R_le' (r s : rat) :
    (rat_to_R r <= rat_to_R s)%R ->
    le_rat r s.    
  Proof.
    rewrite /rat_to_R /rat_to_Q /=.
    move/Rle_Qle.
    case: r; case=> r1 r2 /= H1.
    case: s; case=> s1 s2 /= H2.
    rewrite /le_rat /numq /denq /= => H3.
    rewrite /Qle in H3.
    case: (andP H1)=> H1a _.
    case: (andP H2)=> H2a _.
    rewrite !posint_to_positive in H3=> //.
    rewrite 2!int_to_Z_mul in H3.
    by apply: le_int_to_Z.
  Qed.
  
  Lemma rat_to_R_plus (r s : rat) :
    rat_to_R (r + s) = (rat_to_R r + rat_to_R s)%R.
  Proof.
    rewrite /rat_to_R.
    rewrite -Q2R_plus.
    apply: Qeq_eqR.
    apply: rat_to_Q_plus.
  Qed.

  Lemma rat_to_R_mul (r s : rat) :
    rat_to_R (r * s) = (rat_to_R r * rat_to_R s)%R.
  Proof.
    rewrite /rat_to_R.
    rewrite -Q2R_mult.
    apply: Qeq_eqR.
    by apply: rat_to_Q_mul.
  Qed.

  Lemma rat_to_R_0_center (r : rat) : rat_to_R r = 0%R -> r == 0.
  Proof.
    move =>  H.
    (*have H0 : rat_to_R r = rat_to_R (-r) by
      rewrite -mulN1r rat_to_R_mul H Rmult_0_r => //. *)
    rewrite -numq_eq0.
    rewrite -rat_to_R0 /rat_to_R /rat_to_Q in H.
    rewrite /numq.
    destruct (valq r) as (r1, r2) => /=.
    simpl in H.
    apply eqR_Qeq in H.
    rewrite /Qeq in H. simpl in H.
    ring_simplify in H.
    induction r1 => //.
    simpl in H.
    rewrite <- Nat2Z.inj_0 in H.
    apply Nat2Z.inj in H.
    rewrite H. auto.
  Qed. 

  Lemma rat_to_R_inv (r : rat) : (r != 0) -> rat_to_R r^-1 = Rinv (rat_to_R r).
  Proof.
    (*
    case H0 : (r == 0).
    - move/eqP: H0 => H0.
      rewrite H0. rewrite invr0 => //.
      rewrite /rat_to_R /rat_to_Q /Q2R => /=.
      rewrite Rmult_0_l.
    *)
    move => H.
    apply Rmult_eq_reg_l with (r := rat_to_R r).
    rewrite -rat_to_R_mul Rinv_r.
    rewrite mulfV; first by apply rat_to_R1.
    apply H.
    move => H0.
    apply rat_to_R_0_center in H0. apply negbTE in H. congruence.
    move => H0.
    apply rat_to_R_0_center in H0. apply negbTE in H. congruence.
  Qed. 
  Lemma rat_to_R_opp (r : rat) : rat_to_R (- r) = Ropp (rat_to_R r).
  Proof.
    have ->: -r = -1 * r by rewrite mulNr mul1r.
    have ->: (-rat_to_R r = -1 * rat_to_R r)%R.
    { by rewrite Ropp_mult_distr_l_reverse Rmult_1_l. }
    rewrite rat_to_R_mul; f_equal.
    rewrite /rat_to_R /rat_to_Q /Q2R /= Ropp_mult_distr_l_reverse Rmult_1_l.
    by apply: Ropp_eq_compat; rewrite Rinv_1.
  Qed.

  Lemma rat_to_R1n : rat_to_R (-1) = (-1)%R.
  Proof.
    rewrite rat_to_R_opp rat_to_R1 //.
  Qed.  
End rat_to_R_lemmas.

Section Z_to_int.
  Variable z : Z.

  Definition Z_to_int : int :=
    match z with
    | Z0 => Posz 0
    | Zpos p => Posz (Pos.to_nat p)
    | Zneg p => Negz (Pos.to_nat p).-1
    end.
End Z_to_int.

Lemma Pos_to_natNS p : (Pos.to_nat p).-1.+1 = Pos.to_nat p.
Proof.
  rewrite -(S_pred _ 0) => //.
  apply: Pos2Nat.is_pos.
Qed.  

Lemma PosN0 p : Pos.to_nat p != O%N.
Proof.
  apply/eqP => H.
  move: (Pos2Nat.is_pos p); rewrite H.
  inversion 1.
Qed.  

Section Z_to_int_lemmas.
  Lemma Z_to_int0 : Z_to_int 0 = 0%R.
  Proof. by []. Qed.
  
  Lemma Z_to_int_pos_sub p q :
    Z_to_int (Z.pos_sub q p) = (Posz (Pos.to_nat q) + Negz (Pos.to_nat p).-1)%R.
  Proof.
    rewrite Z.pos_sub_spec.
    case H: (q ?= p)%positive.
    {
      apply Pos.compare_eq_iff in H.
      rewrite NegzE H => //.
      case: (Pos2Nat.is_succ p) => n0 H1.
      rewrite H1 -pred_Sn addrN => //.
    }
    {
      rewrite NegzE => //;
      move: (Pos2Nat.is_pos p) => H0;
      rewrite Nat.succ_pred_pos => //.
      rewrite /Z_to_int NegzE prednK.
      rewrite -opprB. apply /eqP.
      rewrite eqr_opp. apply /eqP.
      rewrite nat_of_P_minus_morphism => /=.
      apply nat_of_P_lt_Lt_compare_morphism in H.
      generalize dependent (Pos.to_nat p);
      induction n => H0 H1;
        first by inversion H1.
      inversion H0.
      {
        rewrite H2 -minus_Sn_m; last by left.
        rewrite minus_diag [Posz n.+1] intS -addrA addrN => //.
      }
      {
        apply IHn in H2.
        rewrite -minus_Sn_m. rewrite !intS H2 addrA => //.
        omega. omega.
      } 
      case: (Pos.compare_lt_iff q p) => H1 _.
      apply Pos.compare_gt_iff. apply H1 in H => //.
      case: (Pos.compare_lt_iff q p) => H1 H2.
      apply H1 in H.
      rewrite nat_of_P_minus_morphism.
      rewrite subn_gt0. apply/ltP.
      apply nat_of_P_lt_Lt_compare_morphism => //.
      apply Pos.compare_gt_iff => //.
    }
    {
      rewrite NegzE => //;
      move: (Pos2Nat.is_pos p) => H0;
      rewrite Nat.succ_pred_pos => //.
      rewrite /Z_to_int.
      rewrite nat_of_P_minus_morphism => /=.
      apply nat_of_P_gt_Gt_compare_morphism in H.
      generalize dependent (Pos.to_nat q).
      induction n => H1;
        first by inversion H1.
      inversion H1.
      {
        rewrite H2 -minus_Sn_m; last by left.
        rewrite minus_diag [Posz n.+1] intS -addrA addrN => //.
      }
      {
        apply IHn in H2.
        rewrite -minus_Sn_m. rewrite !intS H2 addrA => //.
        omega.
      }
      by [].
    }
  Qed.  

  Lemma Z_to_int_plus (r s : Z) :
    Z_to_int (r + s) = (Z_to_int r + Z_to_int s)%R.
  Proof.
    case H: r => [|p|p].
    { by rewrite add0r Zplus_0_l. }
    { case H2: s => [|q|q].
      { by rewrite addr0. }
      { by rewrite /= Pos2Nat.inj_add. }
      by rewrite /= Z_to_int_pos_sub. }
    case H2: s => [|q|q].
    { by rewrite addr0. }
    { by rewrite /= Z_to_int_pos_sub. }
    rewrite /= Pos2Nat.inj_add 3!NegzE.
    rewrite !prednK; try (apply /ltP; apply Pos2Nat.is_pos).
    rewrite -oppz_add //.
    rewrite addn_gt0. apply /orP. left. apply /ltP.
    by apply: Pos2Nat.is_pos.
  Qed.
      
  Lemma Z_to_int_mul (r s : Z) :
    Z_to_int (r * s) = (Z_to_int r * Z_to_int s)%R.
  Proof.
    case H: r => [|p|p].
    { by rewrite /= mul0r. }
    { case H2: s => [|q|q].
      { by rewrite mulr0. }
      { by rewrite /= Pos2Nat.inj_mul. }
      rewrite /= 2!NegzE Pos2Nat.inj_mul.
      have ->: (Pos.to_nat q).-1.+1 = Pos.to_nat q.
      { apply: Pos_to_natNS. }
      rewrite mulrN.
      rewrite prednK //. rewrite muln_gt0. apply /andP.
      split; apply /ltP; apply: Pos2Nat.is_pos. }
    case H2: s => [|q|q].
    { by rewrite mulr0. }
    { rewrite /= Pos2Nat.inj_mul -2!opp_posz_negz Pos_to_natNS.
      rewrite -(S_pred (Pos.to_nat _ * _)%coq_nat 0); first by rewrite mulNr.
      apply /ltP. rewrite muln_gt0. apply /andP.
      split; apply /ltP; apply Pos2Nat.is_pos. }
    rewrite /= Pos2Nat.inj_mul -2!opp_posz_negz 2!Pos_to_natNS.
    by rewrite mulNr mulrN opprK.
  Qed.

  (** This lemma should be in the standard library... *)
  Lemma Zneg_Zle' (r s : positive) :
    (Z.le (Z.neg r) (Z.neg s))%Z -> (r >= s)%positive.
  Proof.
    rewrite /Z.le /Z.compare /CompOpp.
    case H: (r ?= s)%positive => //.
    { move => _; move: H.
      rewrite Pos.compare_eq_iff => ->.
      rewrite Pos.ge_le_iff.
      apply: Pos.le_refl. }
    move => _; move: H.
    by rewrite Pcompare_eq_Gt; rewrite /Pos.gt /Pos.ge => ->.
  Qed.    

  Lemma Z_to_int_le (r s : Z) :
    Z.le r s -> (Z_to_int r <= Z_to_int s)%R.
  Proof.
    rewrite /Z_to_int.
    case: r.
    { case: s => //. }
    { case: s.
      { move => p H.
        move: (Pos2Z.is_pos p) => H2.
        omega. }
      { move => p q.
        rewrite /Z.le -(Pos2Z.inj_compare q p) Pos.compare_le_iff Pos2Nat.inj_le.
        move/leP => //. }
      move => p q; move: (Zle_neg_pos p q); move/Zle_not_lt => H H2.
      have H3: Z.pos q <> Z.neg p by discriminate.
      omega. }
    case: s => //.
    move => p q; move/Zneg_Zle'; rewrite Pos.ge_le_iff Pos2Nat.inj_le.
    move/leP => H.
    have H2: ((Pos.to_nat p).-1 <= (Pos.to_nat q).-1)%N.
    { by apply/leP; apply: Nat.pred_le_mono; apply/leP. }
    by [].
  Qed.

  Lemma Z_to_int_opp r :
    Z_to_int (Z.opp r) = (- Z_to_int r)%R.
  Proof. by rewrite Z.opp_eq_mul_m1 Z_to_int_mul /= NegzE mulrC mulN1r. Qed.
End Z_to_int_lemmas.
      
Section Q_to_rat.
  Variable q : Q.

  Definition Q_to_rat : rat :=
    fracq (Z_to_int (Qnum q), Z_to_int (Zpos (Qden q))).
End Q_to_rat.

Section Q_to_rat_lemmas.
  Lemma Q_to_rat0 : Q_to_rat 0 = 0%R.
  Proof. by rewrite /Q_to_rat /= Pos2Nat.inj_1 fracqE /= divr1. Qed.
  
  Lemma Q_to_rat1 : Q_to_rat 1 = 1%R.
  Proof. by rewrite /Q_to_rat /= Pos2Nat.inj_1 fracqE /= divr1. Qed.
    
  Lemma Q_to_rat_plus (r s : Q) :
    Q_to_rat (r + s) = (Q_to_rat r + Q_to_rat s)%Q.
  Proof.
    rewrite /Q_to_rat !Z_to_int_plus.
    case: r => a b; case s => c d /=.
    rewrite !Z_to_int_mul /= addq_frac /=.
    f_equal; rewrite /addq_subdef //=; f_equal.
    by rewrite Pos2Nat.inj_mul.
    by apply: PosN0.
    by apply: PosN0.    
  Qed.

  Lemma Q_to_rat_mul (r s : Q) :
    Q_to_rat (r * s) = (Q_to_rat r * Q_to_rat s)%Q.
  Proof.
    rewrite /Q_to_rat /=; case: r => a b; case s => c d /=.
    rewrite Z_to_int_mul mulq_frac /mulq_subdef /=; f_equal.
    by rewrite Pos2Nat.inj_mul.
  Qed.

  Lemma Q_to_rat_le0 (r : Q) : Qle 0 r -> (0 <= Q_to_rat r)%R.
  Proof.
    rewrite /Qle /= /Q_to_rat /= Z.mul_1_r fracqE => H.
    rewrite mulrC pmulr_rge0 /=.
    { move: (Z_to_int_le H) => /=.
      by rewrite -(ler_int rat_realFieldType). }
    move: (Pos2Nat.is_pos (Qden r)); move/ltP => H2.
    rewrite invr_gt0.
      by rewrite -ltz_nat -(ltr_int rat_realFieldType) in H2.
  Qed.
  
  Lemma Q_to_rat_opp r :
    Q_to_rat (Qopp r) = (- (Q_to_rat r))%R.
  Proof.
    rewrite /Q_to_rat /Qopp; case: r => /= n d.
    rewrite 2!fracqE /= -mulNr Z_to_int_opp; f_equal.
    move: (Z_to_int n) => r; move {n d}.
    case: r => n; case: n => // n.
    by rewrite NegzE -addn2 opprK -mulNrz -mulNrNz.
  Qed.

  Lemma Q_to_rat_inv r :
    Q_to_rat (Qinv r) = ((Q_to_rat r)^-1)%R.
  Proof.
    rewrite /Qinv.
    case H: (Qnum r) => [|p|p].
    { have ->: Q_to_rat r = 0%R.
      rewrite /Q_to_rat H frac0q => //.
      apply /eqP => //.
    }
    {
      move: H.
      case: r => /= num den H.
      rewrite H.
      rewrite /Q_to_rat => /=.
      rewrite  2!fracqE /= GRing.invf_div //.
    }
    {
      move: H.
      case: r => /= num den H.
      rewrite H.
      rewrite /Q_to_rat => /=.
      rewrite  2!fracqE /= GRing.invf_div.
      rewrite 2!NegzE.
      repeat (rewrite prednK; last by apply /ltP; apply Pos2Nat.is_pos).
      by rewrite mulrNz mulNr mulrNz GRing.invrN mulrN.
    }
  Qed.

  Lemma Q_to_rat_div r s :
    Q_to_rat (r / s) = (Q_to_rat r / Q_to_rat s)%R.
  Proof.
    rewrite Q_to_rat_mul Q_to_rat_inv => //.
  Qed.    
    
  Lemma Q_to_rat_le (r s : Q) :
    Qle r s -> (Q_to_rat r <= Q_to_rat s)%R.
  Proof.
    rewrite Qle_minus_iff -subr_ge0.
    have <-: Q_to_rat (s + - r) = (Q_to_rat s - Q_to_rat r)%R.
    { rewrite Q_to_rat_plus Q_to_rat_opp //. }
    apply: Q_to_rat_le0.
  Qed.    
End Q_to_rat_lemmas.

(** The proofs in this section need to be incorporated into
    the other sections, but the last two require notions after
    the rat_to_Q_lemmas **)
Section rat_to_Q_lemmas_cont.
  Local Open Scope ring_scope.
  Delimit Scope R with R_ssr.  
  Delimit Scope R_scope with R.
  
  Lemma cancel_Z2I x : Z_to_int (int_to_Z x) = x.
  Proof.
    destruct x => //=.
    {
      induction n; auto.
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_l.
      rewrite Z_to_int_plus.
      simpl.
      rewrite IHn.
      auto.
    }
    rewrite SuccNat2Pos.id_succ. auto.
  Qed.

  Lemma cancel_I2Z x : int_to_Z (Z_to_int x) = x.
  Proof.
    induction x => //=. apply positive_nat_Z.
    f_equal.
    rewrite Pos.of_nat_succ Pos_to_natNS Pos2Nat.id => //.
  Qed.

 Lemma int_to_Z_div_nat_pos a b p :
    int_to_Z b = (Zmult (Z.pos p) (int_to_Z a)) ->
    `|b|%N = (Pos.to_nat p * `|a|)%N.
  Proof.
    move => H.
    have H0: (Z.pos p = int_to_Z (Posz (Pos.to_nat p))).
    { by simpl; rewrite positive_nat_Z. }
    rewrite H0  int_to_Z_mul in H.
    apply int_to_Z_inj_iff in H.
    by rewrite H abszM.
  Qed.

  Lemma int_to_Z_div_nat_neg a b p :
    int_to_Z b = (Zmult (Z.neg p) (int_to_Z a)) ->
    `|b|%N = (Pos.to_nat p * `|a|)%N.
  Proof.
    move => H.
    have H0: (Pos.to_nat 1 = 1%N) by [].
    case: (Pos.eq_dec p 1) => Hp.
    - rewrite Hp Z.mul_comm -Z.opp_eq_mul_m1 -int_to_Z_opp in H.
      apply int_to_Z_inj_iff in H.
      by rewrite Hp H H0 mul1n abszN.
    - have H1: (Z.neg p = int_to_Z (Negz (Pos.to_nat (Pos.pred p)))).
      { by simpl; rewrite Pos2SuccNat.id_succ Pos.succ_pred. }
      rewrite H1 int_to_Z_mul in H. apply int_to_Z_inj_iff in H.
      rewrite H -opp_posz_negz Pos2Nat.inj_pred. rewrite prednK.
      destruct (Pos.to_nat p); destruct a => // /=.
      by rewrite GRing.mulNr abszN.
      by apply /ltP; apply Pos2Nat.is_pos.
      have H2: ((1 <= p)%positive). apply Pos.le_1_l.
      apply Pos.lt_eq_cases in H2. case: H2 => H2 => //.
      congruence.
  Qed.

  Lemma int_to_nat_mul (s r : int) :
    ((int_to_nat s) * (int_to_nat r))%N = int_to_nat (s * r).
  Proof.
    case: s; case: r => // m n.
    - elim: n.
      + by rewrite mul0n.
      + move => n' IHn /=.
        have ->: ((n' * m.+1)%Nrec = (n' * m.+1)%N) by [].
        by rewrite mulSn IHn => //.
    - rewrite mulnC mulrC.
      elim: m.
      + by rewrite mul0n.
      + move => m IHm /=.
        have ->: ((m * n.+1)%Nrec = (m * n.+1)%N) by [].
        by rewrite mulSn IHm => //.
  Qed.

  Lemma int_to_nat_inj_pos (s r : int) :
    0 <= s -> 0 <= r ->
    (int_to_nat s) = (int_to_nat r) <-> s = r.
  Proof.
    split; move: H H0; case: s; case: r => //; auto.  
    move=> n m H0 H1 H2. by inversion H2.
  Qed.
  
  Lemma int_to_nat_inj_neg_l (s r : int) :
    0 <= s ->
    r <= 0 ->
    (int_to_nat s) = (int_to_nat r) <-> s = - r.
  Proof.
    split; move: H H0; case: s; case: r => //.
    - move => n m. case: n; case: m => //.
    - move => n m H0 H1 H2. rewrite NegzE. rewrite GRing.opprK.
      simpl in H2. by rewrite H2.
    - move => n m H0 H1 H2. rewrite H2. move: H1 H2. case: n => //.
    - move => n m H0 H1 H2. rewrite NegzE /=. rewrite NegzE in H2.
      rewrite GRing.opprK in H2. by inversion H2.
  Qed.
  
  Lemma int_to_nat_inj_neg_r (s r : int) :
    s < 0 ->
    0 <= r ->
    (int_to_nat s) = (int_to_nat r) <-> s = - r.
  Proof.
    split; move: H H0; case: s; case: r => //.
    - move => n m H0 H1 /= H2. by rewrite NegzE H2.
    - move => n m H0 H1 H2 /=. rewrite NegzE in H2.
      destruct n; destruct m => //;
        by apply GRing.oppr_inj in H2; inversion H2.
  Qed.

  Lemma int_to_nat_inj_neg (s r : int) :
    s < 0 ->
    r <= 0 ->
    (int_to_nat s) = (int_to_nat r) <-> s = r.
  Proof.
    split; move: H H0; case: s; case: r => //; auto.
    - move => n m. case: n; case: m => //.
    - move => n m H0 H1 H2. by inversion H2.
  Qed.

  Lemma int_nat_div_eq :
    forall m n,
      Z.divide (int_to_Z m) (int_to_Z n) <-> dvdn `|m| `|n|.
  Proof.
    split => H.
    - rewrite /Z.divide in H.
      destruct H as [z H].
      apply /dvdnP.
      case: (Z.le_gt_cases Z0 z).
      { exists (Z.to_nat z).
        move: H a. move: m n.
        elim: z; move => /= a b.
        + rewrite mul0n. case: b; move => n. case: n => //; move => H Ha.
          move => H Ha. inversion H.
        + move => c d Ha. by apply int_to_Z_div_nat_pos.
        + move => c d H0. destruct H0. reflexivity. }
      { exists (Z.to_nat (- z)).
        move: H b. case: z => H Hb /=.
        + inversion Hb.
        + move => H0. inversion H0.
        + move => H0. by apply int_to_Z_div_nat_neg. }
    - move: H => /dvdnP [k H].
      rewrite /Z.divide.
      case Hn: (0 <= n); case Hm: (0 <= m).
      { exists (int_to_Z (Posz k)).
        rewrite int_to_Z_mul. f_equal. 
        have H0: (`|n| = n) by apply gez0_abs.
        have H1: (`|m| = m) by apply gez0_abs.
        rewrite -H0 -H1.
        have H2: (absz n = int_to_nat n).
        { by rewrite /int_to_nat; destruct n. }
        have H3: (absz m = int_to_nat m).
        { by rewrite /int_to_nat; destruct m. }
        have H4: (k = int_to_nat (Posz k)) by [].
        rewrite H2 H3 H4 int_to_nat_mul in H.
        apply int_to_nat_inj_pos in H => //.
        rewrite H. destruct k; destruct m => //.
        apply mulr_ge0 => //. }
      { exists (int_to_Z (- Posz k)).
        rewrite int_to_Z_mul. f_equal.
        have H0: (`|n| = n) by apply gez0_abs.
        have H': (m < 0) by destruct m.
        have H1: (`|m| = - m) by apply ltz0_abs.
        rewrite -H0.
        have H2: (absz n = int_to_nat n).
        { rewrite /int_to_nat. destruct n => //. }
        have H3: (absz m = int_to_nat m).
        { rewrite /int_to_nat. destruct m => //. }
        have H4: (k = int_to_nat (Posz k)) by [].
        rewrite H2 H3 H4 int_to_nat_mul in H.
        apply int_to_nat_inj_neg_l in H => //.
        rewrite H. destruct k; destruct m => //.
        apply mulr_ge0_le0 => //. auto. }
      { exists (int_to_Z (- Posz k)).
        rewrite int_to_Z_mul. f_equal.
        have H': (n < 0) by destruct n.
        have H0: (`|n| = - n) by apply ltz0_abs.
        have H1: (`|m| = m) by apply gez0_abs.
        rewrite -H1.
        have H2: (absz n = int_to_nat n).
        { rewrite /int_to_nat. destruct n => //. }
        have H3: (absz m = int_to_nat m).
        { rewrite /int_to_nat. destruct m => //. }
        have H4: (k = int_to_nat (Posz k)) by [].
        rewrite H2 H3 H4 int_to_nat_mul in H.
        apply int_to_nat_inj_neg_r in H => //.
        rewrite H. destruct k; destruct m => //.
        by rewrite GRing.mulNr; apply GRing.oppr_inj;
          rewrite GRing.opprK.
        by apply mulr_ge0. }
      { exists (int_to_Z (Posz k)).
        rewrite int_to_Z_mul. f_equal. 
        have H': (n < 0) by destruct n.
        have H0: (`|n| = - n) by apply ltz0_abs.
        have Hmlt0: (m < 0) by destruct m => // .
        have H1: (`|m| = - m) by apply ltz0_abs.
        have H2: (absz n = int_to_nat n).
        { rewrite /int_to_nat. destruct n. auto. rewrite NegzE //. }
        have H3: (absz m = int_to_nat m).
        { rewrite /int_to_nat. destruct m. auto. rewrite NegzE //. }
        have H4: (k = int_to_nat (Posz k)) by [].
        rewrite H2 H3 H4 int_to_nat_mul in H.
        apply int_to_nat_inj_neg in H => //.
        by destruct k; destruct m => //. }
  Qed.

  Lemma rat_to_Q_gcd (a b : int) (pf : (0 < b) && coprime `|a| `|b|) :
    Z.gcd (int_to_Z a) (Z.pos (int_to_positive b)) = (Zpos 1).
  Proof.
    move: pf. rewrite /coprime. move=> /andP [pf1 pf2].
    move: pf2 => /eqP pf2.
    apply Znumtheory.Zis_gcd_gcd => //.
    constructor; try apply Z.divide_1_l.
    move => x H0 H1.
    rewrite -(cancel_I2Z x) -(cancel_I2Z 1).
    apply int_nat_div_eq => /=.
    rewrite Pos2Nat.inj_1.
    rewrite -pf2 dvdn_gcd.
    apply /andP; split.
    apply int_nat_div_eq. rewrite cancel_I2Z. apply H0.
    apply int_nat_div_eq; rewrite cancel_I2Z => //.
    rewrite /Z.divide. rewrite /Z.divide in H1.
    case: H1 => z H1. exists z.
    by rewrite -int_to_positive_to_Z.
  Qed.

  Lemma rat_to_Q_red (r : rat) :
    rat_to_Q r = Qred (rat_to_Q r).
  Proof.
    rewrite /rat_to_Q. case: r => valq. case: valq => a b /= pf.
    have H0: (match Z.ggcd (int_to_Z a)(Z.pos (int_to_positive b))
                    return Prop with
              | pair g p =>
                match p return Prop with
                | pair aa bb =>
                  and (@eq Z (int_to_Z a) (Z.mul g aa))
                      (@eq Z (Z.pos (int_to_positive b)) (Z.mul g bb))
                end
              end).
    { by apply Z.ggcd_correct_divisors. }
    have H1: ((Z.ggcd (int_to_Z a) (Z.pos (int_to_positive b))).1 =
              Z.gcd (int_to_Z a) (Z.pos (int_to_positive b))).
    { by apply Z.ggcd_gcd. }
    have H2: (Z.gcd (int_to_Z a) (Z.pos (int_to_positive b)) = (Zpos 1)).
    { by apply rat_to_Q_gcd. }
    move: H0 H1.
    case: (Z.ggcd (int_to_Z a) (Z.pos (int_to_positive b))) => z p.
    case: p => z0 z1 /= H0 H1. case: H0.
    rewrite H2 in H1. rewrite H1 2!Z.mul_1_l => H0 H0'.
    by rewrite H0 -H0'.
  Qed.

  Lemma cancel_rat_to_Q q :
    Qeq (rat_to_Q (Q_to_rat q)) q.
  Proof.
    rewrite /Q_to_rat rat_to_Q_fracq_pos /=.
    rewrite cancel_I2Z Pos2Nat.id.
    case: q => //.
    by apply /ltP; apply Pos2Nat.is_pos.
  Qed.

   Import ProofIrrelevance.

  Lemma rat_to_Q_inj r s :
    rat_to_Q r = rat_to_Q s -> r = s.
  Proof.
    case: r; case: s. rewrite /rat_to_Q => r rpf s spf.
    case Hs: (valq (Rat (valq:=s) spf)).
    case Hr: (valq (Rat (valq:=r) rpf)) => H.
    simpl in *. inversion H.
    apply int_to_Z_inj_iff in H1.
    apply int_to_positive_inj_pos in H2; subst; simpl in *;
      try (move: rpf => /andP [rpf1 rpf2];
           move: spf => /andP [spf1 spf2];
           subst; simpl in *; assumption).
    have ->: (rpf = spf) by apply proof_irrelevance.
    by [].
  Qed.

  Lemma rat_to_QK q : rat_to_Q (Q_to_rat (Qred q)) = Qred q.
  Proof.
    rewrite rat_to_Q_red. apply Qred_complete.
    rewrite cancel_rat_to_Q. apply Qred_correct.
  Qed.

  Lemma rat_to_QK1 q : rat_to_Q (Q_to_rat q) = Qred q.
  Proof.
    rewrite rat_to_Q_red. apply Qred_complete.
    by rewrite cancel_rat_to_Q. 
  Qed.
  
  Lemma rat_to_QK2 q r : Qeq q (rat_to_Q r) -> Q_to_rat q = r.
  Proof.
    move => H0.
    have H1: (Qred q = rat_to_Q r).
    { rewrite rat_to_Q_red. apply Qred_complete, H0. }
    apply rat_to_Q_inj. rewrite -H1 rat_to_Q_red.
    apply Qred_complete, cancel_rat_to_Q.
  Qed.

  Lemma rat_to_Qopp r : rat_to_Q (-r) = Qopp (rat_to_Q r).
  Proof.
    rewrite -mulN1r rat_to_Q_red [rat_to_Q r]rat_to_Q_red -Qred_opp.
    apply: Qred_complete; rewrite rat_to_Q_mul //.
  Qed.
End rat_to_Q_lemmas_cont.

Definition N_to_Q (n : N.t) : Q := NtoZ n # 1.

Lemma N_to_Q_plus n1 n2 :
  N_to_Q (n1 + n2) = Qplus (N_to_Q n1) (N_to_Q n2).
Proof.
  rewrite /N_to_Q /NtoZ /Nplus.
  case: n1; case: n2 => //.
  { unfold Qplus; simpl.
    by move => p; rewrite Pos.mul_1_r. }
  { unfold Qplus; simpl.
    by move => p; rewrite Pos.mul_1_r. }
  move => p q.
  by rewrite Pos2Z.inj_add /Qplus /= !Pos.mul_1_r.
Qed.

Lemma N_to_Q_succ n :
  N_to_Q (N.succ n) = Qplus 1 (N_to_Q n).
Proof.
  have ->: N.succ n = N.add 1 n.
  { by elim: n => // p; rewrite /N.add /Pos.add; case: p. }
  rewrite N_to_Q_plus; f_equal.
Qed.  

Definition N_to_D (n : N.t) : D := Dmake (2*NtoZ n) 1.

Lemma N_to_D_plus n1 n2 :
  N_to_D (n1 + n2) = Dadd (N_to_D n1) (N_to_D n2).
Proof.
  rewrite /N_to_D /NtoZ /Nplus.
  case: n1; case: n2 => //.
Qed.

Lemma N_to_D_to_Q n : Qeq (D_to_Q (N_to_D n)) (N_to_Q n).
Proof.
  rewrite /D_to_Q /N_to_D /N_to_Q /=.
  case H: (NtoZ n) => [|p|p].
  { by rewrite /Qeq. }
  { rewrite /Qeq /=.
    rewrite Pos.mul_1_r.
    rewrite Pos2Z.inj_xO /Zmult.
    by rewrite Pos.mul_comm. }
  by rewrite /Qeq /= Pos.mul_1_r Pos2Z.neg_xO /Zmult Pos.mul_comm.
Qed.  

Lemma rat_to_Q_N_to_Q n : Qeq (rat_to_Q n%:R) (N_to_Q (N.of_nat n)).
Proof.
  elim: n => // n IH.
  rewrite Nat2N.inj_succ N_to_Q_succ.
  have ->: (n.+1 = 1 + n)%N.
  { move {IH}; elim: n => //. }
  rewrite natrD rat_to_Q_plus IH //.
Qed.

Lemma Qred_idem (q : Q) : Qred (Qred q) = Qred q.
Proof.
  apply: Qred_complete.
  by rewrite Qred_correct.
Qed.  

(** Dyadic real field values *)

Definition dyadic_rat : Type :=
  {r : rat & {d : D & Qeq (D_to_Q d) (rat_to_Q r)}}.
Notation "'DRat'" := (dyadic_rat) (only parsing).

Definition dyadic_rat_to_rat (d : dyadic_rat) : rat := projT1 d.
Coercion dyadic_rat_to_rat : dyadic_rat >-> rat.

Definition dyadic_rat_to_D (d : dyadic_rat) : D := projT1 (projT2 d).
Coercion dyadic_rat_to_D : dyadic_rat >-> D.

Program Definition D_to_dyadic_rat (d : D) : DRat :=
  existT _ (Q_to_rat (D_to_Q d)) _.
Next Obligation.
  exists d.
  rewrite rat_to_QK1.
  by rewrite Qred_correct.
Defined.

Lemma dyadic_rat_to_Q (d : DRat) : Qeq (D_to_Q d) (rat_to_Q d).
Proof. apply: (projT2 (projT2 d)). Qed.

(** Some random lemmas on nat_of_bin, etc. *)

Lemma nat_of_bin_succ n : nat_of_bin (N.succ n) = (nat_of_bin n).+1.
Proof.
  elim: n => //= p.
  by rewrite nat_of_succ_pos.
Qed.

Lemma nat_of_bin0 : nat_of_bin 0 = 0%nat.
Proof. by []. Qed.

Lemma nat_of_pos_s p : exists n, nat_of_pos p = S n.
Proof.
  set (P p := exists n, nat_of_pos p = n.+1).
  change (P p).
  apply: Pos.peano_ind.
  { by exists O. }
  move => p'; rewrite /P => [][]n IH.
  exists n.+1.
  by rewrite nat_of_succ_pos IH.
Qed.    

Lemma nat_of_pos_inj p1 p2 : nat_of_pos p1 = nat_of_pos p2 -> p1=p2.
Proof.
  move: p1 p2.
  set (P := forall p1 p2 : positive, nat_of_pos p1 = nat_of_pos p2 -> p1 = p2).
  change P.
  apply: Pos.peano_ind.
  { simpl => p2.
    set (Q p2 := (1%nat = nat_of_pos p2 -> 1%positive = p2)).
    change (Q p2).
    apply: Pos.peano_ind => //.
    move => p'; rewrite /Q => IH.
    rewrite nat_of_succ_pos => //.
    case: (nat_of_pos_s p') => x -> //. }
  move => p1 IH p2.
  rewrite nat_of_succ_pos.
  set (Q p2 := (nat_of_pos p1).+1 = nat_of_pos p2 -> Pos.succ p1 = p2).
  change (Q p2).
  apply: Pos.peano_ind.
  { rewrite /Q.
    case: (nat_of_pos_s p1) => x -> //. }
  move => p; rewrite /Q => IH2.
  rewrite nat_of_succ_pos; case => H.
  by rewrite (IH _ H).
Qed.

Lemma nat_of_bin_inj n1 n2 : nat_of_bin n1 = nat_of_bin n2 -> n1=n2.
Proof.
  elim: n1 n2.
  { rewrite nat_of_bin0; case.
    { by rewrite nat_of_bin0. }
    move => p; inversion 1.
    by case: (nat_of_pos_s p) => n; rewrite -H1. }
  move => p; case.
  { rewrite nat_of_bin0.
    case: (nat_of_pos_s p) => n /= -> //. }
  by simpl => p' H; move: (nat_of_pos_inj H) => ->.
Qed.

Lemma N2Nat_lt n m :
  (N.to_nat n < N.to_nat m)%N -> 
  (n < m)%N.
Proof.
  move: n m; apply: N.peano_ind.
  { apply: N.peano_ind => //= n _ _.
    by rewrite nat_of_bin_succ. }
  move => n /= IH m; rewrite nat_of_bin_succ N2Nat.inj_succ.
  move: m; apply: N.peano_ind => // m _.
  rewrite nat_of_bin_succ N2Nat.inj_succ => H.
  have H2: (N.to_nat n < N.to_nat m)%N.
  { move: H; move: (N.to_nat n); move: (N.to_nat m) => x y.
    move/ltP => H; apply/ltP; omega. }
  suff: (n < m)%N => //.
  by apply: (IH _ H2).
Qed.    

(** END random lemmas *)
