Require Import OUVerT.numerics.
Require Import OUVerT.generalized_bigops.
Require Import Reals.Rcomplete.
Require Import Reals.SeqProp.
Require Import Reals.Rseries.
Require Import Rbase.
Require Import Reals.Rfunctions.
Require Import Reals.Rpower.

Import OUVerT.numerics.Numerics.
Require Import OUVerT.extrema.
Import OUVerT.numerics.Numerics.
Import OUVerT.extrema.num_Extrema.
Require Import OUVerT.compile.

Require Import Reals.Rcomplete.

Require Import Psatz.

From mathcomp Require Import all_ssreflect.
Require Import JMeq.
Definition JMeqfun {T1 T2 T3: Type} (f1 : T1 -> T3) (f2 : T2 -> T3) :=
    forall (a : T1) (b : T2), JMeq a b -> f1 a = f2 b.



Lemma JMeq_exists_convert: forall {T1 T2 : Type}, (exists x : T1, exists y : T2, JMeq x y) -> exists f : T1 -> T2, (forall (a : T1) (b : T2), JMeq a b <-> f a = b).
Proof.
  intros.
  destruct H.
  destruct H.
  inversion H.
  rewrite H0 in x H H3.
  exists id.
  intros.
  split; intros.
    apply JMeq_eq. auto.
  rewrite H1. auto.
Qed.
    
  

Delimit Scope Numeric_scope with Num.
Delimit Scope R_scope with R.
Local Open Scope Num.

Module banach.

  Lemma converge_list_strong: forall (T : Type) (l : list T) (seq : T->nat->R) (f : T->R), 
  (forall t : T, List.In t l -> Un_cv (seq t) (f t)) -> 
    (forall (eps : R), 0 < eps -> 
      exists N : nat, forall (t : T) (n : nat), (List.In t l) -> (n >= N)%coq_nat ->
        R_dist (seq t n) (f t) < eps).
  Proof.
    unfold ge.
    intros.
    induction l.
    { exists O. intros. inversion H1. }
    destruct IHl.
    {
      intros.
      apply H.
      apply List.in_cons. auto.
    }      
    unfold Un_cv in H.
    unfold ge in H.
    destruct H with a eps; auto.
      apply List.in_eq.
    exists (Nat.max x x0).
    intros.
    destruct H3.
    {
      rewrite <- H3.
      apply H2.
      apply Nat.le_trans with (Nat.max x x0); auto.
      apply Nat.le_max_r.
    }
    apply H1; auto.
    apply Nat.le_trans with (Nat.max x x0); auto.
    apply Nat.le_max_l.
  Qed.


  Definition max_dist {T Nt : Type} `{Numeric Nt} (l : list T) (H0 : O <> length l) (f g : T->Nt)  : Nt :=
    mapmax_ne (l := l) (fun x=> abs (f x + - g x)) H0.

  Record contraction_func {Nt:  Type} `{Numerics.Numeric Nt} : Type :=
    contraction_mk {
      x_t : Type;        
      x_t_enum : Enumerable x_t;
      x_t_ok : @Enum_ok _ x_t_enum;
      contr : Nt;
      x_t_ne: O <> length x_t_enum;
      step : (x_t -> Nt) -> (x_t -> Nt);
      contr_pos : 0 <= contr;
      contr_lt_1 : contr < 1;
      step_ext: forall (f g : x_t->Nt), (forall x : x_t, f x =  g x) -> (forall x : x_t, (step f) x = (step g) x);
      is_contr : forall x1 x2,  (max_dist x_t_enum x_t_ne (step x1) (step x2) <= contr * max_dist x_t_enum x_t_ne x1 x2 ); 
    }.

  Definition contraction_exists_T {Nt : Type} `{Numerics.Numeric Nt} (c : contraction_func) : (x_t c).
    destruct c.
    simpl.
    destruct (x_t_enum0).
    { exfalso. apply x_t_ne0. auto. }
    exact x.
  Defined.
    
  Fixpoint rec_f {T Nt: Type} `{Numerics.Numeric Nt} (step_f : (T->Nt) -> (T -> Nt)) (f : T->Nt)
       (n : nat) : (T->Nt) :=
  match n with
  | O => f
  | S n' => step_f (rec_f step_f f n')
  end.

  Lemma rec_step_reverse: forall {T Nt : Type} `{Numerics.Numeric Nt} (step_f : (T->Nt) -> (T->Nt)) 
    (f : T->Nt) (n : nat),  rec_f step_f (step_f f) n = step_f (rec_f step_f f n).
  Proof.
    intros.
    generalize f.
    induction n; intros.
      repeat rewrite (recO contraction). auto.
    simpl.
    rewrite IHn. auto.
  Qed.

  Section banach_Numeric.
    Context {Nt:Type} `{Numerics.Numeric_Props Nt}.
    Variable contraction : contraction_func.

    Local Notation step_f := (step contraction).
    Local Notation q := (contr contraction).
    Local Notation dist := (max_dist (x_t_enum contraction) (x_t_ne contraction)).
    Local Notation T := (x_t contraction).
    Local Notation l := (x_t_enum contraction).


    Lemma all_T_in: forall x : T, List.In x l.
    Proof. intros. destruct (x_t_ok contraction). apply enum_total. Qed.

    Lemma one_minus_q_gt0: 0 < 1 + - q.
    Proof.
      intros.
      rewrite <- plus_neg_r with q.
      apply plus_lt_compat_r.
      apply (contr_lt_1 contraction).
    Qed.

    Lemma dist_0_eq: forall (f g : T->Nt), dist f g = 0 -> forall x, f x = g x.
    Proof.
      unfold dist.
      intros.
      apply abs_0_same.
      apply mapmax_ne_eq_const in H0.
      destruct H0.
      repeat destruct H1.
      destruct H0 with x; auto. apply all_T_in.
      exfalso. apply lt_not_le in H3. apply H3. apply abs_ge_0.
    Qed.

    Lemma eq_dist_0: forall (f g : T->Nt), (forall x, f x = g x) -> dist f g = 0.
    Proof.
      unfold dist.
      intros.
      apply mapmax_ne_eq_const. auto.
      split.
      { intros. rewrite H0; auto. rewrite plus_neg_r. right. apply abs_0. }
      exists (contraction_exists_T contraction).
      split.
        apply all_T_in.
      rewrite H0; auto. 
      rewrite plus_neg_r. apply abs_0.
    Qed.


    Lemma dist_ge_0: forall (f g : T->Nt), 0 <= dist f g.
    Proof.
      intros. unfold dist. apply mapmax_ne_ge_const. auto.
      exists (contraction_exists_T contraction).
      split. 
        apply all_T_in.
      apply abs_ge_0.
    Qed.
    
    Lemma rec_ext: forall (f g : T->Nt) (n : nat), (forall x : T, f x =  g x) -> (forall x : T, (rec_f step_f f n) x = (rec_f step_f g n) x).
    Proof. intros.
      generalize dependent x.
      induction n; intros.
        repeat rewrite (recO contraction). auto.
      repeat rewrite (rec_step contraction).
      apply (step_ext contraction); auto.
    Qed.

    Lemma rec_plus: forall f n m, rec_f step_f f (n + m) = (rec_f step_f (rec_f step_f f n) m).
    Proof.
      intros.
      induction m.
      { rewrite <- plus_n_O. auto. }
      rewrite <- plus_n_Sm.
      simpl.
      rewrite IHm.
      auto.
    Qed.

    Lemma q0_step0: forall f g x, 
      q = 0 -> (step_f f) x = (step_f g) x.
    Proof.
      intros.      
      apply dist_0_eq.
      apply le_both_eq.
      2: { apply dist_ge_0. }
      rewrite <- mult_plus_id_l with (dist f g).
      rewrite <- H0.
      apply (is_contr contraction).
    Qed.

    Lemma step0_rec_n: forall (f : T->Nt), dist f (step_f f) = 0 -> forall n, dist f (rec_f step_f f n) = 0.
    Proof.
      intros.
      induction n.
      { simpl. apply eq_dist_0. auto. }
      apply eq_dist_0.
      intros.
      apply dist_0_eq with _ _ x in H0.
      rewrite H0.
      apply dist_0_eq.
      apply le_both_eq.
      2: { apply dist_ge_0. }
      rewrite <- mult_plus_id_r with q.
      rewrite <- IHn.
      simpl.
      apply (is_contr contraction).
    Qed.

    Lemma dist_ub: forall {Nt' : Type} `{Numeric_Props Nt'} (f g : T -> Nt') (x : T), abs (f x + - g x) <= dist f g.
    Proof. 
      intros.
      unfold dist.
      apply mapmax_ne_ge_const. auto.
      exists x.
      split. 
        apply all_T_in.
      apply le_refl.
    Qed.

    Lemma dist_triangle: forall {Nt' : Type} `{Numeric_Props Nt'} (f1 f2 f3 : T -> Nt'), dist f1 f2 <= dist f1 f3 + dist f3 f2.
    Proof. 
      intros.
      unfold dist.
      apply mapmax_ne_dist_triangle.
    Qed.

    Lemma dist_comm: forall  {Nt' : Type} `{Numeric_Props Nt'} (f g : T -> Nt'), dist f g = dist g f.
    Proof.
      intros.
      unfold dist.
      apply mapmax_ne_ext.
      intros.
      rewrite <- abs_neg.
      rewrite plus_neg_distr.
      rewrite double_neg.
      rewrite plus_comm.
      auto.
    Qed.

    Lemma step0_rec_nm: forall (f : T->Nt), dist f (step_f f) = 0 -> forall n m, dist (rec_f step_f f n) (rec_f step_f f m) = 0.
    Proof.
      intros.
      apply le_both_eq.
      2: { apply dist_ge_0. }
      apply le_trans with (dist (rec_f step_f f n) f + dist f (rec_f step_f f m)).
        apply dist_triangle.
      rewrite step0_rec_n; auto.
      rewrite dist_comm.
      rewrite step0_rec_n; auto.
      rewrite plus_id_l.
      apply le_refl.
    Qed. 

    Lemma q0_rec0: forall f g n m, q = 0 -> dist (rec_f step_f f (S n)) (rec_f step_f g (S m)) = 0.
    Proof.
      intros.
      apply le_both_eq.
      2: { apply dist_ge_0. }
      rewrite <- mult_plus_id_l with (dist (rec_f step_f f n) (rec_f step_f g m)).
      rewrite <- H0.
      repeat rewrite (rec_step contraction).
      apply (is_contr contraction).
    Qed.

    

    Lemma rec_dist: forall (f g : T->Nt) (n : nat), dist (rec_f step_f f n) (rec_f step_f g n) <= pow_nat q n * dist f g.
    Proof. 
      intros.
      induction n.
      { repeat rewrite (recO contraction). rewrite pow_natO. rewrite mult_id_l. apply le_refl. }
      repeat rewrite (rec_step contraction).
      apply le_trans with (q * (dist (rec_f step_f f n) (rec_f step_f g n))).
        apply (is_contr contraction).
      rewrite pow_nat_rec.
      rewrite <- mult_assoc.
      apply mult_le_compat_l; auto.
      apply (contr_pos contraction).
    Qed.


    Lemma dist_step_rec_n_ub: forall f n,
      (1 + - q) * dist (rec_f step_f f n) f <= (1 + - pow_nat q n) * dist f (step_f f).
    Proof.
      intros.
      apply le_trans with ((1 + - q) * (dist f (step_f f) * big_sum (List.seq 0 n) (fun n' => pow_nat q n'))).
      {
        apply mult_le_compat_l; auto.
        { apply le_lt_weak. apply one_minus_q_gt0; auto. }
        induction n.
        {rewrite eq_dist_0; auto. simpl. rewrite mult_plus_id_r. apply le_refl. }
        rewrite big_sum_seq_cons.
        simpl.
        rewrite ssrnat.add0n.
        simpl.
        apply le_trans with (dist (step_f (rec_f step_f f n)) (rec_f step_f f n)  + dist (rec_f step_f f n) f).
          apply dist_triangle.
        rewrite mult_plus_distr_l.
        apply plus_le_compat; auto.
        rewrite dist_comm.
        rewrite mult_comm.
        rewrite <- rec_step_reverse.
        apply  rec_dist.
      }
      rewrite -> mult_comm with (dist f (step_f f)) _.
      rewrite mult_assoc.
      apply mult_le_compat_r; auto.
        apply dist_ge_0.
      rewrite big_sum_geometric_1.        
        rewrite pow_natO. rewrite ssrnat.add0n. apply le_refl.
        apply (contr_pos contraction).
      apply (contr_lt_1 contraction).
    Qed.

    Lemma rec_f_nm_ub: forall (f : T->Nt) (n m : nat),
      (1 + - q) * dist (rec_f step_f f n) (rec_f step_f f (n+m)%coq_nat) <=
      dist f (step_f f) *  pow_nat q n.
    Proof.
      intros.
      assert(0 <= 1 + - q).
        apply le_lt_weak. apply one_minus_q_gt0.
      apply le_trans with ((1 + - q) * ( (pow_nat q n) * dist f (rec_f step_f f m))).
      {
        apply mult_le_compat_l; auto.
        rewrite Nat.add_comm. rewrite rec_plus.
        apply rec_dist.
      }
      apply le_trans with ( (1 + - q) * (pow_nat q n * big_sum (List.seq 0 m) (fun i : nat => dist (rec_f step_f f i)  (rec_f step_f f (S i)) ) )).
      {
        apply mult_le_compat_l; auto.
        apply mult_le_compat_l; auto.
          apply pow_ge_0. apply (contr_pos contraction).
        induction m.
        { simpl. right. rewrite eq_dist_0; auto. }
        rewrite big_sum_seq_cons.
        rewrite ssrnat.add0n.
        repeat rewrite (rec_step contraction).
        apply le_trans with (dist f (rec_f step_f f m) + dist (rec_f step_f f m) (step_f (rec_f step_f f m))).
          apply dist_triangle.
        rewrite plus_comm.
        apply plus_le_compat_l.
        auto.
      }
      rewrite -> mult_comm with (pow_nat q n) _.
      rewrite mult_assoc.
      apply mult_le_compat_r.
        apply pow_ge_0. apply (contr_pos contraction).
      apply le_trans with ((1 + - q) * big_sum (List.seq 0 m) (fun x => pow_nat q x *  (dist f (step_f f) ))).
      {
        apply mult_le_compat_l; auto.
        apply big_sum_le. auto.
        intros.
        simpl. 
        rewrite <- rec_step_reverse.
        apply rec_dist.
      }
      rewrite <- big_sum_mult_right.
      rewrite mult_assoc.
      rewrite <- mult_id_l.
      apply mult_le_compat_r.
        apply dist_ge_0.
      rewrite big_sum_geometric_1; auto.
      2:{ apply (contr_pos contraction). }
      2:{ apply (contr_lt_1 contraction). }
      rewrite pow_natO.
      rewrite add0n.
      rewrite <- plus_id_r.
      apply plus_le_compat_l.
      rewrite <- neg_plus_id. 
      apply le_neg.
      apply pow_ge_0.
      apply (contr_pos contraction).
    Qed.


  End banach_Numeric.
  Section banach_R.

    Variable contraction : @contraction_func R _.

    Local Notation step_f := (step contraction).
    Local Notation q := (contr contraction).
    Local Notation dist := (max_dist (x_t_enum contraction) (x_t_ne contraction)).
    Local Notation T := (x_t contraction).
    Local Notation l := (x_t_enum contraction).


    Lemma contraction_cauchy_crit_aux: forall (f : T->R) (n m : nat) (eps: R), 
      0 < eps -> 
      0 < dist f (step_f f) ->
      (pow_nat q n) < eps * to_R (1 + - q) * Rinv ((dist f (step_f f))) ->
      (dist (rec_f step_f f n) (rec_f  step_f f (n + m)))  < eps.
    Proof.
      intros.
      rewrite -> mult_lt_compat_l.
      2: { apply one_minus_q_gt0. }
      apply le_lt_trans with (dist f (step_f f) * pow_nat q n).
        apply rec_f_nm_ub.
      apply lt_le_trans with ( dist f (step_f f) *  (eps * (1 + - q) * Rinv ( dist f (step_f f)))).
        apply mult_lt_compat_l; auto.
      rewrite mult_comm.
      rewrite <- mult_assoc.
      simpl.
      rewrite Rinv_l.
      2: { apply lt_not_eq in H0. auto. }
      rewrite Rmult_1_r.
      rewrite Rmult_comm.
      apply Rle_refl.
    Qed.

    Lemma contraction_cauchy_crit: forall (x : T) (f : T->R), Cauchy_crit (fun n => (rec_f  step_f f n) x).
    Proof.
      intros.
      unfold Cauchy_crit.
      intros.
      unfold Rgt in H.
      destruct (total_order_T 0 (dist f (step_f f))).
      2: { exfalso. apply lt_not_le in l. apply l. apply dist_ge_0. }
      destruct s.
      2: { 
        exists O. intros.
        rewrite <- R_dist_same.
        apply Rle_lt_trans with (dist (rec_f  step_f f n) (rec_f  step_f f m)).
        { rewrite R_abs_same. rewrite <- R_le_same. rewrite <- R_abs_same. apply dist_ub.
          apply Numeric_Props_R.
        }
        rewrite step0_rec_nm; auto.
      }
      destruct exists_pow_lt with q (Rdiv eps 2 * to_R (1 + - q) * Rinv ((dist f (step_f f)))).
        apply (contr_pos contraction).
        apply (contr_lt_1 contraction).
      { 
        simpl.
        apply Rmult_lt_0_compat.
          apply Rmult_lt_0_compat; auto. lra. apply (one_minus_q_gt0 contraction).
        apply Rinv_0_lt_compat. auto.
      }
      exists x0.
      intros.
      rewrite <- R_dist_same.
      apply Rle_lt_trans with (dist (rec_f  step_f f n) (rec_f  step_f f m)).
        rewrite <- R_le_same. apply dist_ub. apply Numeric_Props_R.

      destruct Nat_le_exists_diff with x0 n; auto.
      destruct Nat_le_exists_diff with x0 m; auto.
      rewrite <- H4. rewrite <- H3.
      apply Rlt_le_trans with (Rdiv eps 2 + Rdiv eps 2).
      2:{ simpl. lra. }
      simpl.
      apply Rle_lt_trans with (dist (rec_f  step_f f (addn x0 x1)) (rec_f  step_f f x0) + dist (rec_f  step_f f x0) (rec_f  step_f f (addn x0 x2))).
        rewrite <- R_le_same. apply dist_triangle. 
        apply Numeric_Props_R.
      rewrite -> dist_comm with _ _ _ _ (rec_f _ f x0).
      apply Rplus_lt_compat;
        apply contraction_cauchy_crit_aux; auto;
        try(simpl; lra);
        rewrite to_R_pow_nat; auto.
        apply Numeric_Props_R.
    Qed.

    Lemma func_converge: forall (f g : T -> R) (eps : R) (x : T),
      0 < eps -> exists n0 : nat, forall n : nat, (n0 <= n)%coq_nat -> R_dist (rec_f  step_f f n x) (rec_f  step_f g n x) < eps.
    Proof.
      intros.
      destruct (total_order_T 0 (dist f g)).
      2: { exfalso. apply lt_not_le in l. apply l. apply dist_ge_0. }
      destruct s.
      2:{ 
        exists O.
        intros.
        rewrite <- R_dist_same.
        apply le_lt_trans with (dist (rec_f  step_f f n) (rec_f  step_f g n)).
          apply dist_ub. 
          apply Numeric_Props_R.
        rewrite eq_dist_0.
          auto. 
        intros.
        apply rec_ext.
        symmetry in e.
        intros.  
        apply dist_0_eq with _ _ _ x1 in e.
        auto.
      }
      destruct (total_order_T 0 q).
      2: { apply lt_not_le in l0. exfalso. apply l0. apply (contr_pos contraction). }
      destruct s.
      2:{ 
        exists (S O).
        intros.
        rewrite <- R_dist_same.
        apply le_lt_trans with (dist (rec_f  step_f f n) (rec_f  step_f g n)).
          apply dist_ub.
          apply Numeric_Props_R.
        destruct n.
          inversion H0.
        rewrite q0_rec0; auto.
      }
      destruct exists_pow_lt with q (Rdiv eps (dist f g)).
        apply (contr_pos contraction).
        apply (contr_lt_1 contraction).
        apply Rdiv_lt_0_compat. auto. simpl in l. auto.
      exists x0.
      intros.
      rewrite <- R_dist_same.
      apply le_lt_trans with (dist (rec_f  step_f f n) (rec_f  step_f g n)).
        apply dist_ub.
        apply Numeric_Props_R.
      apply le_lt_trans with (pow_nat q n * dist f g).
        apply rec_dist.
      apply Rmult_lt_reg_r with (Rinv (dist f g)).
      { apply Rinv_0_lt_compat. auto. }
      simpl.
      rewrite Rmult_assoc.
      rewrite Rinv_r.
      2:{ apply lt_not_eq in l. auto. }
      rewrite Rmult_1_r.
      apply Rle_lt_trans with (q ^ x0)%R; auto.
      assert(pow_nat q n <= pow_nat q x0); auto.
      apply pow_nat_le1_le; auto.
        apply le_lt_weak. apply (contr_lt_1 contraction).
    Qed.


    Lemma limit_unique: forall (f g : T->R) (a : T) (x : R),
      Un_cv (fun n => (rec_f  step_f f n) a) x -> Un_cv (fun n => (rec_f  step_f g n) a) x.
    Proof.
      intros.
      unfold Un_cv in *.
      intros.
      destruct func_converge with f g (Rdiv eps 2) a.
        simpl. lra.
      destruct H with (Rdiv eps 2).
        lra.
      exists (Nat.max x0 x1).
      intros.
      apply Rle_lt_trans with (R_dist (rec_f  step_f g n a) (rec_f  step_f f n a) + R_dist (rec_f  step_f f n a) x).
        apply R_dist_tri. 
      apply Rlt_le_trans with (Rdiv eps 2 + Rdiv eps 2)%R.
      2:{ lra. }
      unfold ge in *.
      apply Rplus_lt_compat.
        rewrite R_dist_sym. apply H1. apply Nat.le_trans with (Nat.max x0 x1); auto. apply Nat.le_max_l.
      apply H2. apply Nat.le_trans with (Nat.max x0 x1); auto. apply Nat.le_max_r.
    Qed.

    Definition converge_func (x : T) : R.
      destruct R_complete with (fun n => (rec_f  step_f (fun _ => 0) n) x).
        apply contraction_cauchy_crit.
      exact x0.
    Defined.


    Lemma converge_func_correct: forall (f : T->R) (x : T),
      Un_cv (fun n => (rec_f  step_f f n) x) (converge_func x).
    Proof.
      intros.
      assert (Un_cv (fun n => (rec_f  step_f (fun _ => 0) n) x) (converge_func x)).
      { unfold converge_func. destruct R_complete. auto. }
      apply limit_unique with _ f _ _ in H; auto.
    Qed.

    Lemma func_converge_strong: forall (f : T->R) (eps : R),
            0 < eps -> exists N : nat, forall (x : T) (n : nat), (n >= N)%coq_nat ->
              R_dist (rec_f  step_f f n x)
                 (converge_func x) < eps.
  Proof. 
    intros.
    destruct converge_list_strong with T l (fun s n => to_R ((rec_f  step_f f n) s)) converge_func eps; auto.
    { intros. apply converge_func_correct. }
    exists x.
    intros.
    apply H0; auto.
    apply all_T_in.
  Qed.

  Lemma rec_fixpoint: forall (x : T),
      (step_f converge_func) x = converge_func x.
    Proof.
      intros.
      assert(Un_cv (fun n => rec_f  step_f converge_func (S n) x) ((step_f converge_func) x)).
      {
        simpl.
        unfold Un_cv in *.
        intros.
        destruct (contr_pos contraction).
        2: { 
          exists (S O). intros. destruct n.
            inversion H1.
          rewrite <- R_dist_same.
          apply Rle_lt_trans with (dist
            (rec_f  step_f (step_f converge_func) (S n))
            (step_f converge_func)).
            simpl. rewrite <- R_le_same. rewrite rec_step_reverse. apply dist_ub.
            apply Numeric_Props_R.
          apply Rle_lt_trans with 0; auto.
          right.
          apply  eq_dist_0.
          intros.
          assert(rec_f  step_f (step_f converge_func) (S n) x0 = rec_f  step_f converge_func (S O) x0).
            apply dist_0_eq. apply q0_rec0. auto.
          rewrite H2. auto.
        }
        destruct func_converge_strong with (converge_func) (Rdiv eps q).        
          apply Rdiv_lt_0_compat; auto.
        exists x0.
        intros.
        rewrite <- R_dist_same.
        rewrite <- R_lt_same.
        apply le_lt_trans with (dist (rec_f  step_f converge_func (S n))  (step_f converge_func)).
          apply dist_ub.
          apply Numeric_Props_R.
        simpl (rec_f  step_f converge_func n.+1).
        apply le_lt_trans with ( q * dist (rec_f  step_f converge_func n) (converge_func)).
          apply (is_contr contraction).
        rewrite mult_lt_compat_l.
        2:{ simpl. apply Rinv_0_lt_compat. apply H0. }
        simpl.
        rewrite <- Rmult_assoc.
        rewrite Rinv_l.
        2:{ apply lt_not_eq in H0. auto. }
        rewrite Rmult_1_l.
        unfold dist.
        rewrite <- R_lt_same.
        apply mapmax_ne_lt_const.
        intros.
        rewrite Rmult_comm.
        rewrite R_dist_same.
        auto.
      }
      apply UL_sequence with _ _ (converge_func x) in H; auto.
      apply Ratan.Un_cv_ext with (fun n => rec_f step_f (step_f converge_func) n x).
        intros. simpl. rewrite rec_step_reverse. auto.
      apply converge_func_correct.
    Qed.

    Lemma step_converge0: forall (f : T->R), Un_cv (fun n => dist (rec_f step_f f n) (step_f (rec_f step_f f n))) 0.
    Proof.
      intros.
      unfold Un_cv.
      intros. 
      assert(forall n, step_f (rec_f step_f f n) = rec_f step_f f (S n)). auto.
      destruct (total_order_T 0 (dist f (step_f f))).
      2:{ exfalso. apply lt_not_le in l. apply l. apply dist_ge_0. }
      destruct s.
      2:{ 
        exists O.
        intros.
        rewrite <- R_dist_same.
        rewrite neg_plus_id.
        rewrite plus_id_r.
        rewrite abs_posb.
        2:{ apply leb_true_iff. apply dist_ge_0. }
        apply Rle_lt_trans with 0; auto.
        right.
        rewrite H0.
        apply step0_rec_nm. auto.
      }
      destruct (total_order_T 0 q).
      2: { exfalso. apply lt_not_le in l0. apply l0. apply (contr_pos _). }
      destruct s.
      2: { 
        exists (S O). intros.
        unfold R_dist.
        rewrite Rminus_0_r.
        rewrite <- R_abs_same.
        rewrite <- R_lt_same.
        rewrite abs_posb.
        2: { apply leb_true_iff. apply dist_ge_0. }
        destruct n. inversion H1.
        rewrite <- rec_step_reverse.
        rewrite q0_rec0; auto.
      }
      destruct exists_pow_lt with q (eps * Rinv ( dist f (step_f f))); auto.
        apply contr_pos.
        apply contr_lt_1.
        simpl. apply Rmult_lt_0_compat; auto.
          apply Rinv_0_lt_compat. auto.
      exists x.
      intros.
      rewrite <- R_dist_same.
      rewrite neg_plus_id.
      rewrite plus_id_r.
      rewrite abs_posb.
      2:{ apply leb_true_iff. apply dist_ge_0. }
      rewrite <- R_lt_same.
      rewrite <- rec_step_reverse.
      apply le_lt_trans with  (pow_nat (contr contraction) n * dist f (step_f f)).
      2: { 
        rewrite R_lt_same. apply Rmult_lt_reg_r with (Rinv (dist f (step_f f))).
          apply Rinv_0_lt_compat. auto.
        rewrite Rmult_assoc.
        rewrite Rinv_r.
        2: { apply lt_not_eq in l. auto. }
        rewrite Rmult_1_r.
        apply Rle_lt_trans with (pow_nat q x)%R; auto.
        rewrite <- R_le_same. apply pow_nat_le1_le; auto. apply le_lt_weak. apply (contr_lt_1 _).
      }
      apply rec_dist.
    Qed.

    Lemma fixpoint_limit: forall (f : T->R), (forall x, step_f f x = f x) ->
        (forall x, Un_cv (fun n => rec_f  step_f f n x) (f x)).
    Proof.
      intros.
      unfold Un_cv.
      exists O.
      intros.
      apply Rle_lt_trans with 0; auto.
      rewrite <- R_le_same.
      rewrite <- R_dist_same.
      apply le_trans with (dist (rec_f  step_f f n) f).
        apply dist_ub.
        apply Numeric_Props_R.
      right.
      rewrite dist_comm.
      apply step0_rec_n.
      apply eq_dist_0. auto.
    Qed.

    Lemma fixpoint_unique: forall (f: T->R) ,
        (forall x, step_f f x = f x) ->
        (forall x, f x = converge_func x).
    Proof.
      intros.
      apply UL_sequence with (fun n => rec_f  step_f f n x).
        apply fixpoint_limit. auto.
      apply converge_func_correct.
    Qed.

    Lemma dist_converge_func_step_r : forall (f : T->R), dist f (step_f converge_func) = dist f converge_func.
    Proof.
      intros.
      unfold max_dist.
      apply mapmax_ne_ext. intros.
      rewrite rec_fixpoint. auto.
    Qed.

    Lemma dist_fixpoint_step_ub: forall (f : T->R),
        ((1+ - q) * dist f converge_func <= dist f (step_f f)).
    Proof.
      intros.
      rewrite plus_mult_distr_r.
      enough(dist f converge_func  <=  dist f (step_f f) + q * dist f converge_func).
      { 
        replace(_ <= _) with (1 * dist f converge_func + - q * dist f converge_func <= dist f (step_f f))%R; auto.
        replace(_ <= _) with (dist f converge_func <= dist f (step_f f) + q * dist f converge_func)%R in H; auto.
        lra.
      }
      apply le_trans with (dist f (step_f f) + dist (step_f f) converge_func).
        apply dist_triangle. apply Numeric_Props_R. 
      apply plus_le_compat_l.
      rewrite <- dist_converge_func_step_r.
      apply is_contr.
    Qed.

  End banach_R.


  Lemma contraction_fixpoint_ext: forall (c1 c2 : @contraction_func R _), 
      (forall (f1 : x_t c1 -> R ) (f2 : x_t c2 -> R), JMeqfun f1 f2 -> JMeqfun ( step c1 f1 ) (step c2 f2)) ->
      JMeqfun (converge_func c1) (converge_func c2).
  Proof.
    unfold JMeqfun.
    intros.
    edestruct (JMeq_exists_convert (T1:=x_t c1) (T2 := x_t c2) ) as [f1_2]. eauto.    
    edestruct (JMeq_exists_convert (T1:=x_t c2) (T2 := x_t c1) ) as [f2_1]. eauto.    
    destruct (H1 a b). destruct (H2 b a).    
    rewrite <- (@fixpoint_unique c1 (fun x : x_t c1 => converge_func c2 (f1_2 x)) ).
      rewrite H3; auto. 
    intros.
    erewrite -> (H _ (converge_func c2 ) _ x (f1_2 x) ).
    2: { rewrite H1; auto. }
    apply rec_fixpoint.
    Unshelve.
      intros.
      simpl.
      f_equal.
      apply H1. auto.
  Qed.    
    
  

  Record R_Nt_relation {Nt : Type} `{numeric_t : Numerics.Numeric Nt} `{@Numerics.Numeric_R_inj Nt numeric_t} : Type :=
    R_Nt_relation_mk {
      relation_contr : @contraction_func R _;  
      Nt_step : ((x_t relation_contr) -> Nt) -> ((x_t relation_contr) -> Nt);
      R_Nt_relates : forall (f : x_t relation_contr->Nt) (x : x_t relation_contr), 
        ((step relation_contr) (fun x'=> to_R (f x')) ) x = to_R ((Nt_step f) x)
    }.

  Section banach_Nt_R.
    Context {Nt:Type} `{Numerics.Numeric Nt} `{Nt_R_inj : @Numerics.Numeric_R_inj Nt H}.
    Variable relation : R_Nt_relation.


    Local Notation contr := (relation_contr relation).
    Local Notation T := (x_t (relation_contr relation)).
    Local Notation step_f := (step (relation_contr relation)).
    Local Notation Nt_step_f := (Nt_step relation).

    Lemma R_Nt_rec_relates: forall (f : (T->Nt)) (n : nat) (x : T),
      (rec_f step_f (fun x' => to_R (f x')) n) x = to_R ((rec_f Nt_step_f f n ) x).
    Proof.
      intros.
      generalize x.
      induction n; auto. intros.
      simpl; rewrite <- (R_Nt_relates relation).
      apply (step_ext contr). auto.
    Qed.


    Lemma Cauchy_crit_to_R: forall (f : (T->Nt)) (x : T),
      Cauchy_crit (fun n => to_R ((rec_f Nt_step_f f n) x)).
    Proof.
      intros.
      unfold Cauchy_crit.
      intros.
      destruct contraction_cauchy_crit with contr x (fun x => to_R (f x)) eps; auto.
      exists x0.
      intros.
      repeat rewrite <- R_Nt_rec_relates. auto.
    Qed.
  End banach_Nt_R.    

End banach.


         
    





      

