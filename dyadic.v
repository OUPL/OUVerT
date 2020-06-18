Require Import ZArith PArith QArith ProofIrrelevance.
Require Import Lia.

Record DO : Set :=
  Dmake { num : Z;
          den : positive }.

Definition pow_pos (p r : positive) : positive :=
  Pos.iter (Pos.mul p) 1%positive r.

Lemma pow_pos_Zpow_pos p r : Zpos (pow_pos p r) = Z.pow_pos (Zpos p) r.
Proof.
  unfold pow_pos, Z.pow_pos.
  rewrite !Pos2Nat.inj_iter; generalize (Pos.to_nat r) as n; intro.
  revert p; induction n; auto.
  intros p; simpl; rewrite <-IHn; auto.
Qed.

Definition DO_to_Q (d : DO) :=
  Qmake (num d) (shift_pos (den d) 1).

(* Coercion DO_to_Q : DO >-> Q. *)

Definition DO0 : DO := Dmake 0 1.
Definition DO1 : DO := Dmake 2 1.

Lemma DO_to_Q0' : DO_to_Q DO0 = 0 # 2.
Proof. auto. Qed.

Lemma DO_to_Q0 : DO_to_Q DO0 == 0.
Proof. rewrite DO_to_Q0'; unfold Qeq; simpl; auto. Qed.

Lemma DO_to_Q1' : DO_to_Q DO1 = 2 # 2.
Proof. auto. Qed.

Lemma DO_to_Q1 : DO_to_Q DO1 == 1.
Proof. rewrite DO_to_Q1'; unfold Qeq; simpl; auto. Qed.

Definition DOadd (d1 d2 : DO) : DO :=
  match d1, d2 with
  | Dmake x1 y1, Dmake x2 y2 =>
    if Pos.ltb y1 y2 then
      Dmake (Z.pow_pos 2 (y2 - y1) * x1 + x2) y2
    else if Pos.ltb y2 y1 then 
           Dmake (Z.pow_pos 2 (y1 - y2) * x2 + x1) y1
         else Dmake (x1 + x2) y1
  end.

Lemma Qdiv_mult (s q r : Q) :
  ~ s == 0 -> 
  (q / r) == (q * s) / (r * s).
Proof.
  intros H; unfold Qdiv.
  assert (q * s * /(r * s) == q * /r) as ->.
  { rewrite Qinv_mult_distr, (Qmult_comm (/r)), Qmult_assoc.
    rewrite <-(Qmult_assoc q), Qmult_inv_r, Qmult_1_r; auto.
    apply Qeq_refl. }
  apply Qeq_refl.
Qed.

Lemma Qdiv_1_r q : q / 1 == q.
Proof.
  unfold Qdiv, Qinv; simpl; rewrite Qmult_1_r.
  apply Qeq_refl.
Qed.

Lemma Zdiv_pos0 (x y : positive) : (Zpos (x~0) / Zpos (y~0) = Zpos x / Zpos y)%Z.
Proof.
  rewrite Pos2Z.inj_xO, (Pos2Z.inj_xO y).
  rewrite Zdiv_mult_cancel_l; auto.
  inversion 1.
Qed.  

Lemma Zpow_pos_2exp (x y : nat) :
  (y < x)%nat -> 
  Z.pow 2 (Z.of_nat (x - y)) = (Z.pow 2 (Z.of_nat x) / Z.pow 2 (Z.of_nat y))%Z.
Proof.
  intros H; rewrite <-!two_power_nat_equiv; unfold two_power_nat.
  revert y H; induction x; simpl.
  { destruct y; try solve[inversion 1]. }
  destruct y; simpl.
  { intros H; rewrite Zdiv_1_r; auto. }
  intros H.
  rewrite IHx.
  { rewrite Zdiv_pos0; auto. }
  apply lt_S_n; auto.
Qed.

Lemma Pos_iter_swap' T f g (r : T) (x : positive) :
  (forall t, f (g t) = t) -> 
  Pos.iter f (Pos.iter g r x) x = r.
Proof.
  rewrite 2!Pos2Nat.inj_iter.
  assert (H: exists y, Pos.to_nat x = Pos.to_nat y).
  { exists x; auto. }
  revert H; generalize (Pos.to_nat x) as n; intros n H.
  revert r; induction n; simpl; auto.
  intros r H2.
  destruct (Nat.eq_dec n 0).
  { subst n.
    simpl.
    rewrite H2; auto. }
  assert (H3: exists y, n = Pos.to_nat y).
  { exists (Pos.of_nat n).
    rewrite Nat2Pos.id; auto. }
  destruct H3 as [y H3].
  subst n.
  rewrite <-Pos2Nat.inj_iter.
  rewrite <-Pos.iter_swap.
  rewrite H2.
  rewrite Pos2Nat.inj_iter.
  apply IHn; auto.
  exists y; auto.
Qed.  

Lemma Pos_lt_Zpos_Zlt x y :  
  (x < y)%positive -> 
  (Zpos' x < Zpos' y)%Z.
Proof.
  unfold Z.lt; simpl; rewrite <-Pos.ltb_lt.
  rewrite Pos.ltb_compare.
  destruct (Pos.compare x y); auto; try solve[inversion 1].
Qed.  

Lemma Zlt_le x y : (x < y -> x <= y)%Z.
Proof.
  unfold Z.le; intros H.
  generalize (Zlt_compare _ _ H).
  destruct (Z.compare x y); try solve[inversion 1|auto].
  intros _; inversion 1.
Qed.

Lemma Zpow_pos_div x y :
  (y < x)%positive -> 
  (Z.pow_pos 2 x # 1) * / (Z.pow_pos 2 y # 1) == Z.pow_pos 2 (x - y) # 1.
Proof.
  intros H; rewrite !Z.pow_pos_fold.
  assert (Zpos (x - y) = (Zpos x - Zpos y)%Z) as ->.
  { apply Pos2Z.inj_sub; auto. }
  rewrite Z.pow_sub_r; try omega.
  rewrite <-Z.pow_sub_r.
  { unfold Qmult, Qinv; simpl.
    assert (exists p, Z.pow_pos 2 y = Zpos p).
    { unfold Z.pow_pos.
      rewrite Pos2Nat.inj_iter.
      generalize (Pos.to_nat y); induction n.
      { simpl. exists 1%positive; auto. }
      simpl in IHn|-*.
      destruct IHn as [p H2]; rewrite H2; exists (p~0%positive); auto. }
    destruct H0 as [p H1]; rewrite H1; simpl.
    unfold Qeq; simpl; rewrite <-H1.
    rewrite Z.pos_sub_gt; auto.
    rewrite 2!Z.pow_pos_fold.
    assert (2 ^ Z.pos (x - y) * 2 ^ Z.pos y = 2 ^ Z.pos x)%Z as ->.
    { assert (Zpos (x - y) = (Zpos x - Zpos y)%Z) as ->.
      { rewrite <-Z_pos_sub_gt.
        { rewrite <-Pos2Z.add_pos_neg.
          unfold Z.sub; auto. }
        rewrite Pos.gt_lt_iff; auto. }
      assert (Hbounds : (0 <= Z.pos y <= Z.pos x)%Z).
      { split.
        { apply Pos2Z.is_nonneg. }
        apply Zlt_le.
        apply Pos_lt_Zpos_Zlt; auto. }
      rewrite Z.pow_sub_r; auto; [|inversion 1].
      rewrite <-Z.shiftr_div_pow2; [|apply Pos2Z.is_nonneg].
      rewrite <-Z.shiftl_mul_pow2; [|apply Pos2Z.is_nonneg].
      rewrite <-Z.shiftl_1_l.
      rewrite Z.shiftr_shiftl_l; [|apply Pos2Z.is_nonneg].
      rewrite Z.shiftl_shiftl.
      { rewrite Z.sub_simpl_r; auto. }
      destruct Hbounds.
      apply Zle_minus_le_0; auto. }
    rewrite 2!Zmult_1_r; auto. }
  { inversion 1. }
  split.
  { apply Pos2Z.is_nonneg. }
  unfold Z.le, Z.compare; rewrite H; inversion 1. 
  split.
  { apply Pos2Z.is_nonneg. }
  unfold Z.le, Z.compare; rewrite H; inversion 1. 
Qed.

Lemma Qinv_neq (n : Q) : ~0 == n -> ~0 == / n.
Proof.
  unfold Qeq, Qinv; simpl.
  destruct (Qnum _); simpl; auto.
  { intros _ H.
    generalize (Pos2Z.is_pos (Qden n * 1)).
    rewrite <-H; inversion 1. }
  intros _ H.
  generalize (Zlt_neg_0 (Qden n * 1)).
  rewrite <-H; inversion 1.
Qed.  

Lemma Qdiv_neq_0 n m : ~n==0 -> ~m==0 -> ~(n / m == 0).
Proof.
  intros H H1 H2.
  unfold Qdiv in H2.
  apply Qmult_integral in H2; destruct H2; auto.
  assert (H2: ~0 == m).
  { intros H2; rewrite H2 in H1; apply H1; apply Qeq_refl. }
  apply (Qinv_neq _ H2); rewrite H0; apply Qeq_refl.
Qed.  

Lemma Qmake_neq_0 n m : (~n=0)%Z -> ~(n # m) == 0.
Proof.
  intros H; unfold Qeq; simpl; intros H2.
  rewrite Zmult_1_r in H2; subst n; apply H; auto.
Qed.

Lemma Zpow_pos_neq_0 n m : (n<>0 -> Z.pow_pos n m <> 0)%Z.
Proof.
  intros H0.
  unfold Z.pow_pos.
  apply Pos.iter_invariant.
  { intros x H H2.
    apply Zmult_integral in H2; destruct H2.
    { subst; apply H0; auto. }
    subst x; apply H; auto. }
  inversion 1.
Qed.

Lemma Zmult_pow_plus x y r :
  (r <> 0)%Z -> 
  x * inject_Z (Z.pow r (Z.pos y)) / inject_Z (Z.pow r (Z.pos y+Z.pos y)) ==
  x / inject_Z (Z.pow r (Z.pos y)).
Proof.
  intros H; unfold inject_Z.
  assert (Hy: (Z.pos y >= 0)%Z).
  { generalize (Pos2Z.is_nonneg y).
    unfold Z.le, Z.ge; intros H2 H3.
    destruct (Zle_compare 0 (Z.pos y)); auto. }
  rewrite Zpower_exp; auto.
  unfold Qdiv.
  rewrite <-Qmult_assoc.
  assert (r^(Z.pos y) * r^(Z.pos y) # 1 == (r^(Z.pos y)#1) * (r^(Z.pos y)#1)) as ->.
  { unfold Qmult; simpl; apply Qeq_refl. }
  rewrite Qinv_mult_distr.
  rewrite (Qmult_assoc (r^(Z.pos y)#1)).
  rewrite Qmult_inv_r, Qmult_1_l.
  { apply Qeq_refl. }
  apply Qmake_neq_0; intros H2.
  apply (Zpow_pos_neq_0 _ _ H H2).
Qed.  

Lemma DOadd_ok d1 d2 :
  DO_to_Q (DOadd d1 d2) == DO_to_Q d1 + DO_to_Q d2.
Proof.
  destruct d1, d2; simpl.
  generalize den0 as X; intro.
  generalize num0 as Y; intro.
  generalize den1 as Z; intro.
  generalize num1 as W; intro.
  unfold Qplus; simpl.
  rewrite !shift_pos_correct, Qmake_Qdiv, !Pos2Z.inj_mul, !shift_pos_correct.
  rewrite !Zmult_1_r, !inject_Z_plus, !inject_Z_mult.
  assert (inject_Z (Z.pow_pos 2 X) * inject_Z (Z.pow_pos 2 Z) =
          inject_Z (Z.pow_pos 2 (X + Z))) as ->.
  { rewrite <-inject_Z_mult.
    symmetry; rewrite !Zpower_pos_nat.
    rewrite Pos2Nat.inj_add, Zpower_nat_is_exp; auto. }
  destruct (Pos.ltb X Z) eqn:H.
  { rewrite (Qdiv_mult (1 / inject_Z (Z.pow_pos 2 X))).
    assert (((inject_Z Y * inject_Z (Z.pow_pos 2 Z) +
              inject_Z W * inject_Z (Z.pow_pos 2 X)) *
             (1 / inject_Z (Z.pow_pos 2 X)) ==
             inject_Z Y * inject_Z (Z.pow_pos 2 (Z - X)) + inject_Z W)) as ->.
    { unfold Qdiv; rewrite Qmult_1_l.
      rewrite Qmult_plus_distr_l.
      unfold inject_Z.
      rewrite <-Qmult_assoc.
      assert ((Z.pow_pos 2 Z # 1) * / (Z.pow_pos 2 X # 1) ==
              Z.pow_pos 2 (Z - X) # 1) as ->.
      { rewrite Zpow_pos_div.
        apply Qeq_refl.
        rewrite <-Pos.ltb_lt; auto. }
      apply Qplus_inj_l.
      rewrite <-Qmult_assoc, Qmult_inv_r.
      { rewrite Qmult_1_r; apply Qeq_refl. }
      rewrite Zpower_pos_nat, Zpower_nat_Z.
      unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
      { omega. }
      omega. }
    assert (inject_Z (Z.pow_pos 2 (X + Z)) * (1 / inject_Z (Z.pow_pos 2 X)) ==
            inject_Z (Z.pow_pos 2 Z)) as ->.
    { unfold Qdiv.
      rewrite Qmult_assoc, Qmult_comm, Qmult_assoc.
      rewrite (Qmult_comm (/_)).
      assert (inject_Z (Z.pow_pos 2 (X + Z)) * / inject_Z (Z.pow_pos 2 X) ==
              inject_Z (Z.pow_pos 2 Z)) as ->.
      { rewrite Zpower_pos_is_exp, inject_Z_mult.
        rewrite (Qmult_comm (inject_Z (Z.pow_pos 2 X))).
        rewrite <-Qmult_assoc, Qmult_inv_r.
        { rewrite Qmult_1_r; apply Qeq_refl. }
        unfold inject_Z; rewrite Zpower_pos_nat, Zpower_nat_Z.
        unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
        { omega. }
        omega. }
      rewrite Qmult_1_r; apply Qeq_refl. }
    unfold DO_to_Q; simpl.
    rewrite <-inject_Z_mult, <-inject_Z_plus.
    assert (Z.pow_pos 2 Z = Z.pow_pos 2 Z * Z.pos 1)%Z as ->.
    { rewrite Zmult_1_r; auto. }
    rewrite <-shift_pos_correct, <-Qmake_Qdiv.
    rewrite Zmult_comm; apply Qeq_refl; auto.
    apply Qdiv_neq_0. { apply Q_apart_0_1. }
    unfold inject_Z; apply Qmake_neq_0.
    apply Zpow_pos_neq_0. inversion 1. }
  destruct (Pos.ltb Z X) eqn:H'.
  { rewrite (Qdiv_mult (1 / inject_Z (Z.pow_pos 2 Z))).
    assert (((inject_Z Y * inject_Z (Z.pow_pos 2 Z) +
              inject_Z W * inject_Z (Z.pow_pos 2 X)) *
             (1 / inject_Z (Z.pow_pos 2 Z)) ==
             inject_Z Y + inject_Z W * inject_Z (Z.pow_pos 2 (X - Z)))) as ->.
    { unfold Qdiv; rewrite Qmult_1_l.
      rewrite Qmult_plus_distr_l.
      unfold inject_Z.
      rewrite <-(Qmult_assoc (W # 1)).
      assert ((Z.pow_pos 2 X # 1) * / (Z.pow_pos 2 Z # 1) ==
              Z.pow_pos 2 (X - Z) # 1) as ->.
      { rewrite Zpow_pos_div.
        apply Qeq_refl.
        rewrite <-Pos.ltb_lt; auto. }
      apply Qplus_inj_r.
      rewrite <-Qmult_assoc, Qmult_inv_r.
      { rewrite Qmult_1_r; apply Qeq_refl. }
      rewrite Zpower_pos_nat, Zpower_nat_Z.
      unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
      { omega. }
      omega. }
    assert (inject_Z (Z.pow_pos 2 (X + Z)) * (1 / inject_Z (Z.pow_pos 2 Z)) ==
            inject_Z (Z.pow_pos 2 X)) as ->.
    { unfold Qdiv.
      rewrite Qmult_assoc, Qmult_comm, Qmult_assoc.
      rewrite (Qmult_comm (/_)).
      assert (inject_Z (Z.pow_pos 2 (X + Z)) * / inject_Z (Z.pow_pos 2 Z) ==
              inject_Z (Z.pow_pos 2 X)) as ->.
      { rewrite Zpower_pos_is_exp, inject_Z_mult.
        rewrite <-Qmult_assoc, Qmult_inv_r.
        { rewrite Qmult_1_r; apply Qeq_refl. }
        unfold inject_Z; rewrite Zpower_pos_nat, Zpower_nat_Z.
        unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
        { omega. }
        omega. }
      rewrite Qmult_1_r; apply Qeq_refl. }
    unfold DO_to_Q; simpl.
    rewrite <-inject_Z_mult, <-inject_Z_plus.
    assert (Z.pow_pos 2 X = Z.pow_pos 2 X * Z.pos 1)%Z as ->.
    { rewrite Zmult_1_r; auto. }
    rewrite <-shift_pos_correct, <-Qmake_Qdiv.
    rewrite Zmult_comm, Z.add_comm; apply Qeq_refl.
    apply Qdiv_neq_0. { apply Q_apart_0_1. }
    unfold inject_Z; apply Qmake_neq_0.
    apply Zpow_pos_neq_0. inversion 1. }
  assert (H1: X = Z).
  { generalize H'; rewrite Pos.ltb_antisym.
    generalize H; unfold Pos.ltb, Pos.leb.
    destruct (X ?= Z)%positive eqn:H2; try solve[inversion 1|inversion 2].
    intros _ _.
    apply Pos.compare_eq; auto. }
  (* eq case *)
  subst Z; unfold DO_to_Q; simpl; clear H H'.
  unfold Qdiv; rewrite Qmult_plus_distr_l.
  assert (inject_Z Y * inject_Z (Z.pow_pos 2 X) *
          / inject_Z (Z.pow_pos 2 (X + X)) ==
          inject_Z Y / inject_Z (Z.pow_pos 2 X)) as ->.
  { apply Zmult_pow_plus; inversion 1. }
  assert (inject_Z W * inject_Z (Z.pow_pos 2 X) *
          / inject_Z (Z.pow_pos 2 (X + X)) ==
          inject_Z W / inject_Z (Z.pow_pos 2 X)) as ->.
  { apply Zmult_pow_plus; inversion 1. }  
  unfold Qdiv; rewrite <-Qmult_plus_distr_l, Qmake_Qdiv, inject_Z_plus.
  unfold Qdiv; rewrite shift_pos_correct, Zmult_1_r; apply Qeq_refl.
Qed.

Definition DOmult (d1 d2 : DO) : DO :=
  match d1, d2 with
  | Dmake x1 y1, Dmake x2 y2 =>
    Dmake (x1 * x2) (y1 + y2)
  end.

Lemma shift_nat1_mult n m :
  (shift_nat n 1 * shift_nat m 1 = shift_nat n (shift_nat m 1))%positive.
Proof.
  induction n; simpl; auto.
  rewrite IHn; auto.
Qed.
 
Lemma DOmult_ok d1 d2 :
  DO_to_Q (DOmult d1 d2) = DO_to_Q d1 * DO_to_Q d2.
Proof.
  destruct d1, d2; simpl.
  generalize den0 as X; intro.
  generalize num0 as Y; intro.
  generalize den1 as Z; intro.
  generalize num1 as W; intro.
  unfold DO_to_Q; simpl.
  unfold Qmult; simpl.
  rewrite !shift_pos_nat, Pos2Nat.inj_add, shift_nat_plus.
  rewrite shift_nat1_mult; auto.
Qed.


Definition DOopp (d : DO) : DO :=
  match d with
  | Dmake x y => Dmake (-x) y
  end.

Lemma DOopp_ok d : DO_to_Q (DOopp d) = Qopp (DO_to_Q d).
Proof.
  destruct d; simpl.
  unfold DO_to_Q; simpl.
  unfold Qopp; simpl; auto.
Qed.

Definition DOsub (d1 d2 : DO) : DO := DOadd d1 (DOopp d2).

Lemma DOsub_ok d1 d2 :
  DO_to_Q (DOsub d1 d2) == DO_to_Q d1 - DO_to_Q d2.
Proof.
  unfold DOsub.
  rewrite DOadd_ok.
  rewrite DOopp_ok.
  unfold Qminus; apply Qeq_refl.
Qed.


Definition DOle (d1 d2 : DO) : Prop :=
  Qle (DO_to_Q d1) (DO_to_Q d2).  

Definition DOle_bool (d1 d2 : DO) : bool :=
  Z.leb (num (DOsub d1 d2)) 0 .

Lemma DO_num_neg_iff: forall d, (DO_to_Q d < 0)%Q <-> (num d < 0)%Z.
Proof.
    intros.
    split; intros;
      unfold Qlt in *; simpl in *; lia.
Qed.

Lemma DO_num_leq_0_iff: forall d, (DO_to_Q d <= 0)%Q <-> (num d <= 0)%Z.
Proof.
    intros.
    split; intros;
      unfold Qle in *; simpl in *; lia.
Qed.


Lemma DOle_bool_iff d1 d2 : (DOle_bool d1 d2 = true) <-> DOle d1 d2.
Proof.
  unfold DOle_bool, DOle.
  split; intros.
  {
    setoid_replace (DO_to_Q d2) with (DO_to_Q d2 + 0)%Q using relation Qeq.
    2: unfold Qeq; simpl; lia.
    setoid_replace (DO_to_Q d1) with (DO_to_Q d2 + (DO_to_Q d1 - DO_to_Q d2))%Q using relation Qeq.
    2: unfold Qeq; simpl; lia.
    rewrite Qplus_le_r.
    rewrite <- DOsub_ok.
    apply DO_num_leq_0_iff.
    apply Z.leb_le.
    auto.
  }
  setoid_replace (DO_to_Q d2) with (DO_to_Q d2 + 0)%Q using relation Qeq in H.
  2: unfold Qeq; simpl; lia.
  setoid_replace (DO_to_Q d1) with (DO_to_Q d2 + (DO_to_Q d1 - DO_to_Q d2))%Q using relation Qeq in H.
  2: unfold Qeq; simpl; lia.
  rewrite Qplus_le_r in H.
  rewrite <- DOsub_ok in H.
  apply DO_num_leq_0_iff in H.
  apply Z.leb_le in H.
  auto.
Qed.

Definition DOlt (d1 d2 : DO) : Prop :=
  Qlt (DO_to_Q d1) (DO_to_Q d2).  

Definition DOlt_bool (d1 d2 : DO) : bool :=
  Z.ltb (num (DOsub d1 d2)) 0 .

Lemma DOlt_bool_iff d1 d2 : (DOlt_bool d1 d2 = true) <-> DOlt d1 d2.
Proof.
  unfold DOlt_bool; unfold DOlt; split; intros.
  {
    setoid_replace (DO_to_Q d2) with (DO_to_Q d2 + 0)%Q using relation Qeq.
    2: unfold Qeq; simpl; lia.
    setoid_replace (DO_to_Q d1) with (DO_to_Q d2 + (DO_to_Q d1 - DO_to_Q d2))%Q using relation Qeq.
    2: unfold Qeq; simpl; lia.
    rewrite Qplus_lt_r.
    rewrite <- DOsub_ok.
    apply DO_num_neg_iff.
    apply Z.ltb_lt. auto.
  }
  setoid_replace (DO_to_Q d2) with (DO_to_Q d2 + 0)%Q using relation Qeq in H.
  2: unfold Qeq; simpl; lia.
  setoid_replace (DO_to_Q d1) with (DO_to_Q d2 + (DO_to_Q d1 - DO_to_Q d2))%Q using relation Qeq in H.
  2: unfold Qeq; simpl; lia.
  rewrite Qplus_lt_r in H.
  rewrite <- DOsub_ok in H.
  apply DO_num_neg_iff in H.
  apply Z.ltb_lt. auto.
Qed.  


Lemma DOeq_dec (d1 d2 : DO) : {d1=d2} + {d1<>d2}.
Proof.
  destruct d1, d2.
  destruct (Z.eq_dec num0 num1).
  { destruct (positive_eq_dec den0 den1).
    left; subst; f_equal.
    right; inversion 1; subst; apply n; auto. }
  right; inversion 1; subst; auto.
Qed.  

(*(* MICROBENCHMARK *)
Fixpoint f (n : nat) (d : D) : D :=
  match n with
  | O => d
  | S n' => DOadd d (f n' d)
  end.

Time Compute f 5000 (Dmake 3 2).
(*Finished transaction in 0.012 secs (0.012u,0.s) (successful)*)

Fixpoint g (n : nat) (q : Q) : Q :=
  match n with
  | O => q
  | S n' => Qplus q (g n' q)
  end.

Time Compute g 5000 (Qmake 3 2).
(*Finished transaction in 0.847 secs (0.848u,0.s) (successful)*)
(*Speedup on this microbenchmark: 70x*)*)

Delimit Scope DO_scope with DO.
Bind Scope DO_scope with DO.
Arguments Dmake _%Z _%positive.

Infix "<" := DOlt : DO_scope.
Infix "<=" := DOle : DO_scope.
Notation "x > y" := (DOlt y x)(only parsing) : DO_scope.
Notation "x >= y" := (DOle y x)(only parsing) : DO_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : DO_scope.

Infix "+" := DOadd : DO_scope.
Notation "- x" := (DOopp x) : DO_scope.
Infix "-" := DOsub : DO_scope.
Infix "*" := DOmult : DO_scope.

Notation "'0'" := DO0 : DO_scope.
Notation "'1'" := DO1 : DO_scope.

(** DOmax *)

Definition DOmax (d1 d2 : DO) : DO :=
  if DOlt_bool d1 d2 then d2 else d1.

(** The smallest power of 2 greater than a given rational *)

Definition Zsize (z : Z) : positive :=
  match z with
  | Z0 => 1
  | Zpos p => Pos.size p
  | Zneg p => Pos.size p
  end.

Definition Plub_aux (x : Z) (y : positive) : positive :=
  Zsize x - y.

Definition DOlub (max : DO) : DO :=
  match max with
  | Dmake x y => Dmake 1 (Plub_aux x y)
  end.

Lemma Zpos_2_mult (x : Z) (y : positive) :
  (x <= Z.pos y)%Z -> (x * 2 <= Z.pos y~0)%Z.
Proof.
  intros H.
  rewrite Zmult_comm.
  rewrite (Pos2Z.inj_xO y).
  apply Zmult_le_compat_l; auto.
  omega.
Qed.

Lemma two_power_pos_le x y :
  (x <= y)%positive -> (two_power_pos x <= two_power_pos y)%Z.
Proof.
  intros H.
  rewrite !two_power_pos_nat.
  rewrite Pos2Nat.inj_le in H.
  unfold two_power_nat, shift_nat.
  revert H.
  generalize (Pos.to_nat x) as x'; intro.
  generalize (Pos.to_nat y) as y'; intro.
  revert y'.
  induction x'; simpl.
  { intros y' _; induction y'; simpl; try solve[intros; omega].
    rewrite Pos2Z.inj_xO.
    assert ((1=1*1)%Z) as -> by (rewrite Zmult_1_r; auto).
    apply Zmult_le_compat; try omega. }
  induction y'; try solve[intros; omega].
  simpl; intros H.
  rewrite Pos2Z.inj_xO.
  rewrite
    (Pos2Z.inj_xO
       (nat_rect (fun _ : nat => positive) 1%positive 
                 (fun _ : nat => xO) y')).  
  apply Zmult_le_compat; try omega.
  { apply IHx'; omega. }
  clear - x'.
  induction x'; try (simpl; omega).
  simpl; rewrite Pos2Z.inj_xO.
  assert ((0=0*0)%Z) as -> by (rewrite Zmult_0_r; auto).
  apply Zmult_le_compat; try omega.
Qed.  

Lemma Zpow_pos_size_le x : (x <= Z.pow_pos 2 (Zsize x))%Z.
Proof.
  destruct x; simpl.
  { rewrite <-two_power_pos_correct.
    unfold two_power_pos; rewrite shift_pos_equiv; simpl; omega. }
  { generalize (Pos.lt_le_incl _ _ (Pos.size_gt p)).
    rewrite <-Pos2Z.inj_pow_pos; auto. }
  rewrite <-Pos2Z.inj_pow_pos.
  apply Zle_neg_pos.
Qed.  

Lemma Pos_succ_sub_1 p : (Pos.succ p - 1 = p)%positive.
Proof.
  set (P := fun p => (Pos.succ p - 1)%positive = p).
  change (P p); apply Pos.peano_ind; try reflexivity.
  intros r; unfold P; intros <-.
  rewrite <-Pos2Nat.inj_iff.
  rewrite nat_of_P_minus_morphism.
  { rewrite !Pos2Nat.inj_succ; auto. }
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  rewrite !Pos2Nat.inj_succ.
  rewrite Pos2Nat.inj_1.
  omega.
Qed.  

Lemma Pos_le_1_add_sub x : (x <= 1 + (x - 1))%positive.
Proof.
  set (P := fun x => (x <= 1 + (x - 1))%positive).
  change (P x).
  apply Pos.peano_ind.
  { unfold P; simpl. apply Pos.le_1_l. }
  intros p; unfold P; intros H.
  rewrite Pos_succ_sub_1.
  rewrite <-Pos.add_1_l.
  apply Pos.le_refl.
Qed.

Lemma Pos_succ_lt_2_false p : (Pos.succ p < 2)%positive -> False.
Proof.
  rewrite Pos2Nat.inj_lt.
  rewrite Pos2Nat.inj_succ.
  unfold Pos.to_nat; simpl.
  intros H.
  assert (H2: (2 < 2)%nat).
  { apply Nat.le_lt_trans with (m := S (Pos.iter_op Init.Nat.add p 1%nat)); auto.
    assert (H3: (1 <= Pos.iter_op Init.Nat.add p 1)%nat) by apply le_Pmult_nat.
    apply Peano.le_n_S; auto. }
  omega.
Qed.  

Lemma Pos2Nat_inj_2 : Pos.to_nat 2 = 2%nat.
Proof. unfold Pos.to_nat; simpl; auto. Qed.

Lemma Pos_le_2_add_sub x : 
  (1 + (x - 1) <= 2 + (x - 2))%positive.
Proof.
  rewrite Pos2Nat.inj_le.
  rewrite !Pos2Nat.inj_add.
  assert (Pos.to_nat 1 = 1%nat) as -> by auto.
  assert (Pos.to_nat 2 = 2%nat) as -> by auto.
  destruct (Pos.ltb_spec x 1).
  { elimtype False.
    apply (Pos.nlt_1_r _ H). }
  destruct (Pos.eqb_spec x 1).
  { subst x.
    simpl.
    rewrite Pos.sub_le; auto. }
  assert (H2: Pos.compare_cont Eq x 1 = Gt).
  { rewrite Pos.compare_cont_spec.
    rewrite Pos.compare_antisym.
    rewrite <-Pos.leb_le in H.
    rewrite Pos.leb_compare in H.
    generalize H; clear H.
    destruct (Pos.compare 1 x) eqn:H; simpl; auto.
    { rewrite Pos.compare_eq_iff in H; subst x; elimtype False; auto. }
    inversion 1. }
  rewrite nat_of_P_minus_morphism; auto.
  destruct (Pos.ltb_spec x 2).
  { (*x=1*)
    elimtype False; apply n.
    rewrite Pos.le_lteq in H.
    destruct H; auto.
    rewrite Pos2Nat.inj_lt in H, H0.
    rewrite <-Pos2Nat.inj_iff.
    clear - H H0.
    rewrite Pos2Nat.inj_1 in H|-*.
    rewrite Pos2Nat_inj_2 in H0.
    omega. }
  destruct (Pos.eqb_spec x 2).
  { (*x=2*)
    subst x.
    simpl.
    omega. }
  assert (H3: Pos.compare_cont Eq x 2 = Gt).
  { apply nat_of_P_gt_Gt_compare_complement_morphism.
    rewrite Pos2Nat.inj_le in H, H0.
    rewrite Pos2Nat.inj_1 in H.
    rewrite Pos2Nat_inj_2 in H0|-*.
    assert (H1: Pos.to_nat x <> 2%nat).
    { intros Hx.
      rewrite <-Pos2Nat.inj_iff, Hx in n0.
      auto. }
    omega. }
  rewrite nat_of_P_minus_morphism; auto.
  simpl.
  assert (Pos.to_nat 1 = 1%nat) as -> by auto.
  assert (Pos.to_nat 2 = 2%nat) as -> by auto.
  apply Peano.le_n_S.
  generalize (Pos.to_nat x) as m; intro.
  induction m; try solve[omega].
Qed.

Lemma Psize_minus_aux (x y : positive) : (x <= Pos.div2 (2^y) + (x - y))%positive.
Proof.
  revert y.
  apply Pos.peano_ind.
  { unfold Pos.pow, Pos.mul, Pos.iter, Pos.div2.
    apply Pos_le_1_add_sub. }
  intros p H.
  rewrite Pos.pow_succ_r; simpl.
  eapply Pos.le_trans; [apply H|].
  clear H.
  set (P := fun p =>
       forall x, (Pos.div2 (2 ^ p) + (x - p) <= 2 ^ p + (x - Pos.succ p))%positive).
  revert x.
  change (P p).
  apply Pos.peano_ind.
  { unfold P.
    intros x.
    unfold Pos.pow, Pos.mul, Pos.iter, Pos.div2.
    apply Pos_le_2_add_sub. }
  intros r; unfold P; simpl; intros IH x.
  rewrite Pos.pow_succ_r.
  unfold Pos.div2, Pos.mul.
  generalize (2^r)%positive as y; intro.
  generalize (Pos.succ r) as z; intro.
  assert (H: (x - z <= Pos.succ (x - Pos.succ z))%positive).
  { rewrite Pos.sub_succ_r.
    destruct (Pos.eqb_spec (x-z) 1).
    { rewrite e; simpl.
      rewrite Pos2Nat.inj_le, Pos2Nat.inj_1, Pos2Nat_inj_2; omega. }
    rewrite Pos.succ_pred; auto.
    apply Pos.le_refl. }
  generalize H.
  generalize (x - Pos.succ z)%positive as q; intro.
  clear IH H; intros H.
  set (Q := fun y => (y + (x - z) <= y~0 + q)%positive).
  change (Q y).
  apply Pos.peano_ind.
  { unfold Q.
    assert (2 + q = 1 + Pos.succ q)%positive as ->.
    { rewrite <-Pos.add_1_l, Pos.add_assoc; auto. }
    apply Pos.add_le_mono_l; auto. }
  intros t; unfold Q; intros IH.
  rewrite Pplus_one_succ_l.
  rewrite <-Pos.add_assoc.
  rewrite Pos.add_xO.
  rewrite <-Pos.add_assoc.  
  apply Pos.add_le_mono; auto.
  apply Pos.le_1_l.
Qed.

Lemma Psize_exp_div y : (Pos.div2 (2 ^ (Pos.size y)) <= y)%positive.
Proof.
  generalize (Pos.size_le y).
  destruct (2 ^ Pos.size y)%positive; simpl.
  { unfold Pos.le, Pos.compare; simpl.
    intros H H2.
    apply nat_of_P_gt_Gt_compare_morphism in H2.
    apply H.
    rewrite Pos.compare_cont_Gt_Gt.
    rewrite Pos2Nat.inj_ge; omega. }
  { unfold Pos.le, Pos.compare; simpl.
    intros H H2.
    apply H; auto. }
  intros _; apply Pos.le_1_l.
Qed.
  
Local Open Scope DO_scope.

Lemma DOlub_mult_le1 d : d * DOlub d <= 1.
Proof.
  unfold DOle; rewrite DOmult_ok.
  unfold DO_to_Q, Qle; destruct d as [x y]; simpl.
  rewrite Zmult_1_r; apply Zpos_2_mult.
  rewrite Pos2Z.inj_mul, !shift_pos_correct, !Zmult_1_r.
  rewrite <-Zpower_pos_is_exp.
  unfold Plub_aux.
  assert (H : (x <= Z.pow_pos 2 (Zsize x))%Z).
  { apply Zpow_pos_size_le. }
  eapply Z.le_trans; [apply H|].
  rewrite <-!two_power_pos_correct.
  apply two_power_pos_le.
  rewrite Pos2Nat.inj_le; generalize (Zsize x) as z; intro.
  clear H.
  rewrite Pos2Nat.inj_add.
  destruct (Pos.ltb_spec y z) as [H|H].
  { rewrite Pos2Nat.inj_sub; auto.
    omega. }
  assert ((z - y = 1)%positive) as ->.
  { apply Pos.sub_le; auto. }
  revert H; rewrite Pos2Nat.inj_le.
  rewrite Pos2Nat.inj_1.
  omega.
Qed.

Lemma DOlub_nonneg (d : DO) :
  0 <= d -> 0 <= DOlub d.
Proof.
  destruct d; simpl; intros H.
  unfold DOle; rewrite DO_to_Q0; unfold DO_to_Q; simpl.
  unfold Qle; simpl; omega.
Qed.

Lemma DOlub_ok (d : DO) :
  0 <= d -> 
  DOle 0 (d * DOlub d) /\ DOle (d * DOlub d) 1.
Proof.
  intros H.
  split.
  { unfold DOle; rewrite DOmult_ok.
    rewrite DO_to_Q0; apply Qmult_le_0_compat.
    { rewrite <-DO_to_Q0; auto. }
    rewrite <-DO_to_Q0; apply DOlub_nonneg; auto. }
  apply DOlub_mult_le1.
Qed.

Fixpoint DOred' (n : Z) (d : nat) : (Z * nat) :=
  match d with
  | O => (n,d)
  | S d' => if Zeven_dec n then DOred' (Z.div2 n) d'
            else (n,d)
  end.

Lemma DOred'P n d : Zodd (fst (DOred' n d)) \/ (snd (DOred' n d) = 0%nat).
Proof.
  revert n; induction d; auto.
  intros n; simpl; destruct (Zeven_dec n).
  { apply (IHd (Z.div2 n)). }
  left; simpl.
  destruct (Zodd_dec n); auto.
  destruct (Zeven_odd_dec n); auto.
  elimtype False; apply n0; auto.
Qed.  

Definition DO_of_DOred' (p : Z*nat) : DO :=
  let (x,y) := p in Dmake x (Pos.of_nat (S y)).

Definition DOred (d : DO) : DO := 
  DO_of_DOred' (DOred' (num d) (pred (Pos.to_nat (den d)))).

Lemma DOredP d : Zodd (num (DOred d)) \/ (den (DOred d) = 1%positive).
Proof.
  unfold DOred; destruct d as [x y]; simpl.
  destruct (DOred'P x (pred (Pos.to_nat y))).
  { unfold DO_of_DOred'.
    destruct (DOred' _ _); auto. }
  destruct (DOred' _ _); right; simpl in *.
  rewrite H; auto.
Qed.  

Lemma DO_of_DOred'_correct x y :
  DO_to_Q (DO_of_DOred' (DOred' x y)) == DO_to_Q (DO_of_DOred' (x,y)).
Proof.
  revert x; induction y.
  { intros x; apply Qeq_refl. }
  intros x.
  unfold DOred'; fold DOred'.
  destruct (Zeven_dec x) as [pf|pf].
  { rewrite IHy.
    unfold DO_to_Q; simpl.
    unfold Qeq; simpl.
    pattern x at 2.
    rewrite (Zeven_div2 x pf).
    rewrite 2!shift_pos_correct, 2!Zmult_1_r.
    rewrite 2!Zpower_pos_nat.
    rewrite Pos2Nat.inj_succ.
    rewrite Zpower_nat_succ_r.
    rewrite Zmult_assoc.
    pattern (Z.div2 x * 2)%Z; rewrite Zmult_comm; auto. }
  apply Qeq_refl.
Qed.  

Lemma DOred_correct d : DO_to_Q (DOred d) == DO_to_Q d.
Proof.
  unfold DOred.
  destruct d as [x y] eqn:Heq.
  simpl.
  rewrite DO_of_DOred'_correct.
  unfold DO_of_DOred'.
  rewrite <-Pos.of_nat_succ.
  generalize (Pos2Nat.is_pos y).
  destruct (Pos.to_nat y) eqn:Heq'; try omega.
  intros _; simpl.
  rewrite (SuccNat2Pos.inv n y); auto.
  apply Qeq_refl.
Qed.  

Lemma gcd_2_odd_1 x : Zodd x -> Z.gcd x 2 = 1%Z.
Proof.
  generalize (Z.gcd_divide_r x 2).
  intros H.
  generalize (Znumtheory.Zdivide_bounds _ _ H).
  generalize (Z.gcd_nonneg x 2); intros H2 H3 H4.
  assert (H5: (Z.abs (Z.gcd x 2) <= Z.abs 2)%Z).
  { apply H3; inversion 1. }
  destruct (Z.abs_eq_iff (Z.gcd x 2)) as [_ Y].
  rewrite (Y H2) in H5. clear Y.
  simpl in H5.
  clear - H2 H4 H5.
  assert (H6: (Z.gcd x 2 = 0 \/ Z.gcd x 2 = 1 \/ Z.gcd x 2 = 2)%Z).
  { omega. }
  clear H2 H5.
  destruct H6.
  { apply Z.gcd_eq_0_l in H; subst x.
    inversion H4. }
  destruct H; auto.
  generalize (Z.gcd_divide_l x 2); rewrite H.
  intros H2; apply Znumtheory.Zdivide_mod in H2.
  rewrite Zmod_odd in H2.
  rewrite <-Zodd_bool_iff in H4; rewrite H4 in H2; inversion H2.
Qed.  

Lemma gcd_2_even_2 x : Zeven x -> Z.gcd x 2 = 2%Z.
Proof.
  generalize (Z.gcd_divide_r x 2).
  intros H.
  generalize (Znumtheory.Zdivide_bounds _ _ H).
  generalize (Z.gcd_nonneg x 2); intros H2 H3 H4.
  assert (H5: (Z.abs (Z.gcd x 2) <= Z.abs 2)%Z).
  { apply H3; inversion 1. }
  destruct (Z.abs_eq_iff (Z.gcd x 2)) as [_ Y].
  rewrite (Y H2) in H5. clear Y.
  simpl in H5.
  clear - H2 H4 H5.
  assert (H6: (Z.gcd x 2 = 0 \/ Z.gcd x 2 = 1 \/ Z.gcd x 2 = 2)%Z).
  { omega. }
  clear H2 H5.
  destruct H6.
  { apply Z.gcd_eq_0_l in H; subst x.
    auto. }
  destruct H; auto.
  elimtype False.
  rewrite Znumtheory.Zgcd_1_rel_prime in H.
  destruct H. 
  assert (H2: (2 | x)%Z).
  { apply Znumtheory.Zmod_divide.
    { inversion 1. }
    rewrite Zmod_odd.
    rewrite Zodd_even_bool.
    rewrite <-Zeven_bool_iff in H4; rewrite H4.
    auto. }
  assert (H3: (2 | 2)%Z).
  { exists 1%Z; auto. }
  assert (Hcontra: (2 | 1)%Z).
  { apply H1; auto. }
  assert (2 <= 1)%Z.
  { apply Z.divide_pos_le; auto.
    omega. }
  omega.
Qed.    

Lemma gcd_x_times2_1 x y : Zodd x -> Z.gcd x y = 1%Z -> Z.gcd x (2*y) = 1%Z.
Proof.
  intros Hodd H.
  generalize (Znumtheory.Zgcd_is_gcd x y) as H2; intro.
  apply Znumtheory.Zis_gcd_gcd; try omega.
  inversion H2.
  constructor; try apply Z.divide_1_l. 
  intros w H4 H5.
  rewrite H in H3.
  apply Znumtheory.Gauss in H5; auto.
  rewrite <-Znumtheory.Zgcd_1_rel_prime.
  destruct (Zeven_odd_dec w).
  { rewrite Zeven_ex_iff in z.
    destruct z as [m H6].
    rewrite H6 in H4.
    clear - Hodd H4.
    elimtype False.
    destruct H4 as [y H4].
    rewrite Zmult_assoc in H4.
    rewrite (Zmult_comm y) in H4.
    rewrite <-Zmult_assoc in H4.
    assert (H5: Zeven x).
    { rewrite H4.
      apply Zeven_2p. }
    apply Zodd_not_Zeven in Hodd; auto. }
  apply gcd_2_odd_1; auto.
Qed.  

Lemma gcd_pow2_odd_1 x n : Zodd x -> Z.gcd x (Zpower_nat 2 n) = 1%Z.
Proof.
  induction n.
  { simpl.
    rewrite Z.gcd_1_r; auto. }
  rewrite Zpower_nat_succ_r.
  intros Hodd.
  generalize (IHn Hodd).
  intros H.
  apply gcd_x_times2_1; auto.
Qed.  

Lemma Qred_odd_pow2 x n : Zodd x -> Qred (x # pow_pos 2 n) = x # (pow_pos 2 n).
Proof.
  unfold Qred.
  generalize (Z.ggcd_gcd x (Z.pos (pow_pos 2 n))).
  generalize (Z.ggcd_correct_divisors x (Z.pos (pow_pos 2 n))).
  destruct (Z.ggcd x (Z.pos (pow_pos 2 n))) as [a [b c]]; simpl.
  intros [H0 H] H2 H3.
  subst a.
  assert (H2: Z.gcd x (Z.pos (pow_pos 2 n)) = 1%Z).
  { rewrite pow_pos_Zpow_pos, Zpower_pos_nat.
    apply gcd_pow2_odd_1; auto. }
  rewrite H2, Zmult_1_l in H.
  subst c.
  rewrite H2, Zmult_1_l in H0.
  subst b.
  auto.
Qed.  

Lemma Qred_odd_2 x : Zodd x -> Qred (x # 2) = x # 2.
Proof.
  unfold Qred.
  generalize (Z.ggcd_gcd x 2).
  generalize (Z.ggcd_correct_divisors x 2).
  destruct (Z.ggcd x 2) as [a [b c]]; simpl.
  intros [H0 H] H2 H3.
  subst a.
  assert (H2: Z.gcd x 2 = 1%Z).
  { apply gcd_2_odd_1; auto. }
  rewrite H2, Zmult_1_l in H.
  subst c.
  rewrite H2, Zmult_1_l in H0.
  subst b.
  auto.
Qed.  

Lemma shift_pos_pow_pos n : shift_pos n 1 = pow_pos 2 n.
Proof.
  rewrite shift_pos_nat.
  set (P := fun n => shift_nat (Pos.to_nat n) 1 = pow_pos 2 n).
  change (P n).
  apply Pos.peano_ind.
  { unfold P; auto. }
  intros p; unfold P; intros IH; simpl.
  rewrite Pos2Nat.inj_succ; simpl; rewrite IH.
  unfold pow_pos; simpl; auto.
  rewrite Pos.iter_succ; auto.
Qed.  

Lemma pow_pos_2inj p q : pow_pos 2 p = pow_pos 2 q -> p = q.
Proof.
  rewrite <-!shift_pos_pow_pos.
  unfold shift_pos.
  rewrite !Pos2Nat.inj_iter; intros H.
  apply Pos2Nat.inj.
  revert H.
  generalize (Pos.to_nat p) as n.
  generalize (Pos.to_nat q) as m.
  clear p q.
  induction m.
  { destruct n; auto. inversion 1. }
  destruct n; simpl.
  { inversion 1. }
  inversion 1; subst; f_equal; apply IHm; auto.
Qed.  

Lemma Qred_even_2 x :
  Zeven x -> 
  Qred (x # 2) = Z.div2 x # 1.
Proof.
  unfold Qred.
  generalize (Z.ggcd_gcd x 2).
  generalize (Z.ggcd_correct_divisors x 2).
  destruct (Z.ggcd x 2) as [a [b c]]; simpl.
  intros [H0 H] H2 H3.
  subst a.
  assert (H2: Z.gcd x 2 = 2%Z).
  { apply gcd_2_even_2; auto. }
  rewrite H2 in H.
  assert (H4: c = 1%Z).
  { omega. }
  subst c.
  rewrite H2 in H0.
  rewrite H0.
  f_equal.
  destruct b; auto.
Qed.  

Lemma Zdiv2_even_inj x y : Zeven x -> Zeven y -> Z.div2 x = Z.div2 y -> x=y.
Proof.
  intros H H1 H2.
  destruct x; destruct y; simpl in H2; auto;
  try destruct p; try destruct p0; inversion H2;
  try inversion H; try inversion H1; auto.
Qed.  

Lemma DOred_complete d1 d2 :
  DO_to_Q d1 == DO_to_Q d2 ->
  DOred d1 = DOred d2.
Proof.
  generalize (DOred_correct d1). intros <-.
  generalize (DOred_correct d2). intros <-.
  intros H.
  apply Qred_complete in H.
  unfold DO_to_Q in H|-*.
  generalize H; clear H.
  rewrite !shift_pos_pow_pos.
  destruct (DOredP d1).
  (* Zodd (num (DOred d1)) *)
  { destruct (DOredP d2).
    (* Zodd (num (DOred d2)) *)
    { rewrite !Qred_odd_pow2; auto.
      destruct (DOred d1); simpl.
      destruct (DOred d2); simpl.
      inversion 1; subst.
      f_equal.
      apply pow_pos_2inj; auto. }

    (* den (DOred d2) = 1 *)    
    rewrite H0.
    rewrite Qred_odd_pow2; auto.
    intros H2.
    assert (Hpow : pow_pos 2 1 = 2%positive) by auto.
    rewrite Hpow in H2.
    destruct (Zeven_odd_dec (num (DOred d2))).
    { assert (Qred (num (DOred d2) # 2) = Z.div2 (num (DOred d2)) # 1).
      { rewrite Qred_even_2; auto. }
      rewrite H1 in H2; clear H1.
      inversion H2.
      assert (1 < pow_pos 2 (den (DOred d1)))%positive.
      { rewrite <-shift_pos_pow_pos.
        rewrite shift_pos_nat.
        destruct (Pos2Nat.is_succ (den (DOred d1))) as [x H1].
        rewrite H1; simpl.
        generalize (shift_nat x 1); intros p.
        unfold Pos.lt, Pos.compare; simpl; auto. }
      rewrite H4 in H1.
      inversion H1. }
    rewrite <-Hpow in H2.
    rewrite Qred_odd_pow2 in H2; auto.
    rewrite Hpow in H2.
    inversion H2; subst.
    revert H3 H4 H0.
    destruct (DOred d1); simpl.
    destruct (DOred d2); simpl.
    intros -> Hx ->.
    assert (Hy: pow_pos 2 1 = pow_pos 2 den0).
    { rewrite Hx, Hpow; auto. }
    f_equal.
    apply pow_pos_2inj; auto. }

  (* den (DOred d1) = 1 *)    
  destruct (DOredP d2).
    (* Zodd (num (DOred d2)) *)
    { rewrite H.
      rewrite (Qred_odd_pow2 _ _ H0).
      intros H2.
      assert (Hpow : pow_pos 2 1 = 2%positive) by auto.
      rewrite Hpow in H2.
      destruct (Zeven_odd_dec (num (DOred d1))).
      { assert (Qred (num (DOred d1) # 2) = Z.div2 (num (DOred d1)) # 1).
        { rewrite Qred_even_2; auto. }
        rewrite H1 in H2; clear H1.
        inversion H2.
        assert (1 < pow_pos 2 (den (DOred d2)))%positive.
        { rewrite <-shift_pos_pow_pos.
          rewrite shift_pos_nat.
          destruct (Pos2Nat.is_succ (den (DOred d2))) as [x H1].
          rewrite H1; simpl.
          generalize (shift_nat x 1); intros p.
          unfold Pos.lt, Pos.compare; simpl; auto. }
        rewrite <-H4 in H1.
        inversion H1. }
      rewrite <-Hpow in H2.
      rewrite Qred_odd_pow2 in H2; auto.
      rewrite Hpow in H2.
      inversion H2; subst.
      revert H3 H4 H0.
      destruct (DOred d2); simpl.
      destruct (DOred d1); simpl.            
      intros <- Hx Hodd.
      simpl in H.
      subst den1.
      assert (Hy: pow_pos 2 1 = pow_pos 2 den0).
      { rewrite <-Hx, Hpow; auto. }
      f_equal.
      apply pow_pos_2inj; auto. }

    (* den (DOred d1) = 1 *)
    rewrite H, H0.
    assert (Hpow : pow_pos 2 1 = 2%positive) by auto.
    rewrite Hpow.
    destruct (DOred d1) as [num1 den1].
    destruct (DOred d2) as [num2 den2].
    destruct (Zeven_odd_dec num1); destruct (Zeven_odd_dec num2).
    { rewrite !Qred_even_2; auto.
      simpl.
      inversion 1; subst.
      apply Zdiv2_even_inj in H3; auto.
      subst num1.
      simpl in H0, H.
      subst; auto. }
    { rewrite Qred_even_2; auto.
      rewrite Qred_odd_2; auto.
      simpl.
      inversion 1. }
    { rewrite Qred_odd_2; auto.
      rewrite Qred_even_2; auto.
      simpl.
      inversion 1. }
    rewrite !Qred_odd_2; auto.
    inversion 1; subst.
    simpl in H0, H; subst; auto. 
Qed.

Lemma DOred'_idem x y :
  DOred' (fst (DOred' x y)) (snd (DOred' x y)) = DOred' x y.
Proof.
  destruct (DOred'P x y).
  { revert H.
    generalize (DOred' x y).
    destruct p.
    simpl; intros H.
    unfold DOred'.
    destruct n; auto.
    destruct (Zeven_dec z); auto.
    apply Zodd_not_Zeven in H; contradiction. }
  destruct (DOred' x y); simpl in H|-*; rewrite H; auto.
Qed.  

    
Lemma DOred_idem d : DOred (DOred d) = DOred d.
Proof.
  unfold DOred.
  destruct (DOred' _ _) eqn:H.
  unfold DO_of_DOred' in H.
  assert (H2: (num
           (let (x, y) :=
              DOred' (num d) (Init.Nat.pred (Pos.to_nat (den d))) in
            {| num := x; den := Pos.of_nat (S y) |})) =
              fst (DOred' (num d) (Init.Nat.pred (Pos.to_nat (den d))))).
  { destruct (DOred' _ _).
    destruct (DOred' _ _); auto. }
  rewrite H2 in H.
  assert (H3: (Init.Nat.pred
           (Pos.to_nat
              (den
                 (let (x, y) :=
                    DOred' (num d) (Init.Nat.pred (Pos.to_nat (den d))) in
                  {| num := x; den := Pos.of_nat (S y) |})))) =
              snd (DOred' (num d) (Init.Nat.pred (Pos.to_nat (den d))))).
  { destruct (DOred' _ _).
    destruct (DOred' _ _); auto.
    simpl.
    destruct n1; auto.
    rewrite Pos2Nat.inj_succ.
    unfold Init.Nat.pred.
    rewrite Nat2Pos.id; auto. }
  rewrite H3 in H.
  rewrite DOred'_idem in H.
  rewrite H; auto.
Qed.  


Lemma DOred_complete_converse d1 d2 :
  DOred d1 = DOred d2 ->
  DO_to_Q d1 == DO_to_Q d2.
Proof.
  intros.
  rewrite <- DOred_correct.
  rewrite <- (@DOred_correct d2).
  rewrite H.
  apply Qeq_refl.
Qed.

Lemma DO_lt_le_dec: forall d1 d2, {d1 < d2} + {d2 <= d1}.
Proof.
  intros.  
  unfold DOlt.
  unfold DOle.
  apply Qlt_le_dec.
Qed.


Module DORed.
  Record t : Type :=
    mk { d :> DO;
         pf : DOred d = d }.

  Definition build (d : DO) : t := @mk (DOred d) (DOred_idem d).
  
  Program Definition t0 := mk 0 _.

  Program Definition t1 := mk 1 _.

  Program Definition add (d1 d2 : t) : t :=
    mk (DOred (DOadd d1.(d) d2.(d))) _.
  Next Obligation.
    apply DOred_complete; rewrite DOred_correct; apply Qeq_refl.
  Qed.

  Program Definition sub (d1 d2 : t) : t :=
    mk (DOred (DOsub d1.(d) d2.(d))) _.
  Next Obligation.
    apply DOred_complete; rewrite DOred_correct; apply Qeq_refl.    
  Qed.

  Program Definition mult (d1 d2 : t) : t := 
    mk (DOred (DOmult d1.(d) d2.(d))) _.
  Next Obligation.
    apply DOred_complete; rewrite DOred_correct; apply Qeq_refl.        
  Qed.

  Program Definition opp (dx : t) : t := 
    mk (DOred (DOopp dx.(d))) _.
  Next Obligation.
    apply DOred_complete; rewrite DOred_correct; apply Qeq_refl.            
  Qed.

  Program Definition lub (dx : t) : t := 
    mk (DOred (DOlub dx.(d))) _.
  Next Obligation.
    apply DOred_complete; rewrite DOred_correct; apply Qeq_refl.            
  Qed.

  Program Definition of_nat (n : nat) : t :=
    mk (Dmake (2 * (Z.of_nat n)) 1) _.

  Program Fixpoint natPow (d : t) (n : nat) : t :=
    match n with
    | O => t1
    | S n' => mult d (natPow d n')
    end.


  Lemma DOred_eq (d1 d2 : t) : (DO_to_Q (d d1) == DO_to_Q (d d2))%Q -> d1 = d2.
  Proof.
    destruct d1 as [x1 pf1]; destruct d2 as [x2 pf2]; simpl.
    intros H; assert (H2: x1 = x2).
    { rewrite <-pf1, <-pf2; apply DOred_complete; auto. }
    generalize pf1 pf2; rewrite H2; intros; f_equal; apply proof_irrelevance.
  Qed.

  Lemma DOred_eq_weak: forall (d1 d2 : t), (d d1 = d d2) -> d1 = d2.
  Proof.
    intros.
    apply DOred_eq.
    destruct d1. destruct d2.
    simpl.
    simpl in H.
    rewrite H.
    apply Qeq_refl.
  Qed.
  
  Lemma addP d1 d2 :
    DO_to_Q (d (add d1 d2)) == (DO_to_Q (d d1) + DO_to_Q (d d2))%Q.
  Proof.
    unfold add; simpl.
    rewrite DOred_correct.
    rewrite DOadd_ok; apply Qeq_refl.
  Qed.    
  
  Lemma addC d1 d2 : add d1 d2 = add d2 d1.
  Proof.
    apply DOred_eq; simpl; rewrite 2!DOred_correct, 2!DOadd_ok.
    apply Qplus_comm.
  Qed.

  Lemma addA d1 d2 d3 : add d1 (add d2 d3) = add (add d1 d2) d3.
  Proof.
    apply DOred_eq; simpl.
    rewrite !DOred_correct, !DOadd_ok, !DOred_correct, !DOadd_ok.
    apply Qplus_assoc.
  Qed.    

  Lemma add0l d : add t0 d = d.
  Proof.
    unfold t0; apply DOred_eq; unfold add.
    generalize (add_obligation_1 {|d:=0;pf:=t0_obligation_1|} d).
    unfold DORed.d; rewrite DOred_correct; intros e.
    rewrite DOadd_ok, DO_to_Q0, Qplus_0_l; apply Qeq_refl.
  Qed.    
        
  Lemma subP d1 d2 :
    DO_to_Q (d (sub d1 d2)) == (DO_to_Q (d d1) - DO_to_Q (d d2))%Q.
  Proof.
    unfold sub; simpl.
    rewrite DOred_correct.
    rewrite DOsub_ok; apply Qeq_refl.
  Qed.

  Lemma multP d1 d2 :
    DO_to_Q (d (mult d1 d2)) == (DO_to_Q (d d1) * DO_to_Q (d d2))%Q.
  Proof.
    unfold mult; simpl.
    rewrite DOred_correct.
    rewrite DOmult_ok; apply Qeq_refl.
  Qed.    
  
  Lemma multC d1 d2 : mult d1 d2 = mult d2 d1.
  Proof.
    apply DOred_eq; simpl; rewrite 2!DOred_correct, 2!DOmult_ok.
    apply Qmult_comm.
  Qed.

  Lemma multA d1 d2 d3 : mult d1 (mult d2 d3) = mult (mult d1 d2) d3.
  Proof.
    apply DOred_eq; simpl.
    rewrite !DOred_correct, !DOmult_ok, !DOred_correct, !DOmult_ok.
    apply Qmult_assoc.
  Qed.    

  Lemma oppP dx :
    DO_to_Q (d (opp dx)) == (- DO_to_Q (d dx))%Q.
  Proof.
    unfold opp; simpl.
    rewrite DOred_correct.
    rewrite DOopp_ok; apply Qeq_refl.
  Qed.

  Lemma lubP (dx : t) :
    0 <= dx -> 0 <= dx * lub dx /\ dx * lub dx <= 1.
  Proof.
    intros H.
    generalize (DOlub_ok dx H); intros [H1 H2].
    unfold lub, DOle in *; simpl.
    rewrite DOmult_ok in *.
    rewrite DOred_correct in *; auto.
  Qed.

  Lemma addOppL: forall d1, add (opp d1) d1 = t0.
  Proof.
    intros.
    apply DOred_eq.
    rewrite addP.    
    simpl.
    rewrite DO_to_Q0.
    rewrite DOred_correct.
    rewrite DOopp_ok.
    rewrite Qplus_comm.
    apply Qplus_opp_r.
  Qed.
    
  Lemma addNegDistr: forall d1 d2, opp (add d1 d2) = add (opp d1) (opp d2).
  Proof.
    intros.
    apply DOred_eq.
    rewrite addP.
    repeat (rewrite oppP).
    rewrite addP.
    apply Qopp_plus.
  Qed.


  Lemma mult1L: forall d1, mult t1 d1 = d1.
  Proof.
    intros.
    apply DOred_eq.
    rewrite multP.
    rewrite DO_to_Q1.
    apply Qmult_1_l.
  Qed.

  Lemma multDistrL: forall d1 d2 d3, mult d1 (add d2 d3) = add (mult d1 d2) (mult d1 d3).
  Proof.
    intros.
    apply DOred_eq.
    rewrite multP.
    repeat (rewrite addP).
    repeat (rewrite multP).
    apply Qmult_plus_distr_r.
  Qed.

  Lemma mult0L: forall d1, mult t0 d1 = t0.
  Proof.
    intros.
    apply DOred_eq.
    rewrite multP.
    rewrite DO_to_Q0.
    apply Qmult_0_l.
  Qed.


  Lemma le_lt_or_eq: forall (t1 t2 : t), DOlt t1 t2 \/ t1 = t2 <-> DOle t1 t2.
  Proof.
    intros.
    split.
    {
      unfold DOle,DOlt in *.
      intros.
      apply Qle_lteq.
      destruct H; auto.
      rewrite H.
      right.  
      apply Qeq_refl.
    }
    intros.
    unfold DOle in H.
    rewrite Qle_lteq in H.
    destruct H; auto.
    right.
    apply DOred_eq; auto.
  Qed.


  Lemma plus_le_compat: forall (t1 t2 t3 t4 : t) , DOle t1 t2 -> DOle t3  t4 -> DOle (add t1 t3) (add t2 t4).
  Proof.
    intros.
    unfold DOle in *.
    repeat (rewrite addP).
    apply Qplus_le_compat; auto.
  Qed.


  Lemma plus_lt_le_compat: forall (t1 t2 t3 t4 : t), DOlt t1 t2 ->  DOle t3 t4 -> DOlt (add t1 t3 ) (add t2 t4).
  Proof.
    intros.
    unfold DOle,DOlt in *.
    repeat (rewrite addP).
    apply Qplus_lt_le_compat; auto.
  Qed.
    
  Lemma plus_lt_compat_l : forall t t1 t2 : t, DOlt t1 t2 -> DOlt (add t t1) (add t t2).
  Proof.
    intros.
    rewrite addC.
    rewrite addC with t2 t4.
    apply plus_lt_le_compat; auto.
    unfold DOle.
    apply Qle_refl.
  Qed.


  
  
  Lemma lt_t0_t1: t0 < t1.
  Proof.
    unfold DOlt.
    rewrite DO_to_Q0.
    rewrite DO_to_Q1.
    unfold Qlt, Z.lt.
    auto. 
  Qed.

  Lemma mult_le_compat: 
        forall (r1 r2 r3 r4 : t) , DOle t0 r1 -> DOle t0 r3 -> DOle r1  r2 -> DOle r3 r4 ->
           DOle (mult r1 r3) (mult r2   r4).
  Proof.
    intros.
    unfold DOle in *.
    repeat (rewrite multP).
    remember (DO_to_Q r1) as q1.
    remember (DO_to_Q r2) as q2.
    remember (DO_to_Q r3) as q3.
    remember (DO_to_Q r4) as q4.
    rewrite DO_to_Q0 in *.
    unfold Qle in *.
    simpl in *.
    rewrite Z.mul_1_r in *.
    repeat (rewrite Pos2Z.inj_mul).
    rewrite Z.mul_shuffle0.
    rewrite Z.mul_assoc.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_shuffle0 with (Qnum q2) (Qnum q4) (QDen q1 * QDen q3)%Z.
    rewrite Z.mul_assoc with (Qnum q2) (QDen q1) (QDen q3).
    rewrite <- Z.mul_assoc with (Qnum q2 * QDen q1)%Z (QDen q3) (Qnum q4).
    apply Zmult_le_compat; auto;
    try( apply Zmult_le_0_compat; auto ; apply Pos2Z.pos_is_nonneg).
    rewrite Z.mul_comm.
    rewrite Z.mul_comm with (QDen q3) (Qnum q4).
    auto.
  Qed.

   Lemma mult_lt_compat:
        forall (r1 r2 r3 r4 : t), DOle t0 r1 -> DOle t0 r3 -> DOlt r1 r2 -> DOlt r3 r4 ->
           DOlt (mult r1 r3) (mult r2 r4).
  Proof.
    intros.
    unfold DOle,DOlt in *.
    repeat (rewrite multP).
    remember (DO_to_Q r1) as q1.
    remember (DO_to_Q r2) as q2.
    remember (DO_to_Q r3) as q3.
    remember (DO_to_Q r4) as q4.
    rewrite DO_to_Q0 in *.
    unfold Qlt in *.
    simpl.
    repeat (rewrite Pos2Z.inj_mul).
    rewrite Z.mul_shuffle0.
    rewrite Z.mul_assoc.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_shuffle0 with (Qnum q2) (Qnum q4) (QDen q1 * QDen q3)%Z.
    rewrite Z.mul_assoc with (Qnum q2) (QDen q1) (QDen q3).
    rewrite <- Z.mul_assoc with (Qnum q2 * QDen q1)%Z (QDen q3) (Qnum q4).
    apply Zmult_lt_compat.
    {
      split; auto.
      apply Zmult_le_0_compat.
      {
        unfold Qle in H.
        simpl in *.
        rewrite Z.mul_1_r in H.
        auto.
      }
      apply Pos2Z.pos_is_nonneg.
    }
    split.
    {
      apply Zmult_le_0_compat.
      { apply Pos2Z.pos_is_nonneg. }
      unfold Qle in H0.
      simpl in *.
      rewrite Z.mul_1_r in H0.
      auto.
    }
    rewrite Z.mul_comm.
    rewrite Z.mul_comm with (QDen q3) (Qnum q4).
    auto.
  Qed.
    
  Lemma mult_lt_compat_l : forall r r1 r2 : t, DOlt t0 r -> (DOlt r1 r2 <-> DOlt (mult r r1) (mult r r2)).
  Proof.
    unfold DOlt.
    intros.
    split; intros.
    {
      repeat rewrite multP.
      unfold Qlt in *.
      simpl in *.
      apply Z.mul_pos_cancel_r in H.
      2 :{  unfold Z.lt. auto. } simpl.
      repeat rewrite <- Z.mul_assoc.
      apply Zmult_lt_compat_l; auto.
      repeat rewrite Pos2Z.inj_mul.
      repeat rewrite Z.mul_assoc.
      rewrite Z.mul_comm with (num r1) (Z.pos (shift_pos (den r) 1)).
      rewrite Z.mul_comm with (num r2) (Z.pos (shift_pos (den r) 1)).
      repeat rewrite <- Z.mul_assoc.
      apply Zmult_lt_compat_l; auto.
      apply Pos2Z.pos_is_pos.
    }
    repeat rewrite multP in H0.
    unfold Qlt in *.
    simpl in *.
    apply Z.mul_pos_cancel_r in H.
    2 :{  unfold Z.lt. auto. }
    repeat rewrite <- Z.mul_assoc in H0.
    rewrite Z.mul_comm in H0.
    rewrite Z.mul_comm with (num r) (num r2 * Z.pos (shift_pos (den r) 1 * shift_pos (den r1) 1))%Z in H0.
    apply Zmult_gt_0_lt_reg_r in H0.
    2: { apply Z.lt_gt. auto. }
    rewrite Z.mul_comm in H0.
    rewrite Z.mul_comm with (num r2) ( Z.pos (shift_pos (den r) 1 * shift_pos (den r1) 1 )) in H0.
    repeat rewrite Pos2Z.inj_mul in H0.
    repeat rewrite <- Z.mul_assoc in H0.
    rewrite Z.mul_comm in H0.
    rewrite Z.mul_comm with (Z.pos (shift_pos (den r) 1)) ((Z.pos (shift_pos (den r1) 1) * num r2))%Z in H0.
    apply Zmult_gt_0_lt_reg_r in H0.
    { rewrite Z.mul_comm. rewrite -> Z.mul_comm with (num r2) (Z.pos (shift_pos (den r1) 1)). auto. }
    apply Zgt_pos_0.
  Qed.


  Lemma of_natO: of_nat O = t0.
  Proof. auto. Qed.

  Lemma of_natP: forall n : nat,  DO_to_Q (of_nat n) = (Qmake (2 * (Z.of_nat n)) 2).
  Proof. auto. Qed.

  Lemma of_nat_succ_l: forall n : nat, of_nat (S n) = add t1 (of_nat (n)). 
  Proof.
    intros.
    apply DOred_eq.
    rewrite addP.
    rewrite DO_to_Q1.
    repeat (rewrite of_natP).
    simpl.
    unfold Qeq.
    unfold Z.of_nat.
    simpl.
    destruct n.
    { rewrite Z.mul_0_l. auto. }
    simpl.
    rewrite Pos.mul_1_r.
    rewrite Pos2Z.pos_xO.
    rewrite Pos2Z.pos_xO with ((match Pos.of_succ_nat n with
       | q~1 => (Pos.succ q)~0
       | q~0 => q~1
       | 1 => 2
       end * 2))%positive.
    simpl.
    destruct (Pos.of_succ_nat n); auto.
  Qed.


  (**Trivial, but needed for numerics**)
  Lemma natPowO: forall (d : t), natPow d O = t1.
  Proof. auto. Qed.

  Lemma natPowRec: forall (d : t) (n : nat), natPow d (S n) = mult d (natPow d n).
  Proof. auto. Qed.


  (* Lemma lt_Qeq: forall d1 d2 d3 d4 : DO, DO_to_Q d1 == DO_to_Q d3 -> DO_to_Q d2 == DO_to_Q d4 -> (d1 < d2 <-> d3 < d4).
  Proof.
    intros.
    split; intros.
      unfold DOlt. rewrite <-  H. lia.
      rewrite H.
 *)
  

  Lemma num_ge0_iff: forall d, (0 <= DO_to_Q d)%Q <-> (0 <= num d)%Z.
  Proof.
    intros.
    split; intros;
      unfold Qle in *; simpl in *; lia.
  Qed.

  Lemma le_lt_dec: forall d1 d2,  {d1 <= d2} + {d2 < d1}.
  Proof.
    intros.
    destruct (DO_lt_le_dec d2 d1); auto.
  Qed.

  Lemma num_0_iff: forall d, num d = 0%Z <-> DO_to_Q d == 0.
  Proof.
    intros.
    split; intros;
      unfold Qeq in *; simpl in *; lia.
  Qed.

  Lemma eq_dec: forall d1 d2 : t, {d1 = d2} + {d1 <> d2}.
  Proof.
    intros.
    destruct (Z.eq_dec (num (d d1 - d d2)) 0).
    {
      left.
      rewrite num_0_iff in e.
      apply DOred_eq.
      rewrite DOsub_ok in e.
      unfold Qeq in *. simpl in *.
      lia.
    }
    right.
    unfold not in *. intros.
    apply n.
    subst.
    rewrite num_0_iff.
    setoid_replace 0%Q with (DO_to_Q DO0) using relation Qeq.
    2:{ unfold DO_to_Q. unfold Qeq. auto. }
    rewrite DOsub_ok.
    unfold Qminus. rewrite Qplus_opp_r.
    unfold Qeq. simpl. auto.
  Qed. 

  Lemma le_not_lt: forall d1 d2 : t, (d1 <= d2)-> ~ (d2 < d1).
  Proof.
    intros.
    unfold DOle in H.
    unfold DOlt.
    apply Qle_not_lt.
    auto.
  Qed.

  Lemma lt_asym: forall d1 d2 : t, d1 < d2 -> ~ d2 < d1.
  Proof.
    intros.
    unfold DOlt in *.
    apply Qle_not_lt.
    apply Qlt_le_weak.
    auto.
  Qed.

  Lemma lt_trans: forall d1 d2 d3 : t, d1 < d2 -> d2 < d3 -> d1 < d3.
  Proof.
    unfold DOlt.
    intros.
    apply Qlt_trans with (DO_to_Q d2); auto.
  Qed.
    

  Lemma total_order_T : forall d1 d2 : t, {DOlt d1 d2} + {d1 = d2} + {DOlt d2 d1}.
  Proof.
    intros.
    destruct (DO_lt_le_dec d1 d2); auto.
    destruct (eq_dec d1 d2); auto.
    right.
    unfold DOlt.
    unfold DOle in *.
    apply Qle_lt_or_eq in d0.
    destruct d0; auto.
    exfalso. apply n.
    symmetry.
    apply DOred_eq. auto.
  Qed. 

  Lemma lt_le_dec: forall d1 d2, {d1 < d2} + {d2 <= d1}.
  Proof. apply DO_lt_le_dec. Qed.

  Definition eq_bool (d1 d2 : t) : bool := Z.eqb (num (d d1)) (num (d d2)) && Pos.eqb (den (d d1)) (den (d d2)).

  Lemma eq_bool_refl: forall (d : t), eq_bool d d = true.
  Proof.
    intros d.
    unfold eq_bool.
    destruct d.  
    simpl.
    rewrite Z.eqb_refl.
    rewrite Pos.eqb_refl.
    auto.
  Qed.

  Lemma eq_bool_iff: forall (d1 d2 : t), eq_bool d1 d2 = true <-> d1 = d2.
  Proof.
    intros.
    split; intros.
    2: subst; apply eq_bool_refl.
    unfold eq_bool in H.
    apply DOred_eq_weak.
    destruct d1. destruct d2.
    destruct d1. destruct d0.
    simpl in *.
    apply andb_prop in H.
    destruct H.
    apply Ndec.Peqb_complete in H0.
    apply Z.eqb_eq in H. subst. auto.
  Qed.

  (* TODO: More lemmas here! *)
End DORed.      

Coercion DORed.d : DORed.t >-> DO.

Delimit Scope DORed_scope with DORed.
Bind Scope DORed_scope with DORed.t.

(* notations repeated from DO_scope *)
Infix "<" := DOlt : DORed_scope.
Infix "<=" := DOle : DORed_scope.
Notation "x > y" := (DOlt y x)(only parsing) : DORed_scope.
Notation "x >= y" := (DOle y x)(only parsing) : DORed_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : DORed_scope.
(* END *)

Infix "+" := DORed.add : DORed_scope.
Notation "- x" := (DORed.opp x) : DORed_scope.
Infix "-" := DORed.sub : DORed_scope.
Infix "*" := DORed.mult : DORed_scope.

Notation "'0'" := DORed.t0 : DORed_scope.
Notation "'1'" := DORed.t1 : DORed_scope.

(* A generalization of Dyadic rationals that allows conversion to Q *)
Inductive D : Set :=
| DD : DO -> D
| DQ : Q -> D.

(* Coercion DD : DO >-> D. *)

Definition D_to_Q (d : D) :=
  match d with
  | DD d => 
    DO_to_Q d
  | DQ q => q
  end.

Definition D0 : D := (DD (Dmake 0 1)).
Definition D1 : D := (DD (Dmake 2 1)).

Lemma D_to_Q0' : D_to_Q D0 = 0 # 2.
Proof. auto. Qed.

Lemma D_to_Q0 : D_to_Q D0 == 0.
Proof. rewrite D_to_Q0'; unfold Qeq; simpl; auto. Qed.

Lemma D_to_Q1' : D_to_Q D1 = 2 # 2.
Proof. auto. Qed.

Lemma D_to_Q1 : D_to_Q D1 == 1.
Proof. rewrite D_to_Q1'; unfold Qeq; simpl; auto. Qed.

Definition Dadd (d1 d2 : D) : D :=
  match d1,d2 with
  | DD d1, DD d2 => 
    DD (DOadd d1 d2)
  | _, _ => DQ (D_to_Q d1 + D_to_Q d2)
  end.

Lemma Dadd_ok d1 d2 :
  D_to_Q (Dadd d1 d2) == D_to_Q d1 + D_to_Q d2.
Proof.
  destruct d1, d2.
  {
    simpl.
    apply DOadd_ok.
  }
  all: (unfold Dadd;
        unfold D_to_Q at 1;
           reflexivity).
Qed.

Definition Dmult (d1 d2 : D) : D :=
  match d1,d2 with
  | DD d1, DD d2 => 
    DD (DOmult d1 d2)
  | _, _ => DQ (D_to_Q d1 * D_to_Q d2)
  end.

Close Scope DO_scope.
Lemma Dmult_ok d1 d2 :
  D_to_Q (Dmult d1 d2) = D_to_Q d1 * D_to_Q d2.
Proof.
  destruct d1, d2.
  {
    apply DOmult_ok.
  }
  all: unfold Dmult; unfold D_to_Q at 1; reflexivity.
Qed.

Definition Dopp (d : D) : D :=
  match d with
  | DD d => 
    DD (DOopp d)
  | _ => DQ (Qopp (D_to_Q d))
  end.

Hint Immediate DOopp_ok.

Lemma Dopp_ok d : D_to_Q (Dopp d) = Qopp (D_to_Q d).
Proof.
  destruct d; simpl; auto.
Qed.

Definition Dsub (d1 d2 : D) : D := Dadd d1 (Dopp d2).

Lemma Dsub_ok d1 d2 :
  D_to_Q (Dsub d1 d2) == D_to_Q d1 - D_to_Q d2.
Proof.
  unfold Dsub.
  rewrite Dadd_ok.
  rewrite Dopp_ok.
  unfold Qminus; apply Qeq_refl.
Qed.
Definition Dle (d1 d2 : D) : Prop :=
  Qle (D_to_Q d1) (D_to_Q d2).  

Definition Dle_bool (d1 d2 : D) : bool :=
  match d1,d2 with
  | DD d1', DD d2' => DOle_bool d1' d2' 
  | _,_ => Qle_bool (D_to_Q d1) (D_to_Q d2)
  end.

Lemma Dle_bool_iff d1 d2 : (Dle_bool d1 d2 = true) <-> Dle d1 d2.
Proof.
  unfold Dle_bool, Dle.
  destruct d1.
  2: apply Qle_bool_iff.
  destruct d2.
   apply DOle_bool_iff.
  apply Qle_bool_iff.
Qed.

Definition Dlt (d1 d2 : D) : Prop :=
  Qlt (D_to_Q d1) (D_to_Q d2).  

Definition Dlt_bool (d1 d2 : D) : bool :=
match d1,d2 with
| DD d1', DD d2' => DOlt_bool d1' d2'
| _,_ =>
  match D_to_Q d1 ?= D_to_Q d2 with
  | Lt => true
  | _ => false
  end
end.

Lemma Dlt_bool_iff d1 d2 : (Dlt_bool d1 d2 = true) <-> Dlt d1 d2.
Proof.
  unfold Dlt_bool.
  destruct d1.
  destruct d2. apply DOlt_bool_iff.
  split.
  destruct (Qcompare_spec (D_to_Q (DD d)) (D_to_Q (DQ q)));
    try solve[inversion 1|auto].
  unfold Dlt; rewrite Qlt_alt; intros ->; auto.
  split.
  destruct (Qcompare_spec (D_to_Q (DQ q)) (D_to_Q d2));
    try solve[inversion 1|auto].
  unfold Dlt; rewrite Qlt_alt; intros ->; auto.  
Qed.  

Lemma Deq_dec (d1 d2 : D) : {d1=d2} + {d1<>d2}.
Proof.
  destruct d1, d2.
  {
    destruct (DOeq_dec d d0) as [H1 | H1]; [left; f_equal; auto
                                           | right; intros Hnot; inversion Hnot; eauto].
  }
  {
    right.
    inversion 1.
  }
  {
    right; inversion 1.
  }
  {
    destruct q,q0.
    destruct (Z.eq_dec Qnum Qnum0).
    { destruct (positive_eq_dec Qden Qden0).
      left; subst; f_equal.
      right; inversion 1; subst; apply n; auto. }
    right; inversion 1; subst; auto.
  }
Defined.

(*(* MICROBENCHMARK *)
Fixpoint f (n : nat) (d : D) : D :=
  match n with
  | O => d
  | S n' => Dadd d (f n' d)
  end.

Time Compute f 5000 (Dmake 3 2).
(*Finished transaction in 0.012 secs (0.012u,0.s) (successful)*)

Fixpoint g (n : nat) (q : Q) : Q :=
  match n with
  | O => q
  | S n' => Qplus q (g n' q)
  end.

Time Compute g 5000 (Qmake 3 2).
(*Finished transaction in 0.847 secs (0.848u,0.s) (successful)*)
(*Speedup on this microbenchmark: 70x*)*)

Delimit Scope D_scope with D.
Bind Scope D_scope with D.
Arguments Dmake _%Z _%positive.

Infix "<" := Dlt : D_scope.
Infix "<=" := Dle : D_scope.
Notation "x > y" := (Dlt y x)(only parsing) : D_scope.
Notation "x >= y" := (Dle y x)(only parsing) : D_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : D_scope.

Infix "+" := Dadd : D_scope.
Notation "- x" := (Dopp x) : D_scope.
Infix "-" := Dsub : D_scope.
Infix "*" := Dmult : D_scope.

Notation "'0'" := D0 : D_scope.
Notation "'1'" := D1 : D_scope.

(** Dmax *)

Definition Dmax (d1 d2 : D) : D :=
  if Dlt_bool d1 d2 then d2 else d1.

Definition Dlub (max : D) : D :=
  match max with
  | DD max => 
    DD (DOlub max)
  | DQ q => DQ (Qinv q)
  end.


Local Open Scope D_scope.

Lemma Dlub_mult_le1 d : d * Dlub d <= 1.
Proof.
  destruct d.
  {
    simpl.
    pose proof (DOlub_mult_le1 d).
    unfold Dle.
    unfold DOle in H.
    auto.
  }
  {
    simpl.
    destruct (Qeq_dec q 0).
    {
      unfold Dle.
      simpl.
      rewrite q0.
      unfold Qinv.
      field_simplify.
      unfold Qle.
      simpl.
      omega.
    }
    {
      unfold Dle.
      simpl.
      apply Qmult_inv_r in n.
      rewrite n.
      unfold Qle.
      simpl.
      omega.
    }
  }
Qed.

Lemma Dlub_nonneg (d : D) :
  0 <= d -> 0 <= Dlub d.
Proof.
  destruct d; simpl; intros H.
  {
    pose proof (DOlub_nonneg d).
    unfold Dle, DOle in *; auto.
  }
  {
    unfold Dle in *.
    simpl in *.
    assert ((0 # 2) == (0)).
    {
      clear.
      field.
    }
    rewrite H0.
    rewrite H0 in H.
    apply Qinv_le_0_compat; auto.
  }
Qed.

Lemma Dlub_ok (d : D) :
  0 <= d -> 
  Dle 0 (d * Dlub d) /\ Dle (d * Dlub d) 1.
Proof.
  intros H.
  split.
  { unfold Dle; rewrite Dmult_ok.
    rewrite D_to_Q0; apply Qmult_le_0_compat.
    { rewrite <-D_to_Q0; auto. }
    rewrite <-D_to_Q0; apply Dlub_nonneg; auto. }
  apply Dlub_mult_le1.
Qed.

Fixpoint Dred' (n : Z) (d : nat) : (Z * nat) :=
  match d with
  | O => (n,d)
  | S d' => if Zeven_dec n then Dred' (Z.div2 n) d'
            else (n,d)
  end.

Lemma Dred'P n d : Zodd (fst (Dred' n d)) \/ (snd (Dred' n d) = 0%nat).
Proof.
  revert n; induction d; auto.
  intros n; simpl; destruct (Zeven_dec n).
  { apply (IHd (Z.div2 n)). }
  left; simpl.
  destruct (Zodd_dec n); auto.
  destruct (Zeven_odd_dec n); auto.
  elimtype False; apply n0; auto.
Qed.  

Definition D_of_Dred' (p : Z*nat) : D :=
  let (x,y) := p in DD (Dmake x (Pos.of_nat (S y))).

Eval compute in (log_inf 10).


Fixpoint Is_Pos_Power2 (p : positive) : option positive :=
  match p with
  | xH => None 
  | xO xH => Some xH
  | xO p' => match Is_Pos_Power2 p' with
             | None => None
             | Some pow2 => Some (Pos.succ pow2)
             end
  | xI p' => None
  end.

Definition Try_Q_to_D (q : Q) : option DO :=
  match Is_Pos_Power2 (Qden q) with
  | None =>
    if
      ((Qden q) =? xH)%positive 
    then
      Some (Dmake (2 * (Qnum q))%Z 1)
    else
      None
  | Some pow2 =>
    Some (Dmake (Qnum q) pow2)
  end.

Definition Dred (d : D) : D :=
  match d with
  | DD d => 
    DD (DOred d)
  | DQ q =>
    let qr := Qred q in
    match Try_Q_to_D qr with
    | None => DQ qr
    | Some d => DD d
    end
  end.

Definition Dnum (d : D) : Z :=
  match d with
  | DD d => num d
  | DQ q => Qnum q
  end.

Definition Dden (d : D) : positive :=
  match d with
  | DD d => den d
  | DQ q => Qden q
  end.

Lemma DredP d : Zodd (Dnum (Dred d)) \/ (Dden (Dred d) = 1%positive) \/ (exists q, d = DQ q).
Proof.
  destruct d.
  {
    destruct (DOredP d); auto.
  }
  {
    right.
    right.
    eauto.
  }
Qed.

Lemma D_of_Dred'_correct x y :
  D_to_Q (D_of_Dred' (Dred' x y)) == D_to_Q (D_of_Dred' (x,y)).
Proof.
  revert x; induction y.
  { intros x; apply Qeq_refl. }
  intros x.
  unfold Dred'; fold Dred'.
  destruct (Zeven_dec x) as [pf|pf].
  { rewrite IHy.
    unfold D_to_Q; simpl.
    unfold Qeq; simpl.
    pattern x at 2.
    rewrite (Zeven_div2 x pf).
    rewrite 2!shift_pos_correct, 2!Zmult_1_r.
    rewrite 2!Zpower_pos_nat.
    rewrite Pos2Nat.inj_succ.
    rewrite Zpower_nat_succ_r.
    rewrite Zmult_assoc.
    pattern (Z.div2 x * 2)%Z; rewrite Zmult_comm; auto. }
  apply Qeq_refl.
Qed.  

Lemma Shift_Pos_Not_xI : forall p acc, ~exists res, shift_pos p acc = xI res.
Proof.
  induction p; intros. 
  +
    intros Hnot; eauto.
    destruct Hnot.
    eapply IHp; eauto.
    eexists; eauto.
    unfold shift_pos in H.
    simpl in H.
    inversion H.
  +
    eapply IHp.
  +
    intros Hnot.
    destruct Hnot.
    unfold shift_pos in H.
    simpl in H.
    inversion H.
    Unshelve.
    eauto.
    exact xH.
Qed.


Lemma Is_Pos_Pow_Shift_inv': forall n, Is_Pos_Power2 (shift_nat (S n) 1) = Some (Pos.of_nat (S n)).
Proof.
  induction n.
  simpl.
  auto.
  {
    simpl in *.
    rewrite IHn.
    auto.
  }
Qed.
  
Lemma Is_Pow_Pow_Shift_inv : forall p, Is_Pos_Power2 (shift_pos p 1) = Some p.
Proof.
  intros.
  rewrite shift_pos_nat.
  destruct (Pos2Nat.is_succ p).
  rewrite H.
  rewrite Is_Pos_Pow_Shift_inv'.
  f_equal.
  rewrite <- H.
  apply Pos2Nat.id.
Qed.

Lemma Is_Pow_eq_spec : forall p1 p2, 
    Is_Pos_Power2 p1~0 = Is_Pos_Power2 p2~0 ->

    Is_Pos_Power2 p1 = Is_Pos_Power2 p2.
Proof.
  intros.
  simpl in *.
  destruct p1, p2; auto.
  destruct (Is_Pos_Power2 p1~1) eqn:H1; auto; try inversion H1.
  {
    destruct (Is_Pos_Power2 p2~0); auto.
    inversion H.
  }
  {
    destruct (Is_Pos_Power2 p1~0) eqn:H1; auto.
    destruct (Is_Pos_Power2 p2~1) eqn:H2; [inversion H2 | inversion H].
  }
  {
    destruct (Is_Pos_Power2 p1~0) eqn:H1; auto.
    {
      destruct (Is_Pos_Power2 p2~0); [ inversion H; f_equal; lia | inversion H].
    }
    destruct (Is_Pos_Power2 p2~0); [inversion H | auto].
  }
  {
    destruct (Is_Pos_Power2 p1~0) eqn:H1; auto.
    inversion H.
    exfalso.
    lia.
  }
  {
    destruct (Is_Pos_Power2 p2~0) eqn:H1; auto.
    inversion H.
    exfalso.
    lia.
  }
Qed.

Lemma Is_Pow_None_spec : forall p1,
    Is_Pos_Power2 p1 = None ->
    Is_Pos_Power2 p1~0 = None \/ p1 = xH.
Proof.
  intros.
  induction p1; auto.
  {
    simpl in *.
    destruct p1.
    {
      simpl in *; auto.
    }
    {
      destruct (Is_Pos_Power2 p1~0) eqn:H1; auto.
      inversion H.
    }
    {
      inversion H.
    }
  }
Qed.


Lemma Is_Pow_eq : forall p1 p2,
    Is_Pos_Power2 p1 = Is_Pos_Power2 p2 ->
    p1 = p2 \/ Is_Pos_Power2 p1 = None.
Proof.
  induction p1,p2; auto.
  intros.
  pose proof H.
  apply Is_Pow_eq_spec in H.
  apply IHp1 in H.
  destruct H; auto.
  {
    lia.
  }
  {
    apply Is_Pow_None_spec in H.
    destruct H; subst; auto.
    simpl in *.
    destruct p2; auto.
    destruct (Is_Pos_Power2 p2~0) eqn:H1; auto.
    {
      exfalso.
      inversion H0.
      lia.
    }
  }
Qed.

Lemma Try_Q_to_D_num : forall q d, Try_Q_to_D (Qred q) = Some d ->
       num d = Qnum (Qred q) \/ (num d = (2 * (Qnum (Qred q)))%Z) /\ den d = 1%positive.                    
Proof.
  intros q d H1.
  unfold Try_Q_to_D in H1.
  destruct (Is_Pos_Power2 (Qden (Qred q))).
  {
    inversion H1.
    auto.
  }
  {
    destruct ((Qden (Qred q) =? 1)%positive); auto.
    {
      right.
      split.
      +
        inversion H1.
        simpl in *.
        destruct (Qnum (Qred q)); auto.
      +
        inversion H1; subst; auto.
    }
    {
      inversion H1.
    }
  }
Qed.

Hint Immediate Qred_correct.
Lemma Dred_correct d : D_to_Q (Dred d) == D_to_Q d.
Proof.
  destruct d.
  {
    simpl.
    apply DOred_correct.
  }
  {
    simpl.
    assert (Qred q == q).
    {
      apply Qred_correct.
    }
    destruct (Try_Q_to_D (Qred q)) eqn:H1; auto.
    {
      simpl.
      rewrite <-H.
      unfold DO_to_Q.
      assert (H0 : num d = Qnum (Qred q) \/ (num d = (2 * (Qnum (Qred q)))%Z) /\ den d = 1%positive)
      by (apply Try_Q_to_D_num; auto).
      {
        unfold Try_Q_to_D in H1.
        destruct (Is_Pos_Power2 (Qden (Qred q))) eqn:H2; auto.
        {
          assert (Is_Pos_Power2 (shift_pos (den d) 1) = Some (den d)) by
              (apply Is_Pow_Pow_Shift_inv).
          assert (shift_pos p 1 = (Qden (Qred q))).
          {
            inversion H1.
            subst.
            simpl in *.
            pose proof H3. 
            rewrite <- H2 in H3.
            apply Is_Pow_eq in H3.
            destruct H3; auto.
            rewrite H4 in H3; inversion H3.
          }
          destruct H0.
          {
            inversion H1.
            subst.
            simpl in *.
            unfold Qeq.
            simpl.
            rewrite H4.
            auto.
          }
          {
            destruct H0.
            inversion H1; subst.
            simpl in *.
            unfold Qeq; subst.
            simpl.
            rewrite <- H4.
            simpl.
            auto.
          }
        }
        {
          destruct ((Qden (Qred q) =? 1)%positive) eqn:H3.
          {
            apply Pos.eqb_eq in H3.
            destruct H0; simpl in *;
            subst.
            {
              inversion H1; simpl in *; subst.
              clear H1.
              inversion H0.
              destruct Qnum eqn:H5; try lia.
              {

                simpl in *.
                unfold Qeq.
                rewrite H5.
                auto.
              }
            }
            {
              destruct H0.
              destruct (Qnum (Qred q)) eqn:H5; subst.
              {
                unfold Qeq.
                simpl in *.
                rewrite H0.
                rewrite H5.
                lia.
              }
              {
                unfold Qeq.
                simpl.
                rewrite H0.
                rewrite H5.
                simpl.
                rewrite H4.
                simpl in *.
                rewrite H3.
                lia.
              }
              {
                unfold Qeq.
                simpl.
                rewrite H0.
                rewrite H5.
                simpl.
                rewrite H4.
                simpl in *.
                rewrite H3.
                lia.
              }
            }
          }
          {
            inversion H1.
          }
        }
      }
    }
  }
Qed.

Instance : Proper (Qeq ==> eq) Qred.
Proof.
  unfold Proper.
  unfold respectful.
  intros.
  apply Qred_complete; auto.
Qed.

Open Scope nat_scope.
Theorem strong_induction : forall P : nat -> Prop,
  (forall m : nat, (forall n : nat, n < m -> P n) -> P m) ->
  forall n : nat, P n.
Proof.
  induction n using (well_founded_ind (well_founded_ltof nat id)); auto.
Qed.

Lemma Is_Pow2_eq1' : 
  forall p : positive, Is_Pos_Power2 (Pos.succ p) = Some (Pos.of_nat 1) -> 1%positive = p.
Proof.
    destruct p; intros; auto.
    {
      inversion H.
      simpl in H.
      destruct (Pos.eq_dec p 1); subst; auto.
      {
        simpl in *.
        inversion H.
      }
      {
        assert ((match Pos.succ p with
                 | 1%positive => Some 1%positive
                 | _ => match Is_Pos_Power2 (Pos.succ p) with
                        | Some pow2 => Some (Pos.succ pow2)
                        | None => None
                        end
                 end = Some 1%positive) =
                (match Is_Pos_Power2 (Pos.succ p) with
                 | Some pow2 => Some (Pos.succ pow2)
                 | None => None
                 end
                 = Some 1%positive)).
        {
          destruct p; auto.
        }
        rewrite H0 in H.
        clear H0.
        clear H1.
        destruct (Is_Pos_Power2 (Pos.succ p)) eqn:H1.
        simpl in *.
        inversion H.
        lia.
        inversion H.
      }
    }
    {
      simpl in *.
      inversion H.
    }
Qed.

Lemma Is_Pow2_eq1 : 
  forall p : positive, Is_Pos_Power2 p = Some (Pos.of_nat 1) -> 2%positive = p.
Proof.
 destruct p; intros; inversion H; auto.
 {
   simpl in H.
   destruct (Pos.eq_dec p 1); subst; auto.
   {
     assert ((match p with
       | 1%positive => Some 1%positive
       | _ => match Is_Pos_Power2 p with
              | Some pow2 => Some (Pos.succ pow2)
              | None => None
              end
             end = Some 1%positive) =
             (match Is_Pos_Power2 p with
              | Some pow2 => Some (Pos.succ pow2)
              | None => None
              end
             = Some 1%positive)).
     {
       destruct p; auto.
       lia.
     }
     rewrite H0 in H.
     clear H0.
     clear H1.
     destruct (Is_Pos_Power2 p) eqn:H1.
     simpl in *.
     inversion H.
     lia.
     inversion H.
   }
 }
Qed.

Lemma Pow2_xO : forall p q : positive,
    Is_Pos_Power2 q = Some p ->
    exists q', xO q' = q.
Proof.
  induction q; intros; 
  simpl in *;
  eauto.
  inversion H.
  inversion H.
Qed.

Lemma Pos_Div2_succ2 : forall p,
    (p <> 1)%positive -> 
    Pos.div2 (Pos.succ (Pos.succ p)) =
    Pos.succ (Pos.div2 p).
Proof.
  intros.
  induction p; auto.
  simpl.
  lia.
Qed.
  
Lemma Pos_of_nat_Div2_spec : forall n, Pos.of_nat (Nat.div2 n) =
                      Pos.div2 (Pos.of_nat n).
Proof.
  induction n using strong_induction; auto.
  destruct n; auto.
  destruct n; auto.
  specialize (H n).
  assert (Pos.of_nat (Nat.div2 n) = Pos.div2 (Pos.of_nat n)) by auto.
  clear H.
  simpl Nat.div2.
  destruct (Nat.eq_dec 0 n).
  subst; auto.
  destruct (Nat.eq_dec 1 n).
  subst; auto.
  rewrite Nat2Pos.inj_succ; try lia.
  2:{
    intros Hnot.
    rewrite Hnot in H0.
    simpl in H0.
    destruct n; try lia.
    destruct n; try lia.
    inversion Hnot.
  }
  {
    rewrite H0.
    pose proof (Pos_Div2_succ2 (Pos.of_nat n)).
    rewrite <- H; try lia.
    {
      rewrite Nat2Pos.inj_succ; try lia.
      rewrite Nat2Pos.inj_succ; lia.
    }
    {
      intros Hnot.
      destruct n; auto.
      rewrite Nat2Pos.inj_succ in Hnot; try lia.
    }
  }
Qed.

Lemma Pos_Pow2_xO_spec : forall x p,
    (x <> 1)%positive -> 
    Is_Pos_Power2 x~0 = Some (Pos.of_nat (S p)) ->
    Is_Pos_Power2 x = Some (Pos.of_nat (p)).
Proof.
  intros.
  simpl in H0.
  destruct x.
  {
    simpl in *.
    inversion H0.
  }
  {
    destruct (Is_Pos_Power2 (xO x)) eqn:Hi.
    {
      inversion H0.
      destruct p eqn:Hp in H2.
      subst; auto.
      lia.
      rewrite <- Hp in *.
      apply Pos.succ_inj in H2.
      rewrite <- H2.
      subst; auto.
    }
    inversion H0.
  }
  {
    simpl in *.
    destruct p; auto; try lia.
  }
Qed.      

Lemma Pow2_Div : forall p q : nat,
    (q > 2) -> 
    Is_Pos_Power2 (Pos.of_nat q) = Some (Pos.of_nat (S p)) -> 
    Is_Pos_Power2 (Pos.of_nat (q/2)) = Some (Pos.of_nat p).
Proof.
  intros.
  pose proof (Pow2_xO _ _ H0).
  destruct H1.
  rewrite <- Nat.div2_div.
  rewrite Pos_of_nat_Div2_spec.
  rewrite <- H1 in *.
  destruct (Pos.eq_dec x 1).
  {
    subst.
    clear -H H1.
    exfalso.
    assert (q = 2).
    {
      clear H.
      assert (xO xH = Pos.of_nat 2).
      auto.
      rewrite H in *.
      destruct q; auto.
      simpl in H1.
      lia.
      apply Nat2Pos.inj in H1; auto.
    }
    subst.
    lia.
  }
  {
    apply Pos_Pow2_xO_spec; auto.
  }
Qed.

Lemma shift_nat_spec : forall p q,
    q <> 0 -> 
    shift_nat p 1 = Pos.of_nat q  -> 
    shift_nat (S p) 1 = Pos.of_nat (2 * q).
Proof.
  intros.
  generalize dependent q.
  induction p; auto; intros.
  simpl in *.
  assert (q = 1).
  {
    assert (xH = Pos.of_nat 1).
    auto.
    rewrite H1 in *.
    apply Nat2Pos.inj in H0; lia.
  }
  {
    clear H0.
    subst; auto.
  }
  {
    rewrite Nat2Pos.inj_mul; try lia.
    rewrite <- H0.
    simpl.
    auto.
  }
Qed.

Lemma Pow2_Div2_Not_0 : forall p q,
    Is_Pos_Power2 q = Some p ->
    (Pos.to_nat q) / 2 <> 0.
Proof.
  intros.
  generalize dependent p.
  induction q; auto.
  {
    intros.
    simpl in H.
    inversion H.
  }
  {
    intros.
    intros Hnot.
    assert (q = 2 \/ q = 1)%positive.
    {
      assert ((Pos.to_nat q~0) = 0 \/ Pos.to_nat q~0 = 1).
      {
        generalize dependent (Pos.to_nat q~0).
        clear.
        induction n; auto.
        intros.
        rewrite <- Nat.div2_div in *.
        simpl in Hnot.
        destruct n.
        auto.
        lia.
      }
      destruct H0; lia.
    }
  {
    destruct H0; subst; auto; 
    simpl in Hnot; try lia.
  }
  }
  {
    intros.
    simpl in *.
    inversion H.
  }
Qed.

Lemma Pow2_Mult_Div_inv' : forall q p : positive ,
    Is_Pos_Power2 q = Some p ->
    (2 * (Pos.div2 q) = q)%positive.
Proof.
  intros.
  generalize dependent p.
  destruct q; auto.
  intros.
  {
    inversion H.
  }
  {  
    intros.
    simpl in H.
    inversion H.
  }
Qed.

Lemma Pow2_Mult_Div_inv : forall q p : nat ,
    Is_Pos_Power2 (Pos.of_nat q) = Some (Pos.of_nat p) ->
    (2 * (q / 2) = q).
Proof.
  intros.
  pose proof H.
  apply Pow2_Mult_Div_inv' in H.
  rewrite <- Pos_of_nat_Div2_spec in H.
  rewrite <- Nat.div2_div.
  destruct q; auto.
  {
    destruct q; auto. 
    {
      simpl in *.
      inversion H0.
    }
    {
      assert (S (S q) = Pos.to_nat (Pos.of_nat (S (S q)))).
      {
        rewrite Nat2Pos.id; try lia.
      }
      rewrite H1 at 2.      
      rewrite <- H.
      rewrite Pos2Nat.inj_mul.
      rewrite Nat2Pos.id; try lia.
      intros Hnot.
      simpl in Hnot.
      inversion Hnot.
    }
  }
Qed.

Lemma Shift_Is_Pos_Pow2_inv_nat' : forall p q,
    p <> 0 -> 
    q <> 0 -> 
    Is_Pos_Power2 (Pos.of_nat q) = Some (Pos.of_nat p) ->
    shift_nat p 1 = (Pos.of_nat q).
Proof.
  induction p; auto.
  {
    intros.
    lia.
  }
  {
    intros.
    rename H into Hp.
    rename H0 into Hq.
    rename H1 into H.
    destruct (Nat.eq_dec p 0).
    {
      subst.
      simpl in H.
      assert (Pos.of_nat q = 2%positive); auto.
      {
        simpl in H.
        apply Is_Pow2_eq1 in H.
        lia.
      }
    }
    {
      assert (q / 2 <> 0).
      {
        pose proof (Pow2_Div2_Not_0 (Pos.of_nat (S p)) (Pos.of_nat q)).
        apply H0 in H.
        clear -H Hq.
        destruct q; auto.
        rewrite Nat2Pos.id in H; lia.
      }
      destruct (Nat.eq_dec 2 q).
      {
        subst.
        simpl in H.
        inversion H.
        destruct p; auto.
        lia.
      }
      assert (q > 2).
      {
        destruct q; auto.
        lia.
        destruct q; auto.
        simpl in *.
        inversion H.
        lia.
      }
      specialize (IHp ((q /2)) n H0 (Pow2_Div _ _ H1 H)).
      specialize (shift_nat_spec p (q/2) H0).
      intros spec.
      apply spec in IHp.
      rewrite Pow2_Mult_Div_inv with (p := S p) in IHp; auto.
    }
  }
Qed.

Open Scope positive_scope.

Lemma Shift_Is_Pos_Pow2_inv' : forall p q : positive,
    Is_Pos_Power2 q = Some p ->
    shift_pos p 1 = q.
Proof.
  intros.
  pose proof Shift_Is_Pos_Pow2_inv_nat'.
  rewrite shift_pos_nat.
  specialize (H0 (Pos.to_nat p) (Pos.to_nat q)).
  rewrite Pos2Nat.id in H0.
  apply H0; try lia.
  rewrite Pos2Nat.id.
  auto.
Qed.

Lemma Shift_Is_Pos_Pow2_inv : forall p q, 
    Is_Pos_Power2 ((Qden (Qred q))) = Some p ->
    shift_pos p 1 = (Qden (Qred q)).
Proof.
  intros.
  pose proof Shift_Is_Pos_Pow2_inv'.
  apply H0.
  auto.
Qed.

Lemma Try_Q_to_D_Qred_spec : forall q d,
    Try_Q_to_D (Qred q) = Some d ->
    q == D_to_Q (DD d).
Proof.
  intros.
  pose proof H as h.
  unfold Try_Q_to_D in H.
  destruct (Is_Pos_Power2 (Qden (Qred q))) eqn:h1.
  {
    simpl.
    unfold DO_to_Q.
    inversion H.
    clear H.
    simpl.
    rewrite <- Qred_correct with (q := q) at 1.
    unfold Qeq.
    simpl.
    f_equal.
    apply Shift_Is_Pos_Pow2_inv in h1.
    rewrite h1.
    auto.
  }
  {
    rewrite <- Qred_correct.
    destruct (Qden (Qred q) =? 1) eqn:Hd.
    {
      apply Peqb_true_eq in Hd.
      inversion H.
      subst.
      clear H.
      unfold Qeq.
      simpl.
      destruct (Qnum (Qred q)) eqn:Hq; auto.
      rewrite <- Hq.
      simpl.
      destruct (Qred q).
      {
        simpl in *.
        subst.
        unfold Try_Q_to_D in h.
        simpl in h.
        lia.
      }
      {
        simpl.
        assert ((p * Qden (Qred q))~0 = (p * Qden (Qred q)) * 2) by lia.
        rewrite H.
        rewrite <- Pos.mul_assoc.
        f_equal.
        rewrite Hd.
        lia.
      }
    }
    {
      inversion H.
    }
  }
Qed.

Lemma Try_Q_to_D_Qred_spec1 : forall q d,
    Try_Q_to_D (Qred q) = Some d ->
    DOred d = d.
Proof.
  intros.
  unfold Try_Q_to_D in H.
  destruct (Is_Pos_Power2 (Qden (Qred q))) eqn:Hm.
  {
    inversion H.
    unfold DOred.
    simpl.
    unfold DO_of_DOred'.
    destruct (DOred' _ _) eqn:Hd.
    subst.
    destruct ((Init.Nat.pred (Pos.to_nat p))) eqn:Hp.
    {
      simpl in Hd.
      inversion Hd; subst; auto.
      assert (p = 1) by lia.
      subst.
      auto.
    }
    {
      (*  Relate n0 to n  *)
      destruct (DOred' _ _).
      inversion Hd; subst.
  Admitted.


Lemma QeqD_is_pow2 : forall q d,
    q == DO_to_Q d -> 
    Try_Q_to_D (Qred q) = None -> False.
Proof.
  intros q d H H1.
    simpl in *.
    pose proof H1 as Ht.
    unfold Try_Q_to_D in H1.
    destruct (Is_Pos_Power2 (Qden (Qred q))) eqn:Hm.
    {
      inversion H1.
    }
    {
      destruct (Qden (Qred q) =? 1) eqn:Hm1.
      {
        inversion H1.
      }
      {
        rewrite H in Hm.
        apply Positive_as_OT.eqb_neq in Hm1.
        rewrite  H in Hm1.
        clear -Hm Ht Hm1 H.
        simpl in Hm.
        destruct d; subst.
        simpl in *.
        destruct (snd (Z.ggcd num0 (Z.pos (shift_pos den0 1)))) eqn:H1.
        simpl in Hm.
        unfold Z.ggcd in H1.
        destruct (num0) eqn:H2.
        {
          simpl in H1.
          inversion H1; 
            subst.
          simpl in *.
          lia.
        }
        {
          subst.
          simpl in *.
          pose proof Pos.ggcd_correct_divisors as H0.
          specialize (H0 p (shift_pos den0 1)).
          destruct (Pos.ggcd p (shift_pos den0 1)) eqn:H1'.
          destruct p1; subst; auto.
          intuition.
          simpl in *.
          pose proof (Is_Pow_Pow_Shift_inv den0) as H0.
          inversion H1; subst.
          simpl in *.
        admit.
        }
        {
          subst.
          admit.
        }
    }
Admitted.

Lemma Dred_complete d1 d2 :
  D_to_Q d1 == D_to_Q d2 ->
  Dred d1 = Dred d2.
Proof.
  destruct d1, d2; try (rename d into d1; rename d0 into d2).
  {
    simpl.
    intros.
    f_equal.
    apply DOred_complete; auto.
  }
  intros.
  simpl.
  {
    destruct (Try_Q_to_D (Qred q)) eqn:H1.
    {
      pose proof DOred_complete.
      pose proof H1.
      rewrite <- H in H1.
      apply Try_Q_to_D_Qred_spec in H1.
      rewrite <- Qred_correct in H1.
      rewrite <- Qred_correct with (q := (D_to_Q (DD d0))) in H1.
      specialize (H0 d d0).
      (* apply DOred_complete in H. *)
      rewrite Qred_correct in H1.
      rewrite Qred_correct in H1.
      pose proof H1.
      rewrite H in H1.
      apply H0 in H3.
      simpl in *.
    (* d0 is in lowest terms already so DOred of d0 should be d0 *)
      apply Try_Q_to_D_Qred_spec1 in H2.
      rewrite H3.
      f_equal.
      auto.
    }
    {
      exfalso.
      simpl in *.
      symmetry in H.
      apply QeqD_is_pow2 in H; auto.
    }
  }
  {
    intros.
    simpl.
    destruct (Try_Q_to_D (Qred q)) eqn:H1.
    {
      pose proof DOred_complete.
      pose proof H1.
      rewrite H in H1.
      apply Try_Q_to_D_Qred_spec in H1.
      rewrite <- Qred_correct in H1.
      rewrite <- Qred_correct with (q := (D_to_Q (DD d0))) in H1.
      specialize (H0 d d0).
      (* apply DOred_complete in H. *)
      rewrite Qred_correct in H1.
      rewrite Qred_correct in H1.
      pose proof H1.
      rewrite <- H in H1.
      apply H0 in H3.
      simpl in *.
    (* d0 is in lowest terms already so DOred of d0 should be d0 *)
      apply Try_Q_to_D_Qred_spec1 in H2.
      rewrite H3.
      f_equal.
      auto.
    }
    {
      simpl in *.
      exfalso.
      apply QeqD_is_pow2 in H; auto.
    }
  }
  {
    intros.
    simpl in *.
    rewrite H.
    destruct (Try_Q_to_D (Qred q0)) eqn:H1; auto.
    rewrite H.
    auto.
  }
Qed.

Lemma Dred'_idem x y :
  Dred' (fst (Dred' x y)) (snd (Dred' x y)) = Dred' x y.
Proof.
  destruct (Dred'P x y).
  { revert H.
    generalize (Dred' x y).
    destruct p.
    simpl; intros H.
    unfold Dred'.
    destruct n; auto.
    destruct (Zeven_dec z); auto.
    apply Zodd_not_Zeven in H; contradiction. }
  destruct (Dred' x y); simpl in H|-*; rewrite H; auto.
Qed.  
    
Lemma Dred_idem d : Dred (Dred d) = Dred d.
Proof.
  destruct d.
  {
    simpl.
    f_equal.
    apply DOred_idem.
  }
  {
    unfold Dred.
    unfold DOred.
    destruct (Try_Q_to_D (Qred q)) eqn:Hm; auto.
    {
      apply Try_Q_to_D_Qred_spec1 in Hm.
      rewrite <- Hm.
      unfold DO_of_DOred'.
      destruct (DOred' _ _) eqn:H.
      rewrite Hm in H.
      rewrite <- Hm in H.    
      destruct ((Init.Nat.pred (Pos.to_nat (den (DOred d))))) eqn:H1;
        subst.
      {
        simpl in H.
        inversion H; subst; auto.
        simpl.
        assert (den (DOred d) = 1) by lia.
        rewrite Hm.
        rewrite Hm in H0.
        destruct d.
        simpl in *.
        rewrite H0.
        auto.
      }
      {      
        simpl in H.
        destruct Zeven_dec eqn:He.
        {
          destruct (DOredP d); subst; auto.
          {
            exfalso.
            apply (Zodd_not_Zeven _ H0); eauto.
          }
          {
            rewrite H0 in H1.
            simpl in H1.
            inversion H1.
          }
        }        
        {
          inversion H; subst; auto.
          rewrite Hm in *.
          rewrite <- H1.
          rewrite Nat.succ_pred; try lia.
          rewrite Pos2Nat.id.
          destruct d; auto.
        }
      }
    }
    {
      destruct (Try_Q_to_D (Qred (Qred q))) eqn:Hm1.
      {
        (* Qred of Qred is Qred *)
        admit.
      }
      {      
        (* Qred of Qred is Qred *)
        admit.
      }
    }
  }
Admitted.

Close Scope positive_scope.
Close Scope nat_scope.
Local Open Scope D_scope.
Module DRed.
  Record t : Type :=
    mk { d :> D;
         pf : Dred d = d }.

  Definition build (d : D) : t := @mk (Dred d) (Dred_idem d).
  
  Program Definition t0 := mk 0 _.

  Program Definition t1 := mk 1 _.
  
  Program Definition add (d1 d2 : t) : t :=
    mk (Dred (Dadd d1.(d) d2.(d))) _.
  Next Obligation.
    apply Dred_idem.
  Qed.


  Program Definition sub (d1 d2 : t) : t :=
    mk (Dred (Dsub d1.(d) d2.(d))) _.
  Next Obligation.
    apply Dred_idem.
  Qed.

  Program Definition mult (d1 d2 : t) : t := 
    mk (Dred (Dmult d1.(d) d2.(d))) _.
  Next Obligation.
    apply Dred_idem.
  Qed.

  Program Definition opp (dx : t) : t := 
    mk (Dred (Dopp dx.(d))) _.
  Next Obligation.
    apply Dred_idem.
  Qed.

  Program Definition lub (dx : t) : t := 
    mk (Dred (Dlub dx.(d))) _.
  Next Obligation.
    apply Dred_idem.
  Qed.

  Program Definition of_nat (n : nat) : t :=
    mk (DD (Dmake (2 * (Z.of_nat n)) 1)) _.

  Program Fixpoint natPow (d : t) (n : nat) : t :=
    match n with
    | O => t1
    | S n' => mult d (natPow d n')
    end.

  Lemma Dred_eq (d1 d2 : t) : (D_to_Q (d d1) == D_to_Q (d d2))%Q -> d1 = d2.
  Proof.
    destruct d1 as [x1 pf1]; destruct d2 as [x2 pf2]; simpl.
    intros H; assert (H2: x1 = x2).
    {
      
      rewrite <-pf1, <-pf2; apply Dred_complete; auto. }
    generalize pf1 pf2; rewrite H2; intros; f_equal; apply proof_irrelevance.
  Qed.

  Lemma addP d1 d2 :
    D_to_Q (d (add d1 d2)) == (D_to_Q (d d1) + D_to_Q (d d2))%Q.
  Proof.
    unfold add; simpl.
    rewrite Dred_correct.
    rewrite Dadd_ok; apply Qeq_refl.
  Qed.    
  
  Lemma addC d1 d2 : add d1 d2 = add d2 d1.
  Proof.
    apply Dred_eq; simpl; rewrite 2!Dred_correct, 2!Dadd_ok.
    apply Qplus_comm.
  Qed.

  Lemma addA d1 d2 d3 : add d1 (add d2 d3) = add (add d1 d2) d3.
  Proof.
    apply Dred_eq; simpl.
    rewrite !Dred_correct, !Dadd_ok, !Dred_correct, !Dadd_ok.
    apply Qplus_assoc.
  Qed.    

  Lemma add0l d : add t0 d = d.
  Proof.
    unfold t0; apply Dred_eq; unfold add.
    generalize (add_obligation_1 {|d:=0;pf:=t0_obligation_1|} d).
    unfold DRed.d; rewrite Dred_correct; intros e.
    rewrite Dadd_ok, D_to_Q0, Qplus_0_l; apply Qeq_refl.
  Qed.    
        
  Lemma subP d1 d2 :
    D_to_Q (d (sub d1 d2)) == (D_to_Q (d d1) - D_to_Q (d d2))%Q.
  Proof.
    unfold sub; simpl.
    rewrite Dred_correct.
    rewrite Dsub_ok; apply Qeq_refl.
  Qed.

  Lemma multP d1 d2 :
    D_to_Q (d (mult d1 d2)) == (D_to_Q (d d1) * D_to_Q (d d2))%Q.
  Proof.
    unfold mult; simpl.
    rewrite Dred_correct.
    rewrite Dmult_ok; apply Qeq_refl.
  Qed.    
  
  Lemma multC d1 d2 : mult d1 d2 = mult d2 d1.
  Proof.
    apply Dred_eq; simpl; rewrite 2!Dred_correct, 2!Dmult_ok.
    apply Qmult_comm.
  Qed.

  Lemma multA d1 d2 d3 : mult d1 (mult d2 d3) = mult (mult d1 d2) d3.
  Proof.
    apply Dred_eq; simpl.
    rewrite !Dred_correct, !Dmult_ok, !Dred_correct, !Dmult_ok.
    apply Qmult_assoc.
  Qed.    

  Lemma oppP dx :
    D_to_Q (d (opp dx)) == (- D_to_Q (d dx))%Q.
  Proof.
    unfold opp; simpl.
    rewrite Dred_correct.
    rewrite Dopp_ok; apply Qeq_refl.
  Qed.

  Lemma lubP (dx : t) :
    0 <= dx -> 0 <= dx * lub dx /\ dx * lub dx <= 1.
  Proof.
    intros H.
    generalize (Dlub_ok dx H); intros [H1 H2].
    unfold lub, Dle in *; simpl.
    rewrite Dmult_ok in *.
    rewrite Dred_correct in *; auto.
  Qed.

  Lemma addOppL: forall d1, add (opp d1) d1 = t0.
  Proof.
    intros.
    apply Dred_eq.
    rewrite addP.    
    simpl.
    rewrite D_to_Q0.
    rewrite Dred_correct.
    rewrite Dopp_ok.
    rewrite Qplus_comm.
    apply Qplus_opp_r.
  Qed.
    
  Lemma addNegDistr: forall d1 d2, opp (add d1 d2) = add (opp d1) (opp d2).
  Proof.
    intros.
    apply Dred_eq.
    rewrite addP.
    repeat (rewrite oppP).
    rewrite addP.
    apply Qopp_plus.
  Qed.


  Lemma mult1L: forall d1, mult t1 d1 = d1.
  Proof.
    intros.
    apply Dred_eq.
    rewrite multP.
    rewrite D_to_Q1.
    apply Qmult_1_l.
  Qed.

  Lemma multDistrL: forall d1 d2 d3, mult d1 (add d2 d3) = add (mult d1 d2) (mult d1 d3).
  Proof.
    intros.
    apply Dred_eq.
    rewrite multP.
    repeat (rewrite addP).
    repeat (rewrite multP).
    apply Qmult_plus_distr_r.
  Qed.

  Lemma mult0L: forall d1, mult t0 d1 = t0.
  Proof.
    intros.
    apply Dred_eq.
    rewrite multP.
    rewrite D_to_Q0.
    apply Qmult_0_l.
  Qed.


  Lemma le_lt_or_eq: forall (t1 t2 : t), Dlt t1 t2 \/ t1 = t2 <-> Dle t1 t2.
  Proof.
    intros.
    split.
    {
      unfold Dle,Dlt in *.
      intros.
      apply Qle_lteq.
      destruct H; auto.
      rewrite H.
      right.  
      apply Qeq_refl.
    }
    intros.
    unfold Dle in H.
    rewrite Qle_lteq in H.
    destruct H; auto.
    right.
    apply Dred_eq; auto.
  Qed.


  Lemma plus_le_compat: forall (t1 t2 t3 t4 : t) , Dle t1 t2 -> Dle t3  t4 -> Dle (add t1 t3) (add t2 t4).
  Proof.
    intros.
    unfold Dle in *.
    repeat (rewrite addP).
    apply Qplus_le_compat; auto.
  Qed.


  Lemma plus_lt_le_compat: forall (t1 t2 t3 t4 : t), Dlt t1 t2 ->  Dle t3 t4 -> Dlt (add t1 t3 ) (add t2 t4).
  Proof.
    intros.
    unfold Dle,Dlt in *.
    repeat (rewrite addP).
    apply Qplus_lt_le_compat; auto.
  Qed.
    
  Lemma plus_lt_compat_l : forall t t1 t2 : t, Dlt t1 t2 -> Dlt (add t t1) (add t t2).
  Proof.
    intros.
    rewrite addC.
    rewrite addC with t2 t4.
    apply plus_lt_le_compat; auto.
    unfold Dle.
    apply Qle_refl.
  Qed.


  
  
  Lemma lt_t0_t1: t0 < t1.
  Proof.
    unfold Dlt.
    rewrite D_to_Q0.
    rewrite D_to_Q1.
    unfold Qlt, Z.lt.
    auto. 
  Qed.

  Lemma mult_le_compat: 
        forall (r1 r2 r3 r4 : t) , Dle t0 r1 -> Dle t0 r3 -> Dle r1  r2 -> Dle r3 r4 ->
           Dle (mult r1 r3) (mult r2   r4).
  Proof.
    intros.
    unfold Dle in *.
    repeat (rewrite multP).
    remember (D_to_Q r1) as q1.
    remember (D_to_Q r2) as q2.
    remember (D_to_Q r3) as q3.
    remember (D_to_Q r4) as q4.
    rewrite D_to_Q0 in *.
    unfold Qle in *.
    simpl in *.
    rewrite Z.mul_1_r in *.
    repeat (rewrite Pos2Z.inj_mul).
    rewrite Z.mul_shuffle0.
    rewrite Z.mul_assoc.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_shuffle0 with (Qnum q2) (Qnum q4) (QDen q1 * QDen q3)%Z.
    rewrite Z.mul_assoc with (Qnum q2) (QDen q1) (QDen q3).
    rewrite <- Z.mul_assoc with (Qnum q2 * QDen q1)%Z (QDen q3) (Qnum q4).
    apply Zmult_le_compat; auto;
    try( apply Zmult_le_0_compat; auto ; apply Pos2Z.pos_is_nonneg).
    rewrite Z.mul_comm.
    rewrite Z.mul_comm with (QDen q3) (Qnum q4).
    auto.
  Qed.

   Lemma mult_lt_compat:
        forall (r1 r2 r3 r4 : t), Dle t0 r1 -> Dle t0 r3 -> Dlt r1 r2 -> Dlt r3 r4 ->
           Dlt (mult r1 r3) (mult r2 r4).
  Proof.
    intros.
    unfold Dle,Dlt in *.
    repeat (rewrite multP).
    remember (D_to_Q r1) as q1.
    remember (D_to_Q r2) as q2.
    remember (D_to_Q r3) as q3.
    remember (D_to_Q r4) as q4.
    rewrite D_to_Q0 in *.
    unfold Qlt in *.
    simpl.
    repeat (rewrite Pos2Z.inj_mul).
    rewrite Z.mul_shuffle0.
    rewrite Z.mul_assoc.
    rewrite <- Z.mul_assoc.
    rewrite Z.mul_shuffle0 with (Qnum q2) (Qnum q4) (QDen q1 * QDen q3)%Z.
    rewrite Z.mul_assoc with (Qnum q2) (QDen q1) (QDen q3).
    rewrite <- Z.mul_assoc with (Qnum q2 * QDen q1)%Z (QDen q3) (Qnum q4).
    apply Zmult_lt_compat.
    {
      split; auto.
      apply Zmult_le_0_compat.
      {
        unfold Qle in H.
        simpl in *. 
        rewrite Z.mul_1_r in H.
        auto.
      }
      apply Pos2Z.pos_is_nonneg.
    }
    split.
    {
      apply Zmult_le_0_compat.
      { apply Pos2Z.pos_is_nonneg. }
      unfold Qle in H0.
      simpl in *.
      rewrite Z.mul_1_r in H0.
      auto.
    }
    rewrite Z.mul_comm.
    rewrite Z.mul_comm with (QDen q3) (Qnum q4).
    auto.
  Qed.
    
  Lemma mult_lt_compat_l : forall r r1 r2 : t, Dlt t0 r -> (Dlt r1 r2 <-> Dlt (mult r r1) (mult r r2)).
  Proof.
    unfold Dlt.
    intros.
    split; intros.
    {
      repeat rewrite multP.
      unfold Qlt in *.
      simpl in *.
      apply Z.mul_pos_cancel_r in H.
      2 :{  unfold Z.lt. auto. } simpl.
      repeat rewrite <- Z.mul_assoc.
      apply Zmult_lt_compat_l; auto.
      repeat rewrite Pos2Z.inj_mul.
      repeat rewrite Z.mul_assoc.
      rewrite Z.mul_comm with (Qnum (D_to_Q r1)) (QDen (D_to_Q r)).
      rewrite Z.mul_comm with (Qnum (D_to_Q r2)) (QDen (D_to_Q r)).
      apply Zmult_lt_compat_l with (p := (QDen (D_to_Q r))) in H0; lia.
    }
    repeat rewrite multP in H0.
    unfold Qlt in *.
    simpl in *.
    apply Z.mul_pos_cancel_r in H.
    2 :{  unfold Z.lt. auto. }
    repeat rewrite <- Z.mul_assoc in H0.
    rewrite Z.mul_comm in H0.
    rewrite Z.mul_comm with (Qnum (D_to_Q r)) 
                            ((Qnum (D_to_Q r2) * Z.pos (Qden (D_to_Q r) * Qden (D_to_Q r1)))%Z) in
        H0.
    apply Zmult_gt_0_lt_reg_r in H0.
    2: { apply Z.lt_gt. auto. }
    rewrite Z.mul_comm in H0.
    rewrite Z.mul_comm with (Qnum (D_to_Q r2))
                            (Z.pos (Qden (D_to_Q r) * Qden (D_to_Q r1)))%Z
      in H0.
    repeat rewrite Pos2Z.inj_mul in H0.
    repeat rewrite <- Z.mul_assoc in H0.
    rewrite Z.mul_comm in H0.
    rewrite Z.mul_comm with 
        (QDen (D_to_Q r))
        (QDen (D_to_Q r1) * Qnum (D_to_Q r2))%Z in
        H0.
    apply Zmult_gt_0_lt_reg_r in H0; lia.
  Qed.

  Lemma of_natO: of_nat O = t0.
  Proof. auto. Qed.

  Lemma of_natP: forall n : nat,  D_to_Q (of_nat n) = (Qmake (2 * (Z.of_nat n)) 2).
  Proof. auto. Qed.

  Lemma of_nat_succ_l: forall n : nat, of_nat (S n) = add t1 (of_nat (n)). 
  Proof.
    intros.
    apply Dred_eq.
    rewrite addP.
    rewrite D_to_Q1.
    repeat (rewrite of_natP).
    simpl.
    unfold Qeq.
    unfold Z.of_nat.
    simpl.
    destruct n.
    { rewrite Z.mul_0_l. auto. }
    simpl.
    rewrite Pos.mul_1_r.
    rewrite Pos2Z.pos_xO.
    rewrite Pos2Z.pos_xO with ((match Pos.of_succ_nat n with
       | q~1 => (Pos.succ q)~0
       | q~0 => q~1
       | 1 => 2
       end * 2))%positive.
    simpl.
    destruct (Pos.of_succ_nat n); auto.
  Qed.


  (**Trivial, but needed for numerics**)
  Lemma natPowO: forall (d : t), natPow d O = t1.
  Proof. auto. Qed.

  Lemma natPowRec: forall (d : t) (n : nat), natPow d (S n) = mult d (natPow d n).
  Proof. auto. Qed.

  Lemma lt_le_dec: forall d1 d2, {d1 < d2} + {d2 <= d1}.
  Proof.
    destruct d1; destruct d2.
      exact (DORed.lt_le_dec d0 d1) .
      exact (Qlt_le_dec (DO_to_Q d0) q).
      exact (Qlt_le_dec q (DO_to_Q d0)).
      exact (Qlt_le_dec q q0).
  Defined.

  Lemma le_lt_dec: forall d1 d2,  {d1 <= d2} + {d2 < d1}.
  Proof. intros.
    destruct (lt_le_dec d2 d1); auto.
  Defined.

  Lemma eq_dec: forall d1 d2 : t, {d1 = d2} + {d1 <> d2}.
  Proof.
    intros.
    destruct Deq_dec with (d d1) (d d2).
    { 
      left. 
      destruct d1,d2.
      simpl in e.
      generalize pf0 pf1.
      rewrite e.
      intros.
      f_equal.
      apply proof_irrelevance.
    }
    right.
    destruct d1,d2.
    simpl in n.
    unfold not in *.
    intros.
    apply n.
    inversion H.
    auto.
  Qed.

  Lemma le_not_lt: forall d1 d2 : t, (d1 <= d2)-> ~ (d2 < d1).
  Proof.
    intros.
    unfold Dle in H.
    unfold Dlt.
    apply Qle_not_lt.
    auto.
  Qed.

  Lemma lt_asym: forall d1 d2 : t, d1 < d2 -> ~ d2 < d1.
  Proof.
    intros.
    unfold Dlt in *.
    apply Qle_not_lt.
    apply Qlt_le_weak.
    auto.
  Qed.

  Lemma lt_trans: forall d1 d2 d3 : t, d1 < d2 -> d2 < d3 -> d1 < d3.
  Proof.
    unfold Dlt.
    intros.
    apply Qlt_trans with (D_to_Q d2); auto.
  Qed.
    

  Lemma total_order_T : forall d1 d2 : t, {Dlt d1 d2} + {d1 = d2} + {Dlt d2 d1}.
  Proof.
    intros.
    unfold Dlt.
    destruct Q_dec with (D_to_Q d1) (D_to_Q d2).
      destruct s; auto.
    left.
    right.
    apply Dred_eq.
    auto.
  Qed.

  Definition eq_bool (d1 d2 : t) : bool := 
  match (d d1),(d d2) with
  | (DD d1'), (DD d2') => DORed.eq_bool (DORed.build d1') (DORed.build d2')
  | _ , _ => Qeq_bool (D_to_Q d1) (D_to_Q d2)
  end.

  Lemma eq_bool_refl: forall (d : t), eq_bool d d = true.
  Proof.
    intros d.
    unfold eq_bool.
    destruct d.  
    simpl.
    destruct d0.
      apply DORed.eq_bool_refl.
    apply Qeq_bool_refl.
  Qed.

  Lemma eq_bool_iff: forall (d1 d2 : t), eq_bool d1 d2 = true <-> d1 = d2.
  Proof.
    intros.
    split; intros.
    2: subst; apply eq_bool_refl.
    unfold eq_bool in H.
    destruct d1. destruct d0; simpl in *.
    2:{ apply Qeq_bool_iff in H. apply Dred_eq. auto. }
    destruct d2. destruct d1; simpl in *.
    2:{ apply Qeq_bool_iff in H. apply Dred_eq. auto. }
    apply DORed.eq_bool_iff in H.
    unfold DORed.build in H.
    inversion H.
    apply Dred_eq.
    simpl.
    apply DOred_complete_converse.
    auto.
  Qed.

  (* TODO: More lemmas here! *)
End DRed.      

Coercion DRed.d : DRed.t >-> D.

Delimit Scope DRed_scope with DRed.
Bind Scope DRed_scope with DRed.t.

(* notations repeated from D_scope *)
Infix "<" := Dlt : DRed_scope.
Infix "<=" := Dle : DRed_scope.
Notation "x > y" := (Dlt y x)(only parsing) : DRed_scope.
Notation "x >= y" := (Dle y x)(only parsing) : DRed_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : DRed_scope.
(* END *)

Infix "+" := DRed.add : DRed_scope.
Notation "- x" := (DRed.opp x) : DRed_scope.
Infix "-" := DRed.sub : DRed_scope.
Infix "*" := DRed.mult : DRed_scope.

Notation "'0'" := DRed.t0 : DRed_scope.
Notation "'1'" := DRed.t1 : DRed_scope.



  
    
                         
