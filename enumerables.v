Set Implicit Arguments.
Unset Strict Implicit.

Require Import ProofIrrelevance.
Require Import QArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.


Import GRing.Theory Num.Def Num.Theory.
Require Import OUVerT.extrema.
Require Import OUVerT.numerics.
Require Import OUVerT.dyadic.
Require Import OUVerT.strings.
Require Import OUVerT.compile.
(*The computable state representation is an FMap over
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.



Module Enum_table.

  Definition nonempty_head (T : Type) (l : list T) (H : O <> length l) : T.
    destruct l eqn:e.
      exfalso. apply H. auto.
    exact t.
  Defined.


  Lemma nonempty_head_correct: forall (T : Type) (l : list T) (x : T) (H : O <> length (x :: l)),
    @nonempty_head T (x :: l) H = x.
  Proof. auto. Qed.

  Lemma nonempty_head_map: forall (T1 T2 : Type) (l : list T1) (f : T1->T2)
      (H : O <> length l) (H0 : O <> length (map f l)),
    f (nonempty_head (l:=l) H) = @nonempty_head T2 (map f l) H0.
  Proof.
    intros.
    destruct l.
    { exfalso.  auto. }
    rewrite -> nonempty_head_correct. auto.
  Qed.


  (**Finds the index of an element if it is in the list, otherwise returns the length of the list**)
  Fixpoint index_of (T : Type) (l : list T) (f : T->bool) : nat :=
  match l with
  | nil => O
  | t :: l' => if f t then O else S (index_of l' f)
  end.

  Lemma zip_map: forall (T1 T2 : Type) (l : list T1) (f : T1->T2), zip l (map f l) = map (fun x => (x,f x)) l.
  Proof.
    intros.
    induction l; auto.
    simpl. rewrite IHl. auto.
  Qed.

  Lemma index_of_cons_true: forall (T : Type) (l : list T) (f : T->bool) (x: T),
    f x -> index_of (x :: l) f = O.
  Proof. intros. simpl. rewrite H. auto. Qed.

  Lemma nth_seq_nth_same: forall (T : Type) (l : list T) (A : T) (n : nat),
      nth n l A = seq.nth A l n.
  Proof. intros.
    generalize dependent n.
    induction l.
      destruct n; auto.
    intros.
    simpl.
    destruct n; simpl; auto.
  Qed.

  Lemma length_size_eq: forall (T : Type) (l : list T), length l = size l.
  Proof. intros. auto. Qed.



    Lemma in_zip_swap: forall {T1 T2 : Type} (l1 : list T1) (l2 : list T2) (t1 : T1) (t2 : T2),
        In (t1,t2) (zip l1 l2) -> In (t2,t1) (zip l2 l1).
    Proof.
      intros.
      generalize dependent l1.
      induction l2; intros; auto.
      {
        simpl in H.
        induction l1; auto.
      }
      simpl in H.
      induction l1; auto.
      simpl in *.
      destruct H; auto.
      inversion H. auto.
    Qed.


  (**Lemma eqType_eq_dec: forall (T : eqType) (x y : T), {x = y} + {x <> y}.
  Proof.
    intros.
    destruct (eqVneq x y); auto.
    right.
    assert (x <> y /\ true).
    2: { destruct H. auto. }
    assert(reflect (x <> y /\ true) ((x != y) && true)).
      apply predD1P.
    inversion H; auto.
    rewrite andbT in H0.
    inversion i; auto.
    rewrite H3 in H0; auto.
  Qed.

  Definition eqType_eqb {T : eqType} (x y : T) : bool :=
    eqType_eq_dec x y.

  Lemma eqType_eqb_true_iff: forall {T : eqType} (t1 t2 : T), eqType_eqb t1 t2 = true <-> t1 = t2.
  Proof.
    intros.
    split; intros.
    2:{ rewrite H. unfold eqType_eqb. destruct eqType_eq_dec; auto. }
    unfold eqType_eqb in H. destruct (eqType_eq_dec t1 t2); auto. inversion H.
  Qed.

  Lemma eqType_eqb_false_iff: forall {T : eqType} (t1 t2 : T), eqType_eqb t1 t2 = false <-> t1 <> t2.
  Proof.
    intros. unfold eqType_eqb.
    split; intros;
      destruct (eqType_eq_dec t1 t2) eqn:e; auto.
    exfalso. apply H. auto.
  Qed.**)

  Section eqb_proofs.
    Variable T : Type.
    Hypothesis eqb: forall (t1 t2 : T), {t1 = t2} + {t1 <> t2}.

    Lemma nth_index_of_eqb: forall (l : list T) (t1 t2 : T),
      In t1 l -> nth (index_of l (eqb t1)) l t2 = t1.
    Proof.
      intros.
      induction l; auto.
        inversion H.
      simpl.
      destruct (eqb t1 a) eqn:e; auto.
      apply IHl.
      simpl in H.
      destruct H; auto.
      exfalso. auto.
    Qed.

    Lemma eqb_refl: forall t : T, eqb t t.
    Proof. intros. destruct eqb; auto. Qed.

    Lemma eqb_iff: forall t1 t2 : T, eqb t1 t2 <-> t1 = t2.
    Proof.
      intros.
      split; intros; destruct (eqb t1 t2); auto.
      inversion H.
    Qed.

    Lemma index_of_nth_dec_eq: forall (l : list T) (A : T) (n : nat),
      NoDupA (fun x : T => [eta eq x]) l -> (n < length l)%coq_nat -> index_of l (eqb (nth n l A)) = n.
    Proof.
      intros.
      generalize dependent l.
      induction n.
      {
        intros.
        destruct l; auto.
        simpl.
        rewrite eqb_refl; auto.
      }
      intros.
      destruct l; auto.
        inversion H0.
      simpl.
      destruct (eqb (nth n l A) t) eqn:e; auto.
      {
        inversion H.
        exfalso. apply H3.
        apply In_InA; auto.
        rewrite <- e0.
        apply nth_In.
        apply lt_S_n; auto.
      }
      rewrite IHn; auto.
        inversion H; auto.
      apply lt_S_n; auto.
    Qed.

  (**Lemma reflet_eqType_eqb: forall (T : eqType) (x y : T), reflect (x=y) (eqType_eqb x y).
  Proof.
    intros.
    destruct (eqType_eqb x y) eqn:e; auto.
    { constructor. apply eqType_eqb_true_iff. auto. }
    constructor. apply eqType_eqb_false_iff. auto.
  Qed.**)
  End eqb_proofs.
  Section enum_table.

    Variable T1 : Type.
    Variable T2 : Type.
    Variable T1_enum : Enumerable T1.
    Variable T1_enum_ok : @Enum_ok T1 T1_enum.
    Variable T1_enum_ne : O <> length T1_enum.
    Variable T1_eqdec : forall t1 t2 : T1, {t1 = t2} + {t1 <> t2}.


    Record table : Type :=
      table_mk {
        t_list : list T2;
        t_list_length : length T1_enum = length t_list
      }.

    Program Definition table_head (t : table) : T2 := @nonempty_head T2 (t_list t) _.
    Next Obligation. rewrite <- (t_list_length t). apply T1_enum_ne. Defined.

    Definition enum_head (t : table)  : T1 := @nonempty_head T1 T1_enum T1_enum_ne.


    Definition lookup  (t : table) (x : T1) : T2 :=
     nth  (index_of T1_enum (T1_eqdec x)) (t_list t) (table_head t).

    Definition zip_table (t : table)  := zip T1_enum (t_list t).

    Definition eq_func (t : table) (f : T1->T2):= forall (x : T1), lookup t x = f x.

    Definition to_func (t : table) : (T1->T2) := (fun x => lookup t x).

    Lemma zip_table_length: forall (t : table), length (zip_table t) = length T1_enum.
    Proof.
      intros.
      unfold zip_table.
      rewrite length_size_eq.
      rewrite size_zip.
      repeat rewrite <- length_size_eq.
      rewrite (t_list_length t).
      repeat rewrite length_size_eq.
      unfold minn.
        destruct (size (t_list t) < size (t_list t))%nat; auto.
    Qed.

    Lemma nth_lookup: forall (t : table) (n : nat) (x A1: T1) (y A2 : T2) ,
        (n < length T1_enum)%coq_nat -> nth n T1_enum A1 = x -> nth n (t_list t) A2 = y ->
        lookup t x = y.
    Proof.
      intros.
      unfold lookup.
      rewrite <- H0.
      rewrite -> index_of_nth_dec_eq; auto.
      {
        rewrite -> nth_indep with _ _ _ _ A2; auto.
        rewrite <- t_list_length.
        auto.
      }
      apply (T1_enum_ok).
    Qed.

    Program Definition map_to_table (f : T1->T2) :=
      @table_mk (map f T1_enum) _.
    Next Obligation.
      rewrite map_length. auto.
    Defined.


    Lemma table_head_map: forall (f : T1->T2), table_head (map_to_table f) = f  (nonempty_head  T1_enum_ne).
    Proof.
      intros.
      unfold table_head.
      simpl.
      rewrite <- nonempty_head_map with T1 T2 T1_enum f T1_enum_ne (table_head_obligation_1 (t:=map_to_table f)); auto.
    Qed.

    Lemma lookup_map: forall (f : T1->T2) (x : T1), @lookup (map_to_table f) x = f x.
    Proof.
      intros.
      unfold lookup. simpl.
      rewrite table_head_map.
      rewrite -> map_nth.
      rewrite nth_index_of_eqb; intros; auto.
      destruct T1_enum_ok. auto.
    Qed.

    Lemma zip_table_map: forall (f : T1->T2), zip_table (map_to_table f) = map (fun x => (x, f x)) T1_enum.
    Proof.
      intros.
      unfold map_to_table. unfold zip_table. simpl.
      rewrite zip_map. auto.
    Qed.

    Lemma map_to_table_ext: forall (f1 f2 : T1->T2), (forall x : T1, f1 x = f2 x) ->
      map_to_table f1 = map_to_table f2.
    Proof.
      intros. unfold map_to_table.
      apply map_ext with _ _ f1 f2 T1_enum in H.
      generalize dependent (map_to_table_obligation_1 f1).
      rewrite -> H.
      intros. f_equal. apply proof_irrelevance.
    Qed.


  End enum_table.


  Definition table_eqb (T1 T2 : eqType) (T1_enum : Enumerable T1) (t1 t2 : table T2 T1_enum) : bool :=
   eq_op (t_list t1) (t_list t2).

  Definition table_eqb_func (T1 T2 : eqType) (T1_enum : Enumerable T1)
      (t : table T2 T1_enum) (f : T1->T2) : bool :=
   table_eqb t (map_to_table T1_enum f).


  Lemma table_eqnP : forall (T1 T2 : eqType) (T1_enum : Enumerable T1) (x y : table T2 T1_enum), reflect (x = y) (table_eqb x y).
  Proof.
    intros.
    unfold table_eqb.
    destruct (eq_op (t_list x) (t_list y)) eqn:e.
    {
      constructor.
      assert(t_list x = t_list y).
        apply/(eqP). auto.
      destruct x; destruct y. simpl in *. generalize t_list_length0.
      rewrite H. intros. f_equal. apply proof_irrelevance.
    }
    constructor. destruct x; destruct y.
    unfold not in *. intros.
    simpl in *. inversion H. rewrite H1 in e.
    rewrite eq_refl in e. inversion e.
  Qed.

  (**Definition table_eqMixin (T1 T2 : eqType) (T1_enum : Enumerable T1) : Equality.mixin_of (Enum_table.table T2 T1_enum) :=
    EqMixin (op:=(@table_eqb T1 T2 T1_enum)) (@table_eqnP _ _ _).

  Definition table_eqType (T1 T2: eqType) (T1_enum : Enumerable T1) := Equality.Pack (@table_eqMixin T1 T2 T1_enum) (@table T1 T2 T1_enum).
  **)


End Enum_table.


Lemma InA_map_inj: forall (T1 T2 : Type) (l : list T1) (f : T1->T2) (x : T1),
    (forall (t1 t2 : T1), f t1 = f t2 -> t1 = t2) ->
    (InA (fun x : T1 => [eta eq x]) x l <-> InA (fun x : T2 => [eta eq x]) (f x) (map f l)).
Proof.
  intros.
  split; intros.
  {
    induction l.
      inversion H0.
    inversion H0.
    { apply In_InA; auto. rewrite <- H2. apply in_map. apply in_eq. }
    simpl. auto.
  }
  induction l.
    inversion H0.
  inversion H0; auto.
Qed.

Lemma NoDupA_map_inj: forall (T1 T2 : Type) (l : list T1) (f : T1->T2),
    NoDupA (fun x : T1 => [eta eq x]) l ->
    (forall (t1 t2 : T1), f t1 = f t2 -> t1 = t2) ->
    NoDupA (fun x : T2 => [eta eq x]) (map f l).
Proof.
  intros.
  induction l.
    simpl. auto.
  simpl.
  inversion H.
  constructor; auto.
  rewrite <- InA_map_inj; auto.
Qed.

Lemma In_pair: forall (T1 T2 : Type) (x1 x2: T1) (y : T2) (l : list T2),
    In (x1, y) (map [eta pair x2] l) -> x1 = x2.
Proof.
  intros.
  induction l.
    exfalso. auto.
  simpl in H.
  destruct H; auto.
  inversion H. auto.
Qed.


Lemma prodEnumerableInstance_nodup: forall (aT bT:  Type) (la : Enumerable aT) (lb : Enumerable bT),
     NoDupA (fun x : aT => [eta eq x]) (enumerate _ la) ->
     NoDupA (fun x : bT => [eta eq x]) (enumerate _ lb) ->
     NoDupA (fun x : aT * bT => [eta eq x]) (prodEnumerableInstance la lb).
Proof.
  intros.
    unfold prodEnumerableInstance.
    unfold Enumerable in *.
    unfold enumerable_fun in *.
    generalize dependent lb.
    induction la.
      simpl. auto.
    intros. simpl.
    inversion H.
    apply NoDupA_app; auto.
    { apply NoDupA_map_inj; auto. intros. inversion H5. auto. }
    intros.
    rewrite -> InA_alt in H5. destruct H5. destruct H5.
    rewrite <- H5 in H7. clear H5. clear x1.
    rewrite -> InA_alt in H6.
    destruct H6.
    destruct H5.
    rewrite <- H5 in H6.
    clear H5. clear x1.
    destruct x0.
    rewrite -> in_prod_iff in H6.
    destruct H6.
    apply In_pair in H7.
    apply H3.
    rewrite H7 in H5; auto.
    apply In_InA; auto.
Qed.



Lemma prodEnumerableInstance_ok (aT bT:  Type)
     (enumerableA : Enumerable aT)
     (enumerableB : Enumerable bT)
     (enum_okA: @Enum_ok aT enumerableA)
     (enum_okB: @Enum_ok bT enumerableB)
  : @Enum_ok _ (prodEnumerableInstance enumerableA enumerableB).
  destruct enum_okA.
  destruct enum_okB.
  constructor.
    apply prodEnumerableInstance_nodup; auto.
  intros.
  destruct a.
  apply in_prod_iff.
  split; auto.
Qed.






Record list_len {T : Type} (n : nat) : Type :=
  mk_list_len {
    list_len_l : list T;
    list_len_ok : length list_len_l = n
  }.


Fixpoint cons_all {T : Type} (l : list T) (l2 : list (list T)) :=
match l with
| nil => nil
| x :: l' =>  ( map (fun l2' => x :: l2') l2) ++ (cons_all l' l2)
end.



Fixpoint list_enum {T : Type} (l : list T) (n : nat) : list (list T) :=
match n with
| O => (nil) :: nil
| S n' => cons_all l (list_enum l n')
end.


Lemma in_cons_all: forall (T : Type) (a : T) (l l1: list T) (l2 : list (list T)),
    (In a l1 /\ In l l2) <-> In (a :: l) (cons_all l1 l2).
Proof.
  intros.
  split; intros.
  {
    destruct H.
    induction l1; intuition.
    simpl. simpl in H.
    rewrite in_app_iff.
    destruct H; auto.
    left. rewrite H.
    rewrite in_map_iff.
    exists l; auto.
  }
  induction l1.
  { simpl in H. inversion H. }
  simpl in *.
  rewrite -> in_app_iff in H.
  split.
  {
    destruct H.
    {
      rewrite -> in_map_iff in H.
      destruct H.
      destruct H.
      inversion H. auto.
    }
    right.
    apply IHl1. auto.
  }
  destruct H.
  {
    rewrite -> in_map_iff in H.
    destruct H.
    destruct H.
    inversion H.
    rewrite <- H3. auto.
  }
  apply IHl1. auto.
Qed.



Lemma cons_all_nonempty: forall {T : Type} (l1 l2 : list T) (l3 : list (list T)),
    In l1 (cons_all l2 l3) -> l1 <> [::].
Proof.
  intros.
  generalize dependent l1.
  generalize dependent l3.
  induction l2; intuition.
  destruct l1.
  2: { inversion H0. }
  simpl in H.
  apply in_app_or in H.
  destruct H.
  {
    apply in_map_iff in H.
    destruct H.
    destruct H.
    inversion H.
  }
  eapply IHl2; eauto.
Qed.


Lemma in_list_enum_cons: forall {T : Type} (l1 l2 : list T) (x : T) (n : nat),
  In l1 (list_enum l2 n) -> In l1 (list_enum (x :: l2) n).
Proof.
  intros.
  generalize dependent l1.
  generalize dependent l2.
  induction n; auto.
  simpl. intros.
  rewrite -> in_app_iff.
  right.
  destruct l1.
  { exfalso. eapply  cons_all_nonempty; eauto. }
  apply in_cons_all.
  apply in_cons_all in H.
  destruct H.
  split; auto.
Qed.




Lemma list_enum_len: forall {T : Type} (l1 l2 : list T) (n : nat), In l1 (list_enum l2 n) -> length l1 = n.
Proof.
  intros.
  generalize dependent l2.
  generalize dependent l1.
  induction n.
  { intros. simpl in H. destruct H; intuition. rewrite <- H. auto. }
  intros.
  simpl in H.
  destruct l1.
    exfalso. eapply cons_all_nonempty; eauto.
  simpl.
  apply in_cons_all in H.
  destruct H.
  erewrite IHn; eauto.
Qed.



Program Fixpoint list_to_list_len {T : Type} (l : list (list T)) (n : nat) (H : forall l' : list T, In l' l -> length l' = n) :
    list (@list_len T n) := match l with
| nil => nil
| x :: l' => (@mk_list_len T n x _) :: @list_to_list_len T l' n _
end.
Next Obligation.
  apply H. simpl. auto.
Defined.
Next Obligation.
  apply H. simpl. auto.
Defined.

Lemma list_len0_same: forall {T : Type} (l1 l2 : @list_len T O), l1 = l2.
Proof.
  intros.
  destruct l1.
  destruct l2.
  destruct list_len_l0.
  2: { inversion list_len_ok0. }
  destruct list_len_l1.
  2: { inversion list_len_ok1. }
  f_equal. apply proof_irrelevance.
Qed.





Program Definition list_len_enumerate {T : Type} (l : list T) (n : nat) : list (@list_len T n) :=
  @list_to_list_len T (list_enum l n) n _.
Next Obligation.
  apply list_enum_len with l. auto.
Defined.

Lemma no_dup_cons_all: forall (T : Type) (l : list T) (l2 : list (list T)),
    NoDupA (fun x => [eta eq x]) l -> NoDupA (fun x => [eta eq x]) l2 -> NoDupA (fun x => [eta eq x]) (cons_all l l2).
Proof.
  intros.
  generalize dependent l2.
  induction l.
  { simpl. constructor. }
  intros. simpl.
  apply NoDupA_app; auto.
  {
    apply NoDupA_map_inj; auto.
    intros.
    inversion H1. auto.
  }
  {
    apply IHl; auto.
    inversion H; auto.
  }
  intros.
  apply InA_alt in H1.
  destruct H1. destruct H1.
  apply InA_alt in H2.
  destruct H2. destruct H2.
  rewrite <- H1 in H3. clear H1.
  rewrite <- H2 in H4. clear H2 x0 x1.
  destruct x.
  { eapply cons_all_nonempty; eauto. }
  rewrite <- in_cons_all in H4.
  destruct H4.
  rewrite -> in_map_iff in H3.
  destruct H3. destruct H3.
  inversion H3.
  rewrite H7 in H4. clear H3 H7 x0.
  inversion H.  apply H7.
  apply InA_alt. eauto.
Qed.


Lemma no_dup_enum_list: forall (T : Type) (l : list T) (n : nat),
  NoDupA (fun x => [eta eq x]) l -> NoDupA (fun x => [eta eq x]) (list_enum l n).
Proof.
  intros.
  generalize dependent l.
  induction n; intros; simpl.
  { constructor; auto. unfold not. intros. inversion H0. }
  apply no_dup_cons_all; auto.
Qed.

Lemma in_list_to_len_list: forall (T : Type) (l : list (list T)) (n : nat) (H : forall l' : list T, In l' l -> length l' = n)
    (x : list T) (H0 : length x = n), In  (@mk_list_len T n x H0) (@list_to_list_len T l n H) <-> In x l.
Proof.
  intros.
  split; intros.
  {
    generalize dependent n.
    generalize dependent x.
    induction l. intros. inversion H1.
    simpl in *. intros.
    destruct H1.
      inversion H1. auto.
    right. eapply IHl.
    assert (forall H', (list_to_list_len (l:=l) H') = (list_to_list_len (l:=l) (fun (l'0 : seq.seq T) (H0 : In l'0 l) => H l'0 (or_intror H0)))).
    { intros. f_equal. apply proof_irrelevance. }
    erewrite H2. apply H1.
  }
  generalize dependent n.
  generalize dependent x.
  induction l. intros. inversion H1.
  intros. simpl.
  simpl in H1. destruct H1.
  2: { right. apply IHl. auto. }
  left.
  generalize H.
  generalize H0.
  rewrite H1.
  intros. f_equal. apply proof_irrelevance.
  Unshelve. auto.
Qed.

Lemma no_dup_list_to_len_list: forall (T : Type) (l : list (list T)) (n : nat) (H : forall l' : list T, In l' l -> length l' = n),
    NoDupA (fun x => [eta eq x]) l -> NoDupA (fun x => [eta eq x]) (@list_to_list_len T l n H).
Proof.
  intros.
  generalize dependent n.
  generalize dependent H0.
  induction l.
    simpl. constructor.
  simpl in *.
  intros.
  inversion H0.
  constructor.
  2: { apply IHl. auto. }
  unfold not.
  intros.
  apply H3.
  rewrite InA_alt. eexists. split;  eauto.
  eapply in_list_to_len_list; eauto.
  erewrite InA_alt in H5.
  destruct H5.
  destruct H5.
  rewrite <- H5 in H6.
  eauto.
Qed.


Lemma list_len_enumerate_ok: forall (T : Type) (enum : Enumerable T) (enum_ok : @Enum_ok T enum) (n : nat),
    @Enum_ok (@list_len T n) (@enumerable_fun (@list_len T n) (@list_len_enumerate T enum n)).
Proof.
  intros.
  inversion enum_ok.
  induction n.
  {
    constructor; unfold enumerable_fun.
    { unfold list_len_enumerate. simpl. apply NoDupA_singleton. }
    intros.
    simpl.
    left.
    apply list_len0_same.
  }
  inversion IHn.
  constructor.
  {
    unfold enumerable_fun.
    unfold list_len_enumerate.
    apply no_dup_list_to_len_list. simpl.
    apply no_dup_cons_all; auto.
    apply no_dup_enum_list. auto.
  }
  intros.
  unfold enumerable_fun.
  unfold list_len_enumerate.
  destruct a.
  apply in_list_to_len_list; auto.
  simpl.
  unfold enumerable_fun in enum_total0.
  unfold list_len_enumerate in enum_total0.
  destruct list_len_l0.
  { inversion list_len_ok0. }
  apply in_cons_all; auto.
  split; auto.
  inversion list_len_ok0.
  rewrite H0.
  rewrite <- in_list_to_len_list; auto.
  Unshelve.
  auto.
Qed.


Program Definition enumerate_table {T1 T2 : Type} (T1_eqdec : forall a b : T1, {a = b} + {a <> b}) (T1_enum : Enumerable T1) (T2_enum : Enumerable T2)
      (T1_enum_ok : @Enum_ok T1 T1_enum) (T2_enum_ok : @Enum_ok T2 T2_enum) (T1_enum_ne : O <> length T1_enum)
       : Enumerable (@Enum_table.table T1 T2 T1_enum)
  := map (fun l => @Enum_table.table_mk  T1 T2 T1_enum (list_len_l l) _)
      (list_len_enumerate (enumerate T2) (length (enumerate T1))).
Next Obligation.
  destruct l. auto.
Defined.


Lemma length_list_to_list_len:forall (T : Type) (l : list (list T)) (n : nat)
      (H : forall l' : list T, In l' l -> length l' = n) (x : list T),
        length (list_to_list_len H) = length l.
Proof. intros. induction l; simpl; auto. Qed.

Lemma length_cons_all: forall (T : Type) (l : list T) (l2 : list (list T)), length (cons_all l l2) = (length l * length l2)%coq_nat.
Proof.
  intros.
  induction l; auto.
  simpl.
  rewrite  Enum_table.length_size_eq.
  rewrite size_cat.
  rewrite size_map.
  rewrite <- Enum_table.length_size_eq.
  rewrite <- IHl. auto.
Qed.

Lemma list_enum_nonempty: forall {T : Type} (l : list T) (n : nat),
  O <> length l -> O <> length (list_enum l n).
Proof.
  intros.
  induction n.
    simpl. auto.
  simpl.
  rewrite length_cons_all.
  apply lt_0_neq.
  apply Nat.mul_pos_pos.
  {
    destruct (length l).
      exfalso. apply H. auto.
    apply Nat.lt_0_succ.
  }
  destruct (length (list_enum l n)).
    exfalso. apply IHn. auto.
  apply Nat.lt_0_succ.
Qed.



Lemma enumerate_table_nonempty: forall {T1 T2 : Type} (T1_eqdec : forall a b : T1, {a = b} + {a <> b}) T1_enum T2_enum  T1_enum_ok T2_enum_ok  T1_enum_ne ,
      O <> (length T2_enum) -> O <> length (@enumerate_table T1 T2 T1_eqdec T1_enum T2_enum T1_enum_ok T2_enum_ok T1_enum_ne ).
Proof.
  intros.
  unfold enumerate_table.
  unfold enumerable_fun.
  rewrite Enum_table.length_size_eq.
  rewrite size_map.
  unfold list_len_enumerate.
  rewrite <- Enum_table.length_size_eq.
  rewrite length_list_to_list_len; auto.
  apply list_enum_nonempty. auto.
Qed.


Lemma NoDupA_map: forall (T1 T2 : Type) (f : T1->T2) (l : list T1),
  (forall (x y : T1), f x = f y -> x = y) -> NoDupA (fun x=> [eta eq x]) l ->
    NoDupA (fun x => [eta eq x]) (map f l).
Proof.
  intros.
  induction l; simpl; auto.
  constructor.
  {
    inversion H0.
    unfold not. intros.
    apply H3.
    apply In_InA; auto.
    rewrite -> InA_alt in H5.
    destruct H5. destruct H5.
    rewrite -> in_map_iff in H6.
    destruct H6. destruct H6.
    rewrite <- H5 in H6.
    apply H in H6.
    rewrite H6 in H7.
    auto.
  }
  apply IHl.
  inversion H0. auto.
Qed.



Lemma enum_table_total: forall {T1 T2 : Type} (T1_eqdec : forall a b : T1, {a = b} + {a <> b}) (T1_enum : Enumerable T1) (T2_enum : Enumerable T2)
      (T1_enum_ok : @Enum_ok T1 T1_enum) (T2_enum_ok : @Enum_ok T2 T2_enum) (T1_enum_ne : O <> length T1_enum)
      (t : (@Enum_table.table T1 T2 T1_enum)),
      In t (@enumerate_table T1 T2 T1_eqdec T1_enum T2_enum  _ _ T1_enum_ne).
Proof.
  intros.
  unfold enumerate_table.
  destruct list_len_enumerate_ok with T2 T2_enum (length (enumerate T1)); auto.
  erewrite in_map_iff.
  destruct t.
  assert(length t_list = (length (enumerate T1))).
  { unfold enumerable_fun. rewrite <- t_list_length. auto. }
  exists (mk_list_len H).
  split; auto.
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.


Lemma enum_table_ok: forall {T1 T2 : Type} (T1_eqdec : forall a b : T1, {a = b} + {a <> b}) (T1_enum : Enumerable T1) (T2_enum : Enumerable T2)
      (T1_enum_ok : @Enum_ok T1 T1_enum) (T2_enum_ok : @Enum_ok T2 T2_enum) (T1_enum_ne : O <> length T1_enum),
  @Enum_ok (@Enum_table.table T1 T2 T1_enum) (@enumerate_table T1 T2 T1_eqdec T1_enum T2_enum  _ _ T1_enum_ne).
Proof.
  intros.
  constructor; unfold enumerable_fun.
  {
    apply NoDupA_map.
    {
      intros. inversion H.
      destruct x. destruct y.
      unfold list_len_l in H1.
      generalize list_len_ok0.
      rewrite H1. intros. f_equal.
      apply proof_irrelevance.
    }
    apply list_len_enumerate_ok.
    auto.
  }
  apply enum_table_total.
Qed.


Record enum_nat (n : nat) : Type :=
  mk_enum_nat {
    enum_nat_n : nat;
    enum_nat_lt : lt enum_nat_n n
  }.

Program Fixpoint enum_nat_enumerate_aux (n : nat) (m : nat) (H : le m n) : list (enum_nat n):=
match m with
| O => nil
| S m' => (@mk_enum_nat n m' _) :: (@enum_nat_enumerate_aux n m' _)
end.
Next Obligation.
  unfold lt in *.
  apply Nat.le_trans with (S m'); auto.
Qed.

Program Definition enum_nat_enumerate (n : nat) : list (enum_nat n) :=
  @enum_nat_enumerate_aux n n _.

Lemma enum_nat_enumerate_aux_max: forall (n m : nat) (p : enum_nat n) (H : le m n),
  In p (@enum_nat_enumerate_aux n m H) -> lt (enum_nat_n p) m.
Proof.
  intros.
  generalize dependent p.
  generalize dependent n.
  induction m; intros.
    inversion H0.
  simpl in H0.
  destruct H0.
  {
    destruct p.
    simpl in *.
    by inversion H0.
  }
  apply IHm in H0.
  apply lt_trans with m; auto.
Qed.


Program Definition enum_nat_list_to_succ (n : nat) (l : list (enum_nat n))
    : list (enum_nat (S n)) :=
  map (fun x => @mk_enum_nat (S n) (enum_nat_n x) _) l.
Next Obligation.
  destruct x.
  simpl.
  apply Nat.le_trans with n; auto.
Qed.

Lemma enum_nat_enumerate_aux_to_succ: forall (n m : nat) (H0 : le m n) (H1 : le m (S n)),
    @enum_nat_enumerate_aux (S n) m H1 = enum_nat_list_to_succ (@enum_nat_enumerate_aux n m H0).
Proof.
  intros.
  generalize dependent n.
  induction m; auto; intros.
  unfold enum_nat_list_to_succ in *.
  simpl in *.
  rewrite IHm; auto.
  {
    apply le_trans with (S m); auto.
  }
  intros.
  assert(H1 = enum_nat_list_to_succ_obligation_1 {| enum_nat_n := m; enum_nat_lt := H0 |}).
    apply proof_irrelevance.
  rewrite <- H.
  assert((enum_nat_enumerate_aux Hyp0) = enum_nat_enumerate_aux (enum_nat_enumerate_aux_obligation_2 H0 (erefl (S m)))).
  2:{ rewrite H2. auto. }
  assert(Hyp0 =   (enum_nat_enumerate_aux_obligation_2 H0 (erefl (S m)))).
    apply proof_irrelevance.
  by rewrite H2.
Qed.

Lemma enum_nat_ok: forall n : nat, @Enum_ok (enum_nat n) (enum_nat_enumerate n).
Proof.
  intros.
  constructor; unfold enumerable_fun;
    unfold enum_nat_enumerate.
  {
    induction n.
      simpl. auto.
    simpl.
    constructor.
    {
      unfold not.
      intros.
      apply InA_alt in H.
      destruct H.
      destruct H.
      apply enum_nat_enumerate_aux_max in H0.
      destruct x.
      simpl in *.
      inversion H.
      rewrite H2 in H0.
      eapply Nat.lt_irrefl. apply H0.
    }
    rewrite enum_nat_enumerate_aux_to_succ.
    unfold enum_nat_list_to_succ.
    apply NoDupA_map.
    {
      intros.
      destruct x.
      destruct y.
      inversion H.
      generalize enum_nat_lt0.
      generalize enum_nat_lt1.
      rewrite H1.
      intros. f_equal. apply proof_irrelevance.
    }
    assert (le_n n = enum_nat_enumerate_obligation_1 n).
      apply proof_irrelevance.
    rewrite H.
    auto.
  }
  intros.
  induction n.
  { inversion a. inversion enum_nat_lt0. }
  simpl.
  destruct (Nat.eq_dec (enum_nat_n a) n).
  {
    left. destruct a. simpl in e.
    generalize enum_nat_lt0.
    rewrite e.
    intros. f_equal. apply proof_irrelevance.
  }
  right.
  rewrite enum_nat_enumerate_aux_to_succ.
  unfold enum_nat_list_to_succ.
  remember (fun x : enum_nat n =>
      {| enum_nat_n := enum_nat_n x; enum_nat_lt := enum_nat_list_to_succ_obligation_1 x |}) as f.
  destruct a.
  simpl in *.
  unfold lt in enum_nat_lt0.
  remember enum_nat_lt0 as H.
  clear HeqH.
  apply le_S_n in enum_nat_lt0.
  assert(enum_nat_n0 < n)%coq_nat.
    apply Nat.le_neq. split; auto.
  assert ({| enum_nat_n := enum_nat_n0; enum_nat_lt := H |} = f (@mk_enum_nat n enum_nat_n0 H0)).
    rewrite Heqf. simpl. f_equal. apply proof_irrelevance.
  rewrite H1.
  apply in_map.
  assert (enum_nat_enumerate_obligation_1 n = le_n n).
    apply proof_irrelevance.
  rewrite <- H2.
  apply IHn.
Qed.
