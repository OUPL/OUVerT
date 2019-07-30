Set Implicit Arguments.
Unset Strict Implicit.

Require Import ProofIrrelevance.
Require Import QArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.


Import GRing.Theory Num.Def Num.Theory.

Require Import extrema numerics dyadic strings.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Module OrdNat
  <: OrderedType.OrderedType.
      Definition t := N.t.
      Definition eq := N.eq.
      Definition lt := N.lt.
      Lemma eq_refl : forall x : t, eq x x.
      Proof. apply: N.eq_refl. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. apply: N.eq_sym. Qed.                                      
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. apply: N.eq_trans. Qed.  
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. apply: N.lt_trans. Qed.                                           
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof. move=> x y H H2; rewrite /eq /N.eq in H2; subst x.
             apply: (N.lt_irrefl _ H). Qed.
      Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
      Proof. move=> x y; case H: (N.eq_dec x y).
             { by subst x; apply: OrderedType.EQ. }
             case H2: (N.ltb x y).
             { by apply: OrderedType.LT; rewrite /lt -N.ltb_lt. }
             apply: OrderedType.GT.
             have H3: N.le y x.
             { by rewrite -N.ltb_ge H2. }
             move: H3; rewrite N.lt_eq_cases; case => //.
             by move => H3; subst y; elimtype False. Qed.
      Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      Proof. apply: N.eq_dec. Qed.
End OrdNat.
      
Module M := Make OrdNat. (* The type of shared states *)
Module MFacts := Facts M.
Module MProps := Properties M.

(** OrdNatDep: A computational analogue of 'I_n *)

Module Type BOUND.
  Parameter n : nat.
  Parameter n_gt0 : (0 < n)%nat.
End BOUND.

Module OrdNatDep (B : BOUND)
  <: OrderedType.OrderedType.
      Notation n := B.n.
      Record t' : Type :=
        mk { val :> N.t;
             pf : (N.to_nat val < n)%nat }.
      Definition t := t'.
      Definition eq (x y : t) := N.eq (val x) (val y).
      Definition lt (x y : t) := N.lt (val x) (val y).
      Lemma eq_refl : forall x : t, eq x x.
      Proof. case => x pf; apply: N.eq_refl. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. case => x pf; case => y pf'; apply: N.eq_sym. Qed.   
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. case => x pf; case => y pf'; case => z pf''; apply: N.eq_trans. Qed.  
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. case => x pf; case => y pf'; case => z pf''; apply: N.lt_trans. Qed.        
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof. case => x pf; case => y pf' H H2; rewrite /eq /N.eq in H2.
             rewrite /lt H2 in H; apply: (N.lt_irrefl _ H). Qed.
      Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
      Proof.
        case => x pf; case => y pf'; case H: (N.eq_dec x y).
        { by subst x; apply: OrderedType.EQ. }
        case H2: (N.ltb x y).
        { by apply: OrderedType.LT; rewrite /lt -N.ltb_lt. }
        apply: OrderedType.GT.
        have H3: N.le y x.
        { by rewrite -N.ltb_ge H2. }
        move: H3; rewrite N.lt_eq_cases; case => //.
        by move => H3; subst y; elimtype False. Qed.
      Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      Proof. case => x pf; case => y pf'; apply: N.eq_dec. Qed.
End OrdNatDep.

Class Enumerable (T : Type) :=
  enumerable_fun : list T.
Notation "'enumerate' T" := (@enumerable_fun T _) (at level 30).

Class Enum_ok A `{Enumerable A} : Type :=
  mkEnum_ok { 
      enum_nodup : NoDupA (fun x : A => [eta eq x]) (enumerate A);
      enum_total : forall a : A, In a (enumerate A)
    }.


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


  Lemma nth_index_of_dec_eq: forall (T : Type) (l : list T) (f : T->T->bool) (t1 t2 : T),
    (forall x y, f x y = true <-> x = y) -> (forall x y, f x y = false <-> x <> y) ->
    In t1 l -> nth (index_of l (f t1)) l t2 = t1.
  Proof.
    intros.
    induction l; auto.
      inversion H1.
    simpl.
    destruct (f t1 a) eqn:e.
      rewrite -> H in e. auto.
    apply IHl.
    destruct H1; auto.
      exfalso. rewrite -> H0 in e. apply e. auto.
  Qed.

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

  Lemma index_of_nth_dec_eq: forall (T : Type) (l : list T) (f : T->T->bool) (A : T) (n : nat),
    (forall x y, f x y = true <-> x = y) -> (forall x y, f x y = false <-> x <> y) ->
    NoDupA (fun x : T => [eta eq x]) l ->
    (n < length l)%coq_nat -> index_of l (f (nth n l A)) = n.
  Proof.
    intros.
    generalize dependent l.
    induction n.
    { 
      intros.
      destruct l; auto.
      simpl.
      destruct (f t t) eqn:e;auto.
      exfalso. apply H0 with t t; auto.
    }
    intros.
    destruct l; auto.
      inversion H2. 
    simpl.
    destruct (f (nth n l A) t) eqn:e; auto.
    {
      rewrite -> H in e.
      inversion H1.
      exfalso. apply H5.
      apply In_InA; auto.
      rewrite <- e.
      apply nth_In.
      apply lt_S_n; auto.
    }
    rewrite IHn; auto.
      inversion H1; auto.
    apply lt_S_n; auto.
  Qed.

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

  

  
  Section enum_table.
    Variable T1 : eqType.
    Variable T2 : Type.
    Variable T1_enum : Enumerable T1.
    Variable T1_enum_ok : @Enum_ok T1 T1_enum.
    Variable T1_enum_ne : O <> length T1_enum.
    Hypothesis T1_eq_dec : forall x y : T1, {x = y} + {x <> y}.

    Record table : Type :=
      table_mk {
        t_list : list T2;
        t_list_length : length T1_enum = length t_list
      }.    

    Program Definition table_head (t : table) : T2 := @nonempty_head T2 (t_list t) _.
    Next Obligation. rewrite <- (t_list_length t). apply T1_enum_ne. Defined.

    Definition enum_head (t : table)  : T1 := @nonempty_head T1 T1_enum T1_enum_ne.

    Definition T1_eqb  (t1 t2 : T1) : bool :=
      @T1_eq_dec t1 t2.

    Lemma T1_eqb_true_iff: forall (t1 t2 : T1), T1_eqb t1 t2 = true <-> t1 = t2.
    Proof.
      intros.
      split; intros.
      2:{ rewrite H. unfold T1_eqb. destruct T1_eq_dec; auto. }
      unfold T1_eqb in H. destruct (T1_eq_dec t1 t2); auto. inversion H.
    Qed.

    Lemma T1_eqb_false_iff: forall (t1 t2 : T1), T1_eqb t1 t2 = false <-> t1 <> t2.
    Proof.
      intros. unfold T1_eqb.
      split; intros;
        destruct (T1_eq_dec t1 t2) eqn:e; auto.
      exfalso. apply H. auto.
    Qed.

    Definition lookup  (t : table) (x : T1) : T2 :=
     nth  (index_of T1_enum (T1_eqb x)) (t_list t) (table_head t).

    Definition zip_table (t : table)  := zip T1_enum (t_list t).

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
        destruct (size (t_list t) < size (t_list t))%N; auto.
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
        apply T1_eqb_true_iff.
        apply T1_eqb_false_iff.
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
      rewrite nth_index_of_dec_eq; intros; auto.
        apply T1_eqb_true_iff. 
        apply T1_eqb_false_iff.
      destruct T1_enum_ok. auto.
    Qed. 

    Lemma zip_table_map: forall (f : T1->T2), zip_table (map_to_table f) = map (fun x => (x, f x)) T1_enum.
    Proof. 
      intros.
      unfold map_to_table. unfold zip_table. simpl.
      rewrite zip_map. auto.
    Qed.

  End  enum_table.

End Enum_table.


Class RefineTypeAxiomClass (T : finType)
      (enumerateClass : Enumerable T) :=
  refineTypeAxiom_fun :
    enumerate T =i enum T /\ uniq (enumerate T).
Notation "'enumerateP' T" := (@refineTypeAxiom_fun T _ _) (at level 30).

Instance prodEnumerableInstance (aT bT : Type)
         (enumerableA : Enumerable aT)
         (enumerableB : Enumerable bT)
  : Enumerable (aT*bT) :=
  List.list_prod (enumerate aT) (enumerate bT).

Lemma InA_map_inj: forall (T1 T2 : eqType) (l : list T1) (f : T1->T2) (x : T1),
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

Lemma NoDupA_map_inj: forall (T1 T2 : eqType) (l : list T1) (f : T1->T2),
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

Lemma In_pair: forall (T1 T2 : eqType) (x1 x2: T1) (y : T2) (l : list T2),
    In (x1, y) (map [eta pair x2] l) -> x1 = x2.
Proof.
  intros.
  induction l.
    exfalso. auto.
  simpl in H.
  destruct H; auto.
  inversion H. auto.
Qed.


Lemma prodEnumerableInstance_nodup: forall (aT bT:  eqType) (la : Enumerable aT) (lb : Enumerable bT),
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



Lemma prodEnumerableInstance_ok (aT bT:  eqType)
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

Lemma no_dup_cons_all: forall (T : eqType) (l : list T) (l2 : list (list T)), 
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
  apply InA_alt. exists s; auto.
Qed.


Lemma no_dup_enum_list: forall (T : eqType) (l : list T) (n : nat), 
  NoDupA (fun x => [eta eq x]) l -> NoDupA (fun x => [eta eq x]) (list_enum l n).
Proof.
  intros.
  generalize dependent l.
  induction n; intros; simpl.
  { constructor; auto. unfold not. intros. inversion H0. }
  apply no_dup_cons_all; auto.
Qed.

Lemma in_list_to_len_list: forall (T : eqType) (l : list (list T)) (n : nat) (H : forall l' : list T, In l' l -> length l' = n)
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
  
Lemma no_dup_list_to_len_list: forall (T : eqType) (l : list (list T)) (n : nat) (H : forall l' : list T, In l' l -> length l' = n),
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
  
    
Lemma list_len_enumerate_ok: forall (T : eqType) (enum : Enumerable T) (enum_ok : @Enum_ok T enum) (n : nat),
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
  unfold enumerable_fun in enum_total1. 
  unfold list_len_enumerate in enum_total1.
  destruct list_len_l0.
  { inversion list_len_ok0. }
  apply in_cons_all; auto.
  inversion list_len_ok0.
  rewrite H0.
  rewrite <- in_list_to_len_list; auto.
  Unshelve.
  auto.
Qed.




Class Eq (A : Type) : Type :=
  decEq : A -> A -> Prop.

Class Eq_Dec (A : Type) (eq : Eq A) : Type :=
  isDec : forall x y : A,  {eq x y} + {~ eq x y}.

Class Eq_Refl (A : Type) (eq :Eq A) : Type :=
  isRefl : forall x : A, eq x x.

Instance eqProd
      (A B: Type) (eqA : Eq A) (eqB : Eq B)
  : Eq (A*B)%type :=
    fun p1 p2 =>
    match p1, p2 with
    | (a1, b1), (a2, b2) => (eqA a1 a2) /\ (eqB b1 b2)
    end. 
