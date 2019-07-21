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

  Program Fixpoint zip (T1 T2 : Type) (l1 : list T1) (l2 : list T2) (H : length l1 = length l2) : list (T1 * T2):=
  match l1,l2 with
  | x1 :: l1',x2 :: l2' => (x1,x2) :: @zip T1 T2 l1' l2' _
  | nil,nil => @nil (T1 * T2)
  | x1 :: l1', nil => _
  | nil, x2 :: l2' => _
  end.
    

  Section enum_table.
    Variable T1 T2 : Type.
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
    Next Obligation. rewrite <- (t_list_length t). auto. Defined.

    Definition enum_head : T1 := @nonempty_head T1 T1_enum T1_enum_ne.

    Definition T1_eqb (t1 t2 : T1) : bool :=
      T1_eq_dec t1 t2.
      
     Definition lookup (t : table) (x : T1) : T2 :=
       nth  (find (T1_eqb x) T1_enum) (t_list t)  (table_head t).

    Program Definition map_to_table (f : T1->T2) :=
      @table_mk (map f T1_enum) _.
    Next Obligation.
      rewrite map_length. auto.
    Defined.

    Definition zip_table (t : table) := @zip T1 T2 T1_enum  (t_list t) (t_list_length t).

  End enum_table.
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
