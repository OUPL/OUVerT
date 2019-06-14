Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import OUVerT.numerics.

Local Open Scope ring_scope.

(** This file defines generic notions of extrema. *)

Section Extrema.
(** The primary parameters are:
      - [rty : realFieldType]    A real field
      - [I : finType]            A finite type
      - [P : pred I]             A subset of [I] 
      - [F : I -> rty]           A "valuation" function over [I] 
    The module implements the following functions: 
      - [arg_min]                An [i : I \in P] that minimizes [F]
      - [arg_max]                An [i : I \in P] that maximizes [F]
      - [min]                    := [F arg_min]
      - [max]                    := [F arg_max]
*)
  Variable rty : realFieldType.
  Variables (I : finType) (P : pred I) (F : I -> rty).

  Section getOrd.
    Variable ord : rel rty.
    Hypothesis ord_refl : reflexive ord.
    Hypothesis ord_trans : transitive ord.
    Hypothesis ord_total : total ord.

    Fixpoint getOrd (i0 : I) (l : list I) : I :=
      if l is (i :: l') then
        if ord (F i0) (F i) then getOrd i0 l' else getOrd i l'
      else i0.

    Lemma getOrd_mono i1 i2 l :
      ord (F i1) (F i2) ->
      ord (F (getOrd i1 l)) (F (getOrd i2 l)).
    Proof.
      move: i1 i2; elim: l=> // a l IH i1 i2 H /=.
      case H2: (ord (F i1) (F a)). 
      { by case H3: (ord (F i2) (F a)); apply: IH.
      }
      case H3: (ord (F i2) _)=> //.
      apply: IH.
      have H4: ord (F i1) (F a).
      { by apply: ord_trans; first by apply: H.
      }
      by rewrite H4 in H2.
    Qed.    

    Lemma getOrd_minimalIn i0 l :
      [&& ord (F (getOrd i0 l)) (F i0)
        & [forall (t | t \in l), ord (F (getOrd i0 l)) (F t)]].
    Proof.
      move: i0; elim: l.
      { move=> i0; apply/andP; split=> //.
        by apply/forallP.
      }
      move=> a l IH i0.
      apply/andP; split.
      { simpl; case H2: (ord (F i0) _)=> //.
        by case: (andP (IH i0)).                                        
        apply: ord_trans.        
        case: (andP (IH a))=> H3 _; apply: H3.
        by case: (orP (ord_total (F i0) (F a))); first by rewrite H2.
      }
      apply/forallP=> x; apply/implyP.
      move: (in_cons a l x)=> ->; case/orP.
      { move/eqP=> ?; subst x=> /=.
        case H4: (ord (F i0) _).
        case: (andP (IH i0))=> H2 _.
        by apply: ord_trans; first by apply: H2.
        by case: (andP (IH a)).
      }
      move=> H /=.
      case H2: (ord (F i0) _).
      { case: (andP (IH i0))=> H0; move/forallP; move/(_ x).
        by move/implyP; move/(_ H)=> H3.
      }
      case: (andP (IH a))=> H3; move/forallP; move/(_ x).
      by move/implyP; move/(_ H)=> H4.
    Qed.

    Definition getOrd_tot i0 := getOrd i0 (enum I).
    
    Lemma getOrd_totP i0 : [forall i, ord (F (getOrd_tot i0)) (F i)].
    Proof.
      case: (andP (getOrd_minimalIn i0 (enum I)))=> H H2.
      apply/forallP=> x; apply/implyP=> H3.
      suff H4: false by [].
      apply: H3; move: (forallP H2 x); move/implyP; apply.
      by rewrite mem_enum.
    Qed.

    Definition getOrd_sub i0 := getOrd i0 (filter P (enum I)).

    Lemma getOrd_sub_hasP i0 (Hi0 : P i0) : P (getOrd_sub i0).
    Proof.
      rewrite /getOrd_sub; move: (enum I)=> l.
      elim: l=> // a l /=.
      case H: (P a)=> //=.                   
      case: (ord _ _)=> //.                      
      elim: l a H i0 Hi0 => //= a0 l IH a H i0 Hi0.
      case H2: (P a0)=> //=.
      case: (ord _ _).
      case: (ord _ _)=> //.
      by apply: IH.
      by apply: IH.
      case: (ord _ _)=> //.
      by apply: IH.
      by apply: IH.
    Qed.        
      
    Lemma getOrd_subP i0 (Hi0 : P i0) :
      [&& P (getOrd_sub i0)
        & [forall (i | P i), ord (F (getOrd_sub i0)) (F i)]].
    Proof.
      case: (andP (getOrd_minimalIn i0 (filter P (enum I))))=> H H2.
      apply/andP; split; first by apply: getOrd_sub_hasP.
      apply/forallP=> x; apply/implyP=> H3.
      move: (forallP H2 x); move/implyP; apply.
      by rewrite mem_filter; apply/andP; split=> //; rewrite mem_enum.
    Qed.
  End getOrd.

  Section default.
    Variable i0 : I.
    Hypothesis H : P i0.
  
    Definition arg_max := getOrd_sub ger i0.
  
    Lemma arg_maxP : [&& P arg_max & [forall (i | P i), F arg_max >= F i]].
    Proof.
      apply: getOrd_subP=> //; rewrite /ger.
      by apply: lerr.
      by move=> x y z /= H2 H3; apply: (ler_trans H3 H2).
      by move=> x y /=; move: (ler_total x y); rewrite orbC.
    Qed.

    Definition max := F arg_max.

    Lemma maxP : [forall (i | P i), max >= F i].
    Proof.
      rewrite /max.
      by case: (andP arg_maxP).
    Qed.      
    
    Definition arg_min := getOrd_sub ler i0.

    Lemma arg_minP : [&& P arg_min & [forall (i | P i), F arg_min <= F i]].
    Proof.
      apply: getOrd_subP=> //.
      by apply: ler_trans.                           
      by apply: ler_total.
    Qed.

    Definition min := F arg_min.

    Lemma minP : [forall (i | P i), min <= F i].
    Proof.
      rewrite /min.
      by case: (andP arg_minP).
    Qed.      
  
    Lemma min_le_max : min <= max.
    Proof.
      rewrite /min /max.
      case: (andP arg_minP)=> H2; move/forallP=> H3.
      case: (andP arg_maxP)=> H4; move/forallP=> H5.
      move: (implyP (H3 i0)); move/(_ H)=> Hx.
      move: (implyP (H5 i0)); move/(_ H)=> Hy.
      apply: ler_trans.
      apply: Hx.
      apply: Hy.
    Qed.
  End default.
End Extrema.

Arguments arg_min [rty I] P F i0.
Arguments arg_max [rty I] P F i0.

Arguments arg_minP [rty I P] F [i0] _.
Arguments arg_maxP [rty I P] F [i0] _.

Arguments min [rty I] P F i0.
Arguments max [rty I] P F i0.

Arguments minP [rty I P] F [i0] _.
Arguments maxP [rty I P] F [i0] _.

Arguments min_le_max [rty I P] F [i0] _.

Lemma max_ge (rty : realFieldType) (I : finType) (f : I -> rty) (def i : I) :
  f i <= max xpredT f def.
Proof.
  have H: xpredT i by [].
  move: (forallP (@maxP rty I xpredT f def H)); move/(_ i).
  by move/implyP; apply.
Qed.

Lemma min_le (rty : realFieldType) (I : finType) (f : I -> rty) (def i : I) :
  min xpredT f def <= f i.
Proof.
  have H: xpredT i by [].
  move: (forallP (@minP rty I xpredT f def H)); move/(_ i).
  by move/implyP; apply.
Qed.

Section min_lems.
  Variables (rty : realFieldType) (I : finType).

  Lemma arg_min_ext (p1 p2 : pred I) (f g : I -> rty) d1 d2 :
    p1 =1 p2 -> 
    f =1 g ->
    d1 = d2 -> 
    arg_min p1 f d1 = arg_min p2 g d2 .
  Proof.
    move => H1 H2 ->.
    rewrite /arg_min/getOrd_sub.
    have ->:
     [seq x <- enum I | p1 x] =
     [seq x <- enum I | p2 x].
     { rewrite (eq_in_filter (a2:=p2)) => //. }
     move: ([seq x <- _ | _]) d2; elim => // a l /= IH.
     move => d2; rewrite !H2; case: (_ <= _) => //. 
  Qed.
  
  Lemma min_ext (p1 p2 : pred I) (f g : I -> rty) d1 d2 :
    p1 =1 p2 -> 
    f =1 g ->
    d1 = d2 -> 
    min p1 f d1 = min p2 g d2 .
  Proof.
    move => H1 H2 ->; rewrite /min.
    have ->: arg_min p1 f d2 = arg_min p2 g d2 by apply: arg_min_ext.
    by apply: H2.
  Qed.

  Lemma ler_const_inv (c x y : rat) :
    0 < c ->    
    ((c * x <= c * y) = (x <= y)).
  Proof.
    move => Hpos; rewrite -(ler_pdivl_mull _ _ Hpos) mulrA mulVf.
    { by rewrite mul1r. }
    by apply/eqP => H; rewrite H in Hpos.
  Qed.    

  Lemma arg_min_const (p : pred I) (f : I -> rat) (c : rat) d :
    0 < c -> 
    arg_min p (fun x => c * f x) d = arg_min p f d.
  Proof.
    move => Hpos; rewrite /arg_min/getOrd_sub.
    move: ([seq x <- enum I | p x]) d; elim => // a l IH /= d.
    rewrite (ler_const_inv _ _ Hpos). case: (f d <= f a) => //.
  Qed.    
  
  Lemma min_const (p : pred I) (f : I -> rat) (c : rat) d :
    0 < c -> 
    min p (fun x => c * f x) d = c * min p f d.
  Proof.
    move => Hpos; rewrite /min; f_equal.
    rewrite arg_min_const //.
  Qed.    
End min_lems.    

Local Open Scope Numeric_scope.
Delimit Scope Numerics_scope with Num.

Section use_Numerics.
  Context (Nt:Type) `{Numerics.Numeric Nt}.
  
    Fixpoint num_list_max (l : list Nt) : option Nt :=
      match l with
      | nil => None
      | x :: l' => 
        match num_list_max l' with
        | None => Some x
        | Some x' =>
          Some (if Numerics.leb x x' then x' else x)
        end
    end.

    Definition num_list_max_default (l : list Nt) (def : Nt) : Nt :=
    match num_list_max l with
    | None => def
    | Some x => x
    end.
    

    Fixpoint num_argmax {T : Type} (l : list T) (f : T -> Nt) : option T :=
    match l with
    | nil => None
    | x :: l' =>
      (match num_argmax l' f with
      | None => Some x
      | Some x' =>
        Some (if Numerics.leb (f x) (f x') then x' else x)
      end)
    end.

    Definition num_argmax_default {T : Type} (l : list T) (f : T -> Nt) (def : T) : T :=
    match num_argmax l f with
    | None => def
    | Some x => x
    end.


    Definition num_nonempty_argmax {T : Type} (l : list T) (f : T-> Nt) (h: O <> (length l)) : T.
      destruct l.
      { simpl in h. exfalso. auto. }
      destruct (num_argmax (t :: l) f) eqn:e.
      { exact t0. }
      simpl in e.
      destruct (num_argmax l f); inversion e.
    Defined.


    Fixpoint num_mapmax {T : Type} (l : list T) (f : T->Nt) : option Nt :=
    match l with
    | nil => None
    | x :: l' => match num_mapmax l' f with
        | None => Some (f x)
        | Some x' => Some (if Numerics.leb x' (f x) then (f x) else x')
        end
    end.

    Lemma num_nonempty_argmax_ok: forall {T : Type} (l : list T) (f : T-> Nt) (h : O <> (length l)),
          (num_argmax l f) = Some (num_nonempty_argmax f h).
  Proof.
      intros.
      destruct l.
      { exfalso. apply h. auto.  }
      destruct l; auto.
      simpl in *.
      destruct (num_argmax l f); auto.
    Qed.

    Definition num_nonempty_max (l : list Nt) (h : O <> (length l)) : Nt.
      destruct l.
      { exfalso;  auto. }
      destruct (num_list_max (n ::l)) eqn:e.
      { exact n0. }
      simpl in e.
      destruct (num_list_max l); inversion e.
    Defined.

     Definition num_nonempty_mapmax (T : Type) (l : list T) (f : T->Nt)  (h : O <> (length l)) : Nt.
      destruct l.
      { exfalso;  auto. }
      destruct (num_mapmax (t ::l) f) eqn:e.
      { exact n. }
      simpl in e.
      destruct (num_mapmax l f); inversion e.
    Defined.

    Lemma num_nonempty_mapmax_ok: forall (T : Type) (l : list T) (f : T->Nt) (h : O <> (length l)), num_mapmax l f = Some (num_nonempty_mapmax f h).
    Proof.
      intros.
      destruct l.
      { exfalso. apply h; auto. }
      destruct l; auto.
      simpl.
      destruct (num_mapmax l f); auto.
    Qed.

    Lemma num_nonempty_max_ok: forall (l : list Nt) (h : O <> (length l)), num_list_max l = Some (num_nonempty_max h).
    Proof.
      intros.
      destruct l.
      { exfalso. apply h. auto. }
      destruct l; auto.
      simpl.
      destruct (num_list_max l); auto.
    Qed.
    
    Lemma argmax_mapmax: forall (T : Type) (l : list T) (f : T -> Nt), O <> length l ->
       (exists x, num_argmax l f = Some x /\  Some (f x) = num_mapmax l f).
    Proof.
      intros.
      induction l.
      { exfalso. apply H0. auto. }
      simpl in *.
      destruct l.
      { simpl. exists a. split; auto. } 
      destruct IHl; simpl; auto.
      destruct H1.
      simpl in *.
      destruct (num_argmax l f) eqn:e.
      {
        inversion H1.
        rewrite H4.
        exists (if Numerics.leb (f a) (f x) then x else a).
        split; auto.
        inversion H2.   
        destruct (Numerics.leb (f a) (f x)) eqn:e2.
        {
          apply Numerics.leb_true_iff in e2.
          rewrite <- Numerics.le_lt_or_eq in e2.
          destruct e2.
          {
            apply Numerics.lt_not_le in H3.
            apply Numerics.leb_false_iff in H3.
            rewrite H3.
            auto.
          }
          rewrite H3.
          destruct (Numerics.leb (f x) (f x)); auto.
      }
      apply Numerics.leb_false_iff in e2.
      apply Numerics.not_le_lt in e2.
      apply Numerics.le_lt_weak in e2.
      apply Numerics.leb_true_iff in e2.
      rewrite e2.
      auto.
    }
    exists (if Numerics.leb (f a) (f t) then t else a).
    split; auto.
    inversion H1.
    destruct (num_mapmax l f) eqn:e2.
    {
      inversion H2.
      destruct Numerics.lt_le_dec with (f t) n.
      {
        apply Numerics.lt_not_le in l0.
        apply Numerics.leb_false_iff in l0.
        rewrite l0 in H5.
        rewrite <- H5.
        assert ((if Numerics.leb (f x) (f x) then f x else f x) = f x).
        { destruct (Numerics.leb (f x) (f x) ); auto. }
        rewrite H3.
        destruct Numerics.lt_le_dec with (f a) (f x).
        {
          apply Numerics.lt_not_le in l1.
          apply Numerics.leb_false_iff in l1.
          rewrite l1.
          apply Numerics.leb_false_iff in l1.
          apply Numerics.not_le_lt in l1.
          apply Numerics.le_lt_weak in l1.
          apply Numerics.leb_true_iff in l1.
          rewrite l1.
          auto.
        }
        apply Numerics.leb_true_iff in l1.
        rewrite l1.
        apply Numerics.leb_true_iff in l1.
        apply Numerics.le_lt_or_eq in l1.
        destruct l1.
        {
          apply Numerics.lt_not_le in H6.
          apply Numerics.leb_false_iff in H6.
          rewrite H6.
          auto.
        }
        destruct (Numerics.leb (f a) (f x) ); auto.
        rewrite H6; auto.
      }
      rewrite H4 in l0.
      apply Numerics.leb_true_iff in l0.
      rewrite l0.
      destruct Numerics.lt_le_dec with (f a) (f x).
      {
        apply Numerics.lt_not_le in l1.
        apply Numerics.leb_false_iff in l1.
        rewrite l1.
        apply Numerics.leb_false_iff in l1.
        apply Numerics.not_le_lt in l1.
        apply Numerics.le_lt_weak in l1.
        apply Numerics.leb_true_iff in l1.
        rewrite l1.
        auto.
      }
      apply Numerics.le_lt_or_eq in l1.
      destruct l1.
      {
        apply Numerics.lt_not_le in H3.
        apply Numerics.leb_false_iff in H3.
        rewrite H3.
        apply Numerics.leb_false_iff in H3.
        apply Numerics.not_le_lt in H3.
        apply Numerics.le_lt_weak in H3.
        apply Numerics.leb_true_iff in H3.
        rewrite H3.
        auto.
      }
      rewrite H3.
      destruct (Numerics.leb (f a) (f a)); auto.
      rewrite H3; auto.
    }
    destruct Numerics.lt_le_dec with (f a) (f x).
    {
      apply Numerics.lt_not_le in l0.
      apply Numerics.leb_false_iff in l0.
      rewrite l0.
      apply Numerics.leb_false_iff in l0.
      apply Numerics.not_le_lt in l0.
      apply Numerics.le_lt_weak in l0.
      apply Numerics.leb_true_iff in l0.
      rewrite l0.
      auto.
    }
    apply Numerics.le_lt_or_eq in l0.
    destruct l0.
    {
      apply Numerics.lt_not_le in H3.
      apply Numerics.leb_false_iff in H3.
      rewrite H3.
      apply Numerics.leb_false_iff in H3.
      apply Numerics.not_le_lt in H3.
      apply Numerics.le_lt_weak in H3.
      apply Numerics.leb_true_iff in H3.
      rewrite H3.
      auto.
    }
    rewrite H3.
    destruct (Numerics.leb (f a) (f a)); auto.
    rewrite H3; auto.
  Qed.


    Lemma nonempty_argmax_mapmax: forall (T : Type) (l : list T) (f : T -> Nt) (h : O <> length l),
       num_nonempty_mapmax f h = f (num_nonempty_argmax f h).
    Proof.
      intros.
      destruct argmax_mapmax with T l f; auto.
      destruct H0.
      rewrite num_nonempty_argmax_ok in H0.
      inversion H0.
      rewrite H3.
      rewrite num_nonempty_mapmax_ok in H1.
      inversion H1.
      auto. 
    Qed.

    (**Lemma nonempty_argmax_mapmax': forall (T : Type) (l : list T) (f g: T -> Nt) (h : O <> length l),
       (forall (t1 t2 : T), f t1 <= f t2 <-> g t1 <= g t2) ->
       num_nonempty_mapmax f h = g (num_nonempty_argmax f h).
    Proof.
      intros.**)
      
    Lemma num_mapmax_ext: forall (T : Type) (f g : T->Nt) (l : list T), (forall x : T, f x = g x) -> num_mapmax l f = num_mapmax l g.
    Proof.
      intros.
      induction l; auto.
      simpl.
      rewrite IHl.
      rewrite H0.
      auto.
    Qed.
    
    Lemma num_argmax_ext: forall (T : Type) (f g : T->Nt) (l : list T), (forall x : T, f x = g x) -> num_argmax l f = num_argmax l g.
    Proof.
      intros.
      induction l; auto.
      simpl.
      rewrite IHl.
      repeat rewrite H0.
      destruct (num_argmax l g); auto.
      repeat rewrite H0.
      auto.
    Qed.

    Lemma num_argmax_ext': forall (T : Type) (f g : T->Nt) (l : list T), (forall x y: T, f x <= f y <-> g x <= g y) -> num_argmax l f = num_argmax l g.
    Proof.
      intros.
      induction l; auto.
      simpl.
      rewrite IHl.
      destruct (num_argmax l g); auto.
      destruct Numerics.total_order_T with (f a) (f t).
      { 
        destruct s.
        {
          apply Numerics.le_lt_weak in l0.
          assert (Numerics.leb (f a) (f t) ).
            apply Numerics.leb_true_iff. auto.
          apply H0 in l0.
          apply Numerics.leb_true_iff in l0.
          rewrite l0.
          rewrite H1.
          auto.
        }
        rewrite e.
        rewrite Numerics.leb_refl.
        assert (f a <= f t). { unfold Numerics.le. auto. }
        apply H0 in H1.
        apply Numerics.leb_true_iff in H1.
        rewrite H1.
        auto.
      }
      assert ( ~ f a <= f t).
        apply Numerics.lt_not_le. auto.
      assert ( ~ g a <= g t).
        unfold not.  intros. apply H1. apply H0. auto.
      apply Numerics.leb_false_iff in H1.
      apply Numerics.leb_false_iff in H2.
      rewrite H1.
      rewrite H2.
      auto.
    Qed.

    Lemma num_nonempty_mapmax_ext: forall (T : Type) (f g : T->Nt) (l : list T)  (H : O <> length l), (forall x : T, f x = g x) -> num_nonempty_mapmax f H = num_nonempty_mapmax g H.
    Proof.
      intros.
      assert (num_mapmax l f = Some (num_nonempty_mapmax f H0)).
        apply num_nonempty_mapmax_ok.
      assert (num_mapmax l g = Some (num_nonempty_mapmax g H0)).
        apply num_nonempty_mapmax_ok.
      assert ( num_mapmax l f = num_mapmax l g).
        apply num_mapmax_ext. auto.
      rewrite H2 in H4.
      rewrite H3 in H4.
      inversion H4.
      auto.
    Qed.

    Lemma num_nonempty_argmax_ext: forall (T : Type) (f g : T->Nt) (l : list T) (H : O <> length l), (forall x : T, f x = g x) -> num_nonempty_argmax f H = num_nonempty_argmax g H.
    Proof.
      intros.
      assert (num_argmax l f = Some (num_nonempty_argmax f H0)).
        apply num_nonempty_argmax_ok.
      assert (num_argmax l g = Some (num_nonempty_argmax g H0)).
        apply num_nonempty_argmax_ok.
      assert ( num_argmax l f = num_argmax l g).
        apply num_argmax_ext. auto.
      rewrite H2 in H4.
      rewrite H3 in H4.
      inversion H4.
      auto.
    Qed.

    Lemma num_nonempty_argmax_ext': forall (T : Type) (f g : T->Nt) (l : list T) (H : O <> length l), (forall x y: T, f x <= f y <-> g x <= g y) -> num_nonempty_argmax f H = num_nonempty_argmax g H.
    Proof.
      intros.
      assert (num_argmax l f = Some (num_nonempty_argmax f H0)).
        apply num_nonempty_argmax_ok.
      assert (num_argmax l g = Some (num_nonempty_argmax g H0)).
        apply num_nonempty_argmax_ok.
      assert ( num_argmax l f = num_argmax l g).
        apply num_argmax_ext'. auto.
      rewrite H2 in H4.
      rewrite H3 in H4.
      inversion H4.
      auto.
    Qed.
      
    

    Lemma num_argmax_plus_const_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt), num_argmax l f = num_argmax l (fun n => f n + x).
    Proof.
      intros.
      apply num_argmax_ext'.
      intros.
      split; intros.
      { apply Numerics.plus_le_compat; auto. apply Numerics.le_refl. }
      apply Numerics.plus_le_compat_l with (-x) (f x0 + x) (f y + x) in H0.
      rewrite -> Numerics.plus_comm with (f x0) x in H0.
      rewrite -> Numerics.plus_comm with (f y) x in H0.
      repeat rewrite Numerics.plus_assoc in H0.
      rewrite Numerics.plus_neg_l in H0.
      repeat rewrite Numerics.plus_id_l in H0.
      auto.
    Qed.
      

    Lemma num_argmax_plus_const_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt), num_argmax l f = num_argmax l (fun n => x + f n).
    Proof.
      intros.
      apply num_argmax_ext'.
      intros.
      split; intros.
      { apply Numerics.plus_le_compat; auto. apply Numerics.le_refl. }
      apply Numerics.plus_le_compat_l_reverse in H0.
      auto.
    Qed.
    
    Lemma num_argmax_mult_pos_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt), 0 < x -> num_argmax l f = num_argmax l (fun n => f n * x).
    Proof.
      intros.
      apply num_argmax_ext'.
      intros.
      split; intros.
      { apply Numerics.mult_le_compat_r; auto. apply Numerics.le_lt_weak. auto. }
      apply Numerics.mult_le_compat_r_reverse in H1; auto.
    Qed.

    Lemma num_argmax_mult_pos_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt), 0 < x -> num_argmax l f = num_argmax l (fun n => x * f n).
    Proof.
      intros.
      apply num_argmax_ext'.
      intros.
      split; intros.
      { apply Numerics.mult_le_compat_l; auto. apply Numerics.le_lt_weak. auto. }
      apply Numerics.mult_le_compat_l_reverse in H1; auto.
    Qed.
    

    Lemma num_nonempty_argmax_mult_pos_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), 0 < x -> num_nonempty_argmax f H = num_nonempty_argmax (fun n => f n * x) H.
    Proof.
      intros.
      assert(num_argmax l f = Some (num_nonempty_argmax f H0) ).
        apply num_nonempty_argmax_ok.
      assert(num_argmax l (fun n : T => f n * x) = Some (num_nonempty_argmax (fun n : T => f n * x) H0) ).
        apply num_nonempty_argmax_ok.
     rewrite <- num_argmax_mult_pos_r in H3; auto.
     rewrite H2 in H3.
     inversion H3.
     auto.
    Qed.
    
    Lemma num_nonempty_argmax_mult_pos_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), 0 < x -> num_nonempty_argmax f H = num_nonempty_argmax (fun n => x * f n) H.
    Proof.
      intros.
      assert(num_argmax l f = Some (num_nonempty_argmax f H0) ).
        apply num_nonempty_argmax_ok.
      assert(num_argmax l (fun n : T => x * f n) = Some (num_nonempty_argmax (fun n : T => x * f n) H0) ).
        apply num_nonempty_argmax_ok.
     rewrite <- num_argmax_mult_pos_l in H3; auto.
     rewrite H2 in H3.
     inversion H3.
     auto.
    Qed.
    
    Lemma num_mapmax_const: forall (T : Type) (l : list T) (x : Nt), (O <> length l) -> num_mapmax l (fun _ => x) = Some x.
    Proof.
      intros.
      induction l; auto.
      { exfalso. apply H0; auto. }
      simpl in *.
      destruct l; auto.
      simpl in *.
      rewrite IHl; auto.
      destruct  (Numerics.leb x x); auto.
    Qed.
    
    Lemma num_nonempty_mapmax_const: forall (T : Type) (l : list T) (x : Nt) (H : O <> length l), num_nonempty_mapmax (fun _ => x) H = x.
    Proof.
      intros.
      assert(num_mapmax l (fun _ : T => x) = Some (num_nonempty_mapmax (fun _ : T => x) H0)).
        apply num_nonempty_mapmax_ok.
      assert (num_mapmax l (fun _ : T => x) = Some x).
        apply num_mapmax_const; auto.
      rewrite H1 in H2.
      inversion H2.
      rewrite H4.
      auto.
    Qed.

    Lemma num_nonempty_mapmax_mult_pos_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), 0 <= x -> num_nonempty_mapmax f H * x= num_nonempty_mapmax (fun n => f n * x) H.
    Proof.
      intros.
      destruct H1.
      2: {
        rewrite <- H1. rewrite Numerics.mult_plus_id_r.
        assert  (num_nonempty_mapmax (l:=l) (fun n : T => f n * 0) H0 = num_nonempty_mapmax (l:=l) (fun n : T => 0) H0).
        { apply num_nonempty_mapmax_ext. intros. apply Numerics.mult_plus_id_r. }
        rewrite H2.
        rewrite num_nonempty_mapmax_const.
        auto.
      }
      repeat rewrite nonempty_argmax_mapmax.
      rewrite <- num_nonempty_argmax_mult_pos_r; auto.
    Qed.

    Lemma num_nonempty_mapmax_mult_pos_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), 0 <= x -> x * num_nonempty_mapmax f H = num_nonempty_mapmax (fun n => x * f n) H.
    Proof.
      intros.
      destruct H1.
      2: {
        rewrite <- H1. rewrite Numerics.mult_plus_id_l.
        assert  (num_nonempty_mapmax (l:=l) (fun n : T => 0 * f n ) H0 = num_nonempty_mapmax (l:=l) (fun n : T => 0) H0).
        { apply num_nonempty_mapmax_ext. intros. apply Numerics.mult_plus_id_l. }
        rewrite H2.
        rewrite num_nonempty_mapmax_const.
        auto.
      }
      repeat rewrite nonempty_argmax_mapmax.
      rewrite <- num_nonempty_argmax_mult_pos_l; auto.
    Qed.
    

    Lemma num_nonempty_argmax_plus_const_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), num_nonempty_argmax f H = num_nonempty_argmax (fun n => f n + x) H.
    Proof.
      intros.
      apply num_nonempty_argmax_ext'.
      intros.
      split; intros.
      { apply Numerics.plus_le_compat_r. auto. }
      apply Numerics.plus_le_compat_r_reverse in H1.
      auto.
    Qed.

    Lemma num_nonempty_mapmax_plus_const_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), num_nonempty_mapmax f H + x= num_nonempty_mapmax (fun n => f n + x) H.
    Proof.
      intros.
      rewrite nonempty_argmax_mapmax.
      rewrite nonempty_argmax_mapmax.
      rewrite <- num_nonempty_argmax_plus_const_r; auto.
    Qed.
    
    Lemma num_nonempty_argmax_plus_const_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), num_nonempty_argmax f H = num_nonempty_argmax (fun n => x + f n) H.
    Proof.
      intros.
      apply num_nonempty_argmax_ext'.
      intros.
      split; intros.
      { apply Numerics.plus_le_compat_l. auto. }
      apply Numerics.plus_le_compat_l_reverse in H1.
      auto.
    Qed.

    Lemma num_nonempty_mapmax_plus_const_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), x + num_nonempty_mapmax f H = num_nonempty_mapmax (fun n => x + f n) H.
    Proof.
      intros.
      rewrite nonempty_argmax_mapmax.
      rewrite nonempty_argmax_mapmax.
      rewrite <- num_nonempty_argmax_plus_const_l; auto.
    Qed.

    Lemma num_mapmax_list_max_map: forall (T : Type) (l : list T) (f : T->Nt), num_mapmax l f = num_list_max (map f l).
    Proof.
      intros.
      induction l; auto.
      simpl.
      rewrite IHl.
      destruct (num_list_max [seq f i | i <- l]); auto.
      destruct Numerics.total_order_T with  (f a) n.
      {
        destruct s.
        2: { rewrite e; auto. }
        assert (Numerics.leb (f a) n). 
        { apply Numerics.leb_true_iff. apply Numerics.le_lt_weak; auto. }
        rewrite H0.
        assert (Numerics.leb n (f a) = false).
        { apply Numerics.leb_false_iff. apply Numerics.lt_not_le. auto. }
        rewrite H1; auto.
      }
      assert (Numerics.leb n (f a)). 
      { apply Numerics.leb_true_iff. apply Numerics.le_lt_weak; auto. }
      assert (Numerics.leb (f a) n = false).
      { apply Numerics.leb_false_iff. apply Numerics.lt_not_le. auto. }
      rewrite H0. rewrite H1.
      auto.
    Qed.

    Lemma num_list_max_correct: forall (l : list Nt) (n : Nt), List.In n l -> (exists m, Some m = num_list_max l /\ n <= m).
    Proof.
      intros.
      induction l.
      { inversion H0. }
      simpl in *.
      destruct H0.
      {
        destruct l.
        {
          simpl.
          exists a.
          split; auto.
          rewrite H0.
          apply Numerics.le_refl.
        }
        rewrite H0.
        destruct (num_list_max (n0 :: l)) eqn:H1.
        {
          exists (if Numerics.leb n n1 then n1 else n).
          split; auto.
          destruct (Numerics.leb n n1) eqn:e2.
          { apply Numerics.leb_true_iff. auto. }
          apply Numerics.le_refl.
        }
        exists n.
        split; auto.
        apply Numerics.le_refl.
      }
      destruct IHl; auto.
      destruct H1.
      rewrite <- H1.
      exists (if Numerics.leb a x then x else a).
      split; auto.
      destruct (Numerics.leb a x) eqn:H3; auto.
      apply Numerics.leb_false_iff in H3.
      apply Numerics.not_le_lt in H3.
      apply Numerics.le_lt_weak.
      apply Numerics.le_lt_trans with x; auto.
    Qed.


    Lemma num_nonempty_max_correct: forall (l : list Nt) (n : Nt) (H : O <> length l), List.In n l ->   n <= num_nonempty_max H.
    Proof.
      intros.
      assert (num_list_max l = Some ( num_nonempty_max H0)).
      { apply num_nonempty_max_ok. }
      assert (exists m, Some m = num_list_max l /\ n <= m).
      { apply num_list_max_correct.  auto. } 
      destruct H3.
      destruct H3.
      rewrite H2 in H3.
      inversion H3.
      rewrite <- H6; auto.
    Qed.

    Lemma num_nonempty_mapmax_correct: forall (T : Type) (l : list T) (f : T->Nt) (H : O <> length l) (x : T), List.In x l -> (f x) <= num_nonempty_mapmax f H.
    Proof.
      intros.
      assert(num_mapmax l f = Some (num_nonempty_mapmax f H0)).
      { apply num_nonempty_mapmax_ok. }
      rewrite num_mapmax_list_max_map in H2.
      assert(O <> length  [seq f i | i <- l]).
      { rewrite List.map_length. auto. }
      assert(num_list_max [seq f i | i <- l] = Some (num_nonempty_max  H3)).
      { apply num_nonempty_max_ok. }
      rewrite H2 in H4.
      inversion H4.
      rewrite H6.
      apply num_nonempty_max_correct.
      apply List.in_map.
      auto.
    Qed.
   
End use_Numerics.

