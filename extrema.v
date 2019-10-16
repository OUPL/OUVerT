Set Implicit Arguments.
Unset Strict Implicit.

Require Import Reals.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import OUVerT.numerics.

Local Open Scope ring_scope.
Import OUVerT.numerics.Numerics.

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

Module num_Extrema.

  Section use_Numerics.

  Context (Nt:Type) `{Numeric Nt}.

    

    Fixpoint max (l : list Nt) : option Nt :=
      match l with
      | List.nil => None
      | x :: l' => 
        match max l' with
        | None => Some x
        | Some x' =>
          Some (if leb x x' then x' else x)
        end
    end.

    Definition max_default (l : list Nt) (def : Nt) : Nt :=
    match max l with
    | None => def
    | Some x => x
    end.
    

    Fixpoint argmax {T : Type} (l : list T) (f : T -> Nt) : option T :=
    match l with
    | List.nil => None
    | x :: l' =>
      (match argmax l' f with
      | None => Some x
      | Some x' =>
        Some (if leb (f x) (f x') then x' else x)
      end)
    end.

    Definition argmax_default {T : Type} (l : list T) (f : T -> Nt) (def : T) : T :=
    match argmax l f with
    | None => def
    | Some x => x
    end.


    Definition argmax_ne {T : Type} (l : list T) (f : T-> Nt) (h: O <> (length l)) : T.
      destruct l.
      { simpl in h. exfalso. auto. }
      destruct (argmax (t :: l) f) eqn:e.
      { exact t0. }
      simpl in e.
      destruct (argmax l f); inversion e.
    Defined.


    Fixpoint mapmax {T : Type} (l : list T) (f : T->Nt) : option Nt :=
    match l with
    | List.nil => None
    | x :: l' => match mapmax l' f with
        | None => Some (f x)
        | Some x' => Some (if leb (f x) x' then x' else (f x))
        end
    end.
    

    Lemma argmax_ne_ok: forall {T : Type} (l : list T) (f : T-> Nt) (h : O <> (length l)),
          (argmax l f) = Some (argmax_ne f h).
    Proof.
      intros.
      destruct l.
      { exfalso. apply h. auto.  }
      destruct l; auto.
      simpl in *.
      destruct (argmax l f); auto.
    Qed.

    Definition max_ne (l : list Nt) (h : O <> (length l)) : Nt.
      destruct l.
      { exfalso;  auto. }
      destruct (max (n ::l)) eqn:e.
      { exact n0. }
      simpl in e.
      destruct (max l); inversion e.
    Defined.

     Definition mapmax_ne (T : Type) (l : list T) (f : T->Nt)  (h : O <> (length l)) : Nt.
      destruct l.
      { exfalso;  auto. }
      destruct (mapmax (t ::l) f) eqn:e.
      { exact n. }
      simpl in e.
      destruct (mapmax l f); inversion e.
    Defined.




    Fixpoint nth_max (l : list Nt) (n : nat) : option Nt :=
    match n with
    | O => max l
    | S n' => 
      match (max l) with
      | None => None
      | Some m => nth_max (filter (fun x => ltb x m) l) n'
      end
    end.

      
      


    Lemma mapmax_ne_ok: forall (T : Type) (l : list T) (f : T->Nt) (h : O <> (length l)), mapmax l f = Some (mapmax_ne f h).
    Proof.
      intros.
      destruct l.
      { exfalso. apply h; auto. }
      destruct l; auto.
      simpl.
      destruct (mapmax l f); auto.
    Qed.

    Lemma max_ne_ok: forall (l : list Nt) (h : O <> (length l)), max l = Some (max_ne h).
    Proof.
      intros.
      destruct l.
      { exfalso. apply h. auto. }
      destruct l; auto.
      simpl.
      destruct (max l); auto.
    Qed.
    
    Lemma max_ne_some: forall (l : list Nt), O <> length l <-> exists x, max l = Some x.
    Proof.
      intros.
      split; intros.
      {
        destruct l.
        {
          simpl in *.
          exfalso.
          auto.
        }
        simpl.
        destruct (max l); eauto.
      }
      destruct l; simpl; auto.
      simpl in H0. inversion H0. inversion H1.
    Qed.

    Lemma argmax_ne_some: forall (T : Type) (l : list T) (f : T->Nt), O <> length l <-> exists x , argmax l f= Some x.
    Proof.
      intros.
      split; intros.
      {
        destruct l.
        {
          simpl in *.
          exfalso.
          auto.
        }
        simpl.
        destruct (argmax l); eauto.
      }
      destruct l; simpl; auto.
      simpl in H0. inversion H0. inversion H1.
    Qed.

    Lemma mapmax_map_max: forall (T : Type) (l : list T) (f : T-> Nt), mapmax l f = max (map f l).
    Proof.
      intros.
      induction l; auto.
      simpl.
      rewrite IHl.
      auto.
    Qed.


    Lemma mapmax_ne_some: forall (T : Type) (l : list T) (f : T->Nt), O <> length l <-> exists x , mapmax l f = Some x.
    Proof.
      intros.
      assert (forall (T : Type) (l : list T), length l = size l). auto.
      rewrite H0.
      rewrite mapmax_map_max.            
      rewrite <- size_map with T Nt f _.
      rewrite <- H0.
      apply max_ne_some.
    Qed.

    Lemma argmax_mapmax: forall (T : Type) (l : list T) (f : T -> Nt), O <> length l ->
       (exists x, argmax l f = Some x /\  Some (f x) = mapmax l f).
    Proof.
      intros.
      induction l.
      { exfalso. apply H0. auto. }
      simpl in *.
      destruct l.
      { simpl. exists a. split; auto. } 
      destruct IHl; simpl; auto.
      destruct H1.
      inversion H1.
      destruct (length l) eqn:e.
      { 
        rewrite -> List.length_zero_iff_nil in e. rewrite e; simpl.
        eexists. split; auto.
        destruct (leb (f a) (f t)); auto.
      }
      assert (O <> length l).
      { unfold not.  intros. rewrite e in H3. inversion H3. }
      assert (exists x', argmax l f = Some x').
        apply argmax_ne_some; auto.
      destruct H5.
      rewrite H5.
      assert (exists x', mapmax l f = Some x').
        apply mapmax_ne_some; auto.
      destruct H6.
      rewrite H6.
      eexists; split; auto.
      simpl in H1.
      simpl in H2.
      rewrite H5 in H1.
      rewrite H6 in H2.
      destruct (leb (f t) x1) eqn:e2.
      {
        inversion H2.
        rewrite <- H8 in e2.
        inversion H1.
        destruct (leb (f t) (f x0)).
          destruct (leb (f a) (f x0)); auto.
        destruct (leb (f a) (f t)); auto.
      }
      inversion H1.
      destruct (leb (f t) (f x0)) eqn:e3.
      {
        inversion H1.      
        inversion H2.
        destruct (leb (f a) (f x)); auto.
      }
      destruct (leb (f a) (f t)); auto.
    Qed.


    Lemma argmax_ne_mapmax_ne: forall (T : Type) (l : list T) (f : T -> Nt) (h : O <> length l),
       mapmax_ne f h = f (argmax_ne f h).
    Proof.
      intros.
      destruct argmax_mapmax with T l f; auto.
      destruct H0.
      rewrite argmax_ne_ok in H0.
      inversion H0.
      rewrite H3.
      rewrite mapmax_ne_ok in H1.
      inversion H1.
      auto. 
    Qed.
      
    Lemma mapmax_ext: forall (T : Type) (f g : T->Nt) (l : list T), (forall x : T, f x = g x) -> mapmax l f = mapmax l g.
    Proof.
      intros.
      induction l; auto.
      simpl.
      rewrite IHl.
      rewrite H0.
      auto.
    Qed.
    
    Lemma argmax_ext: forall (T : Type) (f g : T->Nt) (l : list T), (forall x : T, f x = g x) -> argmax l f = argmax l g.
    Proof.
      intros.
      induction l; auto.
      simpl.
      rewrite IHl.
      repeat rewrite H0.
      destruct (argmax l g); auto.
      repeat rewrite H0.
      auto.
    Qed.

    Lemma argmax_ext': forall (T : Type) (f g : T->Nt) (l : list T), (forall x y: T, f x <= f y <-> g x <= g y) -> argmax l f = argmax l g.
    Proof.
      intros.
      induction l; auto.
      simpl.
      rewrite IHl.
      destruct (argmax l g); auto.
      destruct total_order_T with (f a) (f t).
      { 
        destruct s.
        {
          apply le_lt_weak in l0.
          assert (leb (f a) (f t) ).
            apply leb_true_iff. auto.
          apply H0 in l0.
          apply leb_true_iff in l0.
          rewrite l0.
          rewrite H1.
          auto.
        }
        rewrite e.
        rewrite leb_refl.
        assert (f a <= f t). { unfold le. auto. }
        apply H0 in H1.
        apply leb_true_iff in H1.
        rewrite H1.
        auto.
      }
      assert ( ~ f a <= f t).
        apply lt_not_le. auto.
      assert ( ~ g a <= g t).
        unfold not.  intros. apply H1. apply H0. auto.
      apply leb_false_iff in H1.
      apply leb_false_iff in H2.
      rewrite H1.
      rewrite H2.
      auto.
    Qed.

    Lemma mapmax_ne_ext: forall (T : Type) (f g : T->Nt) (l : list T)  (H : O <> length l), (forall x : T, f x = g x) -> mapmax_ne f H = mapmax_ne g H.
    Proof.
      intros.
      assert (mapmax l f = Some (mapmax_ne f H0)).
        apply mapmax_ne_ok.
      assert (mapmax l g = Some (mapmax_ne g H0)).
        apply mapmax_ne_ok.
      assert ( mapmax l f = mapmax l g).
        apply mapmax_ext. auto.
      rewrite H2 in H4.
      rewrite H3 in H4.
      inversion H4.
      auto.
    Qed.

    Lemma argmax_ne_ext: forall (T : Type) (f g : T->Nt) (l : list T) (H : O <> length l), (forall x : T, f x = g x) -> argmax_ne f H = argmax_ne g H.
    Proof.
      intros.
      assert (argmax l f = Some (argmax_ne f H0)).
        apply argmax_ne_ok.
      assert (argmax l g = Some (argmax_ne g H0)).
        apply argmax_ne_ok.
      assert ( argmax l f = argmax l g).
        apply argmax_ext. auto.
      rewrite H2 in H4.
      rewrite H3 in H4.
      inversion H4.
      auto.
    Qed.

    Lemma argmax_ne_ext': forall (T : Type) (f g : T->Nt) (l : list T) (H : O <> length l), (forall x y: T, f x <= f y <-> g x <= g y) -> argmax_ne f H = argmax_ne g H.
    Proof.
      intros.
      assert (argmax l f = Some (argmax_ne f H0)).
        apply argmax_ne_ok.
      assert (argmax l g = Some (argmax_ne g H0)).
        apply argmax_ne_ok.
      assert ( argmax l f = argmax l g).
        apply argmax_ext'. auto.
      rewrite H2 in H4.
      rewrite H3 in H4.
      inversion H4.
      auto.
    Qed.

    Lemma argmax_plus_const_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt), argmax l f = argmax l (fun n => f n + x).
    Proof.
      intros.
      apply argmax_ext'.
      intros.
      split; intros.
      { apply plus_le_compat; auto. apply le_refl. }
      apply plus_le_compat_l with (-x) (f x0 + x) (f y + x) in H0.
      rewrite -> plus_comm with (f x0) x in H0.
      rewrite -> plus_comm with (f y) x in H0.
      repeat rewrite plus_assoc in H0.
      rewrite plus_neg_l in H0.
      repeat rewrite plus_id_l in H0.
      auto.
    Qed.
      

    Lemma argmax_plus_const_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt), argmax l f = argmax l (fun n => x + f n).
    Proof.
      intros.
      apply argmax_ext'.
      intros.
      split; intros.
      { apply plus_le_compat; auto. apply le_refl. }
      apply plus_le_compat_l_reverse in H0.
      auto.
    Qed.
    
    Lemma argmax_mult_pos_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt), 0 < x -> argmax l f = argmax l (fun n => f n * x).
    Proof.
      intros.
      apply argmax_ext'.
      intros.
      split; intros.
      { apply mult_le_compat_r; auto. apply le_lt_weak. auto. }
      apply mult_le_compat_r_reverse in H1; auto.
    Qed.

    Lemma argmax_mult_pos_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt), 0 < x -> argmax l f = argmax l (fun n => x * f n).
    Proof.
      intros.
      apply argmax_ext'.
      intros.
      split; intros.
      { apply mult_le_compat_l; auto. apply le_lt_weak. auto. }
      apply mult_le_compat_l_reverse in H1; auto.
    Qed.
    

    Lemma argmax_ne_mult_pos_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), 0 < x -> argmax_ne f H = argmax_ne (fun n => f n * x) H.
    Proof.
      intros.
      assert(argmax l f = Some (argmax_ne f H0) ).
        apply argmax_ne_ok.
      assert(argmax l (fun n : T => f n * x) = Some (argmax_ne (fun n : T => f n * x) H0) ).
        apply argmax_ne_ok.
     rewrite <- argmax_mult_pos_r in H3; auto.
     rewrite H2 in H3.
     inversion H3.
     auto.
    Qed.
    
    Lemma argmax_ne_mult_pos_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), 0 < x -> argmax_ne f H = argmax_ne (fun n => x * f n) H.
    Proof.
      intros.
      assert(argmax l f = Some (argmax_ne f H0) ).
        apply argmax_ne_ok.
      assert(argmax l (fun n : T => x * f n) = Some (argmax_ne (fun n : T => x * f n) H0) ).
        apply argmax_ne_ok.
     rewrite <- argmax_mult_pos_l in H3; auto.
     rewrite H2 in H3.
     inversion H3.
     auto.
    Qed.
    
    Lemma mapmax_const: forall (T : Type) (l : list T) (x : Nt), (O <> length l) -> mapmax l (fun _ => x) = Some x.
    Proof.
      intros.
      induction l; auto.
      { exfalso. apply H0; auto. }
      simpl in *.
      destruct l; auto.
      simpl in *.
      rewrite IHl; auto.
      destruct  (leb x x); auto.
    Qed.
    
    Lemma mapmax_ne_const: forall (T : Type) (l : list T) (x : Nt) (H : O <> length l), mapmax_ne (fun _ => x) H = x.
    Proof.
      intros.
      assert(mapmax l (fun _ : T => x) = Some (mapmax_ne (fun _ : T => x) H0)).
        apply mapmax_ne_ok.
      assert (mapmax l (fun _ : T => x) = Some x).
        apply mapmax_const; auto.
      rewrite H1 in H2.
      inversion H2.
      rewrite H4.
      auto.
    Qed.

    Lemma mapmax_ne_mult_pos_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), 0 <= x -> mapmax_ne f H * x= mapmax_ne (fun n => f n * x) H.
    Proof.
      intros.
      destruct H1.
      2: {
        rewrite <- H1. rewrite mult_plus_id_r.
        assert  (mapmax_ne (l:=l) (fun n : T => f n * 0) H0 = mapmax_ne (l:=l) (fun n : T => 0) H0).
        { apply mapmax_ne_ext. intros. apply mult_plus_id_r. }
        rewrite H2.
        rewrite mapmax_ne_const.
        auto.
      }
      repeat rewrite argmax_ne_mapmax_ne.
      rewrite <- argmax_ne_mult_pos_r; auto.
    Qed.

    Lemma mapmax_ne_mult_pos_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), 0 <= x -> x * mapmax_ne f H = mapmax_ne (fun n => x * f n) H.
    Proof.
      intros.
      destruct H1.
      2: {
        rewrite <- H1. rewrite mult_plus_id_l.
        assert  (mapmax_ne (l:=l) (fun n : T => 0 * f n ) H0 = mapmax_ne (l:=l) (fun n : T => 0) H0).
        { apply mapmax_ne_ext. intros. apply mult_plus_id_l. }
        rewrite H2.
        rewrite mapmax_ne_const.
        auto.
      }
      repeat rewrite argmax_ne_mapmax_ne.
      rewrite <- argmax_ne_mult_pos_l; auto.
    Qed.
    

    Lemma argmax_ne_plus_const_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), argmax_ne f H = argmax_ne (fun n => f n + x) H.
    Proof.
      intros.
      apply argmax_ne_ext'.
      intros.
      split; intros.
      { apply Numerics.plus_le_compat_r. auto. }
      apply Numerics.plus_le_compat_r_reverse in H1.
      auto.
    Qed.

    Lemma mapmax_ne_plus_const_r: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), mapmax_ne f H + x= mapmax_ne (fun n => f n + x) H.
    Proof.
      intros.
      repeat rewrite argmax_ne_mapmax_ne.
      rewrite <- argmax_ne_plus_const_r; auto.
    Qed.
    
    Lemma argmax_ne_plus_const_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), argmax_ne f H = argmax_ne (fun n => x + f n) H.
    Proof.
      intros.
      apply argmax_ne_ext'.
      intros.
      split; intros.
      { apply Numerics.plus_le_compat_l. auto. }
      apply Numerics.plus_le_compat_l_reverse in H1.
      auto.
    Qed.

    Lemma mapmax_ne_plus_const_l: forall (T : Type) (l : list T) (f : T -> Nt) (x : Nt) (H : O <> length l), x + mapmax_ne f H = mapmax_ne (fun n => x + f n) H.
    Proof.
      intros.
      repeat rewrite argmax_ne_mapmax_ne.
      rewrite <- argmax_ne_plus_const_l; auto.
    Qed.



    Lemma mapmax_ne_map_max_ne: forall (T : Type) (l : list T) (f : T->Nt) (H0 : O <> length l) (H1 : O <> length (map f l)),
         mapmax_ne f H0 = max_ne H1.
    Proof.
      intros.
      assert(mapmax l f = Some (mapmax_ne f H0)).
        apply mapmax_ne_ok.
      assert(max (map f l) = Some (max_ne H1)).
        apply max_ne_ok.
      rewrite <- mapmax_map_max in H3.
      rewrite H2 in H3.
      inversion H3.
      auto.
    Qed.
    
    Lemma max_correct: forall (l : list Nt) (n : Nt), List.In n l -> (exists m, Some m = max l /\ n <= m).
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
        destruct (max (n0 :: l)) eqn:H1.
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

    Lemma max_in: forall (l : list Nt) (x : Nt), max l = Some x -> List.In x l.
    Proof.
      intros. 
      induction l.
      { inversion H0. }
      simpl in *.
      destruct (max l) eqn:e.
      2: { inversion H0. auto. }       
      destruct (leb a n); auto.
      inversion H0. auto.
    Qed.

    Lemma nth_max_in: forall (l : list Nt) (n : nat) (x : Nt),
        nth_max l n = Some x -> List.In x l.
    Proof.
      intros.
      generalize dependent x.
      generalize dependent l.
      induction n; intros.
      {
        simpl in H0.
        apply max_in.
        auto.
      }
      simpl in H0.
      destruct (max l) eqn:e.
      2:{ inversion H0. }
      apply IHn in H0.
      apply List.filter_In in H0.
      destruct H0. auto.
    Qed.

    Lemma max_none: forall (l : list Nt), max l = None <-> l = [::].
    Proof.
      intros.
      split; intros.
      {
        destruct l; auto.
        simpl in H0.
        destruct (max l);
          inversion H0.
      }
      rewrite H0. auto.
    Qed.

    Lemma filter_none: forall {T : Type} (l : list T) (f : T->bool),
      filter f l = [::] <-> (forall x : T, List.In x l ->  f x = false).
    Proof. 
      intros.
      split; intros.
      {
        induction l.
        { inversion H1. }
        simpl in H0.
        destruct (f a) eqn:e.
          inversion H0.
        destruct H1; auto.
        rewrite <- H1. auto.
      }
      induction l; auto.
      simpl.
      rewrite H0; simpl; auto.
      apply IHl.
      simpl in H0.
      intros.
      destruct H0 with x; auto.
    Qed.

    Lemma second_max_none: forall (l : list Nt), nth_max l 1 = None ->
      (forall (x : Nt), List.In x l -> max l = Some x).
    Proof.
      intros.
      simpl in H0.
      destruct l.
      { inversion H1. }
      remember H1.
      clear Heqi.
      apply max_correct in i.
      destruct i.
      destruct H2.
      rewrite <- H2 in H0.
      destruct H3.
      2:{ rewrite H3. auto. }
      rewrite -> max_none in H0.
      rewrite -> filter_none in H0.
      apply ltb_true_iff in H3.
      apply H0 in H1.
      rewrite H1 in H3. inversion H3.
    Qed.

    Lemma second_max_some_max_some: forall (l : list Nt) (x : Nt), nth_max l 1 = Some x ->
      exists y : Nt, max l = Some y.
    Proof.
      intros.
      simpl in H0.
      destruct (max l) eqn:e; eauto.
    Qed.

    Lemma gt_second_max: forall (l : list Nt) (x y z: Nt), max l = Some x -> nth_max l 1 = Some y ->
      List.In z l -> y < z -> x = z.
    Proof.
      intros.
      simpl in *.
      destruct l.
      { inversion H2. }
      rewrite H0 in H1.
      remember H2. clear Heqi.
      apply max_correct in i.
      destruct i. destruct H4.
      rewrite H0 in H4. inversion H4.
      clear H4. rewrite H7 in H5.
      clear H7. clear x0.      
      destruct H5; auto.
      exfalso. apply lt_not_le with y z; auto.
      assert(List.In z ([seq x0 <- n :: l | ltb x0 x])).
        rewrite -> List.filter_In. split; auto. rewrite ltb_true_iff. auto.
      apply max_correct in H5. destruct H5. destruct H5. 
      rewrite H1 in H5. inversion H5. rewrite <- H8. auto.
    Qed.

    Lemma second_max_lt_max: forall (l : list Nt) (x y : Nt), max l = Some x ->
        nth_max l 1 = Some y -> y < x.
    Proof.
      intros.
      simpl in H1.
      destruct (max l) eqn:e.
      2:{ inversion H0. }
      inversion H0.
      rewrite H3 in H1. rewrite H3 in e.
      clear H3. clear H0. clear n.
      apply max_in in H1.
      apply List.filter_In in H1.
      destruct H1. apply ltb_true_iff.
      auto.
    Qed.
  
    Lemma exists_min_dist_to_max: forall (l : list Nt) (x : Nt), max l = Some x ->
       (exists e, 0 < e /\ (forall y : Nt, List.In y l -> abs (x + - y) < e -> x = y)).
    Proof.
      intros.
      destruct (nth_max l 1) eqn:eq.
      2:{ 
        exists 1. split. apply plus_id_lt_mult_id. intros.
        apply second_max_none with l y in eq; auto.
        rewrite H0 in eq. inversion eq. auto.
      }
      exists (x + - n).
      split.
      { 
        rewrite <- plus_neg_r with n.
        apply plus_lt_compat_r.
        apply second_max_lt_max with l; auto.
      }
      intros.
      rewrite abs_posb in H2.
      2:{ 
        apply leb_true_iff.
        rewrite <- plus_neg_r with y.
        apply plus_le_compat_r.
        apply max_correct in H1.
        destruct H1. destruct H1.
        rewrite H0 in H1. inversion H1. rewrite <- H4. auto.
      }
      apply gt_second_max with l n; auto.
      apply plus_lt_compat_l with (- x ) _ _ in H2.
      repeat rewrite plus_assoc in H2.
      repeat rewrite plus_neg_l in H2.
      repeat rewrite plus_id_l in H2.
      apply lt_neg in H2. auto.
    Qed.


    Lemma max_ne_correct: forall (l : list Nt) (n : Nt) (H : O <> length l), List.In n l ->   n <= max_ne H.
    Proof.
      intros.
      assert (max l = Some ( max_ne H0)).
      { apply max_ne_ok. }
      assert (exists m, Some m = max l /\ n <= m).
      { apply max_correct.  auto. } 
      destruct H3.
      destruct H3.
      rewrite H2 in H3.
      inversion H3.
      rewrite <- H6; auto.
    Qed.

    Lemma mapmax_ne_correct: forall (T : Type) (l : list T) (f : T->Nt) (H : O <> length l) (x : T), List.In x l -> (f x) <= mapmax_ne f H.
    Proof.
      intros.
      assert(mapmax l f = Some (mapmax_ne f H0)).
      { apply mapmax_ne_ok. }
      rewrite mapmax_map_max in H2.
      assert(O <> length  [seq f i | i <- l]).
      { rewrite List.map_length. auto. }
      assert(max [seq f i | i <- l] = Some (max_ne  H3)).
      { apply max_ne_ok. }
      rewrite H2 in H4.
      inversion H4.
      rewrite H6.
      apply max_ne_correct.
      apply List.in_map.
      auto.
    Qed.
      

    Lemma mapmax_ne_cons_le: forall (T : Type) (l : list T) (f : T -> Nt) (t : T) (H0 : O <> length l) (H1 : O <> length (t :: l)), 
          mapmax_ne f H0 <= mapmax_ne f H1.
    Proof.
      intros.
      assert(mapmax l f = Some (mapmax_ne f H0)).
        apply mapmax_ne_ok.
      assert(mapmax (t :: l) f = Some (mapmax_ne f H1)).
        apply mapmax_ne_ok.
      simpl mapmax in H3.
      rewrite H2 in H3.
      destruct (Numerics.leb (f t) (mapmax_ne  (l:=l) f H0)) eqn:e.
      {
        assert (mapmax_ne (l:=l) f H0 = mapmax_ne (l:=t :: l) f H1).
        { simpl in *. inversion H3. auto. }
        rewrite <- H4.
        apply Numerics.le_refl.
      }
      assert(f t = mapmax_ne (l:=t :: l) f H1).
      { simpl in *. inversion H3. auto. }
      rewrite <- H4.
      apply Numerics.leb_false_iff in e.
      apply not_le_lt in e.
      apply le_lt_weak.
      auto.
    Qed.

    Lemma max_ne_cons: forall (l : list Nt) (x : Nt) (H0 : O <> length l) (H1 : O <> length (x :: l)),
              (max_ne H0 = max_ne H1 /\ x <= max_ne H0) \/ (x = max_ne H1 /\  max_ne H0 <= x).
    Proof.
      intros.
      induction l; auto.
      { exfalso. apply H0. auto. }
      remember (max_ne (l:=a :: l) H0) as M_a.
      assert (max (a :: l) = Some M_a). rewrite HeqM_a. apply max_ne_ok.
      remember (max_ne (l:=[:: x, a & l]) H1) as M_xa.
      assert (max [:: x, a & l] = Some M_xa). rewrite HeqM_xa. apply max_ne_ok.
      simpl in H2,H3.
      rewrite H2 in H3.
      inversion H3.
      clear H3.
      destruct (max l) eqn:e.
      {
        inversion H2.
        clear H2.
        destruct (leb a n) eqn:e2.
        {
          destruct (leb x n) eqn:e3.
            apply leb_true_iff in e3. auto.
          apply leb_false_iff in e3.
          apply not_le_lt in e3.
          apply le_lt_weak in e3.
          auto.
        }
        destruct (leb x a) eqn:e3.
          apply leb_true_iff in e3. auto.
        apply leb_false_iff in e3.
        apply not_le_lt in e3.
        apply le_lt_weak in e3.
        auto.
      }
      destruct (leb x M_a) eqn:e2.
        apply leb_true_iff in e2. auto.
      apply leb_false_iff in e2.
      apply not_le_lt in e2.
      apply le_lt_weak in e2.
      auto.
    Qed.


    Lemma mapmax_ne_cons: forall (T : Type) (l : list T) (f : T -> Nt) (x : T) (H0 : O <> length l) (H1 : O <> length (x :: l)),
              (mapmax_ne f H0 = mapmax_ne f H1 /\ f x <= mapmax_ne f H0) \/ (f x = mapmax_ne f H1 /\ mapmax_ne f H0 <= f x ).
    Proof.
      intros.
      assert(forall (T : Type) (l : list T), length l = size l). auto.
      repeat (rewrite mapmax_ne_map_max_ne; intros;
        try (
          rewrite H2; rewrite size_map; auto
        )).
      apply max_ne_cons.
    Qed.

    Lemma max_ne_le_all: forall (l : list Nt) (H : O <> length l) (n : Nt), (forall n' : Nt, List.In n' l -> n <= n') -> n <= max_ne H.
    Proof.
      intros.
      induction l.
      { exfalso. apply H0. auto. }
      destruct l.
      { simpl. apply H1. simpl.  auto. }
      assert (O <> length (n0 :: l)). unfold not. intros. inversion H2.
      destruct max_ne_cons with (n0 :: l) a H2 H0; destruct H3.
      { rewrite <- H3. apply IHl. intros. apply H1. simpl in *. auto. }
      rewrite <- H3.
      apply H1.
      simpl.
      auto.
    Qed.

    Lemma mapmax_ne_le_all: forall (T : Type) (l : list T) (f : T -> Nt) (H : O <> length l) (n : Nt),
        (forall t : T, List.In t l -> n <= f t) -> n <= mapmax_ne f H.
    Proof. 
      intros.
      assert (mapmax l f = Some (mapmax_ne f H0)).
        apply mapmax_ne_ok.
      rewrite mapmax_map_max in H2.
      assert ( O <> length ([seq f i | i <- l])).
        unfold not. intros. apply H0. rewrite H3. apply List.map_length.
      assert (max ([seq f i | i <- l]) = Some (max_ne H3)).
        apply max_ne_ok.
      rewrite H2 in H4.
      inversion H4.
      rewrite H6.
      apply max_ne_le_all.
      intros.
      apply List.in_map_iff in H5.
      destruct H5.
      destruct H5.
      rewrite <- H5.
      apply H1; auto.
    Qed.

    Lemma mapmax_ne_le_ext: forall (T : Type) (l : list T) (f g: T -> Nt) (H : O <> length l), 
          (forall t : T, List.In t l -> f t <= g t) -> mapmax_ne f H <= mapmax_ne g H.
    Proof.
      intros.
      induction l.
      { exfalso. apply H0. auto. }
      destruct l.
        simpl. apply H1. simpl. auto.
      assert (O <> length (t :: l)). unfold not. intros. inversion H2.      
      destruct mapmax_ne_cons with T (t :: l) f a H2 H0.
      {
        destruct H3.
        rewrite <- H3.
        apply Numerics.le_trans with (mapmax_ne (l:=t :: l) g H2); auto.
        { apply IHl. intros. apply H1. simpl. auto. }
        apply mapmax_ne_cons_le.
      }
      destruct H3.
      rewrite <- H3.
      apply Numerics.le_trans with (g a).
      { apply H1. simpl. auto. }
      apply mapmax_ne_correct.
      simpl.
      auto.
    Qed.

    Lemma abs_mapmax_ne_le: forall (T : Type) (l : list T) (f: T -> Nt) (H : O <> length l), 
          Numerics.abs ( mapmax_ne f H) <= mapmax_ne (fun x => abs (f x)) H.
    Proof.
      intros.
      destruct (Numerics.leb 0 (mapmax_ne (l:=l) f H0)) eqn:e.
      {
        assert (Numerics.abs (mapmax_ne (l:=l) f H0) = (mapmax_ne (l:=l) f H0)).
        { unfold Numerics.abs. rewrite e. auto. }
        rewrite H1.
        apply mapmax_ne_le_ext.
        intros.
        apply Numerics.le_abs.
      }      
      assert (Numerics.abs (mapmax_ne (l:=l) f H0) = -mapmax_ne (l:=l) f H0).
        unfold Numerics.abs. rewrite e. auto.
      rewrite H1.
      apply Numerics.leb_false_iff in e.
      apply Numerics.not_le_lt in e.
      induction l.
      { exfalso. apply H0. auto. }
      destruct l.
      {
        apply Numerics.le_lt_weak in e.
        simpl.
        rewrite <- Numerics.abs_neg.
        apply Numerics.le_abs.
      }
      assert (O <> length (t :: l)).
        unfold not. intros. inversion H2.
      destruct  mapmax_ne_cons with T (t :: l) f a H2 H0.
      {
        destruct H3.
        rewrite <- H3.
        apply Numerics.le_trans with (mapmax_ne (l:=t :: l) (fun x : T => Numerics.abs (f x)) H2).
        { 
          apply IHl; auto.
          apply Numerics.le_lt_trans with (mapmax_ne (l:=[:: a, t & l]) f H0).
            apply mapmax_ne_cons_le. auto.
          assert (Numerics.leb 0 (mapmax_ne (l:=t :: l) f H2) = false).
          { apply Numerics.leb_false_iff. apply Numerics.lt_not_le.
            apply Numerics.le_lt_trans with (mapmax_ne (l:=[:: a, t & l]) f H0); auto.
            apply mapmax_ne_cons_le.
          }
          unfold Numerics.abs.
          rewrite H5.
          auto.
        }
        apply mapmax_ne_cons_le.
      }
      destruct H3.
      rewrite <- H3.
      apply Numerics.le_trans with (Numerics.abs (f a)).
      { rewrite <- Numerics.abs_neg. apply Numerics.le_abs. }
      remember ((fun x : T => Numerics.abs (f x))) as f'.      
      assert (Numerics.abs (f a) = f' a). rewrite Heqf'. auto.
      rewrite H5.
      apply mapmax_ne_correct.
      simpl. auto.
    Qed.

    Lemma mapmax_ne_plus_le: forall (T : Type) (l : list T) (f g : T->Nt) (H0 : O <> length l),
        mapmax_ne(fun x => f x + g x) H0 <= mapmax_ne f H0 + mapmax_ne g H0.
    Proof.
      intros.
      induction l.
      { exfalso.  apply H0. auto. }
      destruct l.
      { simpl. apply Numerics.le_refl. }
      assert(O <> length (t :: l)).
        unfold not. intros. inversion H1.
      destruct  mapmax_ne_cons with T (t :: l) (fun x : T => f x + g x) a H1 H0.
      { 
        destruct H2.
        rewrite <- H2.
        apply Numerics.le_trans with (mapmax_ne (l:=t :: l) f H1 + mapmax_ne(l:=t :: l) g H1); auto.
        apply Numerics.plus_le_compat; apply mapmax_ne_cons_le.
      }
      destruct H2.
      rewrite <- H2.
      apply Numerics.plus_le_compat;
        apply mapmax_ne_correct; simpl; auto.
    Qed.
  
    Lemma mapmax_ne_sub_le: forall (T : Type) (l : list T) (f g : T->Nt) (H0 : O <> length l),
         mapmax_ne f H0 + - mapmax_ne g H0 <= mapmax_ne(fun x => f x + - g x) H0.
    Proof.
      intros.
      apply Numerics.plus_le_compat_r_reverse with (mapmax_ne (l:=l) g H0).
      rewrite <- Numerics.plus_assoc.
      rewrite Numerics.plus_neg_l.
      rewrite Numerics.plus_id_r.
      apply Numerics.le_trans with (mapmax_ne (l:=l) (fun x => (f x + - g x) + g x) H0).
      {
        unfold Numerics.le.
        right.
        apply mapmax_ne_ext.
        intros.
        rewrite <- Numerics.plus_assoc.
        rewrite Numerics.plus_neg_l.
        rewrite Numerics.plus_id_r.
        auto.
      }
      apply mapmax_ne_plus_le.
    Qed.

        
    Lemma argmax_ne_in: forall (T : Type) (l : list T) (f : T->Nt) (H0 : O <> length l),
        List.In (argmax_ne f H0) l.
    Proof.
      intros.
      induction l.
      { exfalso. apply H0. auto. }
      simpl.
      destruct (argmax l f) eqn:e; auto.
      destruct (Numerics.leb (f a) (f t)); auto.
      assert (O <> length l). rewrite argmax_ne_some. exists t. apply e.
      assert ( (argmax l f = Some (argmax_ne f H1))).
        apply argmax_ne_ok.
      rewrite e in H2.
      inversion H2.
      right.
      apply IHl.
    Qed.

    Lemma mapmax_ne_le_neg: forall (T : Type) (l : list T) (f : T->Nt) (H0 : O <> length l),
        - mapmax_ne (fun x=> - f x) H0 <= mapmax_ne f H0.
    Proof.
      intros.
      rewrite argmax_ne_mapmax_ne.
      rewrite Numerics.double_neg.
      apply mapmax_ne_correct.
      apply argmax_ne_in.
    Qed.

    Lemma mapmax_ne_le_ext': forall (T : Type) (l : list T) (f g: T->Nt) (H0 : O <> length l),
      (forall t : T, List.In t l -> f t <= mapmax_ne g H0) -> mapmax_ne f H0 <= mapmax_ne g H0.
    Proof.
      intros.
      rewrite argmax_ne_mapmax_ne in H1.
      rewrite argmax_ne_mapmax_ne.
      rewrite argmax_ne_mapmax_ne.
      apply H1.
      apply argmax_ne_in.
    Qed.


    Lemma mapmax_ne_increasing_max_ne: forall (l : list Nt) (f : Nt->Nt) (H0 : O <> length l), 
      (forall x : Nt, List.In x l -> x <= f x) ->
      f (max_ne H0) <= mapmax_ne f H0.
    Proof.
      intros.
      induction l.
      { exfalso. apply H0. auto. }
      destruct (Nat.eqb O (length l)) eqn:e.
      { 
        apply EqNat.beq_nat_true in e. symmetry in e. rewrite -> List.length_zero_iff_nil in e.
        simpl. rewrite e. simpl. intros. apply le_refl.
      }
      intros.
      apply EqNat.beq_nat_false in e.      
      destruct max_ne_cons with  l a e H0.
      { 
        destruct H2.
        rewrite <- H2.
        destruct mapmax_ne_cons with  Nt l f a e H0.
        {
          destruct H4.
          rewrite <- H4.
          apply IHl; auto.
          intros.
          apply H1.
          apply List.in_cons.
          auto.
        }
        destruct H4.
        rewrite <- H4.
        apply le_trans with (mapmax_ne (l:=l) f e); auto.
        apply IHl. intros. apply H1.  apply List.in_cons. auto.
      }
      destruct H2.
      rewrite <- H2.
      destruct mapmax_ne_cons with  Nt l f a e H0.
      {
        destruct H4.
        rewrite <- H4.
        auto.
      }
      destruct H4.
      rewrite <- H4.
      apply le_refl.
    Qed.




    Lemma mapmax_ne_abs_dist_le: forall (T : Type) (l : list T) (f g : T->Nt) (H0 : O <> length l),
        Numerics.abs ( mapmax_ne f H0 + - mapmax_ne g H0) <=
        mapmax_ne (fun x => Numerics.abs (f x + - g x)) H0.
    Proof.
      intros.
      generalize dependent f.
      generalize dependent g.
      induction l.
      { exfalso. apply H0. auto. }
      destruct l.
      { intros. simpl. apply Numerics.le_refl. }
      intros.
      remember (t :: l) as l'.
      assert (O <> length l').
          rewrite Heql'. unfold not. intros. inversion H1.
      destruct  mapmax_ne_cons with T l' f a H1 H0.
      {
        destruct H2.
        rewrite <- H2.
        destruct  mapmax_ne_cons with T l' g a H1 H0.
        {
          destruct H4.
          rewrite <- H4.
          destruct  mapmax_ne_cons with T  l' (fun x : T => Numerics.abs (f x + - g x)) a H1 H0.
          { destruct H6. rewrite <- H6. apply IHl. }
          destruct H6.          
          rewrite <- H6.
          apply Numerics.le_trans with ( mapmax_ne (fun x : T => Numerics.abs (f x + - g x)) H1); auto.
        }
        destruct H4.
        rewrite <- H4.
        destruct  mapmax_ne_cons with T l' (fun x : T => Numerics.abs (f x + - g x)) a H1 H0.
        {
          destruct H6. 
          rewrite <- H6.
          destruct (Numerics.leb 0 (mapmax_ne (l:=l') f H1 + - g a)) eqn:e.
          {
            assert (Numerics.abs (mapmax_ne (l:=l') f H1 + - g a)  = mapmax_ne(l:=l') f H1 + - g a).
              unfold Numerics.abs. rewrite e. auto.
            rewrite H8.
            clear H8.
            apply Numerics.le_trans with (mapmax_ne (l:=l') f H1 + - mapmax_ne(l:=l') g H1).
            { apply Numerics.plus_le_compat_l. apply Numerics.le_neg. auto. }
            apply Numerics.le_trans with (Numerics.abs (mapmax_ne (l:=l') f H1 + - mapmax_ne(l:=l') g H1)); auto.
            apply Numerics.le_abs.
          }
          assert (Numerics.abs (mapmax_ne (l:=l') f H1 + - g a)  = - (mapmax_ne (l:=l') f H1 + - g a)).
            unfold Numerics.abs. rewrite e. auto.
          rewrite H8.
          rewrite Numerics.plus_neg_distr.
          rewrite Numerics.double_neg.
          apply Numerics.le_trans with ( - f a + g a).
          {
            apply Numerics.plus_le_compat_r.
            apply Numerics.le_neg.
            auto.
          }
          apply Numerics.le_trans with (Numerics.abs (- f a + g a)).
            apply Numerics.le_abs.
          rewrite <- Numerics.abs_neg.
          rewrite Numerics.plus_neg_distr.
          rewrite Numerics.double_neg.
          rewrite H6.
          remember (fun x: T =>Numerics.abs (f x + - g x)) as f'.
          assert (Numerics.abs (f a + - g a) = f' a). rewrite Heqf'. auto.
          rewrite H9.
          apply mapmax_ne_correct.
          simpl.
          auto.
        }
        destruct H6.
        rewrite <- H6.
        destruct (Numerics.leb 0 (mapmax_ne (l:=l') f H1 + - g a)) eqn:e.
        {
          assert (Numerics.abs (mapmax_ne (l:=l') f H1 + - g a) = mapmax_ne(l:=l') f H1 + - g a).
            unfold Numerics.abs. rewrite e. auto.
          rewrite H8.
          clear H8.
          apply Numerics.le_trans with (mapmax_ne (l:=l') f H1 + - mapmax_ne(l:=l') g H1).
          {
            apply Numerics.plus_le_compat_l.
            apply Numerics.le_neg.
            auto.
          }
          apply Numerics.le_trans with (mapmax_ne (l:=l') (fun x : T => Numerics.abs (f x + - g x)) H1); auto.
          apply Numerics.le_trans with (Numerics.abs (mapmax_ne (l:=l') f H1 + - mapmax_ne(l:=l') g H1)); auto.
          apply Numerics.le_abs.
        }
        assert (Numerics.abs (mapmax_ne (l:=l') f H1 + - g a) = -(mapmax_ne (l:=l') f H1 + - g a)).
          unfold Numerics.abs. rewrite e. auto.
        rewrite H8.
        clear H8.
        rewrite Numerics.plus_neg_distr.
        rewrite Numerics.double_neg.
        apply Numerics.le_trans with (- f a + g a).
        {
          apply Numerics.plus_le_compat_r.
          apply Numerics.le_neg.
          auto.
        }
        rewrite <- Numerics.abs_neg.
        rewrite Numerics.plus_neg_distr.
        rewrite Numerics.double_neg.
        apply Numerics.le_abs.
      }
      destruct H2.
      rewrite <- H2.
      destruct  mapmax_ne_cons with T l' g a H1 H0.
      {
        destruct H4.
        rewrite <- H4.
        destruct (Numerics.leb 0 (f a + - mapmax_ne(l:=l') g H1)) eqn:e.
        {
          assert (Numerics.abs (f a + - mapmax_ne(l:=l') g H1) = (f a + - mapmax_ne(l:=l') g H1)).
            unfold Numerics.abs. rewrite e. auto.
          rewrite H6.
          clear H6.
          apply Numerics.le_trans with (f a + - g a).
          {
            apply Numerics.plus_le_compat_l.
            apply Numerics.le_neg.
            auto.
          }
          apply Numerics.le_trans with (Numerics.abs (f a + - g a)).
            apply Numerics.le_abs.
          remember (fun x => Numerics.abs (f x + - g x)) as f'.
          assert (Numerics.abs (f a + - g a) = f' a).
            rewrite Heqf'. auto.
          rewrite H6.
          apply mapmax_ne_correct.
          simpl. auto.
        }
        assert(Numerics.abs (f a + - mapmax_ne(l:=l') g H1) = - (f a + - mapmax_ne(l:=l') g H1)).
          unfold Numerics.abs. rewrite e. auto.
        rewrite H6.
        clear H6.
        rewrite Numerics.plus_neg_distr.
        rewrite Numerics.double_neg.
        destruct  mapmax_ne_cons with T l' (fun x : T => Numerics.abs (f x + - g x)) a H1 H0.
        {
          destruct H6.
          rewrite <- H6.
          apply Numerics.le_trans with (-mapmax_ne (l:=l') f H1 + mapmax_ne(l:=l') g H1).
          {
            apply Numerics.plus_le_compat_r.
            rewrite Numerics.le_neg.
            auto.
          }
          rewrite Numerics.plus_comm.
          apply Numerics.le_trans with (mapmax_ne (l:=l') (fun x : T => Numerics.abs (g x + - f x)) H1).
          {
            apply Numerics.le_trans with (Numerics.abs (mapmax_ne (l:=l') g H1 + - mapmax_ne(l:=l') f H1 )); auto.
            apply Numerics.le_abs.
          }
          unfold Numerics.le.
          right.
          apply mapmax_ne_ext.
          intros.
          rewrite <- Numerics.abs_neg.
          rewrite Numerics.plus_neg_distr.
          rewrite Numerics.double_neg.
          rewrite Numerics.plus_comm.
          auto.
        }
        destruct H6.
        rewrite <- H6.
        apply Numerics.leb_false_iff in e.
        apply Numerics.not_le_lt in e.
        apply Numerics.le_lt_weak in e.
        apply Numerics.le_trans with (-mapmax_ne (l:=l') f H1 + mapmax_ne(l:=l') g H1 ).
        { apply Numerics.plus_le_compat_r. apply Numerics.le_neg. auto. }
        rewrite Numerics.plus_comm.
        rewrite <- Numerics.abs_neg.
        rewrite Numerics.plus_neg_distr.
        rewrite Numerics.double_neg.
        rewrite -> Numerics.plus_comm with (-f a) (g a).
        apply Numerics.le_trans with (Numerics.abs (mapmax_ne (l:=l') g H1 + - mapmax_ne(l:=l') f H1)).
          apply Numerics.le_abs.
        apply Numerics.le_trans with (mapmax_ne (l:=l') (fun x : T => Numerics.abs (g x + - f x)) H1); auto.
        assert (mapmax_ne (l:=l') (fun x : T => Numerics.abs (g x + - f x)) H1 = mapmax_ne(l:=l') (fun x : T => Numerics.abs (f x + - g x)) H1).
          apply mapmax_ne_ext. intros. rewrite <- Numerics.abs_neg. rewrite Numerics.plus_neg_distr. rewrite Numerics.double_neg. rewrite Numerics.plus_comm. auto.
        rewrite H8.
        assert (Numerics.abs (g a + - f a) = Numerics.abs (f a + - g a)).
          rewrite <- Numerics.abs_neg. rewrite Numerics.plus_neg_distr. rewrite Numerics.double_neg. rewrite Numerics.plus_comm. auto.
        rewrite H9.
        auto.
      }
      destruct H4.
      rewrite <- H4.
      remember (fun x : T => Numerics.abs (f x + - g x) ) as f'.
      assert (Numerics.abs (f a + - g a) = f' a).
        rewrite Heqf'. auto.
      rewrite H6.
      apply mapmax_ne_correct.
      simpl. auto.
    Qed.

    Lemma mapmax_ne_le_const: forall (T : Type) (l : list T) (f : T -> Nt) (H0 : O <> length l) (c : Nt), 
      (forall n : T, List.In n l -> f n <= c) <-> (mapmax_ne f H0 <= c).
    Proof.
      intros.
      split; intros.
      {
        rewrite <- mapmax_ne_const with T l c H0.
        apply mapmax_ne_le_ext.
        intros.
        apply H1.
        auto.
      }
      apply le_trans with (mapmax_ne (l:=l) f H0); auto.
      apply mapmax_ne_correct.
      auto.
    Qed.

    Lemma mapmax_ne_gt_const: forall (T : Type) (l : list T) (f : T -> Nt) (H0 : O <> length l) (c : Nt), 
      (exists n : T, List.In n l /\ c < f n) <-> (c < mapmax_ne f H0).
    Proof.
      intros.
      split; intros.
      {
        destruct H1.
        destruct H1.
        apply lt_le_trans with (f x); auto.
        apply mapmax_ne_correct.
        auto.
      }
      exists (argmax_ne f H0).
      rewrite <- argmax_ne_mapmax_ne. 
      split; auto.
        apply argmax_ne_in.
    Qed.

    Lemma mapmax_ne_ge_const: forall (T : Type) (l : list T) (f : T -> Nt) (H0 : O <> length l) (c : Nt), 
      (exists n : T, List.In n l /\ c <= f n) <-> (c <= mapmax_ne f H0).
    Proof.
      intros.
      split; intros.
      {
        destruct H1.
        destruct H1.
        apply le_trans with (f x); auto.
        apply mapmax_ne_correct.
        auto.
      }
      exists (argmax_ne f H0).
      rewrite <- argmax_ne_mapmax_ne. 
      split; auto.
        apply argmax_ne_in.
    Qed.

    Lemma mapmax_ne_lt_ext: forall (T : Type) (l : list T) (f g : T->Nt) (H0 : O <> length l), 
      (forall t : T, List.In t l -> f t < g t) -> mapmax_ne f H0 < mapmax_ne g H0.
    Proof.
      intros.
      induction l.
        exfalso. apply H0. auto.
      destruct l.
      { simpl. apply H1. apply List.in_eq. }
      assert(O <> length (t :: l)).
        simpl. auto.
      destruct mapmax_ne_cons with T (t :: l) f a H2 H0; destruct H3; rewrite <- H3.
      {
        destruct mapmax_ne_cons with T (t :: l) g a H2 H0; destruct H5; rewrite <- H5.
        {
          apply IHl.
          intros.
          apply H1. apply List.in_cons. auto.
        }
        apply lt_le_trans with (mapmax_ne (l:=t :: l) g H2); auto.
        apply IHl. intros. apply H1. apply List.in_cons. auto.
      }
      destruct mapmax_ne_cons with T (t :: l) g a H2 H0; destruct H5; rewrite <- H5.
      {
        apply lt_le_trans with (g a); auto.
        apply H1.
        apply List.in_eq.
      }
      apply H1.
      apply List.in_eq.
    Qed.

   Lemma mapmax_ne_lt_const: forall (T : Type) (l : list T) (f : T->Nt)  (c : Nt) (H0 : O <> length l), 
      (forall t : T, List.In t l -> f t < c) <-> mapmax_ne f H0 < c .
   Proof.
    intros.
    split; intros.
    {
      rewrite <- mapmax_ne_const with T l c H0.
      apply mapmax_ne_lt_ext.
      intros.
      apply H1; auto.
    }
    apply le_lt_trans with (mapmax_ne (l:=l) f H0).
      apply mapmax_ne_correct. auto.
    auto.
  Qed.

  Lemma mapmax_ne_eq_const: forall (T : Type) (l : list T) (f : T->Nt) (H0 : O <> length l) (c : Nt),
      ((forall x : T, List.In x l -> f x <= c) /\ (exists x : T, List.In x l /\ f x = c)) <-> mapmax_ne f H0 = c.
  Proof.
    intros.
    split; intros.
    {
      destruct H1.
      destruct H2.
      destruct H2.
      apply le_both_eq.
        apply mapmax_ne_le_const. auto.
      apply mapmax_ne_ge_const. exists x. split; auto.
      rewrite H3. apply le_refl. 
    }
    split.
    {
      intros.
      rewrite <- H1.
      apply mapmax_ne_correct.
      auto.
    }
    exists (argmax_ne f H0).
    split.
      apply argmax_ne_in.
    rewrite <- argmax_ne_mapmax_ne.
    auto.
  Qed.

  Lemma mapmax_ne_dist_triangle: forall (T : Type) (f1 f2 f3 : T -> Nt) (l : list T) (H0 : O <> length l),
    mapmax_ne (fun x => abs (f1 x + - f2 x)) H0 <= 
    mapmax_ne (fun x => abs (f1 x + - f3 x)) H0 + mapmax_ne (fun x => abs (f3 x + - f2 x)) H0.
  Proof.
    intros.
    apply le_trans with (mapmax_ne (fun x : T => abs (f1 x + - f3 x) + abs (f3 x + - f2 x)) H0).
    {
      apply mapmax_ne_le_ext.
      intros.
      apply abs_triangle.
    }
    apply mapmax_ne_le_const.
    intros.
    apply plus_le_compat;
      apply mapmax_ne_ge_const; exists n; split; auto; apply le_refl.
  Qed.


  Lemma mapmax_ne_eq_all: forall (T : Type) (f : T->Nt) (l : list T) (H0 : O <> length l) (c : Nt),
      (forall t : T, List.In t l -> f t = c) -> mapmax_ne f H0 = c.
  Proof.
    intros.
    apply mapmax_ne_eq_const.
    split; intros.
      rewrite H1; auto. apply le_refl.
    exists (argmax_ne f H0).
    split.
      apply argmax_ne_in.
    apply H1.
    apply argmax_ne_in.
  Qed.

  (**Lemma max_ne_min_dist_max: forall (l : list Nt) (H0 : O <> length l),
      exists c : Nt, 0 < c /\ forall x : Nt, List.In x l ->  (x = max_ne H0) \/ (x + c <= max_ne H0).
  Proof.
    intros.
    induction l.
    { exfalso. apply H0. auto. }
    
    simpl.**)

  Lemma max_ne_In: forall (l : list Nt) (H0 : O <> length l),
      List.In (max_ne H0) l.
  Proof.
    intros.
    induction l.
    { exfalso. apply H0. auto. }
    destruct l.
    { simpl. auto. }
    assert(O <> length (n :: l)).
      unfold not. intros. inversion H1.
    remember (n :: l).
    destruct max_ne_cons with l0 a H1 H0; destruct H2.
    {
      rewrite <- H2.
      simpl. auto.
    }
    rewrite <- H2.
    simpl. auto.
  Qed.

  Lemma max_ne_min_dist_max: forall (l : list Nt) (H0 : O <> length l),
      exists c : Nt, 0 < c /\ forall n : Nt, List.In n l ->  (n = max_ne H0) \/ (n + c <= max_ne H0).
  Proof.
    intros.
    induction l.
    { exfalso. apply H0. auto. }
    destruct l.
    { 
      exists 1.
      split. apply plus_id_lt_mult_id. intros.
      inversion H1; auto. inversion H2.
    }
    assert(O <> length (n :: l)).
      unfold not. intros. inversion H1.
    destruct max_ne_cons with (n :: l) a H1 H0.
    {
      destruct H2.
      rewrite <- H2. clear H2.
      destruct IHl with H1. clear IHl.
      destruct H2.
      destruct H3.
      {
        exists (Numerics.min x (max_ne H1 + - a)).
        split. 
        {
          unfold Numerics.min. destruct (leb x (max_ne H1 + - a)); auto.
          apply lt_diff_pos. auto.
        }
        intros.
        inversion H5.
        { 
          rewrite <- H6. right.
          apply le_trans with (a + (max_ne (l:=n :: l) H1 + - a)).
            apply plus_le_compat_l. apply ge_min_r.
          rewrite -> plus_comm with _ (- a). rewrite plus_assoc.
          rewrite plus_neg_r. rewrite plus_id_l. apply le_refl.
        }
        destruct H4 with n0; auto.
        right.
        apply le_trans with (n0 + x); auto.
        apply plus_le_compat_l. apply ge_min_l.
      }
      rewrite <- H3 in *.
      exists x. split; auto.
      intros. inversion H5; auto.
    }
    destruct H2.
    rewrite <- H2.
    destruct IHl with H1.
    clear IHl.
    destruct H4.
    destruct H3.
    {      
      exists (a + - max_ne H1).
      split.
        apply lt_diff_pos.  auto.
      intros.
      inversion H6; auto.
      right.
      rewrite plus_assoc. rewrite -> plus_comm with n0 _.
      rewrite <- plus_id_r with a.
      repeat rewrite <- plus_assoc.
      apply plus_le_compat_l.
      rewrite plus_id_l.
      rewrite <- plus_neg_r with n0.
      apply plus_le_compat_l.
      apply le_neg. apply max_ne_correct. auto.
    }
    exists x.
    split; auto.
    intros.
    destruct H6; auto.
    destruct H5 with n0; auto.
    { rewrite H3 in H7. auto. } 
    right. rewrite H3 in H7. auto.
  Qed.
    
  Lemma mapmax_ne_min_dist_max: forall (T : Type) (f : T->Nt) (l : list T) (H0 : O <> length l),
      exists c : Nt, 0 < c /\ forall t : T, List.In t l ->  (f t = mapmax_ne f H0) \/ (f t + c <= mapmax_ne f H0).
  Proof.
    intros.
    rewrite mapmax_ne_map_max_ne.
    {
      assert(O <> size [seq f i | i <- l]); auto.
      rewrite size_map. auto.
    }
    intros.
    edestruct max_ne_min_dist_max.
    destruct H1.
    exists x. split; auto.
    intros.
    apply H2. apply List.in_map. auto.
  Qed.

  End use_Numerics.
  Section use_Numerics2.

  Context (Nt:Type) `{Numeric Nt}.

  
    
  Lemma to_R_argmax: forall (T : Type) (l : list T) (f : T->Nt),
     argmax l f = argmax l (fun x => to_R (f x)).
  Proof.
    intros.
    induction l; auto.
    simpl.
    rewrite <- IHl.
    destruct (argmax l f); auto.
    rewrite <- to_R_leb.
    auto.
  Qed.

  Lemma to_R_mapmax: forall (T : Type) (l : list T) (f : T->Nt),
     O <> length l -> exists x : Nt, 
        Some x = mapmax l f /\ Some (to_R x) = mapmax l (fun x => to_R (f x)).
  Proof.
    intros.
    induction l.
    SearchAbout mapmax.
    { exfalso. apply H0. auto. }
    destruct l.
      simpl. eauto.
    destruct IHl.
    { simpl. auto. }
    destruct H1.
    simpl in *.    
    rewrite <- H1.
    rewrite <- H2.
    exists (if leb (f a) x then x else f a).
    split; auto.
    rewrite <- to_R_leb.
    destruct (leb (f a) x); auto.
  Qed.

 
  Lemma to_R_argmax_ne: forall (T : Type) (l : list T) (f : T-> Nt) (H0 : O <> length l),
    argmax_ne f H0 = argmax_ne (fun x => to_R (f x)) H0.
  Proof.
    intros.
    assert( argmax l f= Some (argmax_ne f H0)).
      apply argmax_ne_ok.
    assert( argmax l (fun x => to_R (f x)) = Some (argmax_ne (fun x => to_R (f x)) H0)).
      apply argmax_ne_ok.
    destruct to_R_argmax with T l f; auto.
    rewrite H1 in H2.
    inversion H2.
    auto.
  Qed.
    
  Lemma to_R_mapmax_ne: forall (T : Type) (l : list T) (f : T-> Nt) (H0 : O <> length l),
    to_R (mapmax_ne f H0) = mapmax_ne (fun x => to_R (f x)) H0.
  Proof.
    intros.
    rewrite argmax_ne_mapmax_ne.
    rewrite to_R_argmax_ne.
    rewrite argmax_ne_mapmax_ne.
    auto.
  Qed.

  



   End use_Numerics2.
End num_Extrema.




