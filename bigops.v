Set Implicit Arguments.
Unset Strict Implicit.

Require Import NArith QArith Reals Rpower Ranalysis Fourier Permutation.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import OUVerT.numerics.

Delimit Scope R_scope with R.

Fixpoint big_sum (T : Type) (cs : seq T) (f : T -> R) : R :=
  if cs is [:: c & cs'] then (f c + big_sum cs' f)%R
  else 0%R.

Lemma big_sum_nmul (T : Type) (cs : seq T) (f : T -> R) :
  (big_sum cs (fun c => - f c) = - big_sum cs [eta f])%R.
Proof.
  elim: cs=> /=; first by rewrite Ropp_0.
    by move=> a l IH; rewrite Ropp_plus_distr IH.
Qed.      

Lemma big_sum_ext' T U (cs : seq T) (cs' : seq U) f f' :
  length cs = length cs' ->
  (List.Forall
     (fun p =>
        let: (c, c') := p in
        f c = f' c')
     (zip cs cs')) -> 
  big_sum cs f = big_sum cs' f'.
Proof.
  move=> H H2; elim: cs cs' H H2; first by case.
  move => a l IH; case => // a' l' H H2; case: H => /= H3.
  by inversion H2; subst; rewrite H1 (IH l').
Qed.

Lemma big_sum_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_sum cs f = big_sum cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_sum_scalar T (cs : seq T) r f :
  (big_sum cs (fun c => r * f c) = r * big_sum cs (fun c => f c))%R.
Proof.
  elim: cs=> /=; first by rewrite Rmult_0_r.
    by move=> a l IH; rewrite IH /=; rewrite Rmult_plus_distr_l.
Qed.      

Lemma big_sum_plus T (cs : seq T) f g :
  (big_sum cs (fun c => f c + g c) =
   big_sum cs (fun c => f c) + big_sum cs (fun c => g c))%R.
Proof.
  elim: cs=> /=; first by rewrite Rplus_0_r.
  move=> a l IH; rewrite IH /=.
  rewrite [((_ + big_sum l (fun c => f c) + _))%R]Rplus_assoc.
  rewrite [(big_sum l (fun c => f c) + (_ + _))%R]Rplus_comm.
  rewrite Rplus_assoc.
  rewrite Rplus_assoc.  
  f_equal.
  f_equal.
  by rewrite Rplus_comm.
Qed.      

Lemma big_sum_cat T (cs1 cs2 : seq T) f :
  (big_sum (cs1++cs2) (fun c => f c) =
   big_sum cs1 (fun c => f c) + big_sum cs2 (fun c => f c))%R.
Proof.
  elim: cs1 => /=; first by rewrite Rplus_0_l.
  move=> a l IH; rewrite IH /=.
  rewrite [((_ + big_sum l (fun c => f c) + _))%R]Rplus_assoc //.
Qed.

Lemma big_sum_perm T (cs1 cs2 : seq T) (H : Permutation cs1 cs2) f :
  (big_sum cs1 (fun c => f c) = big_sum cs2 (fun c => f c))%R.
Proof.
  elim: H => //=.
  { move => x l l' H -> //. }
  { by move => x y l; rewrite -Rplus_assoc [f y + f x]Rplus_comm Rplus_assoc. }
  move => l l' l'' H /= -> H2 -> //.
Qed.

Lemma big_sum_split T (cs : seq T) f (p : pred T) :
  (big_sum cs f = big_sum (filter p cs) f + big_sum (filter (predC p) cs) f)%R.
Proof.
  rewrite ->big_sum_perm with (cs2 := filter p cs ++ filter (predC p) cs); last first.
  { elim: cs => // a l /= H; case: (p a) => /=.
    { by constructor. }
      by apply: Permutation_cons_app. }
  by rewrite big_sum_cat.
Qed.    

Lemma big_sum_ge0 (T:eqType) (cs : seq T) f (H : forall x, x \in cs -> 0 <= f x)
  : 0 <= big_sum cs f.
Proof.
  elim: cs H => /=; first by move => _; apply: Rle_refl.
  move => a l IH H2; rewrite -[0]Rplus_0_l; apply: Rplus_le_compat => //.
  by apply: H2 => /=; apply: mem_head.
  by apply: IH => // x H3; apply: H2; rewrite/=/in_mem/=; apply/orP; right.
Qed.  

Lemma rat_to_R_sum T (cs : seq T) (f : T -> rat) :
  rat_to_R (\sum_(c <- cs) (f c)) =  
  big_sum cs (fun c => (rat_to_R (f c)))%R.
Proof.
  elim: cs=> //=; first by rewrite big_nil rat_to_R0.
  move=> a' l IH; rewrite big_cons.
  rewrite rat_to_R_plus IH.
    by f_equal; rewrite rat_to_R_plus rat_to_R_opp rat_to_R_mul.
Qed.    

Lemma big_sum_constant T (cs : seq T) n :
  (big_sum cs (fun _ => n) = INR (size cs) * n)%R.
Proof.
  elim: cs => //=.
  { by rewrite Rmult_0_l. }
  move => t0 l ->.
  case: (size l).
  { by rewrite /INR Rmult_0_l Rmult_1_l Rplus_0_r. }
  move => x.
  field.
Qed.

(*DUPLICATE: REMOVE*)
Lemma big_sum_mult_left T (cs : seq T) c f :
  c * big_sum cs f = big_sum cs (fun x => c * f x).
Proof.
  elim: cs => //=.
  { by rewrite Rmult_0_r. }
  move => a l /=; rewrite Rmult_plus_distr_l => -> //.
Qed.  

Lemma big_sum_mult_right T (cs : seq T) c f :
  big_sum cs f * c = big_sum cs (fun x => f x * c).
Proof.
  elim: cs => //=.
  { by rewrite Rmult_0_l. }
  move => a l /=; rewrite Rmult_plus_distr_r => -> //.
Qed.  

Fixpoint big_product (T : Type) (cs : seq T) (f : T -> R) : R :=
  if cs is [:: c & cs'] then (f c * big_product cs' f)%R
  else 1%R.

Lemma big_product_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_product cs f = big_product cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_product_ge0 (T : eqType) (cs : seq T) (f : T -> R) :
  (forall c, c \in cs -> 0 <= f c)%R ->
  (0 <= big_product cs f)%R.
Proof.
  elim: cs=> /=.
  { move=> _; apply: Fourier_util.Rle_zero_1. }
  move=> a l IH H.
  have H2: (0 = 0 * 0)%R by rewrite Rmult_0_l.
  rewrite H2; apply: Rmult_le_compat.
  by apply: Rle_refl.
  by apply: Rle_refl.
  by apply: H; rewrite in_cons; apply/orP; left.
  apply: IH=> c H3; apply: H.
  by rewrite in_cons; apply/orP; right.
Qed.

Lemma big_product_gt0 (T : eqType) (cs : seq T) (f : T -> R) :
  (forall c, c \in cs -> 0 < f c)%R ->
  (0 < big_product cs f)%R.
Proof.
  elim: cs=> /=.
  { move=> _; apply: Fourier_util.Rlt_zero_1. }
  move=> a l IH H.
  have H2: (0 = 0 * 0)%R by rewrite Rmult_0_l.
  apply: Rmult_lt_0_compat.
  by apply: H; rewrite in_cons; apply/orP; left.
  by apply: IH=> c H3; apply: H; rewrite in_cons; apply/orP; right.
Qed.      
  
Lemma ln_big_product_sum (T : eqType) (cs : seq T) (f : T -> R) :
  (forall t : T, 0 < f t)%R -> 
  ln (big_product cs f) = big_sum cs (fun c => ln (f c)).
Proof.
  elim: cs=> /=; first by rewrite ln_1.
  move=> a l IH H; rewrite ln_mult=> //; first by rewrite IH.
    by apply: big_product_gt0.
Qed.    

Lemma big_product_exp_sum (T : eqType) (cs : seq T) (f : T -> R) :
  big_product cs (fun x => exp (f x)) = exp (big_sum cs f).
Proof.
  elim: cs => //=; first by rewrite exp_0.
  by move => a l IH; rewrite IH exp_plus.
Qed.  

Lemma big_product_le (T : eqType) (cs : seq T) (f : T -> R) g :
  (forall c, c \in cs -> 0 <= f c)%R ->
  (forall c, c \in cs -> 0 <= g c)%R ->
  (forall c, c \in cs -> f c <= g c)%R -> 
  (big_product cs f <= big_product cs g)%R.
Proof.
  elim: cs=> //=.
  { move=> _ _ _; apply: Rle_refl. }
  move=> a l IH H1 H2 H3; apply Rmult_le_compat.
  { by apply: H1; rewrite in_cons; apply/orP; left. }
  { apply: big_product_ge0.
      by move=> c H4; apply: H1; rewrite in_cons; apply/orP; right. }
  { by apply: H3; rewrite in_cons; apply/orP; left. }
  apply: IH.
  { by move=> c H; apply: H1; rewrite in_cons; apply/orP; right. }
  { by move=> c H; apply: H2; rewrite in_cons; apply/orP; right. }
    by move=> c H; apply: H3; rewrite in_cons; apply/orP; right.
Qed.    

Lemma big_sum_lt_aux (T : eqType) (cs : seq T) (f : T -> R) g :
  (forall c, c \in cs -> f c < g c)%R -> 
  cs=[::] \/ (big_sum cs f < big_sum cs g)%R.
Proof.
  elim: cs=> //=.
  { by move=> _; left. }
  move=> a l IH H1; right; apply Rplus_lt_le_compat.
  { by apply: H1; rewrite in_cons; apply/orP; left. }
  have H2: (forall c : T, c \in l -> f c < g c).
  { by move => c Hin; move: (H1 c); rewrite in_cons; apply; apply/orP; right. }
  case: (IH H2) => //.
  { move => -> /=; apply: Rle_refl. }
  by move => H3; left.
Qed.

Lemma big_sum_lt (T : eqType) (cs : seq T) (f : T -> R) g :
  (forall c, c \in cs -> f c < g c)%R -> 
  cs<>[::] ->
  (big_sum cs f < big_sum cs g)%R.
Proof.
  move => H H1; case: (big_sum_lt_aux H) => //.
Qed.

Lemma big_product_perm T (cs1 cs2 : seq T) (H : Permutation cs1 cs2) f :
  (big_product cs1 (fun c => f c) = big_product cs2 (fun c => f c))%R.
Proof.
  elim: H => //=.
  { move => x l l' H -> //. }
  { by move => x y l; rewrite -Rmult_assoc [f y * f x]Rmult_comm Rmult_assoc. }
  move => l l' l'' H /= -> H2 -> //.
Qed.

Lemma big_product_cat T (cs1 cs2 : seq T) f :
  (big_product (cs1++cs2) (fun c => f c) =
   big_product cs1 (fun c => f c) * big_product cs2 (fun c => f c))%R.
Proof.
  elim: cs1 => /=; first by rewrite Rmult_1_l.
  move=> a l IH; rewrite IH /=.
  rewrite [((_ * big_product l (fun c => f c) * _))%R]Rmult_assoc //.
Qed.

Lemma big_product_split T (cs : seq T) f (p : pred T) :
  (big_product cs f = big_product (filter p cs) f * big_product (filter (predC p) cs) f)%R.
Proof.
  rewrite ->big_product_perm with (cs2 := filter p cs ++ filter (predC p) cs); last first.
  { elim: cs => // a l /= H; case: (p a) => /=.
    { by constructor. }
      by apply: Permutation_cons_app. }
  by rewrite big_product_cat.
Qed.    

Lemma big_product0 (T : eqType) (cs : seq T) c :
  c \in cs -> 
  big_product cs (fun _ => 0) = 0.
Proof. by elim: cs c => // a l IH c /= _; rewrite Rmult_0_l. Qed.

Lemma rat_to_R_prod T (cs : seq T) (f : T -> rat) :
  rat_to_R (\prod_(c <- cs) (f c)) =  
  big_product cs (fun c => (rat_to_R (f c)))%R.
Proof.
  elim: cs=> //=; first by rewrite big_nil rat_to_R1.
  move=> a' l IH; rewrite big_cons.
  rewrite rat_to_R_mul IH.
    by f_equal; rewrite rat_to_R_plus rat_to_R_opp rat_to_R_mul.
Qed.    

Lemma big_sum_lift (T : Type) (ts : seq T) f g 
      (g_zero : g 0 = 0)
      (g_plus : forall x y, g (x + y) = g x + g y) :
  big_sum ts (fun x => g (f x)) = g (big_sum ts (fun x => f x)).
Proof. by elim: ts => //= a l ->. Qed.

Lemma big_product_lift (T : Type) (ts : seq T) f g 
      (g_zero : g 1 = 1)
      (g_mult : forall x y, g (x * y) = g x * g y) :
  big_product ts (fun x => g (f x)) = g (big_product ts (fun x => f x)).
Proof. by elim: ts => //= a l ->. Qed.

Lemma big_product_constant T (cs : seq T) n :
  (big_product cs (fun _ => n) = n ^ size cs)%R.
Proof. elim: cs => //= _ l -> //. Qed.

(*MOVE: numerics.v*)
(*Monoid instance for Coq R*)
Program Definition Rtimes_law : @Monoid.law R 1 :=
  @Monoid.Law R 1 Rmult _ _ _.
Next Obligation. by move => x y z; rewrite Rmult_assoc. Qed.
Next Obligation. by move => x; rewrite Rmult_1_l. Qed.
Next Obligation. by move => x; rewrite Rmult_1_r. Qed.
Lemma Rtimes_com : commutative Rtimes_law.
Proof. by move => x y /=; rewrite Rmult_comm. Qed.
Definition Rtimes_com_law : @Monoid.com_law R 1 :=
  @Monoid.ComLaw _ _ Rtimes_law Rtimes_com.
Program Definition Rtimes : Monoid.mul_law 0 :=
  @Monoid.MulLaw _ 0 Rtimes_com_law _ _.
Next Obligation. by move => x; rewrite Rmult_0_l. Qed.
Next Obligation. by move => x; rewrite Rmult_0_r. Qed.

Program Definition Rplus_law : @Monoid.law R 0 :=
  @Monoid.Law R 0 Rplus _ _ _.
Next Obligation. by move => x y z; rewrite Rplus_assoc. Qed.
Next Obligation. by move => x; rewrite Rplus_0_l. Qed.
Next Obligation. by move => x; rewrite Rplus_0_r. Qed.
Lemma Rplus_com : commutative Rplus_law.
Proof. by move => x y /=; rewrite Rplus_comm. Qed.
Definition Rplus_com_law : @Monoid.com_law R 0 :=
  @Monoid.ComLaw _ _ Rplus_law Rplus_com.
Program Definition Rplus : Monoid.add_law 0 Rtimes :=
  @Monoid.AddLaw _ 0 Rmult Rplus_com_law _ _.
Next Obligation. by move => x y z; rewrite Rmult_plus_distr_r. Qed.
Next Obligation. by move => x y z; rewrite Rmult_plus_distr_l. Qed.
(*END MOVE*)

Section SSR_RBigops.
  Variable I : finType.
  Variable F : I -> R.
  Variable P : pred I.

  Lemma big_sum_sum : big_sum (enum I) F = \big[Rplus/0]_i F i.
  Proof.
    rewrite BigOp.bigopE /index_enum enumT.
    by elim: (Finite.enum I) => //= a l ->.
  Qed.

  Lemma big_sum_sumP : big_sum [seq x <- enum I | P x] F = \big[Rplus/0]_(i | P i) F i.
  Proof.
    rewrite BigOp.bigopE /index_enum enumT.
    by elim: (Finite.enum I) => //= a l; case Heq: (P a) => //= ->.
  Qed.
  
  Lemma big_product_prod : big_product (enum I) F = \big[Rtimes/1]_i F i.
  Proof.
    rewrite BigOp.bigopE /index_enum enumT.
    by elim: (Finite.enum I) => //= a l ->.
  Qed.

  Lemma big_product_prodP : big_product [seq x <- enum I | P x] F = \big[Rtimes/1]_(i | P i) F i.
  Proof.
    rewrite BigOp.bigopE /index_enum enumT.
    by elim: (Finite.enum I) => //= a l; case Heq: (P a) => //= ->.
  Qed.
End SSR_RBigops.    
  
(*ssreflect: bigA_distr_bigA*)
Lemma big_product_distr_sum (I J : finType) (F : I -> J -> R) :
  big_product (enum I) (fun i => big_sum (enum J) (fun j => F i j)) =
  big_sum (enum [finType of {ffun I -> J}])
          (fun f : {ffun I -> J} => big_product (enum I) (fun i => F i (f i))).
Proof.
  rewrite big_sum_sum big_product_prod.
  have ->:
    \big[Rtimes/1]_i big_sum (enum J) [eta F i]       
  = \big[Rtimes/1]_i \big[Rplus/0]_j F i j.
  { by apply: eq_big => // i _; rewrite big_sum_sum. }
  by rewrite bigA_distr_bigA; apply: eq_big => // f _; rewrite big_product_prod.
Qed.    

Lemma marginal_unfoldR N i (A : finType) (F : {ffun 'I_N -> A} -> R) :
  let P t (p : {ffun 'I_N -> A}) := p i == t in     
  \big[Rplus/0]_(p : [finType of (A * {ffun 'I_N -> A})] | P p.1 p.2) (F p.2) =
  \big[Rplus/0]_(p : {ffun 'I_N -> A}) (F p).
Proof.
  move => P.
  set (G (x : A) y := F y).
  have ->:
    \big[Rplus/0]_(p | P p.1 p.2) F p.2 =
    \big[Rplus/0]_(p | predT p.1 && P p.1 p.2) G p.1 p.2 by apply: eq_big.
  rewrite -pair_big_dep /= /G /P.
  have ->:
    \big[Rplus/0]_i0 \big[Rplus/0]_(j : {ffun 'I_N -> A} | j i == i0) F j =
    \big[Rplus/0]_i0 \big[Rplus/0]_(j : {ffun 'I_N -> A} | predT j && (j i == i0)) F j.
  { by apply: eq_big. }
  rewrite -partition_big //. 
Qed.      

Lemma prod_splitR N (i : 'I_N) (A : finType) (y : {ffun 'I_N -> A}) f :
  \big[Rtimes/1]_(j in [set i]) (f j) (y j) *
  \big[Rtimes/1]_(j in [set~ i]) (f j) (y j) = \big[Rtimes/1]_(j < N) (f j) (y j).
Proof.        
  have ->:
    \big[Rtimes/1]_(j < N) (f j) (y j) =
    \big[Rtimes/1]_(j in [predU (pred1 i) & [set~ i]]) (f j) (y j).
  { apply: congr_big => // j; rewrite /in_mem /=.
    case H: (j == i).
    { by have ->: j \in pred1 i = true by rewrite /pred1 /in_mem /= H. }
    have ->: j \in [set~ i] by rewrite in_setC1 H.
      by rewrite orbC. }
  set (F j := f j (y j)).
  rewrite (@bigU R 1 _) /=; last first.
  { by rewrite disjoint1 in_setC1; apply/negP; rewrite eq_refl. }
  f_equal.
  apply: congr_big => //; first by move => j; rewrite in_set1.
Qed.

Lemma sum_splitR N (i : 'I_N) (A : finType) (y : {ffun 'I_N -> A}) f :
  \big[Rplus/0]_(j in [set i]) (f j) (y j) +
  \big[Rplus/0]_(j in [set~ i]) (f j) (y j) = \big[Rplus/0]_(j < N) (f j) (y j).
Proof.        
  have ->:
    \big[Rplus/0]_(j < N) (f j) (y j) =
    \big[Rplus/0]_(j in [predU (pred1 i) & [set~ i]]) (f j) (y j).
  { apply: congr_big => // j; rewrite /in_mem /=.
    case H: (j == i).
    { by have ->: j \in pred1 i = true by rewrite /pred1 /in_mem /= H. }
    have ->: j \in [set~ i] by rewrite in_setC1 H.
      by rewrite orbC. }
  rewrite bigU /=; last first.
  { by rewrite disjoint1 in_setC1; apply/negP; rewrite eq_refl. }
  f_equal.
  apply: congr_big => //; first by move => j; rewrite in_set1.
Qed.

Lemma big_sum_le (T : eqType) (cs : seq T) (f : T -> R) g :
  (forall c, c \in cs -> f c <= g c)%R -> 
  (big_sum cs f <= big_sum cs g)%R.
Proof.
  elim: cs=> //=.
  { move=> _; apply: Rle_refl. }
  move=> a l IH H1; apply Rplus_le_compat.
  { by apply: H1; rewrite in_cons; apply/orP; left. }
    by apply: IH=> c H; apply: H1; rewrite in_cons; apply/orP; right.
Qed.

Lemma perm_eq_nil (T:eqType) (cs : seq T) : perm_eq [::] cs -> cs=[::].
Proof.
  move => H; apply: perm_eq_small => //.
  by rewrite perm_eq_sym.
Qed.    

Lemma In_mem (T:eqType) (a:T) (cs : seq T) : List.In a cs <-> a \in cs.
Proof.
  elim: cs a => // a l IH ax; split.
  { inversion 1; subst; first by rewrite mem_head.
    by rewrite /in_mem/=; apply/orP; right; rewrite -(IH ax). }
  rewrite /in_mem/=; case/orP; first by move/eqP => <-; left.
  by move => H; right; rewrite IH.
Qed.    

Lemma uniq_NoDup (T:eqType) (cs : seq T) : uniq cs -> List.NoDup cs.
Proof.
  elim: cs.
  { move => _; constructor. }
  move => a l IH; rewrite cons_uniq; case/andP => H1 H2; constructor; last by apply: IH.
  by move => Hnin; rewrite /in_mem/= in H1; apply: (negP H1); rewrite -In_mem.
Qed.

Lemma perm_eqi (T:eqType) (cs1 cs2 : seq T) :
  uniq cs1 ->
  uniq cs2 -> 
  cs1 =i cs2 -> Permutation cs1 cs2.
Proof.
  move => U1 U2 H; apply: NoDup_Permutation.
  by apply: uniq_NoDup.
  by apply: uniq_NoDup.    
  move => x; split => H2.
  { by rewrite In_mem; rewrite -(H x); rewrite -In_mem. }
  by rewrite In_mem; rewrite (H x); rewrite -In_mem.
Qed.
  
Lemma perm_sub (T:eqType) (cs1 cs2 : seq T) :
  uniq cs1 ->
  uniq cs2 -> 
  {subset cs1 <= cs2} -> 
  Permutation cs1 [seq x <- cs2 | x \in cs1].
Proof.
  move => U1 U2 H.
  have H2: Permutation cs1 [seq x <- cs1 | x \in cs2].
  { elim: cs1 cs2 H {U1 U2} => // a l IH cs2 H /=.
    case Hin: (a \in cs2) => //.
    { by constructor; apply: IH => x H2; apply: H; rewrite /in_mem/=; apply/orP; right. }
    by move: H; move/(_ a); rewrite mem_head; move/(_ erefl); rewrite Hin. }
  apply: (Permutation_trans H2); move {H2}.
  apply: perm_eqi; try apply: filter_uniq => //.
  by move => x; rewrite 2!mem_filter andbC.
Qed.
  
Lemma big_sum_le2 (T : eqType) (cs1 cs2 : seq T) (f : T -> R) :
  uniq cs1 ->
  uniq cs2 -> 
  (forall c, c \in cs2 -> 0 <= f c)%R -> 
  (forall c, c \in cs1 -> c \in cs2)%R -> 
  (big_sum cs1 f <= big_sum cs2 f)%R.
Proof.
  move => U1 U2 H1 H2.
  rewrite [big_sum cs2 _](big_sum_split _ _ [pred x | x \in cs1]).
  rewrite -[big_sum cs1 _]Rplus_0_r; apply: Rplus_le_compat.
  { have Hperm: Permutation cs1 [seq x <- cs2 | [pred x in cs1] x].
    { by apply: perm_sub. }
    rewrite (big_sum_perm Hperm); apply: Rle_refl. }
  by apply: big_sum_ge0 => x; rewrite mem_filter; case/andP => _ H; apply: H1.
Qed.  

(*TODO: All these bigops should really be consolidated at some point...sigh*)

(** Q bigops *)

Delimit Scope Q_scope with Q.

Fixpoint big_sumQ (T : Type) (cs : seq T) (f : T -> Q) : Q :=
  if cs is [:: c & cs'] then (f c + big_sumQ cs' f)%Q
  else 0%Q.

Lemma big_sumQ_nmul (T : Type) (cs : seq T) (f : T -> Q) :
  Qeq (big_sumQ cs (fun c => - f c))%Q (- big_sumQ cs [eta f])%Q.
Proof.
  elim: cs=> /=; first by [].
    by move => a l IH; rewrite IH Qopp_plus.
Qed.

Lemma big_sumQ_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_sumQ cs f = big_sumQ cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_sumQ_scalar T (cs : seq T) r f :
  Qeq (big_sumQ cs (fun c => r * f c))%Q (r * big_sumQ cs (fun c => f c))%Q.
Proof.
  elim: cs=> /=. rewrite Qmult_0_r. apply Qeq_refl.
    by move => a l IH; rewrite IH Qmult_plus_distr_r.
Qed.

(** N bigops *)

Fixpoint big_sumN (T : Type) (cs : seq T) (f : T -> N) : N :=
  if cs is [:: c & cs'] then (f c + big_sumN cs' f)%num
  else 0%num.

Lemma big_sumN_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_sumN cs f = big_sumN cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_sumN_scalar T (cs : seq T) r f :
  eq (big_sumN cs (fun c => r * f c))%num (r * big_sumN cs (fun c => f c))%num.
Proof.
  elim: cs=> /=. rewrite N.mul_0_r. apply N.eq_refl.
  by move => a l IH; rewrite IH Nmult_plus_distr_l.
Qed.
