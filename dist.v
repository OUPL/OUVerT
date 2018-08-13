Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import bigops numerics expfacts.

Local Open Scope ring_scope.

(** Discrete distributions *)
Section Dist.
  Variable T : finType.
  Variable rty : numDomainType.

  Definition dist_axiom (f : {ffun T -> rty}) :=
    [&& \sum_t (f t) == 1
      & [forall t : T, f t >= 0]].
  Record dist : Type := mkDist { pmf :> {ffun T -> rty}; dist_ax : dist_axiom pmf }.
  Canonical dist_subType := [subType for pmf].

  (* We have eqType and choiceTypes on distributions:*)
  Definition dist_eqMixin := Eval hnf in [eqMixin of dist by <:].
  Canonical dist_eqType := Eval hnf in EqType dist dist_eqMixin.
  Definition dist_choiceMixin := [choiceMixin of dist by <:].
  Canonical dist_choiceType := Eval hnf in ChoiceType dist dist_choiceMixin.
End Dist.

Section distLemmas.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Lemma dist_normalized : \sum_t d t = 1.
  Proof. by case: (andP (dist_ax d)); move/eqP. Qed.

  Lemma dist_positive : forall t : T, d t >= 0.
  Proof. by case: (andP (dist_ax d))=> _; move/forallP. Qed.
End distLemmas.

Section support.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Definition support : {set T} := [set t : T | 0 < d t].

  Lemma in_support x : x \in support -> 0 < d x.
  Proof. by rewrite /support in_set. Qed.

  Lemma supportP x : x \in support <-> 0 < d x.
  Proof.
    split; first by apply: in_support.
    by rewrite /support in_set.
  Qed.      
End support.

Section bind.
  Variable T U : finType.
  Variable rty : numDomainType.  
  Variable d : {ffun T -> rty}.
  Variable f : T -> {ffun U -> rty}.
  Definition bind : {ffun U -> rty} :=
    finfun (fun u : U => \sum_(t : T) (d t) * (f t u)).
End bind.
  
Section expectedValue.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Definition probOf (p : pred T) :=
      \sum_(t : T | p t) d t.

  Lemma probOf_xpredT : probOf xpredT = 1.
  Proof.
    rewrite /probOf; apply: dist_normalized.
  Qed.

  Lemma probOf_nonneg (p : pred T) : 0 <= probOf p.
  Proof.
    apply: sumr_ge0 => i Hi; apply: dist_positive.
  Qed.    

  Definition expectedCondValue (f : T -> rty) (p : pred T) :=
    (\sum_(t : T | p t) (d t) * (f t)) / (probOf p).

  Lemma expectedCondValue_mull f p c :
    expectedCondValue (fun t => c * f t) p = c * expectedCondValue f p.
  Proof.
    rewrite /expectedCondValue.
    have ->: \sum_(t | p t) d t * (c * f t)
           = c * \sum_(t | p t) d t * f t.
    { rewrite mulr_sumr; apply/congr_big=> //= i _.
      by rewrite mulrA [d i * c]mulrC -mulrA. }
    by rewrite mulrA.
  Qed.

  Lemma expectedCondValue_linear f g p :
    expectedCondValue (fun t => f t + g t) p =
    expectedCondValue f p + expectedCondValue g p.
  Proof.
    rewrite /expectedCondValue.
    have ->: \sum_(t | p t) d t * (f t + g t) =
             \sum_(t | p t) (d t * f t + d t * g t).
    { by apply/congr_big=> //= i _; rewrite mulrDr. }
    rewrite 3!mulr_suml -big_split /=; move: (probOf p) => e.
    apply: congr_big => // i _; rewrite mulrDl //.
  Qed.    

  Lemma sum_split (f : T -> rty) p :
    \sum_t f t = \sum_(t | p t) f t + \sum_(t | ~~p t) f t.
  Proof.
    have ->: \sum_t f t = \sum_(t | p t || ~~p t) f t.
    { by apply/congr_big => // x; case: (p x). }
    rewrite -big_filter.
    have ->:
      \sum_(i <- [seq i <- index_enum T | p i || ~~ p i]) f i
    = \sum_(i <- [seq i <- index_enum T | p i] ++ [seq i <- index_enum T | ~~p i]) f i.
    { apply: eq_big_perm.
      have ->: [seq i <- index_enum T | ~~ p i] = [seq i <- index_enum T | predC p i] by [].
      rewrite perm_eq_sym perm_filterC.
      have ->: [seq i <- index_enum T | p i || ~~ p i] = index_enum T.
      { have ->: [seq i <- index_enum T | p i || ~~ p i] = [seq i <- index_enum T | predT i].
        { by apply eq_in_filter => x; rewrite /in_mem /= => H; case: (p x). }
        by rewrite filter_predT. }
      by []. }
    by rewrite big_cat /= !big_filter.
  Qed.    
  
  Definition expectedValue (f : T -> rty) :=
    \sum_(t : T) (d t) * (f t).

  Lemma expectedValue_split f p :
    expectedValue f = \sum_(t | p t) d t * f t + \sum_(t | ~~p t) d t * f t.
  Proof.
    rewrite /expectedValue; rewrite ->sum_split with (p:=p); f_equal => //.
  Qed.    
  
  Lemma expectedValue_expectedCondValue f : 
    expectedValue f = expectedCondValue f xpredT.
  Proof.
    by rewrite /expectedValue /expectedCondValue probOf_xpredT divr1.
  Qed.
  
  Lemma expectedValue_mull f c :
    expectedValue (fun t => c * f t) = c * expectedValue f.
  Proof. by rewrite 2!expectedValue_expectedCondValue expectedCondValue_mull. Qed.

  Lemma expectedValue_linear f g :
    expectedValue (fun t => f t + g t) =
    expectedValue f + expectedValue g.
  Proof. by rewrite 3!expectedValue_expectedCondValue expectedCondValue_linear. Qed.

  Lemma expectedValue_const c : expectedValue (fun _ => c) = c.
  Proof.
    rewrite /expectedValue /expectedCondValue -mulr_suml.
    by case: (andP (dist_ax d)); move/eqP=> ->; rewrite mul1r.
  Qed.

  Lemma expectedValue_range f
        (H : forall x : T, 0 <= f x <= 1) :
    0 <= expectedValue f <= 1.
  Proof.      
    rewrite /expectedValue /expectedCondValue; apply/andP; split.
    apply: sumr_ge0=> i _; case H2: (f i == 0).
    { by move: (eqP H2)=> ->; rewrite mulr0. }
    { rewrite mulrC pmulr_rge0; first by apply: dist_positive.
      case: (andP (H i))=> H3 _.
      rewrite lt0r; apply/andP; split=> //.
      by apply/eqP=> H4; rewrite H4 eq_refl in H2. }
    rewrite -(@dist_normalized T rty d); apply: ler_sum.
    move=> i _; case H2: (d i == 0).
    { by move: (eqP H2)=> ->; rewrite mul0r. }
    rewrite mulrC ger_pmull; first by case: (andP (H i)).
    have H3: 0 <= d i by apply: dist_positive.
    rewrite ltr_def; apply/andP; split=> //.
    by apply/eqP=> H4; rewrite H4 eq_refl in H2.
  Qed.    

  Lemma expectedValue_nonneg f
        (H : forall x : T, 0 <= f x) :
    0 <= expectedValue f.
  Proof.      
    apply: sumr_ge0=> i _; case H2: (f i == 0).
    { by move: (eqP H2)=> ->; rewrite mulr0. }
    apply: mulr_ge0 => //; apply: dist_positive.
  Qed.    

  Lemma expectedCondValue_nonneg f (p : pred T)
        (H : forall x : T, 0 <= f x) :
    0 <= expectedCondValue f p.
  Proof.
    apply: divr_ge0.
    { apply: sumr_ge0=> i _; case H2: (f i == 0).
      { by move: (eqP H2)=> ->; rewrite mulr0. }
      apply: mulr_ge0 => //; apply: dist_positive. }
    apply: probOf_nonneg.
  Qed.      
End expectedValue.

Section cdf.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Fixpoint cdf_aux (x : T) (l : seq T) : rty :=
    if l is [:: y & l'] then
      if x == y then d y
      else d x + cdf_aux x l'
    else 0.

  Definition cdf (x : T) : rty := cdf_aux x (enum T).

  Fixpoint inverse_cdf_aux (p acc : rty) (cand : option T) (l : seq T)
    : option T :=
    if l is [:: y & l'] then
      if acc > p then cand
      else inverse_cdf_aux p (acc + d y) (Some y) l'
    else cand.

  Definition inverse_cdf (p : rty) : option T :=
    inverse_cdf_aux p 0 None (enum T).
End cdf.  

(** Product distributions *)

Lemma sum_ffunE'
      (aT : finType) (rty : numDomainType) (g : aT -> rty) :
  \sum_t [ffun x => g x] t =
  \sum_t g t.
Proof. by apply: eq_big=> // i _; rewrite ffunE. Qed.

Lemma prod_distr_sum
      (I J : finType) (rty : numDomainType) (F : I -> J -> rty) :
  \prod_i (\sum_j F i j) =
  \sum_(f : {ffun I -> J}) \prod_i F i (f i).
Proof. by apply: bigA_distr_bigA. Qed.

Section product.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable n : nat.
  Variable f : {ffun 'I_n -> dist T rty}.

  Notation type := ({ffun 'I_n -> T}).
  
  Definition prod_pmf : {ffun type -> rty} :=
    finfun (fun p : type => \prod_(i : 'I_n) f i (p i)).

  Lemma prod_pmf_dist :
    dist_axiom (T:=[finType of type]) (rty:=rty) prod_pmf.
  Proof.
    apply/andP; split.
    { rewrite /prod_pmf sum_ffunE'.
      rewrite -(@prod_distr_sum _ _ rty (fun x y => f x y)).
      have H: \prod_(i<n) (\sum_j (f i) j) = \prod_(i<n) 1.
      { apply: congr_big => // i _.
        by rewrite dist_normalized. }
      by rewrite H prodr_const expr1n. }
    apply/forallP => x; rewrite /prod_pmf ffunE.
    by apply: prodr_ge0 => i _; apply: dist_positive.
  Qed.    
  
  Definition prod_dist : dist [finType of type] rty :=
    @mkDist _ _ prod_pmf prod_pmf_dist.
End product.

Section uniform.
  Variable T : finType.
  Variable t0 : T.
  Notation rty := rat.
  
  Definition uniform_dist : {ffun T -> rty} :=
    finfun (fun _ => 1 / #|T|%:R).

  Lemma itern_addr_const n (r : rty) : iter n (+%R r) 0 = r *+ n.  
  Proof. by elim: n r=> // n IH r /=; rewrite IH mulrS. Qed.

  Lemma ffun_lem (r : rty) :
            \sum_(t : T) [ffun => r / #|T|%:R] t
          = \sum_(t : T) r / #|T|%:R.
  Proof. by apply/congr_big=> // i _; rewrite ffunE. Qed.
  
  Lemma uniform_normalized : dist_axiom uniform_dist.
  Proof.
    rewrite /dist_axiom ffun_lem; rewrite big_const itern_addr_const.
    have Hgt0: (#|T| > 0)%N.
    { move: (@enumP T); move/(_ t0)=> H; rewrite cardT.
      move: (mem_enum T t0); rewrite /in_mem /=.
        by case: (enum T).
    }
    have H: #|T| != 0%N.
    { by apply/eqP=> H; rewrite H in Hgt0.
    }
    apply/andP; split.    
    { move: #|T| H=> n.
      rewrite div1r -[_ *+ n]mulr_natl; move/eqP=> H.
      apply/eqP; apply: mulfV=> //; apply/eqP=> H2; apply: H.
      suff: n == 0%N; first by move/eqP=> ->.
      by erewrite <-pnatr_eq0; apply/eqP; apply: H2.
    }
    apply/forallP=> t; rewrite /uniform_dist ffunE.
    apply: divr_ge0=> //. 
    by apply: ler0n.
  Qed.

  Definition uniformDist : dist T [numDomainType of rat] := mkDist uniform_normalized.

  Lemma expectedValue_uniform (f : T -> rty) :
    expectedValue uniformDist f = (\sum_(t : T) (f t)) / #|T|%:R.
  Proof.
    rewrite /expectedValue /uniformDist /= /uniform_dist.
    rewrite mulr_suml; apply/congr_big=> // t _; rewrite ffunE.
    by rewrite -mulrA mul1r mulrC.
  Qed.      
End uniform.

(** Markov's Inequality *)
Section markov.
  Variable T : finType.
  Variable rty : numFieldType.
  Variable a : rty.
  Variable a_gt0 : 0 < a.
  Variable f : T -> rty.
  Variable f_nonneg : forall t, 0 <= f t.
  Variable d : dist T rty.

  Definition PRED := [pred x | f x >= a].
  
  Lemma markov : probOf d PRED <= expectedValue d f / a.
  Proof.
    rewrite /probOf; rewrite ->expectedValue_split with (p:=PRED).
    have H1: 0 <= \sum_(t | ~~ PRED t) d t * f t.
    { apply: sumr_ge0 => i H; apply: mulr_ge0 => //; apply: dist_positive. }
    rewrite ler_pdivl_mulr // mulrC.
    have H2:
      \sum_(t | PRED t) d t * f t
      <= \sum_(t | PRED t) d t * f t + \sum_(t | ~~ PRED t) d t * f t.
    { by rewrite ler_addl. }
    have H3: a * (\sum_(t | PRED t) d t) <= \sum_(t | PRED t) d t * f t.
    { rewrite mulr_sumr; apply: ler_sum => i; rewrite/PRED/= => Hi.
      rewrite mulrC ler_pmul => //; first by apply: dist_positive.
      by apply/ltrW. }
    apply: ler_trans; first by apply: H3.
    apply: H2.
  Qed.     
End markov.

(* R-valued stuff after this point: *)
Require Import QArith Reals Rpower Ranalysis Fourier Lra.

(** An R-valued analogue of the Markov lemma proved above *)
Section markovR.
  Variable T : finType.
  Variable a : R.
  Variable a_gt0 : 0 < a.
  Variable f : T -> R.
  Variable f_nonneg : forall x, 0 <= f x.
  Variable d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Definition probOfR (d : T -> R) (p : pred T) := big_sum (filter p (enum T)) d.
  Definition expValR (d f : T -> R) := big_sum (enum T) (fun x => d x * f x).
  Definition PREDR (x : T) : bool := Rle_lt_dec a (f x).

  Lemma probOfR_le (p q : pred T) : (forall x, p x -> q x) -> probOfR d p <= probOfR d q.
  Proof.
    move => H; rewrite /probOfR.
    apply: big_sum_le2; try solve[apply: filter_uniq; apply: enum_uniq].
    { move => c _; apply: d_nonneg. }
    move => c; rewrite !mem_filter; case/andP => H1 H2; apply/andP; split => //.
    by apply: (H _ H1).
  Qed.
    
  Lemma expValR_ge0 : 0 <= expValR d f.
  Proof.
    rewrite /expValR; elim: (enum T) => /=; try apply: Rle_refl.
    move => x l H; apply: Rplus_le_le_0_compat => //.
    by apply: Rmult_le_pos.
  Qed.

  Lemma expValR_linear g h : expValR d (fun x => g x + h x) = expValR d g + expValR d h.
  Proof.
    rewrite /expValR; elim: (enum T) => /=; first by rewrite Rplus_0_r.
    move => x l ->; rewrite Rmult_plus_distr_l -!Rplus_assoc -[(_ + _) + d x * h x]Rplus_comm.
    by rewrite -Rplus_assoc -[d x * h x + _]Rplus_comm.
  Qed.    

  Lemma expValR_const c g : expValR d (fun x => c * g x) = c * expValR d g.
  Proof.    
    rewrite /expValR; elim: (enum T) => /=; first by rewrite Rmult_0_r.
    move => x l ->; rewrite -Rmult_assoc [d x * _]Rmult_comm Rmult_assoc Rmult_plus_distr_l //.
  Qed.

  Lemma expValR_sumconst c : expValR d (fun x => c) = c.
  Proof.    
    by rewrite /expValR -big_sum_mult_right d_dist Rmult_1_l. 
  Qed.
  
  Lemma expValR_Ropp g : expValR d (fun x => - g x) = - expValR d g.
  Proof.
    rewrite /expValR; elim: (enum T) => /=; first by rewrite Ropp_0.
    move => x l ->; rewrite Ropp_plus_distr; f_equal.
    by rewrite Ropp_mult_distr_r_reverse.
  Qed.    

  Lemma expValR_one : expValR d (fun _ : T => 1) = 1.
  Proof.
    rewrite /expValR.
    have ->: big_sum (enum T) (fun x : T => d x * 1) = big_sum (enum T) (fun x : T => d x).
    { by apply: big_sum_ext => //= x; rewrite Rmult_1_r. }
    apply: d_dist.
  Qed.    
  
  Lemma expValR_split (p : pred T) :
    expValR d f =
    big_sum (filter p (enum T)) (fun x => d x * f x) +
    big_sum (filter (predC p) (enum T)) (fun x => d x * f x).
  Proof. by apply: big_sum_split. Qed.

  Lemma ler_pdivl_mulrR z x y : 0 < z -> x * z <= y -> x <= y / z.
  Proof.
    move => H H2; rewrite /Rdiv.
    have H3: x * z <= (y * /z) * z.
    { rewrite Rmult_assoc Rinv_l; last first.
      { move => Heq; rewrite Heq in H.
        by move: (Rnot_lt0 0); rewrite Rmult_0_r. }
      by rewrite Rmult_1_r. }
    eapply Rmult_le_reg_r; eauto.
  Qed.    
  
  Lemma markovR : probOfR d PREDR <= expValR d f / a.
  Proof.
    rewrite ->expValR_split with (p:=PREDR); rewrite /probOfR.
    apply: ler_pdivl_mulrR => //.
    have H:
      big_sum [seq x <- enum T | PREDR x] d * a <=
      big_sum [seq x <- enum T | PREDR x] (fun x : T => d x * f x).
    { rewrite Rmult_comm -big_sum_scalar; apply: big_sum_le => x Hin.
      rewrite Rmult_comm; apply: Rmult_le_compat => //.
      { by apply: Rlt_le. }
      { by apply: Rle_refl. }
      rewrite mem_filter in Hin; case: (andP Hin); rewrite /PREDR.
      case: (Rle_lt_dec a (f x)) => //. }
    apply: Rle_trans; first by apply: H.
    rewrite -[big_sum _ _]Rplus_0_r Rplus_assoc; apply: Rplus_le_compat_l.
    rewrite Rplus_0_l; apply: big_sum_ge0 => x; rewrite -[0](Rmult_0_l 0).
    move => _; apply: Rmult_le_compat => //; apply: Rle_refl.
  Qed.
End markovR.

Section union_bound.
  Variable T : finType.
  Variable N : nat.
  Variable P : 'I_N -> pred T.
  Variable d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.

  Lemma union_bound :
    probOfR d [pred x | [exists i, P i x]] <= \big[bigops.Rplus/0]_i probOfR d (P i).
  Proof.
    rewrite /probOfR big_sum_sumP.
    have ->:
      \big[bigops.Rplus/0]_i big_sum [seq x <- enum T | P i x] d
    = \big[bigops.Rplus/0]_i \big[bigops.Rplus/0]_(x | P i x) d x.    
    { apply: eq_big => // i _; rewrite big_sum_sumP.
      apply: congr_big => //; rewrite enumT //. }
    rewrite (@exchange_big_dep _ _ _ _ _ _ _ _ _ xpredT) => //.
    rewrite big_mkcond -big_sum_sumP -big_sum_sum.
    have ->:
      big_sum [seq _ <- enum T | true] (fun i : T => if [exists i0, P i0 i] then d i else 0)
    = big_sum (enum T) (fun i : T => if [exists i0, P i0 i] then d i else 0).
    { by apply: big_sum_ext => //=; rewrite filter_predT. }
    apply: big_sum_le => /= c H; case H2: [exists i0, P i0 c].
    { case: (existsP H2) => x Hp; rewrite big_const_seq /=.
      rewrite -size_filter.
      have H3: (0 < size [seq i <- index_enum (ordinal_finType N) | P i c])%coq_nat.
      { apply/ltP; rewrite -has_predT has_filter; apply/eqP.
        have Hin: x \in [seq i <- index_enum (ordinal_finType N) | P i c].
        { rewrite mem_filter; apply/andP; split => //. }
        move: Hin; elim: (index_enum _) => // a l /=.
        case: (P a c) => //. }
      move: H3; case: (size _); first by move/ltP.
      move => n _ /=; rewrite -{1}[d c]Rplus_0_r; apply: Rplus_le_compat_l.
      elim: n => /=; first by apply: Rle_refl.
      move => n IH; apply: Rplus_le_le_0_compat => //. }
    rewrite -big_sum_sumP; apply: big_sum_ge0 => //.
  Qed.    
End union_bound.

(** Relative entropy RE(p||q) 
    NOTE: This definition is nonstandard in that we use natural rather 
    than binary log. *)
Section relative_entropy.
  Variable T : finType.
  Variables p q : T -> R.
  Definition RE := big_sum (enum T) (fun x => p x * ln (p x / q x)).
End relative_entropy.

Module Bernoulli.
Section Bernoulli.
  Variable p : R.
  Variable p_range : 0 <= p <= 1.
  Definition t (b : bool) : R := if b then p else 1 - p.
  Lemma dist : big_sum (enum bool_finType) t = 1.
  Proof.
    rewrite /bool_finType /= /enum_mem /= Finite.EnumDef.enumDef /=.
    by rewrite Rplus_0_r -Rplus_assoc [p + 1]Rplus_comm Rplus_assoc Rplus_opp_r Rplus_0_r.
  Qed.
  Lemma nonneg x : 0 <= t x.
  Proof.
    case: p_range => H1 H2; case: x => //=.
    fourier.
  Qed.
End Bernoulli.
End Bernoulli.

Section relative_entropy_Bernoulli.
  Variables p q : R.
  Variable p_range : 0 <= p <= 1.
  Definition p_dist := Bernoulli.t p.
  Definition q_dist := Bernoulli.t q.

  Definition RE_Bernoulli : R := RE p_dist q_dist.

  Lemma RE_Bernoulli_def :
    RE_Bernoulli = p * ln (p / q) + (1 - p) * ln ((1 - p) / (1 - q)).
  Proof.
    rewrite /RE_Bernoulli/RE.
    have ->: enum bool_finType = [:: true; false] by rewrite enumT Finite.EnumDef.enumDef.
    simpl; rewrite Rplus_0_r //.
  Qed.    
End relative_entropy_Bernoulli.

Section TV_Bernoulli.
  Variable p q : R.
  Notation p_dist := (@p_dist p).
  Notation q_dist := (@q_dist q).

  Definition TV_Bernoulli : R := 
    Rmax (Rabs (p_dist true - q_dist true))
         (Rabs (p_dist false - q_dist false)).

  Lemma TV_Bernoulli_eq : TV_Bernoulli = Rabs (p - q).
  Proof.
    rewrite  /TV_Bernoulli /p_dist /q_dist /=.
    have ->: 1 - p - (1 - q) = q - p by lra.
    rewrite Rabs_minus_sym /Rmax; case: (Rle_dec _ _) => //.
  Qed.
End TV_Bernoulli.

Section markovR_exp.
  Variable T : finType.
  Variable a : R.
  Variable a_gt0 : 0 < a.
  Variable f : T -> R.
  Variable f_nonneg : forall x, 0 <= f x.
  Variable d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.
  
  Lemma markovR_exp :
    probOfR d (fun x => Rle_lt_dec (exp a) (exp (f x))) <=
    exp (- a) * expValR d (fun x => exp (f x)).
  Proof.
    rewrite exp_Ropp Rmult_comm; apply: markovR => //; first by apply: exp_pos_pos.
    rewrite /Rle => x; case: (f_nonneg x) => H.
    { by left; apply: exp_pos_pos. }
    rewrite -H; left; rewrite exp_0; apply: Rlt_0_1.
  Qed.    
End markovR_exp.

Section prodR.
  Variable T : finType.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.  
  Variables d : 'I_m -> T -> R.
  Variable d_dist : forall i, big_sum (enum T) (d i) = 1.
  Variable d_nonneg : forall i x, 0 <= (d i) x.

  Definition prodR : {ffun 'I_m -> T} -> R :=
    fun p => big_product (enum 'I_m) (fun i : 'I_m => d i (p i)).
  
  Lemma prodR_dist : big_sum (enum [finType of {ffun 'I_m -> T}]) prodR = 1.
  Proof.
    rewrite /prodR -big_product_distr_sum.
    have ->:
      big_product (enum (ordinal_finType m))
       (fun i : ordinal_finType m => big_sum (enum T) [eta d i])
    = big_product (enum 'I_m) (fun _ => 1).
    { apply: big_product_ext => //. }
    by rewrite big_product_constant pow1.
  Qed.

  Lemma prodR_sub_dist (i:'I_m) (x:T) :
    \big[Rplus/0]_(p : {ffun 'I_m->T} | p i == x) \big[Rtimes/1]_(j | j!=i) d j (p j) = 1.
  Proof.
    set (F j x := d j x).
    set (P (j:'I_m) := (i!=j)%B).
    set (Q (j:'I_m) (y:T) := if (i==j)%B then (x==y)%B else true).
    have ->:
      \big[Rplus/0]_(p:{ffun 'I_m->T} | p i == x) \big[Rtimes/1]_(j | j != i) F j (p j)
    = \big[Rplus/0]_(p in pfamily x P Q) \big[Rtimes/1]_(j | P j) F j (p j).
    { rewrite /pfamily_mem /= /finfun.family_mem/=/in_mem/=/P/Q.
      apply: eq_big => //= y; rewrite /Q /=.
      { rewrite /in_mem /=; apply/eqP; case Heq: [forall x0, _].
        { move: Heq; move/forallP/(_ i); rewrite /in_mem /=.
          by rewrite /P eq_refl /in_mem/=/in_mem/=; move/eqP => <-. }
        move => Heq2; subst x; move: Heq; move/existsP; case => i'; rewrite /in_mem /=.
        rewrite /P; case Heq: (i == i')%B => /=.
        { by move: (eqP Heq) => ->; move/negP; rewrite eq_refl. }
        by []. }
      by move/eqP => H; rewrite /F; apply: eq_big => // j; rewrite eq_sym. }
    rewrite -(@big_distr_big_dep R 0 1 Rtimes bigops.Rplus _ _ x P Q F).
    have Heq: forall ix, ix!=i -> \big[bigops.Rplus/0]_(j | Q ix j) F ix j = 1.
    { move => ix /eqP Hneq; rewrite /F/Q/=; case Heq: (i == ix)%B.
      { by move: (eqP Heq) => Heq'; subst ix. }
      by rewrite -big_sum_sum d_dist. }
    have ->:
      \big[Rtimes/1]_(i0 | P i0) \big[bigops.Rplus/0]_(j | Q i0 j) F i0 j
    = \big[Rtimes/1]_(i0:'I_m | P i0) 1.
    { apply: eq_big => //= ix; rewrite /F/P/Q; case: (i==ix)%B => // _.
      by rewrite -big_sum_sum d_dist. }
    rewrite big_const; elim: (card _) => //= n ->; rewrite Rmult_1_l //.
  Qed.

  Lemma prodR_nonneg p : 0 <= prodR p.
  Proof. by apply: big_product_ge0. Qed.

  Lemma prodR_split i p :
    prodR p =
    d i (p i) *
    big_product (filter (predC (pred1 i)) (enum 'I_m)) (fun j => d j (p j)).
  Proof.
    have ->:
      d i (p i) * big_product [seq x <- enum 'I_m | predC (pred1 i) x] (fun j => d j (p j)) =
      big_product (filter (pred1 i) (enum 'I_m)) (fun j => d j (p j)) *
      big_product (filter (predC (pred1 i)) (enum 'I_m)) (fun j => d j (p j)).
    { f_equal; rewrite (big_product_split _ _ (pred1 i)) -[d i (p i)]Rmult_1_r; f_equal.
      { have ->: [seq x <- [seq x <- enum 'I_m | (pred1 i) x] | (pred1 i) x] = [:: i].
        { rewrite filter_id filter_pred1_uniq //; first by apply: enum_uniq.
          rewrite mem_enum => //. }
        by simpl; rewrite Rmult_1_r. }
      have ->: [seq x <- [seq x <- enum 'I_m | (pred1 i) x] | (predC (pred1 i)) x] = [::].
      { rewrite filter_pred1_uniq => //.
        { by simpl; rewrite eq_refl. }
        by apply: enum_uniq.
        by rewrite mem_enum. }
      by []. }
    rewrite /prodR -big_product_split //.
  Qed.
  
  Lemma prodR_marginal f i :
    big_sum (enum {ffun 'I_m -> T}) (fun p0 => prodR p0 * f i (p0 i)) =
    big_sum (enum T) (fun x : T => d i x * f i x).
  Proof.
    have ->:
      big_sum (enum {ffun 'I_m -> T}) (fun p0 => prodR p0 * f i (p0 i)) 
    = big_sum (enum {ffun 'I_m -> T}) (fun p0 => 
        (d i (p0 i) *
         big_product (filter (predC (pred1 i)) (enum 'I_m)) (fun j => d j (p0 j))) * 
        f i (p0 i)).
    { apply: big_sum_ext => // => p; rewrite (prodR_split i) //. }
    rewrite 2!big_sum_sum -(marginal_unfoldR i).
    set (F (x:T) y := 
           d i (y i) *
           big_product [seq x <- enum 'I_m | (predC (pred1 i)) x]
             (fun j : ordinal_finType m => d j (y j)) *
           f i (y i)).
    change (\big[bigops.Rplus/0]_(p:[finType of (T*{ffun 'I_m->T})] | p.2 i == p.1) F p.1 p.2 =
            \big[bigops.Rplus/0]_i0 (d i i0 * f i i0)).
    set (P (x:T) := predT x).
    set (Q (x:T) (y:{ffun 'I_m->T}) := if x == y i then true else false).
    have ->:
      \big[bigops.Rplus/0]_(p:[finType of (T*{ffun 'I_m->T})] | p.2 i == p.1) F p.1 p.2
    = \big[bigops.Rplus/0]_(p:[finType of (T*{ffun 'I_m->T})]
                           | P p.1 && Q p.1 p.2) F p.1 p.2.
    { apply: eq_big => // x /=; rewrite /Q eq_sym; case: (x.1 == x.2 i)%B => //. }
    rewrite -(@pair_big_dep R 0 Rplus_com_law T [finType of {ffun 'I_m -> T}] P Q F).
    rewrite /F /P /Q /=; apply: eq_big => // k _.
    have ->:
      \big[Rplus/0]_(j:[finType of {ffun 'I_m ->T}] | if k == j i then true else false)
        (d i (j i) * big_product [seq x <- enum 'I_m | x != i] (fun j0 : 'I_m => d j0 (j j0)) * f i (j i)) 
    = \big[Rplus/0]_(j:[finType of {ffun 'I_m->T}] | if k == j i then true else false)
        (d i k * big_product [seq x <- enum 'I_m | x != i] (fun j0 : 'I_m => d j0 (j j0)) * f i k).
    { apply: eq_big => // ix.
      case Heq: (k == ix i)%B => // _; move: (eqP Heq) => <- //. }
    rewrite -big_sum_sumP.
    set (C := d i k).
    set (D := f i k).
    set (cs := [seq x <- _ | _]).
    clear F; set (F i0 := C * big_product [seq x <- enum 'I_m | x != i] (fun j0 : 'I_m => d j0 (i0 j0)) * D).
    change (big_sum cs F = C * D).
    set (G i0 := big_product [seq x <- enum 'I_m | x != i] (fun j0 : 'I_m => d j0 (i0 j0))).
    have ->:
      big_sum cs (fun i0 : [finType of {ffun 'I_m -> T}] => F i0)
    = big_sum cs (fun i0 : [finType of {ffun 'I_m -> T}] => (C*D) * G i0).
    { by apply: big_sum_ext => // x; rewrite /F /G Rmult_assoc [_ * D]Rmult_comm -Rmult_assoc. }
    rewrite big_sum_scalar -[C * D]Rmult_1_r; f_equal; first by rewrite Rmult_1_r.
    rewrite /G /cs /=; clear G cs; rewrite big_sum_sumP.
    have ->:
      \big[bigops.Rplus/0]_(i0:[finType of {ffun 'I_m->T}] | if k == i0 i then true else false)
       big_product [seq x <- enum 'I_m | x != i] (fun j0 : 'I_m => d j0 (i0 j0)) 
    = \big[bigops.Rplus/0]_(i0:[finType of {ffun 'I_m->T}] | if k == i0 i then true else false)
       \big[bigops.Rtimes/1]_(x | x != i) d x (i0 x).
    { apply: eq_big => // x _; rewrite big_product_prodP //. }
    have ->:
      \big[bigops.Rplus/0]_(i0:{ffun 'I_m->T} | if k == i0 i then true else false)
        \big[Rtimes/1]_(x | x != i) d x (i0 x) =
      \big[bigops.Rplus/0]_(i0:{ffun 'I_m->T} | i0 i == k) \big[Rtimes/1]_(x | x != i) d x (i0 x).
    { apply: eq_big => // x; rewrite eq_sym; case: (x i == k)%B => //. }
    apply: prodR_sub_dist.
  Qed.
End prodR.    

Section convolution.
  Variable T : finType.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.
  Variables d : 'I_m -> T -> R.
  Variable d_dist : forall i, big_sum (enum T) (d i) = 1.
  Variable d_nonneg : forall i x, 0 <= (d i) x.
  Variable f : 'I_m -> T -> R.
  Variable f_range : forall i x, 0 <= f i x <= 1.
  
  (** [conv r]: the probability that r is less than or equal to the average 
      sum of the realizations of the random variables [f i] as drawn from 
      distributions [d i]. *)
  Definition conv (r : R) :=
    probOfR (prodR d) (fun p => Rle_lt_dec r ((/INR m) * big_sum (enum 'I_m) (fun i => f i (p i)))).
End convolution.  

Section general_lemmas.
  Variable T : finType.
  Variables d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.
  
  Lemma probOfR_q_exp g h c (Hlt : 0 < c) :
    probOfR d (fun x => Rle_lt_dec (g x) (h x)) =
    probOfR d (fun x => Rle_lt_dec (exp (c * g x)) (exp (c * h x))).
  Proof.
    apply: big_sum_ext => //; apply/eq_filter => x.
    move: (exp_increasing (c * g x) (c * h x)) => H.
    case: (Rle_lt_dec (g x) (h x)).
    { move => H2; case: (Rle_lt_dec (exp (c * g x)) (exp (c * h x))) => // H3.
      { case: H2.
        { move => H4; move: (H (Rfourier_lt _ _ _ H4 Hlt)) => H5.
          by move: (Rlt_asym _ _ H5). }
        move => H4; elimtype False; rewrite ->H4 in H3; clear H4.
        by move: (Rlt_asym _ _ H3). }}
    move => H2; case: (Rle_lt_dec (exp (c * g x)) (exp (c * h x))) => // H3.
    move: (exp_increasing _ _ (Rfourier_lt _ _ _ H2 Hlt)) => H4; case: H3.
    { by move => H5; move: (Rlt_asym _ _ H4). }
    by move => H5; elimtype False; rewrite H5 in H4; move: (Rlt_asym _ _ H4).
  Qed.
End general_lemmas.
