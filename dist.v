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
Require Import QArith Reals Rpower Ranalysis Fourier.

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
    apply: Rmult_le_compat => //; apply: Rle_refl.
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
  Definition p_dist := Bernoulli.t p.
  Definition q_dist := Bernoulli.t q.  

  Definition RE_Bernoulli : R := RE p_dist q_dist.
End relative_entropy_Bernoulli.

Section relative_entropy_lemmas.
  Variables p eps : R.
  Variable p_range : 0 <= p <= 1.
  Variable eps_range : 0 < eps <= 1 - p.
  
  Lemma RE_bounded_below : RE_Bernoulli (p + eps) p >= 2 * eps^2.
  Proof.
  Admitted.  
End relative_entropy_lemmas.

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

Section chernoff_geq.
  Variable T : finType.
  Variables d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.

  (* The distribution function corresponding to m samples of d *)
  Definition d_prod (_ : 'I_m) := d.
  
  Variable f : 'I_m -> T -> R.
  Variable f_range : forall i x, 0 <= f i x <= 1.
  Definition identically_distributed := forall i j : 'I_m, expValR d (f i) = expValR d (f j).  
  Variable f_identically_distributed : identically_distributed.
  (* Mutual independence of the f's: 
     -The expected value of the product of a function of the f_i's is equal to 
      the product of the expected value of the same function of the f_i's.
     -NOTE: this is a stronger assumption than pairwise independence. *)
  Definition mutual_independence :=
    forall g : R -> R, 
    expValR (prodR d_prod) (fun p => big_product (enum 'I_m) (fun i => g (f i (p i)))) =
    big_product (enum 'I_m) (fun i => expValR (prodR d_prod) (fun p => g (f i (p i)))).
  Variable f_independent : mutual_independence.

  Definition mR := INR m.
  Lemma mR_gt0 : (0 < mR)%R.
  Proof. by apply: lt_0_INR; apply/ltP. Qed.
  Lemma mR_neq0 : (mR <> 0)%R.
  Proof. by move: mR_gt0 => H H2; rewrite H2 in H; move: (Rlt_asym _ _ H). Qed.
  
  Definition i0 : 'I_m := Ordinal m_gt0.
  Definition p := expValR d (f i0).
  Variable p_nontrivial : 0 < p < 1. (*required to construct lambda_min*)
  
  Lemma expVal_independence c :
    expValR (prodR d_prod) (fun p => big_product (enum 'I_m) (fun i => exp (c * f i (p i)))) =
    big_product (enum 'I_m) (fun i => expValR (prodR d_prod) (fun p => exp (c * f i (p i)))).
  Proof.
    set (g x := exp (c * x)).
    change
      (expValR (prodR d_prod)
        (fun p => big_product (enum 'I_m) (fun i : ordinal_finType m => g (f i (p i)))) =
      big_product (enum 'I_m)
        (fun i : ordinal_finType m => expValR (prodR d_prod) (fun p => g (f i (p i))))).
    by rewrite f_independent.
  Qed.

  Variable eps : R.
  Variable eps_gt0 : 0 < eps.
  Variable eps_lt_1p : eps < 1 - p.
  (*This above assumption, which is required to show that lambda_min > 0, 
    is strange in the sense that it limits the values epsilon we can choose 
    to (0, 1-p).*)
  
  Definition q := p + eps.

  Lemma lt_p_q : p < q.
  Proof.
    rewrite /q; rewrite -[p]Rplus_0_r.
    have ->: p + 0 + eps = p + eps by rewrite Rplus_0_r.
    apply: Rplus_le_lt_compat => //.
    apply: Rle_refl.
  Qed.

  Lemma lt_p_p2_eps : 0 < p - (p*(p + eps)).
  Proof.
    apply: Rlt_Rminus; rewrite Rmult_plus_distr_l.
    apply: (@Rlt_le_trans _ (p*p + p*(1-p)) _).
    { apply: Rplus_lt_compat_l.
      apply Rmult_lt_compat_l => //.
      by case: p_nontrivial. }
    rewrite Rmult_plus_distr_l Rmult_1_r [p + _]Rplus_comm -Rplus_assoc.
    rewrite -Ropp_mult_distr_r Rplus_opp_r Rplus_0_l; apply: Rle_refl. 
  Qed.
  
  Lemma p_leq1 : p <= 1.
  Proof.
    rewrite /p/expValR -d_dist; apply: big_sum_le; last first.
    move => c Hin; rewrite -[d c]Rmult_1_r.
    have ->: d c * 1 * f i0 c = d c * f i0 c by rewrite Rmult_1_r.
    apply: Rmult_le_compat => //.
    { by case: (f_range i0 c). }
    { by apply: Rle_refl. }
    by case: (f_range i0 c).
  Qed.
  
  Section LAMBDA.
  Variable lambda : R.
  Variable lambda_gt0 : 0 < lambda.
  
  Lemma expValR_linear_approx : 
    exp (-lambda * mR * q) *
    big_product (enum 'I_m)
      (fun i => expValR (prodR d_prod) (fun p => exp (lambda * f i (p i)))) <=
    exp (-lambda * mR * q) *
    big_product (enum 'I_m)
      (fun i => expValR (prodR d_prod) (fun p => 1 - f i (p i) + f i (p i) * exp lambda)).
  Proof.
    apply: Rmult_le_compat_l; first by left; apply: exp_pos.
    apply: big_product_le.
    { move => c Hin; apply: expValR_ge0; first by left; apply: exp_pos.
      by apply: prodR_nonneg. }
    { move => i Hin; apply: expValR_ge0 => p.
      { rewrite -[0]Rplus_0_l; apply: Rplus_le_compat.
        { case: (f_range i (p i)) => _ Hleq; fourier. }
        case: (f_range i (p i)) => H _; rewrite -[0](Rmult_0_r 0).
        apply: Rmult_le_compat; try solve[apply: Rle_refl|by []].
        left; apply: exp_pos. }
      by apply: prodR_nonneg. }
    move => c Hin; apply: big_sum_le => x Hinx; apply: Rmult_le_compat_l.
    { by apply: prodR_nonneg. }
    by apply: exp_upper_01.
  Qed.

  Lemma expValR_simpl i :
    expValR (prodR d_prod) (fun p => 1 - f i (p i) + f i (p i) * exp lambda) =
    1 - p + p * exp lambda.
  Proof.
    rewrite 2!expValR_linear/expValR => //.
    have ->: big_sum (enum {ffun 'I_m -> T}) (fun p => prodR d_prod p * 1)
           = big_sum (enum {ffun 'I_m -> T}) (prodR d_prod).
    { by apply: big_sum_ext => // x; apply: Rmult_1_r. }
    rewrite prodR_dist => //.
    have ->:
       big_sum (enum {ffun 'I_m -> T}) (fun p => prodR d_prod p * - f i (p i)) =
      -big_sum (enum {ffun 'I_m -> T}) (fun p => prodR d_prod p * f i (p i)).
    { rewrite -big_sum_nmul; apply: big_sum_ext => // x.
      by rewrite Ropp_mult_distr_r_reverse. }
    have ->:
       big_sum (enum {ffun 'I_m -> T}) (fun p => prodR d_prod p * (f i (p i) * exp lambda)) =
       big_sum (enum {ffun 'I_m -> T}) (fun p => exp lambda * (prodR d_prod p * f i (p i))).
    { by apply big_sum_ext => // x; rewrite -Rmult_assoc Rmult_comm. }
    f_equal.
    { rewrite /p/expValR/Rminus; f_equal; f_equal => /=; rewrite /d_prod /=.
      rewrite prodR_marginal => //.
      apply: f_identically_distributed. }
    rewrite big_sum_scalar Rmult_comm; f_equal.
    rewrite /p/expValR/Rminus; f_equal; f_equal => /=; rewrite /d_prod /=.
    rewrite prodR_marginal => //.
    apply: f_identically_distributed. 
  Qed.    
  
  Lemma big_product_expValR_simpl_aux : 
    big_product
      (enum 'I_m)
      (fun i => expValR (prodR d_prod) (fun p => 1 - f i (p i) + f i (p i) * exp lambda)) =
    big_product (enum 'I_m) (fun i => 1 - p + p * exp lambda).
  Proof. by apply: big_product_ext => // p; rewrite expValR_simpl. Qed.
    
  Lemma big_product_expValR_simpl :
    big_product
      (enum 'I_m)
      (fun i => expValR (prodR d_prod) (fun p => 1 - f i (p i) + f i (p i) * exp lambda)) =
    (1 - p + p * exp lambda) ^ m.
  Proof. by rewrite big_product_expValR_simpl_aux big_product_constant size_enum_ord. Qed.  

  Definition phi := ln (exp (-lambda*q) * (1 - p + p * exp lambda)).

  Lemma one_minus_p_gt0 : p<>1 -> 0 < 1 - p.
  Proof.
    by move => p_neq1; move: p_leq1; case => H; try fourier.
  Qed.
  
  Lemma one_minus_p_etc_gt0 : 0 < 1 - p + p * exp lambda.
  Proof.
    case: (Req_dec p 1).
    { move => ->; move: (exp_pos lambda) => H; fourier. }
    move => p_neq1; move: (one_minus_p_gt0 p_neq1) => H.
    apply: Rplus_lt_le_0_compat => //.
    apply: Rmult_le_pos.
    { by apply: expValR_ge0 => x; case: (f_range i0 x). }
    left; apply: exp_pos.
  Qed.    
  
  Lemma phi_simpl :
    exp (phi * mR) = exp (-lambda * mR * q) * (1 - p + p * exp lambda) ^ m.
  Proof.
    rewrite /phi ln_mult; last first.
    { apply: one_minus_p_etc_gt0. }
    { apply: exp_pos. }
    rewrite ln_exp Rmult_plus_distr_r exp_plus; f_equal.
    { by rewrite Rmult_assoc [q * mR]Rmult_comm Rmult_assoc. }
    rewrite exp_mult exp_ln => //.
    apply: one_minus_p_etc_gt0. 
  Qed.

  (** The probability that phat is greater than or equal to q: *)
  Definition phat_ge_q : R := conv (fun _ => d) f q.
  
  Lemma probOfR_phat_q :
    phat_ge_q <=
    exp (-lambda * mR * q) *
    big_product (enum 'I_m)
      (fun i => expValR (prodR d_prod) (fun p => exp (lambda * f i (p i)))).
  Proof.
    rewrite -expVal_independence /phat_ge_q /conv.
    have H: 0 < lambda * mR.
    { apply: Rmult_lt_0_compat => //; apply: mR_gt0. }
    rewrite (probOfR_q_exp _ _ _ H); apply: Rle_trans; [apply markovR_exp|].
    { apply: Rmult_lt_0_compat => //.
      rewrite /q/p; rewrite -(Rplus_0_r 0); apply: Rplus_le_lt_compat => //.
      apply: expValR_ge0 => //.
      by move => x; case: (f_range i0 x). }
    { move => x; rewrite -(Rmult_0_r 0); apply: Rmult_le_compat; try apply: Rle_refl.
      { by left. }
      apply: Rmult_le_pos.
      { rewrite -[/INR m]Rmult_1_l.
        apply: Rle_mult_inv_pos; try fourier.
        by apply: lt_0_INR; apply/ltP. }
      by apply: big_sum_ge0 => x0; case: (f_range x0 (x x0)). }
    { move => x; apply: prodR_nonneg => //. }
    have ->: -(lambda * mR * q) = -lambda * mR * q.
    { by rewrite 2!Ropp_mult_distr_l. }
    apply Rmult_le_compat_l; first by left; apply: exp_pos.
    apply: big_sum_le => c H2; apply: Rmult_le_compat_l.
    { apply: prodR_nonneg => //. }
    have ->:
      lambda * mR * (/mR * big_sum (enum 'I_m) (fun i => f i (c i)))
    = lambda * big_sum (enum 'I_m) (fun i => f i (c i)).
    { rewrite Rmult_assoc -[mR * _]Rmult_assoc Rinv_r; last first.
      { apply: mR_neq0. }
      rewrite Rmult_1_l //. }
    rewrite big_sum_mult_left -big_product_exp_sum; apply: Rle_refl.
  Qed.

  Lemma probOfR_phat_q_bound : 
    phat_ge_q <= 
    exp (-lambda * mR * q) *
    big_product (enum 'I_m)
      (fun i => expValR (prodR d_prod) (fun p => 1 - f i (p i) + f i (p i) * exp lambda)).
  Proof.
    apply: Rle_trans; first by apply: probOfR_phat_q.
    apply: expValR_linear_approx.
  Qed.
  
  Lemma chernoff0 : phat_ge_q <= exp (phi * mR).
  Proof.
    apply: Rle_trans; first by apply: probOfR_phat_q_bound.
    rewrite big_product_expValR_simpl phi_simpl; f_equal; apply: Rle_refl.
  Qed.
  End LAMBDA.  

  Definition lambda_min := ln ((q * (1 - p)) / ((1 - q) * p)).

  Lemma lambda_min_gt0 : 0 < lambda_min.
  Proof.
    apply: exp_lt_inv; rewrite exp_0 /lambda_min.
    have Hlt: 1 < q * (1 - p) / ((1 - q) * p).
    { rewrite Rmult_minus_distr_l Rmult_1_r.
      rewrite [(1-q)*p]Rmult_comm Rmult_minus_distr_l Rmult_1_r.
      rewrite Rmult_comm /q; move: lt_p_p2_eps; move: (p*(p+eps)) => r H.
      apply: (Rmult_lt_reg_r (p-r)) => //.
      rewrite Rmult_1_l Rmult_assoc Rinv_l; last first.
      { move => H2; rewrite H2 in H; apply: (Rlt_irrefl _ H). }
      rewrite Rmult_1_r; apply: Rplus_lt_compat_r; fourier. }
    rewrite exp_ln => //.
    apply: Rlt_trans; last by apply: Hlt.
    fourier.
  Qed.    
  
  Lemma phi_lambda_min : phi lambda_min = -(RE (Bernoulli.t (p + eps)) (Bernoulli.t p)).
  Proof.
    rewrite /phi/lambda_min/RE exp_ln.
  Admitted.

  Lemma chernoff1 : phat_ge_q <= exp (-(RE (Bernoulli.t (p + eps)) (Bernoulli.t p)) * mR).
  Proof.
    rewrite -phi_lambda_min; apply: chernoff0.
    by apply: lambda_min_gt0.
  Qed.    

  Lemma chernoff_geq : phat_ge_q <= exp (-2%R * eps^2 * mR).
  Proof.
    apply: Rle_trans; first by apply: chernoff1.
    rewrite -3!Ropp_mult_distr_l !exp_Ropp; apply: Rinv_le_contravar.
    { apply: exp_pos. }
    have H: (RE_Bernoulli (p + eps) p >= 2%R * eps^2).
    { apply: RE_bounded_below.
      { case: p_nontrivial => H1 H2.
        split; apply: Rlt_le => //. }
      split => //.
      by apply: Rlt_le. }
    case: H => H2.
    { left; apply: exp_increasing; simpl.
      rewrite -!Rmult_assoc; apply: (Rmult_lt_compat_r mR).
      { apply: mR_gt0. }
      apply: Rgt_lt.
      by rewrite /RE_Bernoulli/p_dist/q_dist/= -!Rmult_assoc in H2. }
    rewrite /RE_Bernoulli/p_dist/q_dist in H2; rewrite H2.
    apply: Rle_refl.
  Qed.
End chernoff_geq.

Section chernoff_leq.
  Variable T : finType.
  Variables d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.

  Notation d_prod := (@d_prod T d m).
  
  Variable f : 'I_m -> T -> R.
  Variable f_range : forall i x, 0 <= f i x <= 1.
  Variable f_identically_distributed : identically_distributed d f.
  Variable f_independent : mutual_independence d f.

  Definition f_neg (i : 'I_m) (t : T) := 1 - f i t.

  Lemma f_neg_range : forall i x, 0 <= f_neg i x <= 1.
  Proof. move => i x; case: (f_range i x) => H1 H2; split; rewrite /f_neg; fourier. Qed.
  Lemma f_neg_identically_distributed : identically_distributed d f_neg.
  Proof.
    move => i j; rewrite /f_neg; move: (f_identically_distributed i j) => H.
    rewrite 2!expValR_linear; f_equal.
    by rewrite 2!expValR_Ropp H.
  Qed.
  Lemma f_neg_independent : mutual_independence d f_neg.
  Proof. by move => g; rewrite (f_independent (fun x => g (1 - x))). Qed.

  Variable eps : R.
  Variable eps_gt0 : 0 < eps.
  Variable eps_lt_1p : eps < 1 - p d m_gt0 f_neg.
  Variable p_nontrivial : 0 < p d m_gt0 f < 1. 
  
  Definition p_neg := p d m_gt0 f_neg.

  Lemma p_neg_one_minus_p : p_neg = 1 - p d m_gt0 f.
  Proof.
    rewrite /p_neg /p /f_neg; rewrite expValR_linear expValR_Ropp /Rminus; f_equal.
    apply: expValR_one => //.
  Qed.    
  
  Lemma p_neg_nontrivial : 0 < p_neg < 1.
  Proof. rewrite p_neg_one_minus_p; case: p_nontrivial => H1 H2; split; fourier. Qed.
  
  Lemma chernoff_leq : phat_ge_q d m_gt0 f_neg eps <= exp (-2%R * eps^2 * mR m).
  Proof.
    apply: chernoff_geq => //.
    { apply: f_neg_range. }
    { apply: f_neg_identically_distributed. }
    { apply: f_neg_independent. }
    { apply: p_neg_nontrivial. }
  Qed.
End chernoff_leq.

Section chernoff.
  Variable T : finType.
  Variables d : T -> R.
  Variable d_dist : big_sum (enum T) d = 1.
  Variable d_nonneg : forall x, 0 <= d x.
  Variable m : nat.
  Variable m_gt0 : (0 < m)%nat.

  Notation d_prod := (@d_prod T d m).
  
  Variable f : 'I_m -> T -> R.
  Variable f_range : forall i x, 0 <= f i x <= 1.
  Variable f_identically_distributed : identically_distributed d f.
  Variable f_independent : mutual_independence d f.

  Variable eps delt : R.
  Variable eps_gt0 : 0 < eps.
  Variable delt_gt0 : 0 < delt.
  (*NOTE: weird assumptions, required (?) to prove \lambda_min > 0*)
  Variable eps_lt_p : eps < p d m_gt0 f.  
  Variable delt_lt_1p : delt < 1 - p d m_gt0 f.
  (*END: weird assumptions*)
  Variable p_nontrivial : 0 < p d m_gt0 f < 1. 

  Definition min_eps_delt := Rmin eps delt.

  Lemma Rle_0_min_eps_delt : 0 <= min_eps_delt.
  Proof. by rewrite /min_eps_delt /Rmin; case: (Rle_dec _ _) => H; apply: Rlt_le. Qed.

  Lemma Rlt_min_eps_delt_delt : min_eps_delt <> delt -> min_eps_delt < delt.
  Proof. by rewrite /min_eps_delt /Rmin; case: (Rle_dec _ _); first by case. Qed.

  Lemma Rlt_min_eps_delt_eps : min_eps_delt <> eps -> min_eps_delt < eps.
  Proof.
    rewrite /min_eps_delt /Rmin; case: (Rle_dec _ _) => //.
    move/Rnot_le_gt => H1 H2; fourier.
  Qed.    
  
  Lemma Rle_exp_delt_min : exp (- (2) * delt ^ 2 * mR m) <= exp (- (2) * min_eps_delt ^ 2 * mR m).
  Proof.    
    rewrite !Ropp_mult_distr_l_reverse 2!exp_Ropp; apply: Rinv_le_contravar.
    { apply: exp_pos. }
    case: (Req_dec (exp (2 * min_eps_delt ^ 2 * mR m)) (exp (2 * delt ^ 2 * mR m))).
    { by move => ->; apply: Rle_refl. }
    move => Hneq; left; apply: exp_increasing; apply: Rmult_lt_compat_r; first by apply: mR_gt0.
    apply: Rmult_lt_compat_l; first by fourier.
    rewrite -!tech_pow_Rmult /= 2!Rmult_1_r; apply: Rmult_le_0_lt_compat.
    { apply: Rle_0_min_eps_delt. }
    { apply: Rle_0_min_eps_delt. }      
    { by apply: Rlt_min_eps_delt_delt => Heq; rewrite Heq in Hneq; apply: Hneq. }
    by apply: Rlt_min_eps_delt_delt => Heq; rewrite Heq in Hneq; apply: Hneq.
  Qed.    

  Lemma Rle_exp_eps_min : exp (- (2) * eps ^ 2 * mR m) <= exp (- (2) * min_eps_delt ^ 2 * mR m).
  Proof.    
    rewrite !Ropp_mult_distr_l_reverse 2!exp_Ropp; apply: Rinv_le_contravar.
    { apply: exp_pos. }
    case: (Req_dec (exp (2 * min_eps_delt ^ 2 * mR m)) (exp (2 * eps ^ 2 * mR m))).
    { by move => ->; apply: Rle_refl. }
    move => Hneq; left; apply: exp_increasing; apply: Rmult_lt_compat_r; first by apply: mR_gt0.
    apply: Rmult_lt_compat_l; first by fourier.
    rewrite -!tech_pow_Rmult /= 2!Rmult_1_r; apply: Rmult_le_0_lt_compat.
    { apply: Rle_0_min_eps_delt. }
    { apply: Rle_0_min_eps_delt. }      
    { by apply: Rlt_min_eps_delt_eps => Heq; rewrite Heq in Hneq; apply: Hneq. }
    by apply: Rlt_min_eps_delt_eps => Heq; rewrite Heq in Hneq; apply: Hneq.
  Qed.    
  
  Lemma chernoff_aux1 :
    phat_ge_q d m_gt0 f delt + phat_ge_q d m_gt0 (f_neg f) eps <=
    2 * exp (-2%R * min_eps_delt^2 * mR m).
  Proof.
    rewrite double; apply: Rplus_le_compat.
    { apply: Rle_trans; [apply: chernoff_geq => //|]; apply: Rle_exp_delt_min. }
    apply: Rle_trans; [apply: chernoff_leq => //|]; last first.
    { apply: Rle_exp_eps_min. }
    rewrite -p_neg_one_minus_p /p_neg => //.
    have ->: p d m_gt0 (f_neg (T:=T) (f_neg (T:=T) f)) = p d m_gt0 f.
    { rewrite /p/expValR; apply: big_sum_ext => // x; f_equal.
      by rewrite /f_neg /Rminus Ropp_minus_distr' Rplus_comm Rplus_assoc Rplus_opp_l Rplus_0_r. }
    by apply: eps_lt_p.
  Qed.

  (*This bound unifies epsilon=delta*)
  Lemma chernoff_aux2 (Heq : eps = delt) :
    phat_ge_q d m_gt0 f eps + phat_ge_q d m_gt0 (f_neg f) eps <=
    2 * exp (-2%R * eps^2 * mR m).
  Proof.
    have Heq2: eps = min_eps_delt.
    { rewrite /min_eps_delt/Rmin; subst delt; case: (Rle_dec _ _) => //. }
    rewrite {3}Heq2; apply: Rle_trans; last by apply: chernoff_aux1.
    by rewrite Heq; apply: Rle_refl.
  Qed.
  
  Definition p_hat x := / (mR m) * big_sum (enum 'I_m) (fun i => f i (x i)).
  Definition p_exp := p d m_gt0 f.
  
  Lemma chernoff (Heq : eps = delt) :
    probOfR (prodR (fun _ => d)) (fun x => Rle_lt_dec eps (Rabs (p_exp - p_hat x))) <=
    2 * exp (-2%R * eps^2 * mR m).
  Proof.
    apply: Rle_trans; last by apply: (chernoff_aux2 Heq).
    rewrite /phat_ge_q/conv/probOfR/q/= 3!big_sum_sumP; clear delt delt_gt0 delt_lt_1p Heq.
    rewrite big_mkcond.
    set (b1 := \big[bigops.Rplus/0]_(i | Rle_lt_dec _ _) _).
    set (b2 := \big[bigops.Rplus/0]_(i | Rle_lt_dec _ _) _).
    have ->: b1 = \big[bigops.Rplus/0]_(i:{ffun 'I_m->T})
       (if is_left (Rle_lt_dec (p (T:=T) d m_gt0 f + eps)
                               (/ INR m * big_sum (enum 'I_m) (fun i1 : 'I_m => f i1 (i i1))))
        then prodR (T:=T) (fun _ : 'I_m => d) i else 0).
    { by rewrite /b1 big_mkcond. }
    have ->: b2 = \big[bigops.Rplus/0]_(i:{ffun 'I_m->T})
       (if is_left (Rle_lt_dec (p (T:=T) d m_gt0 (f_neg (T:=T) f) + eps)
                               (/ INR m * big_sum (enum 'I_m) (fun i1 : 'I_m => f_neg (T:=T) f i1 (i i1))))
        then prodR (T:=T) (fun _ : 'I_m => d) i else 0).
    { by rewrite /b2 big_mkcond. }
    clear b1 b2.
    set (b1 := \big[bigops.Rplus/0]_i (if _ then _ else _)).
    set (b2 := \big[bigops.Rplus/0]_i (if _ then _ else _)).
    set (b3 := \big[bigops.Rplus/0]_i (if _ then _ else _)).
    have ->: b2 + b3 = bigops.Rplus b2 b3 by [].
    rewrite /b2 /b3 -big_split /b1 -!big_sum_sumP; apply: big_sum_le => x /= Hin.
    set (dP := prodR _); case: (Rle_lt_dec _ _) => Hle /=; last first.
    { apply: Rplus_le_le_0_compat.
      { case: (is_left _); [by apply: prodR_nonneg |fourier]. }
      case: (is_left _); [by apply: prodR_nonneg |fourier]. }
    (*have: eps <= |p-p_hat|*)
    case: (Rle_lt_dec p_exp (p_hat x)); last first => Hle2.
    { (*Case 1: p_hat < p*)
      have Hle3: eps <= p_exp - p_hat x.
      { move: Hle; rewrite Rabs_minus_sym /Rabs; case: (Rcase_abs _) => //= Hx Hy; fourier. }
      have Hle4: p_hat x + eps <= p_exp by fourier.
      case: (Rle_lt_dec (p _ _ f + _) _) => Hle5 /=.
      { rewrite -{1}[dP x]Rplus_0_l; apply: Rplus_le_compat; first by apply: prodR_nonneg.
        case: (Rle_lt_dec _ _) => /= y; [fourier|].
        exfalso; rewrite /p_hat/mR/p_exp in Hle4; move: Hle4 Hle5.
        move: (p _ _ _) => X; move: (/_ * _) => Y => H1 H2; fourier. }
      rewrite Rplus_0_l; case: (Rle_lt_dec (_ + _)) => /= Hle6; first by apply: Rle_refl.
      have Hle7:
        / INR m * big_sum (enum 'I_m) (fun i1 : 'I_m => f_neg (T:=T) f i1 (x i1)) <
        p_neg (T:=T) d m_gt0 f + eps.
      { apply: Hle6. } clear Hle6.
      exfalso; rewrite p_neg_one_minus_p in Hle7 => //.
      have H8: p_hat x < p (T:=T) d m_gt0 f + eps by []. clear Hle5.
      have H9: 1 - p_hat x < 1 - p (T:=T) d m_gt0 f + eps.
      { apply: Rle_lt_trans; last by apply: Hle7.
        rewrite /p_hat /f_neg big_sum_plus big_sum_nmul big_sum_constant size_enum_ord.
        rewrite Rmult_1_r Rmult_plus_distr_l Rinv_l; last first.
        { move => Heq; move: (mR_gt0 m_gt0); rewrite /mR Heq => Hlt; fourier. }
        rewrite -Ropp_mult_distr_r; apply: Rle_refl. }
      have H10: eps > p_exp - p_hat x. 
      { clear - H8 H9; move: H8 H9; rewrite /p_exp; move: (p _ _) => p_exp => H1 H2.
        fourier. }
      fourier. }
    (*Case 2: p_hat >= p*)
    { have Hle3: eps <= p_hat x - p_exp.
      { move: Hle; rewrite Rabs_minus_sym /Rabs; case: (Rcase_abs _) => //= Hx Hy; fourier. }
      have Hle4: p_exp + eps <= p_hat x by fourier.
      case: (Rle_lt_dec (p _ _ f + _) _) => Hle5 /=.
      { rewrite -{1}[dP x]Rplus_0_r; apply: Rplus_le_compat_l.
        case: (Rle_lt_dec _ _) => /= y; [|fourier].
          by apply: prodR_nonneg. }
      exfalso; rewrite /p_hat/mR/p_exp in Hle4; move: Hle4 Hle5.
      move: (p _ _ _) => X; move: (/_ * _) => Y => H1 H2; fourier. }
  Qed.
End chernoff.

