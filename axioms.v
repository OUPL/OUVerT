Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import QArith Reals Rpower Ranalysis Fourier Lra.

Require Import dist.

(** The following lemmas (stated here as axioms) are well 
    known but should nevertheless be proved. Until proved,
    any paper that uses/references results from OUVerT.axioms
    should state explicitly that the formal claims depend upon
    the following assumptions: 

    NOTE: We should see whether the results from Affeldt et al's: 
    https://staff.aist.go.jp/reynald.affeldt/shannon/ 
    can be imported here to prove [pinsker] and related theorems
    in information theory. *)

Axiom pinsker_Bernoulli : 
  forall (p q:R) (p_ax:0<p<1) (q_ax:0<q<1), 
  sqrt (RE_Bernoulli p q / 2) >= TV_Bernoulli p q.

Axiom gibbs_Bernoulli :
  forall (p q:R) (p_ax:0<p<1) (q_ax:0<q<1),   
  0 <= RE_Bernoulli p q.
  

