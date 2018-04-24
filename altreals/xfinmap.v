(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Export finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope fset_scope.

(* -------------------------------------------------------------------- *)
Lemma uniq_fset_keys {K : choiceType} (J : {fset K}) : uniq (enum_fset J).
Proof. by case: J => J /= /canonical_uniq. Qed.

Hint Resolve uniq_fset_keys.

(* -------------------------------------------------------------------- *)
Lemma enum_fset0 (T : choiceType) :
  enum [finType of fset0] = [::] :> seq (@fset0 T).
Proof. by rewrite enumT unlock. Qed.

Lemma enum_fset1 (T : choiceType) (x : T) :
  enum [finType of [fset x]] = [:: [`fset11 x]].
Proof.
apply/perm_eq_small=> //; apply/uniq_perm_eq => //.
  by apply/enum_uniq.
case=> [y hy]; rewrite mem_seq1 mem_enum /in_mem /=.
by rewrite eqE /=; rewrite in_fset1 in hy.
Qed.

(* -------------------------------------------------------------------- *)
Section BigFSet.
Variable (R : Type) (idx : R) (op : Monoid.law idx).
Variable (I : choiceType).

Lemma big_fset0_cond (P : pred _) (F : _ -> R) :
  \big[op/idx]_(i : @fset0 I | P i) F i = idx :> R.
Proof. by apply: big_pred0 => -[j hj]; have := hj; rewrite in_fset0. Qed.

Lemma big_fset0 (F : @fset0 I -> R) :
  \big[op/idx]_(i : fset0) F i = idx.
Proof. by rewrite /index_enum -enumT /= enum_fset0 big_nil. Qed.

Lemma big_fset1 (a : I) (F : [fset a] -> R) :
  \big[op/idx]_(i : [fset a]) F i = F (FSetSub (fset11 a)).
Proof. by rewrite /index_enum -enumT enum_fset1 big_seq1. Qed.
End BigFSet.

(* -------------------------------------------------------------------- *)
Section BigFSetCom.
Variable (R : Type) (idx : R).

Local Notation "1" := idx.

Variable op : Monoid.com_law 1.

Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma big_fset_seq_cond (T : choiceType) (J : {fset T}) P F :
    \big[*%M/1]_(x : J | P (val x)) F (val x)
  = \big[*%M/1]_(x <- enum_fset J | P x) F x.
Proof.
case: J=> J c; rewrite -(big_map val) /index_enum.
by rewrite !unlock val_fset_sub_enum ?canonical_uniq.
Qed.

Lemma big_fset_seq (T : choiceType) (J : {fset T}) F :
    \big[*%M/1]_(x : J) F (val x)
  = \big[*%M/1]_(x <- enum_fset J) F x.
Proof. by apply/big_fset_seq_cond. Qed.

Lemma big_seq_fset_cond (T : choiceType) (s : seq T) P F : uniq s ->
    \big[*%M/1]_(x : seq_fset s | P (val x)) F (val x)
  = \big[*%M/1]_(x <- s | P x) F x.
Proof.
move=> eq_s; rewrite big_fset_seq_cond; apply/eq_big_perm.
by apply/uniq_perm_eq=> //= x; rewrite seq_fsetE.
Qed.

Lemma big_seq_fset (T : choiceType) (s : seq T) F : uniq s ->
    \big[*%M/1]_(x : seq_fset s) F (val x)
  = \big[*%M/1]_(x <- s) F x.
Proof. by apply/big_seq_fset_cond. Qed.
End BigFSetCom.

Arguments big_fset_seq_cond [R idx op T J] P F.
Arguments big_fset_seq [R idx op T J] F.
Arguments big_seq_fset_cond [R idx op T s] P F _.
Arguments big_seq_fset [R idx op T s] F _.

(* -------------------------------------------------------------------- *)
Section BigFSetU.
Context {R : Type} {T : choiceType} (idx : R) (op : Monoid.com_law idx).

Lemma big_fsetU (A B : {fset T}) F : [disjoint A & B] ->
  \big[op/idx]_(j : A `|` B) F (val j) =
    op (\big[op/idx]_(j : A) F (val j))
       (\big[op/idx]_(j : B) F (val j)).
Proof.
move=> dj_AB; rewrite !big_fset_seq -big_cat; apply/eq_big_perm.
apply/uniq_perm_eq=> //.
+ rewrite cat_uniq ?uniq_fset_keys !(andbT, andTb); apply/hasPn => x /=.
  by apply/fdisjointP; rewrite fdisjoint_sym.
+ by move=> x; rewrite mem_cat in_fsetE.
Qed.
End BigFSetU.

(* -------------------------------------------------------------------- *)
Section BigFSetOrder.
Variable (R : realDomainType) (T : choiceType).

Lemma big_fset_subset (I J : {fset T}) (F : T -> R) :
  (forall x, (0 <= F x)%R) -> {subset I <= J} ->
    \sum_(i : I) F (val i) <= \sum_(j : J) F (val j).
Proof.
move=> ge0_F le_IJ; rewrite !big_fset_seq /=.
rewrite [X in _<=X](bigID [pred j : T | j \in I]) /=.
rewrite ler_paddr ?sumr_ge0 // -[X in _<=X]big_filter.
rewrite ler_eqVlt; apply/orP; left; apply/eqP/eq_big_perm.
apply/uniq_perm_eq; rewrite ?filter_uniq //; last move=> i.
rewrite mem_filter; case/boolP: (_ \in _) => //=.
by move/le_IJ => ->.
Qed.

Lemma big_nat_mkfset (F : nat -> R) n :
  \sum_(0 <= i < n) F i =
    \sum_(i : seq_fset (iota 0 n)) F (val i).
Proof.
rewrite -(big_map val xpredT) /=; apply/eq_big_perm.
apply/uniq_perm_eq; rewrite ?iota_uniq //.
  rewrite map_inj_uniq /=; last apply/val_inj.
  by rewrite /index_enum -enumT enum_uniq.
move=> i; rewrite /index_enum unlock val_fset_sub_enum /=.
  by rewrite seq_fsetE /index_iota subn0.
  by apply/enum_fset_uniq.
Qed.

Lemma big_ord_mkfset (F : nat -> R) n :
  \sum_(i < n) F i =
    \sum_(i : seq_fset (iota 0 n)) F (val i).
Proof. by rewrite -(big_mkord xpredT) big_nat_mkfset. Qed.
End BigFSetOrder.

(* -------------------------------------------------------------------- *)
Lemma enum_fsetT {I : finType} :
  perm_eq (enum [fset i | i in I]) (enum I).
Proof.
apply/uniq_perm_eq; rewrite ?enum_uniq //.
by move=> i /=; rewrite !mem_enum in_imfset.
Qed.

(* -------------------------------------------------------------------- *)
