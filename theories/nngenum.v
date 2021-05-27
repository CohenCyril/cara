From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import div fintype path bigop order finset fingroup.
From mathcomp Require Import ssralg poly ssrnum.
Require Import boolp ereal nngnum classical_sets ereal.

(******************************************************************************)
(* This file develops tools to make the manipulation of non-negative extended *)
(* numbers easier, on the model of posnum.v. This is WIP.                     *)
(*                                                                            *)
(*  {nonnege R} == interface types for elements in {ereal R} that are         *)
(*                 non-negative; R must have a numDomainType structure.       *)
(*                 Automatically solves goals of the form x >= 0. {nngenum R} *)
(*                 is stable by addition, multiplication.                     *)
(*                 This type is also shown to be a latticeType, a             *)
(*                 distrLatticeType, and an orderType,                        *)
(* NngeNum xge0 == packs the proof xge0 : x >= 0, for x : {ereal R}, to build *)
(*                 a {nngenum R}                                              *)
(*      x%:nnge == explicitly casts x to {nngenum R}, triggers the inference  *)
(*                 of a {nngeum R} structure for x                            *)
(*   x%:nngneum == explicit cast from {nngenum R} to {ereal R}                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Theory.

Reserved Notation "'{nonnege' R }" (at level 0, format "'{nonnege'  R }").
Reserved Notation "x %:nnge" (at level 2, left associativity, format "x %:nnge").
Reserved Notation "x %:nngenum" (at level 2, left associativity, format "x %:nngenum").
Module Nonnege.
Section nonnegative_extended_numbers.

Definition nonNegativeEReal {R : numDomainType} :=
  [qualify a x : {ereal R} | (x >= 0%:E)%E].
Record nngenum_of (R : numDomainType) (phR : phant R) := NngeNumDef {
  enum_of_nng : {ereal R} ;
  nngenum_ge0 :> enum_of_nng \is a nonNegativeEReal
}.
Hint Resolve nngenum_ge0 : core.
Hint Extern 0 ((0%:E <= _)%E = true) => exact: nngenum_ge0 : core.
Local Notation "'{nonnege' R }" := (nngenum_of (@Phant R)).
Definition NngeNum (R : numDomainType) x x_ge0 : {nonnege R} :=
  @NngeNumDef _ (Phant R) x x_ge0.
Arguments NngeNum {R}.

Local Notation "x %:nngenum" := (enum_of_nng x) : ereal_scope.
Definition nng_of_enum (R : numDomainType) (x : {nonnege R})
   (phx : phantom {ereal R} x%:nngenum%E) := x.
Local Notation "x %:nnge" := (nng_of_enum (Phantom _ x)) : ereal_scope.

Section Order.
Variable (R : numDomainType).

Canonical nngenum_subType := [subType for @enum_of_nng R (Phant R)].
Definition nngenum_eqMixin := [eqMixin of {nonnege R} by <:].
Canonical nngenum_eqType := EqType {nonnege R} nngenum_eqMixin.
Definition nngenum_choiceMixin := [choiceMixin of {nonnege R} by <:].
Canonical nngenum_choiceType := ChoiceType {nonnege R} nngenum_choiceMixin.
Definition nngenum_porderMixin := [porderMixin of {nonnege R} by <:].
Canonical nngenum_porderType :=
  POrderType ring_display {nonnege R} nngenum_porderMixin.

Lemma nngenum_le_total : totalPOrderMixin [porderType of {nonnege R}].
Proof.
move=> [x Hx] [y Hy].
rewrite /Order.le /= /Order.CanMixin.le /=.
move: x y Hx Hy => [x||] [y||] // Hx Hy.
{ apply/real_comparable; exact/ger0_real. }
{ apply/orP; left; exact: ger0_real. }
apply/orP; right; exact: ger0_real.
Qed.

Canonical nngenum_latticeType := LatticeType {nonnege R} nngenum_le_total.
Canonical nngenum_distrLatticeType :=
  DistrLatticeType {nonnege R} nngenum_le_total.
Canonical nngenum_orderType := OrderType {nonnege R} nngenum_le_total.

End Order.

End nonnegative_extended_numbers.

Module Exports.
Arguments NngeNum {R}.
Notation "'{nonnege' R }" := (nngenum_of (@Phant R)) : type_scope.
Notation nngenum R := (@enum_of_nng _ (@Phant R)).
Notation "x %:nngenum" := (enum_of_nng x) : ereal_scope.
Hint Extern 0 ((0%:E <= _)%E = true) => exact: nngenum_ge0 : core.
Notation "x %:nnge" := (nng_of_enum (Phantom _ x)) : ereal_scope.
Canonical nngenum_subType.
Canonical nngenum_eqType.
Canonical nngenum_choiceType.
Canonical nngenum_porderType.
Canonical nngenum_latticeType.
Canonical nngenum_orderType.
End Exports.

End Nonnege.
Export Nonnege.Exports.

Section NngeNum.
Context {R : numDomainType}.
Implicit Types a : {ereal R}.
Implicit Types x y : {nonnege R}.
Import Nonnege.

Canonical addr_nngenum x y := NngeNum (x%:nngenum + y%:nngenum) (adde_ge0 x y).

Lemma nngnum_ge0 (x : {nonneg R}) : (0%:E <= x%:nngnum%:E)%E.
Proof. by rewrite lee_fin. Qed.

Canonical nngnum_nngenum (z : {nonneg R}) := NngeNum z%:nngnum%:E (nngnum_ge0 z).

Lemma nngenum_lt0 x : (x%:nngenum < 0%:E)%E = false.
Proof. by rewrite le_gtF. Qed.

Lemma nnge_eq : {mono nngenum R : x y / x == y}. Proof. by []. Qed.
Lemma nnge_le : {mono nngenum R : x y / x <= y >-> (x <= y)%E}. Proof. by []. Qed.
Lemma nnge_lt : {mono nngenum R : x y / x < y >-> (x < y)%E}. Proof. by []. Qed.

Lemma nnge_eq0 x : (x%:nngenum%E == 0%:E) = (x == 0%:E%:nnge%E).
Proof. by []. Qed.

Lemma nnge_min : {morph nngenum R : x y / Order.min x y}.
Proof. by move=> x y; rewrite !minEle nnge_le -fun_if. Qed.

Lemma nnge_max : {morph nngenum R : x y / Order.max x y}.
Proof. by move=> x y; rewrite !maxEle nnge_le -fun_if. Qed.

Lemma nnge_le_maxr a x y :
  (a <= Order.max x%:nngenum y%:nngenum = (a <= x%:nngenum) || (a <= y%:nngenum))%E.
Proof. exact/comparable_le_maxr/nngenum_le_total. Qed.

Lemma nnge_le_maxl a x y :
  (Order.max x%:nngenum  y%:nngenum <= a = (x%:nngenum <= a) && (y%:nngenum <= a))%E.
Proof. exact/comparable_le_maxl/nngenum_le_total. Qed.

Lemma nnge_le_minr a x y :
  (a <= Order.min x%:nngenum y%:nngenum = (a <= x%:nngenum) && (a <= y%:nngenum))%E.
Proof. exact/comparable_le_minr/nngenum_le_total. Qed.

Lemma nnge_le_minl a x y :
  (Order.min x%:nngenum y%:nngenum <= a = (x%:nngenum <= a) || (y%:nngenum <= a))%E.
Proof. exact/comparable_le_minl/nngenum_le_total. Qed.

Lemma max_nnge_ge0 x y : (Order.max x%:nngenum y%:nngenum >= 0%:E)%E.
Proof. by rewrite nnge_le_maxr; apply/orP; left. Qed.

Lemma min_nnge_ge0 x y : (Order.min x%:nngenum y%:nngenum >= 0%:E)%E.
Proof. by rewrite nnge_le_minr; apply/andP; split. Qed.

Canonical max_nngenum x y :=
  NngeNum (Order.max x%:nngenum%E y%:nngenum%E) (max_nnge_ge0 x y).
Canonical min_nngenum x y :=
  NngeNum (Order.min x%:nngenum%E y%:nngenum%E) (min_nnge_ge0 x y).

End NngeNum.

Section NngeReal.
Context {R : realDomainType}.
Implicit Types a : {ereal R}.
Implicit Types x y : {nonnege R}.
Import Nonnege.

Canonical pinfty_nngenum := @NngeNum R +oo (lee_pinfty 0%:E).

Variant nngenum_spec (y : {nonnege R}) : {ereal R} -> Type :=
  | Nngenum_Fin : forall x : {nonneg R},
      y = x%:nngnum%:E%:nnge%E -> nngenum_spec y x%:nngnum%:E
  | Nngenum_PInf : y = +oo%:nnge%E -> nngenum_spec y +oo.

Lemma nngenumP x : nngenum_spec x x%:nngenum.
Proof.
case: x => -[x | | //] Px.
{ have P'x : 0 <= x; [by rewrite -lee_fin|].
  apply: (@Nngenum_Fin (NngeNum _ Px) (Nonneg.NngNum _ P'x)).
  exact/val_inj. }
apply: (@Nngenum_PInf (NngeNum _ Px)).
exact/val_inj.
Qed.

End NngeReal.

Lemma ereal_inf_nnge_ge0 (R : realFieldType) (P : {nonneg R} -> Prop) :
  (ereal_inf [set x%:nngnum%:E | x in [set x | P x ]]%classic >= 0%:E)%E.
Proof. by apply: lb_ereal_inf => _ [x /= Hx <-]; rewrite leEereal /=. Qed.

Canonical ereal_inf_nngenum (R : realFieldType) (P : {nonneg R} -> Prop) :=
  Nonnege.NngeNum
    (ereal_inf [set x%:nngnum%:E | x in [set x | P x ]]%classic)
    (ereal_inf_nnge_ge0 P).
