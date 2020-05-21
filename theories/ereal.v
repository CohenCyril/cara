(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)

(* NB: taken out from reals.v and generalized in 2019 *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Inductive er (R : Type) := ERFin of R | ERPInf | ERNInf.

Section ExtendedReals.
Variable (R : numDomainType).

Coercion real_of_er x : R :=
  if x is ERFin v then v else 0.
End ExtendedReals.

(* TODO: the following notations should have scopes. *)

(*Notation "\+inf" := (@ERPInf _).*)
Notation "+oo" := (@ERPInf _) : ereal_scope.
(*Notation "\-inf" := (@ERNInf _).*)
Notation "-oo" := (@ERNInf _) : ereal_scope.
Notation "x %:E" := (@ERFin _ x) (at level 2, format "x %:E").

Notation "{ 'ereal' R }" := (er R) (format "{ 'ereal'  R }").

Bind    Scope ereal_scope with er.
Delimit Scope ereal_scope with E.

Local Open Scope ereal_scope.

Section EqEReal.
Variable (R : eqType).

Definition eq_ereal (x y : {ereal R}) :=
  match x, y with
    | x%:E, y%:E => x == y
    | +oo, +oo => true
    | -oo, -oo => true
    | _, _ => false
  end.

Lemma ereal_eqP : Equality.axiom eq_ereal.
Proof. by case=> [?||][?||]; apply: (iffP idP) => //= [/eqP|[]] ->. Qed.

Definition ereal_eqMixin := Equality.Mixin ereal_eqP.
Canonical ereal_eqType := Equality.Pack ereal_eqMixin.

Lemma eqe (x1 x2 : R) : (x1%:E == x2%:E) = (x1 == x2). Proof. by []. Qed.

End EqEReal.

Section ERealChoice.
Variable (R : choiceType).

Definition code (x : {ereal R}) :=
  match x with
  | x%:E => GenTree.Node 0 [:: GenTree.Leaf x]
  | +oo => GenTree.Node 1 [::]
  | -oo => GenTree.Node 2 [::]
  end.

Definition decode (x : GenTree.tree R) : option {ereal R} :=
  match x with
  | GenTree.Node 0 [:: GenTree.Leaf x] => Some x%:E
  | GenTree.Node 1 [::] => Some +oo
  | GenTree.Node 2 [::] => Some -oo
  | _ => None
  end.

Lemma codeK : pcancel code decode. Proof. by case. Qed.

Definition ereal_choiceMixin := PcanChoiceMixin codeK.
Canonical ereal_choiceType  := ChoiceType {ereal R} ereal_choiceMixin.

End ERealChoice.

Section ERealCount.
Variable (R : countType).

Definition ereal_countMixin := PcanCountMixin (@codeK R).
Canonical ereal_countType := CountType {ereal R} ereal_countMixin.

End ERealCount.

Section ERealOrder.
Context {R : numDomainType}.
Implicit Types (x y : {ereal R}).

Definition le_ereal x1 x2 :=
  match x1, x2 with
  | -oo, x%:E | x%:E, +oo => x \is Num.real
  | x1%:E, x2%:E => x1 <= x2
  | -oo, _    | _, +oo => true
  | +oo, _    | _, -oo => false
  end.

Definition lt_ereal x1 x2 :=
  match x1, x2 with
  | -oo, x%:E | x%:E, +oo => x \is Num.real
  | x1%:E, x2%:E => x1 < x2
  | -oo, -oo  | +oo, +oo => false
  | +oo, _    | _  , -oo => false
  | -oo, _  => true
  end.

Lemma lt_def_ereal x y : lt_ereal x y = (y != x) && le_ereal x y.
Proof. by case: x y => [?||][?||] //=; rewrite lt_def eqe. Qed.

Lemma le_refl_ereal : reflexive le_ereal.
Proof. by case => /=. Qed.

Lemma le_anti_ereal : ssrbool.antisymmetric le_ereal.
Proof. by case=> [?||][?||]/=; rewrite ?andbF => // /le_anti ->. Qed.

Lemma le_trans_ereal : ssrbool.transitive le_ereal.
Proof.
case=> [?||][?||][?||] //=; rewrite -?comparabler0; first exact: le_trans.
  by move=> /le_comparable cmp /(comparabler_trans cmp).
by move=> cmp /ge_comparable /comparabler_trans; apply.
Qed.

Fact ereal_display : unit. Proof. by []. Qed.

Definition ereal_porderMixin :=
  LePOrderMixin lt_def_ereal le_refl_ereal le_anti_ereal le_trans_ereal.

Canonical ereal_porderType :=
  POrderType ereal_display {ereal R} ereal_porderMixin.

End ERealOrder.

Notation lee := (@Order.le ereal_display _) (only parsing).
Notation "@ 'lee' R" :=
  (@Order.le ereal_display R) (at level 10, R at level 8, only parsing).
Notation lte := (@Order.lt ereal_display _) (only parsing).
Notation "@ 'lte' R" :=
  (@Order.lt ereal_display R) (at level 10, R at level 8, only parsing).

Notation "x <= y" := (lee x y) : ereal_scope.
Notation "x < y"  := (lte x y) : ereal_scope.

Notation "x <= y <= z" := ((lee x y) && (lee y z)) : ereal_scope.
Notation "x < y <= z"  := ((lte x y) && (lee y z)) : ereal_scope.
Notation "x <= y < z"  := ((lee x y) && (lte y z)) : ereal_scope.
Notation "x < y < z"   := ((lte x y) && (lte y z)) : ereal_scope.

Lemma lee_fin (R : numDomainType) (x y : R) : (x%:E <= y%:E)%E = (x <= y)%O.
Proof. by []. Qed.

Lemma lte_fin (R : numDomainType) (x y : R) : (x%:E < y%:E)%E = (x < y)%O.
Proof. by []. Qed.

Lemma lte_pinfty (R : realDomainType) (x : R) : (x%:E < +oo).
Proof. exact: num_real. Qed.

Lemma lee_pinfty (R : realDomainType) (x : {ereal R}) : (x <= +oo).
Proof. case: x => //= r; exact: num_real. Qed.

Lemma lte_ninfty (R : realDomainType) (x : R) : (-oo < x%:E).
Proof. exact: num_real. Qed.

Lemma lee_ninfty (R : realDomainType) (x : {ereal R}) : (-oo <= x).
Proof. case: x => //= r; exact: num_real. Qed.

Section ERealOrder_realDomainType.
Context {R : realDomainType}.
Implicit Types (x y : {ereal R}).

Definition min_ereal x1 x2 :=
  match x1, x2 with
  | -oo, _ | _, -oo => -oo
  | +oo, x | x, +oo => x

  | x1%:E, x2%:E => (Num.Def.minr x1 x2)%:E
  end.

Definition max_ereal x1 x2 :=
  match x1, x2 with
  | -oo, x | x, -oo => x
  | +oo, _ | _, +oo => +oo

  | x1%:E, x2%:E => (Num.Def.maxr x1 x2)%:E
  end.

Lemma min_erealC : commutative min_ereal.
Proof. by case=> [?||][?||] //=; rewrite meetC. Qed.

Lemma max_erealC : commutative max_ereal.
Proof. by case=> [?||][?||] //=; rewrite joinC. Qed.

Lemma min_erealA : associative min_ereal.
Proof. by case=> [?||][?||][?||] //=; rewrite meetA. Qed.

Lemma max_erealA : associative max_ereal.
Proof. by case=> [?||][?||][?||] //=; rewrite joinA. Qed.

Lemma joinKI_ereal y x : min_ereal x (max_ereal x y) = x.
Proof. by case: x y => [?||][?||] //=; rewrite (joinKI, meetxx). Qed.

Lemma meetKU_ereal y x : max_ereal x (min_ereal x y) = x.
Proof. by case: x y => [?||][?||] //=; rewrite (meetKU, joinxx). Qed.

Lemma leEmeet_ereal x y : (x <= y)%E = (min_ereal x y == x).
Proof.
case: x y => [x||][y||] //=; rewrite ?eqxx ?lee_pinfty ?lee_ninfty //.
exact: leEmeet.
Qed.

Lemma meetUl_ereal : left_distributive min_ereal max_ereal.
Proof.
by case=> [?||][?||][?||] //=; rewrite ?(meetUl, meetUK, meetKUC, joinxx).
Qed.

Lemma minE_ereal x y : min_ereal x y = if le_ereal x y then x else y.
Proof. by case: x y => [?||][?||] //=; rewrite ?num_real //; case: leP. Qed.

Lemma maxE_ereal x y : max_ereal x y = if le_ereal y x then x else y.
Proof. by case: x y => [?||][?||] //=; rewrite ?num_real //; case: ltP. Qed.

Lemma le_total_ereal : total (@le_ereal R).
Proof. by case=> [?||][?||] //=; rewrite ?num_real //; exact: le_total. Qed.

Definition ereal_latticeMixin :=
  LatticeMixin min_erealC max_erealC min_erealA max_erealA
                    joinKI_ereal meetKU_ereal leEmeet_ereal.
Canonical ereal_latticeType := LatticeType {ereal R} ereal_latticeMixin.
Definition ereal_distrLatticeMixin := DistrLatticeMixin meetUl_ereal.
Canonical ereal_distrLatticeType :=
  DistrLatticeType {ereal R} ereal_distrLatticeMixin.
Canonical ereal_orderType := OrderType {ereal R} le_total_ereal.

End ERealOrder_realDomainType.

Section ERealArith.
Context {R : numDomainType}.

Implicit Types (x y z : {ereal R}).

Definition eadd x y :=
  match x, y with
  | x%:E , y%:E  => (x + y)%:E
  | -oo, _     => -oo
  | _    , -oo => -oo
  | +oo, _     => +oo
  | _    , +oo => +oo
  end.

Definition eopp x :=
  match x with
  | x%:E  => (-x)%:E
  | -oo => +oo
  | +oo => -oo
  end.
End ERealArith.

Notation "+%E"   := eadd.
Notation "-%E"   := eopp.
Notation "x + y" := (eadd x y) : ereal_scope.
Notation "x - y" := (eadd x (eopp y)) : ereal_scope.
Notation "- x"   := (eopp x) : ereal_scope.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%E/0%:E]_(i <- r | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%E/0%:E]_(i <- r) F%R) : ereal_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%E/0%:E]_(m <= i < n | P%B) F%R) : ereal_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%E/0%:E]_(m <= i < n) F%R) : ereal_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%E/0%:E]_(i | P%B) F%R) : ereal_scope.
Notation "\sum_ i F" :=
  (\big[+%E/0%:E]_i F%R) : ereal_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%E/0%:E]_(i : t | P%B) F%R) (only parsing) : ereal_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%E/0%:E]_(i : t) F%R) (only parsing) : ereal_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%E/0%:E]_(i < n | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%E/0%:E]_(i < n) F%R) : ereal_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%E/0%:E]_(i in A | P%B) F%R) : ereal_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%E/0%:E]_(i in A) F%R) : ereal_scope.

Section ERealArithTh_numDomainType.

Context {R : numDomainType}.

Implicit Types (x y z : {ereal R}).

Lemma adde0 : right_id (0%:E : {ereal R}) +%E.
Proof. by case=> //= x; rewrite addr0. Qed.

Lemma add0e : left_id (S := {ereal R}) 0%:E +%E.
Proof. by case=> //= x; rewrite add0r. Qed.

Lemma addeC : commutative (S := {ereal R}) +%E.
Proof. by case=> [x||] [y||] //=; rewrite addrC. Qed.

Lemma addeA : associative (S := {ereal R}) +%E.
Proof. by case=> [x||] [y||] [z||] //=; rewrite addrA. Qed.

Canonical adde_monoid := Monoid.Law addeA add0e adde0.
Canonical adde_comoid := Monoid.ComLaw addeC.

Lemma oppe0 : (- 0%:E)%E = 0%:E :> {ereal R}.
Proof. by rewrite /= oppr0. Qed.

Lemma oppeK : involutive (A := {ereal R}) -%E.
Proof. by case=> [x||] //=; rewrite opprK. Qed.

Lemma eqe_opp x y : (- x == - y)%E = (x == y).
Proof.
move: x y => [r| |] [r'| |] //=; apply/idP/idP => [|/eqP[->]//].
by move/eqP => -[] /eqP; rewrite eqr_opp => /eqP ->.
Qed.

End ERealArithTh_numDomainType.

Section ERealArithTh_realDomainType.

Context {R : realDomainType}.
Implicit Types x y a b : {ereal R}.

Lemma sube_gt0 x y: (0%:E < y - x)%E = (x < y)%E.
Proof.
move: x y => [r | |] [r'| |] //=; rewrite ?(lte_pinfty,lte_ninfty) //.
by rewrite !lte_fin subr_gt0.
Qed.

Lemma lte_oppl x y : (- x < y)%E = (- y < x)%E.
Proof.
move: x y => [r| |] [r'| |] //=; rewrite ?lte_pinfty ?lte_ninfty //.
by rewrite !lte_fin ltr_oppl.
Qed.

Lemma lte_oppr x y : (x < - y)%E = (y < - x)%E.
Proof.
move: x y => [r| |] [r'| |] //=; rewrite ?lte_pinfty ?lte_ninfty //.
by rewrite !lte_fin ltr_oppr.
Qed.

Lemma lee_addl x y : (0%:E <= y)%E ->  (x <= x + y)%E.
Proof.
move: x y => -[ x [y| |]//= | [| |]// | [| | ]//];
  by [rewrite !lee_fin ler_addl | move=> _; exact: lee_pinfty].
Qed.

Lemma lee_add2l x a b : (a <= b)%E -> (x + a <= x + b)%E.
Proof.
move: a b x => -[a [b [x /=|//|//] | []// |//] | []// | ].
- by rewrite !lee_fin ler_add2l.
- move=> r _; exact: lee_pinfty.
- move=> -[b [|  |]// | []// | //] r oob; exact: lee_ninfty.
Qed.

Lemma lee_add2r x a b : (a <= b)%E -> (a + x <= b + x)%E.
Proof. rewrite addeC (addeC b); exact: lee_add2l. Qed.

End ERealArithTh_realDomainType.
