(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum.
From mathcomp Require Import matrix interval rat.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype landau sequences.

(******************************************************************************)
(*                Definitions and lemmas about exponential                    *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def  Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section fact_facts.

Local Open Scope nat_scope.

Lemma leq_fact n : n <= n`!.
Proof.
by case: n => // n;  rewrite dvdn_leq ?fact_gt0 // dvdn_fact ?andTb.
Qed.

Lemma prod_rev n m :
  \prod_(0 <= k < n - m) (n - k) = \prod_(m.+1 <= k < n.+1) k.
Proof.
rewrite [in RHS]big_nat_rev /= -{1}(add0n m.+1) big_addn subSS.
by apply eq_bigr => i _; rewrite addnS subSS addnC subnDr.
Qed.

Lemma fact_split n m : m <= n -> n`! = \prod_(0 <= k < n - m) (n - k) * m`!.
Proof.
move=> ?; rewrite [in RHS]fact_prod mulnC prod_rev -big_cat [in RHS]/index_iota.
rewrite subn1 -iota_add subSS addnBCA // subnn addn0 [in LHS]fact_prod.
by rewrite [in RHS](_ : n = n.+1 - 1) // subn1.
Qed.

End fact_facts.

Section exponential_series.

Variable R : realType.
Implicit Types x : R.

Import Order.TTheory.
Import Num.Theory.
Import GRing.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition exp_coeff x := [sequence x ^+ n / n`!%:R]_n.

Local Notation exp := exp_coeff.

Lemma exp_coeff_ge0 x n : 0 <= x -> 0 <= exp x n.
Proof. by move=> x0; rewrite /exp divr_ge0 // ?exprn_ge0 // ler0n. Qed.

Lemma series_exp_coeff0 n : series (exp 0) n.+1 = 1.
Proof.
rewrite /series /= big_nat_recl //= /exp /= expr0n divr1 big1 ?addr0 // => i _.
by rewrite expr0n mul0r.
Qed.

Section exponential_series_cvg.

Variable x : R.
Hypothesis x0 : 0 < x.

Let S0 N n := (N ^ N)%:R * \sum_(N.+1 <= i < n) (x / N%:R) ^+ i.

Let is_cvg_S0 N : x < N%:R -> cvg (S0 N).
Proof.
move=> xN; apply: is_cvgZr; rewrite is_cvg_series_restrict exprn_geometric.
apply/is_cvg_geometric_series; rewrite normrM normfV.
by rewrite ltr_pdivr_mulr ?mul1r !ger0_norm // 1?ltW // (lt_trans x0).
Qed.

Let S0_ge0 N n : 0 <= S0 N n.
Proof.
rewrite mulr_ge0 // ?ler0n //; apply sumr_ge0 => i _.
by rewrite exprn_ge0 // divr_ge0 // ?ler0n // ltW.
Qed.

Let S0_sup N n : x < N%:R -> S0 N n <= sup [set of S0 N].
Proof.
move=> xN; apply/sup_upper_bound; [split; [by exists (S0 N n), n|]|by exists n].
rewrite (_ : [set of _] = [set `|S0 N n0| | n0 in setT]).
  by apply: cvg_has_ub (is_cvg_S0 xN).
by rewrite predeqE=> y; split=> -[z _ <-]; exists z; rewrite ?ger0_norm ?S0_ge0.
Qed.

Let S1 N n := \sum_(N.+1 <= i < n) exp x i.

Lemma incr_S1 N : nondecreasing_seq (S1 N).
Proof.
apply/nondecreasing_seqP => n; rewrite /S1.
have [nN|Nn] := leqP n N; first by rewrite !big_geq // (leq_trans nN).
by rewrite big_nat_recr//= ler_addl exp_coeff_ge0 // ltW.
Qed.

Let S1_sup N n : x < N%:R -> S1 N n <= sup [set of S0 N].
Proof.
move=> xN; rewrite (le_trans _ (S0_sup n xN)) // /S0 big_distrr /=.
have N_gt0 := lt_trans x0 xN.
apply ler_sum => i _.
have [Ni|iN] := ltnP N i; last first.
  rewrite expr_div_n mulrCA ler_pmul2l ?exprn_gt0 // (@le_trans _ _ 1) //.
    by rewrite invf_le1 ?ler1n ?ltr0n // fact_gt0.
  rewrite natrX -expfB_cond ?(negPf (lt0r_neq0 N_gt0)) //.
  by rewrite exprn_ege1 // ler1n; case: (N) xN x0; case: ltrgt0P.
rewrite /exp expr_div_n /= (fact_split Ni) mulrCA.
rewrite ler_pmul2l ?exprn_gt0 // natrX -invf_div -expfB //.
rewrite lef_pinv ?qualifE; last 2 first.
- rewrite ltr0n muln_gt0 fact_gt0 andbT.
  rewrite big_mkord prodn_gt0  // => j.
  by rewrite subn_gt0 (leq_trans (ltn_ord _) (leq_subr _ _)).
- by rewrite exprn_gt0.
rewrite prod_rev -natrX ler_nat -prod_nat_const_nat big_add1 /= big_ltn //.
rewrite mulnC leq_mul //; last by apply: leq_trans (leq_fact _).
rewrite -(subnK Ni); elim: (_ - _)%N => [|k IH]; first by rewrite !big_geq.
rewrite !addSn !big_nat_recr //= ?leq_mul ?leq_addl //.
by rewrite -addSn -addSnnS leq_addl.
Qed.

Lemma is_cvg_series_exp_coeff_pos : cvg (series (exp x)).
Proof.
rewrite /series; near \oo => N; have xN : x < N%:R; last first.
  rewrite -(@is_cvg_series_restrict N.+1).
  exact: (nondecreasing_is_cvg (incr_S1 N) (fun n => S1_sup n xN)).
near: N; exists (absz (floor x)).+1 => // m; rewrite /mkset -(@ler_nat R).
move/lt_le_trans => -> //; rewrite (lt_le_trans (lt_succ_Rfloor x)) // -addn1.
rewrite natrD (_ : 1%:R = 1%R) // ler_add2r RfloorE -(@gez0_abs (floor x)) //.
by rewrite floor_ge0// ltW.
Grab Existential Variables. all: end_near. Qed.

End exponential_series_cvg.

Lemma normed_series_exp_coeff x : [normed series (exp x)] = series (exp `|x|).
Proof.
rewrite funeqE => n /=; apply: eq_bigr => k _.
by rewrite /exp normrM normfV normrX [`|_%:R|]@ger0_norm.
Qed.

Lemma is_cvg_series_exp_coeff x : cvg (series (exp x)).
Proof.
have [/eqP ->|x0] := boolP (x == 0).
  apply/cvg_ex; exists 1; apply/cvg_distP => // => _/posnumP[e].
  rewrite near_map; near=> n; have [m ->] : exists m, n = m.+1.
    by exists n.-1; rewrite prednK //; near: n; exists 1%N.
  by rewrite series_exp_coeff0 subrr normr0.
apply: normed_cvg; rewrite normed_series_exp_coeff.
by apply: is_cvg_series_exp_coeff_pos; rewrite normr_gt0.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_exp_coeff x : exp x --> (0 : R).
Proof. exact: (cvg_series_cvg_0 (@is_cvg_series_exp_coeff x)). Qed.

End exponential_series.

Section exp.

Variable R : realType.

Definition exp (x : R) : R := lim (series (exp_coeff x)).

Lemma exp0 : exp 0 = 1.
Proof.
apply: lim_near_cst => //.
near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_exp_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /exp_coeff /= expr0n mul0r.
Grab Existential Variables. all: end_near. 
Qed.

Lemma exp_ge x : 0 <= x -> 1 + x <= exp x.
Proof.
 move=> xP; rewrite /exp.
pose f (x : R) i := (i == 0%nat)%:R + x *+ (i == 1%nat).
have F n : (1 < n)%nat -> \sum_(0 <= i < n) (f x i) = 1 + x.
  move=> /subnK<-.
  by rewrite addn2 !big_nat_recl //= /f /= mulr1n !mulr0n big1 ?add0r ?addr0.
have -> : 1 + x = lim (series (f x)).
  by apply/sym_equal/lim_near_cst => //; near=> n; apply: F; near: n.
apply: ler_lim; first by apply: is_cvg_near_cst; near=> n; apply: F; near: n.
  exact: is_cvg_series_exp_coeff.
by near=> n; apply: ler_sum => [] [|[|i]] _;
  rewrite /f /exp_coeff /= !(mulr0n, mulr1n, expr0, expr1, divr1, addr0, add0r)
          // exp_coeff_ge0.
Grab Existential Variables. all: end_near. 
Qed.

Lemma exp_gt_1 x : 0 < x  -> 1 < exp x.
Proof.
move=> xP.
apply: lt_le_trans (exp_ge (ltW xP)).
by rewrite -subr_gt0 addrAC subrr add0r.
Qed.

Fact powdiff n (x y : R) : 
  \sum_(0 <= i < n.+1) x ^+ i  * y ^+ (n.+1 - i) =   
  y * \sum_(0 <= i < n.+1) x ^+ i  * y ^+ (n - i).
Proof.
rewrite !big_mkord mulr_sumr; apply: eq_bigr => i _.
by rewrite mulrCA -exprS subSn // -ltnS.
Qed.

Lemma cvg_series_bounded (f : nat -> R) :
  cvg (series f) ->  exists2 K, 0 < K & (forall i, `|f i| < K).
Proof.
(* There should be something simpler *)
move=> Cf.
have F1 := cvg_series_cvg_0 Cf.
have F2 : bounded_near id [filter of f] by apply: cvg_bounded F1.
have [K1 K1_gt0 KF]:= ex_strict_bound_gt0 F2.
case: KF => x _ Hx.
pose K2 := \sum_(i < x) (1 + `|f i|).
have K2_ge0 : 0 <= K2 by apply: sumr_ge0 => *; apply: addr_ge0.
have K1LK1DK2 : K1 <= K1 + K2 by rewrite -{1}[K1]addr0 ler_add2l.
have K2LK1DK2 : K2 <= K1 + K2 by rewrite -{1}[K2]add0r ler_add2r ltW.
exists (K1 + K2) => [|i]; first by apply: lt_le_trans K1_gt0 _.
have [iLx|xLi] := leqP x i; first by apply: lt_le_trans (Hx i iLx) _.
apply: lt_le_trans K2LK1DK2.
rewrite /K2 (bigD1 (Ordinal xLi)) //=.
rewrite -subr_gt0 addrC !addrA [- _ + _]addrC subrK.
apply: lt_le_trans (_ : 1 <= _) => //.
rewrite -subr_ge0 [1 + _]addrC addrK //.
by apply: sumr_ge0 => *; apply: addr_ge0.
Qed.

Fact pow_ser_inside_a f (x z : R) :
  cvg (series (fun i => f i * x ^+ i)) -> `|z| < `|x| ->
  cvg (series (fun i => `|f i| * z ^+ i)).
Proof.
move=> Cx zLx.
have [K K_gt0 KP] := cvg_series_bounded Cx.
have F1 := cvg_series_cvg_0 Cx.
have F2 n : 0 <= K * `|z ^+ n| / `|x ^+ n|.
  by rewrite !mulr_ge0 ?invr_ge0 // ltW.
apply: normed_cvg.
apply: series_le_cvg F2 _ _ => [//=| /= n|].
  rewrite (_ : `|_ * _| = `|f n * x ^+ n| * `|z ^+ n| / `|x ^+ n|); last first.
    rewrite !normrM normr_id mulrAC mulfK // normr_eq0 expf_eq0 andbC.
    by case: ltrgt0P zLx; rewrite //= normr_lt0.
  do! (apply: ler_pmul || apply: mulr_ge0 || rewrite invr_ge0) => //.
  by apply: ltW.
have F : `|z / x| < 1.
  by rewrite normrM normfV ltr_pdivr_mulr ?mul1r // (le_lt_trans _ zLx).
rewrite (_ : (fun _ => _) = geometric K `|z / x|).
apply: is_cvg_geometric_series; first by rewrite normr_id.
apply/funext => i /=.
by rewrite normrM exprMn mulrA normfV !normrX exprVn.
Qed.

Fact pow_ser_inside f (x z : R) :
  cvg (series (fun i => f i * x ^+ i)) -> `|z| < `|x| ->
  cvg (series (fun i => f i * z ^+ i)).
Proof.
move=> Cx zLx.
apply: normed_cvg; rewrite /normed_series_of /=.
rewrite (_ : (fun _ => _) = (fun i : nat => `|f i| * `|z| ^+ i)); last first.
  by apply/funext => i; rewrite normrM normrX.
by apply: pow_ser_inside_a Cx _; rewrite normr_id.
Qed.

Definition diffs (f : nat -> R) i := i.+1%:R * f i.+1.

Lemma diffsN (f : nat -> R) :  diffs (- f) = -(diffs f).
Proof. by apply/funext => i; rewrite /diffs /= -mulrN. Qed.

Lemma diffs_sumE n f x :
 \sum_(0 <= i < n) diffs f i * x ^+ i =
 (\sum_(0 <= i < n) i%:R * f i * x ^+ i.-1) + n%:R * f n * x ^+ n.-1.
Proof.
case: n => [|n]; first by rewrite !big_nil !mul0r add0r.
under eq_bigr do unfold diffs.
by rewrite big_nat_recr //= big_nat_recl //= !mul0r add0r.
Qed.

Lemma cvg_ext (f g : nat -> R) (x : R) : f = g -> (f --> x) = (g --> x).
Proof. by move->. Qed. 

Lemma cvgS (f : nat -> R) (x : R) : (f \o S --> x) = (f --> x).
Proof.
have <- /= := @cvg_shiftn 1 _ f x.
by apply/cvg_ext/funext => i; rewrite addn1.
Qed.

Lemma diffs_equiv f x :
  cvg (series (fun i => diffs f i * x ^+ i)) ->
  series (fun i => i%:R * f i * x ^+ i.-1) -->
  lim (series (fun i => diffs f i * x ^+ i)).
Proof.
move=> Cx.
rewrite -[lim _]subr0.
rewrite {2}/series /=.
have F n : \sum_(0 <= i < n) i%:R * f i * x ^+ i.-1 =
           (\sum_(0 <= i < n) diffs f i * x ^+ i) - n%:R * f n * x ^+ n.-1.
    by rewrite diffs_sumE addrK. 
rewrite (cvg_ext _ (funext F)).
apply: cvgB => //; rewrite -cvgS.
by apply: cvg_series_cvg_0.
Qed.

Lemma termdiff_P1 m (z h : R) :
  \sum_(0 <= i < m) ((z + h) ^+ (m - i) * z ^+ i - z ^+ m) =
  \sum_(0 <= i < m) z ^+ i * ((z + h) ^+ (m - i) - z ^+ (m - i)).
Proof.
rewrite !big_mkord; apply: eq_bigr => i _.
by rewrite mulrDr mulrN -exprD mulrC addnC subnK // ltnW.
Qed.

Lemma termdiff_P2 n (z h : R) :
  h != 0 ->
  ((z + h) ^+ n - (z ^+ n)) / h - n%:R * z ^+ n.-1 =
  h * \sum_(0 <= i < n) z ^+ i *
      \sum_(0 <= j < n - i) (z + h) ^+ j * z ^+ (n.-2 - i - j).
Proof.
move=> hNZ; apply: (mulfI hNZ).
rewrite mulrBr mulrC divfK //.
case: n => [|n].
  by rewrite !expr0 !(mul0r, mulr0, subr0, subrr, big_geq).
Check powdiff.
rewrite powdiff.
Search _ ((_ + _)^+ _).






End exp.
