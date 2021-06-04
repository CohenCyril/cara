(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import bigop div ssralg ssrint ssrnum fintype order.
From mathcomp Require Import binomial matrix interval rat.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype landau sequences.

(******************************************************************************)
(*               More standard sequences and series (WIP)                     *)
(*                                                                            *)
(* The main purpose of this file is to test extensions to sequences.v         *)
(*                                                                            *)
(*           euler_seq n == the sequence (1 + 1 / n) ^ n                      *)
(*        euler_constant == Euler constant e defined as lim euler_seq with    *)
(*                          proof 2 < e <= 4                                  *)
(*          dvg_harmonic == the harmonic series does not converge             *)
(*               riemann == Riemann sequence 1/(n + 1)^a                      *)
(*           dvg_riemann == the Riemann series does not converge              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section euler_constant.
Variable (R : realType).
Implicit Types n m : nat.

Definition euler_seq : (R^o) ^nat := [sequence (1 + 1 / n%:R) ^+ n]_n.
Local Notation u_ := euler_seq.

Lemma euler_seq0 : u_ O = 1.
Proof. by rewrite /u_ {1}(_ : 1 = 1%:R) // ler_nat. Qed.

Lemma euler_seq1 : u_ 1%nat = 2.
Proof. by rewrite /u_ /= expr1 divr1. Qed.

Lemma euler_seq2 : u_ 2%nat = 9%:R / 4%:R.
Proof.
rewrite /euler_seq /= -{1}(@divrr _ 2) ?unitfE // -mulrDl.
by rewrite expr_div_n {2}(_ : 1 = 1%:R) // -natrD -2!natrX.
Qed.

Section euler_seq_is_bounded_by_4.
Let v_ n m : R := (n - m + 2)%:R / (n - m)%:R.

Let v_increasing n : forall m, (m < n)%nat -> v_ n.*2 m < v_ n.*2 m.+1.
Proof.
move=> m mn; rewrite /v_.
have H : forall p q,
  (1 < q < p)%nat -> (p%:R : R) / q%:R < (p%:R - 1) / (q%:R - 1).
  move=> p q pq; rewrite ltr_pdivr_mulr; last first.
    move/andP : pq => -[a b].
    by rewrite (_ : 0 = 0%:R) // ltr_nat (ltn_trans _ a).
  rewrite mulrAC ltr_pdivl_mulr; last first.
    by rewrite subr_gt0 (_ : 1 = 1%:R) // ltr_nat; case/andP: pq.
  by rewrite mulrBl mulrBr mul1r mulr1 ler_lt_sub // ltr_nat; case/andP : pq.
rewrite -(addn1 m) !subnDA (@natrB _ _ 1); last first.
  by rewrite subn_gt0 (leq_trans mn) // -addnn leq_addr.
rewrite (_ : (n.*2 - m - 1 + 2)%:R = (n.*2 - m + 2 - 1)%:R); last first.
  rewrite !subn1 !addn2 /= prednK // subn_gt0 (leq_trans mn) //.
  by rewrite -addnn leq_addr.
rewrite (@natrB _ _ 1) ?subn_gt0 ?addn2 //.
apply H; apply/andP; split; last by rewrite ltnS.
move: (mn); rewrite -(ltn_add2r 1) !addn1 => mn'.
rewrite ltn_subRL addn1 (leq_trans mn'){mn'} // -addnn -{1}(addn0 n) ltn_add2l.
by rewrite (leq_trans _ mn).
Qed.

Let v_nondecreasing n : forall i, (i < n)%nat -> v_ n.*2 0 <= v_ n.*2 i.
Proof.
elim=> // -[/= _ n1|i ih ni].
  by apply/ltW/v_increasing; rewrite (ltn_trans _ n1).
rewrite (le_trans (ih _)) // ?(leq_trans _ ni) //.
by apply/ltW/v_increasing; rewrite (leq_trans _ ni).
Qed.

Let prod_v_ n : (0 < n)%nat ->
  \prod_(i < n) v_ n.*2 i = (n.*2.+2 * n.*2.+1)%:R / (n.+2 * n.+1)%:R.
Proof.
move=> n0; set lhs := LHS. set rhs := RHS.
rewrite -(@divr1_eq _ lhs rhs) // {}/lhs {}/rhs invf_div mulrA.
rewrite /v_ big_split /= -mulrA mulrACA.
rewrite [X in X * _ = 1](_ : _ = \prod_(i < n.+2) (n.*2 - i + 2)%:R); last first.
  rewrite 2!big_ord_recr /= -mulrA; congr (_ * _).
  by rewrite -addnn addnK subnS addnK 2!addn2 /= natrM prednK.
rewrite [X in _ * X = 1](_ : _ = \prod_(i < n.+2) (n.*2 - i + 2)%:R^-1); last first.
  rewrite 2!big_ord_recl /= mulrA [in LHS]mulrC; congr (_ * _).
    rewrite subn0 addn2 subn1 addn2 prednK ?double_gt0 //.
    by rewrite natrM invrM ?unitfE // mulrC.
    apply eq_bigr => i _; congr (_ %:R^-1).
    rewrite /bump !leq0n !add1n -addn2 subnDA subn2 addn2 /= prednK; last first.
      rewrite -subnS subn_gt0 -addnn -(addn1 i) (@leq_trans n.+1) //.
      by rewrite addn1 ltnS.
      by rewrite -{1}(addn0 n) ltn_add2l.
    by rewrite prednK // subn_gt0 -addnn (@leq_trans n) // leq_addr.
by rewrite -big_split /= big1 // => i _; rewrite divrr // ?unitfE addn2.
Qed.

Lemma euler_seq_lt4 n : (0 < n)%nat -> u_ n < 4%:R.
Proof.
move=> n0.
rewrite /u_ /= -{1}(@divrr _ n%:R) ?unitfE ?pnatr_eq0 -?lt0n // -mulrDl.
rewrite (_ : _ ^+ n = \prod_(i < n) ((n%:R + 1) / n%:R)); last first.
  move _ : (_ / _) => h.
  elim: n n0 => // -[_ _|n ih _].
    by rewrite big_ord_recl big_ord0 mulr1 expr1.
  by rewrite exprS ih // [in RHS]big_ord_recl.
rewrite (@le_lt_trans _ _ (\prod_(i < n) v_ n.*2 i)) //; last first.
  rewrite prod_v_ // (_ : _ / _%:R = 2%:R * (n.*2.+1)%:R / n.+2%:R); last first.
    rewrite -doubleS natrM -muln2 (natrM _ _ 2) natrM.
    rewrite invrM ?unitfE ?pnatr_eq0 //.
    rewrite mulrCA 3!mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r; congr (_ * _).
  rewrite ltr_pdivr_mulr // (_ : 4 = 2 * 2)%nat // (natrM _ 2) -mulrA.
  rewrite  ltr_pmul2l // -natrM mul2n ltr_nat doubleS 2!ltnS -2!muln2.
  by rewrite leq_mul2r /=.
apply ler_prod => i _; apply/andP; split.
  apply divr_ge0; last exact/ler0n.
  by rewrite [X in _ <= _ + X](_ : _ = 1%:R) // -natrD ler0n.
apply: (@le_trans _ _ (v_ n.*2 (@ord0 n))).
  rewrite /v_ subn0 addn2 -doubleS.
  rewrite -2!muln2 2!natrM invrM // ?unitfE //; last first.
    by rewrite pnatr_eq0 -lt0n.
  rewrite -mulrA (mulrA 2) divrr ?unitfE // div1r.
  by rewrite [X in (_ + X) / _ <= _](_ : _ = 1%:R) // -natrD addn1.
exact/v_nondecreasing.
Qed.

End euler_seq_is_bounded_by_4.

Section euler_seq_increasing.

(* NB: see also SUM_GROUP in the PR 383 *)
Let sum_group_by_2 n (f : nat -> R) :
  \sum_(i < n) f i = \sum_(i < n./2) (f i.*2 + f i.*2.+1) + if
  odd n.+1 then 0 else f n.-1.
Proof.
elim: n.+1 {-2}n (ltnSn n) => {n} // m ih [_|n].
  by rewrite 2!big_ord0 /= addr0.
rewrite ltnS => nm.
rewrite big_ord_recr /= ih // negbK; case: ifPn => /= [|].
  by move/negbTE => no; rewrite no addr0 uphalf_half no add0n.
rewrite negbK => no.
rewrite no uphalf_half no add1n addr0 big_ord_recr /= -!addrA; congr (_ + _).
move: (odd_double_half n); rewrite no add1n => nE.
by rewrite nE -{1}nE.
Qed.

Lemma increasing_euler_seq : increasing_seq euler_seq.
Proof.
apply/increasing_seqP.
case=> [|n]; first by rewrite euler_seq0 euler_seq1 {1}(_ : 1 = 1%:R) // ltr_nat /u_.
rewrite -(@ltr_pmul2l _ (((n.+2%:R - 1) / n.+2%:R) ^+ n.+2)); last first.
  apply/exprn_gt0/divr_gt0; last by rewrite ltr0n.
  by rewrite subr_gt0 {1}(_ : 1 = 1%:R) // ltr_nat.
rewrite [X in X < _](_ : _ = (n.+2%:R - 1) / n.+2%:R); last first.
  rewrite {1}/u_ exprS -[RHS]mulr1 -3!mulrA; congr (_ * _).
  rewrite -mulrA; congr (_ * _).
  rewrite (_ : _ / n.+2%:R = (1 + 1 / n.+1%:R) ^-1); last first.
    rewrite -{4}(@divrr _ n.+1%:R) ?unitfE ?pnatr_eq0 // -mulrDl.
    by rewrite invf_div {2 6}(_ : 1 = 1%:R) // -natrD -natrB // subn1 addn1.
  by rewrite exprVn mulVr // unitfE expf_eq0 /= paddr_eq0 //= oner_eq0.
rewrite [X in _ < X](_ : _ = ((n.+2%:R ^+ 2 - 1) / n.+2%:R ^+ 2) ^+ n.+2); last first.
  rewrite /u_ /=.
  rewrite -{4}(@divrr _ n.+2%:R) ?unitfE ?pnatr_eq0 // -mulrDl.
  rewrite -exprMn_comm; last by rewrite /GRing.comm mulrC.
  congr (_ ^+ _); rewrite mulrACA -subr_sqr expr1n; congr (_ * _).
  by rewrite -invrM // unitfE pnatr_eq0.
rewrite mulrBl divrr ?unitfE ?pnatr_eq0 // mulrBl.
rewrite divrr ?unitfE ?expf_eq0 /= ?pnatr_eq0 //.
rewrite exprBn_comm; last by rewrite /GRing.comm mulrC.
rewrite big_ord_recl 2!expr0 expr1n bin0 mulr1n 2![in X in _ < X]mul1r.
rewrite big_ord_recl 2!expr1 expr1n bin1 [in X in _ < X]mul1r mulN1r.
rewrite (_ : -1 / _ *+ _ = -1 / n.+2%:R); last first.
  rewrite 2!mulN1r mulNrn; congr (- _).
  rewrite expr2 invrM ?unitfE ?pnatr_eq0 //.
  rewrite -mulrnAr -[RHS]mulr1; congr (_ * _).
  by rewrite -mulr_natl divrr // unitfE pnatr_eq0.
rewrite addrA mulN1r div1r -ltr_subl_addl subrr.
pose F : 'I_n.+1 -> R :=
  fun i => (-1) ^+ i.+2 * n.+2%:R ^- 2 ^+ i.+2 *+ 'C(n.+2, i.+2).
rewrite (eq_bigr F); last first.
  by move=> i _; congr (_ *+ _); rewrite /= expr1n mulr1.
rewrite (sum_group_by_2 n.+1
  (fun i => ((-1) ^+ i.+2 * n.+2%:R ^- 2 ^+ i.+2 *+ 'C(n.+2, i.+2)))).
move: n => [|n'] in F *.
  by rewrite /= big_ord0 add0r -signr_odd /= expr0 mul1r.
set n := n'.+1.
set G := BIG_F.
have G_gt0 : forall i, 0 < G i.
  move=> /= i; rewrite /G.
  rewrite -signr_odd /= negbK odd_double expr0 mul1r.
  rewrite -signr_odd /= negbK odd_double /= expr1 mulN1r.
  rewrite mulNrn (@exprSr _ _ i.*2.+2) -mulrnAr -mulr_natr -mulrBr.
  rewrite mulr_gt0 // ?exprn_gt0 //.
  rewrite subr_gt0 -mulr_natr ltr_pdivr_mull // -natrX -natrM.
  move: (@mul_bin_left n.+2 i.*2.+2).
  move/(congr1 (fun x => x%:R : R)).
  move/(congr1 (fun x => (i.*2.+3)%:R^-1 * x)).
  rewrite natrM mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r => ->.
  rewrite 2!natrM mulrA.
  have ? : (i.*2.+1 < n.+2)%nat.
    move: (ltn_ord i).
    rewrite 3!ltnS -(@leq_pmul2r 2) // !muln2 => /leq_trans; apply.
    case/boolP : (odd n') => on'.
      move: (odd_geq n' on'); rewrite leqnn => /esym.
      by move/leq_trans; apply; rewrite leqnSn.
    by move: (@odd_geq n' n on') => <-; rewrite leqnSn.
  rewrite ltr_pmul2r ?ltr0n ?bin_gt0 // ltr_pdivr_mull // -natrM ltr_nat.
  rewrite -(@ltn_add2r i.*2.+2) subnK // ltn_addr // -{1}(mul1n n.+2) -mulnn.
  by rewrite  mulnA ltn_mul2r /= mulSn addSn ltnS addSn.
have sum_G_gt0 : 0 < \big[+%R/0]_i G i.
  rewrite {1}(_ : 0 = \big[+%R/0]_(i < n.+1./2) 0); last by rewrite big1.
  apply: (@lt_leif _ _ _ _ false).
  rewrite (_ : false = [forall i : 'I_n.+1./2, false]); last first.
    apply/idP/forallP => //=; apply; exact: (@Ordinal _ 0).
  apply: leif_sum => i _; exact/leifP/G_gt0.
case: ifPn => no; first by rewrite addr0.
rewrite addr_gt0 //= -signr_odd (negbTE no) expr0 mul1r.
by rewrite pmulrn_lgt0 ?bin_gt0 // exprn_gt0.
Qed.

End euler_seq_increasing.

Lemma cvg_euler_seq : cvg u_.
Proof.
apply: (@near_nondecreasing_is_cvg _ _ 4%:R).
  by apply: nearW => x y ?; rewrite increasing_euler_seq.
by near=> n; rewrite ltW// euler_seq_lt4//; near: n.
Grab Existential Variables. all: end_near. Qed.

Lemma lim_euler_seq_gt2 : 2 < lim u_.
Proof.
apply: (@lt_le_trans _ _ (u_ 2%nat)).
  by rewrite euler_seq2 ltr_pdivl_mulr // -natrM ltr_nat.
rewrite lim_ge//; first exact: cvg_euler_seq.
by near=> n; rewrite increasing_euler_seq; near: n.
Grab Existential Variables. all: end_near. Qed.

Definition euler_constant : R := lim euler_seq.

Lemma euler_constant_gt0 : 0 < euler_constant.
Proof. by rewrite (lt_trans _ lim_euler_seq_gt2). Qed.

Lemma euler_constant_neq1 : euler_constant != 1.
Proof. by rewrite eq_sym lt_eqF // (lt_trans _ lim_euler_seq_gt2) // ltr1n. Qed.

End euler_constant.

(* Density of R (i.e., for any x in R and 0 < a, there is an nonincreasing *)
(* sequence of Q.a that converges to x)                                 *)
Section R_dense.

(*Lemma ratr_fracq (G : realType) (p : int) (q : nat) :
  (p + 1)%:~R / q.+1%:~R = @ratr [unitRingType of G] ((p + 1)%:Q / q.+1%:Q).
Proof. by rewrite rmorph_div /= ?ratr_int // unitfE. Qed.*)

(* sequence in Q.a that converges to x \in R *)
Section rat_approx_R.
Variables (G : archiFieldType) (a x : G) (m : int).

Fixpoint seq_Q (n : nat) : rat :=
  if n is n'.+1 then
    if x - ratr (seq_Q n') * a < ratr (1%:Q / (2^n'.+1)%:Q) * a then
      seq_Q n'
    else if x - ratr (seq_Q n') * a > ratr (1%:Q / (2^n'.+1)%:Q) * a then
           seq_Q n' + 1%:Q / (2^n'.+1)%:Q
         else
           0 (* should not happen *)
  else m%:~R.

Hypothesis a0 : 0 < a.

Lemma nondecreasing_seq_Q : (forall q : rat, x != ratr q * a) -> nondecreasing_seq seq_Q.
Proof.
move=> /(_ _)/negPf xa_alg; apply/nondecreasing_seqP => n /=.
have [//||/eqP] := ltgtP; last by rewrite subr_eq -mulrDl -rmorphD/= xa_alg.
by rewrite ler_addl mulr_ge0 // ltW // invr_gt0 // ltr0z exprn_gt0.
Qed.

Hypothesis xma : x < (m + 1)%:~R * a.

Lemma seq_QP : (forall q : rat, x != ratr q * a) ->
   forall n, x - ratr (seq_Q n) * a < ratr (1%:Q / (2^n)%:Q) * a.
Proof.
move=> xqa; elim => [|n ih] /=.
  by rewrite expr0z divr1 ltr_subl_addr -mulrDl 2!ratr_int -intrD addrC.
case: ifPn => [//|].
rewrite -leNgt le_eqVlt => /orP[abs|H1].
  exfalso; move: abs; apply/negP.
  rewrite eq_sym subr_eq -mulrDl -rmorphD /=; exact: xqa.
rewrite H1 rmorphD /= mulrDl opprD addrA ltr_sub_addr -mulrDl -rmorphD.
rewrite -mulrDl /= -intrD exprSz intrM invrM; last 2 first.
  by rewrite unitfE intr_eq0.
  by rewrite unitfE intr_eq0 expf_neq0.
rewrite mulrCA divrr ?unitfE ?intr_eq0 // mulr1.
by rewrite div1r in ih.
Qed.

Hypothesis max : m%:~R * a <= x.

Lemma seq_Q_ub : (forall q : rat, x != ratr q * a) ->
   forall n, ratr (seq_Q n) * a <= x.
Proof.
move=> xa; elim => [|n unx].
  by rewrite /= ratr_int.
move: (seq_QP xa) => H /=.
case: ifPn => //.
rewrite -leNgt le_eqVlt => /orP[abs|K].
- exfalso.
  move: abs; apply/negP.
  by rewrite eq_sym subr_eq -mulrDl -rmorphD /= xa.
- by rewrite K rmorphD /= mulrDl -lter_sub_addl ltW.
Qed.

End rat_approx_R.

Section rat_approx_R_contd.
Variables (R : realType) (a x : R) (m : int).

Hypothesis a0 : 0 < a.
Hypothesis xma : x < (m + 1)%:~R * a.
Hypothesis max : m%:~R * a <= x.

Lemma is_cvg_seq_Q (xa : (forall q : rat, x != ratr q * a)) :
  cvg (fun n : nat => ratr (seq_Q a x m n) : R^o).
Proof.
apply: (@nondecreasing_is_cvg _ _ (x / a)).
by apply/nondecreasing_seqP => n; rewrite ler_rat; apply: nondecreasing_seq_Q.
by move=> n; rewrite ler_pdivl_mulr //; apply seq_Q_ub => //; exact/ltrW.
Qed.

Lemma cvg_seq_Q (xa : (forall q : rat, x != ratr q * a)) :
  (fun n : nat => ratr (seq_Q a x m n) * a : R^o) --> (x:R^o).
Proof.
apply/cvg_distP => _/posnumP[e].
rewrite near_map; near=> n.
move: (seq_Q_ub xma max xa n) => H1.
rewrite [X in X < _](_ : _ = `|x - ratr (seq_Q a x m n) * a|%R) //.
rewrite ger0_norm // ?subr_ge0 //.
move: (seq_QP xma xa) => H.
rewrite (lt_le_trans (H _)) // -ler_pdivl_mulr // ltW //.
rewrite [X in X < _](_ : _ = `| (0 - ratr (1%:Q / (2 ^ n)%:Q)) : R^o |); last first.
  rewrite distrC subr0 [RHS](_ : _ = `|ratr (1%:~R / (2 ^ n)%:~R)|%R) //.
  by rewrite ger0_norm // ler0q divr_ge0 // ler0z // -exprnP exprn_ge0.
near: n.
have K : (fun n : nat => ratr (1%:~R / (2 ^ n)%:~R) : R^o) --> (0 : R^o).
  rewrite (_ : (fun _ => _) = geometric 1 (2 ^ -1)); last first.
    rewrite funeqE => n; rewrite /geometric /ratr.
    rewrite coprimeq_num ?absz1 ?coprime1n // gtr0_sg ?exprn_gt0 // mul1r.
    rewrite coprimeq_den ?absz1 ?coprime1n // expfz_eq0 andbF div1r.
    by rewrite ger0_norm // ?exprn_ge0 // -exprz_pintl //= mul1r exprVn.
  by apply: cvg_geometric; rewrite gtr0_norm // exprN1 invr_lt1 ?ltr1n // unitfE.
have ea0 : 0 < e%:num / a by rewrite divr_gt0.
by move/cvg_distP : K => /(_ _ ea0) /=; rewrite near_map.
Grab Existential Variables. all: end_near. Qed.

Lemma start_x : (forall q : rat, x != ratr q * a) ->
  {m : int | m%:~R * a < x < (m + 1)%:~R * a}.
Proof.
move=> xa; exists (floor (x / a)); apply/andP; split; last first.
  by rewrite -ltr_pdivr_mulr // intrD -RfloorE lt_succ_Rfloor.
rewrite -ltr_pdivl_mulr // lt_neqAle -{2}RfloorE Rfloor_le andbT.
apply/negP => /eqP H.
move: (xa (floor (x / a))%:~R) => /negP; apply; apply/eqP.
by rewrite ratr_int H -mulrA mulVr ?mulr1 // unitfE gt_eqF.
Qed.

End rat_approx_R_contd.

Lemma R_dense_corollary (R : realType) (a x : R) (a0 : 0 < a) :
  {x_ : rat ^nat | nondecreasing_seq x_ /\
    cvg (fun n => ratr (x_ n) : R^o) /\ lim (fun n => ratr (x_ n) * a : R^o) = x}.
Proof.
have [xa|xa] := pselect (forall q : rat, x != ratr q * a); last first.
  have [q xqa] : {q : rat | x = ratr q * a}.
    apply/cid/asboolP/negPn/negP => abs; apply xa => {xa} q.
    apply: contra abs => /eqP ->.
    by apply/asboolP; exists q.
  exists (fun=> q); split => //.
  split; first exact: is_cvg_cst.
  by rewrite xqa; exact: lim_cst.
have [m /andP[max xma]] := start_x a0 xa.
set x0 := m%:~R * a; set x_ := seq_Q a x m; exists (seq_Q a x m).
split; first exact: nondecreasing_seq_Q.
split; first by apply: is_cvg_seq_Q => //; rewrite addrC in xma => //; exact/ltW.
by apply/cvg_lim => //; apply/cvg_seq_Q => //; exact/ltW.
Qed.

End R_dense.

(* PR in progress *)
Lemma dvg_harmonic (R : numFieldType) : ~ cvg (@series [zmodType of R^o] harmonic).
Proof.
have ge_half n : (0 < n)%N -> 2^-1 <= \sum_(n <= i < n.*2) harmonic i.
  case: n => // n _.
  rewrite (@le_trans _ _ (\sum_(n.+1 <= i < n.+1.*2) n.+1.*2%:R^-1)) //=.
    rewrite sumr_const_nat -addnn addnK addnn -mul2n natrM invfM.
    by rewrite -[_ *+ n.+1]mulr_natr divfK.
  by apply: ler_sum_nat => i /andP[? ?]; rewrite lef_pinv ?qualifE ?ler_nat.
move/cvg_cauchy/cauchy_ballP => /(_ _ 2^-1%:pos); rewrite !near_map2.
rewrite -ball_normE => /nearP_dep hcvg; near \oo => n; near \oo => m.
have: `|series harmonic n - series harmonic m| < 2^-1 :> R by near: m; near: n.
rewrite le_gtF// distrC -[X in X - _](addrNK (series harmonic n.*2)).
rewrite sub_series_geq; last by near: m; apply: nbhs_infty_ge.
rewrite -addrA sub_series_geq -addnn ?leq_addr// addnn.
have sh_ge0 i j : 0 <= \sum_(i <= k < j) harmonic k :> R.
  by rewrite ?sumr_ge0//; move=> k _; apply: harmonic_ge0.
by rewrite ger0_norm ?addr_ge0// ler_paddl// ge_half//; near: n.
Grab Existential Variables. all: end_near. Qed.
(* /PR in progress *)

Section riemann_sequence.
Variable R : realType.
Variable pow_fun : forall a : R, R -> R.
Local Notation "a `^ x" := (pow_fun a x).
Hypothesis pow_fun_gt0 : forall a : R, 0 < a -> (forall x, 0 < a `^ x).
Hypothesis pow_funa1 : forall a : R, 0 < a -> a `^ 1 = a.
Hypothesis pow_fun1 : pow_fun 1 = fun=> 1.
Hypothesis pow_fun_homo_leq :
  forall a : R, 1 < a -> {homo pow_fun a : x y / x <= y}.
Hypothesis pow_fun_morph :
  forall a : R, 0 < a -> {morph pow_fun a : x y / x + y >-> x * y}.
Hypothesis pow_funa0 : forall a : R, 0 < a -> a `^ 0 = 1.
(*
Hypothesis pow_fun_homo_geq :
  forall a : R, 0 < a -> a < 1 -> {homo pow_fun a : x y / x >= y}. *)

Lemma pow_fun_inv (a : R) : 0 < a -> a `^ (-1) = a ^-1.
Proof.
move=> a0.
apply/(@mulrI _ a); first by rewrite unitfE gt_eqF.
rewrite -{1}(pow_funa1 a0) -pow_fun_morph // subrr pow_funa0 //.
by rewrite divrr // unitfE gt_eqF.
Qed.

Lemma pow_fun_mulrn (a : R) (n : nat) : 0 < a -> pow_fun a n%:R = a ^+ n.
Proof.
move=> a0; elim: n => [|n ih]; first by rewrite mulr0n expr0 pow_funa0.
by rewrite -addn1 natrD pow_fun_morph // exprD ih pow_funa1.
Qed.

(*Definition exp_fun : R -> R := pow_fun exp_base.*)

Definition riemann (a : R) : R^o ^nat := fun n => (n.+1%:R `^ a)^-1.
Arguments riemann a n /.

Lemma riemann_gt0 a i : 0 < a -> 0 < riemann a i.
Proof. move=> ?; by rewrite /riemann invr_gt0 pow_fun_gt0. Qed.

Lemma dvg_riemann (a : R): 0 < a <= 1 -> ~ cvg (series (riemann a)).
Proof.
case/andP => a0; rewrite le_eqVlt => /orP[/eqP ->|a1].
  rewrite (_ : riemann 1 = harmonic); first exact: dvg_harmonic.
  by rewrite funeqE => i /=; rewrite pow_funa1.
have : forall n, harmonic n <= riemann a n.
  case=> /= [|n]; first by rewrite pow_fun1 invr1.
  rewrite -[X in _ <= X]div1r ler_pdivl_mulr ?pow_fun_gt0 // mulrC.
  rewrite ler_pdivr_mulr // mul1r -[X in _ <= X]pow_funa1 //.
  by rewrite (pow_fun_homo_leq) // ?ltr1n // ltW.
move/(series_le_cvg harmonic_ge0 (fun i => ltW (riemann_gt0 i a0))).
by move/contra_not; apply; exact: dvg_harmonic.
Qed.

End riemann_sequence.
