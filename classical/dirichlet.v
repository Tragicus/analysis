From HB Require Import structures.
From mathcomp Require Import all_ssreflect boolp ssralg functions.
Import Order.OrdinalOrder Order.POrderTheory GRing.Theory.
Local Open Scope order_scope.
Local Open Scope nat_scope.
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma mem_allpairs (S T : eqType) (s : seq S) (t : seq T)
    (x : S) (y : T) : (x, y) \in allpairs pair s t = (x \in s) && (y \in t).
Proof.
elim: s => //= a s IHs.
rewrite mem_cat in_cons andb_orl {}IHs; congr orb.
elim: t => /= [|b t IHt]; first by rewrite andbF.
by rewrite !in_cons IHt andb_orr.
Qed.

Lemma uniq_allpairs (S T : eqType) (s : seq S) (t : seq T) :
  uniq (allpairs pair s t) = ((uniq s || (t == [::])) && ((s == [::]) || uniq t)).
Proof.
elim: s t => //= x s IHs t.
rewrite cat_uniq {}IHs.
case: t => [/=|y t]; first by rewrite !orbT !andbT has_pred0.
rewrite !orbF andbCA -andbA; congr (~~ _ && _).
  case/boolP: (x \in s) => [|/negP] xs.
    apply/hasP; exists (x, y); first by rewrite mem_allpairs xs mem_head.
    by rewrite mem_map ?mem_head// => a b [].
  apply/negP/negP.
  rewrite -all_predC; apply/allP => -[] a b.
  rewrite mem_allpairs => /andP[] aP _ /=; apply/negP.
  elim: t => /= [/andP[]/eqP[] ax _ _|c t IHt]; first by rewrite ax in aP.
  rewrite !in_cons orbCA => /orP[] // /eqP[] ax _.
  by rewrite ax in aP.
rewrite map_inj_uniq => [|a b [] //].
case: s => [/=|z s]; first by rewrite andbT.
by rewrite andbCA; congr andb => /=; rewrite andbb.
Qed.

Lemma allpairs_nilr (S T R : eqType) (f : S -> T -> R) (s : seq S) :
  allpairs f s [::] = [::].
Proof. by elim: s. Qed.

Lemma allpairs_consr (S T R : eqType) (f : S -> T -> R) (s : seq S) (x : T) (t : seq T) :
  perm_eq (allpairs f s (x :: t)) ([seq f y x | y <- s] ++ allpairs f s t).
Proof.
elim: s => [|y s IHs] //=.
rewrite perm_cons.
move: IHs; rewrite -(perm_cat2l [seq f y z | z <- t]) => /perm_trans; apply.
by rewrite perm_catCA !perm_cat2l.
Qed.

Lemma swap_allpairs (S T : eqType) (s : seq S) (t : seq T) :
  perm_eq [seq (x.2, x.1) | x <- allpairs pair s t] (allpairs pair t s).
Proof.
elim: s => [|x s IHs]; first by rewrite allpairs_nilr.
rewrite perm_sym.
apply: (perm_trans (allpairs_consr _ _ _ _)) => /=.
by rewrite map_cat -map_comp perm_cat2l perm_sym.
Qed.

Lemma if_arg (A B : Type) (b : bool) (fT fF : A -> B) :
  (if b then fT else fF) = fun x => if b then fT x else fF x.
Proof. apply: funext => x; apply: if_arg. Qed.

Section Dirichlet.
Variable (R : comSemiRingType).

Definition dirichlet := nat -> R.

(* N.B. This is not standard because I want my functions to be defined at 0 and
  (eq_op 1) to be neutral. *)
Definition dirichlet_mul (f g : dirichlet) n :=
  \sum_(0 <= d1 < n.+2) \sum_(0 <= d2 < n.+2 | (d1 * d2)%N == n) f d1 * g d2.

Local Notation "f \* g" := (dirichlet_mul f g). 

Lemma dirichlet_mul1f f : (fun n => (n == 1)%:R) \* f = f.
Proof.
apply/funext => -[|n].
  rewrite /dirichlet_mul !big_nat_recr//= big_geq// big_geq//=.
  rewrite !mul0r !add0r.
  under eq_bigl do rewrite mul1n.
  by rewrite big_nat1_eq/= mul1r.
rewrite /dirichlet_mul.
under eq_bigr => d1 _.
  rewrite big_mkcond/=.
  under eq_bigr => d2 _.
    have -> : (d1 == 1)%:R * f d2 = if d1 == 1 then f d2 else 0.
      by case: ifP => _; [apply: mul1r|apply: mul0r].
    rewrite -if_and andbC if_and.
    over.
  over.
rewrite exchange_big/=.
under eq_bigr => d2 _.
  rewrite -big_mkcond big_nat1_eq/= mul1n.
  over.
by rewrite -big_mkcond/= big_nat1_eq/= leqnSn.
Qed.

Lemma dirichlet_mulC : commutative dirichlet_mul.
Proof.
move=> f g.
apply/funext => n.
rewrite /dirichlet_mul.
rewrite (exchange_big_dep xpredT)//=.
under eq_bigr => ? _.
  under eq_bigl do rewrite mulnC.
  under eq_bigr do rewrite mulrC.
  over.
by [].
Qed.

Lemma big_dirichlet_mulE I F k (r : k.-tuple I) n :
  (\big[dirichlet_mul/(fun n => (n == 1)%:R)]_(f <- r) F f) n =
  \sum_(x : k.-tuple 'I_n.+2 | \prod_(d <- x) (d : nat) == n)
      \prod_(i < k) F (tnth r i) (tnth x i).
Proof. 
elim: k r n => [|k IHk] r n.
  rewrite tuple0 big_nil.
  rewrite big_mkcond.
  under eq_bigl => x.
    move: (tuple0 x) => /eqP <-.
    over.
  rewrite big_pred1_eq_id/= !big_ord0 big_nil addr0 eq_sym.
  by case: ifP.
rewrite (tuple_eta r).
move: (thead r) => f.
rewrite big_cons [LHS]/dirichlet_mul.
under eq_bigr => d1 _.
  under eq_bigr do rewrite (IHk (Tuple (behead_tupleP r))) mulr_sumr.
  over.
rewrite [X in bigop _ _ X]/=.
transitivity (\sum_(x : 'I_n.+2 * k.-tuple 'I_n.+2 | (x.1 : nat) * \prod_(d <- x.2) (d : nat) == n) F f x.1 * \prod_(i < k) F (tnth (behead r) i) (tnth x.2 i)); last first.
  rewrite big_mkcond/=.
  under eq_bigl => x.
    have <- : x \in setT by [].
    over.
  have ->: finset.setT = [set ((thead x), (Tuple (behead_tupleP x))) | x in [set: k.+1.-tuple 'I_n.+2]].
    apply/eqP; rewrite eqEsubset; apply/andP; split=> //.
    apply/subsetP => -[]/= x s _.
    have xsk: size (x :: s) == k.+1 by rewrite /= eqSS (valP s).
    apply/imsetP; exists (Tuple xsk); first exact: in_setT.
    by congr pair; apply/val_inj.
  rewrite big_imset => [|x y _ _ [] xyh xyb]; last first.
    rewrite (tuple_eta x) (tuple_eta y); apply/val_inj => /=.
    by rewrite xyh xyb.
  under eq_bigl do rewrite in_setT.
  rewrite -big_mkcond.
  apply: eq_big => x /=.
    by rewrite [in RHS](tuple_eta x) big_cons.
  move=> _; rewrite big_ord_recl [in RHS](tuple_eta x) !tnth0; congr GRing.mul.
  by apply eq_bigr => d _; rewrite !tnthS.
rewrite -(pair_big_dep xpredT
  (fun (d : 'I_n.+2) (s : k.-tuple 'I_n.+2) => (d : nat) * \prod_(d <- s) (d : nat) == n)
  (fun d s => F f d * \prod_(i < k) F _ (tnth s i)))/=.
case: n => [|n].
  rewrite big_nat_recl//.
  under eq_bigl do rewrite eqxx.
  rewrite !big_nat_recl// big_geq// addrC.
  under eq_bigl do rewrite mul1n.
  rewrite big_nat1_eq/= big_geq// !addr0.
  under [X in _ + (_ + X)]eq_bigl => x.
    set G := x \in [set map_tuple (widen_ord (erefl : 2 <= 3)) x | x : k.-tuple 'I_2].
    set H := \prod_(d <- x) (d : nat) == 1%N.
    have <-: G && H = H.
      rewrite /H big_tuple; apply: andb_idl => /eqP x1.
      suff x2 i : tnth x i < 2.
        apply/imsetP; exists (mktuple (fun i => Ordinal (x2 i))) => //.
        apply: eq_from_tnth => i.
        by rewrite tnth_map; apply: val_inj; rewrite tnth_mktuple.
      move: (valP (tnth x i)); rewrite leq_eqVlt => /orP[|//]. 
      rewrite eqSS => /eqP xi3.
      suff: 2 %| 1 by [].
      rewrite -xi3 -[X in _ %| X]x1.
      by rewrite (bigD1 i)//= dvdn_mulr.
    rewrite /G /H.
    over.
  rewrite big_imset_cond/=; last first.
    move=> x y _ _ /(congr1 val) /inj_map xy.
    apply/val_inj/xy => {xy}x {}y /(congr1 val)/= xy.
    exact: val_inj.
  under [X in _ + (_ + X)]eq_bigl do rewrite big_map/=.
  rewrite [X in _ + (X + _)]big_mkcond [X in _ + (_ + X)]big_mkcond/=.
  rewrite -[X in _ + X]big_split/=.
  under [X in _ + X]eq_bigr => x _.
    under [in X in _ + if _ then X else _]eq_bigr do rewrite tnth_map/=.
    set G := _ * _.
    set H := _ + _.
    have -> : H = G.
      rewrite /H.
      have: \prod_(d <- x) d <= 1.
      have p1: (\prod_(d <- x) 1 = 1)%N by apply: big1_eq.
      rewrite -[X in _ <= X]p1.
      by apply: leq_prod => i _; apply: (valP i).
      rewrite leq_eqVlt => /orP[/eqP ->|]; first by rewrite add0r.
      by rewrite ltnS leqn0 => /eqP ->; rewrite addr0.
    over.
  rewrite !big_ord_recl big_ord0 addr0.
  under [in RHS]eq_bigl do rewrite eqxx.
  rewrite addrC; congr GRing.add.
  by apply: eq_big => // i; rewrite mul1r.
rewrite big_mkord; apply: eq_bigr => -[] d dn _.
rewrite big_mkcond/= big_nat_recr//=.
case: ifPn => [/eqP/esym dnn|_].
  have: n.+2 %| n.+1 by apply/dvdnP; exists d.
  by move=> /dvdn_leq-/(_ erefl); rewrite ltnn.
rewrite addr0 big_nat.
under eq_bigr => d0 d0n.
  have s0: \sum_(i : k.-tuple 'I_d0.+2 | \prod_(d1 <- i) (d1 : nat) == d0) 0
      = 0 :> R by apply big1_eq.
  rewrite -[X in if _ then _ else X]s0 -!fun_if if_arg.
  under [X in bigop _ _ X]funext do rewrite -!fun_if.
  under eq_bigr => d1 _.
    under eq_bigr => i _.
      have ->: tnth d1 i = tnth (map_tuple (@widen_ord d0.+2 n.+3 d0n) d1) i :> nat.
        by rewrite tnth_map.
      over.
    over.
  under eq_bigl => d1.
    rewrite -(big_map (widen_ord (d0n : d0.+1 < n.+3)) xpredT (@nat_of_ord _)).
    rewrite -[_ == _]andTb -[X in X && _](in_setT d1).
    over.
  rewrite [X in bigop _ _ X]/=.
  rewrite -(@big_imset_cond _ _ _ _ _
    (map_tuple (widen_ord (d0n : d0.+1 < n.+3))) _
    (fun s => \prod_(d1 <- s) (d1 : nat) == d0)
    (fun s => if _ then _ * \prod_(i < k) F _ (tnth s i) else 0))/=; last first.
    move=> x y _ _ /(congr1 val) /inj_map xy.
    apply/val_inj/xy => {xy}x {}y /(congr1 val)/= xy.
    exact: val_inj.
  under eq_bigl => x.
    set G := in_mem _ _.
    have -> : G = [forall i, tnth x i < d0.+2].
      apply/imsetP/forallP => /=.
      move=> [] s _ -> i.
        rewrite tnth_map; apply: (valP (tnth s i)).
      move=> xlt.
      exists (mktuple (fun i => Ordinal (xlt i))) => //.
      apply: eq_from_tnth => i.
      rewrite tnth_map; apply/val_inj => /=.
      by rewrite tnth_mktuple.
    over.
  over.
rewrite -big_nat (exchange_big_dep xpredT)//=.
rewrite [RHS]big_mkcond/=.
apply: eq_bigr => x _.
rewrite big_mkcondl/=.
under eq_bigl do rewrite eq_sym.
rewrite big_nat1_eq/= -!if_and.
congr (if _ then _ else _).
rewrite andb_idl// => /eqP/esym dpn.
rewrite ltnS dvdn_leq//=; last first.
  by apply/dvdnP; exists d.
apply/forallP => i.
move: dpn.
rewrite big_tuple (bigD1 i)//= ltnS => dpn; apply/ltnW; rewrite ltnS.
apply: leq_pmulr; rewrite lt0n; apply/negP => /eqP p0.
by move: dpn; rewrite p0 mulr0 muln0.
Qed.

Lemma dirichlet_mulA : associative dirichlet_mul.
Proof.
move=> f g h.
transitivity ((\big[dirichlet_mul/(fun n => (n == 1)%:R)]_(f <- in_tuple [:: f; g; h]) f)).
  by rewrite !big_cons big_nil [h \* _]dirichlet_mulC dirichlet_mul1f.
rewrite dirichlet_mulC.
transitivity ((\big[dirichlet_mul/(fun n => (n == 1)%:R)]_(f <- in_tuple [:: h; f; g]) f)); last first.
  by rewrite !big_cons big_nil [g \* _]dirichlet_mulC dirichlet_mul1f.
apply/funext => n.
rewrite !big_dirichlet_mulE.
have mod3 i: (i %% 3 < 3)%N by rewrite ltn_mod.
under eq_bigl => x.
  have x3: x \in [set mktuple (fun i => tnth x (Ordinal (mod3 i.+1))) | x : 3.-tuple 'I_n.+2].
    apply/imsetP; exists (mktuple (fun i => tnth x (Ordinal (mod3 i.+2)))) => //.
    apply: eq_from_tnth => -[] i i3.
    rewrite !tnth_mktuple; congr tnth; apply: val_inj => /=.
    by rewrite -addn2 modnDml addSn -addnS -modnDmr modnn addn0 modn_small.
  rewrite -[_ == _]andTb -[X in X && _]x3.
  over.
rewrite big_imset_cond/=; last first.
  move=> x y _ _ /(congr1 (@tnth _ _)); rewrite funeqE => xy.
  apply: eq_from_tnth => i.
  move: (xy (Ordinal (mod3 i.+2))).
  rewrite !tnth_mktuple/=.
  set j := Ordinal _; suff -> : j = i by [].
  apply: val_inj => /=.
  by rewrite -addn1 modnDml -addn2 -addnA -modnDmr modnn addn0 modn_small.
apply: eq_big => x => [|_].
  congr eq_op; apply: perm_big.
  case: x => -[]// a []// b []// c []//= eq33.
  rewrite !enum_ordSr enum_ord0/= !(tnth_nth ord0)/=.
  by rewrite (perm_catC [:: b; c] [:: a]).
rewrite !big_ord_recr !big_ord0/= !mul1r !(tnth_nth f)/= !(tnth_nth ord0)/=.
rewrite !enum_ordSr !enum_ord0/= !(tnth_nth ord0)/=.
by rewrite mulrC mulrA.
Qed.

Lemma dirichlet_mulDl : left_distributive dirichlet_mul +%R.
Proof.
move=> f g h; apply: funext => n; rewrite /dirichlet_mul !fctE/=.
rewrite -big_split/=; apply: eq_bigr => d1 _.
rewrite -big_split/=; apply: eq_bigr => d2 _.
exact: mulrDl.
Qed.


Lemma dirichlet_mul0f : left_zero 0 dirichlet_mul.
Proof.
move=> f; apply: funext => n; rewrite /dirichlet_mul.
under eq_bigr => d1 _.
  under eq_bigr do rewrite mul0r.
  rewrite big1//.
  over.
exact: big1.
Qed.

Lemma dirichlet_mul10 : (fun n => (n == 1)%:R) != 0 :> dirichlet.
Proof.
by apply/negP => /eqP; rewrite funeqE => /(_ 1)/eqP; rewrite oner_eq0.
Qed.

HB.instance Definition _ := Monoid.isComLaw.Build _ _ dirichlet_mul
  dirichlet_mulA dirichlet_mulC dirichlet_mul1f.

HB.instance Definition _ := GRing.Nmodule.on dirichlet.

HB.instance Definition _ := GRing.Nmodule_isComNzSemiRing.Build dirichlet
  dirichlet_mulA dirichlet_mulC dirichlet_mul1f dirichlet_mulDl dirichlet_mul0f dirichlet_mul10.

Lemma dirichlet_mulE_dvdn (f g : dirichlet) (n : nat) : 0 < n ->
  (f * g) n = \sum_(1 <= d < n.+1 | d %| n) f d * g (n %/ d).
Proof.
move=> n0.
rewrite [LHS]big_nat_recr//= addrC big_pred0; last first.
  move=> d.
  apply/eqP => /esym nd.
  have: n.+1 %| n by apply/dvdnP; exists d; rewrite mulnC.
  by move=> /dvdn_leq-/(_ n0); rewrite ltnn.
rewrite add0r big_ltn// big_pred0//; last first.
  by move=> d; rewrite mul0n eq_sym eqn0Ngt n0.
rewrite add0r [RHS]big_mkcond [LHS]big_nat [RHS]big_nat.
apply: eq_bigr => d /andP[] d0 dn.
  case: ifPn => dn'; last first.
  rewrite big_pred0// => d1.
  apply/negP/negP; move: dn'; apply: contra => /eqP/esym dn'.
  by apply/dvdnP; exists d1; rewrite mulnC.
under eq_bigl do rewrite eq_sym mulnC eqn_mul// eq_sym.
rewrite big_nat1_eq/= ltnS.
suff ->: (n %/ d <= n.+1) by [].
exact: (leq_trans (leq_div _ _)).
Qed.

Definition multiplicative (f : nat -> R) :=
  forall n m, coprime n m -> f (n * m)%N = f n * f m.

Lemma dvdnM (k m n : nat) : ((0 < k) || (0 < m)) -> (k %| m * n = (k %/ gcdn k m %| n)).
Proof.
case: k => /=; first by rewrite div0n !dvd0n muln_eq0 lt0n => /negPf ->.
move=> k _.
have km0: 0 < gcdn k.+1 m by rewrite gcdn_gt0.
move: (gcdn k.+1 m) km0 (dvdn_gcdl k.+1 m) (dvdn_gcdr k.+1 m) ((dvdn_gcd^~ k.+1)^~ m).
move=> d d0 /dvdnP[] a -> /dvdnP[] b -> dP.
rewrite mulnAC dvdn_pmul2r// mulnK// Gauss_dvdr//.
move: (dP ((gcdn a b) * d)); rewrite !dvdn_pmul2r// dvdn_gcdl dvdn_gcdr.
by rewrite -dvdn_divRL// divnn d0/= dvdn1.
Qed.

Lemma gcdnZ (k m n : nat) : (k * gcdn m n = gcdn (k * m) (k * n))%N.
Proof.
case: k => // k.
(apply/esym/gcdn_def; rewrite ?dvdn_pmul2l//) => [||d].
- exact: dvdn_gcdl.
- exact: dvdn_gcdr.
have dn0 : 0 < gcdn d k.+1 by rewrite gcdn_gt0 orbT.
case: d dn0 => [|d] dn0; first by rewrite !dvd0n !muln_eq0/= => /eqP -> /eqP ->.
by rewrite !dvdnM// dvdn_gcd => ->.
Qed.

Lemma coprime_gcdn (k m n : nat) : coprime m n -> coprime (gcdn k m) (gcdn k n).
Proof.
move=> /eqP mn; apply/eqP/gcdn_def => // d.
by rewrite -mn !dvdn_gcd => /andP[] _ -> /andP[] _.
Qed.

Lemma mulnI (k : nat) : 0 < k -> injective (muln k).
Proof.
by move=> k0 => m n /(congr1 (divn^~ k)); rewrite mulnC mulnK// mulnC mulnK.
Qed.

Lemma gcdnM (k m n : nat) : coprime m n -> (gcdn k (m * n) = gcdn k m * gcdn k n)%N.
Proof.
move=> /[dup] mn /(coprime_gcdn k) kmn.
apply/gcdn_def.
- by rewrite Gauss_dvd// !dvdn_gcdl.
- by apply: dvdn_mul; apply: dvdn_gcdr.
case=> [|d dk].
  by rewrite !dvd0n muln_eq0 => /eqP -> /orP[] /eqP -> //; rewrite muln0.
rewrite dvdnM// => dmn.
have dm0 : 0 < gcdn d.+1 m by rewrite gcdn_gt0.
rewrite -(mulKn d.+1 dm0) -muln_divA; last exact: dvdn_gcdl.
apply: dvdn_mul; rewrite dvdn_gcd; apply/andP; split=> //.
- exact/(dvdn_trans _ dk)/dvdn_gcdl.
- exact: dvdn_gcdr.
- by rewrite -dvdnM// dvdn_mull.
Qed.

Lemma gcdn_prod (I : Type) (r : seq I) (P : pred I) (F : I -> nat) k :
  pairwise coprime [seq F i | i <- r & P i] ->
  (gcdn k (\prod_(i <- r | P i) F i) = \prod_(i <- r | P i) gcdn k (F i))%N.
Proof.
elim: r k => [k _|x r IHr k]; first by rewrite !big_nil gcdn1.
rewrite !big_cons/=; case: ifP => Px; last exact: IHr.
move=> /= /andP[] xr rc.
rewrite gcdnM ?IHr// /coprime IHr//.
elim: r xr {rc IHr} => [_|y r IHr]/=; first by rewrite big_nil.
rewrite big_cons; case: ifP => Py//= /andP[] /eqP -> /IHr.
by rewrite mul1n.
Qed.

Lemma coprimeW (k l m n : nat) : k %| m -> l %| n -> coprime m n -> coprime k l.
Proof.
move=> km ln /eqP mn; apply/eqP/gcdn_def => // d dk dl.
rewrite -mn dvdn_gcd; apply/andP; split; first exact: (dvdn_trans dk).
exact: (dvdn_trans dl).
Qed.

Lemma dirichlet_mul_multiplicative (f g : dirichlet) :
  multiplicative f -> multiplicative g -> multiplicative (f * g).
Proof.
move=> fm gm n m.
wlog: n m / (n <= m)%N => nm.
  move: (leq_total n m) => /orP[/nm //|mn].
  rewrite coprime_sym mulnC [RHS]mulrC.
  exact: (nm _ _ mn).
case: n nm => [_|n nm].
  rewrite /coprime gcd0n => /eqP ->.
  rewrite mul0n [_ 0%N]big_nat_recl// [X in (X + _)]big_nat_recl// !big_nat1.
  under eq_bigl do rewrite mul1n.
  rewrite big_nat1_eq/= [X in _ = _ * X]big_nat_recl//= big_pred0//= add0r.
  rewrite big_nat_recl//=.
  under eq_bigl do rewrite mul1n.
  rewrite big_nat1_eq/= big_nat1.
  under eq_bigl => d.
    have ->: (2 * d)%N == 1 = false.
      apply/eqP => /esym d2.
      suff: 2 %| 1 by [].
      by apply/dvdnP; exists d; rewrite mulnC.
    over.
  rewrite big_pred0// addr0 !mulrDl mulrACA.
  move: (fm 0 1 erefl) (gm 0 1 erefl).
  rewrite mul0n => fm1 gm1.
  rewrite -fm1 -gm1 mulrACA -fm1 mulrACA -gm1 -(fm 1 1 erefl) -(gm 1 1 erefl).
  by rewrite muln1.
case: m nm => // m _ nm.
rewrite dirichlet_mulE_dvdn// big_add1/= big_mkord.
under eq_bigl => d.
  set b := _ %| _.
  have -> : b = (d \in [set d : 'I_(n.+1 * m.+1) | d.+1 %| n.+1 * m.+1]).
    by rewrite inE.
  over.
rewrite [X in bigop _ _ X]/=.
have ltnm (d0 : 'I_n.+1) (d1 : 'I_m.+1) : (d0.+1 * d1.+1).-1 < n.+1 * m.+1.
  by rewrite prednK// leq_mul.
have ->: [set d0 : 'I_(n.+1 * m.+1) | d0.+1 %| (n.+1 * m.+1)%R] = [set (Ordinal (ltnm d.1 d.2)) | d in [set d : 'I_n.+1 * 'I_m.+1 | (d.1.+1 %| n.+1) && (d.2.+1 %| m.+1)]].
  apply/eqP; rewrite eqEsubset.
  apply/andP; split; apply/subsetP => d; rewrite inE; last first.
    move=> /imsetP[] [] d0 d1; rewrite inE/= => /andP[] dn dm ->.
    exact: (dvdn_mul dn dm).
  move=> /gcdn_idPl; rewrite gcdnM// => /esym dE.
  have dn0 : 0 < gcdn d.+1 n.+1 by rewrite gcdn_gt0.
  have dn : (gcdn d.+1 n.+1).-1 < n.+1.
    by rewrite prednK//; apply: dvdn_leq => //; apply: dvdn_gcdr.
  have dm0 : 0 < gcdn d.+1 m.+1 by rewrite gcdn_gt0.
  have dm : (gcdn d.+1 m.+1).-1 < m.+1.
    by rewrite prednK//; apply: dvdn_leq => //; apply: dvdn_gcdr.
  apply/imsetP; exists (Ordinal dn, Ordinal dm).
    by rewrite inE; apply/andP; split; rewrite /= prednK//; apply: dvdn_gcdr.
  by apply/val_inj/succn_inj; rewrite [RHS]prednK/= !prednK// muln_gt0 !gcdn_gt0.
rewrite big_imset/= => [|[] a1 a2 [] b1 b2]; last first.
  rewrite !inE/= => /andP[] an am /andP[] bn bm.
  move=> /(congr1 val)/(congr1 succn)/=.
  rewrite -[LHS]/(a1.+1 * a2.+1) -[RHS]/(b1.+1 * b2.+1).
  move=> /[dup]/(congr1 (gcdn n.+1)).
  rewrite Gauss_gcdl; last exact: (coprimeW (dvdnn _) am).
  rewrite Gauss_gcdl; last exact: (coprimeW (dvdnn _) bm).
  rewrite gcdnC (gcdn_idPl an) gcdnC (gcdn_idPl bn) => /succn_inj a1E.
  rewrite a1E => /mulnI-/(_ erefl)/succn_inj a2E.
  by apply/pair_equal_spec; split; apply: val_inj.
under eq_bigl do rewrite inE.
rewrite -(pair_big (fun i => (val i).+1 %| n.+1) (fun i => (val i).+1 %| m.+1)
  (fun i j => f ((val i).+1 * (val j).+1)%N *
              g ((n.+1 * m.+1) %/ ((val i).+1 * (val j).+1))%N))/=.
under eq_bigr => i din.
  under eq_bigr => j djn.
    rewrite fm; last exact: (coprimeW din djn).
    rewrite divnMA -divn_mulAC// -muln_divA// gm; last first.
      by apply: (coprimeW _ _ nm); apply: dvdn_div.
    rewrite mulrACA.
    over.
  rewrite -mulr_sumr.
  over.
by rewrite -mulr_suml !dirichlet_mulE_dvdn// !big_add1/= !big_mkord.
Qed.


Lemma multiplicative_prod (I : Type) (r : seq I) (P : pred I) (F : I -> nat)
    f : multiplicative f ->
  pairwise coprime [seq F i | i <- [seq i <- r | P i]] ->
  ~~ nilp [seq i <- r | P i] ->
  f (\prod_(i <- r | P i) F i) = \prod_(i <- r | P i) f (F i).
Proof.
move=> fm; elim: r => [//|] x r IHr/=.
rewrite !big_cons; case: ifPn => Px//= /andP[] xr rc _.
rewrite fm; last first.
  rewrite /coprime gcdn_prod//.
  elim: r xr {IHr rc} => [|y r IHr]/=; first by rewrite big_nil.
  rewrite big_cons/=; case: ifP => Py//= /andP[] /eqP -> /IHr.
  by rewrite mul1n.
rewrite -big_filter -[in RHS]big_filter.
move: IHr; rewrite -big_filter -[RHS]big_filter.
move: (filter _ _) rc => -[rc _|y s rc -> //].
rewrite !big_nil mulr1.
by move: (fm (F x) 1 (coprimen1 _)) => <-; rewrite muln1.
Qed.

Lemma coprime_primes n : pairwise coprime (primes n).
Proof.
apply/(pairwiseP 0) => i j /[dup] ilt + /[dup] jlt; rewrite !inE.
move=> /(mem_nth 0) ip /(mem_nth 0) jp ij.
move: (all_prime_primes n) => /allP pp.
rewrite prime_coprime; last exact: pp.
rewrite dvdn_prime2; try exact: pp.
apply/eqP.
move: (primes_uniq n) => /(uniqP 0)/(_ i j ilt jlt)/[apply].
by move: ij => /[swap] ->; rewrite ltnn.
Qed.

Lemma eq_multiplicative f g : multiplicative f -> multiplicative g ->
  f 0 = g 0 -> (forall p k, prime p -> f (p ^ k) = g (p ^ k)) -> f = g.
Proof.
move=> fm gm fg0 fg.
apply/funext => -[//|] n.
rewrite (@prod_prime_decomp n.+1)// prime_decompE big_map.
case: n => [|n]/=; first by rewrite big_nil (fg 2 0).
have ?: ~~ nilp [seq _ <- primes n.+2 | true]
  by rewrite filter_predT /nilp size_eq0 primes_eq0. 
have ?: pairwise coprime [seq i ^ logn i n.+2 | i <- primes n.+2 & true].
  rewrite filter_predT pairwise_map.
  apply: (sub_pairwise _ (coprime_primes _)) => a b ab.
  exact/coprimeXr/coprimeXl.
rewrite !multiplicative_prod// big_seq [RHS]big_seq.
apply: eq_bigr => i.
rewrite mem_primes => /andP[] ip _.
exact: fg.
Qed.

End Dirichlet.

HB.instance Definition _ (R : comRingType) := GRing.Zmodule.on (dirichlet R).

Definition mobius (R : comNzRingType) : dirichlet R := fun n =>
  ((n != 0) && all (fun p => logn p n == 1) (primes n))%:R *
  (-1) ^+ (size (primes n)).

Section DirichletUnit.
(* TODO weaken to rings with decidable divisibility. *)
Variable (R : fieldType).

Notation dirichlet := (dirichlet R).

(* N.B. This definition is compatible with the weakening to comUnitRingType but
  the actual second hypothesis should be (f 0 + f 1 %| f 0) in a ring with
  decidable divisibility. *)
Definition dirichlet_unit (f : dirichlet) := 
  (f 1 \is a GRing.unit) && (f 0 + f 1 \is a GRing.unit).

Fixpoint dirichlet_inv_subdef (f : dirichlet) (s : seq R) n :=
  match n with
  | 0 => [:: - f 0 / (f 1 * (f 0 + f 1))]
  | n.+1 => 
    let s := dirichlet_inv_subdef f s n in
    match n with
    | 0 => (f 1)^-1
    | n.+1 => - ((((fun k => (k <= n.+1)%:R * s`_(n.+1 - k)) : dirichlet) * f) n.+2) / f 1
    end :: s
  end.

Definition dirichlet_inv (f : dirichlet) (n : nat) :=
  if ~~ (f \in dirichlet_unit) then f n else (dirichlet_inv_subdef f [::] n)`_0.

Lemma dirichlet_mulVx :
  {in dirichlet_unit, left_inverse 1 dirichlet_inv (@GRing.mul dirichlet)}.
Proof.
move=> f funit.
have subproof n k : k <= n ->
    (dirichlet_inv_subdef f [::] n)`_(n - k) = (dirichlet_inv_subdef f [::] k)`_0.
  elim: n k => [|n IHn] k; first by rewrite leqn0 sub0n => /eqP ->.
  rewrite [in LHS]/dirichlet_inv_subdef.
  case: n IHn => [_|n IHn].
    by rewrite leq_eqVlt ltnS leqn0 => /orP[] /eqP ->.
  rewrite leq_eqVlt => /orP[/eqP ->|].
    by rewrite subnn/=.
  by rewrite ltnS => kn; rewrite subSn//= IHn.
have dvdnF d n k : n.+1 < k -> (k * d)%N == n.+1 = false.
  move=> nk; rewrite mulnC; apply/negP => /eqP /esym nE.
  suff /dvdn_leq-/(_ erefl)/(leq_trans nk): (k %| n.+1) by rewrite ltnn.
  by apply/dvdnP; exists d.
apply: funext => -[|n].
  rewrite [LHS]big_nat_recr//= !big_nat_recr//= big_geq//=.
  rewrite big_geq//=.
  under eq_bigl do rewrite mul1n.
  rewrite big_nat1_eq/= !add0r /dirichlet_inv/= funit/=.
  move: funit => /andP[] f1 f01.
  rewrite -mulrDr invrM// mulrCA mulrC !mulrA divrr// mul1r.
  by rewrite mulrC mulrN addNr.
rewrite /dirichlet_inv.
under [X in X * _]funext do rewrite funit.
move: funit => /andP[] f1 f01.
rewrite [LHS]big_nat_recr//= addrC.
under eq_bigl do rewrite dvdnF//.
rewrite big_pred0// add0r.
rewrite big_nat_recr//= addrC.
under eq_bigl do rewrite mulnC -eqn_div// divnn/=.
rewrite big_nat1_eq/= [X in X * _]/nth/=.
case: n => [|n] /=.
  rewrite mulVr// big_nat1.
  by rewrite big_pred0// addr0.
rewrite -mulrA mulVr// mulr1.
under [X in - X]eq_bigr => d _.
  set G := bigop _ _ _.
  have -> : G = if d <= n.+1 then G else 0.
    case: (leqP d n.+1) => //; rewrite ltnNge => /negPf dn.
    rewrite /G.
    under eq_bigr do rewrite dn mul0r mul0r.
    by rewrite big1.
  rewrite -ltnS /G.
  over.
rewrite -big_mkcond/= -(big_nat_widen _ _ _ xpredT); last first.
  by rewrite !ltnS -addn2 leq_addr.
rewrite big_nat.
under eq_bigr => d/= dn.
  under eq_bigr => d0 _.
    rewrite ltnS in dn.
    rewrite dn mul1r [X in X * _]subproof//.
    over.
  over.
rewrite -big_nat -sumrN -big_split/=.
under eq_bigr => d _.
  rewrite -sumrN -big_split/=.
  under eq_bigr do rewrite addNr.
  rewrite big1//.
  over.
rewrite big1//.
Qed.

Lemma dirichlet_unitPl (f g : dirichlet) : g * f = 1 -> dirichlet_unit f.
Proof.
rewrite funeqE => gf.
have: (f 1 \in GRing.unit) /\ (g 1 \in GRing.unit).
  move: (gf 1).
  rewrite [LHS]big_nat_recr//= !big_nat_recr//= big_geq//=.
  under eq_bigl do rewrite mul0n.
  rewrite big_pred0//.
  under eq_bigl do rewrite mul1n.
  rewrite big_nat1_eq/=.
  under eq_bigl => d.
    have -> : (2 * d)%N == 1 = false.
      apply/negP => /eqP /esym d2.
      suff: (2 %| 1)%N by [].
      by apply/dvdnP; exists d; rewrite mulnC.
    over.
  rewrite big1// !add0r addr0 => gf1.
  split; apply/unitrPr; last by exists (f 1).
  by exists (g 1); rewrite mulrC.
move=> [] f1 g1; apply/andP; split=> //.
(* TODO: This is where we need to change the definition of `unit` to generalise
   to rings with decidable divisibility *)
rewrite unitfE; apply/eqP => f01.
move: (gf 0).
rewrite [LHS]big_nat_recr//= big_nat1.
under [X in _ + X]eq_bigl do rewrite mul1n.
rewrite big_nat1_eq/= big_nat_recr//= big_nat1.
rewrite -mulrDr f01 mulr0 add0r => /eqP.
rewrite mulf_eq0.
move: g1; rewrite unitfE => /negPf -> /= /eqP f0.
move: f01; rewrite f0 add0r => f10.
by move: f1; rewrite f10 unitfE eqxx.
Qed.

Lemma dirichlet_invr_out : {in [predC dirichlet_unit], dirichlet_inv =1 id}.
Proof.
move=> f; rewrite inE => /negPf f1.
rewrite /dirichlet_inv.
by under [LHS]funext do rewrite f1.
Qed.

HB.instance Definition _ := GRing.ComNzRing_hasMulInverse.Build dirichlet 
  dirichlet_mulVx dirichlet_unitPl dirichlet_invr_out.

Lemma primes_coprime n m : 0 < n -> 0 < m -> coprime n m ->
  perm_eq (primes n ++ primes m) (primes (n * m)).
Proof.
move=> n0 m0 nm; apply: uniq_perm.
- rewrite cat_uniq !primes_uniq andbT/= -all_predC.
  apply/allP => k/=; rewrite !mem_primes => /andP[] kp /andP[] _ km.
  apply/negP => /andP[] _ /andP[] _ kn.
  move: (prime_gt1 kp); apply/negP; rewrite -leqNgt; apply/dvdn_leq => //.
  by rewrite -(eqP nm) dvdn_gcd kn.
- exact: primes_uniq.
move=> k; rewrite mem_cat !mem_primes.
case/boolP: (prime k) => kp//=.
by rewrite muln_gt0 n0 m0/= Euclid_dvdM.
Qed.

Lemma unit_mobius : mobius R \in GRing.unit.
Proof.
apply/andP/andP; rewrite /mobius/= expr0 mul1r mul0r add0r andbb.
exact: unitr1.
Qed.

Lemma multiplicative_mobius : multiplicative (mobius R).
Proof.
move=> n m nm.
rewrite /mobius muln_eq0; case: (posnP n) => n0; first by rewrite !mul0r.
case: (posnP m) => m0/=; first by rewrite !mul0r mulr0.
have nmp := primes_coprime n0 m0 nm.
rewrite -(perm_all _ nmp) all_cat.
rewrite -(all_map (logn^~ (n * m)) (eq_op^~ 1%N)).
rewrite (_ : map (logn^~ (n * m)) (primes n) = map (logn^~ n) (primes n)); last first.
  apply/eqP; rewrite eq_map_all all_map; apply/allP => k.
  rewrite mem_primes n0/= => /andP[] kp kn. 
  rewrite lognM// addnC logn_coprime//.
  exact: (coprime_dvdl kn).
rewrite all_map.
case: (all _ _) => //=; last by rewrite !mul0r.
rewrite -(all_map (logn^~ (n * m)) (eq_op^~ 1%N)).
rewrite (_ : map (logn^~ (n * m)) (primes m) = map (logn^~ m) (primes m)); last first.
  apply/eqP; rewrite eq_map_all all_map; apply/allP => k.
  rewrite mem_primes m0/= => /andP[] kp km. 
  rewrite lognM// logn_coprime// coprime_sym.
  exact: (coprime_dvdr km).
rewrite all_map.
case: (all _ _) => //=; last by rewrite !mul0r mulr0.
by rewrite !mul1r -(perm_size nmp) size_cat exprD.
Qed.

Lemma mobiusV : (mobius R)^-1 = (fun n => (n != 0)%:R).
Proof.
apply/esym/(mulrI unit_mobius); rewrite divrr; last exact: unit_mobius.
apply: eq_multiplicative.
- apply: dirichlet_mul_multiplicative => n m/=.
    exact: multiplicative_mobius.
  by rewrite muln_eq0 negb_or -mulnb natrM.
- by move=> n m _; rewrite [X in (_ X)%:R = _]muln_eq1 -mulnb natrM.
- rewrite [LHS]big_nat_recl//=.
  under eq_bigr do rewrite /mobius !mul0r.
  rewrite big1// add0r big_nat1.
  under eq_bigl do rewrite mul1n.
  by rewrite big_nat1_eq/= mulr0.
move=> p k pp.
have p0 i: 0 < p ^ i by rewrite expn_gt0 prime_gt0.
rewrite dirichlet_mulE_dvdn//.
rewrite big_mkcond big_nat_recl/= ?p0// dvd1n divn1 -lt0n p0 mulr1.
rewrite -big_mkcond big_nat_cond/=.
under eq_bigr => d /andP[] /andP[] d0 _ dpk.
  rewrite -lt0n divn_gt0// (dvdn_leq (p0 k) dpk) mulr1.
  rewrite /mobius andTb.
  move: dpk d0; rewrite -ltnS => /dvdn_pfactor-/(_ pp)[] i ik dE.
  rewrite dE -[X in X.+1](expn0 p) ltn_exp2l ?prime_gt1// => i0.
  rewrite primesX// primes_prime//= pfactorK// andbT.
  rewrite -(inj_eq (expnI (prime_gt1 pp))) expn1 -dE.
  rewrite -[X in _ == X]prednK; last exact: prime_gt0.
  rewrite eqSS mulrb !fun_if if_arg mul1r mul0r expr1.
  over.
rewrite -big_nat_cond -big_mkcondl big_mkcondr big_nat1_eq.
rewrite ltn_predRL prime_gt1//= prednK ?prime_gt0//.
rewrite /mobius/= mul1r expr0.
case: k => [|k]; first by rewrite expn0 leqNgt prime_gt1//= addr0.
have pk: p %| p ^ k.+1 by apply/dvdn_exp.
rewrite pk (dvdn_leq _ pk) ?p0// subrr -[X in _ = (_ == X)%:R](expn0 p).
by rewrite (inj_eq (expnI (prime_gt1 pp))).
Qed.

End DirichletUnit.
