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
  forall n m, coprime n m -> f (n * m) = f n * f m.

Lemma dirichlet_mul_multiplicative (f g : dirichlet) :
  multiplicative f -> multiplicative g -> multiplicative (f * g).
Proof.
move=> fm gm [|n] m.
  rewrite /coprime gcd0n => /eqP ->.
  rewrite mul0r.
STOP.
Search gcdn 0%N.
m nm.
rewrite !dirichlet_mulE_dvdn.

End Dirichlet.

HB.instance Definition _ (R : comRingType) := GRing.Zmodule.on (dirichlet R).

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

Lemma dirichletVcst1E n : ((fun n => (n != 0)%:R) : dirichlet)^-1 n =
  match primes n with
  | [::] => (n == 1)%:R
  | [:: p] => (-1) ^+ (logn p n)
  | _ => 0
  end.
Proof.
have f1: ((fun n0 : nat => (n0 != 0)%:R) : dirichlet.dirichlet R) \in GRing.unit.
  apply/andP/andP; rewrite eqxx add0r andbb oner_neq0.
  exact: unitr1.
move: n; rewrite -/(_ =1 _) -funeqE.
apply/esym/(mulrI f1); rewrite divrr//.
apply: funext => n.
rewrite [LHS]big_nat_recl//.
under eq_bigr do rewrite mul0r.
rewrite big1// add0r.
under eq_bigr do under eq_bigr do rewrite mul1r.
case: n => [|n].
  rewrite big_nat1.
  under eq_bigl do rewrite mul1n.
  by rewrite big_nat1_eq.

rewrite /injective.
Set Printing All.
apply.
Search GRing.inv GRing.mul.
case pn: (primes n).
  move: pn => /eqP; rewrite primes_eq0.
  rewrite ltnS leq_eqVlt ltnS leqn0 => /orP[] /eqP ->.
Search primes nil.

End DirichletUnit.
