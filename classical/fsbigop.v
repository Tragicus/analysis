(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality.

(**md**************************************************************************)
(* # Finitely-supported big operators                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*     finite_support idx D F := D `&` F @^-1` [set~ idx]                     *)
(* \big[op/idx]_(i \in A) F i == iterated application of the operator op      *)
(*                               with neutral idx over finite_support idx A F *)
(*         \sum_(i \in A) F i == iterated addition, in ring_scope             *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "\big [ op / idx ]_ ( i '\in' A ) F"
  (F at level 36, A at level 60,
           format "'[' \big [ op / idx ]_ ( i  '\in'  A ) '/  '  F ']'").

Reserved Notation "\sum_ ( i '\in' A ) F"
  (F at level 41, A at level 60,
    format "'[' \sum_ ( i  '\in'  A ) '/  '  F ']'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Notation "\big [ op / idx ]_ ( i '\in' A ) F" :=
  (\big[op/idx]_(i <- fset_set (((fun i : A => F) @^-1` [set~ idx]))) F)
    (only parsing) : big_scope.

Lemma finite_index_key : unit. Proof. exact: tt. Qed.
Definition finite_support {I : choiceType} {T : eqType} (idx : T)
    (F : I -> T) : seq I :=
  locked_with finite_index_key (fset_set (F @^-1` [set~ idx] : set I)).
Notation "\big [ op / idx ]_ ( i '\in' D ) F" :=
    (\big[op/idx]_(i <- finite_support idx (fun i : D => F)) F)
  : big_scope.

Lemma in_finite_support (T : eqType) (J : choiceType) (i : T)
    (F : J -> T) : finite (F @^-1` [set~ i]) ->
  finite_support i F =i F @^-1` [set~ i].
Proof. by move=> finF j; rewrite /finite_support unlock in_fset_set. Qed.

Lemma finite_support_uniq (T : eqType) (J : choiceType) (i : T)
    (F : J -> T) : uniq (finite_support i F).
Proof. by rewrite /finite_support unlock; exact: fset_uniq. Qed.
#[global] Hint Resolve finite_support_uniq : core.

Lemma no_finite_support (T : eqType) (J : choiceType) (i : T)
    (F : J -> T) : infinite (F @^-1` [set~ i]) ->
  finite_support i F = [::].
Proof.
move=> infinF; rewrite /finite_support unlock.
by rewrite /fset_set/=; case: pselect => //.
Qed.

Lemma eq_finite_support {I : choiceType} {T : eqType} (idx : T)
    (F G : I -> T) : F =1 G ->
  finite_support idx F = finite_support idx G.
Proof.
by move=> eqFG; rewrite /finite_support !unlock// (eq_preimage _ eqFG).
Qed.

Variant finite_support_spec (R : eqType) (T : choiceType)
  (F : T -> R) (idx : R) : seq T -> Type :=
| NoFiniteSupport of infinite (F @^-1` [set~ idx]) :
    finite_support_spec F idx [::]
| FiniteSupport (X : {fset T})
   & [set` X] = (F @^-1` [set~ idx]) :
    finite_support_spec F idx X.

Lemma finite_supportP (R : eqType) (T : choiceType) (F : T -> R) (idx : R) :
  finite_support_spec F idx (finite_support idx F).
Proof.
rewrite /finite_support unlock/= /fset_set.
case: pselect=> // Xfin; last by constructor.
case: cid => //= X eqX; constructor; rewrite -?eqX ?range_val//.
Qed.

Notation "\sum_ ( i '\in' A ) F" := (\big[+%R/0%R]_(i \in A) F) : ring_scope.

Lemma eq_fsbigr (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (T : choiceType) (f g : T -> R) :
  f =1 g -> (\big[op/idx]_(x \in T) f x = \big[op/idx]_(x \in T) g x).
Proof.
move=> fg; rewrite (eq_finite_support _ fg); apply: eq_big_seq => x.
by case: finite_supportP => //= X /subsetP XP _ gidx xX; rewrite [LHS]fg //; apply/XP.
Qed.
Arguments eq_fsbigr {R idx op T f} g.

Lemma fsbigTE (R : eqType) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (A : {fset T}) (f : T -> R) :
    (forall i, i \notin A -> f i = idx) ->
  \big[op/idx]_(i \in T) f i = \big[op/idx]_(i <- A) f i.
Proof.
move=> Af; have Afin : finite (f @^-1` [set~ idx]).
  apply/(card_le_finite _ (finite_subfset A))/subset_card_le/subsetP => x /negP.
  by apply: contra_notT => /Af/eqP.
rewrite [in RHS](big_fsetID _ [pred x | f x == idx])/=.
rewrite [X in _ = op X _]big_fset [X in _ = op X _]big1 ?Monoid.simpm//; last first.
  by move=> i /= /eqP.
apply eq_fbigl => r.
rewrite in_finite_support// ?setTI// /preimage/=; apply/idP/idP => /=.
  move=> /eqP; rewrite !inE/=; apply: contra_notP => /negP.
  by rewrite negb_and negbK => /orP[|/eqP//]; exact: Af.
by rewrite !inE/= => /andP[_].
Qed.
Arguments fsbigTE {R idx op T} A f.

Lemma fsbig_mkcond (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (T : choiceType) (A : set T) (f : T -> R) :
  \big[op/idx]_(i \in A) f (val i) =
  \big[op/idx]_(i \in T) if i \in A then f i else idx.
Proof.
rewrite -big_mkcond/= -[in RHS]big_filter -(big_map _ xpredT); apply: perm_big.
apply: uniq_perm.
- rewrite map_inj_uniq; last exact: val_inj.
  exact: finite_support_uniq.
- exact: filter_uniq.
move=> i; rewrite mem_filter.
set g := fun i => if i \in A then f i else idx.
have gAf : g @^-1` [set~ idx] = (A `&` f @^-1` [set~ idx]).
  apply/eqP/seteqP => x; apply/idP/andP => [/eqP|[] xA /eqP]; rewrite /g/=.
    by case: ifPn => // _ /eqP.
  by rewrite in_mkset xA => /eqP.
have valA: (val : A -> T) @^-1` (f @^-1` [set~ idx]) = (val : A -> T) @^-1` (A `&` f @^-1` [set~ idx]).
  rewrite preimage_setI -[X in _ @^-1` X `&` _]range_val preimage_range.
  exact/esym/setTI.
case: finite_supportP => [Ay|].
  rewrite no_finite_support ?andbF// gAf.
  apply: contra_not Ay; rewrite (comp_preimage _ val) valA.
  exact/finite_preimage/val_inj.
move=> X; rewrite comp_preimage valA => XE.
case: finite_supportP; rewrite gAf.
  move=> /(_ (@finite_preimage_surj _ _ _ (val : A -> T) _ _))/wrap[]//.
    by rewrite range_val//.
  by rewrite -XE; apply: finite_subfset.
move=> Y /eqP/seteqP/= YX; rewrite YX andbA andbb.
move: XE => /eqP/seteqP XE.
apply/mapP/andP => [[] j + ->|[]iA i0]/=.
  by rewrite XE => /andP[].
by exists i => //; rewrite XE; apply/andP.
Qed.

Lemma fsbig_mkcondr (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (T : choiceType) (I J : set T) (a : T -> R) :
  \big[op/idx]_(i \in I `&` J) a (val i) =
  \big[op/idx]_(i \in I) if val i \in J then a (val i) else idx.
Proof.
rewrite fsbig_mkcond.
rewrite [RHS](fsbig_mkcond _ _ (fun i => if i \in J then a i else idx)).
by under eq_fsbigr do rewrite if_and.
Qed.

Lemma fsbig_mkcondl (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (T : choiceType) (I J : set T) (a : T -> R) :
  \big[op/idx]_(i \in I `&` J) a (val i) =
  \big[op/idx]_(i \in J) if val i \in I then a (val i) else idx.
Proof. by rewrite setIC fsbig_mkcondr. Qed.

Lemma fsbigT (R : eqType) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (f : T -> R) :
  \big[op/idx]_(i \in [set: T]) f (val i) = \big[op/idx]_(i \in T) f i.
Proof. exact: fsbig_mkcond. Qed.

Lemma bigfs (R : eqType) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (r : seq T) (P : {pred T}) (f : T -> R) : uniq r ->
    (forall i, P i -> i \notin r -> f i = idx) ->
  \big[op/idx]_(i <- r | P i) f i = \big[op/idx]_(i \in [set` P]) f (val i).
Proof.
move=> r_uniq fidx; rewrite fsbig_mkcond.
rewrite [RHS](fsbigTE [fset x | x in r]%fset); last first.
  move=> i; rewrite !in_mkset/=; case: ifP => // Pi ri.
  apply: fidx; apply: contraNN ri => ri.
  by apply/imfsetP; exists i.
rewrite -big_mkcond; under [RHS]eq_bigl do rewrite mem_setE.
by apply: perm_big; rewrite [perm_eq _ _]uniq_perm// => i; rewrite !inE.
Qed.

Lemma fsbigE (R : eqType) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (A : set T) (r : seq T) (f : T -> R) :
    uniq r ->
    [set` r] `<=` A ->
    (forall i : A, val i \notin r -> f i = idx) ->
  \big[op/idx]_(i \in A) f (val i) = \big[op/idx]_(i <- r | i \in A) f i.
Proof.
move=> r_uniq rQ fidx; rewrite [RHS]bigfs ?set_mem_set//= => i iA.
exact: fidx.
Qed.
Arguments fsbigE {R idx op T A}.

Lemma fsbig_seq (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (r : seq I) (F : I -> R) :
  uniq r ->
  \big[op/idx]_(a <- r) F a = \big[op/idx]_(a \in [set` r]) F (val a).
Proof.
move=> ur; rewrite [RHS](fsbigE r)//=; last by move=> []/= + ->.
by rewrite mem_setE big_seq_cond big_mkcondr.
Qed.

Lemma fsbig1 (R : eqType) (idx : R) (op : Monoid.law idx) (I : choiceType)
    (F : I -> R) :
  (forall i, F i = idx) -> \big[op/idx]_(i \in I) F i = idx.
Proof. by move=> PF0; rewrite [LHS]big1_seq/=. Qed.

Lemma fsbig_dflt (R : eqType) (idx : R) (op : Monoid.law idx) (I : choiceType)
    (F : I -> R) :
  infinite (F @^-1` [set~ idx])-> \big[op/idx]_(i \in I) F i = idx.
Proof. by case: finite_supportP; rewrite ?big_nil// => X <- /(_ (finite_subfset _)). Qed.

Lemma fsbig_widen (T : choiceType) [R : eqType] [idx : R]
    (op : Monoid.com_law idx) (P D : set T) (f : T -> R) :
    P `<=` D ->
    D `\` P `<=` f @^-1` [set idx] ->
  \big[op/idx]_(i \in P) f (val i) = \big[op/idx]_(i \in D) f (val i).
Proof.
move=> /subsetP PD /subsetP DPf; rewrite fsbig_mkcond [RHS]fsbig_mkcond.
apply: eq_fsbigr => x; case: ifPn => [/PD ->//|Px].
by case: ifP => // Dx; apply/esym/eqP/DPf/andP; split.
Qed.
Arguments fsbig_widen {T R idx op} P D f.

Lemma fsbig_supp (T : choiceType) [R : eqType] [idx : R]
    (op : Monoid.com_law idx) (f : T -> R) :
  \big[op/idx]_(i \in T) f i = \big[op/idx]_(i \in f @^-1` [set~ idx]) f (val i).
Proof.
rewrite -fsbigT.
apply/esym/fsbig_widen => //; first exact: subsetT.
by rewrite setTD preimage_setC setCK.
Qed.

Lemma fsbig_fwiden (T : choiceType) [R : eqType] [idx : R]
    (op : Monoid.com_law idx)
    (r : seq T) (P : set T) (f : T -> R) :
  P `<=` [set` r] ->
  uniq r ->
  [set i | i \in r] `\` P `<=` f @^-1` [set idx] ->
  \big[op/idx]_(i \in P) f (val i) = \big[op/idx]_(i <- r) f i.
Proof. by move=> *; rewrite [LHS](fsbig_widen _ [set` r])// [RHS]fsbig_seq. Qed.
Arguments fsbig_fwiden {T R idx op} r P f.

Lemma fsbig_set0 (R : eqType) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
  (F : T -> R) : \big[op/idx]_(x \in set0) F (val x) = idx.
Proof. by rewrite [LHS](fsbigE [::])// ?big_nil//; case. Qed.

Lemma fsbig_set1 (R : eqType) (idx : R) (op : Monoid.com_law idx) (T : choiceType) x
  (F : T -> R) : \big[op/idx]_(y \in [set x]) F (val y) = F x.
Proof.
rewrite [LHS](fsbigE [:: x])//= ?big_cons ?big_nil ?ifT ?inE ?Monoid.simpm//.
  by apply/subsetP => y /=; rewrite !in_mkset orbF.
by move=> []/= i /eqP ->; rewrite inE eqxx.
Qed.

Lemma __deprecated__full_fsbigID (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (A : set I) (F : I -> R) :
  finite (A `&` F @^-1` [set~ idx]) ->
  \big[op/idx]_(i \in A) F i = op (\big[op/idx]_(i \in A `&` B) F i)
                                  (\big[op/idx]_(i \in A `&` ~` B) F i).
Proof.
move=> finF.
have fsbig_setI C : \big[op/idx]_(i <-
      [fset x | x in fset_set (A `&` F @^-1` [set~ idx]) & x \in C]%fset) F i =
    \big[op/idx]_(i \in A `&` C) F i.
  apply: eq_fbigl => i /=; apply/idP/idP.
    rewrite 2!inE/= => /andP[+ Bi]; rewrite in_fset_set// => /andP[Ai Fi].
    by rewrite unlock in_fset_set setIAC//; apply/(sub_finite _ finF)/subIsetl.
  rewrite unlock in_fset_set setIAC; last exact/(sub_finite _ finF)/subIsetl.
  by move=> /andP[] iA iC; rewrite !inE/= in_fset_set//; apply/andP.
rewrite (big_fsetID _ [pred i | i \in B])/= [locked_with _ _]unlock.
rewrite fsbig_setI; congr (op _ _); rewrite -fsbig_setI.
by apply eq_fbigl => i; rewrite !inE.
Qed.
Arguments __deprecated__full_fsbigID {R idx op I} B.

Lemma fsbigID (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (B : set I) (A : set I) (F : I -> R) :
    finite A ->
  \big[op/idx]_(i \in A) F i = op (\big[op/idx]_(i \in A `&` B) F i)
                                  (\big[op/idx]_(i \in A `&` ~` B) F i).
Proof. by move=> Afin; apply/__deprecated__full_fsbigID/(sub_finite _ Afin)/subIsetl. Qed.
Arguments fsbigID {R idx op I} B.

#[deprecated(note="Use fsbigID instead")]
Notation full_fsbigID := __deprecated__full_fsbigID (only parsing).

Lemma fsbigU (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (A B : set I) (F : I -> R) :
    finite A -> finite B -> A `&` B `<=` F @^-1` [set idx] ->
  \big[op/idx]_(i \in A `|` B) F i =
     op (\big[op/idx]_(i \in A) F i) (\big[op/idx]_(i \in B) F i).
Proof.
move=> Afin Bfin AB0; rewrite (fsbigID A) ?finiteU; last by split.
rewrite setUK -setDE; congr (op _ _); rewrite setDE setIUl setICr set0U.
by apply: fsbig_widen => //; rewrite -setDE setDD setIC.
Qed.
Arguments fsbigU {R idx op I} [A B F].

Lemma fsbigU0 (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (A B : set I) (F : I -> R) :
    finite A -> finite B -> A `&` B `<=` set0 ->
  \big[op/idx]_(i \in A `|` B) F i =
     op (\big[op/idx]_(i \in A) F i) (\big[op/idx]_(i \in B) F i).
Proof. move=> Af Bf AB0; rewrite [LHS]fsbigU//; apply/(subset_trans AB0)/sub0set. Qed.

Lemma fsbigD1 (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (I : choiceType) (i : I) (A : set I) (F : I -> R) :
     finite A -> i \in A ->
  \big[op/idx]_(j \in A) F j = op (F i) (\big[op/idx]_(j \in A `\ i) F j).
Proof. by move=> *; rewrite (fsbigID [set i])// setI1 [if _ then _ else _]ifT// fsbig_set1. Qed.
Arguments fsbigD1 {R idx op I} i A F.

Lemma full_fsbig_distrr (R : eqType) (zero : R) (times : Monoid.mul_law zero)
    (plus : Monoid.add_law zero times) (I : choiceType) (a : R) (P : set I)
    (F : I -> R) :
  finite (P `&` F @^-1` [set~ zero]) (*NB: not needed in the integral case*)->
  times a (\big[plus/zero]_(i \in P) F i) =
  \big[plus/zero]_(i \in P) times a (F i).
Proof.
move=> finF.
have [->|a0] := eqVneq a zero.
  by rewrite Monoid.mul0m [bigop _ _ _]fsbig1//; move=> i; rewrite Monoid.mul0m.
rewrite big_distrr [RHS](full_fsbigID (F @^-1` [set zero])); last first.
  apply/(sub_finite _ finF)/subsetP => x /= /andP[Px aFN0].
  by apply/andP; split=> //; apply: contraNN aFN0 => /eqP ->; rewrite Monoid.simpm.
set b0 := bigop _ _ _.
set b1 := bigop _ _ _.
set b2 := bigop _ _ _.
rewrite (_ : b1 = zero) ?Monoid.simpm; last first.
  by rewrite [b1]fsbig1// => -[]/= i /andP[_ /eqP ->]; rewrite Monoid.simpm.
apply/esym/fsbig_fwiden => //.
  by apply/subsetP => x; rewrite in_finite_support.
apply/subsetP => i; rewrite in_mkset in_finite_support// in_setC !in_setI.
by move=> /andP[]/andP[] ->/=; rewrite negbK => /negP.
Qed.

Lemma fsbig_distrr (R : eqType) (zero : R) (times : Monoid.mul_law zero)
    (plus : Monoid.add_law zero times) (I : choiceType) (a : R) (P : set I)
    (F : I -> R) :
  finite P (*NB: not needed in the integral case*) ->
  times a (\big[plus/zero]_(i \in P) F i) =
  \big[plus/zero]_(i \in P) times a (F i).
Proof.
by move=> Pf; apply: full_fsbig_distrr; apply/(sub_finite _ Pf)/subIsetl.
Qed.

Lemma mulr_fsumr (R : idomainType) (I : choiceType) a (P : set I) (F : I -> R) :
   a * (\sum_(i \in P) F i) = \sum_(i \in P) a * F i.
Proof.
have [->|aN0] := eqVneq a 0; first by rewrite mul0r [bigop _ _ _]big1// => i; rewrite mul0r.
case: (pselect (finite (P `&` F @^-1` [set~ 0]))) => PFfin.
  exact: full_fsbig_distrr.
rewrite !fsbig_dflt ?mulr0//; apply/(contra_not _ PFfin)/sub_finite/setIS.
by apply/subsetP => x x0; rewrite !in_mkset [~~ _]mulf_neq0.
Qed.

Lemma mulr_fsuml (R : idomainType) (I : choiceType) a (P : set I) (F : I -> R) :
   (\sum_(i \in P) F i) * a = \sum_(i \in P) (F i * a).
Proof. by rewrite mulrC mulr_fsumr; under eq_fsbigr do rewrite mulrC. Qed.

Lemma fsbig_ord (R : eqType) (idx : R) (op : Monoid.com_law idx) n (F : nat -> R) :
  \big[op/idx]_(a < n) F a = \big[op/idx]_(a \in `I_n) F a.
Proof.
rewrite -(big_mkord xpredT) [LHS]fsbig_seq ?iota_uniq//.
by apply: eq_fsbigl; rewrite -Iiota /index_iota subn0.
Qed.

Lemma fsbig_finite (R : eqType) (idx : R) (op : Monoid.com_law idx) (T : choiceType)
    (D : set T) (F : T -> R) : finite D ->
  \big[op/idx]_(x \in D) F x = \big[op/idx]_(x <- fset_set D) F x.
Proof.
by move=> Dfin; apply: fsbig_fwiden; rewrite ?fset_setK// setDv sub0set.
Qed.

Section fsbig2.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx).

(* Lemma reindex_inside I F P ...  : finite_set (P `&` F @` [set~ id]) -> ... *)
(* Isn't this reversed compared to reindex in bigop? *)
Lemma reindex_fsbig {I J : choiceType} (h : I -> J) P Q
    (F : J -> R) : set_bij P Q h ->
  \big[op/idx]_(j \in Q) F j = \big[op/idx]_(i \in P) F (h i).
Proof.
elim/choicePpointed: I => I in h P *.
  rewrite !emptyE => /Pbij[{}h ->].
  by rewrite -[in LHS](image_eq h) image_set0 !fsbig_set0.
elim/choicePpointed: J => J in F h Q *; first by have := no (h point).
move=> /(@pPbij _ _ _)[{}h ->].
pose A := P `&` (F \o h) @^-1` [set~ idx].
pose B := Q `&` F @^-1` [set~ idx].
have /(@pPbij _ _ _)[g gh] : set_bij A B h.
  apply: splitbij_sub; rewrite /A /B /preimage //=.
    by move=> x [Px Fhx]; split=> //; apply: funS.
  by move=> x [Qx Fx]; split; rewrite ?invK ?inE//; apply: funS.
case: finite_supportP; rewrite ?big_nil//=.
  case: finite_supportP; rewrite ?big_nil//=.
  move=> X XP _ XE []; rewrite -/B -(image_eq g) /A.
  by apply: finite_image; rewrite -XE.
move=> Y YQ Fidx YE; case: finite_supportP.
  move=> []; rewrite -/A -(image_eq [bij of g^-1%FUN]).
  by apply: finite_image; rewrite /B -YE.
move=> X XP Fhidx XE; suff -> : Y = (h @` X)%fset.
  by rewrite big_imfset// => ? ? ? ? /inj; apply; rewrite inE; apply: XP.
have BY j : (B j) = (j \in Y) by rewrite -[RHS]/([set` Y] j) YE.
have AX i : (A i) = (i \in X) by rewrite -[RHS]/([set` X] i) XE.
rewrite gh; apply/fsetP=> j; apply/idP/imfsetP => [Yj | [i iX ->]]; last first.
  by rewrite -BY; apply: funS; rewrite AX.
by exists (g^-1%FUN j); rewrite ?invK ?inE ?BY// -AX; apply: funS; rewrite BY.
Qed.

Lemma fsbig_image {I J : choiceType} P (h : I -> J) (F : J -> R) : set_inj P h ->
  \big[op/idx]_(j \in h @` P) F j = \big[op/idx]_(i \in P) F (h i).
Proof. by move=> /inj_bij; apply: reindex_fsbig. Qed.

(* Lemma reindex_inside I F P ...  : finite_set (P `&` F @` [set~ id]) -> ... *)
Lemma __deprecated__reindex_inside {I J : choiceType} P Q (h : I -> J) (F : J -> R) :
  bijective h -> P `<=` h @` Q -> Q `<=` h @^-1` P ->
  \big[op/idx]_(j \in P) F j = \big[op/idx]_(i \in Q) F (h i).
Proof.
move=> hbij PQ QP; apply: reindex_fsbig; split=> //.
by move=> x y _ _ /(bij_inj hbij).
Qed.

Lemma reindex_fsbigT {I J : choiceType} (h : I -> J) (F : J -> R) :
  bijective h ->
  \big[op/idx]_(j \in [set: J]) F j = \big[op/idx]_(i \in [set: I]) F (h i).
Proof. by rewrite -setTT_bijective => -[? ? ?]; apply: reindex_fsbig. Qed.

End fsbig2.
Arguments reindex_fsbig {R idx op I J} _ _ _.
Arguments fsbig_image {R idx op I J} _ _.
Arguments __deprecated__reindex_inside {R idx op I J} _ _.
Arguments reindex_fsbigT {R idx op I J} _ _.
#[deprecated(note="use reindex_fsbig, fsbig_image or reindex_fsbigT instead")]
Notation reindex_inside := __deprecated__reindex_inside (only parsing).
#[deprecated(note="use reindex_fsbigT instead")]
Notation reindex_inside_setT := reindex_fsbigT (only parsing).

Lemma fsbigN1 (R : eqType) (idx : R) (op : Monoid.com_law idx)
    (T1 T2 : choiceType) (Q : set T2) (f : T1 -> T2 -> R) (x : T1) :
  \big[op/idx]_(y \in Q) f x y != idx -> exists2 y, Q y & f x y != idx.
Proof.
apply: contra_neqP => /forall2NP Qf; apply/fsbig1 => y Qy.
by case: (Qf y) => // /negP/negPn/eqP->.
Qed.

Lemma fsbig_split (T : choiceType) (R : eqType) (idx : R)
    (op : Monoid.com_law idx) (P : set T) (f g : T -> R) : finite_set P ->
  \big[op/idx]_(x \in P) op (f x) (g x) =
  op (\big[op/idx]_(x \in P) f x) (\big[op/idx]_(x \in P) g x).
Proof. by move=> Pfin; rewrite !fsbig_finite// big_split. Qed.

Lemma fsumr_ge0 (R : numDomainType) (I : choiceType) (P : set I) (F : I -> R) :
  (forall i, P i -> 0 <= F i) -> 0 <= \sum_(i \in P) F i.
Proof.
move=> PF; case: finite_supportP; rewrite ?big_nil// => X XP F0 _.
by rewrite big_seq_cond big_mkcondr sumr_ge0// => i /XP/PF.
Qed.

Lemma fsumr_le0 (R : numDomainType) (I : choiceType) (P : set I) (F : I -> R) :
  (forall i, P i -> F i <= 0) -> \sum_(i \in P) F i <= 0.
Proof.
move=> PF; case: finite_supportP; rewrite ?big_nil// => X XP F0 _.
by rewrite big_seq_cond big_mkcondr sumr_le0// => i /XP/PF.
Qed.

Lemma fsumr_gt0 (R : realDomainType) (I : choiceType) (r : seq I) (P : set I)
    (F : I -> R) :
  0 < \sum_(i \in P) F i -> exists2 i, P i & 0 < F i.
Proof.
apply: contraPP => /forall2NP xNPF; rewrite le_gtF// fsumr_le0// => i Pi.
by case: (xNPF i) => // /negP; case: ltP.
Qed.

Lemma fsumr_lt0 (R : realDomainType) (I : choiceType) (P : set I)
    (F : I -> R) :
  \sum_(i \in P) F i < 0 -> exists2 i, P i & F i < 0.
Proof.
apply: contraPP => /forall2NP xNPF; rewrite le_gtF// fsumr_ge0// => i Pi.
by case: (xNPF i) => // /negP; case: ltP.
Qed.

Lemma pfsumr_eq0 (R : realDomainType) (I : choiceType) (P : set I)
    (F : I -> R) :
  finite_set P ->
  (forall i, P i -> 0 <= F i) ->
  \sum_(i \in P) F i = 0 -> forall i, P i -> F i = 0.
Proof.
move=> Pfin F0 /eqP; apply: contraTP => /existsPNP[i Pi /eqP Fi0].
rewrite (fsbigD1 i)//= paddr_eq0 ?F0 ?negb_and ?Fi0//.
by rewrite fsumr_ge0// => j [/F0->].
Qed.

Lemma fsbig_setU {T} {I : choiceType} (A : set I) (F : I -> set T) :
  finite_set A ->
  \big[setU/set0]_(i \in A) F i = \bigcup_(i in A) F i.
Proof. by move=> Afin; rewrite fsbig_finite// bigsetU_fset_set. Qed.

Lemma fsbig_setU_set1 {T : choiceType} (A : set T) :
  finite_set A -> \big[setU/set0]_(x \in A) [set x] = A.
Proof.
move=> fA; rewrite fsbig_setU//.
by apply/seteqP; split=> [t [x Ax ->]//|t At]; exists t.
Qed.

Lemma pair_fsbig (R : Type) (idx : R) (op : Monoid.com_law idx)
    (I J : choiceType) (P : set I) (Q : set J) (F : I -> J -> R) :
  finite_set P -> finite_set Q ->
  \big[op/idx]_(i \in P) \big[op/idx]_(j \in Q) F i j
  = \big[op/idx]_(p \in P `*` Q) F p.1 p.2.
Proof.
move=> Pfin Qfin; have PQfin : finite_set (P `*` Q) by exact: finite_setX.
rewrite !fsbig_finite//=; under eq_bigr do rewrite fsbig_finite//=.
rewrite pair_big_dep_cond/= fset_setX//.
apply: eq_fbigl => -[i j] //=; apply/imfset2P/idP; rewrite inE //=.
  by move=> [x + [y + [-> ->]]]; rewrite 4!inE/= !andbT/= => -> ->.
move=> /andP[Pi Qi]; exists i; rewrite 2?inE ?andbT//.
by exists j; rewrite 2?inE ?andbT.
Qed.

Lemma exchange_fsbig (R : Type) (idx : R) (op : Monoid.com_law idx)
    (I J : choiceType) (P : set I) (Q : set J) (F : I -> J -> R) :
  finite_set P -> finite_set Q ->
  \big[op/idx]_(i \in P) \big[op/idx]_(j \in Q) F i j
  = \big[op/idx]_(j \in Q) \big[op/idx]_(i \in P) F i j.
Proof.
move=> Pfin Qfin; rewrite 2?pair_fsbig//; pose swap (x : I * J) := (x.2, x.1).
apply/esym/(reindex_fsbig swap).
split=> [? [? ?]//|[? ?] [? ?] /set_mem[? ?] /set_mem[? ?] [-> ->]//|].
by move=> [i j] [? ?]; exists (j, i).
Qed.
