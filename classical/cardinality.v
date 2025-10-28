(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap ssralg ssrnum ssrint rat.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.

(**md**************************************************************************)
(* # Cardinality                                                              *)
(*                                                                            *)
(* This file provides an account of cardinality properties of classical sets. *)
(* This includes standard results of set theory such as the Pigeon Hole       *)
(* principle, the Cantor-Bernstein Theorem, or lemmas about the cardinal of   *)
(* nat, nat * nat, and rat.                                                   *)
(*                                                                            *)
(* Since universe polymorphism is not yet available in our framework, we      *)
(* develop a relational theory of cardinals: there is no type for cardinals   *)
(* only relations A #<= B and A #= B to compare the cardinals of two sets     *)
(* (on two possibly different types).                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*           A #<= B == the cardinal of A is smaller or equal to the one of B *)
(*           A #>= B := B #<= A                                               *)
(*            A #= B == the cardinal of A is equal to the cardinal of B       *)
(*           A #!= B := ~~ (A #= B)                                           *)
(*      finite A == the set A is finite                                   *)
(*                   := exists n, A #= `I_n                                   *)
(*                   <-> exists X : {fset T}, A = [set` X]                    *)
(*                   <-> ~ ([set: nat] #<= A)                                 *)
(*    infinite A := ~ finite A                                        *)
(*       countable A <-> A is countable                                       *)
(*                   := A #<= [set: nat]                                      *)
(*        fset_set A == the finite set corresponding if A : set T is finite,  *)
(*                      set0 otherwise (T : choiceType)                       *)
(*              A.`1 := [fset x.1 | x in A]                                   *)
(*              A.`2 := [fset x.2 | x in A]                                   *)
(* {fimfun aT >-> T} == type of functions with a finite image                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "A '#<=' B" (at level 79, format "A  '#<='  B").
Reserved Notation "A '#>=' B" (at level 79, format "A  '#>='  B").
Reserved Notation "A '#=' B" (at level 79, format "A  '#='  B").
Reserved Notation "A '#!=' B" (at level 79, format "A  '#!='  B").

Import Order.Theory GRing.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope function_scope.

Declare Scope card_scope.
Delimit Scope card_scope with card.
Local Open Scope card_scope.

Definition card_le T U :=
  `[< $|{inj T >-> U}| >].
Notation "A '#<=' B" := (card_le A B) : card_scope.
Notation "A '#>=' B" := (card_le B A) (only parsing) : card_scope.

Definition card_eq T U :=
  `[< $|{splitbij T >-> U}| >].
Notation "A '#=' B" := (card_eq A B) : card_scope.
Notation "A '#!=' B" := (~~ (card_eq A B)) : card_scope.

Definition finite T := exists n, T #= `I_n.
Notation infinite T := (~ finite T).

Lemma injPex {T U} :
   $|{inj T >-> U}| <-> exists f : T -> U, injective f.
Proof. by split=> [[f]|[_ /Pinj[f _]]]; first by exists f. Qed.

Lemma surjPex {T U} :
  $|{surj T >-> U}| <-> exists f : T -> U, surjective f.
Proof.
split=> [[f]|[_ /Psurj[f _]]]; first by exists f; apply: surj.
by move: (f : {surj _ >-> _}).
Qed.

Lemma bijPex {T U} :
  $|{splitbij T >-> U}| <-> exists f : T -> U, bijective f.
Proof. by split=> [[f]|[_ /Pbij[f _]]]; first by exists f; apply: bij. Qed.

(*
Lemma surjfunPex {T U} {A : set T} {B : set U} :
  $|{surjfun A >-> B}| <-> exists f, B = f @` A.
Proof.
split=> [[f]|[f ->]]; last by squash [fun f in A].
by exists f; apply/seteqP; split=> //; apply: surj.
Qed.

Lemma injfunPex {T U} {A : set T} {B : set U}:
   $|{injfun A >-> B}| <-> exists2 f : T -> U, set_fun A B f & set_inj A f.
Proof. by split=> [[f]|[_ /Pfun[? ->] /funPinj[f]]]; [exists f | squash f]. Qed.
 *)

Lemma card_leP {T U} :
  reflect $|{inj T >-> U}| (T #<= U).
Proof. exact: asboolP. Qed.

Lemma inj_card_le {T U} : {inj T >-> U} -> (T #<= U).
Proof. by move=> f; apply/card_leP. Qed.

(*
Lemma pcard_leP {T} {U : pointedType} {A : set T} {B : set U} :
   reflect $|{injfun A >-> B}| (A #<= B).
Proof.
by apply: (iffP card_leP) => -[f]; [squash (valLR point f) | squash (sigLR f)].
Qed.

Lemma pcard_leTP {T} {U : pointedType} {A : set T} :
  reflect $|{inj A >-> U}| (A #<= [set: U]).
Proof.
by apply: (iffP pcard_leP) => -[f]; [squash f | squash ('totalfun_A f)].
Qed.

 *)
Lemma card_injP {T} {U : Type} :
  reflect (exists f : T -> U, injective f) (T #<= U).
Proof.
apply: (iffP card_leP).
  exact: injPex.1.
exact: injPex.2.
Qed.

Lemma pcard_leP {T : pointedType} {U : Type} :
   reflect $|{splitinj T >-> U}| (T #<= U).
Proof. apply: (iffP card_leP) => -[f]; squash (split f). Qed.

Lemma card_eqP {T U} :
  reflect $|{splitbij T >-> U}| (T #= U).
Proof. exact: asboolP. Qed.

Lemma card_eqVP {T U} :
   reflect $|{splitbij T >-> U}| (U #= T).
Proof. by apply: (iffP card_eqP) => -[] f; squash f^-1. Qed.

Lemma card_lexx T : T #<= T.
Proof. by apply/card_leP; squash idfun. Qed.
#[global] Hint Resolve card_lexx : core.

Lemma card_le_trans (T U V : Type) :
  U #<= T -> T #<= V -> U #<= V.
Proof. by move=> /card_leP[f]/card_leP[g]; apply/card_leP; squash (g \o f). Qed.

Lemma card_eqxx T : T #= T.
Proof. by apply/card_eqP; squash idfun. Qed.
#[global] Hint Resolve card_eqxx : core.

Lemma card_esym T U : T #= U -> U #= T.
Proof. by move=> /card_eqVP TU; apply/card_eqP. Qed.

Lemma card_eq_sym T U : (T #= U) = (U #= T).
Proof. by apply/idP/idP => /card_esym. Qed.

Lemma card_eq_trans T U V (A : set T) (B : set U) (C : set V) :
  A #= B -> B #= C -> A #= C.
Proof. by move=> /card_eqP[f]/card_eqP[g]; apply/card_eqP; squash (g \o f). Qed.

Lemma card_leT T (S : set T) : S #<= T.
Proof. by apply/card_leP; squash val. Qed.

Lemma card_setT T : [set: T] #= T.
Proof. by apply/card_eqVP; squash to_setT. Qed.
#[global] Hint Resolve card_setT : core.

Lemma card_setT_sym T : T #= [set: T].
Proof. exact/card_esym/card_setT. Qed.
#[global] Hint Resolve card_setT : core.

Lemma subset_card_le T (A B : set T) : A `<=` B -> A #<= B.
Proof. by move=> AB; apply/card_leP; squash (incl AB). Qed.

(* TODO: move to classical_sets.v *)
Lemma set00 T : @set0 T -> False.
Proof. by case=> x; rewrite in_set0. Qed.

(* TOTHINK: The subject head is `memType` so I can only declare empty and not
  any other structure (i.e. finType) *)
HB.instance Definition _ T := Type_isEmpty.Build (@set0 T) (@set00 T).

Lemma card_ge0 (T : emptyType) U : T #<= U.
Proof.
apply/card_leP/squash.
have f: T -> U by move=> /no.
by have /Pinj[]: injective f by move=> /[dup]/no.
Qed.
#[global] Hint Resolve card_ge0 : core.

Lemma card_le0P T (U : emptyType) : reflect ([set: T] = set0) (T #<= U).
Proof.
apply: (iffP idP) => [/card_leP[f]|T0].
  by apply/eqP/seteqP => /[dup] /f/no.
apply/card_leP/squash.
have f: T -> U by move=> x; have: x \in setT by []; rewrite T0 in_set0.
suff /Pinj[]: injective f by [].
by move=> x; have: x \in setT by []; rewrite T0 in_set0.
Qed.

Lemma card_le0 T (U : emptyType) : (T #<= U) = ([set: T] == set0).
Proof.
by apply/card_le0P/eqP => T0; apply/eqP/seteqP => x; rewrite in_set0;
  apply/negP => _; have: x \in [set: T] by []; rewrite T0.
Qed.

Lemma card_le_eql {T U V} :
   T #= U -> (T #<= V) = (U #<= V).
Proof.
move=> /card_eqP[f]; apply/card_leP/card_leP => -[] g; apply: squash.
  exact: (g \o f^-1).
exact: (g \o f).
Qed.

Lemma card_le_eqr {T U V} :
   T #= U -> (V #<= T) = (V #<= U).
Proof.
move=> /card_eqP[f]; apply/card_leP/card_leP => -[] g; apply: squash.
  exact: (f \o g).
exact: (f^-1 \o g).
Qed.

Lemma card_eql {T U V} :
   T #= U -> (T #= V) = (U #= V).
Proof.
move=> /card_eqP[f]; apply/card_eqP/card_eqP => -[] g; apply: squash.
  exact: (g \o f^-1).
exact: (g \o f).
Qed.

Lemma card_eqr {T U V} :
   T #= U -> (V #= T) = (V #= U).
Proof.
move=> /card_eqP[f]; apply/card_eqP/card_eqP => -[] g; apply: squash.
  exact: (f \o g).
exact: (f^-1 \o g).
Qed.

Section empty1.
Implicit Types (T : emptyType).
Lemma empty_eq0 T : all_equal_to (set0 : set T).
Proof. by move=> X; apply/setF_eq0/no. Qed.
Lemma card_le_emptyl T U : T #<= U.
Proof. exact: card_ge0. Qed.
Lemma card_le_emptyr T U : (U #<= T) = ([set: U] == set0).
Proof.
by apply/idP/eqP => [/card_le0P//|]; rewrite -(card_le_eql (card_setT U)) => ->.
Qed.

Definition emptyE_subdef := (empty_eq0, card_le_emptyl, card_le_emptyr, eq_opE).
End empty1.

(*
Lemma setC_some (T : eqType) : ~` (range some) = [set None] :> set (option T).
Proof.
apply/eqP/seteqP; case=> [x|].
  by rewrite in_setC range_f/= in_set1; apply/esym/eqP.
by rewrite in_set1 eqxx in_setC; apply/negP => /rangeP[].
Qed.

Lemma card_le_option T U : (option T #<= option U) = (T #<= U).
Proof.
apply/card_leP/card_leP => -[f]; last by squash (omap f).
apply: squash.
wlog: f / range (f \o some) `<=` range some => fsome.
  case/boolP: (range (f \o some) `<=` range some) => [/fsome//|].
  move: f fsome; rewrite -/(_ {classic T}) -/(_ {classic U}) => f fsome.
  move=> /negP/nonsubset/cid[] _ /andP[] /rangeP/cid[] x <-.
  rewrite setC_some in_set1.
  move=> /eqP/= x0.
  apply: (fsome (f \o (@swap (option (classicType T)) None (Some x)))).
  apply/subsetP => _ /rangeP[] y <-/=.
  rewrite -[_ \in _]negbK -in_setC setC_some in_set1 -x0 /swap/=.
  by apply/eqP => /(@inj _ _ f); case: ifPn => /eqP.
admit.
Admitted.
 *)

Lemma card_eq_range T U (f : {inj T >-> U}) : range f #= T.
Proof.
apply/card_esym/card_eqP/squash.
move gE: (sigR f (subset_refl _)) => g.
suff /PbijTT[] : bijective g by [].
rewrite -gE; split; first exact: inj.
apply/subsetP; case=> _ /[dup]/rangeP[] x <- fx _.
by apply/rangeP; exists x; apply: val_inj.
Qed.

Theorem Cantor_Bernstein T U :
  T #<= U -> U #<= T -> T #= U.
Proof.
suff card_eq (A : set T) : T #<= A -> T #= A.
  move=> ? /card_leP[g]; move: (card_eq (range g)).
  by rewrite (card_eqr (card_eq_range g)) (card_le_eqr (card_eq_range g)).
move=> /card_leP[u].
pose C_ := fix C n := if n is n.+1 then (val \o u) @` C n else ~` A.
pose C := \bigcup_n C_ n.
have /subsetP CA : ~` C `<=` A.
  by rewrite setC_bigcup; apply/subsetP => x /in_bigcapP/(_ 0); rewrite setCK.
have uC: {homo (val \o u) : x / x \in C}.
  by move=> x/= => /in_bigcupP[] i Cix; apply/in_bigcupP; exists i.+1 => /=.
pose f x := if x \in C then val (u x) else x.
have fA x : f x \in A by rewrite /f; case: ifPn => // /CA.
suff /PbijTT[s _]: bijective (f : T -> A) by apply/card_eqP/squash.
split.
  move=> x y; rewrite /f => /(congr1 val)/=.
  have [xC|] := boolP (x \in C); have [yC|] := boolP (y \in C) => //.
  - exact: (@inj _ _ (val \o u)).
  - by move=> /[swap]/= <- /negP; have := uC _ xC.
  - by move=> /[swap]/= -> /negP; have := uC _ yC.
apply/subsetP => y _.
case: (boolP (val y \in C)) => [|/negPf yC]; last first.
  by apply/rangeP; exists y; apply: val_inj; rewrite /f/= yC.
move=> /in_bigcupP[] [/negP/(_ _)//|i]/= /imageP[] x [] xC xy.
apply/rangeP; exists x; apply: val_inj; rewrite /f/=.
by have -> : x \in C by apply/in_bigcupP; exists i.
Qed.

Lemma card_eq_le T U : (T #= U) = (T #<= U) && (U #<= T).
Proof.
apply/idP/andP => [/card_eqVP[f]|[]]; last exact: Cantor_Bernstein.
by split; apply/card_leP; [squash f^-1|squash f].
Qed.

Lemma card_eqPle T U : (T #= U) <-> (T #<= U) /\ (U #<= T).
Proof. by rewrite card_eq_le (rwP andP). Qed.

Lemma card_bijP {T U} :
   reflect (exists f : T -> U, bijective f) (T #= U).
Proof.
apply: (iffP card_eqP) => [[f]|[_ /PbijTT[f _]]]; [exists f|squash f].
exact: bij.
Qed.

Lemma card_set_bijP {T U} :
   reflect (exists f, @splitbijective U T f) (T #= U).
Proof.
apply: (iffP card_eqP) => [[f]|[_ /split_bijectiveP/PbijTT[f _]]]; [exists f|squash f].
exact/split_bijectiveP/bij.
Qed.

Lemma card_eq00 T U : @set0 T #= @set0 U.
Proof. by apply: Cantor_Bernstein; apply: card_ge0. Qed.
#[global] Hint Resolve card_eq00 : core.

Lemma card_range_le {T U} (f : T -> U) : range f #<= T.
Proof.
apply/card_leP/squash.
have fsurj : surjective (f : T -> range f).
  apply/subsetP; case=> _ /[dup] /rangeP[] x <- fx _.
  by apply/rangeP; exists x; apply: val_inj.
exact: (fsurj^-1).
Qed.

Lemma card_image_le {T U} (f : T -> U) (A : set T) : f @` A #<= A.
Proof. exact: card_range_le. Qed.

Lemma inj_card_eq {T U} {f : T -> U} : injective f -> range f #= T.
Proof. by move=> /Pinj[] s ->; apply: card_eq_range. Qed.
Arguments inj_card_eq {T U f}.

Lemma card_some {T} : range (some : T -> _) #= T.
Proof. exact/inj_card_eq/Some_inj. Qed.

Lemma card_image {T U} {A : set T} (f : {inj T >-> U}) : f @` A #= A.
Proof. exact: (@card_eq_range _ _(f \o val)). Qed.

(*
Lemma card_imsub {T U} (A : set T) (f : {inj A >-> U}) X : X `<=` A -> f @` X #= X.
Proof. by move=> XA; rewrite (card_image [inj of f \o incl XA]). Qed.

Lemma card_ge_image {T U V} {A : set T} (f : {inj A >-> U}) X (Y : set V) :
  X `<=` A -> (f @` X #<= Y) = (X #<= Y).
Proof. by move=> XA; rewrite (card_le_eql (card_imsub _ _)). Qed.

Lemma card_le_image {T U V} {A : set T} (f : {inj A >-> U}) X (Y : set V) :
  X `<=` A -> (Y #<= f @` X) = (Y #<= X).
Proof. by move=> XA; rewrite (card_le_eqr (card_imsub _ _)). Qed.

Lemma card_le_image2 {T U} (A : set T) (f : {inj A >-> U}) X Y :
   X `<=` A -> Y `<=` A ->
   (f @` X #<= f @` Y) = (X #<= Y).
Proof. by move=> *; rewrite card_ge_image// card_le_image. Qed.

Lemma card_eq_image {T U V} {A : set T} (f : {inj A >-> U}) X (Y : set V) :
  X `<=` A -> (f @` X #= Y) = (X #= Y).
Proof. by move=> XA; rewrite (card_eql (card_imsub _ _)). Qed.

Lemma card_eq_imager {T U V} {A : set T} (f : {inj A >-> U}) X (Y : set V) :
  X `<=` A -> (Y #= f @` X) = (Y #= X).
Proof. by move=> XA; rewrite (card_eqr (card_imsub _ _)). Qed.

Lemma card_eq_image2 {T U} (A : set T) (f : {inj A >-> U}) X Y :
   X `<=` A -> Y `<=` A ->
   (f @` X #= f @` Y) = (X #= Y).
Proof. by move=> *; rewrite card_eq_image// card_eq_imager. Qed.
 *)
Lemma card_ge_some {T U} : (range (some : T -> _) #<= U) = (T #<= U).
Proof. by rewrite (card_le_eql card_some). Qed.

Lemma card_le_some {T U} : (T #<= (range (some : U -> _))) = (T #<= U).
Proof. by rewrite (card_le_eqr card_some). Qed.
(*

Lemma card_le_some2 {T T'} {A : set T} {B : set T'} :
  (some @` A #<= some @` B) = (A #<= B).
Proof. by rewrite card_ge_some card_le_some. Qed.

Lemma card_eq_somel {T T'} {A : set T} {B : set T'} :
  (some @` A #= B) = (A #= B).
Proof. by rewrite (card_eql card_some). Qed.

Lemma card_eq_somer {T T'} {A : set T} {B : set T'} :
  (A #= some @` B) = (A #= B).
Proof. by rewrite (card_eqr card_some). Qed.

Lemma card_eq_some2 {T T'} {A : set T} {B : set T'} :
  (some @` A #= some @` B) = (A #= B).
Proof. by rewrite card_eq_somel card_eq_somer. Qed.
 *)

Lemma card_eq0 {T U} : (T #= @set0 U) = ([set: T] == set0).
Proof. by rewrite card_eq_le card_le0 card_ge0 andbT. Qed.

Lemma card_set1 {T : eqType} {x : T} : [set x] #= `I_1.
Proof.
apply/card_eqP; suff /Pbij[f]: @bijective [set x] `I_1 (fun=> 0%N) by squash f.
split=> [[] _ /[dup]/eqP-> xx [] z /[dup]/eqP-> xx' _|]; first exact: val_inj.
apply/subsetP => y _; apply/rangeP; exists x; apply: val_inj => /=.
by case: y => y/=; rewrite [_ \in _]leqn0 => /eqP/esym.
Qed.

Lemma eq_card1 {T U : eqType} (x : T) (y : U) : [set x] #= [set y].
Proof. by rewrite (card_eql card_set1) (card_eqr card_set1). Qed.

Lemma card_eq_emptyr (T : emptyType) U :
  (U #= T) = ([set: U] == set0).
Proof. by rewrite -(card_eqr (card_setT T)) empty_eq0; exact: card_eq0. Qed.

Lemma card_eq_emptyl (T : emptyType) U :
  (T #= U) = ([set: U] == set0).
Proof. by rewrite card_eq_sym card_eq_emptyr. Qed.

Definition emptyE := (emptyE_subdef, card_eq_emptyr, card_eq_emptyl).

Lemma surj_card_ge {T U} : {surj U >-> T} -> T #<= U.
Proof.
move=> g.
apply: (card_le_trans _ (card_range_le g)).
have := @surj _ _ g; rewrite [surjective _]subTset => /eqP ->.
by rewrite (card_le_eqr (card_setT T)).
Qed.
Arguments surj_card_ge {T U} g.

Lemma pcard_surjP {T : pointedType} {U} :
  reflect (exists g : U -> T, surjective g) (T #<= U).
Proof.
apply: (iffP idP) => [|[_ /Psurj[g _]]]; last exact/surj_card_ge/g.
by move=> /pcard_leP[f]; exists (f^-1); exact: surj.
Qed.

Lemma pcard_geP {T : pointedType} {U} :
  reflect $|{surj U >-> T}| (T #<= U).
Proof. apply: (iffP pcard_surjP).
(* TODO: Why do `rewrite surjPex` and `apply/surjPex` fail? *)
exact: surjPex.2.
exact: surjPex.1.
Qed.

(* TOTHINK: What is the point of this if I still need a pointedType structure
  on T?
Lemma ocard_geP {T U} :
  reflect $|{surj U >-> range (some : T -> _)}| (T #<= U).
Proof.
elim/Ppointed: T => T; rewrite -card_ge_some; last first.
apply: pcard_geP.
Qed.
 *)

Lemma pfcard_geP {T U} :
  reflect ([set: T] = set0 \/ $|{surj U >-> T}|) (T #<= U).
Proof.
apply: (iffP idP); last first.
  move=> [T0|[f]]; last by apply: surj_card_ge; exact: f.
  by rewrite -(card_le_eql (card_setT T)) T0 card_ge0.
elim/Ppointed: T => T; first by rewrite !emptyE; left.
by move=> /pcard_geP; right.
Qed.

Lemma card_le_II n m : (`I_n #<= `I_m) = (n <= m)%N.
Proof.
apply/idP/idP=> [/card_leP[f]|?]; last first.
  by apply/subset_card_le/subsetP => k /leq_trans; apply.
by have /leq_card := @inj _ _ (IIord \o f \o IIord^-1); rewrite !card_ord.
Qed.

Lemma ocard_eqP {T U} :
  reflect $|{splitbij T >-> range (some : U -> _)}| (T #= U).
Proof. by rewrite -(card_eqr card_some); exact: card_eqP. Qed.

(*
Lemma oocard_eqP {T U} {A : set T} {B : set U} :
  reflect $|{splitbij some @` A >-> some @` B}| (A #= B).
Proof.
elim/Pchoice: U => U in B *; elim/Pchoice: T => T in A *.
rewrite -(card_eql card_some) -(card_eqr card_some).
exact: (iffP ppcard_eqP).
Qed.
 *)

Lemma card_eq_II {n m} : reflect (n = m) (`I_n #= `I_m).
Proof. by rewrite card_eq_le !card_le_II -eqn_leq; apply: eqP. Qed.

Lemma sub_setP  {T} {A : set T} (X : set A) : val @` X `<=` A.
Proof. by apply/subsetP => x /imageP[] /= a [] Xa <-. Qed.
Arguments sub_setP {T A}.
Arguments image_subset {aT rT} f [A B].

Lemma card_subP T U :
  reflect (exists (A : set U), A #= T) (T #<= U).
Proof.
apply: (iffP idP) => [/card_leP[f]|[A AT]]; last first.
  by rewrite -(card_le_eql AT) card_leT.
by exists (range f); rewrite (card_eql (inj_card_eq _)).
Qed.

(* remove *)
Lemma pigeonhole m n (f : `I_m -> nat) : injective f ->
  range f `<=` `I_n -> (m <= n)%N.
Proof.
move=> /Pinj[{}f->] /subset_card_le.
by rewrite (card_le_eql (inj_card_eq _))// card_le_II.
Qed.

Definition countable T := T #<= nat.

Lemma eq_countable T U :
  T #= U -> countable T = countable U.
Proof. by move=> /card_le_eql leT; rewrite /countable leT. Qed.

Lemma countableP (T : countType) : countable T.
Proof. by apply/card_leP; squash choice.pickle. Qed.
#[global] Hint Resolve countableP : core.

Lemma countable0 T : countable (@set0 T). Proof. exact: card_ge0. Qed.
#[global] Hint Resolve countable0 : core.

Lemma countable_injP T :
  reflect (exists f : T -> nat, injective f) (countable T).
Proof. exact: card_injP. Qed.

Lemma countable_bijP T :
  reflect (exists B : set nat, (T #= B)%card) (countable T).
Proof.
apply: (iffP idP); last by move=> [B] /eq_countable ->.
move=> /card_leP[f]; exists (range f).
by rewrite (card_eqr (card_eq_range f)).
Qed.

Lemma sub_countable T U : T #<= U ->
  countable U -> countable T.
Proof. exact: card_le_trans. Qed.

Lemma finiteP T : finite T <-> exists n, T #= `I_n.
Proof. by []. Qed.

Lemma eq_finite T U :
  T #= U -> finite T = finite U.
Proof.
move=> eqTU; apply/propeqP.
by split=> -[n Xn]; exists n; move: Xn; rewrite (card_eql eqTU).
Qed.

Lemma finite_II n : finite `I_n. Proof. by apply/finiteP; exists n. Qed.
#[global] Hint Resolve finite_II : core.

Lemma card_II {n} : `I_n #= 'I_n.
Proof. by apply/card_esym/card_eqP; squash IIord^-1. Qed.

Lemma finite_subfset {T : choiceType} (X : {fset T}) : finite [set` X].
Proof.
exists #|{: X}|; rewrite (card_eqr card_II).
by apply/card_eqP; squash (enum_rank \o val_finset).
Qed.
Arguments finite_subfset {T} X.

Lemma finite_subfsetP {T} {U : choiceType} (f : {inj T >-> U}) :
  finite T <-> exists X : {fset U}, range f = [set` X].
Proof.
(* TOTHINK: Why does setoid rewrite fail? *)
split=> [/finiteP [n]|[X] TE]; last first.
  by rewrite -(eq_finite (card_eq_range f)) TE; apply: finite_subfset.
rewrite (card_eqr card_II) => /card_esym/card_eqVP[g].
exists [fset f (g^-1 i) | i in 'I_n]%fset.
apply/eqP/seteqP => y; apply/rangeP/imfsetP => /= [[x <-]|[x _ ->]].
  by exists (g x); rewrite // invK.
by exists (g^-1 x).
Qed.

Lemma finite_fsetP {T : choiceType} :
  finite T <-> exists X : {fset T}, [set: T] = [set` X].
Proof.
suff ->: [set: T] = range id by apply: (finite_subfsetP idfun).
by apply/eqP/seteqP => x; rewrite in_setT; apply/esym.
Qed.

Lemma finite0 T : finite (set0 : set T).
Proof. by apply/finiteP; exists 0%N; rewrite II0. Qed.
#[global] Hint Resolve finite0 : core.

Lemma finite_seq {T : eqType} (s : seq T) : finite [set` s].
Proof.
elim/eqPchoice: T => T in s *.
apply/(finite_subfsetP val).
exists [fset x | x in s]%fset.
apply/eqP/seteqP => x.
apply/rangeP/imfsetP => [[]y <-|[]y + ->].
  by exists (val y); first exact: valP.
by rewrite -[in_mem _ _]/(y \in [set` s])/= => ys; exists y.
Qed.
#[global] Hint Resolve finite_seq : core.

Lemma finite_subseqP {T} {U : choiceType} (f : {inj T >-> U}) :
  finite T <-> exists s : seq U, range f = [set` s].
Proof.
split=> [/finiteP [n]|[s] TE]; last first.
  by rewrite -(eq_finite (card_eq_range f)) TE; apply: finite_seq.
rewrite (card_eqr card_II) => /card_esym/card_eqVP[g].
exists [fset f (g^-1 i) | i in 'I_n]%fset.
apply/eqP/seteqP => y; apply/rangeP/imfsetP => /= [[x <-]|[x _ ->]].
  by exists (g x); rewrite // invK.
by exists (g^-1 x).
Qed.

Lemma finite_seqP {T : eqType} :
   finite T <-> exists s : seq T, [set: T] = [set` s].
Proof.
elim/eqPchoice: T => T.
suff ->: [set: T] = range id by apply: (finite_subseqP idfun).
by apply/eqP/seteqP => x; rewrite in_setT; apply/esym.
Qed.

(* TODO: move to classical_sets.v *)
Lemma range_val {T} (X : set T) : range (val : X -> T) = X.
Proof.
by apply/eqP/seteqP => y; apply/rangeP/idP => [[]x <-//|yX]; exists y.
Qed.

Lemma finite_fset {T : choiceType} (X : {fset T}) : finite X.
Proof.
apply/(finite_subfsetP val); exists X.
apply/eqP/seteqP => y; apply/rangeP/idP => [[]x <-|yX]; first exact: valP.
by exists [` yX]%fset.
Qed.
#[global] Hint Resolve finite_fset : core.

Lemma finite_finpred {T : finType} {pT : predType T} (P : pT) :
  finite [set` P].
Proof.
rewrite (finite_subseqP val); exists (enum P).
by apply/eqP/seteqP => x/=; rewrite range_val mem_enum.
Qed.
#[global]
Hint Extern 0 (finite [set` _]) => solve [apply: finite_finpred] : core.

Lemma finite_finset {T : finType} {X : set T} : finite X.
Proof.
have -> : X = [set` mem X] by apply/eqP/seteqP => x /=; rewrite !inE.
(* TOTHINK: Why is this not applied by the `Hint Extern` above? *)
exact: finite_finpred.
Qed.
#[global] Hint Resolve finite_finset : core.

Lemma finite_countable T : finite T -> countable T.
Proof. by move=> /finiteP[n /eq_countable->]. Qed.

(* TODO: move to classical_sets.v *)
Lemma range_id (T : Type) : range (id : T -> T) = setT.
Proof. by rewrite -image_setT image_id. Qed.

Lemma infiniteP T : infinite T <-> nat #<= T.
Proof.
elim/Pchoice: T => T.
split=> [Ainfinite| + /finiteP[n eqAI]]; last first.
  rewrite (card_le_eqr eqAI) => le_nat_n.
  suff: `I_n.+1 #<= `I_n by rewrite card_le_II ltnn.
  exact/(card_le_trans _ le_nat_n)/card_leT.
have /all_sig[f fX] : forall X : {fset T}, {x | x \notin X}.
  move=> X; apply/sigW; apply: contra_notP Ainfinite => nAX.
  apply/finite_fsetP; exists X; apply/esym/eqP/seteqP => x; rewrite in_setT.
  by apply: contra_notT nAX => xNX; exists x; rewrite ?inE.
suff [g gE] : exists g : nat -> T,
    forall n, g n = f [fset g k | k in iota 0 n]%fset.
  apply/card_injP; exists g.
  move=> i j; apply: contra_eq; wlog lt_ij : i j / (i < j)%N => [hwlog|_].
    by case: ltngtP => // ij _; [|rewrite eq_sym];
      apply: hwlog => //; rewrite (@lt_eqF _ _ _ _ _)//.
  rewrite [g j]gE; set X := (X in f X); have := fX X.
  by apply: contraNneq => <-; apply/imfsetP; exists i => //=; rewrite mem_iota.
pose g := fix g n :=
  if n isn't n'.+1 then fset0 else let X := g n' in (f X |` X)%fset.
exists (f \o g) => /= n; congr f.
elim: n => /= [|n IHn].
  by apply/esym/fsetP => x; rewrite inE; apply/negP => /imfsetP[].
rewrite [X in (_ |` X)%fset]IHn.
apply/fsetP => y; apply/fset1UP/imfsetP => /= [[->|/imfsetP[k] + ->]|[]k + ->].
- by exists n; rewrite // (mem_iota 0 n.+1)/= leqnn.
- rewrite mem_iota => kn; exists k; rewrite // (mem_iota 0 n.+1) ltnS/=.
  exact: ltnW.
rewrite (mem_iota 0 n.+1)/= ltnS leq_eqVlt => /orP[/eqP ->|kn]; first by left.
by right; apply/imfsetP; exists k => //; rewrite mem_iota.
Qed.

Lemma finitePn T : finite T <-> ~ (nat #<= T).
Proof. by rewrite -infiniteP notK. Qed.

Lemma card_le_finite T U :
  T #<= U -> finite U -> finite T.
Proof.
move=> ? /finitePn Ufin; apply/finitePn.
by apply: contra_not Ufin => /card_le_trans; apply.
Qed.

Lemma sub_finite T (A B : set T) : A `<=` B ->
  finite B -> finite A.
Proof. by move=> ?; apply/card_le_finite/subset_card_le. Qed.

Lemma finite_leP T : finite T <-> exists n, T #<= `I_n.
Proof.
split=> [[n /card_eqPle[]]|[n leTn]]; first by exists n.
by apply: card_le_finite leTn _; exists n.
Qed.

Lemma card_ge_preimage {T U} (B : set U) (f : T -> U) :
  injective f -> f @^-1` B #<= B.
Proof.
move=> /Pinj[g eqg]; rewrite -(card_le_eql (card_image g)) -eqg.
by apply: subset_card_le; apply: image_preimage_subset.
Qed.

Corollary finite_preimage {T U} (B : set U) (f : T -> U) :
  injective f -> finite B -> finite (f @^-1` B).
Proof. by move=> /card_ge_preimage fB; apply: card_le_finite. Qed.

Lemma card_le_setD T (A B : set T) : A `\` B #<= A.
Proof. exact/subset_card_le/subDsetl. Qed.

Lemma finite_range T T' (f : T -> T') : finite T -> finite (range f).
Proof. exact/card_le_finite/card_range_le. Qed.

Lemma finite_image T T' (A : set T) (f : T -> T') : finite A -> finite (f @` A).
Proof. exact: finite_range. Qed.

Lemma finite1 (T : eqType) (x : T) : finite [set x].
Proof.
elim/eqPchoice: T => T in x *.
by apply/(finite_subfsetP val); exists (fset1 x); rewrite set_fset1 range_val.
Qed.
#[global] Hint Resolve finite1 : core.

Lemma finiteD T (A B : set T) : finite A -> finite (A `\` B).
Proof. exact/card_le_finite/card_le_setD. Qed.

Lemma finiteU T (A B : set T) :
  finite (A `|` B) = (finite A /\ finite B).
Proof.
elim/Pchoice: T => T in A B *.
rewrite propeqE; split.
  by move=> finAUB; split; apply: sub_finite finAUB.
case=> /(finite_subfsetP val)[] X + /(finite_subfsetP val)[] Y.
rewrite !range_val => -> ->.
apply/(finite_subfsetP val); exists (X `|` Y)%fset.
by rewrite range_val set_fsetU.
Qed.

Lemma finite2 (T : eqType) (x y : T) : finite [set x; y].
Proof. by rewrite !finiteU; split; apply: finite1. Qed.
#[global] Hint Resolve finite2 : core.

Lemma finite3 (T : eqType) (x y z : T) : finite [set x; y; z].
Proof. by rewrite !finiteU; do !split; apply: finite1. Qed.
#[global] Hint Resolve finite3 : core.

Lemma finite4 (T : eqType) (x y z t : T) : finite [set x; y; z; t].
Proof. by rewrite !finiteU; do !split; apply: finite1. Qed.
#[global] Hint Resolve finite4 : core.

Lemma finite5 (T : eqType) (x y z t u : T) : finite [set x; y; z; t; u].
Proof. by rewrite !finiteU; do !split; apply: finite1. Qed.
#[global] Hint Resolve finite5 : core.

Lemma finite6 (T : eqType) (x y z t u v : T) : finite [set x; y; z; t; u; v].
Proof. by rewrite !finiteU; do !split; apply: finite1. Qed.
#[global] Hint Resolve finite6 : core.

Lemma finite7 (T : eqType) (x y z t u v w : T) : finite [set x; y; z; t; u; v; w].
Proof. by rewrite !finiteU; do !split; apply: finite1. Qed.
#[global] Hint Resolve finite7 : core.

Lemma finiteI T (A B : set T) :
  (finite A \/ finite B) -> finite (A `&` B).
Proof.
by case; apply: contraPP => /infiniteP ABfin; apply/infiniteP;
  apply: (card_le_trans ABfin); apply: subset_card_le.
Qed.

Lemma finiteIl T (A B : set T) : finite A -> finite (A `&` B).
Proof. by move=> ?; apply: finiteI; left. Qed.

Lemma finiteIr T (A B : set T) : finite B -> finite (A `&` B).
Proof. by move=> ?; apply: finiteI; right. Qed.

Lemma finite_setX T T' (A : set T) (B : set T') :
  finite A -> finite B -> finite (A `*` B).
Proof.
elim/Pchoice: T => T in A *; elim/Pchoice: T' => T' in B *.
move=> /(finite_subfsetP val)[] A' + /(finite_subfsetP val)[] B' +.
rewrite !range_val => -> ->.
apply/(finite_subfsetP val); exists (A' `*` B')%fset; rewrite range_val.
by apply/eqP/seteqP => x; rewrite in_setX in_fsetM.
Qed.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to finiteX.")]
Notation finiteM := finite_setX (only parsing).

Lemma finiteX T T' :
  finite T -> finite T' -> finite (T * T').
Proof.
rewrite -(eq_finite (card_setT T)) -(eq_finite (card_setT T')).
rewrite -(eq_finite (card_setT (T * T'))).
exact: finite_setX.
Qed.

(* TODO: move to classical_sets.v *)
Lemma range2E {TA TB rT : Type} (f : TA -> TB -> rT) :
  range2 f = range (uncurry f).
Proof.
apply/eqP/seteqP => z; apply/asboolP/asboolP => [[] x [] y <-|[][] x y <-].
  by exists (x, y).
by exists x, y.
Qed.

Lemma finite_range2 [aT bT rT : Type] (f : aT -> bT -> rT) :
  finite aT -> finite bT -> finite [set f x y | x in aT & y in bT].
Proof. by move=> fA fB; rewrite range2E; apply/finite_range/finiteX. Qed.

Lemma finite_image2 [aT bT rT : Type] [A : set aT] [B : set bT]
    (f : aT -> bT -> rT) :
  finite A -> finite B -> finite [set f x y | x in A & y in B].
Proof. by move=> fA fB; rewrite image2E; exact/finite_image/finite_setX. Qed.

Lemma finite_range11 [xT aT bT rT : Type]
    (g : aT -> bT -> rT) (fa : xT -> aT) (fb : xT -> bT) :
    finite (range fa) -> finite (range fb) ->
  finite [set g (fa x) (fb x) | x in xT].
Proof.
move=> /(finite_image2 g) /[apply]; apply: sub_finite; rewrite image2E.
by apply/subsetP => r/= /rangeP[x <-]; apply/rangeP; exists (fa x, fb x).
Qed.

Lemma finite_image11 [xT aT bT rT : Type] [X : set xT]
    (g : aT -> bT -> rT) (fa : xT -> aT) (fb : xT -> bT) :
    finite (fa @` X) -> finite (fb @` X) ->
  finite [set g (fa x) (fb x) | x in X].
Proof. exact: finite_range11. Qed.

Definition fset_set (T : choiceType) (A : set T) :=
  if pselect (finite A) is left Afin
  then projT1 (cid ((finite_subfsetP val).1 Afin)) else fset0.

Lemma fset_setK (T : choiceType) (A : set T) : finite A ->
  [set` fset_set A] = A.
Proof.
rewrite /fset_set; case: pselect => // Afin _; case: cid => /= X /esym.
by rewrite range_val.
Qed.

Lemma in_fset_set (T : choiceType) (A : set T) : finite A ->
  fset_set A =i A.
Proof.
by move=> fA x; rewrite -[A in RHS]fset_setK//; apply/idP/idP; rewrite ?inE.
Qed.

Lemma fset_set_sub (T : choiceType) (A B : set T) :
  finite A -> finite B -> A `<=` B = (fset_set A `<=` fset_set B)%fset.
Proof.
move=> finA finB; apply/subsetP/fsubsetP => AB t.
  by rewrite in_fset_set// in_fset_set// 2!inE => /AB.
by have := AB t; rewrite !in_fset_set// !inE.
Qed.

Lemma fset_set_set0 (T : choiceType) (A : set T) : finite A ->
  fset_set A = fset0 -> A = set0.
Proof.
move=> finA; rewrite /fset_set; case: pselect => // {}finA.
by case: cid => _/= /[swap] ->; rewrite range_val.
Qed.

Lemma fset_set0 {T : choiceType} : fset_set (set0 : set T) = fset0.
Proof.
by apply/fsetP=> x; rewrite in_fset_set ?inE//; apply/negP; rewrite inE.
Qed.

Lemma fset_set1 {T : choiceType} (x : T) : fset_set [set x] = [fset x]%fset.
Proof. by apply/fsetP=> y; rewrite in_fset_set ?inE. Qed.

Lemma fset_setU {T : choiceType} (A B : set T) :
  finite A -> finite B ->
  fset_set (A `|` B) = (fset_set A `|` fset_set B)%fset.
Proof.
move=> fA fB; apply/fsetP=> x.
by rewrite ?(inE, in_fset_set)//; last by rewrite finiteU.
Qed.

Lemma fset_setI {T : choiceType} (A B : set T) :
  finite A -> finite B ->
  fset_set (A `&` B) = (fset_set A `&` fset_set B)%fset.
Proof.
move=> fA fB; apply/fsetP=> x.
rewrite ?(inE, in_fset_set)//; last by apply: finiteI; left.
Qed.

Lemma fset_setU1 {T : choiceType} (x : T) (A : set T) :
  finite A -> fset_set (x |` A) = (x |` fset_set A)%fset.
Proof. by move=> fA; rewrite fset_setU// fset_set1. Qed.

Lemma fset_setD {T : choiceType} (A B : set T) :
  finite A -> finite B ->
  fset_set (A `\` B) = (fset_set A `\` fset_set B)%fset.
Proof.
move=> fA fB; apply/fsetP=> x.
rewrite ?(inE, in_fset_set)//; last exact: finiteD.
by rewrite andbC.
Qed.

Lemma fset_setD1 {T : choiceType} (x : T) (A : set T) :
  finite A -> fset_set (A `\ x) = (fset_set A `\ x)%fset.
Proof. by move=> fA; rewrite fset_setD// fset_set1. Qed.

Lemma fset_setX {T1 T2 : choiceType} (A : set T1) (B : set T2) :
    finite A -> finite B ->
  fset_set (A `*` B) = (fset_set A `*` fset_set B)%fset.
Proof.
move=> Afin Bfin; have ABfin : finite (A `*` B) by exact: finite_setX.
by apply/fsetP => i; apply/idP/idP; rewrite !(inE, in_fset_set).
Qed.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to fset_setX.")]
Notation fset_setM := fset_setX (only parsing).

Definition fst_fset (T1 T2 : choiceType) (A : {fset (T1 * T2)}) : {fset T1} :=
  [fset x.1 | x in A]%fset.
Definition snd_fset (T1 T2 : choiceType) (A : {fset (T1 * T2)}) : {fset T2} :=
  [fset x.2 | x in A]%fset.
Notation "A .`1" := (fst_fset A) : fset_scope.
Notation "A .`2" := (snd_fset A) : fset_scope.

Lemma finite_fst (T1 T2 : choiceType) (A : set (T1 * T2)) :
  finite A -> finite A.`1.
Proof. exact: finite_image. Qed.

Lemma finite_snd (T1 T2 : choiceType) (A : set (T1 * T2)) :
  finite A -> finite A.`2.
Proof. exact: finite_image. Qed.

Lemma bigcup_finite {I T} (D : set I) (F : I -> set T) :
    finite D -> (forall i : D, finite (F i)) ->
  finite (\bigcup_(i in D) F i).
Proof.
elim/Pchoice: I => I in D F *.
elim/Pchoice: T => T in F *.
move=> Dfin Ffin; pose G (i : fset_set D) := fset_set (F (val i)).
suff: (\bigcup_(i in D) F i #<= [set: {i & G i}])%card.
  by move=> /card_le_finite; apply; apply: finite_finset.
rewrite (card_le_eqr (card_setT _)); apply/pfcard_geP; right; apply/surjPex.
have GD : forall (k : {i : fset_set D & G i}),
    val (projT2 k) \in \bigcup_(i in D) F i.
  case=> i x.
  move: (valP i); rewrite in_fset_set//= => iD.
  apply/in_bigcupP; exists (val i) => /=.
  move: (valP x); rewrite in_fset_set//; apply: (Ffin (fsval i)).
exists (fun (k : {i : fset_set D & G i}) => val (projT2 k)).
apply/subsetP => y _.
rewrite -image_setT -(image_inj val_inj) image_comp/comp/=.
case: y => y/= /in_bigcupP[] i yF.
have iD : val i \in fset_set D by move: (valP i); rewrite in_fset_set.
have yG : y \in G [` iD]%fset by rewrite in_fset_set//; apply: Ffin.
by apply/rangeP; exists (existT G [` iD]%fset [` yG]%fset).
Qed.

(* TODO
Lemma trivIset_sum_card (T : choiceType) (F : nat -> set T) n :
  (forall n, finite (F n)) -> trivIset [set: nat] F ->
  (\sum_(i < n) #|` fset_set (F i)| =
   #|` fset_set (\big[setU/set0]_(k < n) F k)|)%N.
Proof.
move=> finF tF; elim: n => [|n ih]; first by rewrite !big_ord0 fset_set0.
rewrite big_ord_recr//= ih big_ord_recr/= fset_setU//; last first.
  by rewrite -bigcup_mkord; exact: bigcup_finite.
rewrite cardfsU [X in (_ - X)%N](_ : _  = O) ?subn0// ?EFinD ?natrD//.
apply/eqP; rewrite cardfs_eq0 -fset_setI//; last first.
  by rewrite -bigcup_mkord; exact: bigcup_finite.
rewrite (@trivIset_bigsetUI _ xpredT)// ?fset_set0//.
by rewrite [X in trivIset X F](_ : _ = [set: nat])//; exact/seteqP.
Qed.

Lemma finiteXR (T T' : choiceType) (A : set T) (B : T -> set T') :
  finite A -> (forall x, A x -> finite (B x)) -> finite (A `*`` B).
Proof.
move=> Afin Bfin; rewrite -bigcupX1l.
by apply: bigcup_finite => // i Ai; exact/finiteX/Bfin.
Qed.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to finiteXR.")]
Notation finiteMR := finiteXR (only parsing).

Lemma finiteXL (T T' : choiceType) (A : T' -> set T) (B : set T') :
  (forall x, B x -> finite (A x)) -> finite B -> finite (A ``*` B).
Proof.
move=> Afin Bfin; rewrite -bigcupX1r.
by apply: bigcup_finite => // i Ai; apply/finiteX => //; exact: Afin.
Qed.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to finiteXL.")]
Notation finiteML := finiteXL (only parsing).

 *)
Lemma fset_set_II n : fset_set `I_n = [fset val i | i in 'I_n]%fset.
Proof.
apply/fsetP => i; rewrite /= ?inE in_fset_set//.
apply/idP/imfsetP => [lt_in|[j _ ->]]; last exact: valP.
by exists (Ordinal lt_in).
Qed.

Lemma set_fsetK (T : choiceType) (A : {fset T}) : fset_set [set` A] = A.
Proof. by apply/fsetP => x; rewrite in_fset_set//=; apply: finite_subfset. Qed.

Lemma fset_set_image {T U : choiceType} (f : T -> U) (A : set T) :
  finite A -> fset_set (f @` A) = (f @` fset_set A)%fset.
Proof.
move=> Afset; apply/fsetP=> i.
rewrite !in_fset_set; last exact: finite_image.
apply/imageP/imfsetP => -[x] => [[]xA <-|xA ->]; exists x => //.
  by rewrite in_fset_set.
by rewrite in_fset_set in xA.
Qed.

Lemma fset_set_inj {T : choiceType} (A B : set T) :
  finite A -> finite B -> fset_set A = fset_set B -> A = B.
Proof. by move=> Afin Bfin /(congr1 pred_set); rewrite !fset_setK. Qed.

(*TODO
Lemma bigsetU_fset_set T (I : choiceType) (A : set I) (F : I -> set T) :
  finite A -> \big[setU/set0]_(i <- fset_set A) F i =\bigcup_(i in A) F i.
Proof.
move=> finA; rewrite -bigcup_fset /fset_set; case: pselect => [{}finA|//].
apply/seteqP; split=> [x [i /=]|x [i Ai Fix]].
  by case: cid => /= B -> iB Fix; exists i.
by exists i => //; case: cid => // B AB /=; move: Ai; rewrite AB.
Qed.

Lemma __deprecated__bigcup_fset_set T (I : choiceType) (A : set I) (F : I -> set T) :
  finite A -> \bigcup_(i in A) F i = \big[setU/set0]_(i <- fset_set A) F i.
Proof. by move=> /bigsetU_fset_set->. Qed.
#[deprecated(note="Use -bigsetU_fset_set instead")]
Notation bigcup_fset_set := __deprecated__bigcup_fset_set (only parsing).

Lemma bigsetU_fset_set_cond T (I : choiceType) (A : set I) (F : I -> set T)
    (P : pred I) : finite A ->
  \big[setU/set0]_(i <- fset_set A | P i) F i = \bigcup_(i in A `&` P) F i.
Proof.
by move=> *; rewrite bigcup_mkcondr big_mkcond -bigsetU_fset_set ?mem_setE.
Qed.

Lemma __deprecated__bigcup_fset_set_cond T (I : choiceType) (A : set I) (F : I -> set T)
    (P : pred I) : finite A ->
  \bigcup_(i in A `&` P) F i = \big[setU/set0]_(i <- fset_set A | P i) F i.
Proof. by move=> /bigsetU_fset_set_cond->. Qed.
#[deprecated(note="Use -bigsetU_fset_set_cond instead")]
Notation bigcup_fset_set_cond := __deprecated__bigcup_fset_set_cond (only parsing).

Lemma bigsetI_fset_set T (I : choiceType) (A : set I) (F : I -> set T) :
  finite A -> \big[setI/setT]_(i <- fset_set A) F i =\bigcap_(i in A) F i.
Proof.
by move=> *; apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigsetU_fset_set.
Qed.

Lemma __deprecated__bigcap_fset_set T (I : choiceType) (A : set I) (F : I -> set T) :
  finite A -> \bigcap_(i in A) F i = \big[setI/setT]_(i <- fset_set A) F i.
Proof. by move=> /bigsetI_fset_set->. Qed.
#[deprecated(note="Use -bigsetI_fset_set instead")]
Notation bigcap_fset_set := __deprecated__bigcap_fset_set (only parsing).

Lemma bigsetI_fset_set_cond T (I : choiceType) (A : set I) (F : I -> set T)
    (P : pred I) : finite A ->
  \big[setI/setT]_(i <- fset_set A | P i) F i = \bigcap_(i in A `&` P) F i.
Proof.
by move=> *; rewrite bigcap_mkcondr big_mkcond -bigsetI_fset_set ?mem_setE.
Qed.

Lemma super_bij T U (X A : set T) (Y B : set U) (f : {splitbij X >-> Y}) :
  X `<=` A -> Y `<=` B -> A `\` X #= B `\` Y ->
  exists g : {splitbij A >-> B}, {in X, val \o g =1 val \o f}.
Proof.
elim/Ppointed: U => U in Y B f *.
  rewrite !emptyE in f * => XA _; rewrite setD_eq0 => AX.
  by suff /seteqP->// : A `<=>` X by exists f.
move=> XA YB /pcard_eqP[g].
rewrite -(joinIB X A) -(joinIB Y B) !meetEset.
have /disj_set2P AX : (A `&` X) `&` (A `\` X) = set0 by apply: meetIB.
have /disj_set2P BY : (B `&` Y) `&` (B `\` Y) = set0 by apply: meetIB.
rewrite !(setIidr XA) !(setIidr YB) in AX BY *.
by exists [bij of glue AX BY f g] => x /= xX; rewrite glue1.
Qed.

Lemma card_eq_fsetP {T : choiceType} {A : {fset T}} {n} :
  reflect (#|` A| = n) ([set` A] #= `I_n).
Proof.
elim/choicePpointed: T => T in A *.
  rewrite -{1}[A]set_fsetK !emptyE fset_set0 cardfs0.
  by apply: (iffP eqP) => [/IIn_eq0->//|<-]; rewrite II0.
rewrite (card_eqr card_II) card_eq_sym.
apply: (iffP pcard_eqP) => [[f]|]; last first.
  rewrite cardfE => eqAn.
  by squash (set_val \o finset_val \o enum_val \o cast_ord (esym eqAn)).
suff -> : A = [fset f i | i in 'I_n]%fset by rewrite card_imfset ?size_enum_ord.
apply/fsetP => x; apply/idP/imfsetP => /= [xA|[i _ ->]].
  by have [i _ <-] := 'surj_f xA; exists i.
by have /(_ i I) := 'funS_f.
Qed.

Lemma card_fset_set {T : choiceType} (A : set T) n :
  A #= `I_n -> #|`fset_set A| = n.
Proof.
move=> An; apply/card_eq_fsetP; rewrite fset_setK//.
by apply/finiteP; exists n.
Qed.

Lemma geq_card_fset_set {T : choiceType} (A : set T) n :
  A #<= `I_n -> (#|`fset_set A| <= n)%N.
Proof.
move=> An; have /finiteP[m Am] : finite A
  by apply/finite_leP; exists n.
by rewrite (card_fset_set Am) -card_le_II -(card_le_eql Am).
Qed.

Lemma leq_card_fset_set {T : choiceType} (A : set T) n :
  finite A -> A #>= `I_n -> (#|`fset_set A| >= n)%N.
Proof.
move=> /finiteP[m Am]; rewrite (card_fset_set Am).
by rewrite (card_le_eqr Am) card_le_II.
Qed.

Lemma infinite_fset {T : choiceType} (A : set T) n :
  infinite A ->
    exists2 B : {fset T}, [set` B] `<=` A & (#|` B| >= n)%N.
Proof.
elim/choicePpointed: T => T in A *; first by rewrite emptyE.
move=> /infiniteP/ppcard_leP[f]; exists (fset_set [set f i | i in `I_n]).
  rewrite fset_setK//; last exact: finite_image.
  by apply: subset_trans (fun_image_sub f); apply: image_subset.
rewrite fset_set_image// card_imfset//= fset_set_II/=.
by rewrite card_imfset//= ?size_enum_ord//; apply: val_inj.
Qed.

Lemma infinite_fsetP {T : choiceType} (A : set T) :
  infinite A <->
   forall n, exists2 B : {fset T}, [set` B] `<=` A & (#|` B| >= n)%N.
Proof.
split; first by move=> ? ?; apply: infinite_fset.
elim/choicePpointed: T => T in A *.
  move=> /(_ 1%N)[B _]; rewrite cardfs_gt0 => /fset0Pn[x xB].
  by have: [set` B] x by []; rewrite emptyE.
move=> Bge /finiteP[n An]; have [B BA] := Bge n.+1.
apply/negP; rewrite -leqNgt -(card_fset_set An) fsubset_leq_card//.
apply/fsubsetP => x /BA; rewrite in_fset_set ?inE//.
by apply/finiteP; exists n.
Qed.

Lemma fcard_eq {T T' : choiceType} (A : set T) (B : set T') :
    finite A -> finite B ->
  reflect (#|`fset_set A| = #|`fset_set B|) (A #= B).
Proof.
move=> /finiteP/cid[n An] /finiteP/cid[m Bm].
rewrite (card_fset_set An) (card_fset_set Bm).
by rewrite (card_eql An) (card_eqr Bm); apply: card_eq_II.
Qed.
 *)

Lemma range_comp {T U V} (f : T -> U) (g : U -> V) :
  g @` (range f) = range (g \o f).
Proof.
by rewrite -[range f]image_setT image_comp image_setT.
Qed.

Lemma card_IID {n k} : `I_n `\` `I_k #= `I_(n - k)%N.
Proof.
apply/card_bijP.
have nk (i : `I_n `\` `I_k) : (val i - k)%N \in `I_(n - k).
  move: (valP i) => /andP[]; rewrite !in_mkset -leqNgt => ilt ki.
  by rewrite ltn_sub2rE.
exists (fun i : `I_n `\` `I_k => (val i - k)%N).
split=> [i j /(congr1 val)/= ij|].
  apply: val_inj; case: i j ij => i /andP[] + + [] j/= /andP[] + + /eqP.
  rewrite !in_mkset -!leqNgt => ilt ki jlt kj.
  by rewrite eqn_sub2rE => /eqP.
apply/subsetP => -[] j jlt _.
rewrite -(image_inj val_inj) range_comp /comp/=.
have jnk : (j + k)%N \in `I_n `\` `I_k.
  by rewrite !in_mkset -leqNgt leq_addl andbT addnC -ltn_subRL.
by apply/rangeP; exists (j + k)%N; rewrite /= addnK.
  (*TODO: restore old proof once I fix the previousTODOs.
apply/fcard_eq => //; first exact: finiteD.
rewrite fset_setD//= cardfsD/= -fset_setI// setI_II.
rewrite !fset_set_II !card_imfset// /= !size_enum_ord.
by case: leqP; rewrite // subnn => /eqP->.
   *)
Qed.

(*
Lemma finite_bij T (A : set T) n S : A != set0 ->
    A #= `I_n -> S `<=` A ->
  exists (f : {bij `I_n >-> A}) k, (k <= n)%N /\ `I_n `&` (f @^-1` S) = `I_k.
Proof.
elim/Ppointed: T => T in A S *; first by rewrite !emptyE eqxx.
move=> AN0 An SA; have [k kn Sk] : exists2 k, (k <= n)%N & S #= `I_k.
  have /finiteP[k Sk]: finite S by apply: sub_finite SA _; exists n.
  exists k => //; rewrite -card_le_II.
  by rewrite -(card_le_eqr An) -(card_le_eql Sk); apply: subset_card_le.
have /card_esym/ppcard_eqP[f] := Sk.
have eqAS : A `\` S #= `I_n `\` `I_k.
  have An' := An; have Sk' := Sk.
  do [have /finite_fsetP[{An'}A ->] : finite A by exists n] in An AN0 SA *.
  do [have /finite_fsetP[{Sk'}S ->] : finite S by exists k] in Sk f SA *.
  have [/card_eq_fsetP {}An /card_eq_fsetP {}Sk] := (An, Sk).
  rewrite -set_fsetD (card_eqr card_IID); apply/card_eq_fsetP.
  by rewrite cardfsD (fsetIidPr _) ?An ?Sk //; apply/fsubsetP.
case: (super_bij [bij of f^-1] SA _ eqAS) => [x /= /leq_trans->// | g].
have [{}g ->] := pPbij 'bij_g => /= gE.
exists [bij of g^-1], k; split=> //=; rewrite -inv_sub_image //= invV.
by under eq_imagel do rewrite /= gE ?inE//; rewrite image_eq.
Qed.
 *)
#[deprecated(note="use countable0 instead")]
Notation countable_set0 := countable0 (only parsing).

Lemma countable1 (T : eqType) (x : T) : countable [set x].
Proof. exact: finite_countable. Qed.
#[global] Hint Resolve countable1 : core.

Lemma countable_fset (T : choiceType) (X : {fset T}) : countable [set` X].
Proof. exact/finite_countable/finite_subfset. Qed.
#[global] Hint Resolve countable_fset : core.

Lemma countable_finpred (T : finType) (pT : predType T) (P : pT) : countable [set` P].
Proof. exact: finite_countable. Qed.
#[global] Hint Extern 0 (is_true (countable [set` _])) => solve [apply: countable_finpred] : core.

Lemma eq_card_nat T :
  countable T -> ~ finite T -> T #= nat.
Proof. by move=> Acnt /infiniteP leNT; rewrite card_eq_le leNT andbT. Qed.

Lemma infinite_nat : ~ finite nat.
Proof. exact/infiniteP/card_lexx. Qed.

Lemma infinite_prod_nat : infinite (nat * nat).
Proof. by apply/infiniteP/card_leP/injPex; exists (pair 0%N) => // m n []. Qed.

Lemma card_nat2 : nat * nat #= nat.
Proof. exact/eq_card_nat/infinite_prod_nat/countableP. Qed.

(* TODO: What is this doing here? *)
HB.instance Definition _ := isPointed.Build rat 0.

Lemma infinite_rat : infinite rat.
Proof.
apply/infiniteP/card_leP/injPex; exists (GRing.natmul 1) => // m n.
exact: Num.Theory.mulrIn.
Qed.

Lemma card_rat : rat #= nat.
Proof. exact/eq_card_nat/infinite_rat/countableP. Qed.

Lemma choicePcountable {T : choiceType} : countable T ->
  {T' : countType | T = T' :> Type}.
Proof.
move=> /card_leP/unsquash f.
pose TcM := PCanIsCountable (@funoK _ _ f).
pose TC : countType := HB.pack T TcM.
by exists TC.
Qed.

Lemma eqPcountable {T : eqType} : countable T ->
  {T' : countType | T = T' :> Type}.
Proof. by elim/eqPchoice: T => T /choicePcountable. Qed.

Lemma Pcountable {T : Type} : countable T ->
  {T' : countType | T = T' :> Type}.
Proof. by elim/Pchoice: T => T /choicePcountable. Qed.

Lemma bigcup_countable {I T} (F : I -> set T) :
    countable I -> (forall i, countable (F i)) ->
  countable (\bigcup_i F i).
Proof.
move: F => /[swap] /Pcountable[] {}I -> F cF.
suff: (\bigcup_i F i #<= {i & F i})%card.
  have /all_sig[G GE] := fun i => Pcountable (cF i).
  move=> /sub_countable; apply.
  by rewrite (eq_fun GE); apply: countableP.
apply/pfcard_geP; right; apply/surjPex.
have fP (k : {i & F i}) : val (projT2 k) \in \bigcup_i F i.
  by case: k => i x/=; apply/in_bigcupP; exists i.
exists (fun (k : {i & F i}) => val (projT2 k)).
apply/subsetP => x _.
rewrite -(image_inj val_inj) range_comp /comp/=.
case: x => x/= /in_bigcupP[] i xi.
by apply/rangeP; exists (existT F i (x : F i)).
Qed.

(* TODO:
Lemma countableXR T T' (A : set T) (B : T -> set T') :
  countable A -> (forall i, A i -> countable (B i)) -> countable (A `*`` B).
Proof.
elim/Ppointed: T => T in A B *; first by rewrite emptyE -bigcupX1l bigcup_set0.
elim/Ppointed: T' => T' in B *.
  by rewrite -bigcupX1l bigcup0// => i; rewrite emptyE setX0.
move=> Ac Bc; rewrite -bigcupX1l bigcup_countable// => i Ai.
have /ppcard_leP[f] := Bc i Ai; apply/pcard_geP/surjPex.
exists (fun k => (i, f^-1%FUN k)) => -[_ j]/= [-> dj].
by exists (f j) => //=; rewrite funK ?inE.
Qed.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to countableXR.")]
Notation countableMR := countableXR (only parsing).

Lemma countableX T1 T2 (D1 : set T1) (D2 : set T2) :
  countable D1 -> countable D2 -> countable (D1 `*` D2).
Proof. by move=> D1c D2c; exact: countableXR (fun _ _ => D2c). Qed.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to countableX.")]
Notation countableM := countableX (only parsing).

Lemma countableXL T T' (A : T' -> set T) (B : set T') :
  countable B -> (forall i, B i -> countable (A i)) -> countable (A ``*` B).
Proof.
move=> Bc Ac; rewrite -bigcupX1r; apply: bigcup_countable => // i Bi.
by apply: countableX => //; exact: Ac.
Qed.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to countableXL.")]
Notation countableML := countableXL (only parsing).

Lemma infiniteXRl T T' (A : set T) (B : T -> set T') :
  infinite A -> (forall i, B i !=set0) -> infinite (A `*`` B).
Proof.
move=> /infiniteP/pcard_geP[f] /(_ _)/cid-/all_sig[b Bb].
apply/infiniteP/pcard_geP/surjPex; exists (fun x => f x.1).
by move=> i iT; have [a Aa fa] := 'oinvP_f iT; exists (a, b a).
Qed.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to infiniteXRl.")]
Notation infiniteMRl := infiniteXRl (only parsing).

Lemma cardXR_eq_nat T T' (A : set T) (B : T -> set T') :
    (A #= [set: nat] -> (forall i, countable (B i) /\ B i !=set0) ->
   A `*`` B #= [set: nat])%card.
Proof.
rewrite !card_eq_le => /andP[Acnt /infiniteP Ainfty] /all_and2[Bcnt Bn0].
by rewrite [(_ #<= _)%card]countableXR//=; exact/infiniteP/infiniteXRl.
Qed.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to cardXR_eq_nat.")]
Notation cardMR_eq_nat := cardXR_eq_nat (only parsing).

Lemma eq_cardSP {T : Type} (A : set T) n :
  reflect (exists2 x, A x & A `\ x #= `I_n) (A #= `I_n.+1).
Proof.
elim/Ppointed: T A => T A.
  rewrite !emptyE; apply: (iffP eqP) => [|[]//].
  by move=> /(congr1 (@^~ 0%N))/=; rewrite -falseE ltnS leq0n => /is_true_inj.
apply: (iffP idP) => [|[x Ax]].
  move=> /ppcard_eqP[f]; exists (f^-1 n); first by apply: funS => /=.
  by apply/card_esym/card_set_bijP; exists f^-1; apply: bij_II_D1.
move=> /pcard_eqP[f]; have [//|||g _] := @super_bij _ _ _ A _ `I_n.+1 f.
- by move=> k /=; apply: leq_trans.
- by rewrite setDD (card_eqr card_IID) subSnn// setIidr ?card_set1// => ? ->.
- by apply/pcard_eqP; squash g.
Qed.

Lemma countable_n_subset {T : Type} (D : set T) n :
  countable D -> countable [set A | A `<=` D /\ A #= `I_n].
Proof.
move=> Dcnt; elim: n => [|n].
  rewrite [X in countable X]( _ : _ = [set set0])// eqEsubset II0.
  by split=> A /=; [rewrite card_eq0; case=> _ /eqP | move->; split].
move=> /(countableX Dcnt); apply: sub_countable.
apply: card_le_trans (card_image_le (fun u => u.1 |` u.2) _).
apply: subset_card_le => B [BD] /eq_cardSP [x Bx BDx].
exists (x, B `\ x) => /=; last by apply: setDUK => ? ->.
by do !split=> //; [exact: BD | apply: subset_trans _ BD; apply: subDsetl].
Qed.

Lemma countable_finite_subset {T : Type} (D : set T) :
  countable D -> countable [set A | A `<=` D /\ finite A ].
Proof.
move=> Dcnt; suff -> : [set A | A `<=` D /\ finite A ] =
    \bigcup_n [set A | A `<=` D /\ A #= `I_n ].
  by apply: bigcup_countable => // ? _; exact: countable_n_subset.
rewrite eqEsubset; split=> [A [AD /finiteP[n An]]|A]; first by exists n.
by move=> [n _ [AD An]]; split=> //; apply/finiteP; exists n.
Qed.

Lemma eq_card_fset_subset {T : pointedType} (D : set T) :
  [set A | A `<=` D /\ finite A ] #= [set A : {fset T} | {subset A <= D}] .
Proof.
apply/card_set_bijP; exists (@fset_set T); split.
- by move=> A [AD fsetA] /= x; rewrite in_fset_set // ?inE; exact: AD.
- by move=> ? ? /set_mem [_ +] /set_mem [_ +]; exact: fset_set_inj.
- move=> B /= BD; exists [set` B]; rewrite ?set_fsetK //.
  by split; [by move => x /= /BD /set_mem | exact: finite_fset].
Qed.

Lemma fset_subset_countable {T : pointedType} (D : set T) :
  countable D -> countable [set A : {fset T} | {subset A <= D}].
Proof.
rewrite -(eq_countable (eq_card_fset_subset _)) => ?.
exact: countable_finite_subset.
Qed.
 *)
HB.mixin Record FiniteImage aT rT (f : aT -> rT) := {
  fimfunP : finite (range f)
}.
HB.structure Definition FImFun aT rT := {f of @FiniteImage aT rT f}.

Arguments fimfunP {aT rT} _.
#[global] Hint Extern 0 (finite _) => solve [apply: fimfunP] : core.

Reserved Notation "{ 'fimfun' aT >-> T }"
  (at level 0, format "{ 'fimfun'  aT  >->  T }").
Reserved Notation "[ 'fimfun' 'of' f ]"
  (at level 0, format "[ 'fimfun'  'of'  f ]").
Notation "{ 'fimfun' aT >-> T }" := (@FImFun.type aT T) : form_scope.
Notation "[ 'fimfun' 'of' f ]" := [the {fimfun _ >-> _} of f] : form_scope.

Lemma fimfun_inP {aT rT} (f : {fimfun aT >-> rT}) (D : set aT) :
  finite (f @` D).
Proof.
apply: (@sub_finite _ _ (range f)); last exact: fimfunP.
by rewrite -[X in _ `<=` X]image_setT; apply/image_subset/subsetT.
Qed.

#[global] Hint Resolve fimfun_inP : core.

Lemma fset_set_comp (T1 : Type) (T2 T3 : choiceType) (D : set T1)
    (f : {fimfun T1 >-> T2}) (g : T2 -> T3) :
  fset_set [set (g \o f) x | x in D] =
  [fset g x | x in fset_set [set f x | x in D]]%fset.
Proof. by rewrite -(image_comp f g) fset_set_image. Qed.

Section fimfun_pred.
Context {aT rT : Type}.
Definition fimfun : {pred aT -> rT} := mem [set f | `[< finite (range f) >]].
Definition fimfun_key : pred_key fimfun.
Proof. exact. Qed.
Canonical fimfun_keyed := KeyedPred fimfun_key.
End fimfun_pred.

Section fimfun.
Context {aT rT : Type}.
Notation T := {fimfun aT >-> rT}.
Notation fimfun := (@fimfun aT rT).
Section Sub.
Context (f : aT -> rT) (fP : f \in fimfun).
Definition fimfun_Sub_subproof := @FiniteImage.Build aT rT f (elimTF (asboolP _) fP).
#[local] HB.instance Definition _ := fimfun_Sub_subproof.
Definition fimfun_Sub := [fimfun of f].
End Sub.

Lemma fimfun_rect (K : T -> Type) :
  (forall f (Pf : f \in fimfun), K (fimfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf]]]/=.
move: (Ksub _ (introT (asboolP _) Pf)).
congr (K (FImFun.Pack (FImFun.Class (FiniteImage.Axioms_ _ _ _)))).
exact: Prop_irrelevance.
Qed.

Lemma fimfun_valP f (Pf : f \in fimfun) : fimfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T fimfun_rect fimfun_valP.
End fimfun.

Lemma fimfuneqP aT rT (f g : {fimfun aT >-> rT}) :
  f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ aT (rT : eqType) :=
  [Equality of {fimfun aT >-> rT} by <:].

HB.instance Definition _ aT (rT : choiceType) :=
  [Choice of {fimfun aT >-> rT} by <:].

Lemma finite_image_cst {aT rT : Type} (x : rT) :
  finite (range (cst x : aT -> _)).
Proof.
elim/Pchoice: rT => rT in x *.
suff /sub_finite: range (@cst aT _ x) `<=` [set x] by apply; apply: finite1.
by apply/subsetP => y /rangeP[] z <-.
Qed.

HB.instance Definition _ aT rT x :=
  FiniteImage.Build aT rT (cst x) (@finite_image_cst aT rT x).

Definition cst_fimfun {aT rT} x : {fimfun aT >-> rT} := cst x.

Lemma fimfun_cst aT rT x : @cst_fimfun aT rT x =1 cst x. Proof. by []. Qed.

Lemma comp_fimfun_subproof aT rT sT
   (f : {fimfun aT >-> rT}) (g : rT -> sT) : @FiniteImage aT sT (g \o f).
Proof. by split; rewrite -(range_comp f g); apply: finite_image. Qed.
HB.instance Definition _ aT rT sT f g := @comp_fimfun_subproof aT rT sT f g.

Section zmod.
Context (aT : Type) (rT : zmodType).
Lemma fimfun_zmod_closed : zmod_closed (@fimfun aT rT).
Proof.
split=> [|f g /asboolP fA /asboolP gA]; apply/asboolP.
  exact: finite_image_cst.
exact: (finite_range11 (fun x y => x - y)).
Qed.
HB.instance Definition _ :=
  GRing.isZmodClosed.Build (aT -> rT) fimfun fimfun_zmod_closed.
HB.instance Definition _ :=
  [SubChoice_isSubZmodule of {fimfun aT >-> rT} by <:].

Implicit Types (f g : {fimfun aT >-> rT}).

Lemma fimfunD f g : f + g = f \+ g :> (_ -> _). Proof. by []. Qed.
Lemma fimfunN f : - f = \- f :> (_ -> _). Proof. by []. Qed.
Lemma fimfunB f g : f - g = f \- g :> (_ -> _). Proof. by []. Qed.
Lemma fimfun0 : (0 : {fimfun aT >-> rT}) = cst 0 :> (_ -> _). Proof. by []. Qed.
Lemma fimfun_sum I r (P : {pred I}) (f : I -> {fimfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.

HB.instance Definition _ f g := FImFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := FImFun.copy (\- f) (- f).
HB.instance Definition _ f g := FImFun.copy (f \- g) (f - g).
End zmod.
