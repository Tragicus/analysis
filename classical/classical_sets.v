(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From elpi Require Import coercion tc.
From mathcomp Require Import all_ssreflect ssralg matrix finmap ssrnum.
From mathcomp Require Import ssrint interval.
From mathcomp Require Import mathcomp_extra boolp.

(**md**************************************************************************)
(* # Set Theory                                                               *)
(*                                                                            *)
(* This file develops a basic theory of sets and types equipped with a        *)
(* canonical inhabitant (pointed types):                                      *)
(* - A decidable equality is defined for any type. It is thus possible to     *)
(*   define an eqType structure for any type using the mixin gen_eqMixin.     *)
(* - This file adds the possibility to define a choiceType structure for      *)
(*   any type thanks to an axiom gen_choiceMixin giving a choice mixin.       *)
(* - We chose to have generic mixins and no global instances of the eqType    *)
(*   and choiceType structures to let the user choose which definition of     *)
(*   equality to use and to avoid conflict with already declared instances.   *)
(*                                                                            *)
(* Thanks to this basic set theory, we proved Zorn's Lemma, which states      *)
(* that any ordered set such that every totally ordered subset admits an      *)
(* upper bound has a maximal element. We also proved an analogous version     *)
(* for preorders, where maximal is replaced with premaximal: $t$ is           *)
(* premaximal if whenever $t < s$ we also have $s < t$.                       *)
(*                                                                            *)
(* About the naming conventions in this file:                                 *)
(* - use T, T', T1, T2, etc., aT (domain type), rT (return type) for names    *)
(*   of variables in Type (or choiceType/pointedType/porderType)              *)
(*   + use the same suffix or prefix for the sets as their containing type    *)
(*     (e.g., A1 in T1, etc.)                                                 *)
(*   + as a consequence functions are rather of type aT -> rT                 *)
(* - use I, J when the type corresponds to an index                           *)
(* - sets are named A, B, C, D, etc., or Y when it is ostensibly an image     *)
(*   set (i.e., of type set rT)                                               *)
(* - indexed sets are rather named F                                          *)
(*                                                                            *)
(* Examples of notations:                                                     *)
(* | Coq notations                |   | Meaning                             | *)
(* |-----------------------------:|---|:------------------------------------  *)
(* |                         set0 |==| $\emptyset$                            *)
(* |                     [set: A] |==| the full set of elements of type A     *)
(* |                   `` `\|` `` |==| $\cup$                                 *)
(* |                    `` `&` `` |==| $\cap$                                 *)
(* |                    `` `\` `` |==| set difference                         *)
(* |                    `` `+` `` |==| symmetric difference                   *)
(* |                     `` ~` `` |==| set complement                         *)
(* |                   `` `<=` `` |==| $\subseteq$                            *)
(* |                 `` f @` A `` |==| image by f of A                        *)
(* |              `` f @^-1` A `` |==| preimage by f of A                     *)
(* |                      [set x] |==| the singleton set $\{x\}$              *)
(* |                     [set~ x] |==| the complement of $\{x\}$              *)
(* |            [set E \| x in P] |==| the set of E with x ranging in P       *)
(* |                      range f |==| image by f of the full set             *)
(* | \big[setU/set0]_(i <- s \| P i) f i |==| finite union                    *)
(* |         \bigcup_(k in P) F k |==| countable union                        *)
(* |         \bigcap_(k in P) F k |==| countable intersection                 *)
(* |                 trivIset D F |==| F is a sequence of pairwise disjoint   *)
(* |                              |  | sets indexed over the domain D         *)
(*                                                                            *)
(* Detailed documentation:                                                    *)
(* ## Sets                                                                    *)
(* ```                                                                        *)
(*                       set T == type of sets on T                           *)
(*                   (x \in P) == boolean membership predicate from ssrbool   *)
(*                                for set P, available thanks to a canonical  *)
(*                                predType T structure on sets on T           *)
(*             [set x : T | P] == set of points x : T such that P holds       *)
(*                 [set x | P] == same as before with T left implicit         *)
(*            [set E | x in A] == set defined by the expression E for x in    *)
(*                                set A                                       *)
(*   [set E | x in A & y in B] == same as before for E depending on 2         *)
(*                                variables x and y in sets A and B           *)
(*                        setT == full set                                    *)
(*                        set0 == empty set                                   *)
(*                     range f == the range of f, i.e., [set f x | x in setT] *)
(*                     [set a] == set containing only a                       *)
(*                 [set a : T] == same as before with the type of a made      *)
(*                                explicit                                    *)
(*                     A `|` B == union of A and B                            *)
(*                      a |` A == A extended with a                           *)
(*        [set a1; a2; ..; an] == set containing only the n elements ai       *)
(*                     A `&` B == intersection of A and B                     *)
(*                     A `*` B == product of A and B, i.e., set of pairs      *)
(*                                (a,b) such that A a and B b                 *)
(*                        A.`1 == set of points a such that there exists b so *)
(*                                that A (a, b)                               *)
(*                        A.`2 == set of points a such that there exists b so *)
(*                                that A (b, a)                               *)
(*                        ~` A == complement of A                             *)
(*                    [set~ a] == complement of [set a]                       *)
(*                     A `\` B == complement of B in A                        *)
(*                      A `\ a == A deprived of a                             *)
(*                        `I_n := [set k | k < n]                             *)
(*          \bigcup_(i in P) F == union of the elements of the family F whose *)
(*                                index satisfies P                           *)
(*           \bigcup_(i : T) F == union of the family F indexed on T          *)
(*           \bigcup_(i < n) F := \bigcup_(i in `I_n) F                       *)
(*          \bigcup_(i >= n) F := \bigcup_(i in [set i | i >= n]) F           *)
(*                 \bigcup_i F == same as before with T left implicit         *)
(*          \bigcap_(i in P) F == intersection of the elements of the family  *)
(*                                F whose index satisfies P                   *)
(*           \bigcap_(i : T) F == union of the family F indexed on T          *)
(*           \bigcap_(i < n) F := \bigcap_(i in `I_n) F                       *)
(*          \bigcap_(i >= n) F := \bigcap_(i in [set i | i >= n]) F           *)
(*                 \bigcap_i F == same as before with T left implicit         *)
(*                smallest C G := \bigcap_(A in [set M | C M /\ G `<=` M]) A  *)
(*                   A `<=` B <-> A is included in B                          *)
(*                     A `<` B := A `<=` B /\ ~ (B `<=` A)                    *)
(*                  A `<=>` B <-> double inclusion A `<=` B and B `<=` A      *)
(*                   f @^-1` A == preimage of A by f                          *)
(*                      f @` A == image of A by f                             *)
(*                                This is a notation for `image A f`          *)
(*                    A !=set0 := exists x, A x                               *)
(*                    [set` p] == a classical set corresponding to the        *)
(*                                predType p                                  *)
(*                     `[a, b] := [set` `[a, b]], i.e., a classical set       *)
(*                                corresponding to the interval `[a, b]       *)
(*                     `]a, b] := [set` `]a, b]]                              *)
(*                     `[a, b[ := [set` `[a, b[]                              *)
(*                     `]a, b[ := [set` `]a, b[]                              *)
(*                   `]-oo, b] := [set` `]-oo, b]]                            *)
(*                   `]-oo, b[ := [set` `]-oo, b[]                            *)
(*                   `[a, +oo[ := [set` `[a, +oo[]                            *)
(*                   `]a, +oo[ := [set` `]a, +oo[]                            *)
(*                 `]-oo, +oo[ := [set` `]-oo, +oo[]                          *)
(*               is_subset1 A <-> A contains only 1 element                   *)
(*                   is_fun f <-> for each a, f a contains only 1 element     *)
(*                 is_total f <-> for each a, f a is non empty                *)
(*              is_totalfun f <-> conjunction of is_fun and is_total          *)
(*                   xget x0 P == point x in P if it exists, x0 otherwise;    *)
(*                                P must be a set on a choiceType             *)
(*             fun_of_rel f0 f == function that maps x to an element of f x   *)
(*                                if there is one, to f0 x otherwise          *)
(*                    F `#` G <-> intersections beween elements of F an G are *)
(*                                all non empty                               *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Pointed types                                                           *)
(* ```                                                                        *)
(*                 pointedType == interface type for types equipped with a    *)
(*                                canonical inhabitant                        *)
(*                                The HB class is Pointed.                    *)
(*                       point == canonical inhabitant of a pointedType       *)
(*                       get P == point x in P if it exists, point otherwise  *)
(*                                P must be a set on a pointedType.           *)
(* ```                                                                        *)
(*                                                                            *)
(* ## squash/unsquash                                                         *)
(* ```                                                                        *)
(*                      $| T | == the type `T : Type` is inhabited            *)
(*                                $| T | has type `Prop`.                     *)
(*                                $| T | is a notation for `squashed T`.      *)
(*                    squash x == object of type $| T | (with x : T)          *)
(*                  unsquash s == extract an inhabitant of type `T`           *)
(*                                (with s : $| T |)                           *)
(* ```                                                                        *)
(* Tactic:                                                                    *)
(*   - squash x:                                                              *)
(*     solves a goal $| T | by instantiating with x or [the T of x]           *)
(*                                                                            *)
(* ## Pairwise-disjoint sets                                                  *)
(* ```                                                                        *)
(*                trivIset D F == the sets F i, where i ranges over           *)
(*                                D : set I, are pairwise-disjoint            *)
(*                   cover D F := \bigcup_(i in D) F i                        *)
(*             partition D F A == the non-empty sets F i,where i ranges over  *)
(*                                D : set I, form a partition of A            *)
(*          pblock_index D F x == index i such that i \in D and x \in F i     *)
(*                pblock D F x := F (pblock_index D F x)                      *)
(*                                                                            *)
(*   maximal_disjoint_subcollection F A B == A is a maximal (for inclusion)   *)
(*                                   disjoint subcollection of the collection *)
(*                                   B of elements in F : I -> set T          *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Upper and lower bounds                                                  *)
(* ```                                                                        *)
(*              ubound A == the set of upper bounds of the set A              *)
(*              lbound A == the set of lower bounds of the set A              *)
(* ```                                                                        *)
(*                                                                            *)
(* Predicates to express existence conditions of supremum and infimum of sets *)
(* of real numbers:                                                           *)
(* ```                                                                        *)
(*          has_ubound A := ubound A != set0                                  *)
(*             has_sup A := A != set0 /\ has_ubound A                         *)
(*          has_lbound A := lbound A != set0                                  *)
(*             has_inf A := A != set0 /\ has_lbound A                         *)
(*                                                                            *)
(*             isLub A m := m is a least upper bound of the set A             *)
(*           supremums A := set of supremums of the set A                     *)
(*         supremum x0 A == supremum of A or x0 if A is empty                 *)
(*            infimums A := set of infimums of the set A                      *)
(*          infimum x0 A == infimum of A or x0 if A is empty                  *)
(*                                                                            *)
(*               F `#` G := the classes of sets F and G intersect             *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Sections                                                                *)
(* ```                                                                        *)
(*           xsection A x == with A : set (T1 * T2) and x : T1 is the         *)
(*                           x-section of A                                   *)
(*           ysection A y == with A : set (T1 * T2) and y : T2 is the         *)
(*                           y-section of A                                   *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Relations                                                               *)
(* Notations for composition and inverse (scope: relation_scope):             *)
(* ```                                                                        *)
(*                B \; A == [set x | exists z, A (x.1, z) & B (z, x.2)]       *)
(*                  A^-1 == [set xy | A (xy.2, xy.1)]                         *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

TC.AddAllClasses.
TC.AddAllInstances.

(* Add typeclass resolution to trivial things
   (maybe dangerous in general, must be restricted). *)
Ltac done :=
  trivial; hnf; intros; (solve
   [ do
   ![ solve
    [ trivial | simple refine (eq_sym _); trivial ]
    | discriminate
    | contradiction
    | split ]
   | match goal with
     | H:~ _ |- _ => solve [ case H; trivial ]
     end
   | apply _ ]).

Ltac done_tc := apply _.

Declare Scope classical_set_scope.

Reserved Notation "[ 'set' x : T | P ]" (only parsing).
Reserved Notation "[ 'set' x | P ]" (format "[ 'set'  x  |  P ]").
Reserved Notation "[ 'set' E | x 'in' A ]"
  (format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'set' E | x 'in' A & y 'in' B ]"
  (format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'").
Reserved Notation "[ 'set' a ]" (format "[ 'set'  a ]").
Reserved Notation "[ 'set' : T ]" (format "[ 'set' :  T ]").
Reserved Notation "[ 'set' a : T ]" (format "[ 'set'  a   :  T ]").
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `*`` B"  (at level 46, left associativity).
Reserved Notation "A ``*` B"  (at level 46, left associativity).
Reserved Notation "A .`1" (format "A .`1").
Reserved Notation "A .`2" (format "A .`2").
Reserved Notation "~` A" (at level 35, right associativity).
Reserved Notation "[ 'set' ~ a ]" (format "[ 'set' ~  a ]").
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).
Reserved Notation "A `+` B" (at level 54, left associativity).
Reserved Notation "A `<` B" (at level 70, no associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<=>` B" (at level 70, no associativity).
Reserved Notation "f @^-1` A" (at level 24).
Reserved Notation "f @` A" (at level 24).
Reserved Notation "A !=set0" (at level 80).
Reserved Notation "[ 'set`' p ]" (format "[ 'set`'  p ]").
Reserved Notation "[ 'disjoint' A & B ]"
  (format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'").
Reserved Notation "F `#` G"
  (at level 48, left associativity, format "F  `#`  G").
Reserved Notation "'`I_' n" (at level 8, n at level 2, format "'`I_' n").

Structure set (T : Type) := mkset {
  set_to_pred : pred T
}.
Arguments set_to_pred : simpl never.

HB.instance Definition _ (T : Type) := Choice.copy (set T) (classicType (set T)).

(* we use fun x => instead of pred to prevent inE from working *)
(* we will then extend inE with in_setE to make this work      *)
Canonical set_predType T := @PredType T (set T) (@set_to_pred T).

Existing Class is_true.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-Corelib.Init.Datatypes.tc-is_true B R :-
  coq.unify-eq B {{ true }} ok,
  R = {{ @erefl bool true }}.
}}.

(* FIXME: Why did someone have the brilliant idea of adding `hnf` in `done`? *)
Existing Class eq.

Elpi Accumulate TC.Solver lp:{{
tc-Corelib.Init.Logic.tc-eq {{ bool }} {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) lp:A) }} {{ true }} R :-
  tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) lp:A) }} R.
}}.

Elpi Accumulate coercion.db lp:{{
coercion _ V {{ prod lp:T lp:U }} {{ prod lp:T' lp:U' }} R :-
  coq.unify-eq V {{ @pair lp:T lp:U lp:X lp:Y }} ok,
  coq.elaborate-skeleton X T' X' ok,
  coq.elaborate-skeleton Y U' Y' ok,
  R = {{ @pair lp:T' lp:U' lp:X' lp:Y' }}.
}}.

Lemma in_setE T (A : set T) x : x \in A = set_to_pred A x.
Proof. by []. Qed.

Definition inE := (inE, in_setE).

Bind Scope classical_set_scope with set.
Local Open Scope classical_set_scope.
Delimit Scope classical_set_scope with classic.

(* memType is the type of elements of a given set. *)
Module MemType.
Record type T (X : set T) := Pack { elt : T; memP : elt \in X }.
Definition pack T X elt eltP := @Pack T X elt eltP.
End MemType.
Notation memType := MemType.type.
Notation memP := MemType.memP.
Canonical MemType.pack.

Elpi Accumulate coercion.db lp:{{

coercion _ X _ {{ @MemType.type lp:E lp:S }} R :-
  coq.elaborate-skeleton X E Y ok,
  coq.typecheck C {{ is_true (@in_mem lp:E lp:Y (@ssrbool.mem lp:E (@set_predType lp:E) lp:S)) }} ok,
  coq.ltac.collect-goals C [G] [], !,
  coq.ltac.open (coq.ltac.call-ltac1 "done_tc") G [],
  R = {{ @MemType.Pack lp:E lp:S lp:Y lp:C }}.

coercion _ X {{ @MemType.type _ _ }} E R :-
  coq.elaborate-skeleton {{ (lp:X.(MemType.elt)) }} E R ok, !.
}}.

Elpi Accumulate TC.Solver lp:{{
:before "0"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X.(MemType.elt) (@ssrbool.mem lp:T (@set_predType lp:T) lp:S) }} R :-
  coq.typecheck X {{ @MemType.type lp:T lp:S }} ok,
  R = {{ lp:X.(MemType.memP) }}.

func reduce term -> term.
reduce T R :-
  coq.reduction.whd-betaiota-deltazeta-for-iota-state T U,
  if (T = U)
    (coq.safe-dest-app U Hd Args,
      not (var Hd),
      if (Hd = global (const HdG)) (coq.env.const-body HdG (some Hd'))
        (Hd = primitive (proj P N),
        coq.primitive.projection-unfolded P PU,
        Hd' = primitive (proj PU N)),
      coq.mk-app Hd' Args V,
      coq.reduction.whd-betaiota-deltazeta-for-iota-state V R,
      not (R = T))
    (R = U).

:after "100"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) lp:S) }} R :- !,
  reduce X X',
  tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X' (@ssrbool.mem lp:T (@set_predType lp:T) lp:S) }} R.
}}.

Coercion memType : set >-> Sortclass.

Module MemType_subType.
Section memType_subType.
Variable (T : Type) (A : set T).

Definition Sub (x : T) : x \in A -> A.
Proof. by move=> xA; exists x. Defined.

Lemma Sub_rect K : (forall x Px, K (@Sub x Px)) -> forall u, K u.
Proof. by move=> KA [] u uA; apply: (KA u). Qed.

Lemma SubK_subproof x Px : MemType.elt (@Sub x Px) = x.
Proof. by []. Qed.

#[export]
HB.instance Definition _ := isSub.Build T (fun x => x \in A) (memType A)
  Sub_rect SubK_subproof.
End memType_subType.

Module Exports. HB.reexport. End Exports.
End MemType_subType.
Export MemType_subType.Exports.

HB.instance Definition _ (T : eqType) (A : set T) := [Equality of A by <:].
HB.instance Definition _ (T : choiceType) (A : set T) := [Choice of A by <:].
HB.instance Definition _ (T : countType) (A : set T) := [Countable of A by <:].
HB.instance Definition _ (T : finType) (A : set T) := [Finite of A by <:].
HB.instance Definition _ d (T : preorderType d) (A : set T) :=
  [SubChoice_isSubPreorder of (@memType T A) by <: with d].
HB.instance Definition _ d (T : porderType d) (A : set T) :=
  [SubChoice_isSubPOrder of (@memType T A) by <: with d].
HB.instance Definition _ d (T : orderType d) (A : set T) :=
  [SubChoice_isSubOrder of A by <: with d].

Notation "[ 'set' x : T | P ]" := (mkset (fun x : T => P)) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P] : classical_set_scope.

Definition range {T rT} (f : T -> rT) :=
  [set y | `[< exists x, f x = y >] ].

Notation "[ 'set' E | x 'in' 'setT' ]" :=
  (range (fun x => E)) : classical_set_scope.
Notation "[ 'set' E | x 'in' A ]" :=
  (range (fun x : A => E)) : classical_set_scope.

Definition range2 {TA TB rT} (f : TA -> TB -> rT) :=
  [set z | `[< exists x y, f x y = z >] ].

Notation "[ 'set' E | x 'in 'setT' & y 'in 'setT' ]" :=
  (range2 (fun x y => E)) : classical_set_scope.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" :=
  (range2 (fun (x : A) (y : B) => E)) : classical_set_scope.

Section basic_definitions.
Context {T rT : Type}.
Implicit Types (A B : set T) (f : T -> rT) (Y : set rT).

Definition preimage f Y : set T := [set t | f t \in Y].

Definition setT := [set _ : T | true].
Definition set0 := [set _ : T | false].
Definition set1 (T' : eqType) (t : T') := [set x : T' | x == t].
Definition setI A B := [set x | (x \in A) && (x \in B)].
Definition setU A B := [set x | (x \in A) || (x \in B)].
Definition nonempty A := exists a, a \in A.
Definition setC A := [set a | a \notin A].
Definition setD A B := setI A (setC B).
Definition setY (A B : set T) := setU (setD A B) (setD B A).
Definition setX T1 T2 (A1 : set T1) (A2 : set T2) := [set z | (z.1 \in A1) && (z.2 \in A2)].
Definition setXR T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :=
  [set z | (z.1 \in A1) && (z.2 \in A2 z.1)].
Definition setXL T1 T2 (A1 : T2 -> set T1) (A2 : set T2) :=
  [set z | (z.1 \in A1 z.2) && (z.2 \in A2)].

Lemma asboolI : injective asbool.
Proof. by move=> P Q /(@asbool_eq_equiv P Q)/propext. Qed.

Lemma in_mkset (P : pred T) x : x \in [set x | P x] = P x.
Proof. by []. Qed.

Definition bigcap T I (F : I -> set T) := [set a | `[< forall i, a \in F i >] ].
Definition bigcup T I  (F : I -> set T) := [set a | `[< exists i, a \in F i >] ].

Definition subset A B := `[< {subset A <= B} >].
Local Notation "A `<=` B" := (subset A B).

Lemma subsetP A B : reflect {subset A <= B} (A `<=` B).
Proof. exact: asboolP. Qed.

Definition disj_set A B := setI A B == set0.

Definition proper A B := (A `<=` B) && ~~ (B `<=` A).

End basic_definitions.
Coercion setT : Sortclass >-> set.

#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setX.")]
Notation setM := setX (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setXR.")]
Notation setMR := setXR (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setXL.")]
Notation setML := setXL (only parsing).
Arguments subsetP {T A B}.

Notation "[ 'set' a ]" := (set1 a) : classical_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)] : classical_set_scope.
Notation "[ 'set' : T ]" := (@setT T) : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" :=
  (setU .. (a1 |` [set a2]) .. [set an]) : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "A `*` B" := (setX A B) : classical_set_scope.
Notation "A .`1" := (range (fst : A -> _)) : classical_set_scope.
Notation "A .`2" := (range (snd : A -> _)) : classical_set_scope.
Notation "A `*`` B" := (setXR A B) : classical_set_scope.
Notation "A ``*` B" := (setXL A B) : classical_set_scope.
Notation "~` A" := (setC A) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a]) : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.
Notation "[ 'disjoint' A & B ]" := (disj_set A B) : classical_set_scope.
Notation "A `+` B" := (setY A B) : classical_set_scope.

Notation "'`I_' n" := [set k | (k < n)%N].

Notation "\bigcup_ ( i : T ) F" :=
  (bigcup (fun i : T => F)) : classical_set_scope.
Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigcup (fun i : @MemType.type _ P => F)) : classical_set_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\bigcup_(i in `I_n) F) : classical_set_scope.
Notation "\bigcup_ ( i >= n ) F" :=
  (\bigcup_(i in [set i | is_true (n <= i)%N]) F) : classical_set_scope.
Notation "\bigcup_ i F" := (\bigcup_(i : _) F) : classical_set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (bigcap (fun i : T => F)) : classical_set_scope.
Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigcap (fun i : @MemType.type _ P => F)) : classical_set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\bigcap_(i in `I_n) F) : classical_set_scope.
Notation "\bigcap_ ( i >= n ) F" :=
  (\bigcap_(i in [set i | is_true (n <= i)%N]) F) : classical_set_scope.
Notation "\bigcap_ i F" := (\bigcap_(i : _) F) : classical_set_scope.

Notation "A `<=` B" := (subset A B) : classical_set_scope.
Notation "A `<` B" := (proper A B) : classical_set_scope.

Notation "A `<=>` B" := ((A `<=` B) && (B `<=` A)) : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) : classical_set_scope.
Notation "f @` A" := (range (f \o (@MemType.elt _ A))) : classical_set_scope.
Notation "A !=set0" := (nonempty A) : classical_set_scope.

Notation "[ 'set`' p ]":= [set x | x \in p] : classical_set_scope.
Notation pred_set := (fun i => [set` i]).

Notation "`[ a , b ]" :=
  [set` Interval (BLeft a) (BRight b)] : classical_set_scope.
Notation "`] a , b ]" :=
  [set` Interval (BRight a) (BRight b)] : classical_set_scope.
Notation "`[ a , b [" :=
  [set` Interval (BLeft a) (BLeft b)] : classical_set_scope.
Notation "`] a , b [" :=
  [set` Interval (BRight a) (BLeft b)] : classical_set_scope.
Notation "`] '-oo' , b ]" :=
  [set` Interval -oo%O (BRight b)] : classical_set_scope.
Notation "`] '-oo' , b [" :=
  [set` Interval -oo%O (BLeft b)] : classical_set_scope.
Notation "`[ a , '+oo' [" :=
  [set` Interval (BLeft a) +oo%O] : classical_set_scope.
Notation "`] a , '+oo' [" :=
  [set` Interval (BRight a) +oo%O] : classical_set_scope.
Notation "`] -oo , '+oo' [" :=
  [set` Interval -oo%O +oo%O] : classical_set_scope.

Lemma eqEsubset (T : Type) (A B : set T) : (A == B) = (A `<=>` B).
Proof.
apply/idP/andP => [/eqP ->|[]]; first by split; apply/subsetP.
case: A B => A [] B /subsetP AB /subsetP BA; apply/eqP.
by congr mkset; apply: funext => x; apply/idP/idP => [/AB|/BA].
Qed.

Lemma seteqP (T : Type) (A B : set T) :
  reflect (forall x, x \in A = (x \in B)) (A == B).
Proof.
rewrite eqEsubset.
apply/(iffP andP) => [[] /subsetP AB /subsetP BA x|AB].
  by apply/idP/idP => [/AB|/BA].
by split; apply/subsetP => x; rewrite (AB x).
Qed.

Lemma in_setT (T : Type) (x : T) : x \in [set: T]. Proof. by []. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) (@setT lp:T')) }} R :-
  coq.unify-eq T T' ok,
  R = {{ @in_setT lp:T lp:X }}.
}}.

Lemma in_set0 (T : Type) (x : T) : (x \in set0) = false.
Proof. by []. Qed.

Lemma in_set1 (T : eqType) (x y : T) : (y \in [set x]) = (y == x).
Proof. by []. Qed.

Lemma mem_set1 (T : eqType) (x : T) : x \in [set x].
Proof. exact: eqxx. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) (@set1 lp:T' lp:X')) }} R :-
  coq.unify-eq T {{ lp:T'.(Equality.sort) }} ok,
  coq.unify-eq X X' ok,
  R = {{ @mem_set1 lp:T' lp:X }}.
}}.

Lemma in_setC (T : Type) (x : T) A : (x \in ~` A) = (x \notin A).
Proof. by []. Qed.

Lemma in_setI (T : Type) (x : T) A B : (x \in A `&` B) = (x \in A) && (x \in B).
Proof. by []. Qed.

Lemma mem_setI (T : Type) (A B : set T) (x : T) : x \in A -> x \in B -> x \in (A `&` B).
Proof. by move=> xA xB; apply/andP. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) (@setI lp:T' lp:A lp:B)) }} R :-
  coq.unify-eq T T' ok,
  tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) lp:A) }} RA,
  tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) lp:B) }} RB,
  R = {{ @mem_setI lp:T' lp:A lp:B lp:X lp:RA lp:RB }}.
}}.

Lemma in_setD (T : Type) (x : T) A B : (x \in A `\` B) = (x \in A) && (x \notin B).
Proof. by []. Qed.

Lemma in_setU (T : Type) (x : T) A B : (x \in A `|` B) = (x \in A) || (x \in B).
Proof. by []. Qed.

Lemma mem_setUl (T : Type) (A B : set T) (x : A) : mem (A `|` B) x.
Proof. by apply/orP; left. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) (@setU lp:T' lp:A lp:B)) }} R :-
  coq.unify-eq T T' ok,
  coq.unify-eq X {{ lp:X'.(MemType.elt) }} ok,
  coq.typecheck X' {{ @MemType.type lp:T lp:A }} ok,
  coq.ltac.collect-goals X' Gs _,
  coq.ltac.all (coq.ltac.open (coq.ltac.call-ltac1 "done_tc")) Gs [],
  R = {{ @mem_setUl lp:T lp:A lp:B lp:X' }}.
}}.

Lemma mem_setUr (T : Type) (A B : set T) (x : B) : mem (A `|` B) x.
Proof. by apply/orP; right. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) (@setU lp:T' lp:A lp:B)) }} R :-
  coq.unify-eq T T' ok,
  coq.unify-eq X {{ lp:X'.(MemType.elt) }} ok,
  coq.typecheck X' {{ @MemType.type lp:T lp:B }} ok,
  coq.ltac.collect-goals X' Gs _,
  coq.ltac.all (coq.ltac.open (coq.ltac.call-ltac1 "done_tc")) Gs [],
  R = {{ @mem_setUr lp:T lp:A lp:B lp:X' }}.
}}.

Lemma in_setX (T T' : Type) A B (x : T * T') : (x \in A `*` B) = (x.1 \in A) && (x.2 \in B).
Proof. by []. Qed.

Lemma mem_setX (T T' : Type) A B (x : T * T') : x.1 \in A -> x.2 \in B -> x \in (A `*` B).
Proof. by move=> xA xB; apply/andP. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T' lp:X (@ssrbool.mem lp:T' (@set_predType lp:T') (@setX lp:T lp:U lp:A lp:B)) }} R :-
  coq.unify-eq T' {{ prod lp:T lp:U }} ok,
  tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T (@fst lp:T lp:U lp:X) (@ssrbool.mem lp:T (@set_predType lp:T) lp:A) }} RA,
  tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:U (@snd lp:T lp:U lp:X) (@ssrbool.mem lp:U (@set_predType lp:U) lp:B) }} RB,
  R = {{ @mem_setX lp:T lp:U lp:A lp:B lp:X lp:RA lp:RB }}.
}}.

Lemma in_preimage (T T' : Type) (f : T -> T') (A : set T') (x : T) :
  x \in f @^-1` A = (f x \in A).
Proof. by []. Qed.

Lemma mem_preimage (T T' : Type) (f : T -> T') (A : set T') (x : T) :
  x \in f @^-1` A -> (f x \in A).
Proof. by []. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:T lp:X (@ssrbool.mem lp:T (@set_predType lp:T) (@preimage lp:T' lp:U lp:F lp:A)) }} R :-
  coq.unify-eq T T' ok,
  tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:U (lp:F lp:X) (@ssrbool.mem lp:U (@set_predType lp:U) lp:A) }} R',
  R = {{ @mem_preimage lp:T lp:U lp:F lp:A lp:X lp:R' }}.
}}.

Lemma rangeP (T T' : Type) (f : T -> T') (y : T') :
  reflect (exists x, f x = y) (y \in range f).
Proof. exact: asboolP. Qed.

Lemma imageP (T T' : Type) (f : T -> T') A y :
  reflect (exists x, (x \in A) /\ f x = y) (y \in f @` A).
Proof.
apply: (iffP idP) => [/rangeP[] x <-|[] x [] xA <-]; first by exists x; split.
by apply/rangeP; exists x.
Qed.

Lemma range_f (T T' : Type) (f : T -> T') (x : T) : f x \in range f.
Proof. by apply/rangeP; exists x. Qed.

Elpi Accumulate TC.Solver lp:{{
:after "1"
tc-Corelib.Init.Datatypes.tc-is_true {{ @in_mem lp:RT lp:Y (@ssrbool.mem lp:RT (@set_predType lp:RT) (@range lp:T lp:RT' lp:F)) }} R :-
  coq.unify-eq RT RT' ok,
  coq.unify-eq Y {{ lp:F lp:X }} ok,
  coq.elaborate-skeleton X T X' ok,
  R = {{ @range_f lp:T lp:RT lp:F lp:X' }}.
}}.

Lemma image_f (T T' : Type) (f : T -> T') A x :
  x \in A -> f x \in f @` A.
Proof. by []. Qed.

Section basic_lemmas.
Variables (T T' : Type).
Implicit Types (A B C D : set T) (x y : T).

Lemma in_setY A B x : (x \in A `+` B) = ((x \in A) (+) (x \in B)).
Proof.
rewrite [LHS]in_setU !in_setD.
case: (x \in A) => /=; last exact: andbT.
by rewrite andbF orbF.
Qed.

Lemma in_bigcupP I (F : I -> set T) x :
  reflect (exists i, x \in F i) (x \in \bigcup_i F i).
Proof. exact: asboolP. Qed.

Lemma in_bigcapP I (F : I -> set T) x :
  reflect (forall i, x \in F i) (x \in \bigcap_i F i).
Proof. exact: asboolP. Qed.

Lemma set_valP A (x : A) : val x \in A.
Proof. by []. Qed.

Lemma set_true  : [set` predT] = setT :> set T.
Proof. exact/eqP/seteqP. Qed.

Lemma set_false : [set` pred0] = set0 :> set T.
Proof. exact/eqP/seteqP. Qed.

Lemma set_predC (P : {pred T}) : [set` predC P] = ~` [set` P].
Proof. exact/eqP/seteqP. Qed.

Lemma set_andb (P Q : {pred T}) : [set` predI P Q] = [set` P] `&` [set` Q].
Proof. exact/eqP/seteqP. Qed.

Lemma set_orb (P Q : {pred T}) : [set` predU P Q] = [set` P] `|` [set` Q].
Proof. exact/eqP/seteqP. Qed.

Lemma fun_true : [set x | true] = setT :> set T.
Proof. exact/eqP/seteqP. Qed.

Lemma fun_false : [set x | false] = set0 :> set T.
Proof. exact/eqP/seteqP. Qed.

Lemma set_mem_set (A : set T) : [set` A] = A.
Proof. exact/eqP/seteqP. Qed.

(* TOTHINK: Is this useless now? *)
Lemma mem_setE (P : pred T) : ssrbool.mem [set` P] = ssrbool.mem P.
Proof. by []. Qed.

Lemma subset_def A B : (A `<=` B) = (A `&` B == A).
Proof.
apply/subsetP/idP => [AB|/eqP <- x]; last by rewrite in_setI => /andP[].
by apply/seteqP => x; rewrite in_setI; apply/andb_idr => /AB.
Qed.

Lemma proper_def A B : A `<` B = (B != A) && (A `<=` B).
Proof. by rewrite /proper eqEsubset negb_and andb_orl andNb orbF andbC. Qed.

Lemma setIC : commutative (@setI T).
Proof. by move=> ??; apply/eqP/seteqP => x; rewrite !in_setI andbC. Qed.

Lemma setUC : commutative (@setU T).
Proof. by move=> ??; apply/eqP/seteqP => x; rewrite !in_setU orbC. Qed.

Lemma setIA : associative (@setI T).
Proof. by move=> ???; apply/eqP/seteqP => x; rewrite !in_setI andbA. Qed.

Lemma setUA : associative (@setU T).
Proof. by move=> ???; apply/eqP/seteqP => x; rewrite !in_setU orbA. Qed.

Lemma setUKI A B : B `&` (B `|` A) = B.
Proof. by apply/eqP/seteqP => x; rewrite in_setI in_setU orbC orKb. Qed.

Lemma setIKU A B : B `|` (B `&` A) = B.
Proof. by apply/eqP/seteqP => x; rewrite in_setU in_setI andbC andKb. Qed.

Lemma setIUl : left_distributive (@setI T) (@setU T).
Proof.
by move=> A B C; apply/eqP/seteqP => x; rewrite !(in_setU, in_setI) andb_orl.
Qed.

Lemma setIid : idempotent_op (@setI T).
Proof. by move=> A; apply/eqP/seteqP => ?; rewrite !in_setI andbb. Qed.

Fact set_display : Order.disp_t. Proof. by []. Qed.

HB.instance Definition _ :=
  Order.isMeetJoinDistrLattice.Build set_display (set T)
    subset_def proper_def setIC setUC setIA setUA 
    setUKI setIKU setIUl setIid.

Lemma subset_refl A : A `<=` A.
Proof. exact: (@Order.POrderTheory.le_refl _ (set T)). Qed.

Lemma subset_trans B A C : A `<=` B -> B `<=` C -> A `<=` C.
Proof. exact: (@Order.POrderTheory.le_trans _ (set T)). Qed.

Lemma properxx A : ~ A `<` A.
Proof. by rewrite [_ `<` _](@Order.POrderTheory.ltxx _ (set T)). Qed.

Lemma properW A B : A `<` B -> A `<=` B.
Proof. exact: (@Order.POrderTheory.ltW _ (set T)). Qed.

Lemma setIS C A B : A `<=` B -> C `&` A `<=` C `&` B.
Proof. exact: (@Order.MeetTheory.leI2 _ (set T)). Qed.

Lemma setSI C A B : A `<=` B -> A `&` C `<=` B `&` C.
Proof. by move=> ?; apply: (@Order.MeetTheory.leI2 _ (set T)). Qed.

Lemma setISS A B C D : A `<=` C -> B `<=` D -> A `&` B `<=` C `&` D.
Proof. exact: (@Order.MeetTheory.leI2 _ (set T)). Qed.

Lemma setICA : left_commutative (@setI T).
Proof. exact: (@Order.MeetTheory.meetCA _ (set T)). Qed.

Lemma setIAC : right_commutative (@setI T).
Proof. exact: (@Order.MeetTheory.meetAC _ (set T)). Qed.

Lemma setIACA : @interchange (set T) setI setI.
Proof. exact: (@Order.MeetTheory.meetACA _ (set T)). Qed.

Lemma setIIl A B C : A `&` B `&` C = (A `&` C) `&` (B `&` C).
Proof. by rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr A B C : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
Proof. by rewrite !(setIC A) setIIl. Qed.

Lemma setUS C A B : A `<=` B -> C `|` A `<=` C `|` B.
Proof. exact: (@Order.JoinTheory.leU2 _ (set T)). Qed.

Lemma setSU C A B : A `<=` B -> A `|` C `<=` B `|` C.
Proof. by move=> AB; apply: (@Order.JoinTheory.leU2 _ (set T)). Qed.

Lemma setUSS A B C D : A `<=` C -> B `<=` D -> A `|` B `<=` C `|` D.
Proof. exact: (@Order.JoinTheory.leU2 _ (set T)). Qed.

Lemma setUCA : left_commutative (@setU T).
Proof. exact: (@Order.JoinTheory.joinCA _ (set T)). Qed.

Lemma setUAC : right_commutative (@setU T).
Proof. exact: (@Order.JoinTheory.joinAC _ (set T)). Qed.

Lemma setUACA : @interchange (set T) setU setU.
Proof. exact: (@Order.JoinTheory.joinACA _ (set T)). Qed.

Lemma setUid : idempotent_op (@setU T).
Proof. exact: (@Order.JoinTheory.joinxx _ (set T)). Qed.

Lemma setUUl A B C : A `|` B `|` C = (A `|` C) `|` (B `|` C).
Proof. by rewrite setUA !(setUAC _ C) -(setUA _ C) setUid. Qed.

Lemma setUUr A B C : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
Proof. by rewrite !(setUC A) setUUl. Qed.

Lemma subsetUl A B : A `<=` A `|` B.
Proof. exact: (@Order.JoinTheory.leUl _ (set T)). Qed.

Lemma subsetUr A B : B `<=` A `|` B.
Proof. exact: (@Order.JoinTheory.leUr _ (set T)). Qed.

Lemma subUset A B C : (B `|` C `<=` A) = ((B `<=` A) && (C `<=` A)).
Proof. exact: (@Order.JoinTheory.leUx _ (set T)). Qed.

Lemma subIsetl A B : A `&` B `<=` A.
Proof. exact: (@Order.MeetTheory.leIl _ (set T)). Qed.

Lemma subIsetr A B : A `&` B `<=` B.
Proof. exact: (@Order.MeetTheory.leIr _ (set T)). Qed.

Lemma subIset A B C : (A `<=` C) || (B `<=` C) -> A `&` B `<=` C.
Proof. exact: (@Order.MeetTheory.leIx2 _ (set T)). Qed.

Lemma subsetI A B C : (A `<=` B `&` C) = ((A `<=` B) && (A `<=` C)).
Proof. exact: (@Order.MeetTheory.lexI _ (set T)). Qed.

Lemma setIidPl A B : reflect (A `&` B = A) (A `<=` B).
Proof. exact: (@Order.MeetTheory.meet_idPl _ (set T)). Qed.

Lemma setIidPr A B : reflect (A `&` B = B) (B `<=` A).
Proof. exact: (@Order.MeetTheory.meet_idPr _ (set T)). Qed.

Lemma setIidl A B : A `<=` B -> A `&` B = A.
Proof. by move=> /setIidPl. Qed.

Lemma setIidr A B : B `<=` A -> A `&` B = B.
Proof. by move=> /setIidPr. Qed.

Lemma setUidPl A B : reflect (A `|` B = A) (B `<=` A).
Proof. exact: (@Order.JoinTheory.join_idPl _ (set T)). Qed.

Lemma setUidPr A B : reflect (A `|` B = B) (A `<=` B).
Proof. exact: (@Order.JoinTheory.join_idPr _ (set T)). Qed.

Lemma setUidl A B : B `<=` A -> A `|` B = A.
Proof. by move=> /setUidPl. Qed.

Lemma setUidr A B : A `<=` B -> A `|` B = B.
Proof. by move=> /setUidPr. Qed.

Lemma subsetW A B : A = B -> A `<=` B.
Proof. by move=> ->; apply: subset_refl. Qed.

Definition subsetCW A B : A = B -> B `<=` A := (@subsetW B A) \o esym.

Lemma setIUr : right_distributive (@setI T) (@setU T).
Proof. exact: (@Order.DistrLatticeTheory.meetUr _ (set T)). Qed.

Lemma setUIl : left_distributive (@setU T) (@setI T).
Proof. exact: (@Order.DistrLatticeTheory.joinIl _ (set T)). Qed.

Lemma setUIr : right_distributive (@setU T) (@setI T).
Proof. exact: (@Order.DistrLatticeTheory.joinIr _ (set T)). Qed.

Lemma setUK A B : (A `|` B) `&` A = A.
Proof. exact: (@Order.LatticeTheory.joinIKC _ (set T)). Qed.

Lemma setKU A B : A `&` (B `|` A) = A.
Proof. exact: (@Order.LatticeTheory.joinKIC _ (set T)). Qed.

Lemma setIK A B : (A `&` B) `|` A = A.
Proof. exact: (@Order.LatticeTheory.meetUKC _ (set T)). Qed.

Lemma setKI A B : A `|` (B `&` A) = A.
Proof. exact: (@Order.LatticeTheory.meetKUC _ (set T)). Qed.

Lemma sub0set A : (set0 `<=` A).
Proof. by apply/subsetP => x; rewrite in_set0. Qed.

Lemma subsetT A : (A `<=` setT).
Proof. by apply/subsetP => x; rewrite in_setT. Qed.

#[export]
HB.instance Definition _ := Order.hasBottom.Build set_display (set T) sub0set.

#[export]
HB.instance Definition _ := Order.hasTop.Build set_display (set T) subsetT.

Lemma setTI : left_id setT (@setI T).
Proof. exact: (@Order.TMeetTheory.meet1x _ (set T)). Qed.

Lemma setIT : right_id setT (@setI T).
Proof. exact: (@Order.TMeetTheory.meetx1 _ (set T)). Qed.

Lemma set0I : left_zero set0 (@setI T).
Proof. exact: (@Order.BMeetTheory.meet0x _ (set T)). Qed.

Lemma setI0 : right_zero set0 (@setI T).
Proof. exact: (@Order.BMeetTheory.meetx0 _ (set T)). Qed.

Lemma setTU : left_zero setT (@setU T).
Proof. exact: (@Order.TJoinTheory.join1x _ (set T)). Qed.

Lemma setUT : right_zero setT (@setU T).
Proof. exact: (@Order.TJoinTheory.joinx1 _ (set T)). Qed.

Lemma set0U : left_id set0 (@setU T).
Proof. exact: (@Order.BJoinTheory.join0x _ (set T)). Qed.

Lemma setU0 : right_id set0 (@setU T).
Proof. exact: (@Order.BJoinTheory.joinx0 _ (set T)). Qed.

Lemma subset0 A : (A `<=` set0) = (A == set0).
Proof. exact: (@Order.BPOrderTheory.lex0 _ (set T)). Qed.

Lemma subTset A : (setT `<=` A) = (A == setT).
Proof. exact: (@Order.TPOrderTheory.le1x _ (set T)). Qed.

Lemma setTPn A : reflect (exists t, t \notin A) (A != setT).
Proof.
apply: (iffP idP) => [|[t]]; last first.
  by apply: contraNN => /eqP ->; rewrite in_setT.
rewrite -subTset => /negP.
apply: contra_notP => /forallNP AT.
apply/subsetP => x _.
by move: (AT x) => /negP; rewrite negbK.
Qed.
#[deprecated(note="Use setTPn instead")]
Notation setTP := setTPn (only parsing).

Lemma setICr : right_inverse set0 setC (@setI T).
Proof.
move=> A; apply/eqP; rewrite -subset0.
by apply/subsetP => x; rewrite in_setI in_setC andbN.
Qed.

Lemma subKI A B : B `&` (A `\` B) = set0.
Proof. by rewrite setICA setICr setI0. Qed.

Lemma setUCr : right_inverse setT setC (@setU T).
Proof.
move=> A; apply/eqP; rewrite -subTset.
by apply/subsetP => x _; rewrite in_setU in_setC orbN.
Qed.

Lemma joinIB A B : (A `&` B) `|` A `\` B = A.
Proof. by rewrite -setIUr setUCr setIT. Qed.

#[export]
HB.instance Definition _ :=
  Order.hasRelativeComplement.Build set_display (set T) subKI joinIB.

Lemma setTD A : setT `\` A = ~` A.
Proof. exact: setTI. Qed.

#[export]
HB.instance Definition _ :=
  Order.CBDistrLattice_hasComplement.Build set_display (set T)
  (fun A => esym (setTD A)).

Lemma setC0 : ~` set0 = setT :> set T.
Proof. exact: (@Order.CTBDistrLatticeTheory.compl0 _ (set T)). Qed.

Lemma setCK : involutive (@setC T).
Proof. exact: (@Order.CTBDistrLatticeTheory.complK _ (set T)). Qed.

Lemma setCT : ~` setT = set0 :> set T.
Proof. exact: (@Order.CTBDistrLatticeTheory.compl1 _ (set T)). Qed.

Definition setC_inj := can_inj setCK.

Lemma setICl : left_inverse set0 setC (@setI T).
Proof. exact: (@Order.CTBDistrLatticeTheory.meetCx _ (set T)). Qed.

Lemma setUCl : left_inverse setT setC (@setU T).
Proof. exact: (@Order.CTBDistrLatticeTheory.joinCx _ (set T)). Qed.

Lemma setU_id2r C A B :
  (forall (x : ~` B), val x \in A = (val x \in C)) -> (A `|` B) = (C `|` B).
Proof.
move=> AC; apply/eqP/seteqP => t.
have: t \in setT by exact: in_mkset.
rewrite -(setUCr B) !in_setU => /orP.
case=> [->|tB]; first by rewrite !orbT.
by rewrite (AC t).
Qed.

Lemma setDE A B : A `\` B = A `&` ~` B. Proof. by []. Qed.

Lemma setDUK A B : A `<=` B -> A `|` (B `\` A) = B.
Proof.
by rewrite [LHS](@Order.CBDistrLatticeTheory.diffKU _ (set T)) => /setUidr.
Qed.

Lemma setDKU A B : A `<=` B -> (B `\` A) `|` A = B.
Proof. by move=> /setDUK; rewrite setUC. Qed.

Lemma setDU A B C : A `<=` B -> B `<=` C -> C `\` A = (C `\` B) `|` (B `\` A).
Proof.
move=> /subsetP AB /subsetP BC; apply/eqP/seteqP => x.
rewrite in_setU !in_setD.
case /boolP: (x \in A) => [/AB /[dup] /BC -> -> //|_]/=.
by case /boolP: (x \in B) => [/BC -> //|_]/=; rewrite orbF.
Qed.

Lemma setDv A : A `\` A = set0.
Proof. exact: (@Order.CBDistrLatticeTheory.diffxx _ (set T)). Qed.

Lemma setUv A : A `|` ~` A = setT.
Proof. exact: (@Order.CTBDistrLatticeTheory.joinxC _ (set T)). Qed.

Lemma setvU A : ~` A `|` A = setT.
Proof. exact: (@Order.CTBDistrLatticeTheory.joinCx _ (set T)). Qed.

(* TODO: find the corresponding lemmas from order.v *)
Lemma setUCK A B : (A `|` B) `|` ~` B = setT.
Proof. by rewrite -setUA setUv setUT. Qed.

Lemma setUKC A B : ~` A `|` (A `|` B) = setT.
Proof. by rewrite setUA setvU setTU. Qed.

Lemma setICK A B : (A `&` B) `&` ~` B = set0.
Proof. by rewrite -setIA setICr setI0. Qed.

Lemma setIKC A B : ~` A `&` (A `&` B) = set0.
Proof. by rewrite setIA setICl set0I. Qed.

Lemma setDIK A B : A `&` (B `\` A) = set0.
Proof. by rewrite setDE setICA -setDE setDv setI0. Qed.

Lemma setDKI A B : (B `\` A) `&` A = set0.
Proof. by rewrite setIC setDIK. Qed.

Lemma disj_set2E A B : [disjoint A & B] = (A `&` B == set0).
Proof. by []. Qed.

Lemma disj_set2P A B : reflect (A `&` B = set0) [disjoint A & B]%classic.
Proof. exact/eqP. Qed.

Lemma disj_setPS A B : [disjoint A & B]%classic = (A `&` B `<=` set0).
Proof. by rewrite subset0. Qed.

Lemma disj_set_sym A B : [disjoint B & A] = [disjoint A & B].
Proof. by rewrite !disj_setPS setIC. Qed.

Lemma disj_setPCl A B : [disjoint A & ~` B]%classic = (A `<=` B).
Proof.
rewrite disj_setPS; apply/subsetP/subsetP => AB a; last first.
  by rewrite in_setI in_setC => /andP[] /AB + /negP.
move=> aA; apply: contrapT => /negP ?.
suff: (a \in set0) by rewrite in_set0.
by apply: AB; rewrite in_setI in_setC aA.
Qed.

Lemma disj_setPCr A B : [disjoint ~` B & A]%classic = (A `<=` B).
Proof. by rewrite disj_set_sym; apply: disj_setPCl. Qed.

Lemma disj_setPLR A B : [disjoint A & B]%classic = (A `<=` ~` B).
Proof. by rewrite -disj_setPCl setCK. Qed.

Lemma disj_setPRL A B : [disjoint A & B]%classic = (B `<=` ~` A).
Proof. by rewrite -disj_setPCr setCK. Qed.

Lemma subsets_disjoint A B : reflect (A `&` ~` B = set0) (A `<=` B).
Proof. by rewrite -disj_setPCl; apply: eqP. Qed.

Lemma disjoints_subset A B : reflect (A `&` B = set0) (A `<=` ~` B).
Proof. by rewrite -disj_setPLR; apply: eqP. Qed.

Lemma setSD C A B : A `<=` B -> A `\` C `<=` B `\` C.
Proof. exact: (@Order.CBDistrLatticeTheory.leBl _ (set T)). Qed.

Lemma set0P A : reflect (A !=set0) (A != set0).
Proof.
apply: (iffP idP); last first.
  by move=> [] x xA; apply/eqP => A0; rewrite A0 in_set0 in xA.
rewrite -subset0 => /(negPP subsetP)/not_forallP/contrapT[] x.
by rewrite in_set0 falseE => /contrapT xA; exists x.
Qed.

Lemma setF_eq0 : (T -> False) -> all_equal_to (set0 : set T).
Proof. by move=> TF A; apply: contrapT => /eqP/set0P[] x _; have := TF x. Qed.

Lemma subset_nonempty A B : A `<=` B -> A !=set0 -> B !=set0.
Proof. by move=> /subsetP sAB [x Ax]; exists x; apply: sAB. Qed.

Lemma subsetC A B : ~` B `<=` ~` A = (A `<=` B).
Proof. exact: (@Order.CTBDistrLatticeTheory.leC _ (set T)). Qed.


Lemma subsetCl A B : ~` A `<=` B = (~` B `<=` A).
Proof. exact: (@Order.CTBDistrLatticeTheory.leCx _ (set T)). Qed.

Lemma subsetCr A B : A `<=` ~` B = (B `<=` ~` A).
Proof. exact: (@Order.CTBDistrLatticeTheory.lexC _ (set T)). Qed.

Lemma setDidPl A B : reflect (A `\` B = A) [disjoint A & B]%classic.
Proof. rewrite disj_setPLR; exact: setIidPl. Qed.

Lemma subDsetl A B : A `\` B `<=` A.
Proof. exact: (@Order.CBDistrLatticeTheory.leBx _ (set T)). Qed.

Lemma subDsetr A B : A `\` B `<=` ~` B.
Proof. exact: (@Order.CTBDistrLatticeTheory.leBC _ (set T)). Qed.

Lemma subsetI_neq0 A B C D :
  A `<=` B -> C `<=` D -> A `&` C !=set0 -> B `&` D !=set0.
Proof.
move=> /subsetP AB /subsetP CD [] x.
by rewrite in_setI => /andP[] /AB Bx /CD Dx; exists x.
Qed.

Lemma subsetI_eq0 A B C D :
  A `<=` B -> C `<=` D -> B `&` D = set0 -> A `&` C = set0.
Proof.
by move=> AB /(subsetI_neq0 AB) H; apply: contra_eq => /set0P /H /set0P.
Qed.

(* TOTHINK: Should we remove one of setD_eq0 or subsets_disjoint? *)
Lemma setD_eq0 A B : reflect (A `\` B = set0) (A `<=` B).
Proof. exact: subsets_disjoint. Qed.

Lemma properEneq A B : (A `<` B) = ((A != B) && (A `<=` B)).
Proof. by rewrite eq_sym; apply: proper_def. Qed.

Lemma nonsubset A B : ~ (A `<=` B) -> A `&` ~` B !=set0.
Proof. by move=> /negP/setD_eq0/eqP/set0P. Qed.

Lemma setU_eq0 A B : (A `|` B == set0) = ((A == set0) && (B == set0)).
Proof. by rewrite -!subset0 subUset. Qed.

(* TOTHINK: Wat? *)
Lemma setCS A B : (~` A `<=` ~` B) = (B `<=` A).
Proof. exact: subsetC. Qed.

(* TODO: find the lemmas in order.v *)
Lemma setDT A : A `\` setT = set0.
Proof. by rewrite setDE setCT setI0. Qed.

Lemma set0D A : set0 `\` A = set0.
Proof. by rewrite setDE set0I. Qed.

Lemma setD0 A : A `\` set0 = A.
Proof. by rewrite setDE setC0 setIT. Qed.

Lemma setDS C A B : A `<=` B -> C `\` B `<=` C `\` A.
Proof. by rewrite !setDE -setCS; apply: setIS. Qed.

Lemma setDSS A B C D : A `<=` C -> D `<=` B -> A `\` B `<=` C `\` D.
Proof. exact: (@Order.CBDistrLatticeTheory.leB2 _ (set T)). Qed.

Lemma setCU A B : ~`(A `|` B) = ~` A `&` ~` B.
Proof. exact: (@Order.CTBDistrLatticeTheory.complU _ (set T)). Qed.

Lemma setCI A B : ~` (A `&` B) = ~` A `|` ~` B.
Proof. exact: (@Order.CTBDistrLatticeTheory.complI _ (set T)). Qed.

Lemma setCD A B : ~` (A `\` B) = ~` A `|` B.
Proof. exact: (@Order.CTBDistrLatticeTheory.complB _ (set T)). Qed.

Lemma setDUl : left_distributive setD (@setU T).
Proof. exact: (@Order.CBDistrLatticeTheory.diffUx _ (set T)). Qed.

Lemma setDUr A B C : A `\` (B `|` C) = (A `\` B) `&` (A `\` C).
Proof. exact: (@Order.CBDistrLatticeTheory.diffxU _ (set T)). Qed.

Lemma setUKD A B : A `&` B `<=` set0 -> (A `|` B) `\` A = B.
Proof.
by rewrite subset0 setIC => AB0; rewrite setDUl setDv set0U; apply/setDidPl.
Qed.

(*TODO: find the lemmas in order.v *)

Lemma setUDK A B : A `&` B `<=` set0 -> (B `|` A) `\` A = B.
Proof. by move=> *; rewrite setUC setUKD. Qed.

Lemma setIDA A B C : A `&` (B `\` C) = (A `&` B) `\` C.
Proof. by rewrite !setDE setIA. Qed.

Lemma setIDAC A B C : (A `\` B) `&` C = A `&` (C `\` B).
Proof. by rewrite setIC !setIDA setIC. Qed.

Lemma setDD A B : A `\` (A `\` B) = A `&` B.
Proof. by rewrite 2!setDE setCI setCK setIUr setICr set0U. Qed.

Lemma setDDl A B C : (A `\` B) `\` C = A `\` (B `|` C).
Proof. by rewrite !setDE setCU setIA. Qed.

Lemma setDDr A B C : A `\` (B `\` C) = (A `\` B) `|` (A `&` C).
Proof. by rewrite !setDE setCI setIUr setCK. Qed.

Lemma setDIl A B C : A `&` B `\` C = (A `\` C) `&` (B `\` C).
Proof. by rewrite /setD setICA -!setIA setIid setICA. Qed.

Lemma setDIr A B C : A `\` B `&` C = (A `\` B) `|` (A `\` C).
Proof. by rewrite /setD setCI setIUr. Qed.

Lemma setUIDK A B : (A `&` B) `|` A `\` B = A.
Proof. by rewrite setUC -setDDr setDv setD0. Qed.

Lemma setDUD A B C : (A `|` B) `\` C = A `\` C `|` B `\` C.
Proof. exact: (@Order.CBDistrLatticeTheory.diffUx _ (set T)). Qed.

Lemma setX0 A : A `*` set0 = set0 :> set (T * T').
Proof. by apply/eqP/seteqP => -[t u]; rewrite in_setX/= andbF. Qed.

Lemma set0X (A : set T') : set0 `*` A = set0 :> set (T * T').
Proof. by apply/eqP/seteqP => -[t u]. Qed.

Lemma setXTT  : setT `*` setT = setT :> set (T * T').
Proof. by apply/eqP/seteqP => -[t u]. Qed.

Lemma setXT A : A `*` @setT T' = fst @^-1` A.
Proof. by apply/eqP/seteqP => -[t u]; rewrite in_setX/= andbT. Qed.

Lemma setTX (B : set T') : @setT T `*` B = snd @^-1` B.
Proof. by apply/eqP/seteqP => -[t u]. Qed.

Lemma setXI (X : set T) (X' : set T') (Y : set T) (Y' : set T') :
  (X `&` Y) `*` (X' `&` Y') = X `*` X' `&` Y `*` Y'.
Proof. by apply/eqP/seteqP => x; rewrite in_setX andbACA. Qed.

Lemma setSX (C D : set T) (A B : set T') :
  A `<=` B -> C `<=` D -> C `*` A `<=` D `*` B.
Proof.
move=> /subsetP AB /subsetP CD; apply/subsetP => x.
by rewrite !in_setX => /andP[] /CD -> /AB.
Qed.

(* TODO
Lemma setX_bigcupr I (F : I -> set T') (P : set I) (A : set T) :
  A `*` \bigcup_(i in P) F i = \bigcup_(i in P) (A `*` F i).
Proof.
apply/eqP/seteqP => -[x y]; rewrite in_setX/=; apply/eqP.
apply/(andPP idP in_bigcupP)/in_bigcupP.
Search reflect andb.
apply/andP/asboolP => [[] xA /asboolP[] z yz|[] z].
  by exists z; rewrite in_setX/= yz andbT.
rewrite in_setX/= => /andP[] => xA yz; split=> //.
by apply/asboolP; exists z.
Qed.

Lemma setX_bigcupl T1 T2 I (F : I -> set T2) (P : set I) (A : set T1) :
  \bigcup_(i in P) F i `*` A = \bigcup_(i in P) (F i `*` A).
Proof.
apply/eqP/seteqP => -[x y]; rewrite in_setX/= !mem_mkset; apply/eqP.
apply/andP/asboolP => [[] /asboolP[] z yz xA|[] z].
  by exists z; rewrite in_setX/= yz.
rewrite in_setX/= => /andP[] => yz xA; split=> //.
by apply/asboolP; exists z.
Qed.

Lemma bigcupX1l T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :
  (\bigcup_(i in A1) ([set (val i)] `*` A2 i)) = (A1 `*`` A2).
Proof.
apply/eqP/seteqP.
by apply/predeqP => -[i j]; split=> [[? ? [/= -> //]]|[]]; exists i. Qed.

Lemma bigcupX1r T1 T2 (A1 : T2 -> set T1) (A2 : set T2) :
  \bigcup_(i in A2) (A1 i `*` [set i]) = A1 ``*` A2.
Proof. by apply/predeqP => -[i j]; split=> [[? ? [? /= -> //]]|[]]; exists j. Qed.
 *)

Lemma setY0 : right_id set0 (@setY T).
Proof. by move=> A; rewrite /setY setD0 set0D setU0. Qed.

Lemma set0Y : left_id set0 (@setY T).
Proof. by move=> A; rewrite /setY set0D setD0 set0U. Qed.

Lemma setYK (A : set T) : A `+` A = set0.
Proof. by rewrite /setY setDv setU0. Qed.

Lemma setYC : commutative (@setY T).
Proof. by move=> A B; rewrite /setY setUC. Qed.

Lemma setYTC A : A `+` [set: T] = ~` A.
Proof. by rewrite /setY setDT set0U setTD. Qed.

Lemma setTYC A : [set: T] `+` A = ~` A.
Proof. by rewrite setYC setYTC. Qed.

Lemma setYA : associative (@setY T).
Proof. by move=> A B C; apply/eqP/seteqP => x/=; rewrite !in_setY addbA. Qed.

Lemma setIYl : left_distributive (@setI T) (@setY T).
Proof.
by move=> A B C; rewrite /setY setIUl; congr setU;
  rewrite setIAC /setD setCI setIUr setICK setU0.
Qed.

Lemma setIYr : right_distributive (@setI T) (@setY T).
Proof. by move=> A B C; rewrite setIC setIYl -2!(setIC A). Qed.

Lemma setY_def A B : A `+` B = (A `\` B) `|` (B `\` A).
Proof. by []. Qed.

Lemma setYE A B : A `+` B = (A `|` B) `\` (A `&` B).
Proof.
by rewrite /setY setDUl {1}setIC; congr setU;
  rewrite /setD setCI setIUr -/(setD ?[A] ?A) setDv setU0.
Qed.

Lemma setYU A B : (A `+` B) `+` (A `&` B) = A `|` B.
Proof.
apply/eqP/seteqP => x/=; rewrite !in_setY in_setI in_setU.
by case: (x \in A); case: (x \in B).
Qed.

Lemma setYI A B : (A `|` B) `\` (A `+` B) = A `&` B.
Proof.
apply/eqP/seteqP => x/=; rewrite in_setD in_setY in_setI in_setU.
by case: (x \in A); case: (x \in B).
Qed.

Lemma setYD A B : A `+` (A `&` B) = A `\` B.
Proof.
apply/eqP/seteqP => x/=; rewrite in_setD in_setY in_setI.
by case: (x \in A); case: (x \in B).
Qed.

Lemma setYCT A : A `+` ~` A = [set: T].
Proof. by rewrite /setY setDE setCK setIid setDE setIid setUv. Qed.

Lemma setCYT A : ~` A `+` A = [set: T].
Proof. by rewrite setYC setYCT. Qed.

End basic_lemmas.
Section basic_lemmas.
Variables (T T' : eqType).
Implicit Types (A B C D : set T) (x y : T).

Lemma sub1set x A : ([set x] `<=` A) = (x \in A).
Proof.
apply/idP/idP=> [/subsetP|] xA; first by apply: xA; rewrite in_mkset.
by apply/subsetP => y; rewrite in_mkset => /eqP ->.
Qed.

Lemma setD1K A (a : A) : (val a) |` A `\ (val a) = A.
Proof. by rewrite [LHS]setDUK//= sub1set. Qed.

Lemma setI1 A a : A `&` [set a] = if a \in A then [set a] else set0.
Proof.
case: ifPn => [|/negP] Aa.
  by apply/setIidPr/subsetP => b; rewrite in_mkset => /eqP ->.
apply/eqP; rewrite -subset0; apply/subsetP => b.
by rewrite in_setI in_set0 in_mkset => /andP[] + /eqP => /[swap] ->.
Qed.

Lemma set1I A a : [set a] `&` A = if a \in A then [set a] else set0.
Proof. by rewrite setIC setI1. Qed.

Lemma subsetC1 x A : (A `<=` [set~ x]) = (x \in ~` A).
Proof.
rewrite in_setC; apply/subsetP/negP => [Ax /Ax|xA t tA].
  by rewrite in_setC in_set1 => /negP; apply.
rewrite in_setC; apply/negP; rewrite in_set1 => /eqP tx.
by rewrite -tx in xA.
Qed.

Lemma not_setD1 x A : ~ x \in A -> A `\ x = A.
Proof.
by move=> /negP xA; apply/setDidPl; rewrite disj_setPRL sub1set in_setC.
Qed.

End basic_lemmas.
Arguments subsetT {T} A.

#[global] Hint Resolve subset_refl : core.

Lemma nat_nonempty : nat !=set0. Proof. by exists 0%N. Qed.

#[global] Hint Resolve nat_nonempty : core.

Lemma itv_sub_in2 d (T : porderType d) (P : T -> T -> Prop) (i j : interval T) :
  [set` j] `<=` [set` i] ->
  {in i &, forall x y, P x y} -> {in j &, forall x y, P x y}.
Proof.
by move=> /subsetP ji + x y xj yj; apply; [move: (ji x)|move: (ji y)];
  rewrite !in_mkset; apply.
Qed.

Lemma preimage_itv T d (rT : porderType d) (f : T -> rT) (i : interval rT) (x : T) :
  (x \in (f @^-1` [set` i])) = (f x \in i).
Proof. by []. Qed.

Lemma preimage_itvoy T d (rT : porderType d) (f : T -> rT) y :
  f @^-1` `]y, +oo[%classic = [set x | (y < f x)%O].
Proof. by apply/eqP/seteqP => t; rewrite in_preimage in_itv/= andbT. Qed.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to preimage_itvoy")]
Notation preimage_itv_o_infty := preimage_itvoy (only parsing).

Lemma preimage_itvcy T d (rT : porderType d) (f : T -> rT) y :
  f @^-1` `[y, +oo[%classic = [set x | (y <= f x)%O].
Proof. by apply/eqP/seteqP => t; rewrite in_preimage in_itv/= andbT.
Qed.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to preimage_itvcy")]
Notation preimage_itv_c_infty := preimage_itvcy (only parsing).

Lemma preimage_itvNyo T d (rT : orderType d) (f : T -> rT) y :
  f @^-1` `]-oo, y[%classic = [set x | (f x < y)%O].
Proof. exact/eqP/seteqP. Qed.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to preimage_itvNyo")]
Notation preimage_itv_infty_o := preimage_itvNyo (only parsing).

Lemma preimage_itvNyc T d (rT : orderType d) (f : T -> rT) y :
  f @^-1` `]-oo, y]%classic = [set x | (f x <= y)%O].
Proof. exact/eqP/seteqP. Qed.
#[deprecated(since="mathcomp-analysis 1.8.0", note="renamed to preimage_itvNyc")]
Notation preimage_itv_infty_c := preimage_itvNyc (only parsing).

Lemma eq_set T (P Q : T -> bool) : P =1 Q -> [set x | P x] = [set x | Q x].
Proof. by move=> /funext->. Qed.

Lemma set0fun {P T : Type} : @set0 T -> P. Proof. by case. Qed.

(*TODO
Lemma pred_oappE {T : Type} (D : {pred T}) :
  pred_oapp D = fun x => x \in some @` [set x | D x].
Proof.
apply/funext => -[x|]/=; apply/idP/idP; rewrite /pred_oapp mem_mkset //=.
- move=> xD; apply/asboolP.
  have: x \in [set x | D x] by rewrite mem_mkset asboolb.
  by exists x.
- by move=> /asboolP[] []/= ?; rewrite mksetE => ? [] <-.
- by move=> /asboolP[] []/= ? ? [].
Qed.

Lemma pred_oapp_set {T : Type} (D : set T) :
  pred_oapp (mem D) = mem (some @` D)%classic.
Proof.
by rewrite pred_oappE; apply/funext => x/=; apply/idP/idP; rewrite ?inE;
   move=> [y/= ]; rewrite ?in_setE; exists y; rewrite ?in_setE.
Qed.*)



#[global]
Hint Resolve subsetUl subsetUr subIsetl subIsetr subDsetl subDsetr : core.
Arguments setU_id2r {T} C {A B}.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to in_setX.")]
Notation in_setM := in_setX (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setX0.")]
Notation setM0 := setX0 (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to set0X.")]
Notation set0M := set0X (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setXTT.")]
Notation setMTT := setXTT (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setXT.")]
Notation setMT := setXT (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setTX.")]
Notation setTM := setTX (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setXI.")]
Notation setMI := setXI (only parsing).
(*#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setX_bigcupr.")]
Notation setM_bigcupr := setX_bigcupr (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setX_bigcupl.")]
 Notation setM_bigcupl := setX_bigcupl (only parsing).*)
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to setSX.")]
Notation setSM := setSX (only parsing).
(*#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to bigcupX1l.")]
Notation bigcupM1l := bigcupX1l (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to bigcupX1r.")]
Notation bigcupM1r := bigcupX1r (only parsing).*)

Lemma set_cst {T : eqType} {I} (x : T) (A : set I) :
   [set x | _ in A] = if A == set0 then set0 else [set x].
Proof.
apply/eqP/seteqP => t; rewrite in_mkset.
case: ifPn => [/eqP->|/set0P[] i iA].
  by rewrite in_set0; apply/negP/negP/asboolP => -[][].
by rewrite in_set1; apply/asboolP/eqP => [[_]|] -> //; exists i.
Qed.

Section set_order.
Import Order.TTheory.

Lemma set_eq_le d (rT : porderType d) T (f g : T -> rT) :
  [set x | f x == g x] = [set x | (f x <= g x)%O] `&` [set x | (f x >= g x)%O].
Proof. by apply/eqP/seteqP => x; rewrite !in_mkset eq_le. Qed.

Lemma set_neq_lt d (rT : orderType d) T (f g : T -> rT) :
  [set x | f x != g x ] = [set x | (f x < g x)%O] `|` [set x | (f x > g x)%O].
Proof. by apply/eqP/seteqP => x; rewrite !in_mkset neq_lt. Qed.

End set_order.

Lemma image2E {TA TB rT : Type} (A : set TA) (B : set TB) (f : TA -> TB -> rT) :
  [set f x y | x in A & y in B] = uncurry f @` (A `*` B).
Proof.
apply/eqP/seteqP => x; apply/asboolP/asboolP => [[a][b] <-|[][][a b] + <- /=].
  by exists (a, b).
rewrite in_setX/= => /andP[] aA bB.
by exists a; exists b.
Qed.

Lemma set_nil (T : eqType) : [set` [::]] = @set0 T.
Proof. exact/eqP/seteqP. Qed.

Lemma set_cons1 (T : eqType) (x : T) : [set` [:: x]] = [set x].
Proof. by apply/eqP/seteqP => y /=; rewrite !in_mkset orbF. Qed.

Lemma set_seq_eq0 (T : eqType) (S : seq T) : ([set` S] == set0) = (S == [::]).
Proof.
case: S => [|h t]; first exact/eqP/set_nil.
by rewrite -[RHS]/false; apply/negP => /seteqP /(_ h); rewrite mem_head.
Qed.

Lemma set_fset_eq0 (T : choiceType) (S : {fset T}) :
  ([set` S] == set0) = (S == fset0).
Proof. by rewrite set_seq_eq0. Qed.

Section InitialSegment.

Lemma II0 : `I_0 = set0. Proof. exact/eqP/seteqP. Qed.

Lemma II1 : `I_1 = [set 0]. Proof. by apply/eqP/seteqP; case. Qed.

Lemma IIn_eq0 n : `I_n = set0 -> n = 0.
Proof. by case: n => // n /eqP/seteqP/(_ 0%N). Qed.

Lemma IIS n : `I_n.+1 = `I_n `|` [set n].
Proof. by apply/eqP/seteqP => i; rewrite !in_mkset ltnS leq_eqVlt orbC. Qed.

Lemma IISl n : `I_n.+1 = n |` `I_n.
Proof. by rewrite setUC IIS. Qed.

Lemma IIDn n : `I_n.+1 `\ n = `I_n.
Proof.
rewrite IIS; apply/setUDK/subsetP => x.
by rewrite !in_mkset => /andP[] /eqP ->; rewrite ltnn.
Qed.

Lemma setI_II m n : `I_m `&` `I_n = `I_(minn m n).
Proof.
wlog: m n / m <= n => [mn|/[dup] mn /minn_idPl ->].
  by move: (leq_total m n) => /orP[] /mn//; rewrite setIC minnC.
by rewrite [LHS]setIidl//; apply/subsetP => k /leq_trans; apply.
Qed.

Lemma setU_II m n : `I_m `|` `I_n = `I_(maxn m n).
Proof.
wlog: m n / m <= n => [mn|/[dup] mn /maxn_idPr ->].
  by move: (leq_total m n) => /orP[] /mn//; rewrite setUC maxnC.
by rewrite [LHS]setUidr//; apply/subsetP => k /leq_trans; apply.
Qed.

Lemma Iiota (n : nat) : [set` iota 0 n] = `I_n.
Proof. by apply/eqP/seteqP => ?; rewrite /= mem_iota add0n. Qed.

Definition ordII {n} (k : 'I_n) : `I_n :=
  let kn : val k \in `I_n := valP k in val k.
Definition IIord {n} (k : `I_n) := Ordinal (valP k).

Definition ordIIK {n} : cancel (@ordII n) IIord.
Proof. by move=> k; apply/val_inj. Qed.

Lemma IIordK {n} : cancel (@IIord n) ordII.
Proof. by move=> k; apply/val_inj. Qed.

Lemma setC_I n : ~` `I_n = [set k | n <= k].
Proof. by rewrite -set_predC; apply: eq_set => k; apply/esym/leqNgt. Qed.

Lemma mem_not_I N n : (n \in ~` `I_N) = (N <= n).
Proof. by rewrite setC_I. Qed.

End InitialSegment.

Lemma setT_unit : [set: unit] = [set tt].
Proof. by apply/eqP/seteqP => // -[]. Qed.

Lemma set_unit (A : set unit) : A = set0 \/ A = setT.
Proof.
have [->|/set0P[[] Att]] := eqVneq A set0; [by left|right].
by apply/eqP/seteqP => -[].
Qed.

Lemma setT_bool : [set: bool] = [set true; false].
Proof. by apply/eqP/seteqP => -[]. Qed.

Lemma set_bool (B : set bool) :
  [\/ B == [set true], B == [set false], B == set0 | B == setT].
Proof.
have [Bt|/negPf Bt] := boolP (true \in B); have [Bf|/negPf Bf] := boolP (false \in B).
- have -> : B = setT by apply/eqP/seteqP => -[]//.
  by apply/or4P; rewrite eqxx/= !orbT.
- suff : B = [set true] by move=> ->; apply/or4P; rewrite eqxx.
  by apply/eqP/seteqP => -[].
- suff : B = [set false] by move=> ->; apply/or4P; rewrite eqxx/= orbT.
  by apply/eqP/seteqP => -[].
- suff : B = set0 by move=> ->; apply/or4P; rewrite eqxx/= !orbT.
  by apply/eqP/seteqP => -[].
Qed.

(* TODO: other lemmas that relate fset and classical sets *)
Lemma fdisjoint_cset (T : choiceType) (A B : {fset T}) :
  [disjoint A & B]%fset = [disjoint [set` A] & [set` B]].
Proof.
rewrite -fsetI_eq0; apply/idP/idP; apply: contraLR.
  move=> /set0P[] t /andP[] tA tB.
  by apply/fset0Pn; exists t; rewrite inE; apply/andP.
move=> /fset0Pn[t]; rewrite inE => /andP[tA tB].
by apply/set0P; exists t; apply/andP.
Qed.

Section SetFset.
Context {T : choiceType}.
Implicit Types (x y : T) (A B : {fset T}).

Lemma set_fset0 : [set y : T | y \in fset0] = set0.
Proof. exact/eqP/seteqP. Qed.

Lemma set_fset1 x : [set y | y \in [fset x]%fset] = [set x].
Proof. by apply/eqP/seteqP => y; rewrite in_fset1. Qed.

Lemma set_fsetI A B : [set` (A `&` B)%fset] = [set` A] `&` [set` B].
Proof. by apply/eqP/seteqP => x; rewrite in_fsetI. Qed.

Lemma set_fsetIr (P : {pred T}) (A : {fset T}) :
  [set` [fset x | x in A & P x]%fset] = [set` A] `&` [set` P].
Proof. by apply/eqP/seteqP => x; rewrite in_mkset/= !inE/=. Qed.

Lemma set_fsetU A B :
  [set` (A `|` B)%fset] = [set` A] `|` [set` B].
Proof. by apply/eqP/seteqP => x; rewrite in_fsetU. Qed.

Lemma set_fsetU1 x A : [set y | y \in (x |` A)%fset] = x |` [set` A].
Proof. by rewrite set_fsetU set_fset1. Qed.

Lemma set_fsetD A B :
  [set` (A `\` B)%fset] = [set` A] `\` [set` B].
Proof. by apply/eqP/seteqP => x; rewrite in_fsetD andbC. Qed.

Lemma set_fsetD1 A x : [set y | y \in (A `\ x)%fset] = [set` A] `\ x.
Proof. by rewrite set_fsetD set_fset1. Qed.

Lemma set_imfset (key : unit) [K : choiceType] (f : T -> K) (p : finmempred T) :
  [set` imfset key f p] = f @` [set` p].
Proof.
apply/eqP/seteqP => x.
apply/imfsetP/rangeP => [[] y yp/= ->|[][]y yp /= <-]; last by exists y.
rewrite -[in_mem _ _]/(y \in [set` p])/= in yp.
by exists y.
Qed.

End SetFset.

Section SetMonoids.
Variable (T : Type).

Import Monoid.
HB.instance Definition _ := isComLaw.Build (set T) set0 (@setU T) (@setUA T) (@setUC T) (@set0U T).
HB.instance Definition _ := isMulLaw.Build (set T) setT setU (@setTU T) (@setUT T).
HB.instance Definition _ := isComLaw.Build (set T) setT setI (@setIA T) (@setIC T) (@setTI T).
HB.instance Definition _ := isMulLaw.Build (set T) set0 setI (@set0I T) (@setI0 T).
HB.instance Definition _ := isAddLaw.Build (set T) setU setI (@setUIl T) (@setUIr T).
HB.instance Definition _ := isAddLaw.Build (set T) setI setU (@setIUl T) (@setIUr T).

HB.instance Definition _ := isComLaw.Build (set T) set0 (@setY T) (@setYA T) (@setYC T) (@set0Y T).
HB.instance Definition _ := isAddLaw.Build (set T) setI setY (@setIYl T) (@setIYr T).

End SetMonoids.

Section image_lemmas.
Context {aT rT : Type}.
Implicit Types (A B : set aT) (f : aT -> rT) (Y : set rT).

Lemma image_inj {f A a} : injective f -> (f a \in f @` A) = (a \in A).
Proof. by move=> f_inj; apply/idP/idP => /imageP[] b [] bA /f_inj <-. Qed.

Notation mem_image := image_inj (only parsing).

Lemma inj_image {f} : injective f -> injective (fun A => f @` A).
Proof.
move=> finj A B /eqP/seteqP AB; apply/eqP/seteqP => a.
by rewrite -!(image_inj finj).
Qed.

Lemma image_id A : id @` A = A.
Proof. by apply/eqP/seteqP => x; apply/idP/idP => /imageP[] y [] yA <-. Qed.

Lemma image_subP {A Y f} : reflect {homo f : x / x \in A >-> x \in Y} (f @` A `<=` Y).
Proof.
by apply: (iffP subsetP) => fAY x => [Ax|/imageP[] y [] yA <-]; apply: fAY.
Qed.

Lemma image_sub {f : aT -> rT} {A : set aT} {B : set rT} :
  (f @` A `<=` B) = (A `<=` f @^-1` B).
Proof. by apply/image_subP/subsetP => AB a /AB. Qed.

Lemma image_setU f A B : f @` (A `|` B) = f @` A `|` f @` B.
Proof.
apply/eqP/seteqP => b; rewrite in_setU.
apply/imageP/orP => [[] a []|].
  by rewrite in_setU => /orP[] aP <-; [left|right].
by move=> [] /imageP[] a [] aP <-; exists a; split.
Qed.

Lemma image_set0 f : f @` set0 = set0.
Proof. by apply/eqP/seteqP => b; apply/idP/idP/negP => /imageP[] ? []. Qed.

Lemma image_set0_set0 A f : f @` A = set0 -> A = set0.
Proof.
move=> /eqP/seteqP fA0; apply/eqP/seteqP => t.
rewrite in_set0; apply/negP => tA.
by have : f t \in set0 by rewrite -fA0.
Qed.

Lemma sub_image_setI f A B : f @` (A `&` B) `<=` f @` A `&` f @` B.
Proof. by apply/subsetP => b /imageP[] x [] /andP[] Aa Ba <-. Qed.

Lemma nonempty_image f A : f @` A !=set0 -> A !=set0.
Proof. by case=> b /imageP[] a [] aA _; exists a. Qed.

Lemma image_nonempty f A : A !=set0 -> f @` A !=set0.
Proof. by move=> [x] Ax; exists (f x). Qed.

Lemma image_subset f A B : A `<=` B -> f @` A `<=` f @` B.
Proof. by move=> /subsetP AB; apply/subsetP => _ /imageP[] a [] /AB aB <-. Qed.

Lemma preimage_set0 f : f @^-1` set0 = set0. Proof. by []. Qed.

Lemma preimage_setT f : f @^-1` setT = setT. Proof. by []. Qed.

Lemma nonempty_preimage f Y : f @^-1` Y !=set0 -> Y !=set0.
Proof. by case=> [t ?]; exists (f t). Qed.

Lemma preimage_image f A : A `<=` f @^-1` (f @` A).
Proof. by apply/subsetP => a Aa; apply/imageP; exists a. Qed.

Lemma preimage_range f : f @^-1` (range f) = [set: aT].
Proof. by apply/eqP/seteqP => x; rewrite in_preimage in_setT. Qed.

Lemma image_preimage_subset f Y : f @` (f @^-1` Y) `<=` Y.
Proof. by apply/subsetP => _ /imageP[] t /= [] Yft <-. Qed.

Lemma image_preimage f Y : f @` setT = setT -> f @` (f @^-1` Y) = Y.
Proof.
move=> fsurj; apply/eqP; rewrite eqEsubset; apply/andP; split.
  exact: image_preimage_subset.
apply/subsetP => x.
have: x \in setT by [].
by rewrite -fsurj => /imageP[] y [] _ <- yY.
Qed.

Lemma eq_imagel T1 T2 (A : set T1) (f f' : T1 -> T2) :
  (forall (x : A), f x = f' x) -> f @` A = f' @` A.
Proof.
by move=> h; apply/eqP/seteqP => y; apply/imageP/imageP => -[] x [] xA <-;
  exists x; split=> //; [apply: esym|]; apply: h.
Qed.

Lemma eq_image_id (g : aT -> aT) A : (forall x : A, g x = x) -> g @` A = A.
Proof. by move=> gE; rewrite -[RHS]image_id; apply: eq_imagel. Qed.

Lemma preimage_setU f Y1 Y2 : f @^-1` (Y1 `|` Y2) = f @^-1` Y1 `|` f @^-1` Y2.
Proof. exact/eqP/seteqP. Qed.

Lemma preimage_setI f Y1 Y2 : f @^-1` (Y1 `&` Y2) = f @^-1` Y1 `&` f @^-1` Y2.
Proof. exact/eqP/seteqP. Qed.

Lemma preimage_setC f Y : ~` (f @^-1` Y) = f @^-1` (~` Y).
Proof. by apply/eqP/seteqP => a; split=> + ?; apply. Qed.

Lemma preimage_subset f Y1 Y2 : Y1 `<=` Y2 -> f @^-1` Y1 `<=` f @^-1` Y2.
Proof. by move=> /subsetP Y12; apply/subsetP => t /Y12. Qed.

Lemma nonempty_preimage_setI f Y1 Y2 :
  (f @^-1` (Y1 `&` Y2)) !=set0 <-> (f @^-1` Y1 `&` f @^-1` Y2) !=set0.
Proof. by split; case=> t ?; exists t. Qed.

Lemma preimage_bigcup {I} f (F : I -> set rT) :
  f @^-1` (\bigcup_i F i) = \bigcup_i (f @^-1` F i).
Proof. exact/eqP/seteqP. Qed.

Lemma preimage_bigcap {I} f (F : I -> set rT) :
  f @^-1` (\bigcap_i F i) = \bigcap_i (f @^-1` F i).
Proof. exact/eqP/seteqP. Qed.

Lemma eq_preimage {I T : Type} (A : set T) (F G : I -> T) :
  F =1 G -> F @^-1` A = G @^-1` A.
Proof. by move=> eqFG; apply/eqP/seteqP => i; rewrite in_preimage eqFG. Qed.

Lemma notin_setI_preimage T (R : eqType) (f : T -> R) i :
  i \notin range f -> f @^-1` [set i] = set0.
Proof. by move=> ir; apply/eqP/seteqP => x; apply: contraNF ir => /eqP <-. Qed.

Lemma comp_preimage T1 T2 T3 (A : set T3) (g : T1 -> T2) (f : T2 -> T3) :
  (f \o g) @^-1` A = g @^-1` (f @^-1` A).
Proof. by []. Qed.

Lemma preimage_id T (A : set T) : id @^-1` A = A.
Proof. by apply/eqP/seteqP. Qed.

Lemma preimage_comp T1 T2 (g : T1 -> rT) (f : T2 -> rT) :
  f @^-1` range g = [set x | f x \in range g].
Proof. by []. Qed.

(* TOTHINK: Wat? *)
Lemma preimage_setI_eq0 (f : aT -> rT) (Y1 Y2 : set rT) :
  f @^-1` (Y1 `&` Y2) = set0 <-> f @^-1` Y1 `&` f @^-1` Y2 = set0.
Proof. by rewrite preimage_setI. Qed.

Lemma preimage0eq (f : aT -> rT) (Y : set rT) : Y = set0 -> f @^-1` Y = set0.
Proof. by move=> ->; rewrite preimage_set0. Qed.

Lemma preimage0 {T R} {f : T -> R} {A : set R} :
  A `&` range f `<=` set0 -> f @^-1` A = set0.
Proof.
move=> /subsetP Af; apply/eqP/seteqP => x; rewrite in_set0 in_preimage.
by apply/negP => fx; move: (Af (f x)) => /(_ _)/wrap[].
Qed.

Lemma preimage_true {T} (P : {pred T}) : P @^-1` [set true] = [set` P].
Proof. by apply/eqP/seteqP => x; rewrite !in_mkset eqb_id. Qed.

Lemma preimage_false {T} (P : {pred T}) : P @^-1` [set false] = ~` [set` P].
Proof. by apply/eqP/seteqP => x; rewrite !in_mkset eqbF_neg. Qed.

End image_lemmas.
Arguments sub_image_setI {aT rT f A B}.

Section image_lemmas.
Context {aT rT : eqType}.
Implicit Types (A B : set aT) (f : aT -> rT).

Lemma imsub1 x A f : f @` A `<=` [set x] -> forall a : A, f a = x.
Proof. by move=> /subsetP fA a; apply/eqP/fA. Qed.

Lemma imsub1P x A f : f @` A `<=` [set x] <-> forall a : A, f a = x.
Proof.
split=> [/(@imsub1 _)//|fA].
by apply/subsetP => _ /imageP[] a [] Aa <-; rewrite fA.
Qed.

Lemma image_set1 f t : f @` [set t] = [set f t].
Proof.
apply/eqP/seteqP => b; apply/imageP/idP => [[] a' [] /eqP -> <- //|/eqP ->].
by exists t; split.
Qed.

Lemma subset_set1 A a : A `<=` [set a] -> A = set0 \/ A = [set a].
Proof.
move=> /subsetP Aa.
have [/eqP|/set0P[t At]] := boolP (A == set0); first by left.
right; apply/eqP/seteqP => b; apply/idP/eqP => [/Aa /eqP//|->].
by move: (Aa _ At) => /eqP <-.
Qed.

Lemma subset_set2 A a b : A `<=` [set a; b] ->
  [\/ A = set0, A = [set a], A = [set b] | A = [set a; b]].
Proof.
have [<-|ab /subsetP Aab] := pselect (a = b).
  by rewrite setUid => /subset_set1[]->; [apply: Or41|apply: Or42].
have [|/nonsubset[] x /andP[] /[dup] /Aab /orP[] /eqP -> Ab /eqP// _] := pselect (A `<=` [set a]).
  by move=> /subset_set1[]->; [apply: Or41|apply: Or42].
have [|/nonsubset[] y /andP[] /[dup] /Aab /orP[] /eqP -> Aa /eqP// _] := pselect (A `<=` [set b]).
  by move=> /subset_set1[]->; [apply: Or41|apply: Or43].
by apply: Or44; apply/eqP/seteqP => z; apply/idP/idP => [/Aab|/orP[] /eqP ->].
Qed.

Lemma preimage10P {f : aT -> rT} {x} : ~ x \in range f <-> f @^-1` [set x] = set0.
Proof.
split=> [fx|]; first by rewrite [LHS]preimage0//; apply/subsetP => ? /andP[] /eqP ->.
apply: contraPnot => /rangeP[] t <- /eqP/seteqP/(_ t).
rewrite in_set0 => /negP; apply.
Qed.

Lemma preimage10 {f : aT -> rT} {x} : ~ x \in range f -> f @^-1` [set x] = set0.
Proof. by move/preimage10P. Qed.

End image_lemmas.
Arguments subset_set1 {_ _ _}.
Arguments subset_set2 {_ _ _ _}.

Lemma image2_subset {aT bT rT : Type} (f : aT -> bT -> rT)
    (A B : set aT) (C D : set bT) : A `<=` B -> C `<=` D ->
  [set f x y | x in A & y in C] `<=` [set f x y | x in B & y in D].
Proof. by move=> AB CD; rewrite !image2E; apply: image_subset; exact: setSX. Qed.

Lemma image_comp T1 T2 T3 (f : T1 -> T2) (g : T2 -> T3) A :
  g @` (f @` A) = (g \o f) @` A.
Proof.
apply/eqP/seteqP => x; apply/imageP/imageP => -[] b [] => [/imageP[] a [] aA <- <-|xA <-].
  by exists a.
by exists (f b); split.
Qed.

Lemma subKimage {T T'} {P : set (set T')} (f : T -> T') (g : T' -> T) :
  cancel f g -> [set A | f @` A \in P] `<=` [set g @` A | A in P].
Proof.
move=> ?; apply/subsetP => A; rewrite in_preimage => fA.
by apply/rangeP; exists (f @` A); rewrite image_comp [LHS]eq_image_id/=.
Qed.

Lemma subimageK T T' (P : set (set T')) (f : T -> T') (g : T' -> T) :
  cancel g f -> [set g @` A | A in P] `<=` [set A | f @` A \in P].
Proof.
move=> gK; apply/subsetP => _ /rangeP[] B /= <-.
by rewrite in_preimage image_comp [X in X \in _]eq_image_id/=.
Qed.

Lemma eq_imageK {T T'} {P : set (set T')} (f : T -> T') (g : T' -> T) :
    cancel f g -> cancel g f ->
  [set g @` A | A in P] = [set A | f @` A \in P].
Proof.
move=> fK gK; apply/eqP; rewrite eqEsubset; apply/andP.
by split; [apply: subimageK | apply: subKimage].
Qed.

(* TOTHINK: Should we keep this? *)
Lemma some_set0 {T} : some @` set0 = set0 :> set (option T).
Proof. exact: image_set0. Qed.

(* TOTHINK: Should we keep this? *)
Lemma some_set1 {T : eqType} (x : T) : some @` [set x] = [set some x].
Proof. exact: image_set1. Qed.

(* TODO
Lemma some_setC {T} (A : set T) : some @` (~` A) = [set~ None] `\` (some @` A).
Proof.
apply/seteqP; split; first by move=> _ [x nAx <-]; split=> // -[y /[swap]-[->]].
by move=> [x [_ exAx]|[/(_ erefl)//]]; exists x => // Ax; apply: exAx; exists x.
Qed.

Lemma some_setT {T} : some @` [set: T] = [set~ None].
Proof. by rewrite -[setT]setCK some_setC setCT some_set0 setD0. Qed.

Lemma some_setI {T} (A B : set T) : some @` (A `&` B) = some @` A `&` some @` B.
Proof.
apply/seteqP; split; first by move=> _ [x [Ax Bx] <-]; split; exists x.
by move=> _ [[x + <-] [y By []]] => /[swap]<- Ay; exists y.
Qed.

Lemma some_setU {T} (A B : set T) : some @` (A `|` B) = some @` A `|` some @` B.
Proof.
by rewrite -[_ `|` _]setCK setCU some_setC some_setI setDIr -!some_setC !setCK.
Qed.

Lemma some_setD {T} (A B : set T) : some @` (A `\` B) = (some @` A) `\` (some @` B).
Proof. by rewrite some_setI some_setC setIDA setIidl// => _ [? _ <-]. Qed.

Lemma sub_image_some {T} (A B : set T) : some @` A `<=` some @` B -> A `<=` B.
Proof. by move=> + x Ax => /(_ (Some x))[|y By [<-]]; first by exists x. Qed.

Lemma sub_image_someP {T} (A B : set T) : some @` A `<=` some @` B <-> A `<=` B.
Proof. by split=> [/sub_image_some//|/image_subset]. Qed.

Lemma image_some_inj {T} (A B : set T) : some @` A = some @` B -> A = B.
Proof. by move=> e; apply/seteqP; split; apply: sub_image_some; rewrite e. Qed.

Lemma some_set_eq0 {T} (A : set T) : some @` A = set0 <-> A = set0.
Proof.
split=> [|->]; last by rewrite some_set0.
by rewrite -!subset0 => A0 x Ax; apply: (A0 (some x)); exists x.
Qed.

Lemma some_preimage {aT rT} (f : aT -> rT) (A : set rT) :
  some @` (f @^-1` A) = omap f @^-1` (some @` A).
Proof.
apply/seteqP; split; first by move=> _ [a Afa <-]; exists (f a).
by move=> [x|] [a Aa //= [afx]]; exists x; rewrite // -afx.
Qed.

Lemma some_image {aT rT} (f : aT -> rT) (A : set aT) :
  some @` (f @` A) = omap f @` (some @` A).
Proof. by rewrite !image_comp. Qed.

Lemma disj_set_some {T} {A B : set T} :
  [disjoint some @` A & some @` B] = [disjoint A & B].
Proof.
by apply/disj_setPS/disj_setPS; rewrite -some_setI -some_set0 sub_image_someP.
Qed.

Lemma inl_in_set_inr A B (x : A) (Y : set B) :
  inl x \in [set inr y | y in Y] = false.
Proof. by apply/negP; rewrite inE/= => -[]. Qed.

Lemma inr_in_set_inl A B (y : B) (X : set A) :
  inr y \in [set inl x | x in X] = false.
Proof. by apply/negP; rewrite inE/= => -[]. Qed.

Lemma inr_in_set_inr A B (y : B) (Y : set B) :
  inr y \in [set @inr A B y | y in Y] = (y \in Y).
Proof. by apply/idP/idP => [/[!inE][/= [x ? [<-]]]|/[!inE]]//; exists y. Qed.

Lemma inl_in_set_inl A B (x : A) (X : set A) :
  inl x \in [set @inl A B x | x in X] = (x \in X).
Proof. by apply/idP/idP => [/[!inE][/= [y ? [<-]]]|/[!inE]]//; exists x. Qed.
 *)
Section bigop_lemmas.
Context {T I : Type}.
Implicit Types (A : set T) (i : I) (P : set I) (F G : I -> set T).

Lemma bigcup_sup i F : F i `<=` \bigcup_j F j.
Proof. by apply/subsetP => a Fia; apply/in_bigcupP; exists i. Qed.

Lemma bigcap_inf i F : \bigcap_j F j `<=` F i.
Proof. by apply/subsetP => a /in_bigcapP /(_ i). Qed.

Lemma subset_bigcup_r : {homo (fun x : I -> set T => \bigcup_i x i)
  : F G / range F `<=` range G >-> F `<=` G}.
Proof.
move=> F G /subsetP FG; apply/subsetP => t /in_bigcupP[i Fit].
have := FG (F i) => /(_ ltac:(apply _)) /rangeP[] j ji.
by apply/in_bigcupP; exists j; rewrite ji.
Qed.

Lemma subset_bigcap_r : {homo (fun x : I -> set T => \bigcap_i x i)
  : F G / range F `<=` range G >-> G `<=` F}.
Proof.
move=> F G /subsetP FG; apply/subsetP => t /in_bigcapP Gt.
apply/in_bigcapP => i.
have := FG (F i) => /(_ ltac:(apply _))/rangeP[] j <-.
exact: Gt.
Qed.

Lemma subset_bigcup_l F : {homo (fun x : set I => \bigcup_(i in x) F i)
  : F G / F `<=` G >-> F `<=` G}.
Proof.
move=> P Q /subsetP PQ; apply/subsetP => t /in_bigcupP[] [] i/= /PQ iQ Fit.
by apply/in_bigcupP; exists i.
Qed.

Lemma subset_bigcap_l F : {homo (fun x : set I => \bigcap_(i in x) F i)
  : F G / F `<=` G >-> G `<=` F}.
Proof.
move=> P Q /subsetP PQ; apply/subsetP => t /in_bigcapP tQ.
by apply/in_bigcapP => -[] i /= /PQ iQ; apply: tQ.
Qed.

Lemma eq_bigcupr F G : F =1 G ->
  \bigcup_i F i = \bigcup_i G i.
Proof.
move=> FG; apply/eqP/seteqP => x; apply/asbool_equiv_eq/propeqP/eq_exists => i.
by rewrite FG.
Qed.

Lemma eq_bigcapr F G : F =1 G ->
  \bigcap_i F i = \bigcap_i G i.
Proof.
move=> FG; apply/eqP/seteqP => x; apply/asbool_equiv_eq/propeqP/eq_forall => i.
by rewrite FG.
Qed.

Lemma setC_bigcup F : ~` (\bigcup_i F i) = \bigcap_i ~` F i.
Proof.
apply/eqP/seteqP => x.
apply/forallp_asboolPn/in_bigcapP => xF i; apply/negP => //; apply/xF.
Qed.

Lemma setC_bigcap J (F : J -> set T) : ~` (\bigcap_i (F i)) = \bigcup_i ~` F i.
Proof.
apply/eqP/seteqP => x.
by apply/existsp_asboolPn/in_bigcupP => -[] i /negP Fx; exists i.
Qed.

Lemma image_bigcup rT F (f : T -> rT) :
  f @` (\bigcup_i F i) = \bigcup_i f @` F i.
Proof.
apply/eqP/seteqP => x; apply/imageP/in_bigcupP => -[] => [y [] + <-|i].
  by move=> /in_bigcupP[] i yF; exists i.
move=> /imageP[] y [] yF <-; exists y; split=> //.
by apply/in_bigcupP; exists i.
Qed.

(* TODO
Lemma some_bigcap P F : some @` (\bigcap_(i in P) (F i)) =
  [set~ None] `&` \bigcap_(i in P) some @` F i.
Proof.
apply/seteqP; split.
  by move=> _ [x Fx <-]; split=> // i; exists x => //; apply: Fx.
by move=> [x|[//=]] [_ Fx]; exists x => //= i /Fx [y ? [<-]].
Qed.

Lemma bigcup_set_type P F : \bigcup_(i in P) F i = \bigcup_(j : P) F (val j).
Proof.
rewrite predeqE => x; split; last by move=> [[i/= /set_mem Pi] _ Fix]; exists i.
by move=> [i Pi Fix]; exists (SigSub (mem_set Pi)).
Qed.

Lemma eq_bigcupl P Q F : P `<=>` Q ->
  \bigcup_(i in P) F i = \bigcup_(i in Q) F i.
Proof. by move=> /seteqP->. Qed.

Lemma eq_bigcapl P Q F : P `<=>` Q ->
  \bigcap_(i in P) F i = \bigcap_(i in Q) F i.
Proof. by move=> /seteqP->. Qed.

Lemma eq_bigcup P Q F G : P `<=>` Q -> (forall i, P i -> F i = G i) ->
  \bigcup_(i in P) F i = \bigcup_(i in Q) G i.
Proof. by move=> /eq_bigcupl<- /eq_bigcupr->. Qed.

Lemma eq_bigcap P Q F G : P `<=>` Q -> (forall i, P i -> F i = G i) ->
  \bigcap_(i in P) F i = \bigcap_(i in Q) G i.
Proof. by move=> /eq_bigcapl<- /eq_bigcapr->. Qed.
 *)
Lemma bigcupU F G : \bigcup_i (F i `|` G i) =
  (\bigcup_i F i) `|` (\bigcup_i G i).
Proof.
apply/eqP/seteqP => x; apply/in_bigcupP/orP => [[] i /orP|].
  by case=> xi; [left|right]; apply/in_bigcupP; exists i.
by case=> /in_bigcupP[] i xi; exists i; apply/orP; [left|right].
Qed.

Lemma bigcapI F G : \bigcap_i (F i `&` G i) =
  (\bigcap_i F i) `&` (\bigcap_i G i).
Proof.
apply/eqP/seteqP => x; apply/in_bigcapP/andP => [xFG|[]].
  by split; apply/in_bigcapP => i; case/andP: (xFG i).
by move=> /in_bigcapP xF /in_bigcapP xG i; apply/andP.
Qed.

Lemma bigcup_const A : I -> \bigcup_(i : I) A = A.
Proof.
by move=> j; apply/eqP/seteqP => x; apply/in_bigcupP/idP => [[]//|xA]; exists j.
Qed.

Lemma bigcap_const A : I -> \bigcap_(i : I) A = A.
Proof. by move=> PN0; apply: setC_inj; rewrite setC_bigcap bigcup_const. Qed.

Lemma bigcapIl F A : I ->
  \bigcap_i (F i `&` A) = \bigcap_i F i `&` A.
Proof. by move=> PN0; rewrite bigcapI bigcap_const. Qed.

Lemma bigcapIr F A : I ->
  \bigcap_i (A `&` F i) = A `&` \bigcap_i F i.
Proof. by move=> PN0; rewrite bigcapI bigcap_const. Qed.

Lemma bigcupUl F A : I ->
  \bigcup_i (F i `|` A) = \bigcup_i F i `|` A.
Proof. by move=> PN0; rewrite bigcupU bigcup_const. Qed.

Lemma bigcupUr F A : I ->
  \bigcup_i (A `|` F i) = A `|` \bigcup_i F i.
Proof. by move=> PN0; rewrite bigcupU bigcup_const. Qed.

Lemma bigcup_set0 F : \bigcup_(i in set0) F i = set0.
Proof.
by apply/eqP/seteqP => a; rewrite in_set0; apply/negP => /in_bigcupP[][].
Qed.

Lemma bigcap_set0 F : \bigcap_(i in set0) F i = setT.
Proof. by apply/eqP/seteqP => a; rewrite in_setT; apply/in_bigcapP => [][]. Qed.

Lemma bigcup_setT F : \bigcup_(i in setT) F i = \bigcup_i F i.
Proof.
by apply/eqP/seteqP => a; apply/in_bigcupP/in_bigcupP => -[] i ai; exists i.
Qed.

Lemma bigcap_setT F : \bigcap_(i in setT) F i = \bigcap_i F i.
Proof.
by apply/eqP/seteqP => a; apply/in_bigcapP/in_bigcapP => + i; apply.
Qed.

Lemma bigcup_set1 {J : eqType} (F : J -> set T) (i : J) :
  \bigcup_(j in [set i]) F j = F i.
Proof.
apply/eqP/seteqP => a; apply/in_bigcupP/idP => [[][] _ /= /eqP -> //|ai].
by exists i.
Qed.

Lemma bigcap_set1 {J : eqType} (F : J -> set T) (i : J) :
  \bigcap_(j in [set i]) F j = F i.
Proof.
by apply/eqP/seteqP => a; apply/in_bigcapP/idP => [/(_ i)|aF [] _ /= /eqP ->].
Qed.

(*Lemma bigcup_nonempty P F :
  (\bigcup_(i in P) F i !=set0) <-> exists2 i, P i & F i !=set0.
Proof.
split=> [[t [i ? ?]]|[j ? [t ?]]]; by [exists i => //; exists t| exists t, j].
Qed.

Lemma bigcup0 P F :
  (forall i, P i -> F i = set0) -> \bigcup_(i in P) F i = set0.
Proof. by move=> PF; rewrite -subset0 => t -[i /PF ->]. Qed.

Lemma bigcap0 P F :
  (exists2 i, P i & F i = set0) -> \bigcap_(i in P) F i = set0.
Proof. by move=> [i Pi]; rewrite -!subset0 => Fi t Ft; apply/Fi/Ft. Qed.

Lemma bigcapT P F :
  (forall i, P i -> F i = setT) -> \bigcap_(i in P) F i = setT.
Proof. by move=> PF; rewrite -subTset => t -[i /PF ->]. Qed.

Lemma bigcupT P F :
  (exists2 i, P i & F i = setT) -> \bigcup_(i in P) F i = setT.
Proof. by move=> [i Pi F0]; rewrite -subTset => t; exists i; rewrite ?F0. Qed.

Lemma bigcup0P P F :
  (\bigcup_(i in P) F i = set0) <-> forall i, P i -> F i = set0.
Proof.
split=> [|/bigcup0//]; rewrite -subset0 => F0 i Pi; rewrite -subset0.
by move=> t Ft; apply: F0; exists i.
Qed.

Lemma bigcapTP P F :
  (\bigcap_(i in P) F i = setT) <-> forall i, P i -> F i = setT.
Proof.
split=> [|/bigcapT//]; rewrite -subTset => FT i Pi; rewrite -subTset.
by move=> t _; apply: FT.
   Qed.*)

Lemma setI_bigcupr F A :
  A `&` \bigcup_i F i = \bigcup_i (A `&` F i).
Proof.
apply/eqP/seteqP => x; apply/andP/in_bigcupP => [[] xA /in_bigcupP[] i xi|[] i /andP[] xA xi].
  by exists i.
by split=> //; apply/in_bigcupP; exists i.
Qed.

Lemma setI_bigcupl F A :
  \bigcup_i F i `&` A = \bigcup_i (F i `&` A).
Proof. by rewrite setIC setI_bigcupr//; under eq_bigcupr do rewrite setIC. Qed.

Lemma setU_bigcapr F A :
  A `|` \bigcap_i F i = \bigcap_i (A `|` F i).
Proof.
apply: setC_inj; rewrite setCU !setC_bigcap setI_bigcupr.
by under eq_bigcupr do rewrite -setCU.
Qed.

Lemma setU_bigcapl F A :
  \bigcap_i F i `|` A = \bigcap_i (F i `|` A).
Proof. by rewrite setUC setU_bigcapr//; under eq_bigcapr do rewrite setUC. Qed.

(*TODO
Lemma bigcup_mkcond P F :
  \bigcup_(i in P) F i = \bigcup_i if i \in P then F i else set0.
Proof.
rewrite predeqE => x; split=> [[i Pi Fix]|[i _]].
  by exists i => //; case: ifPn; rewrite (inE, notin_setE).
by case: ifPn; rewrite (inE, notin_setE) => Pi Fix; exists i.
Qed.

Lemma bigcup_mkcondr P Q F :
  \bigcup_(i in P `&` Q) F i = \bigcup_(i in P) if i \in Q then F i else set0.
Proof.
rewrite bigcup_mkcond [RHS]bigcup_mkcond; apply: eq_bigcupr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma bigcup_mkcondl P Q F :
  \bigcup_(i in P `&` Q) F i = \bigcup_(i in Q) if i \in P then F i else set0.
Proof.
rewrite bigcup_mkcond [RHS]bigcup_mkcond; apply: eq_bigcupr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma bigcap_mkcond F P :
  \bigcap_(i in P) F i = \bigcap_i if i \in P then F i else setT.
Proof.
apply: setC_inj; rewrite !setC_bigcap bigcup_mkcond; apply: eq_bigcupr => i _.
by case: ifP; rewrite ?setCT.
Qed.

Lemma bigcap_mkcondr P Q F :
  \bigcap_(i in P `&` Q) F i = \bigcap_(i in P) if i \in Q then F i else setT.
Proof.
rewrite bigcap_mkcond [RHS]bigcap_mkcond; apply: eq_bigcapr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma bigcap_mkcondl P Q F :
  \bigcap_(i in P `&` Q) F i = \bigcap_(i in Q) if i \in P then F i else setT.
Proof.
rewrite bigcap_mkcond [RHS]bigcap_mkcond; apply: eq_bigcapr => i _.
by rewrite in_setI; case: (i \in P) (i \in Q) => [] [].
Qed.

Lemma bigcup_imset1 P (f : I -> T) : \bigcup_(x in P) [set f x] = f @` P.
Proof.
by rewrite eqEsubset; split=>[a [i ?]->| a [i ?]<-]; [apply: imageP | exists i].
   Qed.*)

Lemma bigcup_setU J (F : J -> set T) (X Y : set J) :
  \bigcup_(i in X `|` Y) F i = \bigcup_(i in X) F i `|` \bigcup_(i in Y) F i.
Proof.
apply/eqP/seteqP => x; apply/in_bigcupP/orP => [[][] i /= /orP + xF|].
  by case=> iXY; [left|right]; apply/in_bigcupP; exists i.
by case=> /in_bigcupP[] i xF; exists i.
Qed.

Lemma bigcap_setU J (F : J -> set T) (X Y : set J) :
  \bigcap_(i in X `|` Y) F i = \bigcap_(i in X) F i `&` \bigcap_(i in Y) F i.
Proof.
by apply: setC_inj; rewrite !(setCI, setC_bigcap) (bigcup_setU (setC \o F)).
Qed.

Lemma bigcup_setU1 (J : eqType) (F : J -> set T) (x : J) (X : set J) :
  \bigcup_(i in x |` X) F i = F x `|` \bigcup_(i in X) F i.
Proof. by rewrite bigcup_setU bigcup_set1. Qed.

Lemma bigcap_setU1 (J : eqType) (F : J -> set T) (x : J) (X : set J) :
  \bigcap_(i in x |` X) F i = F x `&` \bigcap_(i in X) F i.
Proof. by rewrite bigcap_setU bigcap_set1. Qed.

Lemma bigcup_setD1 (J : eqType) (x : J) (F : J -> set T) (X : set J) :
  x \in X -> \bigcup_(i in X) F i = F x `|` \bigcup_(i in X `\ x) F i.
Proof. by move=> Xx; rewrite -bigcup_setU1 setD1K. Qed.

Lemma bigcap_setD1 (J : eqType) (x : J) (F : J -> set T) (X : set J) :
  x \in X -> \bigcap_(i in X) F i = F x `&` \bigcap_(i in X `\ x) F i.
Proof. by move=> Xx; rewrite -bigcap_setU1 setD1K. Qed.

Lemma setC_bigsetU U (s : seq T) (f : T -> set U) (P : pred T) :
   (~` (\big[setU/set0]_(t <- s | P t) f t)) = \big[setI/setT]_(t <- s | P t) ~` f t.
Proof. by elim/big_rec2: _ => [|i X Y Pi <-]; rewrite ?setC0 ?setCU. Qed.

Lemma setC_bigsetI U (s : seq T) (f : T -> set U) (P : pred T) :
  (~` (\big[setI/setT]_(t <- s | P t) f t)) =
  \big[setU/set0]_(t <- s | P t) ~` f t.
Proof. by elim/big_rec2: _ => [|i X Y Pi <-]; rewrite ?setCT ?setCI. Qed.

Lemma bigcupDr F (A : set T) : I ->
  \bigcap_i (A `\` F i) = A `\` \bigcup_i F i.
Proof. by move=> PN0; rewrite setDE setC_bigcup -bigcapIr. Qed.

Lemma setD_bigcupl F (A : set T) :
  \bigcup_i F i `\` A = \bigcup_i (F i `\` A).
Proof. by rewrite setDE setI_bigcupl; under eq_bigcupr do rewrite -setDE. Qed.

Lemma bigcup_setX_dep {J : Type} (F : I -> J -> set T)
    (P : set I) (Q : I -> set J) :
  \bigcup_(k in P `*`` Q) F k.1 k.2 = \bigcup_(i in P) \bigcup_(j in Q i) F i j.
Proof.
apply/eqP/seteqP => x; apply/in_bigcupP/in_bigcupP => [[][][] i j/=|[] i].
  by move=> /andP/= [] iP jQ xF; exists i; apply/in_bigcupP => /=; exists j.
move=> /in_bigcupP[] j xF.
have ijPQ: (val i, val j) \in P `*`` Q by apply/andP; split.
by exists (val i, val j).
Qed.

Lemma bigcup_setX {J : Type} (F : I -> J -> set T) (P : set I) (Q : set J) :
  \bigcup_(k in P `*` Q) F k.1 k.2 = \bigcup_(i in P) \bigcup_(j in Q) F i j.
Proof. exact: bigcup_setX_dep. Qed.

Lemma bigcup_bigcup T' F (G : T -> set T') :
  \bigcup_(i in \bigcup_n F n) G i =
  \bigcup_n \bigcup_(i in F n) G i.
Proof.
apply/eqP/seteqP => x; apply/in_bigcupP/in_bigcupP => [[][] n/=|[] i] /in_bigcupP[].
  by move=> i ni xn; exists i; apply/in_bigcupP; exists n.
move=> [] n/= ni xn.
have nn: n \in \bigcup_n F n by apply/in_bigcupP; exists i.
by exists n.
Qed.

Lemma bigcupID (Q : set I) (F : I -> set T) :
  \bigcup_i F i =
    (\bigcup_(i in Q) F i) `|` (\bigcup_(i in ~` Q) F i).
Proof. by rewrite -bigcup_setU setUv bigcup_setT. Qed.

Lemma bigcapID (Q : set I) (F : I -> set T) :
  \bigcap_i F i =
    (\bigcap_(i in Q) F i) `&` (\bigcap_(i in ~` Q) F i).
Proof. by rewrite -bigcap_setU setUv bigcap_setT. Qed.

Lemma bigcup_sub J (F : J -> set T) A :
  (forall i : J, F i `<=` A) -> \bigcup_i F i `<=` A.
Proof.
move=> FD; apply/subsetP => t /in_bigcupP[] n Fnt.
by move: (FD n) => /subsetP; apply.
Qed.

Lemma sub_bigcap F A :
  (forall i, A `<=` F i) -> A `<=` \bigcap_i F i.
Proof.
move=> AF; apply/subsetP => t At; apply/in_bigcapP => [] n.
by move: (AF n) => /subsetP; apply.
Qed.

Lemma subset_bigcup F G : (forall i, F i `<=` G i) ->
  \bigcup_i F i `<=` \bigcup_i G i.
Proof.
by move=> FG; apply: bigcup_sub => i; apply/(subset_trans (FG i))/bigcup_sup.
Qed.

Lemma bigcup_subset P Q F : P `<=` Q ->
  \bigcup_(i in P) F i `<=` \bigcup_(i in Q) F i.
Proof.
move=> /subsetP PQ; apply: bigcup_sub => -[] i/= /PQ iQ; apply/subsetP => x xi.
by apply/in_bigcupP; exists i.
Qed.

Lemma subset_bigcap F G : (forall i, F i `<=` G i) ->
  \bigcap_i F i `<=` \bigcap_i G i.
Proof.
move=> FG; apply: sub_bigcap => i; apply/subsetP => x /in_bigcapP xF.
by move: (FG i) => /subsetP; apply.
Qed.

End bigop_lemmas.
Arguments bigcup_setD1 {T I} x : rename.
Arguments bigcap_setD1 {T I} x : rename.

#[deprecated(since="mathcomp-analysis 1.3.0",note="renamed to bigcup_setX_dep")]
Notation bigcup_setM_dep := bigcup_setX_dep (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0",note="renamed to bigcup_setX")]
Notation bigcup_setM := bigcup_setX (only parsing).

Lemma setD_bigcup {T} (I : eqType) (F : I -> set T) (j : I) :
  F j `\` \bigcup_(i in [set k | k != j]) (F j `\` F i) = \bigcap_i F i.
Proof.
rewrite /setD setC_bigcup; under eq_bigcapr do rewrite setCI setCK.
rewrite -setU_bigcapr setIUr setICr set0U -bigcap_setU1.
(* TOTHINK: Should this be exposed? *)
have -> : j |` [set k | k != j] = setT by apply/eqP/seteqP => i; exact: orbN.
by rewrite bigcap_setT.
Qed.

Definition bigcup2 T (A B : set T) : nat -> set T :=
  fun i => if i == 0 then A else if i == 1 then B else set0.
Arguments bigcup2 T A B n /.

Lemma bigcup2E T (A B : set T) : \bigcup_i (bigcup2 A B) i = A `|` B.
Proof.
apply/eqP/seteqP => x; apply/in_bigcupP/orP => [[] i|].
  by rewrite /bigcup2; case: ifP => _; [|case: ifP => _ //] => xAB; [left|right].
by case=> xAB; [exists 0|exists 1].
Qed.

Lemma bigcup2inE T (A B : set T) : \bigcup_(i < 2) (bigcup2 A B) i = A `|` B.
Proof.
apply/eqP/seteqP => x; apply/in_bigcupP/orP => [[] i|].
  by rewrite /bigcup2; case: ifP => _; [|case: ifP => _ //] => xAB; [left|right].
by case=> xAB; [exists 0|exists 1].
Qed.

Definition bigcap2 T (A B : set T) : nat -> set T :=
  fun i => if i == 0 then A else if i == 1 then B else setT.
Arguments bigcap2 T A B n /.

Lemma bigcap2E T (A B : set T) : \bigcap_i (bigcap2 A B) i = A `&` B.
Proof.
apply: setC_inj; rewrite setC_bigcap setCI -bigcup2E /bigcap2 /bigcup2.
by apply: eq_bigcupr => -[|[|[]]].
Qed.

Lemma bigcap2inE T (A B : set T) : \bigcap_(i < 2) (bigcap2 A B) i = A `&` B.
Proof.
apply: setC_inj; rewrite setC_bigcap setCI -bigcup2inE /bigcap2 /bigcup2.
by apply: eq_bigcupr => -[] [|[|[]]].
Qed.

Lemma bigcup_recl T (F : nat -> set T) :
  \bigcup_n F n = F 0%N `|` \bigcup_(n in ~` `I_1) F n.
Proof.
rewrite -bigcup_setU1; suff ->: 0 |` ~` `I_1 = setT by rewrite bigcup_setT.
by apply/eqP/seteqP => n; rewrite !in_mkset -leqNgt lt0n orbN.
Qed.

Lemma bigcup_range {aT rT I} (f : aT -> I) (F : I -> set rT) :
  \bigcup_(i in range f) F i = \bigcup_x F (f x).
Proof.
apply/eqP/seteqP => y; apply/in_bigcupP/in_bigcupP => [[][]|[] x yx].
  by move=> _ /= /rangeP[] x <- yx; exists x.
by exists (f x).
Qed.

(* TOTHINK: Is this not exactly `bigcup_range`? *)
Lemma bigcup_image {aT rT I} (P : set aT) (f : aT -> I) (F : I -> set rT) :
  \bigcup_(x in f @` P) F x = \bigcup_(x in P) F (f x).
Proof. exact: bigcup_range. Qed.

Lemma bigcap_range {aT rT I} (f : aT -> I) (F : I -> set rT) :
  \bigcap_(i in range f) F i = \bigcap_x F (f x).
Proof.
by apply: setC_inj; rewrite !setC_bigcap (bigcup_range _ (setC \o F)).
Qed.

Lemma bigcap_image {aT rT I} (P : set aT) (f : aT -> I) (F : I -> set rT) :
  \bigcap_(x in f @` P) F x = \bigcap_(x in P) F (f x).
Proof. exact: bigcap_range. Qed.

(*TODO
Lemma bigcup_fset {I : choiceType} {U : Type}
    (F : I -> set U) (X : {fset I}) :
  \bigcup_(i in [set i | i \in X]) F i = \big[setU/set0]_(i <- X) F i :> set U.
Proof.
elim/finSet_rect: X => X IHX; have [->|[x xX]] := fset_0Vmem X.
  by rewrite big_seq_fset0 -subset0 => x [].
rewrite -(fsetD1K xX) set_fsetU set_fset1 big_fsetU1 ?inE ?eqxx//=.
by rewrite bigcup_setU1 IHX// fproperD1.
Qed.

Lemma bigcap_fset {I : choiceType} {U : Type}
    (F : I -> set U) (X : {fset I}) :
  \bigcap_(i in [set i | i \in X]) F i = \big[setI/setT]_(i <- X) F i :> set U.
Proof. by apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigcup_fset. Qed.

Lemma bigcup_fsetU1 {T U : choiceType} (F : T -> set U) (x : T) (X : {fset T}) :
  \bigcup_(i in [set j | j \in x |` X]%fset) F i =
  F x `|` \bigcup_(i in [set j | j \in X]) F i.
Proof. by rewrite set_fsetU1 bigcup_setU1. Qed.

Lemma bigcap_fsetU1 {T U : choiceType} (F : T -> set U) (x : T) (X : {fset T}) :
  \bigcap_(i in [set j | j \in x |` X]%fset) F i =
  F x `&` \bigcap_(i in [set j | j \in X]) F i.
Proof. by rewrite set_fsetU1 bigcap_setU1. Qed.

Lemma bigcup_fsetD1 {T U : choiceType} (x : T) (F : T -> set U) (X : {fset T}) :
    x \in X ->
  \bigcup_(i in [set i | i \in X]%fset) F i =
  F x `|` \bigcup_(i in [set i | i \in X `\ x]%fset) F i.
Proof. by move=> Xx; rewrite (bigcup_setD1 x)// set_fsetD1. Qed.
Arguments bigcup_fsetD1 {T U} x.

Lemma bigcap_fsetD1 {T U : choiceType} (x : T) (F : T -> set U) (X : {fset T}) :
    x \in X ->
  \bigcap_(i in [set i | i \in X]%fset) F i =
  F x `&` \bigcap_(i in [set i | i \in X `\ x]%fset) F i.
Proof. by move=> Xx; rewrite (bigcap_setD1 x)// set_fsetD1. Qed.
   Arguments bigcup_fsetD1 {T U} x.

Section bigcup_seq.
Variables (T : choiceType) (U : Type).

Lemma bigcup_seq_cond (s : seq T) (f : T -> set U) (P : pred T) :
  \bigcup_(t in [set x | (x \in s) && P x]) (f t) =
  \big[setU/set0]_(t <- s | P t) (f t).
Proof.
elim: s => [/=|h s ih]; first by rewrite set_nil bigcup_set0 big_nil.
rewrite big_cons -ih predeqE => u; split=> [[t /andP[]]|].
- rewrite inE => /orP[/eqP ->{t} -> fhu|ts Pt ftu]; first by left.
  case: ifPn => Ph; first by right; exists t => //; apply/andP; split.
  by exists t => //; apply/andP; split.
- case: ifPn => [Ph [fhu|[t /andP[ts Pt] ftu]]|Ph [t /andP[ts Pt ftu]]].
  + by exists h => //; apply/andP; split => //; rewrite mem_head.
  + by exists t => //; apply/andP; split => //; rewrite inE orbC ts.
  + by exists t => //; apply/andP; split => //; rewrite inE orbC ts.
Qed.

Lemma bigcup_seq (s : seq T) (f : T -> set U) :
  \bigcup_(t in [set` s]) (f t) = \big[setU/set0]_(t <- s) (f t).
Proof.
rewrite -(bigcup_seq_cond s f xpredT); congr (\bigcup_(t in mkset _) _).
by rewrite funeqE => t; rewrite andbT.
Qed.

Lemma bigcap_seq_cond (s : seq T) (f : T -> set U) (P : pred T) :
  \bigcap_(t in [set x | (x \in s) && P x]) (f t) =
  \big[setI/setT]_(t <- s | P t) (f t).
Proof. by apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigcup_seq_cond. Qed.

Lemma bigcap_seq (s : seq T) (f : T -> set U) :
  \bigcap_(t in [set` s]) (f t) = \big[setI/setT]_(t <- s) (f t).
Proof. by apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigcup_seq. Qed.

End bigcup_seq.

Lemma in_set1 [T : finType] (x y : T) : (x \in [set y]) = (x \in [set y]%SET).
Proof. by apply/idP/idP; rewrite !inE /= => /eqP. Qed.

Lemma bigcup_pred [T : finType] [U : Type] (P : {pred T}) (f : T -> set U) :
  \bigcup_(t in [set` P]) f t = \big[setU/set0]_(t in P) f t.
Proof.
apply/predeqP => u; split=> [[x Px fxu]|]; first by rewrite (bigD1 x)//; left.
move=> /mem_set; rewrite (@big_morph _ _ (fun X => u \in X) false orb).
- by rewrite big_has_cond => /hasP[x _ /andP[xP]]; rewrite inE => ufx; exists x.
- by move=> /= x y; apply/idP/orP; rewrite !inE.
- by rewrite in_set0.
Qed.*)

Section smallest.
Context {T} (C : set (set T)) (G : set T).

Definition smallest := \bigcap_(A in [set M : C | G `<=` M]) A.

Lemma sub_gen_smallest : G `<=` smallest.
Proof.
by apply/subsetP => x xG; apply/in_bigcapP => -[] A/= /subsetP; apply.
Qed.

Lemma sub_smallest X : X `<=` G -> X `<=` smallest.
Proof. move=> /subset_trans; apply; apply: sub_gen_smallest. Qed.

Lemma smallest_sub (X : C) : G `<=` X -> smallest `<=` X.
Proof. by move=> XC; apply: bigcap_inf. Qed.

Lemma smallest_id : G \in C -> smallest = G.
Proof.
move=> Cs; apply/eqP; rewrite eqEsubset [X in X && _]smallest_sub//=.
exact: sub_smallest.
Qed.

End smallest.
#[global] Hint Resolve sub_gen_smallest : core.

Lemma sub_smallest2r {T} (C : set (set T)) G1 G2 :
   smallest C G2 \in C -> G1 `<=` G2 -> smallest C G1 `<=` smallest C G2.
Proof. by move=> *; apply: smallest_sub=> //; apply: sub_smallest. Qed.

Lemma sub_smallest2l {T} (C1 C2 : set (set T)) G :
  C1 `<=` C2 -> smallest C2 G `<=` smallest C1 G.
Proof.
move=> /subsetP C12; apply/subsetP => A /in_bigcapP A1.
apply/in_bigcapP => -[][]/= X X1; rewrite in_mkset/= => GX.
have X2 := C12 _ X1.
have X2' : (X : C2) \in [set M : C2 | G `<=` MemType.elt M] by [].
exact: (A1 X).
Qed.

(*TODO
Section bigop_nat_lemmas.
Context {T : Type}.
Implicit Types (A : set T) (F : nat -> set T).

Lemma bigcup_mkord n F : \bigcup_(i < n) F i = \big[setU/set0]_(i < n) F i.
Proof.
rewrite -(big_mkord xpredT F) -bigcup_seq.
by apply: eq_bigcupl; split=> i; rewrite /= mem_index_iota leq0n.
Qed.

Lemma bigcup_mkord_ord n (G : 'I_n.+1 -> set T) :
  \bigcup_(i < n.+1) G (inord i) = \big[setU/set0]_(i < n.+1) G i.
Proof.
rewrite bigcup_mkord; apply: eq_bigr => /= i _; congr G.
by apply/val_inj => /=; rewrite inordK.
Qed.

Lemma bigcap_mkord n F : \bigcap_(i < n) F i = \big[setI/setT]_(i < n) F i.
Proof. by apply: setC_inj; rewrite setC_bigsetI setC_bigcap bigcup_mkord. Qed.

Lemma bigsetU_sup i n F : (i < n)%N -> F i `<=` \big[setU/set0]_(j < n) F j.
Proof. by move: n => // n ni; rewrite -bigcup_mkord; exact/bigcup_sup. Qed.

Lemma bigsetU_bigcup F n : \big[setU/set0]_(i < n) F i `<=` \bigcup_k F k.
Proof. by rewrite -bigcup_mkord => x [k _ Fkx]; exists k. Qed.

Lemma bigsetU_bigcup2 (A B : set T) :
   \big[setU/set0]_(i < 2) bigcup2 A B i = A `|` B.
Proof. by rewrite -bigcup_mkord bigcup2inE. Qed.

Lemma bigsetI_bigcap2 (A B : set T) :
   \big[setI/setT]_(i < 2) bigcap2 A B i = A `&` B.
Proof. by rewrite -bigcap_mkord bigcap2inE. Qed.

Lemma bigcup_splitn n F :
  \bigcup_i F i = \big[setU/set0]_(i < n) F i `|` \bigcup_i F (n + i).
Proof.
rewrite -bigcup_mkord -(bigcup_image _ (addn n)) -bigcup_setU.
apply: eq_bigcupl; split=> // k _.
have [ltkn|lenk] := ltnP k n; [left => //|right].
by exists (k - n); rewrite // subnKC.
Qed.

Lemma bigcap_splitn n F :
  \bigcap_i F i = \big[setI/setT]_(i < n) F i `&` \bigcap_i F (n + i).
Proof.
by apply: setC_inj; rewrite setCI !setC_bigcap (bigcup_splitn n) setC_bigsetI.
Qed.

Lemma subset_bigsetU F :
  {homo (fun n => \big[setU/set0]_(i < n) F i) : n m / (n <= m) >-> n `<=` m}.
Proof.
move=> m n mn; rewrite -!bigcup_mkord => x [i im Fix].
by exists i => //=; rewrite (leq_trans im).
Qed.

Lemma subset_bigsetI F :
  {homo (fun n => \big[setI/setT]_(i < n) F i) : n m / (n <= m) >-> m `<=` n}.
Proof.
move=> m n mn; rewrite -setCS !setC_bigsetI.
exact: (@subset_bigsetU (setC \o F)).
Qed.

Lemma subset_bigsetU_cond (P : pred nat) F :
  {homo (fun n => \big[setU/set0]_(i < n | P i) F i)
    : n m / (n <= m) >-> n `<=` m}.
Proof.
move=> n m nm; rewrite big_mkcond [in X in _ `<=` X]big_mkcond/=.
exact: (@subset_bigsetU (fun i => if P i then F i else _)).
Qed.

Lemma subset_bigsetI_cond (P : pred nat) F :
  {homo (fun n => \big[setI/setT]_(i < n | P i) F i)
    : n m / (n <= m) >-> m `<=` n}.
Proof.
move=> n m nm; rewrite big_mkcond [in X in _ `<=` X]big_mkcond/=.
exact: (@subset_bigsetI (fun i => if P i then F i else _)).
Qed.

Lemma bigcup_addn F n : \bigcup_i F (n + i) = \bigcup_(i >= n) F i.
Proof.
rewrite eqEsubset; split => [x /= [m _ Fmnx]|x /= [m nm Fmx]].
- by exists (n + m) => //=; rewrite leq_addr.
- by exists (m - n) => //; rewrite subnKC.
Qed.

Lemma bigcap_addn F n : \bigcap_i F (n + i) = \bigcap_(i >= n) F i.
Proof.
rewrite eqEsubset; split=> [x /= Fnx m nm|x /= nFx m _].
- by rewrite -(subnKC nm); exact: Fnx.
- exact/nFx/leq_addr.
Qed.

End bigop_nat_lemmas.
 *)
Definition is_subset1 T := forall (x y : T), x = y.
Definition is_fun {T1 T2} (f : set (T1 * T2)) :=
  forall x, is_subset1 ((pair x) @^-1` f).
Definition is_total {T1 T2} (f : set (T1 * T2)) :=
  forall x, ((pair x) @^-1` f) !=set0.
Definition is_totalfun {T1 T2} (f : set (T1 * T2)) :=
  forall x, let A := ((pair x) @^-1` f) in A !=set0 /\ is_subset1 A.

(* TOTHINK: naming. *)
Lemma is_subset10 T : is_subset1 (@set0 T). Proof. by move=> []. Qed.

Lemma is_subset11 (T : eqType) (x : T) : is_subset1 [set x].
Proof.
by move=> y z; apply: val_inj; case: y z => /= y /eqP + [] /= _ /eqP ->.
Qed.

Section xget.
Variables (T : choiceType) (x0 : T).
Implicit Types (P : set T).

Definition xget (P : set T) : T :=
  if pselect (P !=set0) isn't left exP then x0
  else projT1 (sigW exP).

Lemma xgetP (P : set T) :
  reflect (P !=set0) (xget P \in P).
Proof.
apply: (iffP idP) => [xP|P0]; first by exists (xget P).
by rewrite /xget; case: pselect => // /sigW[]/=.
Qed.

Lemma xgetI (P : set T) (x : T): x \in P -> xget P \in P.
Proof. by move=> Px; apply/xgetP; exists x. Qed.

Lemma xget_subset1 (P : set T) (x : P) :
  is_subset1 P -> xget P = x.
Proof.
move=> /(_ _ x) xE; have getP := xgetI (valP x).
by move: (xE (xget P)) => /(congr1 val).
Qed.

Lemma xget_unique (P : set T) (x : P) :
  (forall (y : P), val y = x) -> xget P = x.
Proof. by have getP := xgetI (valP x); apply. Qed.

Lemma xget0 : xget (@set0 T) = x0.
Proof. by rewrite /xget; case: pselect => // -[]. Qed.

Lemma xget1 x : xget [set x] = x. Proof. exact/xget_subset1/is_subset11. Qed.

End xget.

Definition fun_of_rel {aT} {rT : choiceType} (f0 : aT -> rT)
  (f : set (aT * rT)) := fun x => xget (f0 x) ((pair x) @^-1` f).

Lemma fun_of_relP {aT} {rT : choiceType} (f : set (aT * rT)) (f0 : aT -> rT) a :
  reflect ((pair a) @^-1` f !=set0) (fun_of_rel f0 f a \in (pair a) @^-1` f).
Proof. exact: xgetP. Qed.

Lemma fun_of_rel_uniq {aT} {rT : choiceType}
    (f : set (aT * rT)) (f0 : aT -> rT) a :
  is_subset1 ((pair a) @^-1` f) -> forall b : (pair a) @^-1` f, val b = fun_of_rel f0 f a.
Proof. by move=> fa1 b; apply/esym/xget_subset1. Qed.

Lemma in_setP {U} (A : set U) (P : U -> Prop) :
  (forall x : A, P x) <-> forall x, x \in A -> P x.
Proof. by split=> AP x => [xA|]; apply: AP. Qed.

Lemma in_set2P {U V} (A : set U) (B : set V) (P : U -> V -> Prop) :
  (forall (x : A) (y : B), P x y) <-> (forall x y, x \in A -> y \in B -> P x y).
Proof. by split=> AP x y => [xA yA|]; apply: AP. Qed.

Lemma in1TTP [T1] (P1 : T1 -> Prop) :
  (forall x : [set: T1], P1 x) <-> forall x : T1, P1 x.
Proof. by split=> PT x; apply: PT. Qed.

Lemma in2TTP [T1 T2] (P2 : T1 -> T2 -> Prop) :
  (forall (x : [set: T1]) (y : [set: T2]), P2 x y) <->
  forall (x : T1) (y : T2), P2 x y.
Proof. by split=> PT x; apply: PT. Qed.

Lemma in3TTP [T1 T2 T3] (P3 : T1 -> T2 -> T3 -> Prop) :
  (forall (x : [set: T1]) (y : [set: T2]) (z : [set: T3]), P3 x y z) <->
  forall (x : T1) (y : T2) (z : T3), P3 x y z.
Proof. by split=> PT x; apply: PT. Qed.

Lemma inTT_bij [T1 T2 : Type] [f : T1 -> T2] :
  {in [set: T1], bijective f} -> bijective f.
Proof. by case=> g fg gf; exists g => x; [apply: fg|apply: gf]. Qed.

HB.mixin Record isPointed T := { point : T }.

#[short(type=pointedType)]
HB.structure Definition Pointed := {T of isPointed T & Choice T}.

(* NB: was arrow_pointedType *)
HB.instance Definition _ (T : Type) (T' : T -> pointedType) :=
  isPointed.Build (forall t : T, T' t) (fun=> point).

HB.instance Definition _ := isPointed.Build unit tt.
HB.instance Definition _ := isPointed.Build bool false.
HB.instance Definition _ := isPointed.Build Prop False.
HB.instance Definition _ := isPointed.Build nat 0.
HB.instance Definition _ (T T' : pointedType) :=
  isPointed.Build (T * T')%type (point, point).
HB.instance Definition _ (n : nat) (T : pointedType) :=
  isPointed.Build (n.-tuple T) (nseq n point).
HB.instance Definition _ m n (T : pointedType) :=
  isPointed.Build 'M[T]_(m, n) (\matrix_(_, _) point)%R.
HB.instance Definition _ (T : choiceType) := isPointed.Build (option T) None.
HB.instance Definition _ (T : choiceType) := isPointed.Build {fset T} fset0.
HB.instance Definition _ (T : choiceType) := isPointed.Build (set T) set0.

Notation get := (xget point).
Notation "[ 'get' x | E ]" := (get [set x | E])
  (at level 0, x name, format "[ 'get'  x  |  E ]", only printing) : form_scope.
Notation "[ 'get' x : T | E ]" := (get (fun x : T  => E))
  (at level 0, x name, format "[ 'get'  x  :  T  |  E ]", only parsing) : form_scope.
Notation "[ 'get' x | E ]" := (get (fun x => E))
  (at level 0, x name, format "[ 'get'  x  |  E ]") : form_scope.

Section PointedTheory.
Context {T : pointedType}.

Lemma getP (P : set T) : reflect (P !=set0) (get P \in P).
Proof. exact: xgetP. Qed.

Lemma getI (P : set T) (x : P): get P \in P. Proof. exact: (xgetI point). Qed.

Lemma get_subset1 (P : set T) (x : P) : is_subset1 P -> get P = x.
Proof. exact: (xget_subset1 point). Qed.

Lemma get_unique (P : set T) (x : P) : (forall y : P, val y = x) -> get P = x.
Proof. exact: (xget_unique point). Qed.

Lemma get0 : get (@set0 T) = point.
Proof. exact: (xget0 point). Qed.

Lemma setT0 : setT != set0 :> set T. Proof. by apply/set0P; exists point. Qed.

End PointedTheory.

HB.mixin Record isBiPointed (X : Type) of Equality X := {
  zero : X;
  one : X;
  zero_one_neq : zero != one;
}.

#[short(type="biPointedType")]
HB.structure Definition BiPointed :=
  { X of Choice X & isBiPointed X }.

Variant squashed T : Prop := squash (x : T).
Arguments squash {T} x.
Notation "$| T |" := (squashed T) : form_scope.
Tactic Notation "squash" uconstr(x) := (exists; refine x) ||
   match goal with |- $| ?T | => exists; refine [the T of x] end.

Definition unsquash {T} (s : $|T|) : T :=
  projT1 (cid (let: squash x := s in @ex_intro T _ x isT)).
Lemma unsquashK {T} : cancel (@unsquash T) squash. Proof. by move=> []. Qed.

(* Empty types *)

HB.mixin Record isEmpty T := {
  axiom : T -> False
}.

#[short(type="emptyType")]
HB.structure Definition Empty := {T of isEmpty T & Finite T}.

HB.factory Record Choice_isEmpty T of Choice T := {
  axiom : T -> False
}.
HB.builders Context T of Choice_isEmpty T.

Definition pickle : T -> nat := fun=> 0%N.
Definition unpickle : nat -> option T := fun=> None.
Lemma pickleK : pcancel pickle unpickle.
Proof. by move=> x; case: (axiom x). Qed.
HB.instance Definition _ := isCountable.Build T pickleK.

Lemma fin_axiom : Finite.axiom ([::] : seq T).
Proof. by move=> /[dup]/axiom. Qed.
HB.instance Definition _ := isFinite.Build T fin_axiom.

HB.instance Definition _ := isEmpty.Build T axiom.
HB.end.

HB.factory Record Type_isEmpty T := {
  axiom : T -> False
}.
HB.builders Context T of Type_isEmpty T.
Definition eq_op (x y : T) := true.
Lemma eq_opP : Equality.axiom eq_op. Proof. by move=> ? /[dup]/axiom. Qed.
HB.instance Definition _ := hasDecEq.Build T eq_opP.

Definition find of pred T & nat : option T := None.
Lemma findP (P : pred T) (n : nat) (x : T) :  find P n = Some x -> P x.
Proof. by []. Qed.
Lemma ex_find (P : pred T) : (exists x : T, P x) -> exists n : nat, find P n.
Proof. by move=> [/[dup]/axiom]. Qed.
Lemma eq_find (P Q : pred T) : P =1 Q -> find P =1 find Q.
Proof. by []. Qed.
HB.instance Definition _ := hasChoice.Build T findP ex_find eq_find.

HB.instance Definition _ := Choice_isEmpty.Build T axiom.
HB.end.

HB.instance Definition _ := Type_isEmpty.Build False id.

HB.instance Definition _ := isEmpty.Build void (@of_void _).

Definition no {T : emptyType} : T -> False := @axiom T.
Definition any {T : emptyType} {U}  : T -> U := @False_rect _ \o no.

Lemma empty_eq0 {T : emptyType} : all_equal_to (set0 : set T).
Proof. by move=> X; apply/setF_eq0/no. Qed.

Definition quasi_canonical_of T C (sort : C -> T) (alt  : emptyType -> T):=
    forall (G : T -> Type), (forall s : emptyType, G (alt s)) -> (forall x, G (sort x)) ->
  forall x, G x.
Notation quasi_canonical_ sort alt := (@quasi_canonical_of _ _ sort alt).
Notation quasi_canonical T C := (@quasi_canonical_of T C id id).

Lemma qcanon T C (sort : C -> T) (alt : emptyType -> T) :
    (forall x, (exists y : emptyType, alt y = x) + (exists y, sort y = x)) ->
  quasi_canonical_ sort alt.
Proof. by move=> + G Cx Gs x => /(_ x)[/cid[y <-]|/cid[y <-]]. Qed.
Arguments qcanon {T C sort alt} x.

Lemma choicePpointed : quasi_canonical choiceType pointedType.
Proof.
apply: qcanon => -[Ts [Tc Te]].
set T := Choice.Pack _.
have [/unsquash x|/(_ (squash _)) TF] := pselect $|T|.
  right.
  pose Tp := isPointed.Build T x.
  pose TT : pointedType := HB.pack T Te Tc Tp.
  by exists TT.
left.
pose TMixin := Choice_isEmpty.Build T TF.
pose TT : emptyType := HB.pack T Te Tc TMixin.
by exists TT.
Qed.

Lemma eqPpointed : quasi_canonical eqType pointedType.
Proof.
by apply: qcanon; elim/eqPchoice; elim/choicePpointed => [[T F]|T];
   [left; exists (Empty.Pack F) | right; exists T].
Qed.

Lemma Ppointed : quasi_canonical Type pointedType.
Proof.
by apply: qcanon; elim/Peq; elim/eqPpointed => [[T F]|T];
   [left; exists (Empty.Pack F) | right; exists T].
Qed.

Section partitions.

(* TOTHINK: Do I want `set (set T)` instead of `I -> set T`? *)
Definition trivIset T I (F : I -> set T) :=
  forall i j, F i `&` F j !=set0 -> i = j.

Lemma trivIset1 T (I : eqType) (i : I) (F : [set i] -> set T) : trivIset F.
Proof.
by move=> [] j ji [] k ki _; apply: val_inj; rewrite /= (eqP ji) (eqP ki).
Qed.

Lemma ltn_trivIset T (F : nat -> set T) :
  (forall n m, (m < n)%N -> F m `&` F n = set0) -> trivIset F.
Proof.
move=> h m n [] t /andP[mt nt]; apply/eqP/negPn/negP.
by rewrite neq_ltn => /orP[] /h; apply/eqP/set0P; exists t.
Qed.

Lemma subsetC_trivIset T (F : nat -> set T) :
  (forall n, F n.+1 `<=` ~` (\bigcup_(i < n.+1) F i)) -> trivIset F.
Proof.
move=> sF; apply: ltn_trivIset => n m h; rewrite setIC; apply/disjoints_subset.
case: n h => // n h; apply: (subset_trans (sF n)).
by rewrite subsetC; apply: bigcup_sup.
Qed.

Lemma trivIset_mkcond T I (D : set I) (F : I -> set T) :
  trivIset (F \o (@MemType.elt _ D)) <-> trivIset (fun i => if i \in D then F i else set0).
Proof.
split=> [tA i j|tA i j]; last first.
  by have := tA i j; rewrite (valP i) (valP j)/= => /[apply]; apply: val_inj.
case: ifPn => iD; last by rewrite set0I => -[].
by case: ifPn => [jD /tA /(congr1 val)//|jD]; rewrite setI0 => -[].
Qed.

Lemma trivIset_set0 {I T} : trivIset (fun _ : I => set0 : set T).
Proof. by move=> i j; rewrite setI0 => /set0P; rewrite eqxx. Qed.

Lemma trivIsetP {T} {I : eqType} {F : I -> set T} :
  trivIset F <->
  forall i j : I, i != j -> F i `&` F j = set0.
Proof.
split=> tDF i j; first by apply: contraNeq => /set0P/tDF->.
by move=> /set0P; apply: contraNeq => /tDF->.
Qed.

(* TODO
Lemma trivIset_bigsetUI T (D : set nat) (F : nat -> set T) : trivIset (F \o (@MemType.elt _ D)) ->
  forall n (m : D), n <= m -> \bigcup_(i in D `&` `I_n) F i `&` F m = set0.
Proof.
move=> /(@trivIsetP _ D (F \o (@MemType.elt _ D))) tA.
elim=> [|n IHn] m.
  by move=> _; rewrite setI0 bigcup_set0 set0I.
  Search bigcup.
    STOP
move=> lt_nm; rewrite bigcup_mkcond. /= big_ord_recr -big_mkcond/=.
rewrite setIUl IHn 1?ltnW// set0U.
by case: ifPn => [Dn|NDn]; rewrite ?set0I// tA// ltn_eqF.
   Qed.*)

Lemma trivIset_setIl (T I : Type) (F G : I -> set T) :
  trivIset F -> trivIset (fun i => G i `&` F i).
Proof.
by move=> tF i j [] x /andP[] /andP[_] xi /andP[_] xj; apply: tF; exists x.
Qed.

Lemma trivIset_setIr (T I : Type) (F G : I -> set T) :
  trivIset F -> trivIset (fun i => F i `&` G i).
Proof.
by move=> tF i j [] x /andP[] /andP[] xi _ /andP[] xj _; apply: tF; exists x.
Qed.

Lemma sub_trivIset I T (D D' : set I) (F : I -> set T) :
  D `<=` D' -> trivIset (F \o @MemType.elt _ D') -> trivIset (F \o @MemType.elt _ D).
Proof.
move=> /subsetP DD' Ftriv [] i iD [] j jD/= ij; apply: val_inj => /=.
by move: iD jD ij => /DD' iD' /DD' jD' /Ftriv /(congr1 val).
Qed.

(* TOTHINK: Do I prefer reflect? *)
Lemma trivIset_bigcup2 T (A B : set T) :
  (A `&` B = set0) <-> trivIset (bigcup2 A B).
Proof.
split=> [AB0|/(_ 0 1)/= AB0]; last by apply/eqP/negP => /negP/set0P/AB0.
by (case=> [|[|i j]]/=; last by rewrite set0I => -[]);
  (move=> -[|[|j]]//=; last by rewrite setI0 => -[]); [|rewrite setIC];
  rewrite AB0 => -[].
Qed.

Lemma trivIset_image T T' I (f : T -> T') (F : I -> set T) :
  trivIset (fun i => f @` F i) -> trivIset F.
Proof. by move=> FI i j [] x /andP[] xi xj; apply: FI; exists (f x). Qed.
Arguments trivIset_image {T T' I} f F.

Lemma trivIset_image_inj T T' I (f : T -> T') (F : I -> set T) :
  injective f -> trivIset (fun i => f @` F i) <-> trivIset F.
Proof.
move=> finj; split; first exact: trivIset_image.
move=> trivF i j [] y /andP[] /imageP[] x [] xi <-.
by rewrite image_inj// => xj; apply: trivF; exists x.
Qed.

Lemma trivIset_preimage1 {aT} {rT : eqType} (f : aT -> rT) :
  trivIset (fun x => f @^-1` [set x]).
Proof. by move=> i j [] x /andP[] /eqP <- /eqP. Qed.

Lemma trivIset_preimage aT rT I (f : aT -> rT) (F : I -> set rT) :
  trivIset F -> trivIset (fun i => f @^-1` F i).
Proof.
move=> FI i j [] x /andP[]; rewrite !in_preimage => xi xj.
by apply: FI; exists (f x).
Qed.

Lemma trivIset_preimage_surj aT rT I (f : aT -> rT) (F : I -> set rT) :
  \bigcup_i F i `<=` range f -> trivIset (fun i => f @^-1` F i) = trivIset F.
Proof.
move=> /subsetP fsurj; apply: propext; split; last exact: trivIset_preimage.
move=> FI i j [] y /andP[] yi yj.
have /fsurj/rangeP[x yE]: y \in \bigcup_i F i by apply/in_bigcupP; exists i.
rewrite -yE in yi yj.
by apply: FI; exists x.
Qed.

(*
Lemma trivIset_bigcup (I T : Type) (J : eqType) (D : J -> set I) (F : I -> set T) :
  (forall n, trivIset (D n) F) ->
  (forall n m i j, n != m -> D n i -> D m j -> F i `&` F j !=set0 -> i = j) ->
  trivIset (\bigcup_k D k) F.
Proof.
move=> tB H; move=> i j [n _ Dni] [m _ Dmi] ij.
have [nm|nm] := eqVneq n m; first by apply: (tB m) => //; rewrite -nm.
exact: (H _ _ _ _ nm).
Qed.

Lemma trivIsetT_bigcup T1 T2 (I : eqType) (D : I -> set T1) (F : T1 -> set T2) :
  trivIset setT D ->
  trivIset (\bigcup_i D i) F ->
  trivIset setT (fun i => \bigcup_(t in D i) F t).
Proof.
move=> D0 h i j _ _ [t [[m Dim Fmt] [n Djn Fnt]]].
have mn : m = n by apply: h => //; [exists i|exists j|exists t].
rewrite {}mn {m} in Dim Fmt *.
by apply: D0 => //; exists n.
   Qed.

Definition cover T I D (F : I -> set T) := \bigcup_(i in D) F i.

Lemma coverE T I D (F : I -> set T) : cover D F = \bigcup_(i in D) F i.
Proof. by []. Qed.

Lemma cover_restr T I D' D (F : I -> set T) :
  D `<=` D' -> (forall i, D' i -> ~ D i -> F i = set0) ->
  cover D F = cover D' F.
Proof.
move=> DD' D'DF; rewrite /cover eqEsubset; split=> [r [i Di Fit]|r [i D'i Fit]].
- by have [D'i|] := pselect (D' i); [exists i | have := DD' _ Di].
- by have [Di|Di] := pselect (D i); [exists i | move: Fit; rewrite (D'DF i)].
Qed.

Lemma eqcover_r T I D (F G : I -> set T) :
  [set F i | i in D] = [set G i | i in D] ->
  cover D F = cover D G.
Proof.
move=> FG.
rewrite eqEsubset; split => [t [i Di Fit]|t [i Di Git]].
  have [j Dj GF] : [set G i | i in D] (F i) by rewrite -FG /mkset; exists i.
  by exists j => //; rewrite GF.
have [j Dj GF] : [set F i | i in D] (G i) by rewrite FG /mkset; exists i.
by exists j => //; rewrite GF.
Qed.

Definition partition T I D (F : I -> set T) (A : set T) :=
  [/\ cover D F = A, trivIset D F & forall i, D i -> F i !=set0].

Definition pblock_index T (I : pointedType) D (F : I -> set T) (x : T) :=
  [get i | D i /\ F i x].

Definition pblock T (I : pointedType) D (F : I -> set T) (x : T) :=
  F (pblock_index D F x).

(* TODO: theory of trivIset, cover, partition, pblock_index and pblock *)

Notation trivIsets X := (trivIset X id).

Lemma trivIset_sets T I D (F : I -> set T) :
  trivIset D F -> trivIsets [set F i | i in D].
Proof. exact: trivIset_image. Qed.

Lemma trivIset_widen T I D' D (F : I -> set T) :
(*  D `<=` D' -> (forall i, D i -> ~ D' i -> F i !=set0) ->*)
  D `<=` D' -> (forall i, D' i -> ~ D i -> F i = set0) ->
  trivIset D F = trivIset D' F.
Proof.
move=> DD' DD'F.
rewrite propeqE; split=> [DF i j D'i D'j FiFj0|D'F i j Di Dj FiFj0].
  have [Di|Di] := pselect (D i); last first.
    by move: FiFj0; rewrite (DD'F i) // set0I => /set0P; rewrite eqxx.
  have [Dj|Dj] := pselect (D j).
  - exact: DF.
  - by move: FiFj0; rewrite (DD'F j) // setI0 => /set0P; rewrite eqxx.
by apply D'F => //; apply DD'.
Qed.

Lemma perm_eq_trivIset {T : eqType} (s1 s2 : seq (set T)) (D : set nat) :
  [set k | (k < size s1)] `<=` D -> perm_eq s1 s2 ->
  trivIset D (fun i => nth set0 s1 i) -> trivIset D (fun i => nth set0 s2 i).
Proof.
move=> s1D; rewrite perm_sym => /(perm_iotaP set0)[s ss1 s12] /trivIsetP ts1.
apply/trivIsetP => i j Di Dj ij.
rewrite {}s12 {s2}; have [si|si] := ltnP i (size s); last first.
  by rewrite (nth_default set0) ?size_map// set0I.
rewrite (nth_map O) //; have [sj|sj] := ltnP j (size s); last first.
  by rewrite setIC (nth_default set0) ?size_map// set0I.
have nth_mem k : k < size s -> nth O s k \in iota 0 (size s1).
  by move=> ?; rewrite -(perm_mem ss1) mem_nth.
rewrite (nth_map O)// ts1 ?(nth_uniq,(perm_uniq ss1),iota_uniq)//; apply/s1D.
- by have := nth_mem _ si; rewrite mem_iota leq0n add0n.
- by have := nth_mem _ sj; rewrite mem_iota leq0n add0n.
Qed.
 *)

End partitions.
#[deprecated(note="Use trivIset_setIl instead")]
Notation trivIset_setI := trivIset_setIl (only parsing).

(*TODO: What is this?
Definition maximal_disjoint_subcollection T I (F : I -> set T) (A B : set I) :=
  [/\ A `<=` B, trivIset A F & forall C,
      A `<` C -> C `<=` B -> ~ trivIset C F ].

Section maximal_disjoint_subcollection.
Context {I T : Type}.
Variables (B : I -> set T) (D : set I).

Let P := fun X => X `<=` D /\ trivIset X B.

Let maxP (A : set (set I)) :
  A `<=` P -> total_on A (fun x y => x `<=` y) -> P (\bigcup_(x in A) x).
Proof.
move=> AP h; split; first by apply: bigcup_sub => E /AP [].
move=> i j [x Ax] xi [y Ay] yj ij; have [xy|yx] := h _ _ Ax Ay.
- by apply: (AP _ Ay).2 => //; exact: xy.
- by apply: (AP _ Ax).2 => //; exact: yx.
Qed.

Lemma ex_maximal_disjoint_subcollection :
  { E | maximal_disjoint_subcollection B E D }.
Proof.
have /cid[E [[ED tEB] maxE]] := Zorn_bigcup maxP.
by exists E; split => // F /maxE + FD; exact: contra_not.
Qed.

End maximal_disjoint_subcollection.
 *)

(* TOTHINK: What is this?
Definition meets T (F G : set (set T)) :=
  forall A B, F A -> G B -> A `&` B !=set0.

Notation "F `#` G" := (meets F G) : classical_set_scope.

Section meets.

Lemma meetsC T (F G : set (set T)) : F `#` G = G `#` F.
Proof.
gen have sFG : F G / F `#` G -> G `#` F.
  by move=> FG B A => /FG; rewrite setIC; apply.
by rewrite propeqE; split; apply: sFG.
Qed.

Lemma sub_meets T (F F' G G' : set (set T)) :
  F `<=` F' -> G `<=` G' -> F' `#` G' -> F `#` G.
Proof. by move=> sF sG FG A B /sF FA /sG GB; apply: (FG A B). Qed.

Lemma meetsSr T (F G G' : set (set T)) :
  G `<=` G' -> F `#` G' -> F `#` G.
Proof. exact: sub_meets. Qed.

Lemma meetsSl T (G F F' : set (set T)) :
  F `<=` F' -> F' `#` G -> F `#` G.
Proof. by move=> /sub_meets; apply. Qed.

End meets.
 *)

Section product.
Variables (T1 T2 : Type).
Implicit Type A B : set (T1 * T2).

(* TOTHINK: If I want to define `fst_set` as was done before I need to unfold
  the set in the unfolding clause too. *)
Lemma subset_fst_set : {homo (fun A => @fst T1 T2 @` A) : A B / A `<=` B}.
Proof.
by move=> A B /subsetP AB; apply/subsetP => x /asboolP[] [] y/= /AB yB <-.
Qed.

Lemma subset_snd_set : {homo (fun A => @fst T1 T2 @` A) : A B / A `<=` B}.
Proof.
by move=> A B /subsetP AB; apply/subsetP => x /asboolP[] [] y/= /AB yB <-.
Qed.

Lemma setX_sub_fst_snd A : A `<=` A.`1 `*` A.`2.
Proof. by apply/subsetP => -[] x y xyA; apply/andP; split. Qed.

(* TOTHINK: I do not understand what these are.
Lemma fst_set_fst A : A `<=` A.`1 \o fst. Proof. by move=> [x y]; exists y. Qed.

Lemma snd_set_snd A: A `<=` A.`2 \o snd. Proof. by move=> [x y]; exists x. Qed.
 *)

Lemma fst_setX (X : set T1) (Y : set T2) : (X `*` Y).`1 `<=` X.
Proof. by apply/subsetP => x /imageP[] y [] /andP[] + _ <-. Qed.

Lemma snd_setX (X : set T1) (Y : set T2) : (X `*` Y).`2 `<=` Y.
Proof. by apply/subsetP => x /imageP[] y [] /andP[] _ + <-. Qed.

Lemma fst_setXR (X : set T1) (Y : T1 -> set T2) : (X `*`` Y).`1 `<=` X.
Proof. by apply/subsetP => x /imageP[] y [] /andP[] + _ <-. Qed.

End product.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to fst_setX.")]
Notation fst_setM := fst_setX (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to snd_setX.")]
Notation snd_setM := snd_setX (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to fst_setXR instead.")]
Notation fst_setMR := fst_setXR (only parsing).

Section section.
Variables (T1 T2 : Type).
Implicit Types (A : set (T1 * T2)) (x : T1) (y : T2).

Definition xsection x A := pair x @^-1` A.

Definition ysection y A := pair^~ y @^-1` A.

Lemma xsection_snd_set x A : xsection x A `<=` A.`2.
Proof. by apply/subsetP => y Axy; apply/imageP; exists (x, y). Qed.

Lemma ysection_fst_set y A : ysection y A `<=` A.`1.
Proof. by apply/subsetP => x Axy; apply/imageP; exists (x, y). Qed.

Lemma mem_xsection x y A : (y \in xsection x A) = ((x, y) \in A).
Proof. exact: in_preimage. Qed.

Definition in_xsection := mem_xsection.

Lemma mem_ysection x y A : (x \in ysection y A) = ((x, y) \in A).
Proof. exact: in_preimage. Qed.

Definition in_ysection := mem_ysection.

Lemma xsectionE A x : xsection x A = (fun y => (x, y)) @^-1` A.
Proof. by []. Qed.

Lemma ysectionE A y : ysection y A = (fun x => (x, y)) @^-1` A.
Proof. by []. Qed.

Lemma xsection0 x : xsection x set0 = set0.
Proof. exact: preimage_set0. Qed.

Lemma ysection0 y : ysection y set0 = set0.
Proof. exact: preimage_set0. Qed.

Lemma in_xsectionX X1 X2 x : x \in X1 -> xsection x (X1 `*` X2) = X2.
Proof.
by move=> xX1; apply/eqP/seteqP => y; rewrite in_xsection in_setX xX1.
Qed.

Lemma in_ysectionX X1 X2 y : y \in X2 -> ysection y (X1 `*` X2) = X1.
Proof.
by move=> yX2; apply/eqP/seteqP => x; rewrite in_ysection in_setX yX2 andbT.
Qed.

Lemma notin_xsectionX X1 X2 x : x \notin X1 -> xsection x (X1 `*` X2) = set0.
Proof.
by move=> /negPf xX1; apply/eqP/seteqP => y; rewrite in_xsection in_setX xX1.
Qed.

Lemma notin_ysectionX X1 X2 y : y \notin X2 -> ysection y (X1 `*` X2) = set0.
Proof.
move=> /negPf yX2; apply/eqP/seteqP => x.
by rewrite in_ysection in_setX yX2 andbF.
Qed.

Lemma xsection_bigcup (F : nat -> set (T1 * T2)) x :
  xsection x (\bigcup_n F n) = \bigcup_n xsection x (F n).
Proof. exact: preimage_bigcup. Qed.

Lemma ysection_bigcup (F : nat -> set (T1 * T2)) y :
  ysection y (\bigcup_n F n) = \bigcup_n ysection y (F n).
Proof. exact: preimage_bigcup. Qed.

Lemma trivIset_xsection (I : Type) (F : I -> set (T1 * T2)) x : trivIset F ->
  trivIset (xsection x \o F).
Proof. exact: trivIset_preimage. Qed.

Lemma trivIset_ysection (I : Type) (F : I -> set (T1 * T2)) y : trivIset F ->
  trivIset (ysection y \o F).
Proof. exact: trivIset_preimage. Qed.

Lemma le_xsection x : {homo xsection x : X Y / X `<=` Y >-> X `<=` Y}.
Proof. exact: preimage_subset. Qed.

Lemma le_ysection y : {homo ysection y : X Y / X `<=` Y >-> X `<=` Y}.
Proof. exact: preimage_subset. Qed.

Lemma xsectionI A B x : xsection x (A `&` B) = xsection x A `&` xsection x B.
Proof. exact: preimage_setI. Qed.

Lemma ysectionI A B y : ysection y (A `&` B) = ysection y A `&` ysection y B.
Proof. exact: preimage_setI. Qed.

Lemma xsectionD X Y x : xsection x (X `\` Y) = xsection x X `\` xsection x Y.
Proof. by rewrite /xsection preimage_setI -preimage_setC. Qed.

Lemma ysectionD X Y y : ysection y (X `\` Y) = ysection y X `\` ysection y Y.
Proof. by rewrite /ysection preimage_setI -preimage_setC. Qed.

Lemma xsection_preimage_snd (B : set T2) x : xsection x (snd @^-1` B) = B.
Proof. by rewrite /xsection -comp_preimage preimage_id. Qed.

Lemma ysection_preimage_fst (A : set T1) y : ysection y (fst @^-1` A) = A.
Proof. by rewrite /ysection -comp_preimage preimage_id. Qed.

End section.
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to in_xsectionX.")]
Notation in_xsectionM := in_xsectionX (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to in_ysectionX.")]
Notation in_ysectionM := in_ysectionX (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to notin_xsectionX.")]
Notation notin_xsectionM := notin_xsectionX (only parsing).
#[deprecated(since="mathcomp-analysis 1.3.0", note="renamed to notin_ysectionX.")]
Notation notin_ysectionM := notin_ysectionX (only parsing).

Declare Scope relation_scope.
Delimit Scope relation_scope with relation.

Notation "B \; A" :=
  ([set xy | `[< exists z, ((xy.1, z) \in A) && ((z, xy.2) \in B) >]]) : relation_scope.

Notation "A ^-1" := ([set xy | (xy.2, xy.1) \in A]) : relation_scope.

Definition diagonal {T : eqType} := [set x : T * T | x.1 == x.2].

Lemma diagonalP {T : eqType} (x y : T) : reflect (x = y) ((x, y) \in diagonal).
Proof. exact: eqP. Qed.

Local Open Scope relation_scope.

Lemma set_compose_subset {X Y : Type} (A C : set (X * Y)) (B D : set (Y * X)) :
  A `<=` C -> B `<=` D -> A \; B `<=` C \; D.
Proof.
move=> /subsetP AC /subsetP BD.
apply/subsetP => -[] x y /asboolP/= [] z /andP[] /BD xz /AC zy.
by apply/asboolP; exists z; apply/andP.
Qed.

Lemma set_compose_diag {T : eqType} {U : Type} (E : set (T * U)) :
  E \; diagonal = E.
Proof.
apply/eqP/seteqP => -[] x y; apply/asboolP/idP => [[]/= z|xy].
  by move=> /andP[] /diagonalP ->.
by exists x; apply/andP; split=> //; apply/diagonalP.
Qed.

Lemma set_prod_invK {T : Type} (E : set (T * T)) : E^-1^-1 = E.
Proof. by apply/eqP/seteqP => -[]. Qed.

Local Close Scope relation_scope.
