(** * Sorted types. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(*
This file contains a formalization of _sorted types_, i.e. types indexed by elements of another
type, called _index type_. Notation and terminologies are inspired by Wolfgang Wechler,
_Universal Algebra for Computer Scientist_, Springer.
*)

Require Import UniMath.Foundations.All.

Require Export UniMath.Algebra.Universal.MoreLists.
Require Export UniMath.Algebra.Universal.HVectors.

Declare Scope sorted_scope.

Delimit Scope sorted_scope with sorted.

Local Open Scope sorted_scope.

(** An element of [sUU S] is an [S]-sorted type, i.e., an [S]-indexed family of types. *)

Definition sUU (S: UU): UU := S → UU.

(** If [X] and [Y] are [S]-sorted types, then [sfun X Y] is an [S]-sorted mapping, i.e.,
a [S]-indexed family of functions [X s → Y s]. *)

Definition sfun {S: UU} (X Y: sUU S): UU := ∏ s: S, X s → Y s.

Notation "x s→ y" := (sfun x y) (at level 99, y at level 200, right associativity): type_scope.

Bind Scope sorted_scope with sUU.

Bind Scope sorted_scope with sfun.

Definition idsfun {S: UU} (X: sUU S): X s→ X := λ s: S, idfun (X s).

Definition scomp {S: UU} {X Y Z: sUU S} (f: Y s→ Z) (g: X s→ Y): sfun X Z
  := λ s: S, (f s) ∘ (g s).

Infix "s∘" := scomp (at level 40, left associativity): sorted_scope.

Definition sunit (S: UU): sUU S := λ σ: S, unit.

Definition tosunit {S: UU} {X: sUU S}: X s→ sunit S := λ σ: S, tounit.

Lemma iscontr_sfuntosunit {S: UU} {X: sUU S}: iscontr (X s→ sunit S).
Proof.
  apply impred_iscontr.
  intros.
  apply iscontrfuntounit.
Defined.

(** An element of [shSet S] is an [S]-sorted set, i.e., an [S]-indexed family of sets. It ca be
immediately coerced to an [S]-sorted type. *)

Definition shSet (S: UU): UU := S → hSet.

Definition sunitset (S: UU): shSet S := λ _, unitset.

Lemma isaset_set_sfun_space {S: UU} {X: sUU S} {Y: shSet S}: isaset (X s→ Y).
Proof.
  change (isaset (X s→ Y)).
  apply impred_isaset.
  intros.
  apply isaset_forall_hSet.
Defined.

(** If [X: sUU S], then [star X] is the lifting of [X] to the index type [list S], given
by [X [s1; s2; ...; sn] = [X s1 ; X s2 ; ... ; X sn]. *)

Definition star {S: UU} (X: sUU S): sUU (list S) := λ l: list S, hvec (vec_map X (pr2 l)).

Bind Scope hvec_scope with star.

Notation "A ⋆" := (star A) (at level 3, format "'[ ' A '⋆' ']'"): sorted_scope.

(** If [f] is an indexed mapping between [S]-indexed types [X] and [Y], then [starfun X] is the lifting of
[f] to a [list S]-indexed mapping between [list S]-indexed sets [star X] and [star Y].
*)

Definition starfun {S: UU} {X Y: sUU S} (f: sfun X Y) : sfun X⋆ Y⋆ := λ s: list S, h1map f.

Notation "f ⋆⋆" := (starfun f) (at level 3, format "'[ ' f '⋆⋆' ']'"): sorted_scope.

(** Here follows the proof that [starfun] is functorial. Compositionality w.r.t. [s∘] is presented as
[(f s∘ g)⋆⋆ _ x = f⋆⋆ _ (g⋆⋆ _ x)] instead of [(f s∘ g)⋆⋆ = (f⋆⋆) s∘ (g⋆⋆ )] since the former
does not require function extensionality. *)

Lemma staridfun {S: UU} {X: sUU S} (l: list S) (x: X⋆ l): (idsfun X)⋆⋆ _ x = idsfun X⋆ _ x.
Proof.
  apply h1map_idfun.
Defined.

Lemma starcomp {S: UU} {X Y Z: sUU S} (f: Y s→ Z) (g: X s→ Y) (l: list S) (x: X⋆ l)
  : (f s∘ g)⋆⋆ _ x = f⋆⋆ _ (g⋆⋆ _ x).
Proof.
  unfold starfun.
  apply pathsinv0.
  apply h1map_compose.
Defined.
