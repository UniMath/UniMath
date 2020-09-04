(** * Basic definitions for sorted types *)

(**
This file contains a formalization of sorted types, i.e. types indeced by element on another
type, called index type.
 *)
 
Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.Algebra.Universal.HVectors.

Declare Scope sorted_scope.

Delimit Scope sorted_scope with sorted.

Local Open Scope sorted_scope.

Definition sUU (S: UU): UU := S → UU.

Definition sfun {S: UU} (X Y: sUU S): UU := ∏ s: S, X s → Y s.

Notation "x s→ y" := (sfun x y) (at level 99, y at level 200, right associativity): type_scope.

Bind Scope sorted_scope with sUU.

Bind Scope sorted_scope with sfun.

Definition idsfun {S: UU} (X: sUU S): X s→ X := λ s: S, idfun (X s).

Definition sunit (S: UU): sUU S := λ σ: S, unit.

Definition tosunit {S: UU} {X: sUU S}: X s→ sunit S := λ σ: S, tounit.

Lemma iscontr_sfuntosunit {S: UU} {X: sUU S}: iscontr (X s→ sunit S).
Proof.
  apply impred_iscontr.
  intros.
  apply iscontrfuntounit.
Defined.

Definition scomp {S: UU} {X Y Z: sUU S} (f: Y s→ Z) (g: X s→ Y): sfun X Z
  := λ s: S, (f s) ∘ (g s).

Infix "s∘" := scomp (at level 40, left associativity): sorted_scope.

Definition shSet (S: UU): UU := S → hSet.

Definition sunitset (S: UU): shSet S := λ _, unitset.

Lemma isaset_set_sfun_space {S: UU} {X: sUU S} {Y: shSet S}: isaset (X s→ Y).
Proof.
  change (isaset (X s→ Y)).
  apply impred_isaset.
  intros.
  apply isaset_forall_hSet.
Defined.

Definition star {S: UU} (X: sUU S): sUU (list S) := λ l: list S, HVec (vector_map X (pr2 l)).

Bind Scope hvec_scope with star.

Notation "A ↑" := (star A) (at level 10): sorted_scope.

Definition starfun {S: UU} {X Y: sUU S} (f: sfun X Y): sfun (X ↑) (Y ↑) := λ s: list S, hmap f.

Notation "f ↑↑" := (starfun f) (at level 10): sorted_scope.

Lemma staridfun {S: UU} {X: sUU S} (l: list S) (x: X ↑ l): (idsfun X) ↑↑ _ x = idsfun (X ↑ ) _ x.
Proof.
  apply hmap_idfun.
Defined.

Lemma starcomp {S: UU} {X Y Z: sUU S} (f: Y s→ Z) (g: X s→ Y) (l: list S) (x: X ↑ l)
  : (f s∘ g) ↑↑ _ x = f ↑↑ _ (g ↑↑ _ x).
Proof.
  unfold starfun.
  apply pathsinv0.
  apply hmap_comp.
Defined.

