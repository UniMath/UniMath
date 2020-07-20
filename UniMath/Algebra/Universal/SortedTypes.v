(** * Basic definitions for sorted types *)

(**
   This file contains a formalization of sorted types, i.e. types indeced by element on another
   type, called index type.
 *)
 
Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.HLists.

Declare Scope sorted_scope.

Delimit Scope sorted_scope with sorted.

Local Open Scope sorted_scope.

Definition sUU (S: UU): UU := S → UU.

Definition sfun {S: UU} (X Y: sUU S): UU := ∏ s: S, X s → Y s.

Infix "s→" := sfun (at level 99, right associativity): type_scope.

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

Infix "∘" := scomp: sorted_scope.

Definition shSet (S: UU): UU := S → hSet.

Definition sunitset (S: UU): shSet S := λ _, unitset.

Lemma isaset_set_sfun_space {S: UU} {X Y: shSet S}: isaset (X s→ Y).
Proof.
  apply impred_isaset.
  intros.
  apply isaset_forall_hSet.
Defined.

Definition star {S: UU} (X: sUU S): sUU (list S) := λ l: list S, HList (map X l).

Notation "A *" := (star A) (at level 10): sorted_scope.

Definition starfun {S: UU} {X Y: sUU S} (f: sfun X Y): sfun (star X) (star Y)
  := list_ind (λ arity, star X arity → star Y arity)
              (idfun unit)
              (λ (x: S) (xs: list S) HP, (dirprodf (f x) HP)).

Notation "f **" := (starfun f) (at level 10): sorted_scope.

Lemma staridfun {S: UU} {X: sUU S} (l: list S) (x: (star X) l): (idsfun X)** _ x = idsfun (X*) _ x.
Proof.
  change (idsfun (X*) l x) with x.
  revert l x.
  refine (list_ind _ _ _).
  - apply idpath.
  - intros σ σs HP x.
    change (X* (cons σ σs)) with (dirprod (X σ) (X* σs)) in x.
    induction x as [x1 x2].
    change ((idsfun X)** (cons σ σs)) with (dirprodf (idsfun X σ) ((idsfun X)** σs)).
    cbv [dirprodf make_dirprod].
    rewrite HP.
    apply idpath.
Defined.

Lemma starcomp {S: UU} {X Y Z: sUU S} (f: Y s→ Z) (g: X s→ Y) (l: list S) (x: (star X) l)
  : (f ∘ g) ** _ x = f** _ (g** _ x).
Proof.
  revert l x.
  refine (list_ind _ _ _).
  - apply idpath.
  - intros σ σs HP x.
    change (((f ∘ g) **) (cons σ σs)) with (dirprodf ((f ∘ g) σ) (((f ∘ g))** σs)).
    cbv [dirprodf make_dirprod].
    rewrite HP.
    apply idpath.
Defined.
