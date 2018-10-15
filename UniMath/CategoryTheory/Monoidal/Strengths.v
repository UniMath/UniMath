(**
  Definition of tensorial strengths between actions over monoidal categories.

  Based on the definitions in the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore.
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.Actions.

Local Open Scope cat.

Let Mon_V := Actions.Mon_V.
Let V := monoidal_precat_precat Mon_V.
Let I := monoidal_precat_unit Mon_V.
Let tensor := monoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)) (at level 31).

Section Strengths_Definition.

Context (actn actn' : action).

Let A := pr1 actn.
Let odot := pr1 (pr2 actn).
Let ϱ := pr1 (pr2 (pr2 actn)).
Let χ := pr1 (pr2 (pr2 (pr2 actn))).
Let A' := pr1 actn'.
Let odot' := pr1 (pr2 actn').
Let ϱ' := pr1 (pr2 (pr2 actn')).

Let χ' := pr1 (pr2 (pr2 (pr2 actn'))).

Section Strengths_Natural_Transformation.

Context (F : A ⟶ A').

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (#odot (f #, g)) (at level 31).
Notation "X ⊙' Y" := (odot' (X , Y)) (at level 31).
Notation "f #⊙' g" := (#odot' (f #, g)) (at level 31).

Definition strength_dom_data : functor_data (precategory_binproduct A V) A'.
Proof.
  exists (λ ax, F (ob1 ax) ⊙' (ob2 ax)).
  intros ? ? f.
  exact ((#F (mor1 f)) #⊙' (mor2 f)).
Defined.

Definition strength_dom_is_functor : is_functor strength_dom_data.
Proof.
  split.
  - intro.
    simpl.
    rewrite (functor_id F).
    rewrite <- (functor_id odot').
    rewrite <- binprod_id.
    reflexivity.
  - unfold functor_compax.
    simpl.
    intros.
    rewrite <- (functor_comp odot').
    rewrite <- binprod_comp.
    rewrite <- (functor_comp F).
    reflexivity.
Qed.

Definition strength_dom : (precategory_binproduct A V) ⟶ A' := mk_functor strength_dom_data strength_dom_is_functor.

Definition strength_codom_data : functor_data (A ⊠ V) A'.
Proof.
  exists (λ ax, F (ob1 ax ⊙ ob2 ax)).
  intros ? ? f.
  exact (#F (mor1 f #⊙ mor2 f)).
Defined.

Definition strength_codom_is_functor : is_functor strength_codom_data.
Proof.
  split.
  - intro.
    simpl.
    rewrite <- (functor_id F).
    rewrite <- (functor_id odot).
    rewrite <- binprod_id.
    reflexivity.
  - unfold functor_compax.
    simpl.
    intros.
    rewrite <- (functor_comp F).
    rewrite <- (functor_comp odot).
    rewrite <- binprod_comp.
    reflexivity.
Qed.

Definition strength_codom : A ⊠ V ⟶ A' := mk_functor strength_codom_data strength_codom_is_functor.

Definition strength_nat : UU := nat_iso strength_dom strength_codom.

Definition strength_triangle_eq (ϛ : strength_nat) := ∏ (a : A),
(pr1 ϛ (a, I)) · (#F (pr1 ϱ a)) = pr1 ϱ' (F a).

Definition strength_pentagon_eq (ϛ : strength_nat) := ∏ (a : A), ∏ (x y : V),
  (pr1 χ' ((F a, x), y)) · pr1 ϛ (a, x ⊗ y) = (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)) · (#F (pr1 χ ((a, x), y))).

End Strengths_Natural_Transformation.

Definition strength : UU := ∏ F : A ⟶ A', ∑ (ϛ : strength_nat F),
(strength_triangle_eq F ϛ) × (strength_pentagon_eq F ϛ).

End Strengths_Definition.

(*
  The standard tensorial strength:
  F(A) ⊗ B --> F(A ⊗ B)
*)
Definition tensorial_strength := strength tensorial_action tensorial_action.
