(**
  Generalisation of the concept of actions, over monoidal categories.

  Based on the definitions in the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore.
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Local Open Scope cat.

Context (Mon_V : monoidal_precat).

Let V := monoidal_precat_precat Mon_V.
Let I := monoidal_precat_unit Mon_V.
Let tensor := monoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)) (at level 31).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).
Let α' := monoidal_precat_associator Mon_V.
Let λ' := monoidal_precat_left_unitor Mon_V.

Section Actions_Definition.

(* A ⊙ I --> A *)

Section Actions_Natural_Transformations.

Context (A : precategory) (odot : functor (precategory_binproduct A V) A).

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (# odot (f #, g)) (at level 31).

Definition odot_I_functor : functor A A.
Proof.
    use tpair; [| split].
    - use tpair.
      exact (λ a, a ⊙ I).
      intros ? ? f.
      exact (f #⊙ (id I)).
    - intro.
      simpl.
      rewrite binprod_id.
      rewrite (functor_id odot).
      reflexivity.
    - unfold functor_compax.
      simpl.
      intros.
      replace (id I) with (id I · id I).
      rewrite binprod_comp.
      rewrite id_left.
      rewrite (functor_comp odot).
      reflexivity.
      rewrite id_left.
      reflexivity.
Defined.

Definition action_right_unitor : UU := nat_iso odot_I_functor (functor_identity A).

Definition odot_x_odot_y_functor : (A ⊠ V) ⊠ V ⟶ A.
Proof.
  use tpair; [| split].
  - use tpair.
    exact (λ a, (ob1 (ob1 a) ⊙ ob2 (ob1 a)) ⊙ ob2 a).
    intros ? ? f.
    exact ((mor1 (mor1 f) #⊙ mor2 (mor1 f)) #⊙ mor2 f).
  - intro.
    simpl.
    repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
    do 2 (rewrite binprod_id; rewrite (functor_id odot)).
    reflexivity.
  - unfold functor_compax.
    simpl.
    intros.
    repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
    do 2 (rewrite binprod_comp; rewrite (functor_comp odot)).
    reflexivity.
Defined.

Definition odot_x_otimes_y_functor : (A ⊠ V) ⊠ V ⟶ A.
Proof.
  use tpair; [| split].
    - use tpair.
      exact (λ a, ob1 (ob1 a) ⊙ (ob2 (ob1 a) ⊗ ob2 a)).
      intros ? ? f.
      exact (mor1 (mor1 f) #⊙ (mor2 (mor1 f) #⊗ mor2 f)).
    - intro.
      simpl.
      repeat rewrite (binprod_proj_id a); repeat rewrite binprod_proj_id.
      rewrite binprod_id.
      rewrite (functor_id tensor).
      rewrite binprod_id.
      rewrite (functor_id odot).
      reflexivity.
    - unfold functor_compax.
      simpl.
      intros.
      rewrite <- (functor_comp odot).
      rewrite <- binprod_comp.
      repeat rewrite (binprod_proj_comp f); repeat rewrite binprod_proj_comp.
      rewrite binprod_comp.
      rewrite (functor_comp tensor).
      reflexivity.
Defined.

Definition action_convertor : UU := nat_iso odot_x_odot_y_functor odot_x_otimes_y_functor.

Definition action_triangle_eq (ϱ : action_right_unitor) (χ : action_convertor) := ∏ (a : A), ∏ (x : V),
  (pr1 ϱ a) #⊙ (id x) = (pr1 χ ((a, I), x)) · (id a) #⊙ (pr1 λ' x).

Definition action_pentagon_eq (χ : action_convertor) := ∏ (a : A), ∏ (x y z : V),
(pr1 χ ((a ⊙ x, y), z)) · (pr1 χ ((a, x), y ⊗ z)) = (pr1 χ ((a, x), y)) #⊙ (id z) · (pr1 χ ((a, x ⊗ y), z)) · (id a) #⊙ (pr1 α' ((x, y), z)).

End Actions_Natural_Transformations.

(* Action *)

Definition action : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor A odot), ∑ (χ : action_convertor A odot), (action_triangle_eq A odot ϱ χ) × (action_pentagon_eq A odot χ).

Definition action_struct : UU := ∑ A : precategory, ∑ (odot : A ⊠ V ⟶ A), ∑ (ϱ : action_right_unitor A odot), ∑ (χ : action_convertor A odot), unit.

End Actions_Definition.
