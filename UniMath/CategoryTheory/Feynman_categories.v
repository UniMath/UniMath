(** Anthony Bordg, April 2017 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.

(** * Monoidal category *)

Definition binprod_precategory (C D : precategory) : precategory.
Proof.
  refine (product_precategory bool _).
  intro x. induction x.
  - exact C.
  - exact D.
Defined.

Variable C D : precategory.

Notation "C × D" := (binprod_precategory C D) (at level 30) : cat.

Variable a b c d : C.

Notation "( a , b )" := (λ x : bool, match x with true => a |false => b end) : cat.

Local Open Scope cat.

Variable F : C × C ⟶ C.

Notation "a ⊗ b" := (F (a , b)) (at level 30, right associativity) : cat.
(** use \ox with Agda input mode *)

Definition isassoc_up_to_natiso := ∏ a b c : C, iso (a ⊗ (b ⊗ c)) ((a ⊗ b) ⊗ c).

Definition lunit_up_to_natiso (e : C) := ∏ a : C, iso (e ⊗ a) a.

Definition runit_up_to_natiso (e : C) := ∏ a : C, iso (a ⊗ e) a.

Variable f : a --> c.
Variable g : b --> d.

Notation "( f , g )" := (λ x : bool, match x with true => f |false => g end) : cat.

Definition pentagone (α : isassoc_up_to_natiso) :=
  (#F (inv_from_iso (α a b c), identity d)) ∘ (α (a ⊗ b) c d) ∘ (α a b (c ⊗ d)) = (α a (b ⊗ c) d) ∘ (#F (identity a, α b c d)).

Definition unit_tensor_unit_to_unit_uniqueness {e : C} (l : lunit_up_to_natiso e) (r : runit_up_to_natiso e) := l e = r e.

Definition triangle (α : isassoc_up_to_natiso) (e : C) (l : lunit_up_to_natiso e) (r : runit_up_to_natiso e) :=
   (#F (r a , identity c)) ∘ (α a e c) = #F (identity a , l c).