(** Anthony Bordg, April 2017 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.


Section monoidal_precategory.

(** * Monoidal (pre)category *)

Definition binprod_precategory (C D : precategory) : precategory.
Proof.
  refine (product_precategory bool _).
  intro x. induction x.
  - exact C.
  - exact D.
Defined.

Notation "C × D" := (binprod_precategory C D) (at level 30): cat.

Local Open Scope cat.

Definition binprod_precategory_pair_of_el {C : precategory} (a b : C) : C × C.
Proof.
  intro x. induction x.
  - exact a.
  - exact b.
Defined.

Notation "( a , b )" := (binprod_precategory_pair_of_el a b) : cat.

Variable C : precategory.
Variable F : C × C ⟶ C.
Notation "a ⊗ b" := (F (a , b)) (at level 30, right associativity) : cat.
(** use \ox with Agda input mode *)

Definition isassoc_up_to_natiso := ∏ a b c : C, iso (a ⊗ (b ⊗ c)) ((a ⊗ b) ⊗ c).

Definition lunit_up_to_natiso (e : C) := ∏ a : C, iso (e ⊗ a) a.

Definition runit_up_to_natiso (e : C) := ∏ a : C, iso (a ⊗ e) a.

Definition binprod_precategory_pair_of_mor {x y z w : C} (f : x --> z) (g : y --> w) : (x , y) --> (z , w).
Proof.
  intro. induction i.
  - exact f.
  - exact g.
Defined.

Notation "( f , g )" := (binprod_precategory_pair_of_mor f g) : cat.

Notation "f #⊗ g" := (#F (f , g)) (at level 30, right associativity) : cat.

Definition pentagone (α : isassoc_up_to_natiso) :=
  ∏ a b c d : C, (inv_from_iso (α a b c) #⊗ identity d) ∘ (α (a ⊗ b) c d) ∘ (α a b (c ⊗ d)) = (α a (b ⊗ c) d) ∘ (identity a #⊗ α b c d).

Definition unit_tensor_unit_to_unit_uniqueness {e : C} (l : lunit_up_to_natiso e) (r : runit_up_to_natiso e) := l e = r e.

Definition triangle (α : isassoc_up_to_natiso) (e : C) (l : lunit_up_to_natiso e) (r : runit_up_to_natiso e) :=
  ∏ a c : C, (r a #⊗ identity c) ∘ (α a e c) = identity a #⊗ l c.

Definition monoidal_struct : UU :=
  ∑ α : isassoc_up_to_natiso, ∑ e : C, ∑ l : lunit_up_to_natiso e, ∑ r : runit_up_to_natiso e, ∑ p : pentagone α,
                                                                            ∑ t : triangle α e l r,  unit_tensor_unit_to_unit_uniqueness l r.

Definition monoidal_precategory : UU := ∑ C : precategory, monoidal_struct.

(** Symmetric monoidal (pre)category *)

Definition braiding := ∏ a b : C, iso (a ⊗ b) (b ⊗ a).

End monoidal_precategory.