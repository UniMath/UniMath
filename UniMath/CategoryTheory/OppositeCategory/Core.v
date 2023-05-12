Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.opp_precat.

Definition opp_cat (C : category)
  : category.
Proof.
  exists (opp_precat C).
  apply has_homsets_op.
Defined.

Notation " C ^opp" := (opp_cat C) (at level 31).

(* functor_opp is defined as a functor between precategories,
   so in order to avoid always explicit casting, the following is introduced: *)
Definition functor_op {C D : category} (F : functor C D)
  : functor (opp_cat C) (opp_cat D)
  := functor_opp F.
