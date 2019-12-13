(** ****************************************************************************

Theory about the cartesian cube category and cartesian cubical sets.

Contents:

- Cartesian cube category ([cartesian_cube_category])
- Binary products in the cartesian cube category ([cartesian_cube_category_binproducts])
- The empty set is a terminal object in the cartesian cube category
  ([empty_is_terminal_cartesian_cube_category])
- The unit interval in cartesian cubical sets is tiny
  ([unit_interval_cartesian_cubical_sets_is_tiny])


Written by: Elisabeth Bonnevier, 2019

 ********************************************************************************)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.ExponentiationLeftAdjoint.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.yoneda.

Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.

Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.StandardFiniteSets.


Local Open Scope stn.

(** The cartesian cube category. *)
Definition cartesian_cube_precategory_ob_mor : precategory_ob_mor :=
  make_precategory_ob_mor nat (λ m n : nat, ⟦n⟧ → ⟦m⟧ ⨿ ⟦2⟧).

Definition cartesian_cube_precategory_data : precategory_data.
Proof.
  exists cartesian_cube_precategory_ob_mor.
  split.
  - intro n.
    exact (λ i : ⟦n⟧, inl i).
  - intros l m n f g i.
    induction (g i) as [j1 | j2].
    + exact (f j1).
    + exact (inr j2).
Defined.

Definition cartesian_cube_precategory : precategory.
Proof.
  exists cartesian_cube_precategory_data.
  use make_is_precategory_one_assoc.
  - intros m n f.
    apply funextfun; intro i.
    cbn.
    now induction (f i).
  - intros m n g.
    apply idpath.
  - intros k l m n f g h.
    apply funextfun; intro i.
    cbn.
    now induction (h i).
Defined.

Definition cartesian_cube_category : category.
Proof.
  exists cartesian_cube_precategory.
  intros m n.
  apply funspace_isaset, isfinite_isaset.
  apply isfinitecoprod; apply isfinitestn.
Defined.

(** Binary products in the cartesian cube category. The product ⟦m⟧ × ⟦n⟧ is the sum ⟦m + n⟧. *)
Definition cartesian_cube_category_binproducts : BinProducts cartesian_cube_category.
Proof.
  intros m n.
  use make_BinProduct.
  - exact (m + n).
  - exact (λ i : ⟦m⟧, inl (stn_left _ _ i)).
  - exact (λ i : ⟦n⟧, inl (stn_right _ _ i)).
  - use make_isBinProduct.
    + apply homset_property.
    + intros l f g.
      use unique_exists.
      * intro i.
        induction (weqfromcoprodofstn_invmap _ _ i) as [x1 | x2];
          [exact (f x1) | exact (g x2)].
      * cbn.
        split; apply funextfun; intro i.
        -- assert (H :  weqfromcoprodofstn_invmap _ _ (stn_left m n i) = inl i).
           { now rewrite <- weqfromcoprodofstn_eq1. }
           now rewrite H.
        -- assert (H : weqfromcoprodofstn_invmap _ _ (stn_right m n i) = inr i).
           { now rewrite <- weqfromcoprodofstn_eq1. }
           now rewrite H.
      * intro h.
        now apply isapropdirprod; apply homset_property.
      * intros h [H1 H2].
        apply funextfun; intros i.
        rewrite <- (maponpaths h (weqfromcoprodofstn_eq2 _ _ i)).
        induction (weqfromcoprodofstn_invmap _ _ i) as [x1 | x2];
          [now rewrite <- H1 | now rewrite <- H2].
Defined.

(** The empty set is terminal in the cartesian cube category. *)
Lemma empty_is_terminal_cartesian_cube_category : Terminal cartesian_cube_category.
Proof.
  exists 0.
  intro n.
  apply iscontrfunfromempty2.
  use weqstn0toempty.
Defined.

Local Close Scope stn.

Local Open Scope cat.

(** Cartesian cubical sets *)
Definition cartesian_cubical_sets : category :=
  PreShv cartesian_cube_category.

Local Definition I : cartesian_cubical_sets :=
  yoneda cartesian_cube_category (homset_property cartesian_cube_category) 0.

Definition cartesian_cubical_sets_exponentials : Exponentials (@BinProducts_PreShv cartesian_cube_category).
Proof.
  apply Exponentials_functor_HSET.
  apply has_homsets_opp.
  apply homset_property.
Defined.

Local Definition exp_I : cartesian_cubical_sets ⟶ cartesian_cubical_sets :=
  pr1 (cartesian_cubical_sets_exponentials I).

(** The unit interval in cartesian cubical sets is tiny *)
Theorem unit_interval_cartesian_cubical_sets_is_tiny : is_left_adjoint exp_I.
Proof.
  use is_left_adjoint_exp_yoneda.
  apply cartesian_cube_category_binproducts.
Defined.

Local Close Scope cat.
