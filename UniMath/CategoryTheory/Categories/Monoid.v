(**

  The Univalent Category of Monoids

  This file shows that the category of monoids, already defined in Magma.v, is univalent. It gives
  the forgetful and free functors to and from the category of sets.

  Contents
  1. The univalent category of monoids [monoid_univalent_category]
  2. The free and forgetful functors
  2.1. The Forgetful functor [monoid_forgetful_functor]
  2.2. The Free functor [monoid_free_functor]
  2.3. The adjunction [monoid_free_forgetful_adjunction]

 *)
Require Import UniMath.Foundations.All.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids2.

Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.IteratedBinaryOperations.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.Product.

Local Open Scope cat.

(** *  1. The univalent category of monoids *)

Definition is_univalent_monoid_disp_cat
  : is_univalent_disp monoid_disp_cat
  := dirprod_disp_cat_is_univalent _ _
    is_univalent_semigroup_disp_cat
    is_univalent_unital_magma_disp_cat.

Definition is_univalent_monoid_category
  : is_univalent monoid_category
  := is_univalent_total_category
    is_univalent_magma_category
    is_univalent_monoid_disp_cat.

Definition monoid_univalent_category : univalent_category
  := make_univalent_category monoid_category is_univalent_monoid_category.

(** *  2. The free and forgetful functors *)
(** **  2.1. The Forgetful functor *)

Definition monoid_forgetful_functor
  : functor monoid_category HSET
  := pr1_category _ ∙ pr1_category _.

Lemma monoid_forgetful_functor_is_faithful : faithful monoid_forgetful_functor.
Proof.
  apply comp_faithful_is_faithful.
  - apply faithful_pr1_category.
    intros.
    apply (isapropdirprod _ _ isapropunit).
    apply setproperty.
  - apply faithful_pr1_category.
    intros.
    apply isapropisbinopfun.
Defined.

(** **  2.2. The Free functor *)

Definition monoid_free_functor : functor HSET monoid_category.
Proof.
  use make_functor.
  - use make_functor_data.
    + intros s; exact (free_monoid s).
    + intros ? ? f; exact (free_monoidfun f).
  - apply make_is_functor.
    + (** Identity axiom *)
      intro.
      abstract (apply monoidfun_paths, funextfun; intro; apply map_idfun).
    + (** Composition axiom *)
      intros ? ? ? ? ?.
      abstract (apply monoidfun_paths, funextfun, (free_monoidfun_comp_homot f g)).
Defined.

(** **  2.3. The adjunction *)

Local Definition singleton {A : UU} (x : A) := cons x Lists.nil.

(** The unit of this adjunction is the singleton function [x ↦ x::nil] *)
Definition monoid_free_forgetful_unit :
  nat_trans (functor_identity _)
            (functor_composite monoid_free_functor monoid_forgetful_functor).
Proof.
  use make_nat_trans.
  - intro; exact singleton.
  - intros ? ? ?.
    abstract (apply funextfun; intro; reflexivity).
Defined.

(** This amounts to naturality of the counit: mapping commutes with folding *)
Lemma iterop_list_mon_map {m n : monoid} (f : monoidfun m n) :
  ∏ l, ((iterop_list_mon ∘ map (pr1monoidfun m n f)) l =
        (pr1monoidfun _ _ f ∘ iterop_list_mon) l)%functions.
Proof.
  apply list_ind.
  - apply pathsinv0, monoidfununel.
  - intros x xs H.
    simpl in *.
    refine (maponpaths iterop_list_mon (map_cons _ _ _) @ _).
    refine (iterop_list_mon_step _ _ @ _).
    refine (_ @ !maponpaths _ (iterop_list_mon_step _ _)).
    refine (_ @ !binopfunisbinopfun f _ _).
    apply maponpaths.
    assumption.
Qed.

(** The counit of this adjunction is the "folding" function
    [[a, b, …, z] ↦ a · b · ⋯ · z]

    (This is known to Haskell programmers as [mconcat].) *)
Definition monoid_free_forgetful_counit :
  nat_trans (functor_composite monoid_forgetful_functor monoid_free_functor )
            (functor_identity _).
Proof.
  use make_nat_trans.
  - intro.
    use make_monoidfun.
    + intro; apply iterop_list_mon; assumption.
    + split.
      * intros ? ?; apply iterop_list_mon_concatenate.
      * reflexivity.
  - intros ? ? f; apply monoidfun_paths.
    apply funextfun; intro; simpl in *.
    apply (iterop_list_mon_map f).
Defined.

Definition monoid_free_forgetful_adjunction_data :
  adjunction_data HSET monoid_category .
Proof.
  use make_adjunction_data.
  - exact monoid_free_functor.
  - exact monoid_forgetful_functor.
  - exact monoid_free_forgetful_unit.
  - exact monoid_free_forgetful_counit.
Defined.

Lemma monoid_free_forgetful_adjunction :
  form_adjunction' monoid_free_forgetful_adjunction_data.
Proof.
  apply make_form_adjunction;
    intro.
  - apply monoidfun_paths.
    apply funextfun.
    simpl.
    unfold homot; apply list_ind; [reflexivity|].
    intros x xs ?.
    unfold compose, identity.
    simpl.
    rewrite map_cons.
    refine (iterop_list_mon_step (M := free_monoid _) _ _ @ _).
    apply maponpaths; assumption.
  - reflexivity.
Qed.
