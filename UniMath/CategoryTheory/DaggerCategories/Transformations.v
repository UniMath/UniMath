(* No special notion of 'dagger natural transformation' is required.
   However, some concepts are defined in terms of natural transformations.
   1. The category of dagger functors and natural transformations has the structure of dagger category.
      The dagger of a natural transformation is given by taking the dagger objectwise.
      This is called the 'dagger adjoint'.
   2. A unitary morphism in the dagger functor category is given by a natural isomorphism whose inverse is given objectwise by the dagger [unitary_functors].
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.

Local Open Scope cat.

Section DaggerAdjoint.

  Definition dagger_adjoint_data
             {C D : category}
             {dagC : dagger C} {dagD : dagger D}
             {F G : functor C D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
             (α : nat_trans F G)
    : nat_trans_data G F
    := λ c, dagD _ _ (α c).

  Definition dagger_adjoint_is_nat_trans
             {C D : category}
             {dagC : dagger C} {dagD : dagger D}
             {F G : functor C D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
             (α : nat_trans F G)
    : is_nat_trans _ _ (dagger_adjoint_data dagF dagG α).
  Proof.
    intro ; intros.

    apply (dagger_injective dagD).

    refine (dagger_to_law_comp _ _ _ _ _ _ @ _ @ ! dagger_to_law_comp _ _ _ _ _ _).

    refine (maponpaths_2 compose (dagger_to_law_idemp _ _ _ _) _ @ _).
    refine (_ @ ! maponpaths_12 compose  (idpath _) (dagger_to_law_idemp _ _ _ _)).

    refine (! maponpaths (compose (α x')) (dagG _ _ f) @ _).
    refine (_ @ maponpaths_12 compose (dagF _ _ f) (idpath _)).

    apply pathsinv0, (pr2 α).
  Qed.

  Definition dagger_adjoint
             {C D : category}
             {dagC : dagger C} {dagD : dagger D}
             {F G : functor C D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
             (α : nat_trans F G)
    : nat_trans G F
    := _ ,, dagger_adjoint_is_nat_trans dagF dagG α.

End DaggerAdjoint.

Section UnitaryFunctors.

  Definition unitary_functors
             {C D : category}
             {dagC : dagger C} {dagD : dagger D}
             {F G : functor C D}
             (dagF : is_dagger_functor dagC dagD F)
             (dagG : is_dagger_functor dagC dagD G)
    : UU
    := ∑ α : nat_trans F G,
        (∏ x : C, Isos.is_inverse_in_precat (α x) (dagD _ _ (α x))).

End UnitaryFunctors.
