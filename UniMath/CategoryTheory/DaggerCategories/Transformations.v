(* No special notion of 'dagger natural transformation' is required,
   because the following definition will give the a functor category
   between dagger categories, restricted to the dagger functors,
   the structure of a dagger category:
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

    etrans.
    1: apply dagger_to_law_comp.
    etrans.
    2: apply pathsinv0, dagger_to_law_comp.

    etrans.
    1: apply maponpaths_2, dagger_to_law_idemp.
    etrans.
    2: apply maponpaths, pathsinv0, dagger_to_law_idemp.

    simpl in F, G.
    etrans.
    1: apply maponpaths, pathsinv0, dagG.
    etrans.
    2: apply maponpaths_2, dagF.
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
