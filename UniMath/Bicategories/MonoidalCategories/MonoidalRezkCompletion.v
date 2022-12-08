Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorCategory.

Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensor.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensorUnit.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedUnitors.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedAssociator.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.MonoidalRezkCompletion.

Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.

Local Open Scope cat.

Definition adj_equivalence_of_cats_to_cat_iso
      {C D : category} (Cuniv : is_univalent C) (Duniv : is_univalent D)
      {F : functor C D}
      (Fa : adj_equivalence_of_cats F)
  : catiso C D.
Proof.
  use (invweq (cat_iso_to_adjequiv (_,,Cuniv) (_,,Duniv))).
  use equiv_to_adjequiv.
  2: {
    apply adj_equivalence_to_left_equivalence.
    exact Fa.
  }
Defined.

Section TensorRezkCompletion.

  Context {C D E : category} {H : functor C D}
          (Duniv : is_univalent D)
          (Euniv : is_univalent E)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H)
          (TC : functor (C ⊠ C) C)
          (TE : functor (E ⊠ E) E).


  Definition precomp_tensor_catiso
    : catiso (total_category (functor_tensor_disp_cat (TransportedTensor Duniv H_eso H_ff TC) TE))
             (total_category (functor_tensor_disp_cat TC TE)).
  Proof.
    use adj_equivalence_of_cats_to_cat_iso.
    4: exact (precomp_tensor_adj_equiv Duniv Euniv H_eso H_ff TC TE).
    - apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensor_disp_cat_is_univalent _ _)).
    - apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensor_disp_cat_is_univalent _ _)).
  Defined.

End TensorRezkCompletion.

Section LiftedUnit.

  Context {C D E : category} {H : functor C D}
          (Duniv : is_univalent D)
          (Euniv : is_univalent E)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H)
          (I : C) (IE : E).

  Definition precomp_unit_catiso
    : catiso (total_category (functor_unit_disp_cat (H I) IE))
             (total_category (functor_unit_disp_cat I IE)).
  Proof.
    use adj_equivalence_of_cats_to_cat_iso.
    4: exact (precomp_unit_adj_equiv Euniv H_eso H_ff I IE).
    - apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_unit_disp_cat_is_univalent _ _)).
    - apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_unit_disp_cat_is_univalent _ _)).
  Defined.

End LiftedUnit.

Section LiftedTensorUnit.

  Context {C D E : category} {H : functor C D}
          (Duniv : is_univalent D)
          (Euniv : is_univalent E)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (TE : functor (E ⊠ E) E) (IE : E).

  Definition precomp_tensorunit_catiso
    : catiso (total_category (functor_tensorunit_disp_cat (TransportedTensor Duniv H_eso H_ff TC) TE (H I) IE))
             (total_category (functor_tensorunit_disp_cat TC TE I IE)).
  Proof.
    use adj_equivalence_of_cats_to_cat_iso.
    4: exact (precomp_tensorunit_cat_is_weak_equivalence Duniv Euniv H_eso H_ff TC I TE IE).

    - apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
    - apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
  Defined.

End LiftedTensorUnit.

Section LiftedLeftUnitor.

  Context {C D : category} {H : functor C D}
          (Duniv : is_univalent D)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (lu : left_unitor TC I).

  Context {E : category} (Euniv : is_univalent E)
          (TE : functor (E ⊠ E) E) (IE : E)
          (luE : left_unitor TE IE).

  Definition precomp_lunitor_catiso
    : catiso (total_category (functor_lu_disp_cat (TransportedLeftUnitor Duniv H_eso H_ff TC I lu) luE))
             (total_category (functor_lu_disp_cat lu luE)).
  Proof.
    use adj_equivalence_of_cats_to_cat_iso.
    4: {
      use precomp_lunitor_adj_equiv.
      exact Euniv.
    }

    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_lu_disp_cat_is_univalent.
    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_lu_disp_cat_is_univalent.
  Defined.

End LiftedLeftUnitor.

Section LiftedRightUnitor.

  Context {C D : category} {H : functor C D}
          (Duniv : is_univalent D)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (ru : right_unitor TC I).

  Context {E : category} (Euniv : is_univalent E)
          (TE : functor (E ⊠ E) E) (IE : E)
          (ruE : right_unitor TE IE).

  Definition precomp_runitor_catiso
    : catiso (total_category (functor_ru_disp_cat (TransportedRightUnitor Duniv H_eso H_ff TC I ru) ruE))
             (total_category (functor_ru_disp_cat ru ruE)).
  Proof.
    use adj_equivalence_of_cats_to_cat_iso.
    4: {
      use precomp_runitor_adj_equiv.
      exact Euniv.
    }

    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_ru_disp_cat_is_univalent.
    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_ru_disp_cat_is_univalent.
  Defined.

End LiftedRightUnitor.

Section LiftedAssociator.

  Context {C D : category} {H : functor C D}
          (Duniv : is_univalent D)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (α : associator TC).

  Context {E : category} (Euniv : is_univalent E)
          (TE : functor (E ⊠ E) E) (IE : E)
          (αE : associator TE).

  Definition precomp_associator_catiso
    : catiso (total_category (functor_ass_disp_cat (IC := H I) (ID := IE) (TransportedAssociator Duniv H_eso H_ff TC α) αE))
             (total_category (functor_ass_disp_cat (IC := I) (ID := IE) α αE)).
  Proof.
    use adj_equivalence_of_cats_to_cat_iso.
    4: {
      use precomp_associator_adj_equiv.
      exact Euniv.
    }

    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_ass_disp_cat_is_univalent.
    - apply is_univalent_total_category.
      + apply (is_univalent_total_category (is_univalent_functor_category _ _ Euniv) (functor_tensorunit_disp_cat_is_univalent _ _ _ _)).
      + apply functor_ass_disp_cat_is_univalent.
  Defined.

End LiftedAssociator.

Section LiftedMonoidal.

  Context {C D : category} {H : functor C D}
          (Duniv : is_univalent D)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (lu : left_unitor TC I)
          (ru : right_unitor TC I)
          (α : associator TC)
          (tri : triangle_eq TC I lu ru α)
          (pent : pentagon_eq TC α).

  Context {E : category}
          (Euniv : is_univalent E)
          (TE : functor (E ⊠ E) E) (IE : E)
          (luE : left_unitor TE IE)
          (ruE : right_unitor TE IE)
          (αE : associator TE).

  Definition precomp_monoidal_catiso
    : catiso (total_category (functor_monoidal_disp_cat
                                (TransportedLeftUnitor Duniv H_eso H_ff TC I lu) luE
                                (TransportedRightUnitor Duniv H_eso H_ff TC I ru) ruE
                                (TransportedAssociator Duniv H_eso H_ff TC α) αE
             ))
             (total_category (functor_monoidal_disp_cat
                                lu luE ru ruE α αE
             )).
  Proof.
    use adj_equivalence_of_cats_to_cat_iso.
    4: {
      use precomp_monoidal_adj_equiv.
      exact Euniv.
    }

    - apply is_univalent_LaxMonoidalFunctorCategory.
      exact Euniv.
    - apply is_univalent_LaxMonoidalFunctorCategory'.
      exact Euniv.
  Defined.

  Definition precomp_strongmonoidal_catiso
    : catiso (total_category (functor_strong_monoidal_disp_cat
                                (TransportedLeftUnitor Duniv H_eso H_ff TC I lu) luE
                                (TransportedRightUnitor Duniv H_eso H_ff TC I ru) ruE
                                (TransportedAssociator Duniv H_eso H_ff TC α) αE
             ))
             (total_category (functor_strong_monoidal_disp_cat
                                lu luE ru ruE α αE
             )).
  Proof.
    use adj_equivalence_of_cats_to_cat_iso.
    4: {
      use precomp_strongmonoidal_adj_equiv.
      exact Euniv.
    }

    - apply is_univalent_StrongMonoidalFunctorCategory.
      exact Euniv.
    - apply is_univalent_total_category.
      + apply is_univalent_LaxMonoidalFunctorCategory'.
        exact Euniv.
      + apply Constructions.disp_full_sub_univalent.
        intro ; apply isapropdirprod.
        * apply NaturalTransformations.isaprop_is_nat_z_iso.
        * apply Isos.isaprop_is_z_isomorphism.
  Defined.

End LiftedMonoidal.
