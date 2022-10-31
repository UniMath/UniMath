Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.DisplayedCategoriesLemmas.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensor.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensorUnit.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedUnitors.
Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedAssociator.

Local Open Scope cat.

Section RezkMonoidal.

  Context {C D E : category} {H : functor C D}
          (Duniv : is_univalent D)
          (Euniv : is_univalent E)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (lu : left_unitor TC I)
          (ru : right_unitor TC I)
          (α : associator TC)
          (tri : triangle_eq TC I lu ru α)
          (pent : pentagon_eq TC α).

  Let TD := TransportedTensor Duniv H_eso H_ff TC.
  Let ID := (H I).
  Let luD := TransportedLeftUnitor Duniv H_eso H_ff _ _ lu.
  Let ruD := TransportedRightUnitor Duniv H_eso H_ff _ _ ru.
  Let αD := TransportedAssociator Duniv H_eso H_ff _ α.

  Lemma TransportedTriangleEq
    :  triangle_eq TD (H I) luD ruD αD.
  Proof.
  Admitted.

  Lemma TransportedPentagonEq
    : pentagon_eq TD αD.
  Proof.
  Admitted.

  Definition TransportedMonoidal
    : monoidal_cat
    := D ,, TD ,, H I ,, luD ,, ruD ,, αD ,, TransportedTriangleEq ,, TransportedPentagonEq.

  Definition H_monoidal
    : functor_monoidal_cat lu luD ru ruD α αD.
  Proof.
    exists  (H,, pr1 (TransportedTensorComm Duniv H_eso H_ff TC),, id H I).
    split.
    - split.
      + exact (H_plu Duniv H_eso H_ff TC I lu).
      + exact (H_pru Duniv H_eso H_ff TC I ru).
    - exact (H_pα Duniv H_eso H_ff TC α I).
  Defined.

  Context (TE : functor (E ⊠ E) E) (IE : E)
          (luE : left_unitor TE IE)
          (ruE : right_unitor TE IE)
          (αE : associator TE).



  Definition precompMonoidal
    : disp_functor (precomp_tensorunit_functor Duniv H_eso H_ff TC I TE IE)
                   (functor_monoidal_disp_cat luD luE ruD ruE αD αE)
                   (functor_monoidal_disp_cat lu luE ru ruE α αE).
  Proof.
    apply disp_prod_functor_over_fixed_base.
    - apply disp_prod_functor_over_fixed_base.
      + apply precompLU.
      + apply precompRU.
    - apply precompA.
      exact Euniv.
  Defined.

  Definition precompMonoidal_ff
    : disp_functor_ff precompMonoidal.
  Proof.
    apply disp_prod_functor_over_fixed_base_ff.
    - apply disp_prod_functor_over_fixed_base_ff.
      + apply precompLU_ff.
      + apply precompRU_ff.
    - apply precompA_ff.
  Qed.

  Definition precompMonoidal_eso
    :  disp_functor_disp_ess_split_surj precompMonoidal.
  Proof.
    apply disp_prod_functor_over_fixed_base_eso.
    - apply disp_prod_functor_over_fixed_base_eso.
      + apply precompLU_eso.
      + apply precompRU_eso.
    - apply precompA_eso.
  Qed.

  Definition precomp_monoidal_is_ff
    : fully_faithful (total_functor precompMonoidal).
  Proof.
    use disp_functor_ff_to_total_ff.
    - apply (precomp_tensorunit_is_ff Duniv Euniv).
    - exact precompMonoidal_ff.
  Qed.

  Definition precomp_monoidal_is_eso
    : essentially_surjective (total_functor precompMonoidal).
  Proof.
    use disp_functor_eso_to_total_eso.
    - apply (precomp_tensorunit_is_eso Duniv Euniv).
    - exact precompMonoidal_eso.
  Qed.

  Definition precomp_monoidal_adj_equiv
    : adj_equivalence_of_cats (total_functor precompMonoidal).
  Proof.
    apply rad_equivalence_of_cats.
    - apply is_univalent_total_category.
      + apply is_univalent_total_category.
        * apply (is_univalent_functor_category _ _ Euniv).
        * apply is_disp_univalent_functor_tensorunit_disp_cat.
      + apply Constructions.dirprod_disp_cat_is_univalent.
        {
          apply Constructions.dirprod_disp_cat_is_univalent.
          apply functor_lu_disp_cat_is_univalent.
          apply functor_ru_disp_cat_is_univalent.
        }
        apply functor_ass_disp_cat_is_univalent.
    - exact precomp_monoidal_is_ff.
    - exact precomp_monoidal_is_eso.
  Defined.

End RezkMonoidal.
