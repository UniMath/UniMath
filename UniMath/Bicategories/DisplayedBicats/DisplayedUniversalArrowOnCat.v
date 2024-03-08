(*
In this file, we construct displayed universal arrows over the inclusion UnivCat to Cat (with left biadjoint the Rezk completion).

Contents:
1. LocallyContr:
   A make constructor for a displayed universal arrow.
2. LocallyContrWeakEquivalences:
   A make constructor for a displayed universal arrow in terms of weak equivalences.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.TotalAdjunction.

Require Import UniMath.CategoryTheory.WeakEquivalences.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Import DispBicat.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.

Local Open Scope cat.

Section LocallyContr.

  Let UnivCat := bicat_of_univ_cats.
  Let Cat := bicat_of_cats.
  Let R := univ_cats_to_cats.

  Context (D : disp_bicat Cat)
    (HD : disp_2cells_iscontr D)
    (LUR : left_universal_arrow R).

  Let D' := (disp_bicat_on_cat_to_univ_cat D).

  Let RR := (disp_psfunctor_on_cat_to_univ_cat D
               (disp_2cells_isaprop_from_disp_2cells_iscontr _ HD)).

  Let LL0 := λ C,  (pr1 (pr1 LUR C)).

  Context (LL : ∏ C : category, D C → D (LL0 C)).
  Context (ηη :  ∏ (C : category) (CC : D C), CC -->[ (pr12 LUR) C] LL C CC).
  Context (extension_preserve_structure :
            ∏ (C1 : category) (CC1 : pr1 D C1) (C2 : univalent_category) (CC2 : D (pr1 C2))
              (F : C1 ⟶ pr1 C2),
              CC1 -->[F] CC2 → LL C1 CC1 -->[ right_adjoint ((pr22 LUR) C1 C2) F] CC2).

  Definition make_disp_left_universal_arrow_if_contr_CAT
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_univ_arrow_if_contr.
    - exact (disp_2cells_iscontr_disp_bicat_on_cat_to_univ_cat _ HD).
    - exact HD.
    - exact LL.
    - exact ηη.
    - exact extension_preserve_structure.
  Defined.

End LocallyContr.

Section LocallyContrWeakEquivalences.

  Let UnivCat := bicat_of_univ_cats.
  Let Cat := bicat_of_cats.
  Let R := univ_cats_to_cats.

  Context (D : disp_bicat Cat)
    (HD : disp_2cells_iscontr D)
    (LUR : left_universal_arrow R).

  Let D' := (disp_bicat_on_cat_to_univ_cat D).

  Let RR := (disp_psfunctor_on_cat_to_univ_cat D (disp_2cells_isaprop_from_disp_2cells_iscontr _ HD)).

  Let LL0 : bicat_of_cats → category := λ C,  (pr1 (pr1 LUR C)).
  Let LL0' : bicat_of_cats → univalent_category := λ C,  pr1 LUR C.

  Let η := (pr12 LUR).

  Context (η_weak_equiv : ∏ C : category, is_weak_equiv (η C)).
  Context (weak_equiv_preserve_struct
            : ∏ (C1 C2 : category) (H : is_univalent C2) (F : C1 ⟶ C2),
              is_weak_equiv F -> D C1 -> D C2).
  Context (η_preserves_structs : ∏ (C : category) (CC : D C),
              CC -->[η C] weak_equiv_preserve_struct C (LL0 C) (pr2 (pr1 LUR C))
                (η C) (η_weak_equiv C) CC).

  Context (extension_preserves_struct
            : ∏ (C1 : category) (C2 C3 : univalent_category)
                (F : C1 ⟶ C3) (G : C1 ⟶ C2) (H : C2 ⟶ C3)
                (n : nat_z_iso (G ∙ H) F)
                (CC1 : D C1) (CC2 : D (pr1 C2)) (CC3 : D (pr1 C3)),
              is_weak_equiv G -> CC1 -->[ F ] CC3 -> CC2 -->[ H ] CC3).

  Definition make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv
    : disp_left_universal_arrow LUR RR.
  Proof.
    use make_disp_left_universal_arrow_if_contr_CAT.
    - intros C CC.
      use (weak_equiv_preserve_struct _ _ _ (η C)).
      + apply (pr1 LUR C).
      + apply η_weak_equiv.
      + exact CC.
    - exact η_preserves_structs.
    - intros C1 CC1 C2 CC2 F FF.
      use (extension_preserves_struct C1 (LL0' C1) C2 F (η C1) _ _ CC1).
      + set (t := counit_nat_z_iso_from_adj_equivalence_of_cats (pr22 LUR C1 C2)).
        set (tg := nat_z_iso_pointwise_z_iso t F).
        exact (nat_z_iso_from_z_iso (homset_property _) tg).
      + apply η_weak_equiv.
      + exact FF.
  Defined.

End LocallyContrWeakEquivalences.
