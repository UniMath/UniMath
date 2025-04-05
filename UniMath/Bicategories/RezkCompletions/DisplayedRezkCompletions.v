(**
   The (universal property of the) Rezk completion for categories is equivalent to the following statement:
   "The inclusion of the (full sub)bicategory CAT_univ of univalent categories into all categories has a left biadjoint."

   Let D be a (locally contractible) displayed bicategory over CAT, encoding a "structure on categories".
   Denote by D_univ the restriction of D to CAT_univ.
   In this file, we give sufficient conditions on D such that the left biadjoint lifts to a left biadjoint of the inclusion ∫ D_univ → ∫ D, in terms of weak equivalences.
   In particular, the conditions are independent of an implementation/construction of the Rezk completion.

   - The lifting of the left biadjoint is defined in [cat_with_structure_has_RezkCompletion].
   - The conditions are bundled into [cat_with_struct_has_RC].
   - The proof that these conditions induces a left biadjoint (formalized as a left_universal_arrow) is given in [make_RezkCompletion_from_locally_contractible].

   Remark:
   The definition of [cat_with_struct_has_RC] allows for a modular lifting, when stacking displayed bicategories (see [MakeRezkCompletionsForSigma, MakeRezkCompletionsForBinProd].)

 **)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.
Import DispBicat.Notations.

Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.

Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

Local Open Scope cat.

Section CategoriesWithStructureAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats).

  Definition cat_with_structure_has_disp_RezkCompletion
    (D : disp_bicat bicat_of_cats) : UU
    := ∑ (D_prop : disp_2cells_isaprop D), disp_left_universal_arrow LUR (disp_psfunctor_on_cat_to_univ_cat _ D_prop).

  Definition cat_with_structure_has_RezkCompletion
    (D : disp_bicat bicat_of_cats) : UU
    := ∑ (D_prop : disp_2cells_isaprop D),
      left_universal_arrow (total_psfunctor _ _ _ (disp_psfunctor_on_cat_to_univ_cat _ D_prop)).

  Lemma cat_with_structure_has_disp_RezkCompletion_to_total_RezkCompletion
    (D : disp_bicat bicat_of_cats)
    (D_RC : cat_with_structure_has_disp_RezkCompletion D)
    : cat_with_structure_has_RezkCompletion D.
  Proof.
    exists (pr1 D_RC).
    apply (total_left_universal_arrow LUR).
    exact (pr2 D_RC).
  Defined.

End CategoriesWithStructureAdmitRezkCompletions.

Section MakeRezkCompletionsFromLocallyContractible.

  Context {LUR : left_universal_arrow univ_cats_to_cats}
    (LUR_weq : ∏ C : category, is_weak_equiv ((pr12 LUR) C)).
  Context (D : disp_bicat bicat_of_cats).

  Let RC : bicat_of_cats → category := λ C,  (pr1 (pr1 LUR C)).
  Let η := pr12 LUR.

  Definition cat_with_struct_has_RC : UU
    := ∑ (ax1 : ∏ (C1 C2 : category) (H : is_univalent C2) (F : C1 ⟶ C2),
             is_weak_equiv F -> D C1 -> D C2)
         (ax2 : ∏ (C : category) (CC : D C),
              CC -->[η C] ax1 _ (RC C) (pr2 (pr1 LUR C))
                (η C) (LUR_weq C) CC),
      ∏ (C1 : category) (C2 C3 : univalent_category)
                (F : C1 ⟶ C3) (G : C1 ⟶ C2) (H : C2 ⟶ C3)
                (n : nat_z_iso (G ∙ H) F)
                (CC1 : D C1) (CC2 : D (pr1 C2)) (CC3 : D (pr1 C3)),
      is_weak_equiv G -> CC1 -->[ F ] CC3 -> CC2 -->[ H ] CC3.

  Context (D_RC : cat_with_struct_has_RC).

  Definition cat_with_struct_has_RC_transport_weak_equiv
    {C1 C2 : category} (H : is_univalent C2) {F : C1 ⟶ C2}
    (F_weq : is_weak_equiv F)
    : D C1 -> D C2
    := pr1 D_RC _ _ H _ F_weq.

  Definition cat_with_struct_has_RC_weak_equiv_preserves_struct
    {C : category} (CC : D C)
    : CC -->[ (pr12 LUR) C]
        cat_with_struct_has_RC_transport_weak_equiv (pr2 (pr1 LUR C)) (LUR_weq C) CC
    := pr12 D_RC _ CC.

  Definition cat_with_struct_has_RC_lift_struct_along_weak_equiv
    {C1 : category} (C2 C3 : univalent_category)
    {F : C1 ⟶ C3} {G : C1 ⟶ C2} {H : C2 ⟶ C3}
    (n : nat_z_iso (G ∙ H) F)
    (CC1 : D C1) (CC2 : D (pr1 C2)) (CC3 : D (pr1 C3))
    (G_weq : is_weak_equiv G)
    : CC1 -->[ F ] CC3 -> CC2 -->[ H ] CC3
    := pr22 D_RC _ C2 C3 _ _ _ n CC1 CC2 CC3 G_weq.

  Corollary make_RezkCompletion_from_locally_contractible
    (D_contr : disp_2cells_iscontr D)
    : cat_with_structure_has_RezkCompletion D.
  Proof.
    apply (cat_with_structure_has_disp_RezkCompletion_to_total_RezkCompletion LUR).
    exists (disp_2cells_isaprop_from_disp_2cells_iscontr _ D_contr).
    use make_disp_left_universal_arrow_if_contr_CAT_from_weak_equiv.
    - exact LUR_weq.
    - exact (λ _ _ C2_univ _ F_weq, cat_with_struct_has_RC_transport_weak_equiv C2_univ F_weq).
    - exact (λ _ C, cat_with_struct_has_RC_weak_equiv_preserves_struct C).
    - exact (λ _ C2 C3 _ _ _ n CC1 CC2 CC3 G_weq,
              cat_with_struct_has_RC_lift_struct_along_weak_equiv C2 C3 n CC1 CC2 CC3 G_weq).
  Defined.

End MakeRezkCompletionsFromLocallyContractible.

Section MakeRezkCompletionsForSigma.

  Context {LUR : left_universal_arrow univ_cats_to_cats}
    (LUR_weq : ∏ C : category, is_weak_equiv ((pr12 LUR) C)).

  Context {D : disp_bicat bicat_of_cats} (E : disp_bicat (total_bicat D)).
  Context (D_RC : cat_with_struct_has_RC LUR_weq D).

  Let LL0 : bicat_of_cats → category := λ C,  (pr1 (pr1 LUR C)).
  Let η := pr12 LUR.

  Context (weak_equiv_preserve_struct
            : ∏ (C1 C2 : category) (H : is_univalent C2) (F : C1 ⟶ C2) (F_weq : is_weak_equiv F),
              ∏ d : D C1, E (C1 ,, d) → E (C2,, cat_with_struct_has_RC_transport_weak_equiv LUR_weq D D_RC H F_weq d)).

  Context (η_preserves_structs : ∏ (C : category) (d : D C) (e : E (C,,d)),
              e -->[η C ,, cat_with_struct_has_RC_weak_equiv_preserves_struct LUR_weq D D_RC d]
                (weak_equiv_preserve_struct C (pr1 (pr1 LUR C)) (pr2 (pr1 LUR C)) ((pr12 LUR) C)
    (LUR_weq C) d e)).

  Context (extension_preserves_struct
            : ∏ (C1 : category) (C2 C3 : univalent_category)
                (F : C1 ⟶ C3) (G : C1 ⟶ C2) (H : C2 ⟶ C3)
                (n : nat_z_iso (G ∙ H) F)
                (d1 : D C1) (e1 : E (C1,, d1))
                (d2 : D (pr1 C2)) (e2 : E (pr1 C2,, d2))
                (d3 : D (pr1 C3)) (e3 : E (pr1 C3,, d3))
                (G_weq : is_weak_equiv G)
                (f_D : d1 -->[ F] d3)
                (f_E : e1 -->[ F,, f_D] e3),
              e2 -->[H,, cat_with_struct_has_RC_lift_struct_along_weak_equiv LUR_weq D D_RC C2 C3 n d1 d2 d3 G_weq f_D] e3).

  Lemma make_cat_with_struct_has_RC_from_sigma
    : cat_with_struct_has_RC LUR_weq (sigma_bicat _ _ E).
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C1 C2 C2_univ F F_weq.
      intros [d e].
      exists (cat_with_struct_has_RC_transport_weak_equiv LUR_weq _ D_RC C2_univ F_weq d).
      apply weak_equiv_preserve_struct.
      exact e.
    - intros C [d e].
      use tpair ; cbn.
      + exact (cat_with_struct_has_RC_weak_equiv_preserves_struct LUR_weq _ D_RC d).
      + apply η_preserves_structs.
    - intros C1 C2 C3 F G H n [d1 e1] [d2 e2] [d3 e3] G_weq.
      intros [f_D f_E].
      use tpair.
      + exact (cat_with_struct_has_RC_lift_struct_along_weak_equiv LUR_weq _ D_RC C2 C3 n d1 d2 d3 G_weq f_D).
      + apply (extension_preserves_struct _ _ _ _ _ _ _ _ e1).
        exact f_E.
  Defined.

  Corollary make_RezkCompletion_from_sigma
    (D_contr : disp_2cells_iscontr D) (E_contr : disp_2cells_iscontr E)
    : cat_with_structure_has_RezkCompletion (sigma_bicat _ _ E).
  Proof.
    use make_RezkCompletion_from_locally_contractible.
    - exact LUR.
    - exact LUR_weq.
    - exact make_cat_with_struct_has_RC_from_sigma.
    - exact (disp_2cells_of_sigma_iscontr D_contr E_contr).
  Defined.

End MakeRezkCompletionsForSigma.

Section MakeRezkCompletionsForBinProd.

  Context {LUR : left_universal_arrow univ_cats_to_cats}
    (LUR_weq : ∏ C : category, is_weak_equiv ((pr12 LUR) C)).

  Context {D₁ D₂ : disp_bicat bicat_of_cats}.

  Context (D₁_RC : cat_with_struct_has_RC LUR_weq D₁).
  Context (D₂_RC : cat_with_struct_has_RC LUR_weq D₂).

  Lemma make_cat_with_struct_has_RC_from_dirprod
    : cat_with_struct_has_RC LUR_weq (disp_dirprod_bicat D₁ D₂).
  Proof.
    simple refine (_ ,, _ ,, _).
    - intros C₁ C₂ C₂_univ F F_weq [d₁ d₂].
      split.
      + exact (cat_with_struct_has_RC_transport_weak_equiv LUR_weq _ D₁_RC C₂_univ F_weq d₁).
      + exact (cat_with_struct_has_RC_transport_weak_equiv LUR_weq _ D₂_RC C₂_univ F_weq d₂).
    - intro ; intro ; split ; apply cat_with_struct_has_RC_weak_equiv_preserves_struct.
    - intros C1 C2 C3 D F H n [d₁ d₂] [d₁' d₂'] [d₁'' d₂''] G_weq [f₁ f₂].
      split.
      + apply (cat_with_struct_has_RC_lift_struct_along_weak_equiv LUR_weq _ D₁_RC C2 C3 n _ _ _ G_weq f₁).
      + apply (cat_with_struct_has_RC_lift_struct_along_weak_equiv LUR_weq _ D₂_RC C2 C3 n _ _ _ G_weq f₂).
  Defined.

  Corollary make_RezkCompletion_from_dirprod
    (D₁_contr : disp_2cells_iscontr D₁) (D₂_contr : disp_2cells_iscontr D₂)
    : cat_with_structure_has_RezkCompletion (disp_dirprod_bicat D₁ D₂).
  Proof.
    use (make_RezkCompletion_from_locally_contractible LUR_weq).
    - apply make_cat_with_struct_has_RC_from_dirprod.
    - apply (disp_2cells_of_dirprod_iscontr D₁_contr D₂_contr).
  Defined.

End MakeRezkCompletionsForBinProd.
