(* ----------------------------------------------------------------------------------- *)
(** ** Trivial display.

   Every bicategory is, in a trivial way, a displayed bicategory over any other
   bicategory.                                                                         *)
(* ----------------------------------------------------------------------------------- *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.TransportLaws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Import StrictPseudoFunctor.Notations.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Definition idtoiso_2_1_concat
           {C : bicat}
           {X Y : C}
           {f₁ f₂ f₃ : C⟦X,Y⟧}
           (q₁ : f₁ = f₂)
           (q₂ : f₂ = f₃)
  : idtoiso_2_1 _ _ q₁ • idtoiso_2_1 _ _ q₂
    =
    idtoiso_2_1 _ _ (q₁ @ q₂).
Proof.
  induction q₁.
  induction q₂.
  apply id2_right.
Qed.


Section StrictPsFunctorToDispBicat.
  Context {B₁ B₂ : bicat}.
  Variable (F : strict_psfunctor B₁ B₂).

  Definition strict_psfunctor_to_disp_bicat_disp_cat_ob_mor
    : disp_cat_ob_mor B₂.
  Proof.
    use tpair.
    - exact (λ Y, ∑ (X : B₁), F X = Y).
    - exact (λ Y₁ Y₂ Z₁ Z₂ f, ∑ (h : pr1 Z₁ --> pr1 Z₂),
             #F h = idtoiso_2_0 _ _ (pr2 Z₁) · f · idtoiso_2_0 _ _ (!(pr2 Z₂))).
  Defined.

  Definition strict_psfunctor_to_disp_bicat_disp_cat_id_comp
    : disp_cat_id_comp B₂ strict_psfunctor_to_disp_bicat_disp_cat_ob_mor.
  Proof.
    use tpair.
    - cbn ; intros Y X.
      refine (id₁ _ ,, _).
      (*
      refine (!(strict_psfunctor_id F (pr1 X)) @ _).
      induction (pr2 X) ; cbn.
       *)
      apply TODO.
    - cbn ; intros Y₁ Y₂ Y₃ f₁ f₂ X₁ X₂ X₃ h₁ h₂.
      refine (pr1 h₁ · pr1 h₂ ,, _).
      (*
      refine (!(strict_psfunctor_comp F (pr1 h₁) (pr1 h₂)) @ _).
      rewrite (pr2 h₁), (pr2 h₂).
       *)
      apply TODO.
  Defined.

  Definition strict_psfunctor_to_disp_bicat_disp_cat_data
    : disp_cat_data B₂.
  Proof.
    use tpair.
    - exact strict_psfunctor_to_disp_bicat_disp_cat_ob_mor.
    - exact strict_psfunctor_to_disp_bicat_disp_cat_id_comp.
  Defined.

  Definition strict_psfunctor_to_disp_bicat_disp_prebicat_1_id_comp_cells
    : disp_prebicat_1_id_comp_cells B₂.
  Proof.
    use tpair.
    - exact strict_psfunctor_to_disp_bicat_disp_cat_data.
    - intros Y₁ Y₂ f₁ f₂ α X₁ X₂ h₁ h₂.
      exact (∑ (β : pr1 h₁ ==> pr1 h₂),
             ##F β
             =
             (idtoiso_2_1 _ _ (pr2 h₁))
               • ((_ ◃ α) ▹ _)
               • idtoiso_2_1 _ _ (!(pr2 h₂))).
  Defined.

  Definition strict_psfunctor_to_disp_bicat_disp_prebicat_ops
    : disp_prebicat_ops strict_psfunctor_to_disp_bicat_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat use tpair.
    - cbn ; intros Y₁ Y₂ f X₁ X₂ h.
      refine (id₂ _ ,, _).
      abstract (rewrite strict_psfunctor_id2 ;
                rewrite lwhisker_id2, id2_rwhisker, id2_right ;
                rewrite idtoiso_2_1_concat ;
                rewrite pathsinv0r ;
                reflexivity).
    - cbn ; intros Y₁ Y₂ f X₁ X₂ h.
      refine (lunitor _ ,, _).
      rewrite strict_psfunctor_F_lunitor.
      rewrite !vassocl.
      unfold strict_psfunctor_comp_cell, strict_psfunctor_id_cell.
      apply TODO.
    - cbn ; intros Y₁ Y₂ f X₁ X₂ h.
      refine (runitor _ ,, _).
      apply TODO.
    - cbn ; intros Y₁ Y₂ f X₁ X₂ h.
      refine (linvunitor _ ,, _).
      apply TODO.
    - cbn ; intros Y₁ Y₂ f X₁ X₂ h.
      refine (rinvunitor _ ,, _).
      apply TODO.
    - cbn ; intros Y₁ Y₂ Y₃ Y₄ f₁ f₂ f₃ X₁ X₂ X₃ X₄ h₁ h₂ h₃.
      refine (rassociator _ _ _ ,, _).
      apply TODO.
    - cbn ; intros Y₁ Y₂ Y₃ Y₄ f₁ f₂ f₃ X₁ X₂ X₃ X₄ h₁ h₂ h₃.
      refine (lassociator _ _ _ ,, _).
      apply TODO.
    - cbn ; intros Y₁ Y₂ f₁ f₂ f₃ α₁ α₂ Z₁ Z₂ h₁ h₂ h₃ β₁ β₂.
      refine (pr1 β₁ • pr1 β₂ ,, _).
      apply TODO.
    - cbn ; intros Y₁ Y₂ Y₃ f g₁ g₂ α₁ α₂ Z₁ Z₂ h χ₁ χ₂ β.
      refine (pr1 h ◃ pr1 β ,, _).
      apply TODO.
    - cbn ; intros Y₁ Y₂ Y₃ f₁ f₂ g α₁ α₂ Z₁ Z₂ h₁ h₂ χ β.
      refine (pr1 β ▹ pr1 χ ,, _).
      apply TODO.
  Defined.

  Definition strict_psfunctor_to_disp_bicat_disp_prebicat_data
    : disp_prebicat_data B₂.
  Proof.
    use tpair.
    - exact strict_psfunctor_to_disp_bicat_disp_prebicat_1_id_comp_cells.
    - exact strict_psfunctor_to_disp_bicat_disp_prebicat_ops.
  Defined.

  Definition strict_psfunctor_to_disp_bicat_laws
    : disp_prebicat_laws strict_psfunctor_to_disp_bicat_disp_prebicat_data.
  Proof.
    repeat split ; intro ; intros
    ; (apply subtypeEquality ; [ intro ; apply B₂ | ])
    ; cbn
    ; unfold transportb
    ; rewrite pr1_transportf, transportf_const
    ; unfold idfun.
    - apply id2_left.
    - apply id2_right.
    - apply vassocr.
    - apply lwhisker_id2.
    - apply id2_rwhisker.
    - apply lwhisker_vcomp.
    - apply rwhisker_vcomp.
    - apply vcomp_lunitor.
    - apply vcomp_runitor.
    - apply lwhisker_lwhisker.
    - apply rwhisker_lwhisker.
    - apply rwhisker_rwhisker.
    - apply vcomp_whisker.
    - apply lunitor_linvunitor.
    - apply linvunitor_lunitor.
    - apply runitor_rinvunitor.
    - apply rinvunitor_runitor.
    - apply lassociator_rassociator.
    - apply rassociator_lassociator.
    - apply runitor_rwhisker.
    - apply lassociator_lassociator.
  Qed.

  Definition strict_psfunctor_to_disp_bicat_disp_prebicat : disp_prebicat B₂.
  Proof.
    use tpair.
    - exact strict_psfunctor_to_disp_bicat_disp_prebicat_data.
    - exact strict_psfunctor_to_disp_bicat_laws.
  Defined.

  Definition strict_psfunctor_to_disp_bicat_disp_bicat : disp_bicat B₂.
  Proof.
    use tpair.
    - exact strict_psfunctor_to_disp_bicat_disp_prebicat.
    - intros Y₁ Y₂ f₁ f₂ α X₁ X₂ h₁ h₂.
      apply isaset_total2.
      + apply B₁.
      + intro.
        apply isasetaprop.
        apply B₂.
  Defined.
End StrictPsFunctorToDispBicat.
