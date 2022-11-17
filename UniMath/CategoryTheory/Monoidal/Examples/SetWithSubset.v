(*
In this file we construct the category whose objects are pairs, consisting of a set and a subset of that set, as a displayed category.
Furthermore, we show that this displayed category is monoidal
and we construct a monoidal section which maps a set X to (X,X) (where the second X is considered to be maximal subset of X).
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalSectionsWhiskered.

Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Monoidal.CartesianMonoidalCategoriesWhiskered.

Section SetWithSubset.

  Local Definition setsubtype (X : HSET) : UU := hsubtype (pr1 X).

  Definition SS_disp_cat_ob_mor : disp_cat_ob_mor hset_category.
  Proof.
    use tpair.
    - exact (λ X, setsubtype X).
    - exact (λ _ _ U V f, hsubtype_preserving U V f).
  Defined.

  Definition SS_disp_cat_data : disp_cat_data hset_category.
  Proof.
    exists SS_disp_cat_ob_mor.
    use tpair.
    - intro ; intro.
      apply id_hsubtype_preserving.
    - intros ? ? ? ? ? ? ? ? fsp gsp.
      apply (comp_hsubtype_preserving fsp gsp).
  Defined.

  Definition SS_disp_cat_axioms : disp_cat_axioms hset_category SS_disp_cat_data.
  Proof.
    repeat split; cbn; intros; try (apply proofirrelevance, isaprop_hsubtype_preserving).
    apply isasetaprop. apply isaprop_hsubtype_preserving.
  Defined.

  Definition SS_disp_cat : disp_cat hset_category
    := SS_disp_cat_data ,, SS_disp_cat_axioms.

  Definition total_subset_section_data : section_disp_data SS_disp_cat.
  Proof.
    exists (λ X, totalsubtype (pr1 X)).
    intro ; intros.
    apply total_hsubtype_preserving.
  Defined.

  Definition total_subset_section_axioms : section_disp_axioms total_subset_section_data.
  Proof.
    use tpair.
    - intro ; repeat (apply funextsec ; intro) ; apply totalsubtype.
    - intro ; intros ; repeat (apply funextsec ; intro) ; apply totalsubtype.
  Qed.

  Definition total_subset_section : section_disp SS_disp_cat
    := total_subset_section_data ,, total_subset_section_axioms.

End SetWithSubset.

Section SetWithSubsetMonoidal.

  Definition SS_disp_cat_tensor_data
    : disp_bifunctor_data SET_cartesian_monoidal SS_disp_cat SS_disp_cat SS_disp_cat.
  Proof.
    exists (λ _ _ U V, subtypesdirprod U V).
    split.
    - intros X Y1 Y2 g Ux U1 U2 gsp.
      intros xy2 xy1_prop.
      use (factor_through_squash _ _ xy1_prop).
      { apply subtypesdirprod. }
      intro xy1.
      split.
      + rewrite (! pr12 xy1).
        exact (pr122 xy1).
      + simpl in *.
        apply (gsp _).
        apply hinhpr.
        exists (pr21 xy1).
        split.
        * rewrite (! pr12 xy1).
          apply idpath.
        * exact (pr222 xy1).
    - intros X1 X2 Y f U1 U2 Uy fsp.
      intros x2y x1y_prop.
      use (factor_through_squash _ _ x1y_prop).
      { apply subtypesdirprod. }
      intro x1y.
      split.
      + simpl in *.
        apply (fsp _).
        apply hinhpr.
        exists (pr11 x1y).
        split.
        * rewrite (! pr12 x1y).
          apply idpath.
        * exact (pr122 x1y).
      + rewrite (! pr12 x1y).
        exact (pr222 x1y).
  Defined.

  Lemma SS_disp_cat_tensor_laws : is_disp_bifunctor SS_disp_cat_tensor_data.
  Proof.
    repeat split; red; intros; apply isaprop_hsubtype_preserving.
  Qed.

  Definition SS_disp_cat_tensor : disp_tensor SS_disp_cat SET_cartesian_monoidal
    := SS_disp_cat_tensor_data,, SS_disp_cat_tensor_laws.

  Definition SS_disp_monoidal_data : disp_monoidal_data SS_disp_cat SET_cartesian_monoidal.
  Proof.
    exists (SS_disp_cat_tensor).
    exists (totalsubtype (pr1 unitHSET)).
    repeat (use tpair).
    - intros X U x xinU_prop.
      use (factor_through_squash _ _ xinU_prop).
      { apply U. }
      intro xinU.
      rewrite (! pr12 xinU).
      exact (pr222 xinU).
    - intros X U x xinU_prop.
      exists tt.
      use (factor_through_squash _ _ xinU_prop).
      { apply U. }
      intro xinU.
      rewrite (! pr12 xinU).
      exact (pr22 xinU).
    - intros X U x xinU_prop.
      use (factor_through_squash _ _ xinU_prop).
      { apply U. }
      intro xinU.
      rewrite (! pr12 xinU).
      exact (pr122 xinU).
    - intros X U x xinU_prop.
      refine (_ ,, tt).
      use (factor_through_squash _ _ xinU_prop).
      { apply U. }
      intro xinU.
      rewrite (! pr12 xinU).
      exact (pr22 xinU).
    - intros X Y Z U V W xyz xyzinUVW_prop.
      use (factor_through_squash _ _ xyzinUVW_prop).
      {
        repeat (apply isapropdirprod).
        + apply U.
        + apply V.
        + apply W.
      }
      intro xyzinUVW.
      rewrite (! pr12 xyzinUVW).
      repeat split ; apply (pr22 xyzinUVW).
    - intros X Y Z U V W xyz xyzinUVW_prop.
      use (factor_through_squash _ _ xyzinUVW_prop).
      {
        repeat (apply isapropdirprod).
        + apply U.
        + apply V.
        + apply W.
      }
      intro xyzinUVW.
      rewrite (! pr12 xyzinUVW).
      repeat split ; apply (pr22 xyzinUVW).
  Defined.

  Definition SS_disp_monoidal_laws : disp_monoidal_laws (SS_disp_monoidal_data).
  Proof.
    repeat split ; try (intro ; intros) ; apply isaprop_hsubtype_preserving.
  Qed.

  Definition SS_disp_monoidal : disp_monoidal SS_disp_cat SET_cartesian_monoidal
    := SS_disp_monoidal_data,, SS_disp_monoidal_laws.

  Definition total_subset_section_monoidal_data : smonoidal_data SET_cartesian_monoidal SS_disp_monoidal total_subset_section .
  Proof.
    use tpair.
    - exact (λ _ _ _ _, tt).
    - exact (λ _ _, tt).
  Defined.

  Definition total_subset_section_monoidal_ax : smonoidal_laxlaws _ _ total_subset_section_monoidal_data.
  Proof.
    repeat split ; repeat (intro ; intros ; apply isaprop_hsubtype_preserving).
  Qed.

  Definition total_subset_section_monoidal_lax : smonoidal_lax SET_cartesian_monoidal SS_disp_monoidal total_subset_section
    := total_subset_section_monoidal_data,, total_subset_section_monoidal_ax.

  Definition total_subset_section_monoidal : smonoidal SET_cartesian_monoidal SS_disp_monoidal total_subset_section.
  Proof.
    exists (total_subset_section_monoidal_lax).
    use tpair.
    - intros X Y.
      repeat (use tpair) ; repeat (apply isaprop_hsubtype_preserving).
      exists tt.
      exact tt.
    - repeat (use tpair) ; repeat (apply isaprop_hsubtype_preserving).
      exact (λ _ _, tt).
  Defined.

End SetWithSubsetMonoidal.
