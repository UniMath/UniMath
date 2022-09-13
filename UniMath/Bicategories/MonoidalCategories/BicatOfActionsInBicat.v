(** introduces monoidal actions in a bicategorical setting

    This lifts to bicategories the view on actions as put forward in G. Janelidze and G.M. Kelly: A Note on Actions of a Monoidal Category, Theory and Applications of Categories, Vol. 9, 2001, No. 4, pp 61-91.
    The strength notion for the morphisms between actions is taken from
    B. Ahrens, R. Matthes and A. Mörtberg: Implementing a category-theoretic framework for typed abstract syntax, Proceedings CPP'22.

Authors: Ralph Matthes 2022
 *)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
(*
Require Import UniMath.CategoryTheory.Core.Isos.
*)
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
(*
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
*)
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalSectionsWhiskered.
Require Import UniMath.Bicategories.MonoidalCategories.EndofunctorsWhiskeredMonoidal.
(*
Require Import UniMath.Bicategories.MonoidalCategories.Actions.
Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrength.
*)
Require Import UniMath.Bicategories.MonoidalCategories.WhiskeredMonoidalFromBicategory.
Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrongFunctorsWhiskeredMonoidal.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
(*
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
*)

Import Bicat.Notations.
Import BifunctorNotations.
Import DisplayedBifunctorNotations.

Local Open Scope cat.
Section FixMoncatAndBicat.

  Context {V : category}.
  Context (Mon_V : monoidal V).

  Notation "X ⊗ Y" := (X ⊗_{ Mon_V } Y).

  Context (C : bicat).

  Definition disp_actionbicat_disp_mor {a0 a0' : C}
  {FA : V ⟶ category_from_bicat_and_ob a0}
  (FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA)
  {FA' : V ⟶ category_from_bicat_and_ob a0'}
  (FA'm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0') FA')
  (G : C ⟦ a0, a0' ⟧): UU :=
    ∑ δ : parameterized_distributivity_bicat_nat G,
                param_distr_bicat_triangle_eq Mon_V FAm FA'm G δ ×
                  param_distr_bicat_pentagon_eq Mon_V FAm FA'm G δ.

  Lemma disp_actionbicat_disp_mor_eq {a0 a0' : C}
  {FA : V ⟶ category_from_bicat_and_ob a0}
  {FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA}
  {FA' : V ⟶ category_from_bicat_and_ob a0'}
  {FA'm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0') FA'}
  {G : C ⟦ a0, a0' ⟧}
  (pm1 pm2: disp_actionbicat_disp_mor FAm FA'm G):
    pr1 pm1 = pr1 pm2 -> pm1 = pm2.
  Proof.
    intro Hyp.
    apply subtypePath.
    - intro δ. apply isapropdirprod.
      + apply isaprop_param_distr_bicat_triangle_eq.
      + apply isaprop_param_distr_bicat_pentagon_eq.
    - exact Hyp.
  Qed.

  Definition disp_actionbicat_disp_ob_mor : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - intro a0.
      exact (∑ FA: functor V (category_from_bicat_and_ob a0),
                fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA).
    - intros a0 a0' [FA FAm] [FA' FA'm] G.
      exact (disp_actionbicat_disp_mor FAm FA'm G).
  Defined.

  Definition disp_actionbicat_disp_id_comp : disp_cat_id_comp C disp_actionbicat_disp_ob_mor.
  Proof.
    split.
    - intros a [FA FAm].
      use tpair.
      + red.
        use make_nat_trans.
        * intro v. cbn. exact (lunitor _ • rinvunitor _).
        * abstract ( intros v w f;
          cbn;
          rewrite hcomp_identity_left;
          rewrite hcomp_identity_right;
          rewrite vassocr;
          rewrite vcomp_lunitor;
          do 2 rewrite vassocl;
          apply maponpaths;
          apply pathsinv0, (rhs_right_inv_cell _ _ _ (is_invertible_2cell_runitor _));
          rewrite vassocl;
          rewrite vcomp_runitor;
          rewrite vassocr;
          rewrite rinvunitor_runitor;
          apply id2_left ).
      + split; red; cbn.
        * rewrite vassocr.
          rewrite vcomp_lunitor.
          do 2 rewrite vassocl.
          rewrite lunitor_id_is_left_unit_id.
          apply maponpaths.
          apply pathsinv0, (rhs_right_inv_cell _ _ _ (is_invertible_2cell_runitor _)).
          rewrite vassocl.
          apply pathsinv0, (rhs_left_inv_cell _ _ _ (is_invertible_2cell_lunitor _)).
          rewrite vcomp_runitor.
          rewrite lunitor_id_is_left_unit_id.
          apply idpath.
        * intros v w.
          unfold param_distr_bicat_pentagon_eq_body, param_distr_bicat_pentagon_eq_body_RHS.
          cbn.
          etrans.
          { rewrite vassocl. apply maponpaths. rewrite vassocr. apply maponpaths_2.
            apply vcomp_lunitor. }
          etrans.
          { repeat rewrite vassocr. apply idpath. }
          apply pathsinv0, (rhs_right_inv_cell _ _ _ (is_invertible_2cell_runitor _)).
          etrans.
          { repeat rewrite vassocl. apply idpath. }
          rewrite vcomp_runitor.
          repeat rewrite vassocr. apply maponpaths_2.
          rewrite <- rwhisker_vcomp.
          rewrite <- lwhisker_vcomp.
          show_id_type.
          rewrite <- runitor_triangle.
          rewrite <- lunitor_triangle.
          etrans.
          2: { rewrite vassocr.
               rewrite rassociator_lassociator.
               apply pathsinv0, id2_left. }
          etrans.
          { repeat rewrite vassocr. apply maponpaths_2.
            repeat rewrite vassocl. rewrite lassociator_rassociator.
            rewrite id2_right. apply idpath. }
          repeat rewrite vassocl.
          etrans.
          { do 4 apply maponpaths.
            rewrite lwhisker_vcomp.
            rewrite rinvunitor_runitor.
            apply lwhisker_id2. }
          rewrite id2_right.
          etrans.
          2: { apply id2_right. }
          apply maponpaths.
          rewrite lunitor_lwhisker.
          rewrite rwhisker_vcomp.
          rewrite rinvunitor_runitor.
          apply id2_rwhisker.
    - intros a0 a1 a2 g1 g2 [FA FAm] [FA' FA'm] [FA'' FA''m] Hyp1 Hyp2.
      use tpair.
      + red.
        use make_nat_trans.
        * intro v. cbn.
          exact (rassociator g1 g2 (FA'' v)
                   • ((g1 ◃ (pr1 Hyp2 v))
                   • ((lassociator g1 (FA' v) g2
                   • ((pr1 Hyp1 v) ▹ g2) : g1 · H' g2 v ==> FA v · g1 · g2)
                  • rassociator (FA v) g1 g2))).
          (* refine (vcomp2 _ _).
          { apply rassociator. }
          refine (vcomp2 _ _).
          { apply lwhisker.
            apply Hyp2. }
          refine (vcomp2 _ _).
          2: { apply rassociator. }
          cbn.
          refine (vcomp2 _ _).
          { apply lassociator. }
          apply rwhisker.
          apply Hyp1. *)
        * intros v w f;
          cbn;
          rewrite hcomp_identity_left;
          rewrite hcomp_identity_right;
          rewrite vassocr.
          admit.
      + split; red; cbn.
        * admit.
        * intros v w.
          unfold param_distr_bicat_pentagon_eq_body, param_distr_bicat_pentagon_eq_body_RHS.
          cbn.
          admit.
  Abort.

End FixMoncatAndBicat.
