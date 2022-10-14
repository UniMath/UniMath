(** introduces monoidal actions in a bicategorical setting

    This lifts to bicategories the view on actions as put forward in G. Janelidze and G.M. Kelly: A Note on Actions of a Monoidal Category, Theory and Applications of Categories, Vol. 9, 2001, No. 4, pp 61-91.
    The strength notion for the morphisms between actions is taken from
    B. Ahrens, R. Matthes and A. Mörtberg: Implementing a category-theoretic framework for typed abstract syntax, Proceedings CPP'22.

Authors: Ralph Matthes and Kobe Wullaert 2022
 *)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

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

Require Import UniMath.Bicategories.MonoidalCategories.WhiskeredMonoidalFromBicategory.
Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrongFunctorsWhiskeredMonoidal.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.

Import Bicat.Notations.
Import BifunctorNotations.
Import DisplayedBifunctorNotations.

Local Open Scope cat.
Section FixMoncatAndBicat.

  Context {V : category}.
  Context (Mon_V : monoidal V).

  Notation "X ⊗ Y" := (X ⊗_{ Mon_V } Y).

  Context (B : bicat).

  Definition disp_actionbicat_disp_mor {a0 a0' : B}
  {FA : V ⟶ category_from_bicat_and_ob a0}
  (FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA)
  {FA' : V ⟶ category_from_bicat_and_ob a0'}
  (FA'm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0') FA')
  (G : B ⟦ a0, a0' ⟧): UU :=
    ∑ δ : parameterized_distributivity_bicat_nat G,
                param_distr_bicat_triangle_eq Mon_V FAm FA'm G δ ×
                  param_distr_bicat_pentagon_eq Mon_V FAm FA'm G δ.

  Lemma disp_actionbicat_disp_mor_eq {a0 a0' : B}
  {FA : V ⟶ category_from_bicat_and_ob a0}
  {FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA}
  {FA' : V ⟶ category_from_bicat_and_ob a0'}
  {FA'm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0') FA'}
  {G : B ⟦ a0, a0' ⟧}
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

  Definition disp_actionbicat_disp_ob_mor : disp_cat_ob_mor B.
  Proof.
    use tpair.
    - intro a0.
      exact (∑ FA: functor V (category_from_bicat_and_ob a0),
                fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA).
    - intros a0 a0' [FA FAm] [FA' FA'm] G.
      exact (disp_actionbicat_disp_mor FAm FA'm G).
  Defined.

  Definition disp_actionbicat_disp_id_nat_trans
  {a : B}
  {FA : V ⟶ category_from_bicat_and_ob a}
  (FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a) FA):
    H(V:=V)(FA':=FA) (id₁ a) ⟹ H'(FA:=FA) (id₁ a).
  Proof.
    use make_nat_trans.
    * intro v. cbn. exact (lunitor _ • rinvunitor _).
    * abstract ( intros v w f;
                 cbn;
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
  Defined.

  Lemma disp_actionbicat_disp_id_triangle {a : B}
  {FA : V ⟶ category_from_bicat_and_ob a}
  (FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a) FA):
    param_distr_bicat_triangle_eq Mon_V FAm FAm (id₁ a) (disp_actionbicat_disp_id_nat_trans FAm).
  Proof.
    red; cbn.
    rewrite vassocr.
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
  Qed.

  Lemma disp_actionbicat_disp_id_pentagon {a : B}
    {FA : V ⟶ category_from_bicat_and_ob a}
    (FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a) FA):
    param_distr_bicat_pentagon_eq Mon_V FAm FAm (id₁ a) (disp_actionbicat_disp_id_nat_trans FAm).
  Proof.
    red; cbn.
    intros v w.
    unfold param_distr_bicat_pentagon_eq_body, param_distr_bicat_pentagon_eq_body_RHS.
    cbn.
    etrans.
    { rewrite vassocl. apply maponpaths. rewrite vassocr. apply maponpaths_2.
      apply vcomp_lunitor. }
    etrans.
    { repeat rewrite vassocr. apply idpath. }
    apply pathsinv0, (rhs_right_inv_cell _ _ _ (is_invertible_2cell_runitor _)).
    etrans.
    { rewrite !vassocl. (* instead of repeat rewrite vassocl - hint by Niels van der Weide *) apply idpath. }
    rewrite vcomp_runitor.
    repeat rewrite vassocr. apply maponpaths_2.
    (* now pure bicategorical reasoning *)
    rewrite <- rwhisker_vcomp.
    rewrite <- lwhisker_vcomp.
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
  Qed.

  Definition disp_actionbicat_disp_comp_nat_trans_data {a0 a1 a2 : B}
      {g1 : B ⟦ a0, a1 ⟧}
      {g2 : B ⟦ a1, a2 ⟧}
      {FA : V ⟶ category_from_bicat_and_ob a0}
      {FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA}
      {FA' : V ⟶ category_from_bicat_and_ob a1}
      {FA'm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a1) FA'}
      {FA'' : V ⟶ category_from_bicat_and_ob a2}
      {FA''m : fmonoidal Mon_V (monoidal_from_bicat_and_ob a2) FA''}
      (Hyp1 : disp_actionbicat_disp_mor FAm FA'm g1)
      (Hyp2 : disp_actionbicat_disp_mor FA'm FA''m g2):
    nat_trans_data (H(V:=V)(FA':=FA'') (g1 · g2)) (H'(FA:=FA) (g1 · g2)).
  Proof.
    intro v. cbn.
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
  Defined.

  Lemma disp_actionbicat_disp_comp_is_nat_trans {a0 a1 a2 : B}
    {g1 : B ⟦ a0, a1 ⟧}
    {g2 : B ⟦ a1, a2 ⟧}
    {FA : V ⟶ category_from_bicat_and_ob a0}
    {FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA}
    {FA' : V ⟶ category_from_bicat_and_ob a1}
    {FA'm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a1) FA'}
    {FA'' : V ⟶ category_from_bicat_and_ob a2}
    {FA''m : fmonoidal Mon_V (monoidal_from_bicat_and_ob a2) FA''}
    (Hyp1 : disp_actionbicat_disp_mor FAm FA'm g1)
    (Hyp2 : disp_actionbicat_disp_mor FA'm FA''m g2):
    is_nat_trans _ _ (disp_actionbicat_disp_comp_nat_trans_data Hyp1 Hyp2).
  Proof.
    intros v w f. unfold disp_actionbicat_disp_comp_nat_trans_data.
    cbn; rewrite vassocr.

    rewrite (! lwhisker_lwhisker_rassociator _ _ _ _ _ _ _ _ _).
    rewrite vassocr.
    etrans. {
      apply maponpaths_2.
      rewrite vassocl.
      apply maponpaths.
      exact (lwhisker_vcomp g1  (g2 ◃ # FA'' f) (pr1 Hyp2 w)).
    }

    etrans.
    2: {
      rewrite !vassocr.
      rewrite vassocl.
      apply maponpaths.
      apply rwhisker_rwhisker_alt.
    }

    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    apply maponpaths_2.
    etrans. {
      apply maponpaths_2.
      apply maponpaths_2.
      apply maponpaths.
      exact (pr21 Hyp2 v w f).
    }
    etrans.
    2: {
      rewrite vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      apply maponpaths.
      exact (pr21 Hyp1 v w f).
    }

    cbn.
    rewrite (! lwhisker_vcomp _ _ _).

    do 3 rewrite vassocl.
    apply maponpaths.
    rewrite vassocr.
    etrans.
    2: {
      rewrite (! rwhisker_vcomp _ _ _).
      rewrite vassocr.
      apply idpath.
    }
    apply maponpaths_2.
    apply rwhisker_lwhisker.
  Qed.

  Definition disp_actionbicat_disp_comp_nat_trans {a0 a1 a2 : B}
    {g1 : B ⟦ a0, a1 ⟧}
    {g2 : B ⟦ a1, a2 ⟧}
    {FA : V ⟶ category_from_bicat_and_ob a0}
    {FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA}
    {FA' : V ⟶ category_from_bicat_and_ob a1}
    {FA'm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a1) FA'}
    {FA'' : V ⟶ category_from_bicat_and_ob a2}
    {FA''m : fmonoidal Mon_V (monoidal_from_bicat_and_ob a2) FA''}
    (Hyp1 : disp_actionbicat_disp_mor FAm FA'm g1)
    (Hyp2 : disp_actionbicat_disp_mor FA'm FA''m g2):
    parameterized_distributivity_bicat_nat(V:=V)(FA:=FA)(FA':=FA'') (g1 · g2) :=
    _,, disp_actionbicat_disp_comp_is_nat_trans Hyp1 Hyp2.

  Lemma disp_actionbicat_disp_comp_triangle {a0 a1 a2 : B}
    {g1 : B ⟦ a0, a1 ⟧}
    {g2 : B ⟦ a1, a2 ⟧}
    {FA : V ⟶ category_from_bicat_and_ob a0}
    {FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA}
    {FA' : V ⟶ category_from_bicat_and_ob a1}
    {FA'm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a1) FA'}
    {FA'' : V ⟶ category_from_bicat_and_ob a2}
    {FA''m : fmonoidal Mon_V (monoidal_from_bicat_and_ob a2) FA''}
    (Hyp1 : disp_actionbicat_disp_mor FAm FA'm g1)
    (Hyp2 : disp_actionbicat_disp_mor FA'm FA''m g2):
    param_distr_bicat_triangle_eq Mon_V FAm FA''m (g1 · g2) (disp_actionbicat_disp_comp_nat_trans Hyp1 Hyp2).
  Proof.
    red; cbn.
    unfold disp_actionbicat_disp_comp_nat_trans_data.
    assert (aux1 := pr12 Hyp1).
    assert (aux2 := pr12 Hyp2).
    apply param_distr_bicat_triangle_eq_variant0_follows in aux1.
    apply param_distr_bicat_triangle_eq_variant0_follows in aux2.
    red in aux1, aux2; cbn in aux1, aux2.
    rewrite aux1, aux2.
    clear Hyp1 Hyp2 aux1 aux2.
    unfold param_distr_bicat_triangle_eq_variant0_RHS.
    repeat rewrite <- lwhisker_vcomp.
    repeat rewrite <- rwhisker_vcomp.
    etrans.
    { repeat rewrite lassocr.
      apply maponpaths.
      repeat rewrite vassocr.
      rewrite lwhisker_lwhisker_rassociator.
      apply idpath. }
    etrans.
    { repeat rewrite vassocr.
      do 10 apply maponpaths_2.
      rewrite lwhisker_vcomp.
      apply maponpaths.
      apply (z_iso_inv_after_z_iso (_,,fmonoidal_preservesunitstrongly FA''m)). }
    cbn.
    rewrite lwhisker_id2.
    rewrite id2_left.
    etrans.
    { repeat rewrite vassocl.
      do 3 apply maponpaths.
      repeat rewrite vassocr.
      do 5 apply maponpaths_2.
      apply rwhisker_lwhisker. }
    etrans.
    { repeat rewrite vassocr.
      do 4 apply maponpaths_2.
      repeat rewrite vassocl.
      do 4 apply maponpaths.
      rewrite rwhisker_vcomp.
      rewrite lwhisker_vcomp.
      do 2 apply maponpaths.
      apply (z_iso_inv_after_z_iso (_,,fmonoidal_preservesunitstrongly FA'm)). }
    cbn.
    rewrite lwhisker_id2.
    rewrite id2_rwhisker.
    rewrite id2_right.
    etrans.
    { repeat rewrite vassocl.
      rewrite rwhisker_rwhisker_alt.
      apply idpath. }
    repeat rewrite vassocr.
    apply maponpaths_2.
    (* now pure bicategorical reasoning *)
    rewrite <- runitor_triangle.
    apply (rhs_right_inv_cell _ _ _ (is_invertible_2cell_lunitor _)).
    rewrite <- lunitor_triangle.
    repeat rewrite vassocr.
    etrans.
    { apply maponpaths_2.
      repeat rewrite vassocl.
      rewrite rassociator_lassociator.
      rewrite id2_right.
      apply idpath. }
    etrans.
    { repeat rewrite vassocl.
      rewrite rwhisker_vcomp.
      rewrite linvunitor_lunitor.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath. }
    etrans.
    2: { apply id2_right. }
    repeat rewrite vassocl.
    do 2 apply maponpaths.
    rewrite runitor_rwhisker.
    rewrite lwhisker_vcomp.
    rewrite linvunitor_lunitor.
    apply lwhisker_id2.
  Qed.

  Lemma disp_actionbicat_disp_comp_pentagon {a0 a1 a2 : B}
    {g1 : B ⟦ a0, a1 ⟧}
    {g2 : B ⟦ a1, a2 ⟧}
    {FA : V ⟶ category_from_bicat_and_ob a0}
    {FAm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA}
    {FA' : V ⟶ category_from_bicat_and_ob a1}
    {FA'm : fmonoidal Mon_V (monoidal_from_bicat_and_ob a1) FA'}
    {FA'' : V ⟶ category_from_bicat_and_ob a2}
    {FA''m : fmonoidal Mon_V (monoidal_from_bicat_and_ob a2) FA''}
    (Hyp1 : disp_actionbicat_disp_mor FAm FA'm g1)
    (Hyp2 : disp_actionbicat_disp_mor FA'm FA''m g2):
    param_distr_bicat_pentagon_eq Mon_V FAm FA''m (g1 · g2) (disp_actionbicat_disp_comp_nat_trans Hyp1 Hyp2).
  Proof.
    intros v w.
    red; cbn.
    unfold param_distr_bicat_pentagon_eq_body_RHS,
      disp_actionbicat_disp_comp_nat_trans, disp_actionbicat_disp_comp_nat_trans_data.
    set (aux1 := pr22 Hyp1 v w).
    set (aux2 := pr22 Hyp2 v w).
    apply param_distr_bicat_pentagon_eq_body_variant_follows in aux1.
    apply param_distr_bicat_pentagon_eq_body_variant_follows in aux2.
    red in aux1, aux2; cbn in aux1, aux2.
    rewrite aux1, aux2.
    clear aux1 aux2.
    unfold param_distr_bicat_pentagon_eq_body_variant_RHS, param_distr_bicat_pentagon_eq_body_RHS.
    induction Hyp1 as [δ1 [trieq1 pentaeq1]].
    induction Hyp2 as [δ2 [trieq2 pentaeq2]].
    cbn.
    clear trieq1 trieq2 pentaeq1 pentaeq2.
    repeat rewrite rwhisker_vcomp.
    repeat rewrite <- lwhisker_vcomp.
    etrans.
    { repeat rewrite vassocl.
      apply maponpaths.
      repeat rewrite vassocr.
      do 10 apply maponpaths_2.
      apply pathsinv0, lwhisker_lwhisker_rassociator. }
    etrans.
    { repeat rewrite vassocl.
      do 2 apply maponpaths.
      repeat rewrite vassocr.
      do 9 apply maponpaths_2.
      etrans.
      { rewrite lwhisker_vcomp.
        apply maponpaths.
        rewrite lwhisker_vcomp.
        apply maponpaths.
        apply (pr2 (fmonoidal_preservestensorstrongly FA''m v w)). }
      cbn.
      rewrite lwhisker_id2.
      apply lwhisker_id2.
    }
    rewrite id2_left.
    etrans.
    { repeat rewrite vassocr.
      apply idpath. }
    apply pathsinv0.
    apply (vcomp_move_L_Vp _ _ _ (is_invertible_2cell_lassociator _ _ _)).
    etrans.
    { repeat rewrite vassocl.
      do 8 apply maponpaths.
      apply pathsinv0, rwhisker_rwhisker. }
    repeat rewrite <- rwhisker_vcomp.
    repeat rewrite vassocr.
    apply maponpaths_2.
    etrans.
    2: { do 5 apply maponpaths_2.
         repeat rewrite vassocl.
         do 7 apply maponpaths.
         etrans.
         2: { rewrite vassocr.
              apply maponpaths_2.
              apply pathsinv0, rwhisker_lwhisker. }
         rewrite vassocl.
         apply maponpaths.
         rewrite rwhisker_vcomp.
         apply maponpaths.
         rewrite lwhisker_vcomp.
         apply maponpaths.
         apply pathsinv0, (pr2 (fmonoidal_preservestensorstrongly FA'm v w)). }
    cbn.
    rewrite lwhisker_id2.
    rewrite id2_rwhisker.
    rewrite id2_right.
    (* the equation is now free from the preservation of the tensor by the given strong monoidal functors;
       both sides of the equation are chains of 13 two-cells *)
    etrans.
    2: { repeat rewrite vassocl.
         do 6 apply maponpaths.
         repeat rewrite vassocr.
         do 4 apply maponpaths_2.
         apply pathsinv0, lassociator_lassociator. }
    etrans.
    { repeat rewrite vassocl.
      do 4 apply maponpaths.
      repeat rewrite vassocr.
      do 6 apply maponpaths_2.
      apply rassociator_rassociator. }
    (* both sides of the equation are chains of 12 two-cells *)
    etrans.
    2: { repeat rewrite vassocr.
         do 10 apply maponpaths_2.
         apply rassociator_rassociator. }
    repeat rewrite vassocl.
    apply maponpaths.
    etrans.
    2: { repeat rewrite vassocr.
         do 8 apply maponpaths_2.
         etrans.
         2: { apply maponpaths_2.
              rewrite vassocl.
              etrans.
              2: { apply maponpaths.
                   rewrite lwhisker_vcomp.
                   apply maponpaths.
                   apply pathsinv0, rassociator_lassociator. }
              rewrite lwhisker_id2.
              apply pathsinv0, id2_right. }
         apply pathsinv0, rwhisker_lwhisker_rassociator.
    }
    repeat rewrite vassocl.
    apply maponpaths.
    (* two occurrences of [δ2] vanished *)
    etrans.
    { apply maponpaths.
      repeat rewrite vassocr.
      do 5 apply maponpaths_2.
      rewrite rwhisker_rwhisker_alt.
        rewrite vassocl.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite vassocl.
        apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        apply vcomp_whisker. }
    etrans.
    2: { do 2 apply maponpaths.
         repeat rewrite vassocr.
         do 3 apply maponpaths_2.
         rewrite lwhisker_lwhisker.
         rewrite vassocl.
         rewrite rwhisker_rwhisker.
         apply idpath.
    }
    assert (Haux: (lassociator g1 (FA' v) g2 ▹ FA'' w) • rassociator (g1 · FA' v) g2 (FA'' w) =
                    rassociator g1 (FA' v · g2) (FA'' w) • (g1 ◃ rassociator (FA' v) g2 (FA'' w)) • lassociator g1 (FA' v) (g2 · FA'' w)).
    { etrans.
      2: { rewrite vassocl.
           apply inverse_pentagon_2. }
      apply maponpaths_2.
      apply pathsinv0, hcomp_identity_right. }
    etrans.
    { repeat rewrite vassocr.
      do 8 apply maponpaths_2.
      apply Haux. }
    clear Haux.
    repeat rewrite vassocl.
    do 5 apply maponpaths.
    (* two occurrences of [δ1] and [δ2] vanished
       ten two-cells remain, one occurrence of [δ1] on both sides *)
    assert (Haux2: rassociator (FA v) g1 (FA' w · g2) • (FA v ◃ lassociator g1 (FA' w) g2) =
                     lassociator (FA v · g1) (FA' w) g2 • ((rassociator (FA v) g1 (FA' w) ▹ g2) • rassociator (FA v) (g1 · FA' w) g2)).
    { rewrite <- hcomp_identity_right.
      etrans.
      2: { apply inverse_pentagon_4. }
      rewrite hcomp_identity_left.
      apply idpath.
    }
    etrans.
    { repeat rewrite vassocr.
      do 4 apply maponpaths_2.
      exact Haux2. }
    clear Haux2.
    repeat rewrite vassocl.
    do 2 apply maponpaths.
    etrans.
    { repeat rewrite vassocr.
      do 3 apply maponpaths_2.
      apply rwhisker_lwhisker_rassociator. }
    repeat rewrite vassocl.
    apply maponpaths.
    (* no more [δ1] nor [δ2] *)
    etrans.
    { repeat rewrite vassocr.
      apply maponpaths_2.
      rewrite vassocl.
      apply pathsinv0, inverse_pentagon_2. }
    rewrite vassocl.
    rewrite rassociator_lassociator.
    rewrite hcomp_identity_right.
    apply id2_right.
  Qed.

  Definition disp_actionbicat_disp_id_comp : disp_cat_id_comp B disp_actionbicat_disp_ob_mor.
  Proof.
    split.
    - intros a [FA FAm].
      use tpair.
      + exact (disp_actionbicat_disp_id_nat_trans FAm).
      + split; [apply disp_actionbicat_disp_id_triangle | apply disp_actionbicat_disp_id_pentagon]; assumption.
    - intros a0 a1 a2 g1 g2 [FA FAm] [FA' FA'm] [FA'' FA''m] Hyp1 Hyp2. cbn in Hyp1, Hyp2.
      exists (disp_actionbicat_disp_comp_nat_trans Hyp1 Hyp2).
      + split; [apply disp_actionbicat_disp_comp_triangle | apply ax1]; assumption.
  Defined.

  Definition disp_actionbicat_disp_catdata : disp_cat_data B
    := (disp_actionbicat_disp_ob_mor,,disp_actionbicat_disp_id_comp).

  Definition bidisp_actionbicat_disp_2cell_eq_body
    {a a' : B}
    {f1 f2 : B ⟦ a, a' ⟧}
    (η : f1 ==> f2)
    (FA : V ⟶ category_from_bicat_and_ob a)
    (FA' : V ⟶ category_from_bicat_and_ob a')
    (δ1 : parameterized_distributivity_bicat_nat f1)
    (δ2 : parameterized_distributivity_bicat_nat f2)
    (v : V): UU
    := δ1 v • (FA v ◃ η) = (η ▹ FA' v) • δ2 v.

  Lemma isaprop_bidisp_actionbicat_disp_2cell_eq_body
    {a a' : B}
    {f1 f2 : B ⟦ a, a' ⟧}
    (η : f1 ==> f2)
    (FA : V ⟶ category_from_bicat_and_ob a)
    (FA' : V ⟶ category_from_bicat_and_ob a')
    (δ1 : parameterized_distributivity_bicat_nat f1)
    (δ2 : parameterized_distributivity_bicat_nat f2)
    (v : V): isaprop (bidisp_actionbicat_disp_2cell_eq_body η FA FA' δ1 δ2 v).
  Proof.
    apply B.
  Qed.

  Definition bidisp_actionbicat_disp_2cell_struct : disp_2cell_struct disp_actionbicat_disp_ob_mor.
  Proof.
    intros a a' f1 f2 η [FA FAm] [FA' FA'm] [δ1 [tria1 penta1]] [δ2 [tria2 penta2]].
    exact (∏ v: V, bidisp_actionbicat_disp_2cell_eq_body η FA FA' δ1 δ2 v).
  Defined.

  Lemma isaprop_bidisp_actionbicat_disp_2cell_struct
    {a a' : B}
    {f1 f2 : B ⟦ a, a' ⟧}
    (η : f1 ==> f2)
    {M : disp_actionbicat_disp_catdata a}
    {M' : disp_actionbicat_disp_catdata a'}
    (FM1 : M -->[ f1] M')
    (FM2 : M -->[ f2] M'):
    isaprop (bidisp_actionbicat_disp_2cell_struct a a' f1 f2 η M M' FM1 FM2).
  Proof.
    apply impred.
    intro v.
    apply isaprop_bidisp_actionbicat_disp_2cell_eq_body.
  Qed.

  Definition bidisp_actionbicat_disp_prebicat_1_id_comp_cells
    :  disp_prebicat_1_id_comp_cells B
    := (disp_actionbicat_disp_catdata,, bidisp_actionbicat_disp_2cell_struct).

  Ltac aux_bidisp_actionbicat_disp_prebicat_ops :=
      intros; red; cbn;
      unfold bidisp_actionbicat_disp_2cell_struct, bidisp_actionbicat_disp_2cell_eq_body;
      intro v;
      unfold disp_actionbicat_disp_comp_nat_trans, disp_actionbicat_disp_comp_nat_trans_data;
      cbn; show_id_type.

  Definition actionbicat_ax2 : UU :=
  (∏ (a b c d : B) (f : B ⟦ a, b ⟧) (g : B ⟦ b, c ⟧) (h : B ⟦ c, d ⟧)
  (w : bidisp_actionbicat_disp_prebicat_1_id_comp_cells a)
  (x : bidisp_actionbicat_disp_prebicat_1_id_comp_cells b)
  (y : bidisp_actionbicat_disp_prebicat_1_id_comp_cells c)
  (z : bidisp_actionbicat_disp_prebicat_1_id_comp_cells d) (ff : w -->[ f] x)
  (gg : x -->[ g] y) (hh : y -->[ h] z),
  disp_2cells (rassociator f g h) (ff ;; gg ;; hh) (ff ;; (gg ;; hh)))
 × (∏ (a b c d : B) (f : B ⟦ a, b ⟧) (g : B ⟦ b, c ⟧) (h : B ⟦ c, d ⟧)
    (w : bidisp_actionbicat_disp_prebicat_1_id_comp_cells a)
    (x : bidisp_actionbicat_disp_prebicat_1_id_comp_cells b)
    (y : bidisp_actionbicat_disp_prebicat_1_id_comp_cells c)
    (z : bidisp_actionbicat_disp_prebicat_1_id_comp_cells d) (ff : w -->[ f] x)
    (gg : x -->[ g] y) (hh : y -->[ h] z),
    disp_2cells (lassociator f g h) (ff ;; (gg ;; hh)) (ff ;; gg ;; hh))
   × (∏ (a b : B) (f g h : B ⟦ a, b ⟧) (r : f ==> g) (s : g ==> h)
      (x : bidisp_actionbicat_disp_prebicat_1_id_comp_cells a)
      (y : bidisp_actionbicat_disp_prebicat_1_id_comp_cells b) (ff : x -->[ f] y)
      (gg : x -->[ g] y) (hh : x -->[ h] y),
      disp_2cells r ff gg → disp_2cells s gg hh → disp_2cells (r • s) ff hh)
     × (∏ (a b c : B) (f : B ⟦ a, b ⟧) (g1 g2 : B ⟦ b, c ⟧) (r : g1 ==> g2)
        (x : bidisp_actionbicat_disp_prebicat_1_id_comp_cells a)
        (y : bidisp_actionbicat_disp_prebicat_1_id_comp_cells b)
        (z : bidisp_actionbicat_disp_prebicat_1_id_comp_cells c) (ff : x -->[ f] y)
        (gg1 : y -->[ g1] z) (gg2 : y -->[ g2] z),
        disp_2cells r gg1 gg2 → disp_2cells (f ◃ r) (ff ;; gg1) (ff ;; gg2))
       × (∏ (a b c : B) (f1 f2 : B ⟦ a, b ⟧) (g : B ⟦ b, c ⟧) (r : f1 ==> f2)
          (x : bidisp_actionbicat_disp_prebicat_1_id_comp_cells a)
          (y : bidisp_actionbicat_disp_prebicat_1_id_comp_cells b)
          (z : bidisp_actionbicat_disp_prebicat_1_id_comp_cells c) (ff1 : x -->[ f1] y)
          (ff2 : x -->[ f2] y) (gg : y -->[ g] z),
         disp_2cells r ff1 ff2 → disp_2cells (r ▹ g) (ff1 ;; gg) (ff2 ;; gg)).

  Context (ax2 : actionbicat_ax2).

  Lemma bidisp_actionbicat_disp_prebicat_ops :
    disp_prebicat_ops bidisp_actionbicat_disp_prebicat_1_id_comp_cells.
  Proof.
    split; [| split; [| split ; [| split ; [| split]]]].
    (*repeat split; intros; red ; cbn;
      unfold bidisp_actionbicat_disp_2cell_struct, bidisp_actionbicat_disp_2cell_eq_body;
      intro v;
      unfold disp_actionbicat_disp_comp_nat_trans, disp_actionbicat_disp_comp_nat_trans_data;
      cbn; show_id_type. *)
    - aux_bidisp_actionbicat_disp_prebicat_ops. rewrite lwhisker_id2. rewrite id2_right.
      rewrite id2_rwhisker. apply pathsinv0, id2_left.
    - aux_bidisp_actionbicat_disp_prebicat_ops. rewrite <- rwhisker_vcomp.
      etrans.
      { repeat rewrite vassocl. do 5 apply maponpaths.
        apply lunitor_lwhisker. }
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      rewrite vassocr.
      apply maponpaths_2.
      apply (lhs_left_invert_cell _ _ _ (is_invertible_2cell_rassociator _ _ _)).
      cbn.
      apply pathsinv0, lunitor_triangle.
    - aux_bidisp_actionbicat_disp_prebicat_ops. rewrite <- lwhisker_vcomp.
      etrans.
      {
        repeat rewrite vassocl.
        do 5 apply maponpaths.
        apply runitor_triangle.
      }

      etrans. {
        do 2 apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        apply rinvunitor_triangle.
      }
      rewrite vcomp_runitor.
      etrans. {
        do 2 apply maponpaths.
        rewrite vassocr.
        rewrite rinvunitor_runitor.
        apply id2_left.
      }
      rewrite vassocr.
      apply maponpaths_2.
      apply lunitor_lwhisker.
    - aux_bidisp_actionbicat_disp_prebicat_ops. etrans.
      2: {
        do 3 apply maponpaths.
        apply maponpaths_2.
        rewrite <- rwhisker_vcomp.
        rewrite vassocr.
        apply maponpaths_2.
        apply (! lunitor_triangle _ _ _ _ _ _).
      }
      etrans.
      2: {
        do 2 apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        rewrite vassocr.
        apply maponpaths_2.
        apply (! vcomp_lunitor _ _ _).
      }

      rewrite vassocr.
      rewrite <- linvunitor_assoc.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      rewrite vassocl.
      apply maponpaths.
      rewrite (! hcomp_identity_right _ _ _ _).
      rewrite (! hcomp_identity_left _ _ _ _).
      apply triangle_r_inv.
    - aux_bidisp_actionbicat_disp_prebicat_ops. rewrite <- lwhisker_vcomp.
      etrans.
      2: {
        apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        rewrite vassocr.
        apply maponpaths_2.
        apply (! lunitor_lwhisker _ _).
      }
      (* Search (lassociator _ _ (id₁ _)). *)
      etrans.
      2: {
        apply maponpaths.
        rewrite vassocl.
        apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        rewrite vassocr.
        apply maponpaths_2.
        apply (! rinvunitor_triangle  _ _ _ _ _ _).
      }
      rewrite vassocr.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite left_unit_inv_assoc.
      rewrite vassocr.
      apply maponpaths_2.
      rewrite rinvunitor_natural.
      apply maponpaths.
      apply hcomp_identity_right.
    - exact ax2.

  (* probably not useful for 10th goal after splitting:
      induction x as [FA FAm].
      induction y as [FA' FA'm].
      induction f' as [δ [tria penta]].
      cbn.
      red in tria, penta. unfold param_distr_bicat_pentagon_eq_body in penta.
      (* assert (δnat := pr2 δ). red in δnat.
      unfold H, H' in δnat. cbn in δnat.
      rewrite hcomp_identity_left in δnat; rewrite hcomp_identity_right in δnat. *)
       *)

  Qed.

  Definition bidisp_actionbicat_disp_prebicat_data : disp_prebicat_data B
    := (bidisp_actionbicat_disp_prebicat_1_id_comp_cells,, bidisp_actionbicat_disp_prebicat_ops).

  Definition bidisp_actionbicat_disp_prebicat_laws : disp_prebicat_laws bidisp_actionbicat_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isaprop_bidisp_actionbicat_disp_2cell_struct.
  Qed.

  Definition bidisp_actionbicat_disp_prebicat : disp_prebicat B
    := (bidisp_actionbicat_disp_prebicat_data,,bidisp_actionbicat_disp_prebicat_laws).

  Definition bidisp_actionbicat_disp_bicat : disp_bicat B.
  Proof.
    refine (bidisp_actionbicat_disp_prebicat,, _).
    intros a a' f1 f2 η M M' FM1 FM2.
    apply isasetaprop.
    apply isaprop_bidisp_actionbicat_disp_2cell_struct.
  Defined.

  Lemma actionbicat_disp_2cells_isaprop : disp_2cells_isaprop bidisp_actionbicat_disp_bicat.
  Proof.
    red.
    intros.
    apply isaprop_bidisp_actionbicat_disp_2cell_struct.
  Qed.

  Definition bicatactionbicat : bicat := total_bicat bidisp_actionbicat_disp_bicat.

  Lemma actionbicat_disp_locally_groupoid : disp_locally_groupoid bidisp_actionbicat_disp_bicat.
  Proof.
    red. intros a a' f1 f2 ηinvertible [FA FAm] [FA' FA'm] [δ1 [tria1 penta1]] [δ2 [tria2 penta2]] is2cell.
    use tpair.
    - red. cbn. red. intro v. red.
      transparent assert (invertible1 : (invertible_2cell (FA v · f2) (FA v · f1))).
      { use make_invertible_2cell.
        - exact (FA v ◃ ηinvertible ^-1).
        - is_iso. }
      transparent assert (invertible2 : (invertible_2cell (f2 · FA' v) (f1 · FA' v))).
      { use make_invertible_2cell.
        - exact (ηinvertible ^-1 ▹ FA' v).
        - is_iso. }
      apply (lhs_right_invert_cell _ _ _ invertible1).
      rewrite vassocl.
      apply pathsinv0, (lhs_left_invert_cell _ _ _ invertible2).
      exact (is2cell v).
    - split; apply isaprop_bidisp_actionbicat_disp_2cell_struct.
  Qed.

End FixMoncatAndBicat.
