(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

 Displayed bicategory of contravariant functors into a fixed category K.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Section fix_a_category.
  Local Notation "∁" := bicat_of_cats.

  Variable (K : univalent_category).

  Definition disp_presheaf_cat_ob_mor : disp_cat_ob_mor ∁.
  Proof.
    use tpair.
    + exact (λ c : univalent_category, functor (op_unicat c) K).
    + cbn. intros c d ty ty' f.
      exact (nat_trans ty (functor_composite (functor_opp f) ty')).
  Defined.

  Definition disp_presheaf_cat_data : disp_cat_data ∁.
  Proof.
    exists disp_presheaf_cat_ob_mor.
    use tpair.
    + intros c f.
      set (T:= nat_trans_id (pr1 f) ).
      exact T.
    + intros c d e f g ty ty' ty''.
      intros x y.
      set (T1 := x).
      set (T2 := @pre_whisker
                   (op_unicat c) (op_unicat d) K
                   (functor_opp f) _ _ (y : nat_trans (ty': functor _ _ )  _  )).
      exact (@nat_trans_comp (op_unicat c) K _ _ _ T1 T2 ).
  Defined.

  Definition disp_presheaf_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells bicat_of_cats.
  Proof.
    exists disp_presheaf_cat_data.
    intros c d f g a.
    intros p p'.
    intros x y.
    exact (x = @nat_trans_comp (op_unicat c) K _  _ _ y (post_whisker (op_nt a) p')).
  Defined.

  Definition disp_presheaf_prebicat_ops : disp_prebicat_ops disp_presheaf_prebicat_1_id_comp_cells.
  Proof.
    repeat split; cbn.
    - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
      intro. rewrite (functor_id y). apply pathsinv0, id_right.
    - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
      intro.  rewrite (functor_id y). rewrite id_left, id_right. apply idpath.
    - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
      intro. rewrite (functor_id y). apply idpath.
    - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
      intro. rewrite (functor_id y). rewrite id_left, id_right. apply idpath.
    - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
      intro. rewrite (functor_id y). repeat rewrite id_right. apply idpath.
    - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
      intro. rewrite (functor_id z). rewrite id_right. apply pathsinv0, assoc.
    - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
      intro. rewrite (functor_id z). rewrite id_right. apply assoc.
    - intros. apply nat_trans_eq; try apply (homset_property K).
      intro.
      rewrite X. rewrite X0.
      cbn.
      pose (T:= @functor_comp (op_cat b) _ y).
      rewrite <- assoc.
      rewrite <- T.
      apply idpath.
    - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
      rewrite X.
      intro. apply assoc.
    - intros. apply nat_trans_eq; try apply (homset_property K); cbn.
      rewrite X.
      intros. cbn.
      pose (T:= nat_trans_ax gg).
      cbn in T.
      rewrite <- assoc.
      rewrite T.
      apply assoc.
  Qed.

  Definition disp_presheaf_prebicat_data : disp_prebicat_data ∁
    := _ ,,  disp_presheaf_prebicat_ops.

  Lemma disp_presheaf_prebicat_laws : disp_prebicat_laws disp_presheaf_prebicat_data.
  Proof.
    repeat split; intro;
      intros;
      apply isaset_nat_trans; apply K.
  Qed.

  Definition disp_presheaf_prebicat : disp_prebicat ∁ :=
    (disp_presheaf_prebicat_data,, disp_presheaf_prebicat_laws).

  Lemma has_disp_cellset_disp_presheaf_prebicat
    : has_disp_cellset disp_presheaf_prebicat.
  Proof.
    red. intros.
    unfold disp_2cells.
    cbn.
    apply isasetaprop.
    cbn in *.
    apply isaset_nat_trans.
    apply K.
  Qed.

  Definition disp_presheaf_bicat : disp_bicat ∁
    := (disp_presheaf_prebicat,, has_disp_cellset_disp_presheaf_prebicat).

  Definition disp_presheaves_all_invertible
             {C D : ∁}
             {F G : ∁⟦C, D⟧}
             (α : invertible_2cell F G)
             {CD : disp_presheaf_bicat C}
             {FC : disp_presheaf_bicat D}
             {γF : CD -->[ F] FC}
             {γG : CD -->[ G ] FC}
             (p : disp_2cells α γF γG)
    : is_disp_invertible_2cell α p.
  Proof.
    use tpair.
    - apply nat_trans_eq.
      { apply K. }
      intro x.
      refine (!_).
      refine (maponpaths (λ z, z · _) (nat_trans_eq_pointwise p x) @ _).
      refine (!(assoc _ _ _) @ _).
      refine (maponpaths (λ z, _ · z) (!(functor_comp FC _ _)) @ _).
      etrans.
      {
        do 2 apply maponpaths.
        exact (nat_trans_eq_pointwise (pr222 α) x).
      }
      etrans.
      {
        apply maponpaths.
        apply (functor_id FC).
      }
      apply id_right.
    - split ; apply isaset_nat_trans ; apply K.
  Qed.

  Definition disp_presheaves_is_univalent_2_1
    : disp_univalent_2_1 disp_presheaf_bicat.
  Proof.
    apply fiberwise_local_univalent_is_univalent_2_1.
    intros C D F CD FC α β.
    use isweqimplimpl.
    - intro p ; cbn in * ; unfold idfun in *.
      apply nat_trans_eq.
      { apply K. }
      intro x.
      pose (nat_trans_eq_pointwise (pr1 p) x) as q.
      cbn in q.
      rewrite q.
      rewrite (functor_id FC), id_right.
      reflexivity.
    - apply isaset_nat_trans.
      apply K.
    - apply isofhleveltotal2.
      + apply isaset_nat_trans.
        apply K.
      + intro.
        apply isaprop_is_disp_invertible_2cell.
  Qed.

  Definition disp_presheaves_adjequiv
             {C : ∁}
             (FC FC' : disp_presheaf_bicat C)
    : @invertible_2cell bicat_of_cats _ _ FC FC'
      -> disp_adjoint_equivalence (internal_adjoint_equivalence_identity C) FC FC'.
  Proof.
    intros α.
    use tpair.
    - apply α.
    - use tpair.
      + use tpair.
        * apply α.
        * split ; apply nat_trans_eq ; try (apply K) ; intro x ; cbn.
          ** rewrite (functor_id FC), id_right.
             exact (!(nat_trans_eq_pointwise (pr122 α) x)).
          ** rewrite (functor_id FC'), id_left.
             exact (nat_trans_eq_pointwise (pr222 α) x).
      + split ; split.
        * apply isaset_nat_trans.
          apply K.
        * apply isaset_nat_trans.
          apply K.
        * apply disp_presheaves_all_invertible.
        * apply disp_presheaves_all_invertible.
  Defined.

  Definition disp_presheaves_adjequiv_inv
             {C : ∁}
             (FC FC' : disp_presheaf_bicat C)
    : disp_adjoint_equivalence (internal_adjoint_equivalence_identity C) FC FC'
      → @invertible_2cell bicat_of_cats _ _ FC FC'.
  Proof.
    intros α.
    use tpair.
    - apply α.
    - use tpair.
      + apply α.
      + split.
        * apply nat_trans_eq.
          { apply K. }
          intro x ; cbn.
          pose (nat_trans_eq_pointwise (pr1(pr212 α)) x) as p.
          cbn in p.
          rewrite (functor_id FC), id_right in p.
          exact (!p).
        * apply nat_trans_eq.
          { apply K. }
          intro x ; cbn.
          pose (nat_trans_eq_pointwise (pr2(pr212 α)) x) as p.
          cbn in p.
          rewrite (functor_id FC'), id_right in p.
          exact p.
  Defined.

  Definition disp_presheaves_adjequiv_weq
             {C : ∁}
             (FC FC' : disp_presheaf_bicat C)
    : @invertible_2cell bicat_of_cats _ _ FC FC'
      ≃ disp_adjoint_equivalence (internal_adjoint_equivalence_identity C) FC FC'.
  Proof.
    exists (disp_presheaves_adjequiv FC FC').
    use isweq_iso.
    - exact (disp_presheaves_adjequiv_inv FC FC').
    - intro x.
      apply subtypeEquality.
      { intro ; apply isaprop_is_invertible_2cell. }
      reflexivity.
    - intro x.
      apply subtypeEquality.
      {
        intro.
        apply isaprop_disp_left_adjoint_equivalence.
        + apply univalent_cat_is_univalent_2_1.
        + apply disp_presheaves_is_univalent_2_1.
      }
      reflexivity.
  Defined.

  Definition disp_presheaves_idtoiso_2_0
             {C : ∁}
             (FC FC' : disp_presheaf_bicat C)
    : FC = FC' ≃ disp_adjoint_equivalence (internal_adjoint_equivalence_identity C) FC FC'
    := ((disp_presheaves_adjequiv_weq FC FC')
          ∘ (make_weq (@idtoiso_2_1 bicat_of_cats _ _ FC FC')
                     (univalent_cat_is_univalent_2_1 _ _ _ _)))%weq.

  Definition disp_presheaves_is_univalent_2_0
    : disp_univalent_2_0 disp_presheaf_bicat.
  Proof.
    apply fiberwise_univalent_2_0_to_disp_univalent_2_0.
    intros C FC FC'.
    use weqhomot.
    - exact (disp_presheaves_idtoiso_2_0 FC FC').
    - intro p.
      apply subtypeEquality.
      {
        intro.
        apply isaprop_disp_left_adjoint_equivalence.
        + apply univalent_cat_is_univalent_2_1.
        + apply disp_presheaves_is_univalent_2_1.
      }
      induction p ; cbn.
      reflexivity.
  Defined.

  Definition disp_presheaves_is_univalent_2
    : disp_univalent_2 disp_presheaf_bicat.
  Proof.
    split.
    - exact disp_presheaves_is_univalent_2_0.
    - exact disp_presheaves_is_univalent_2_1.
  Defined.

End fix_a_category.
