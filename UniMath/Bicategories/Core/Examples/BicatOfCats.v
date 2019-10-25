(* ******************************************************************************* *)
(** * Bicategory of 1-categories

    Benedikt Ahrens, Marco Maggesi

    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryEquality.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.

Definition cat_prebicat_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact univalent_category.
  - exact (λ C D, functor C D).
  - exact (λ _ _ F G, nat_trans F G).
  - exact (λ C, functor_identity C).
  - exact (λ _ _ _ F G, functor_composite F G).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ α β, nat_trans_comp _ _ _ α β).
  - exact (λ _ _ _ F _ _ α, pre_whisker F α).
  - exact (λ _ _ _ _ _ H α, post_whisker α H).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ F, nat_trans_id F).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
  - exact (λ _ _ _ _ _ _ _, nat_trans_id _).
Defined.

Definition cat_prebicat_laws : prebicat_laws cat_prebicat_data.
Proof.
  repeat split; cbn.
  - intros C D F G η.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F G η.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_right.
  - intros C D F₁ F₂ F₃ F₄ α β γ.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply assoc.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    reflexivity.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    apply functor_id.
  - intros C₁ C₂ C₃ F G₁ G₂ G₃ α β.
    apply nat_trans_eq; try apply C₃.
    reflexivity.
  - intros C₁ C₂ C₃ F₁ F₂ F₃ G α β.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact (!(functor_comp G _ _)).
  - intros C D F G α.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C D F G α.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F G H₁ H₂ α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ H α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G H α.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    rewrite id_left, id_right.
    reflexivity.
  - intros C₁ C₂ C₃ F₁ F₂ G₁ H₂ α β.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact ((nat_trans_ax β _ _ _)).
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply D.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply C₄.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply C₃.
    intros ; cbn.
    exact (id_left _ @ functor_id G _).
  - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄.
    apply nat_trans_eq; try apply C₅.
    intros ; cbn.
    rewrite !id_left.
    exact (functor_id F₄ _).
Qed.

Definition prebicat_of_cats : prebicat := _ ,, cat_prebicat_laws.

Lemma isaset_cells_prebicat_of_cats : isaset_cells prebicat_of_cats.
Proof.
  intros a b f g.
  apply isaset_nat_trans.
  apply homset_property.
Qed.

Definition bicat_of_cats : bicat
  := (prebicat_of_cats,, isaset_cells_prebicat_of_cats).

Definition is_invertible_2cell_to_is_nat_iso
           {C D : bicat_of_cats}
           {F G : C --> D}
           (η : F ==> G)
  : is_invertible_2cell η → is_nat_iso η.
Proof.
  intros Hη X.
  use is_iso_qinv.
  - apply (Hη^-1).
  - split ; cbn.
    + exact (nat_trans_eq_pointwise (vcomp_rinv Hη) X).
    + exact (nat_trans_eq_pointwise (vcomp_linv Hη) X).
Defined.

Definition invertible_2cell_to_nat_iso
           {C D : bicat_of_cats}
           (F G : C --> D)
  : invertible_2cell F G → nat_iso F G.
Proof.
  intros η.
  use make_nat_iso.
  - exact (cell_from_invertible_2cell η).
  - apply is_invertible_2cell_to_is_nat_iso.
    apply η.
Defined.

Definition is_nat_iso_to_is_invertible_2cell
           {C D : bicat_of_cats}
           {F G : C --> D}
           (η : F ==> G)
  : is_nat_iso η → is_invertible_2cell η.
Proof.
  intros Hη.
  use tpair.
  - apply (nat_iso_inv (η ,, Hη)).
  - split.
    + apply nat_trans_eq.
      { apply D. }
      intros X ; cbn.
      exact (iso_inv_after_iso (pr1 η X ,, _)).
    + apply nat_trans_eq.
      { apply D. }
      intros X ; cbn.
      exact (iso_after_iso_inv (pr1 η X ,, _)).
Defined.

Definition nat_iso_to_invertible_2cell
           {C D : bicat_of_cats}
           (F G : C --> D)
  : nat_iso F G → invertible_2cell F G.
Proof.
  intros η.
  use tpair.
  - apply η.
  - apply is_nat_iso_to_is_invertible_2cell.
    apply η.
Defined.

Definition invertible_2cell_is_nat_iso
           {C D : bicat_of_cats}
           (F G : C --> D)
  : nat_iso F G ≃ invertible_2cell F G.
Proof.
  use make_weq.
  - exact (nat_iso_to_invertible_2cell F G).
  - use isweq_iso.
    + exact (invertible_2cell_to_nat_iso F G).
    + intros X.
      use subtypePath.
      * intro.
        apply isaprop_is_nat_iso.
      * reflexivity.
    + intros X.
      use subtypePath.
      * intro.
        apply isaprop_is_invertible_2cell.
      * reflexivity.
Defined.

Definition adj_equiv_to_equiv_cat
           {C D : bicat_of_cats}
           (F : C --> D)
  : left_adjoint_equivalence F → adj_equivalence_of_precats F.
Proof.
  intros A.
  use make_adj_equivalence_of_precats.
  - exact (left_adjoint_right_adjoint A).
  - exact (left_adjoint_unit A).
  - exact (left_adjoint_counit A).
  - split.
    + intro X.
      cbn.
      pose (nat_trans_eq_pointwise (internal_triangle1 A) X) as p.
      cbn in p.
      rewrite !id_left, !id_right in p.
      exact p.
    + intro X.
      cbn.
      pose (nat_trans_eq_pointwise (internal_triangle2 A) X) as p.
      cbn in p.
      rewrite !id_left, !id_right in p.
      exact p.
  - split.
    + intro X.
      apply (invertible_2cell_to_nat_iso _ _ (left_equivalence_unit_iso A)).
    + intro X.
      apply (invertible_2cell_to_nat_iso _ _ (left_equivalence_counit_iso A)).
Defined.

Definition equiv_cat_to_adj_equiv
           {C D : bicat_of_cats}
           (F : C --> D)
  : adj_equivalence_of_precats F → left_adjoint_equivalence F.
Proof.
  intros A.
  use tpair.
  - use tpair.
    + apply A.
    + split ; cbn.
      * exact (pr1(pr1(pr2(pr1 A)))).
      * exact (pr2(pr1(pr2(pr1 A)))).
  - split ; split.
    + apply nat_trans_eq.
      { apply D. }
      intro X ; cbn.
      rewrite id_left, !id_right.
      apply (pr2(pr2(pr1 A))).
    + apply nat_trans_eq.
      { apply C. }
      intro X ; cbn.
      rewrite id_left, !id_right.
      apply (pr2(pr2(pr1 A))).
    + apply is_nat_iso_to_is_invertible_2cell.
      intro X.
      apply (pr2 A).
    + apply is_nat_iso_to_is_invertible_2cell.
      intro X.
      apply (pr2 A).
Defined.

Definition adj_equiv_is_equiv_cat
           {C D : bicat_of_cats}
           (F : C --> D)
  : left_adjoint_equivalence F ≃ adj_equivalence_of_precats F.
Proof.
  use make_weq.
  - exact (adj_equiv_to_equiv_cat F).
  - use isweq_iso.
    + exact (equiv_cat_to_adj_equiv F).
    + intros A.
      use subtypePath.
      * intro.
        do 2 apply isapropdirprod.
        ** apply bicat_of_cats.
        ** apply bicat_of_cats.
        ** apply isaprop_is_invertible_2cell.
        ** apply isaprop_is_invertible_2cell.
      * reflexivity.
    + intros A.
      use subtypePath.
      * intro.
        apply isapropdirprod ; apply impred ; intro ; apply isaprop_is_iso.
      * use total2_paths_b.
        ** reflexivity.
        ** use subtypePath.
           *** intro ; simpl.
               apply (@isaprop_form_adjunction (pr1 C ,, _) (pr1 D ,, _)).
           *** reflexivity.
Defined.

Definition univalent_cat_idtoiso_2_1
           {C D : univalent_category}
           (F G : bicat_of_cats⟦C,D⟧)
  : F = G ≃ invertible_2cell F G.
Proof.
  refine ((invertible_2cell_is_nat_iso F G)
            ∘ iso_is_nat_iso F G
            ∘ make_weq (@idtoiso (functor_category C D) F G) _)%weq.
  exact (pr1 (is_univalent_functor_category C D _) F G).
Defined.

Definition univalent_cat_is_univalent_2_1
  : is_univalent_2_1 bicat_of_cats.
Proof.
  intros C D f g.
  use weqhomot.
  - exact (univalent_cat_idtoiso_2_1 f g).
  - intros p.
    induction p.
    use subtypePath.
    + intro.
      apply isaprop_is_invertible_2cell.
    + apply nat_trans_eq.
      { apply D. }
      reflexivity.
Defined.

Definition path_univalent_cat
           (C D : bicat_of_cats)
  : C = D ≃ pr1 C = pr1 D.
Proof.
  apply path_sigma_hprop.
  simpl.
  apply isaprop_is_univalent.
Defined.

Section CatIso_To_LeftAdjEquiv.
  Context {C D : univalent_category}.
  Variable (F : C ⟶ D)
           (HF : is_catiso F).

  Local Definition cat_iso_unit
    : nat_iso
        (functor_identity C)
        (functor_composite F (inv_catiso (F ,, HF))).
  Proof.
    use tpair.
    - use make_nat_trans.
      + intros X ; cbn.
        exact (pr1 (idtoiso (! homotinvweqweq (catiso_ob_weq (F ,, HF)) X))).
      + intros X Y f ; cbn.
        use (invmaponpathsweq (#F ,, _)).
        { apply HF. }
        cbn.
        refine (functor_comp _ _ _ @ !_).
        refine (functor_comp _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          match goal with [ |- _ (invmap ?FFF ?fff) = _ ] => apply (homotweqinvweq FFF fff) end.
        }
        rewrite !assoc.
        etrans.
        {
          refine (maponpaths (λ z, ((z · _) · _) · _) _).
          apply (!(base_paths _ _ (maponpaths_idtoiso _ _ F _ _ _))).
        }
        etrans.
        {
          refine (maponpaths (λ z, (z · _) · _) (!_)).
          apply (base_paths _ _ (idtoiso_concat _ _ _ _ _ _)).
        }
        rewrite maponpathsinv0.
        etrans.
        {
          refine (maponpaths (λ z, (pr1 (idtoiso (! z @ _)) · _) · _) _).
          match goal with [ |- _ (homotinvweqweq ?w _) = _] => apply (homotweqinvweqweq w) end.
        }
        rewrite pathsinv0l ; cbn.
        rewrite id_left.
        apply maponpaths.
        etrans.
        {
          repeat apply maponpaths.
          match goal with [ |- (homotweqinvweq ?w _) = _] => apply (! homotweqinvweqweq w Y) end.
        }
        rewrite <- maponpathsinv0.
        apply (base_paths _ _ (maponpaths_idtoiso _ _ F _ _ _)).
    - intros X.
      apply (idtoiso (! homotinvweqweq (catiso_ob_weq (F ,, HF)) X)).
  Defined.

  Local Definition cat_iso_counit
    : nat_iso
        (functor_composite (inv_catiso (F ,, HF)) F)
        (functor_identity (pr1 (pr1 D))).
  Proof.
    use tpair.
    - use make_nat_trans.
      + intros X ; cbn.
        exact (pr1 (idtoiso (homotweqinvweq (catiso_ob_weq (F ,, HF)) X))).
      + intros X Y f ; cbn.
        etrans.
        {
          apply maponpaths_2.
          match goal with [ |- _ (invmap ?FFF ?fff) = _ ] => apply (homotweqinvweq FFF fff) end.
        }
        rewrite <- !assoc.
        etrans.
        {
          refine (maponpaths (λ z, _ · (_ · z)) _).
          apply (base_paths _ _ (!(idtoiso_concat _ _ _ _ _ _))).
        }
        rewrite pathsinv0l ; cbn.
        rewrite id_right.
        reflexivity.
    - intros X.
      apply (idtoiso (homotweqinvweq (catiso_ob_weq (F ,, HF)) X)).
  Defined.

  Definition is_catiso_to_left_adjoint_equivalence
    : @left_adjoint_equivalence bicat_of_cats _ _ F.
  Proof.
    use equiv_to_adjequiv.
    use tpair.
    - use tpair.
      + exact (inv_catiso (F ,, HF)).
      + split.
        * apply cat_iso_unit.
        * apply cat_iso_counit.
    - split.
      + use tpair ; try split.
        * apply (nat_iso_inv cat_iso_unit).
        * apply nat_trans_eq.
          { apply C. }
          intro X ; cbn.
          rewrite idtoiso_inv ; cbn ; unfold precomp_with.
          rewrite id_right.
          apply iso_after_iso_inv.
        * apply nat_trans_eq.
          { apply C. }
          intro X ; cbn.
          rewrite idtoiso_inv ; cbn ; unfold precomp_with.
          rewrite id_right.
          apply iso_inv_after_iso.
      + use tpair ; try split.
        * apply (nat_iso_inv cat_iso_counit).
        * apply nat_trans_eq.
          { apply D. }
          intro X ; cbn.
          apply iso_inv_after_iso.
        * apply nat_trans_eq.
          { apply D. }
          intro X ; cbn.
          apply iso_after_iso_inv.
  Qed.
End CatIso_To_LeftAdjEquiv.

Definition left_adjoint_equivalence_to_is_catiso
           {C D : bicat_of_cats}
           (L : (pr1 C) ⟶ (pr1 D))
  : @left_adjoint_equivalence bicat_of_cats _ _ L → is_catiso L.
Proof.
  intros HF.
  pose (R := pr1 (left_adjoint_right_adjoint HF)).
  pose (η := left_adjoint_unit HF).
  pose (ηinv := (left_equivalence_unit_iso HF)^-1).
  pose (ε := left_adjoint_counit HF).
  pose (εinv := (left_equivalence_counit_iso HF)^-1).
  assert (ηηinv := nat_trans_eq_pointwise
                     (pr1(pr2(pr2 (left_equivalence_unit_iso HF))))).
  assert (ηinvη := nat_trans_eq_pointwise
                     (pr2(pr2(pr2 (left_equivalence_unit_iso HF))))).
  assert (εεinv := nat_trans_eq_pointwise
                     (pr1(pr2(pr2 (left_equivalence_counit_iso HF))))).
  assert (εinvε := nat_trans_eq_pointwise
                     (pr2(pr2(pr2 (left_equivalence_counit_iso HF))))).
  assert (LηεL := nat_trans_eq_pointwise (internal_triangle1 HF)).
  assert (ηRRε := nat_trans_eq_pointwise (internal_triangle2 HF)).
  cbn in *.
  use tpair.
  - intros X Y.
    use isweq_iso.
    + intros f.
      exact (η X · #R f · ηinv Y).
    + intros f ; cbn.
      etrans.
      {
        apply maponpaths_2.
        exact (!(pr2 η X Y f)).
      }
      rewrite <- assoc.
      refine (maponpaths (λ z, _ · z) (ηηinv Y) @ _).
      apply id_right.
    + intros f ; cbn.
      rewrite !functor_comp.
      assert (#L (ηinv Y) = ε (L Y)) as X0.
      {
        specialize (LηεL Y).
        rewrite !id_left, !id_right in LηεL.
        refine (!(id_right _) @ _).
        refine (maponpaths (λ z, _ · z) (!LηεL) @ _).
        rewrite assoc.
        rewrite <- functor_comp.
        refine (maponpaths (λ z, # L z · _) (ηinvη Y) @ _).
        rewrite functor_id, id_left.
        reflexivity.
      }
      etrans.
      {
        apply maponpaths.
        exact X0.
      }
      rewrite <- assoc.
      refine (maponpaths _ (nat_trans_ax ε (L X) (L Y) f) @ _).
      rewrite assoc.
      specialize (LηεL X).
      rewrite !id_left, !id_right in LηεL.
      etrans.
      {
        apply maponpaths_2.
        exact LηεL.
      }
      apply id_left.
  - cbn.
    use isweq_iso.
    + apply R.
    + intros X ; cbn.
      apply isotoid.
      * apply C.
      * use tpair.
        ** exact (ηinv X).
        ** use is_iso_qinv ; try split.
           *** exact (η X).
           *** exact (ηinvη X).
           *** exact (ηηinv X).
    + intros Y ; cbn.
      apply isotoid.
      * apply D.
      * use tpair.
        ** exact (ε Y).
        ** use is_iso_qinv ; try split.
           *** exact (εinv Y).
           *** exact (εεinv Y).
           *** exact (εinvε Y).
Qed.

Definition is_catiso_left_adjoint_equivalence
           {C D : univalent_category}
           (F : C ⟶ D)
  : is_catiso F ≃ @left_adjoint_equivalence bicat_of_cats C D F.
Proof.
  use weqimplimpl.
  - exact (is_catiso_to_left_adjoint_equivalence F).
  - exact (left_adjoint_equivalence_to_is_catiso F).
  - apply isaprop_is_catiso.
  - apply invproofirrelevance.
    intros A₁ A₂.
    apply unique_internal_adjoint_equivalence.
    apply univalent_cat_is_univalent_2_1.
Defined.

Definition cat_iso_to_adjequiv
           (C D : bicat_of_cats)
  : catiso (pr1 C) (pr1 D) ≃ adjoint_equivalence C D.
Proof.
  use weqfibtototal.
  intros.
  apply is_catiso_left_adjoint_equivalence.
Defined.

Definition idtoiso_2_0_univalent_cat
           (C D : bicat_of_cats)
  : C = D ≃ adjoint_equivalence C D
  := ((cat_iso_to_adjequiv C D)
        ∘ catiso_is_path_precat (pr1 C) (pr1 D) (pr2(pr2 D))
        ∘ path_univalent_cat C D)%weq.

Definition univalent_cat_is_univalent_2_0
  : is_univalent_2_0 bicat_of_cats.
Proof.
  intros C D.
  use weqhomot.
  - exact (idtoiso_2_0_univalent_cat C D).
  - intro p.
    induction p.
    apply path_internal_adjoint_equivalence.
    + apply univalent_cat_is_univalent_2_1.
    + reflexivity.
Defined.

Definition univalent_cat_is_univalent_2
  : is_univalent_2 bicat_of_cats.
Proof.
  split.
  - exact univalent_cat_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_1.
Defined.

Definition adj_equivalence_to_left_equivalence
           {C₁ C₂ : univalent_category}
           {F : C₁ ⟶ C₂}
           (A : adj_equivalence_of_precats F)
  : @left_equivalence bicat_of_cats _ _ F.
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (adj_equivalence_inv A).
  - exact (pr1 (unit_nat_iso_from_adj_equivalence_of_precats A)).
  - exact (pr1 (counit_nat_iso_from_adj_equivalence_of_precats A)).
  - apply is_nat_iso_to_is_invertible_2cell.
    exact (pr2 (unit_nat_iso_from_adj_equivalence_of_precats A)).
  - apply is_nat_iso_to_is_invertible_2cell.
    exact (pr2 (counit_nat_iso_from_adj_equivalence_of_precats A)).
Defined.
