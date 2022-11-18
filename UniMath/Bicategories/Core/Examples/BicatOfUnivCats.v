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
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
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

Lemma cat_prebicat_laws : prebicat_laws cat_prebicat_data.
Proof.
  repeat split; cbn.
  - intros C D F G η.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply id_left.
  - intros C D F G η.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply id_right.
  - intros C D F₁ F₂ F₃ F₄ α β γ.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply assoc.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply homset_property.
    intro; apply idpath.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply functor_id.
  - intros C₁ C₂ C₃ F G₁ G₂ G₃ α β.
    apply nat_trans_eq; try apply homset_property.
    intros; apply idpath.
  - intros C₁ C₂ C₃ F₁ F₂ F₃ G α β.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    exact (!(functor_comp G _ _)).
  - intros C D F G α.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C D F G α.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G H₁ H₂ α.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G₁ G₂ H α.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ G H α.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    rewrite id_left, id_right.
    apply idpath.
  - intros C₁ C₂ C₃ F₁ F₂ G₁ H₂ α β.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    exact ((nat_trans_ax β _ _ _)).
  - intros C D F.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply id_left.
  - intros C D F.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    apply id_left.
  - intros C₁ C₂ C₃ F G.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    exact (id_left _ @ functor_id G _).
  - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄.
    apply nat_trans_eq; try apply homset_property.
    intros ; cbn.
    rewrite !id_left.
    exact (functor_id F₄ _).
Qed.

Definition prebicat_of_univ_cats : prebicat := _ ,, cat_prebicat_laws.

Lemma isaset_cells_prebicat_of_univ_cats : isaset_cells prebicat_of_univ_cats.
Proof.
  intros a b f g.
  apply isaset_nat_trans.
  apply homset_property.
Qed.

Definition bicat_of_univ_cats : bicat
  := (prebicat_of_univ_cats,, isaset_cells_prebicat_of_univ_cats).

Definition is_invertible_2cell_to_is_nat_z_iso
           {C D : bicat_of_univ_cats}
           {F G : C --> D}
           (η : F ==> G)
  : is_invertible_2cell η → is_nat_z_iso (pr1 η).
Proof.
  intros Hη X.
  use tpair.
  - apply (Hη^-1).
  - abstract
      (split ; cbn ;
       [ exact (nat_trans_eq_pointwise (vcomp_rinv Hη) X)
       | exact (nat_trans_eq_pointwise (vcomp_linv Hη) X)]).
Defined.

Definition invertible_2cell_to_nat_z_iso
           {C D : bicat_of_univ_cats}
           (F G : C --> D)
  : invertible_2cell F G → nat_z_iso F G.
Proof.
  intros η.
  use make_nat_z_iso.
  - exact (cell_from_invertible_2cell η).
  - apply is_invertible_2cell_to_is_nat_z_iso.
    apply η.
Defined.

Definition is_nat_z_iso_to_is_invertible_2cell
           {C D : bicat_of_univ_cats}
           {F G : C --> D}
           (η : F ==> G)
  : is_nat_z_iso (pr1 η) → is_invertible_2cell η.
Proof.
  intros Hη.
  use tpair.
  - apply (nat_z_iso_inv (η ,, Hη)).
  - abstract
      (split ;
       [ apply nat_trans_eq ; [ apply homset_property | ] ;
         intros x ; cbn ;
         exact (z_iso_inv_after_z_iso (pr1 η x ,, _))
       | apply nat_trans_eq ; [ apply homset_property | ] ;
         intros x ; cbn ;
         exact (z_iso_after_z_iso_inv (pr1 η x ,, _)) ]).
Defined.

Definition nat_z_iso_to_invertible_2cell
           {C D : bicat_of_univ_cats}
           (F G : C --> D)
  : nat_z_iso F G → invertible_2cell F G.
Proof.
  intros η.
  use tpair.
  - apply η.
  - apply is_nat_z_iso_to_is_invertible_2cell.
    apply η.
Defined.

Definition invertible_2cell_is_nat_z_iso
           {C D : bicat_of_univ_cats}
           (F G : C --> D)
  : nat_z_iso F G ≃ invertible_2cell F G.
Proof.
  use make_weq.
  - exact (nat_z_iso_to_invertible_2cell F G).
  - use isweq_iso.
    + exact (invertible_2cell_to_nat_z_iso F G).
    + intros x.
      use subtypePath.
      * intro.
        apply isaprop_is_nat_z_iso.
      * apply idpath.
    + intros x.
      use subtypePath.
      * intro.
        apply isaprop_is_invertible_2cell.
      * apply idpath.
Defined.

Definition adj_equiv_to_equiv_cat
           {C D : bicat_of_univ_cats}
           (F : C --> D)
  : left_adjoint_equivalence F → adj_equivalence_of_cats F.
Proof.
  intros A.
  use make_adj_equivalence_of_cats.
  - exact (left_adjoint_right_adjoint A).
  - exact (left_adjoint_unit A).
  - exact (left_adjoint_counit A).
  - split.
    + abstract
        (intro x ;
         cbn ;
         pose (nat_trans_eq_pointwise (internal_triangle1 A) x) as p ;
         cbn in p ;
         rewrite !id_left, !id_right in p ;
         exact p).
    + abstract
        (intro x ;
         cbn ;
         pose (nat_trans_eq_pointwise (internal_triangle2 A) x) as p ;
         cbn in p ;
         rewrite !id_left, !id_right in p ;
         exact p).
  - split.
    + intro X.
      apply (invertible_2cell_to_nat_z_iso _ _ (left_equivalence_unit_iso A)).
    + intro X.
      apply (invertible_2cell_to_nat_z_iso _ _ (left_equivalence_counit_iso A)).
Defined.

Definition equiv_cat_to_adj_equiv
           {C D : bicat_of_univ_cats}
           (F : C --> D)
  : adj_equivalence_of_cats F → left_adjoint_equivalence F.
Proof.
  intros A.
  use tpair.
  - use tpair.
    + apply A.
    + split ; cbn.
      * exact (pr1 (pr121 A)).
      * exact (pr2 (pr121 A)).
  - split ; split.
    + abstract
        (apply nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         rewrite id_left, !id_right ;
         apply (pr2(pr2(pr1 A)))).
    + abstract
        (apply nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         rewrite id_left, !id_right ;
         apply (pr2(pr2(pr1 A)))).
    + apply is_nat_z_iso_to_is_invertible_2cell.
      intro x.
      apply (pr2 A).
    + apply is_nat_z_iso_to_is_invertible_2cell.
      intro x.
      apply (pr2 A).
Defined.

Definition adj_equiv_is_equiv_cat
           {C D : bicat_of_univ_cats}
           (F : C --> D)
  : left_adjoint_equivalence F ≃ adj_equivalence_of_cats F.
Proof.
  use make_weq.
  - exact (adj_equiv_to_equiv_cat F).
  - use isweq_iso.
    + exact (equiv_cat_to_adj_equiv F).
    + intros A.
      use subtypePath.
      * intro.
        do 2 apply isapropdirprod.
        ** apply cellset_property.
        ** apply cellset_property.
        ** apply isaprop_is_invertible_2cell.
        ** apply isaprop_is_invertible_2cell.
      * apply idpath.
    + intros A.
      use subtypePath.
      * intro.
        apply isapropdirprod ; apply impred ; intro ; apply isaprop_is_z_isomorphism.
      * use total2_paths_b.
        ** apply idpath.
        ** use subtypePath.
           *** intro ; simpl.
               apply (@isaprop_form_adjunction (pr1 C) (pr1 D)).
           *** apply idpath.
Defined.

Definition univalent_cat_idtoiso_2_1
           {C D : univalent_category}
           (F G : bicat_of_univ_cats⟦C,D⟧)
  : F = G ≃ invertible_2cell F G.
Proof.
  refine ((invertible_2cell_is_nat_z_iso F G)
            ∘ z_iso_is_nat_z_iso F G
            ∘ make_weq (@idtoiso (functor_category C D) F G) _)%weq.
  refine (is_univalent_functor_category C D _ F G).
  apply D.
Defined.

Definition univalent_cat_is_univalent_2_1
  : is_univalent_2_1 bicat_of_univ_cats.
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
      { apply homset_property. }
      intros; apply idpath.
Defined.

Definition path_univalent_cat
           (C D : bicat_of_univ_cats)
  : C = D ≃ pr1 C = pr1 D.
Proof.
  apply path_sigma_hprop.
  simpl.
  apply isaprop_is_univalent.
Defined.

Definition path_cat
           (C D : category)
  : C = D ≃ pr1 C = pr1 D.
Proof.
  apply path_sigma_hprop.
  simpl.
  apply isaprop_has_homsets.
Defined.

Section CatIso_To_LeftAdjEquiv.
  Context {C D : univalent_category}.
  Variable (F : C ⟶ D)
           (HF : is_catiso F).

  Local Definition cat_iso_unit
    : nat_z_iso
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
    : nat_z_iso
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
        apply idpath.
    - intros X.
      apply (idtoiso (homotweqinvweq (catiso_ob_weq (F ,, HF)) X)).
  Defined.

  Definition is_catiso_to_left_adjoint_equivalence
    : @left_adjoint_equivalence bicat_of_univ_cats _ _ F.
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
        * apply (nat_z_iso_inv cat_iso_unit).
        * apply nat_trans_eq.
          { apply homset_property. }
          intro X ; cbn.
          rewrite idtoiso_inv; cbn.
          apply z_iso_after_z_iso_inv.
        * apply nat_trans_eq.
          { apply homset_property. }
          intro X ; cbn.
          rewrite idtoiso_inv; cbn.
          apply z_iso_inv_after_z_iso.
      + use tpair ; try split.
        * apply (nat_z_iso_inv cat_iso_counit).
        * apply nat_trans_eq.
          { apply homset_property. }
          intro X ; cbn.
          apply z_iso_inv_after_z_iso.
        * apply nat_trans_eq.
          { apply homset_property. }
          intro X ; cbn.
          apply z_iso_after_z_iso_inv.
  Qed.

End CatIso_To_LeftAdjEquiv.

Definition left_adjoint_equivalence_to_is_catiso
           {C D : bicat_of_univ_cats}
           (L : (pr1 C) ⟶ (pr1 D))
  : @left_adjoint_equivalence bicat_of_univ_cats _ _ L → is_catiso L.
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
        apply idpath.
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
        ** exists (η X); split.
           *** exact (ηinvη X).
           *** exact (ηηinv X).
    + intros Y ; cbn.
      apply isotoid.
      * apply D.
      * use tpair.
        ** exact (ε Y).
        ** exists (εinv Y); split.
           *** exact (εεinv Y).
           *** exact (εinvε Y).
Qed.

Definition is_catiso_left_adjoint_equivalence
           {C D : univalent_category}
           (F : C ⟶ D)
  : is_catiso F ≃ @left_adjoint_equivalence bicat_of_univ_cats C D F.
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
           (C D : bicat_of_univ_cats)
  : catiso (pr1 C) (pr1 D) ≃ adjoint_equivalence C D.
Proof.
  use weqfibtototal.
  intros.
  apply is_catiso_left_adjoint_equivalence.
Defined.

Definition idtoiso_2_0_univalent_cat
           (C D : bicat_of_univ_cats)
  : C = D ≃ adjoint_equivalence C D
  := (cat_iso_to_adjequiv C D
      ∘ catiso_is_path_precat (pr11 C) (pr11 D) (pr21 D)
      ∘ path_cat (pr1 C) (pr1 D)
      ∘ path_univalent_cat C D)%weq.

Definition univalent_cat_is_univalent_2_0
  : is_univalent_2_0 bicat_of_univ_cats.
Proof.
  intros C D.
  use weqhomot.
  - exact (idtoiso_2_0_univalent_cat C D).
  - intro p.
    induction p.
    apply path_internal_adjoint_equivalence.
    + apply univalent_cat_is_univalent_2_1.
    + apply idpath.
Defined.

Definition univalent_cat_is_univalent_2
  : is_univalent_2 bicat_of_univ_cats.
Proof.
  split.
  - exact univalent_cat_is_univalent_2_0.
  - exact univalent_cat_is_univalent_2_1.
Defined.

Definition adj_equivalence_to_left_equivalence
           {C₁ C₂ : univalent_category}
           {F : C₁ ⟶ C₂}
           (A : adj_equivalence_of_cats F)
  : @left_equivalence bicat_of_univ_cats _ _ F.
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (adj_equivalence_inv A).
  - exact (pr1 (unit_nat_z_iso_from_adj_equivalence_of_cats A)).
  - exact (pr1 (counit_nat_z_iso_from_adj_equivalence_of_cats A)).
  - apply is_nat_z_iso_to_is_invertible_2cell.
    exact (pr2 (unit_nat_z_iso_from_adj_equivalence_of_cats A)).
  - apply is_nat_z_iso_to_is_invertible_2cell.
    exact (pr2 (counit_nat_z_iso_from_adj_equivalence_of_cats A)).
Defined.

(** Left adjoints and right adjoints of categories *)
Definition left_adjoint_to_is_left_adjoint
           {C₁ C₂ : bicat_of_univ_cats}
           {L : C₁ --> C₂}
           (HL : left_adjoint L)
  : is_left_adjoint L.
Proof.
  simple refine (left_adjoint_right_adjoint HL
                 ,,
                 ((left_adjoint_unit HL
                   ,,
                   left_adjoint_counit HL)
                 ,,
                 _)).
  split.
  - abstract
      (intro x ; cbn ;
       pose (nat_trans_eq_pointwise (internal_triangle1 HL) x) as p ;
       cbn in p ;
       rewrite !id_left, !id_right in p ;
       exact p).
  - abstract
      (intro x ; cbn ;
       pose (nat_trans_eq_pointwise (internal_triangle2 HL) x) as p ;
       cbn in p ;
       rewrite !id_left, !id_right in p ;
       exact p).
Defined.

Definition is_left_adjoint_to_left_adjoint
           {C₁ C₂ : bicat_of_univ_cats}
           {L : C₁ --> C₂}
           (HL : is_left_adjoint L)
  : left_adjoint L.
Proof.
  simple refine ((right_functor HL ,, (adjunit HL ,, adjcounit HL)) ,, _).
  split.
  - abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       rewrite !id_left, !id_right ;
       apply (pr122 HL)).
  - abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       rewrite !id_left, !id_right ;
       apply (pr222 HL)).
Defined.

Definition left_adjoint_weq_is_left_adjoint
           {C₁ C₂ : bicat_of_univ_cats}
           (L : C₁ --> C₂)
  : left_adjoint L ≃ is_left_adjoint L.
Proof.
  use make_weq.
  - exact left_adjoint_to_is_left_adjoint.
  - use isweq_iso.
    + exact is_left_adjoint_to_left_adjoint.
    + abstract
        (intro HL ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         apply idpath).
    + abstract
        (intro HL ;
         refine (maponpaths (λ z, _ ,, z) _) ;
         use subtypePath ; [ | apply idpath ] ;
         intro ;
         apply isapropdirprod ; use impred ; intro ; apply homset_property).
Defined.

Definition right_adjoint_to_is_right_adjoint
           {C₁ C₂ : bicat_of_univ_cats}
           {R : C₁ --> C₂}
           (HR : internal_right_adj R)
  : is_right_adjoint R.
Proof.
  simple refine (pr11 HR
                 ,,
                 ((pr121 HR
                   ,,
                   pr221 HR)
                 ,,
                 _)).
  split.
  - abstract
      (intro x ; cbn ;
       pose (nat_trans_eq_pointwise (pr12 HR) x) as p ;
       cbn in p ;
       rewrite !id_left, !id_right in p ;
       exact p).
  - abstract
      (intro x ; cbn ;
       pose (nat_trans_eq_pointwise (pr22 HR) x) as p ;
       cbn in p ;
       rewrite !id_left, !id_right in p ;
       exact p).
Defined.

Definition is_right_adjoint_to_right_adjoint
           {C₁ C₂ : bicat_of_univ_cats}
           {R : C₁ --> C₂}
           (HR : is_right_adjoint R)
  : internal_right_adj R.
Proof.
  simple refine ((pr1 HR ,, (pr112 HR ,, pr212 HR)) ,, _).
  split.
  - abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       rewrite !id_left, !id_right ;
       apply (pr122 HR)).
  - abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       rewrite !id_left, !id_right ;
       apply (pr222 HR)).
Defined.

Definition right_adjoint_weq_is_right_adjoint
           {C₁ C₂ : bicat_of_univ_cats}
           (R : C₁ --> C₂)
  : internal_right_adj R ≃ is_right_adjoint R.
Proof.
  use make_weq.
  - exact right_adjoint_to_is_right_adjoint.
  - use isweq_iso.
    + exact is_right_adjoint_to_right_adjoint.
    + abstract
        (intro HL ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         apply idpath).
    + abstract
        (intro HL ;
         refine (maponpaths (λ z, _ ,, z) _) ;
         use subtypePath ; [ | apply idpath ] ;
         intro ;
         apply isapropdirprod ; use impred ; intro ; apply homset_property).
Defined.
