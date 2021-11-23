Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.Colimits.Pullback.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

(** Characterization of cartesian 2-cells *)
Definition cleaving_of_fibs_is_cartesian_2cell
           {C₁ C₂ : bicat_of_univ_cats}
           {F₁ F₂ : C₁ --> C₂}
           {α : F₁ ==> F₂}
           {D₁ : disp_bicat_of_fibs C₁}
           {D₂ : disp_bicat_of_fibs C₂}
           {FF₁ : D₁ -->[ F₁ ] D₂}
           {FF₂ : D₁ -->[ F₂ ] D₂}
           (αα : FF₁ ==>[ α ] FF₂)
           (Hαα : ∏ (x : (C₁ : univalent_category))
                    (xx : (pr1 D₁ : disp_univalent_category _) x),
                  is_cartesian (pr11 αα x xx))
  : is_cartesian_2cell disp_bicat_of_fibs αα.
Proof.
  intros G GG β βα.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply disp_bicat_of_fibs | ] ;
       use subtypePath ; [ intro ; apply isapropunit | ] ;
       use disp_nat_trans_eq ;
       intros x xx ;
       assert (p₁ := maponpaths (λ z, (pr11 z) x xx) (pr2 φ₁)) ;
       assert (p₂ := maponpaths (λ z, (pr11 z) x xx) (pr2 φ₂)) ;
       cbn in p₁, p₂ ;
       pose (r := p₁ @ !p₂) ;
       use (cartesian_factorisation_unique (Hαα x xx)) ;
       exact r).
  - simple refine ((_ ,, tt) ,, _).
    + exact (cartesian_factorisation_disp_nat_trans (pr1 αα) (pr1 βα) Hαα).
    + abstract
        (use subtypePath ; [ intro ; apply isapropunit | ] ;
         use subtypePath ; [ intro ; apply isaprop_disp_nat_trans_axioms| ] ;
         use funextsec ; intro x ;
         use funextsec ; intro xx ;
         apply cartesian_factorisation_commutes).
Defined.

Definition cleaving_of_fibs_cartesian_2cell_is_pointwise_cartesian
           {C₁ C₂ : bicat_of_univ_cats}
           {F₁ F₂ : C₁ --> C₂}
           {α : F₁ ==> F₂}
           {D₁ : disp_bicat_of_fibs C₁}
           {D₂ : disp_bicat_of_fibs C₂}
           {FF₁ : D₁ -->[ F₁ ] D₂}
           {FF₂ : D₁ -->[ F₂ ] D₂}
           (αα : FF₁ ==>[ α ] FF₂)
           (Hαα : is_cartesian_2cell disp_bicat_of_fibs αα)
           (x : (C₁ : univalent_category))
           (xx : (pr1 D₁ : disp_univalent_category _) x)
  : is_cartesian (pr11 αα x xx).
Proof.
  intros z g zz gg.
  unfold is_cartesian_2cell in Hαα.
  cbn in Hαα.
  (*
  cbn in *.
  pose (Hαα (constant_functor C₁ C₂ z)) as i.
  cbn in i.
  assert (disp_functor (constant_functor C₁ C₂ z) (pr1 D₁) (pr1 D₂)).
  {
    use tpair.
    - simple refine ((λ _ _, zz) ,, (λ _ _ _ _ _ _, _)).
      exact (id_disp zz).
    - apply TODO.
  }
  specialize (i (X ,, TODO)).
  cbn.
  cbn in i.
   *)
  apply TODO.
Defined.

Definition cleaving_of_fibs_local_cleaving
  : local_cleaving disp_bicat_of_fibs.
Proof.
  intros C₁ C₂ D₁ D₂ F G GG α.
  cbn in *.
  simple refine (_ ,, _).
  - simple refine (_ ,, _).
    + exact (cartesian_factorisation_disp_functor (pr2 D₂) (pr1 GG) α).
    + apply cartesian_factorisation_disp_functor_is_cartesian.
      exact (pr2 GG).
  - simpl.
    simple refine ((_ ,, tt) ,, _).
    + exact (cartesian_factorisation_disp_functor_cell (pr2 D₂) (pr1 GG) α).
    + apply cleaving_of_fibs_is_cartesian_2cell.
      apply cartesian_factorisation_disp_functor_cell_is_cartesian.
Defined.

Definition cleaving_of_fibs_lwhisker_cartesian
  : lwhisker_cartesian disp_bicat_of_fibs.
Proof.
  intros C₁ C₂ C₃ D₁ D₂ D₃ H F G HH FF GG α αα Hαα.
  apply cleaving_of_fibs_is_cartesian_2cell.
  intros x xx ; cbn.
  apply (cleaving_of_fibs_cartesian_2cell_is_pointwise_cartesian _ Hαα).
Defined.

Definition cleaving_of_fibs_rwhisker_cartesian
  : rwhisker_cartesian disp_bicat_of_fibs.
Proof.
  intros C₁ C₂ C₃ D₁ D₂ D₃ H F G HH FF GG α αα Hαα.
  apply cleaving_of_fibs_is_cartesian_2cell.
  intros x xx ; cbn.
  pose (pr2 GG) as m.
  cbn in m.
  apply m.
  apply (cleaving_of_fibs_cartesian_2cell_is_pointwise_cartesian _ Hαα).
Defined.

(** Global cleaving *)
Definition cleaving_of_fibs_lift_obj
           {C₁ C₂ : bicat_of_univ_cats}
           (D₂ : disp_bicat_of_fibs C₂)
           (F : C₁ --> C₂)
  : disp_bicat_of_fibs C₁.
Proof.
  simple refine ((_ ,, _) ,, _).
  - exact (reindex_disp_cat F (pr11 D₂)).
  - exact (is_univalent_reindex_disp_cat F _ (pr21 D₂)).
  - exact (cleaving_reindex_disp_cat F _ (pr2 D₂)).
Defined.

Definition cleaving_of_fibs_lift_mor
           {C₁ C₂ : bicat_of_univ_cats}
           (D₂ : disp_bicat_of_fibs C₂)
           (F : C₁ --> C₂)
  : cleaving_of_fibs_lift_obj D₂ F -->[ F ] D₂.
Proof.
  simple refine (_ ,, _).
  - exact (reindex_disp_cat_disp_functor F (pr11 D₂)).
  - exact (is_cartesian_reindex_disp_cat_disp_functor F (pr11 D₂) (pr2 D₂)).
Defined.

Definition cleaving_of_fibs_lift_mor_lift_1cell
           {C₁ C₂ C₃ : bicat_of_univ_cats}
           {D₂ : disp_bicat_of_fibs C₂}
           {D₃ : disp_bicat_of_fibs C₃}
           {F : C₁ --> C₂}
           {H : C₃ --> C₁}
           (HH : D₃ -->[ H · F] D₂)
  : lift_1cell_factor disp_bicat_of_fibs (cleaving_of_fibs_lift_mor D₂ F) HH.
Proof.
  simple refine (_ ,, _).
  - simple refine (_ ,, _).
    + exact (lift_functor_into_reindex (pr1 HH)).
    + exact (is_cartesian_lift_functor_into_reindex (pr2 HH)).
  - simple refine ((_ ,, tt) ,, _).
    + exact (lift_functor_into_reindex_commute (pr1 HH)).
    + apply disp_bicat_of_fibs_is_disp_invertible_2cell.
      intros x xx.
      apply id_is_iso_disp.
Defined.

Section Lift2CellFibs.
  Context {C₁ C₂ C₃ : bicat_of_univ_cats}
          {F : C₁ --> C₂}
          {H₁ H₂ : C₃ --> C₁}
          {α : H₁ ==> H₂}
          {D₂ : disp_bicat_of_fibs C₂}
          {D₃ : disp_bicat_of_fibs C₃}
          {HH₁ : D₃ -->[ H₁ · F] D₂}
          {HH₂ : D₃ -->[ H₂ · F] D₂}
          (αα : HH₁ ==>[ α ▹ F] HH₂)
          (Lh : lift_1cell_factor _ (cleaving_of_fibs_lift_mor D₂ F) HH₁)
          (Lh' : lift_1cell_factor _ (cleaving_of_fibs_lift_mor D₂ F) HH₂).

  Definition cleaving_of_fibs_lift_2cell_data
    : disp_nat_trans_data
        (pr1 α)
        (pr11 Lh : disp_functor _ _ _)
        (pr11 Lh' : disp_functor _ _ _).
  Proof.
    intros x xx.
    simple refine (transportf
                     (λ z, _ -->[ z ] _)
                     _
                     (pr1 (pr112 Lh) x xx
                      ;; pr11 αα x xx
                      ;; inv_mor_disp_from_iso
                           (disp_bicat_of_fibs_disp_invertible_2cell_pointwise_inv
                              _
                              (pr2 Lh')
                              (pr22 Lh')
                              xx))%mor_disp).
    abstract
      (cbn ; unfold precomp_with ; cbn ;
       rewrite !id_left, id_right ;
       apply idpath).
  Defined.

  Definition cleaving_of_fibs_axioms
    : disp_nat_trans_axioms cleaving_of_fibs_lift_2cell_data.
  Proof.
    intros x y f xx yy ff.
    unfold cleaving_of_fibs_lift_2cell_data.
    cbn.
    unfold transportb.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    etrans.
    {
      pose (disp_nat_trans_ax (pr112 Lh) ff) as d.
      cbn in d.
      rewrite !assoc_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        exact d.
      }
      clear d.
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite !assoc_disp_var.
      rewrite !transport_f_f.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite assoc_disp.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (disp_nat_trans_ax (pr1 αα) ff).
        }
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite assoc_disp_var.
        rewrite transport_f_f.
        do 2 apply maponpaths.
        apply idpath.
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      do 3 apply maponpaths.
      exact (disp_nat_trans_ax (pr11 (pr22 Lh')) ff).
    }
    unfold transportb.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !transport_f_f.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !transport_f_f.
    cbn.
    refine (!_).
    etrans.
    {
      apply transportf_reindex.
    }
    rewrite transport_f_f.
    refine (!_).
    rewrite !assoc_disp.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Definition cleaving_of_fibs_lift_2cell
    : disp_nat_trans
        α
        (pr11 Lh : disp_functor _ _ _)
        (pr11 Lh' : disp_functor _ _ _).
  Proof.
    simple refine (_ ,, _).
    - exact cleaving_of_fibs_lift_2cell_data.
    - exact cleaving_of_fibs_axioms.
  Defined.

  Definition cleaving_of_fibs_unique_2_lifts
             (φ₁ φ₂ : lift_2cell_factor_type _ _ αα Lh Lh')
    : φ₁ = φ₂.
  Proof.
      use subtypePath.
      {
        intro.
        apply disp_bicat_of_fibs.
      }
      use subtypePath.
      {
        intro.
        apply isapropunit.
      }
      use disp_nat_trans_eq.
      intros x xx.
      pose (maponpaths (λ d, pr11 d x xx) (pr2 φ₁)) as p₁.
      cbn in p₁.
      rewrite pr1_transportf in p₁.
      unfold disp_cell_lift_1cell_factor in p₁.
      pose (disp_nat_trans_transportf
              _ _
              _ _
              (H₁ ∙ F) (H₂ ∙ F)
              _ _
              (id2_right (α ▹ F) @ ! id2_left (α ▹ F))
              (disp_functor_composite
                 (pr11 Lh)
                 (reindex_disp_cat_disp_functor F (pr11 D₂)))
              (pr1 HH₂)
              (disp_nat_trans_comp
                 (post_whisker_disp_nat_trans
                    (pr11 φ₁)
                    (reindex_disp_cat_disp_functor F (pr11 D₂)))
                 (pr112 Lh'))
              x
              xx) as p₁'.
      pose (!p₁' @ p₁) as r₁.
      pose (maponpaths (λ d, pr11 d x xx) (pr2 φ₂)) as p₂.
      cbn in p₂.
      rewrite pr1_transportf in p₂.
      unfold disp_cell_lift_1cell_factor in p₂.
      pose (disp_nat_trans_transportf
              _ _
              _ _
              (H₁ ∙ F) (H₂ ∙ F)
              _ _
              (id2_right (α ▹ F) @ ! id2_left (α ▹ F))
              (disp_functor_composite
                 (pr11 Lh)
                 (reindex_disp_cat_disp_functor F (pr11 D₂)))
              (pr1 HH₂)
              (disp_nat_trans_comp
                 (post_whisker_disp_nat_trans
                    (pr11 φ₂)
                    (reindex_disp_cat_disp_functor F (pr11 D₂)))
                 (pr112 Lh'))
              x
              xx) as p₂'.
      pose (!p₂' @ p₂) as r₂.
      cbn in r₂.
      assert (r := r₁ @ !r₂).
      clear p₁ p₂ p₁' p₂' r₁ r₂.
      cbn in r.
      assert (r' := maponpaths
                      (λ z₁, transportb
                               (λ z₂, _ -->[ z₂ ] _)
                               (nat_trans_eq_pointwise
                                  (id2_right (α ▹ F)
                                   @ ! id2_left (α ▹ F)) x)
                               z₁)
                      r).
      clear r ; cbn in r'.
      rewrite !transportbfinv in r'.
      assert (p := transportf_transpose_left
                     (inv_mor_after_iso_disp
                        (disp_bicat_of_fibs_disp_invertible_2cell_pointwise_inv
                           _
                           (pr2 Lh')
                           (pr22 Lh')
                           xx))).
      simpl in p.
      cbn.
      refine (id_right_disp_var _ @ _ @ !(id_right_disp_var _)).
      cbn.
      etrans.
      {
        do 2 apply maponpaths.
        exact (!p).
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        exact (!p).
      }
      clear p.
      refine (!_).
      cbn.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite !assoc_disp.
      unfold transportb.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact r'.
      }
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition cleaving_of_fibs_lift_mor_lift_2cell
    : lift_2cell_factor _ _ αα Lh Lh'.
  Proof.
    use iscontraprop1.
    - use invproofirrelevance.
      intros φ₁ φ₂.
      exact (cleaving_of_fibs_unique_2_lifts φ₁ φ₂).
    - simple refine ((_ ,, tt) ,, _).
      + exact cleaving_of_fibs_lift_2cell.
      + abstract
          (cbn ;
           use subtypePath ; [ intro ; apply isapropunit | ] ;
           use disp_nat_trans_eq ;
           intros x xx ;
           cbn ;
           rewrite pr1_transportf ;
           unfold disp_cell_lift_1cell_factor ;
           refine (disp_nat_trans_transportf
                     _ _
                     _ _
                     (H₁ ∙ F) (H₂ ∙ F)
                     _ _
                     (id2_right (α ▹ F) @ ! id2_left (α ▹ F))
                     (disp_functor_composite
                        (pr11 Lh)
                        (reindex_disp_cat_disp_functor F (pr11 D₂)))
                     (pr1 HH₂)
                     (disp_nat_trans_comp
                        (post_whisker_disp_nat_trans
                           cleaving_of_fibs_lift_2cell
                           (reindex_disp_cat_disp_functor F (pr11 D₂)))
                        (pr112 Lh'))
                     x
                     xx
                     @ _) ;
           cbn ;
           unfold cleaving_of_fibs_lift_2cell_data ;
           rewrite !mor_disp_transportf_postwhisker ;
           rewrite !transport_f_f ;
           rewrite !assoc_disp_var ;
           rewrite !transport_f_f ;
           etrans ;
           [ do 3 apply maponpaths ;
             apply (iso_disp_after_inv_mor
                      (disp_bicat_of_fibs_disp_invertible_2cell_pointwise_inv
                         (id2_invertible_2cell (H₂ · F))
                         (pr2 Lh') (pr22 Lh') xx))
           | ] ;
           unfold transportb ;
           rewrite !mor_disp_transportf_prewhisker ;
           rewrite transport_f_f ;
           rewrite id_right_disp ;
           unfold transportb ;
           rewrite mor_disp_transportf_prewhisker ;
           rewrite transport_f_f ;
           apply transportf_set ;
           apply homset_property).
  Defined.
End Lift2CellFibs.



Definition total_univalent_category
           {C : univalent_category}
           (D : disp_univalent_category C)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (total_category D).
  - exact (is_univalent_total_category (pr2 C) (pr2 D)).
Defined.

Definition unit_disp_cat
           (C : category)
  : disp_cat C.
Proof.
  simple refine (_ ,, _).
  - simple refine (_ ,, _).
    + simple refine (_ ,, _).
      * exact (λ _, unit).
      * exact (λ _ _ _ _ _, unit).
    + split.
      * exact (λ _ _, tt).
      * exact (λ _ _ _ _ _ _ _ _ _ _, tt).
  - abstract
      (repeat split ; intro ; intros ; try (apply isapropunit) ;
       apply isasetaprop ;
       apply isapropunit).
Defined.

Definition is_disp_univalent_unit_disp_cat
           (C : category)
  : is_univalent_disp (unit_disp_cat C).
Proof.
  intros x y p xx yy.
  induction p.
  use isweqimplimpl.
  * intro.
    apply isapropunit.
  * apply isapropifcontr.
    apply isapropunit.
  * use isaproptotal2.
    ** intro.
       apply isaprop_is_iso_disp.
    ** intros.
       apply isapropunit.
Qed.

Definition unit_univalent_disp_cat
           (C : category)
  : disp_univalent_category C
  := (unit_disp_cat C ,, is_disp_univalent_unit_disp_cat C).

Definition cleaving_unit_disp_cat
           (C : category)
  : cleaving (unit_disp_cat C).
Proof.
  intros x y f yy.
  simple refine (tt ,, tt ,, _).
  intros z g zz gf.
  use iscontraprop1.
  - use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath ; [ intro ; apply isapropifcontr ; apply isapropunit | ].
    apply isapropunit.
  - simple refine (tt ,, _).
    apply isapropunit.
Defined.

(*
Section Cartesian1Cell.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F : C₁ --> C₂}
          {D₁ : disp_bicat_of_fibs C₁}
          {D₂ : disp_bicat_of_fibs C₂}
          {FF : D₁ -->[ F ] D₂}
          (HFF : cartesian_1cell _ FF).

  Let totD₁ : bicat_of_univ_cats := total_univalent_category (pr1 D₁).
  Let totD₂ : bicat_of_univ_cats := total_univalent_category (pr1 D₂).
  Let π₁ : pr1 totD₁ ⟶ pr1 C₁ := pr1_category (pr11 D₁).
  Let π₂ : pr1 totD₂ ⟶ pr1 C₂ := pr1_category (pr11 D₂).
  Let totF : pr1 totD₁ ⟶ pr1 totD₂ := total_functor (pr1 FF).

  Local Definition cone_commutes_nat_trans
    : π₁ ∙ F ⟹ totF ∙ π₂.
  Proof.
    use make_nat_trans.
    - exact (λ x, identity _).
    - abstract
        (intros x y f ;
         cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Local Definition cone_commutes
    : nat_iso (π₁ ∙ F) (totF ∙ π₂).
  Proof.
    use make_nat_iso.
    - exact cone_commutes_nat_trans.
    - intros x.
      apply identity_is_iso.
  Defined.

  Definition cartesian_to_cone
    : pb_cone F π₂
    := make_pb_cone
         totD₁
         π₁
         totF
         (nat_iso_to_invertible_2cell
            _ _
            cone_commutes).

  Section UMP1.
    Variable (q : pb_cone F π₂).

    Let υ : disp_bicat_of_fibs q
      := (unit_univalent_disp_cat (pr11 q) ,, cleaving_unit_disp_cat _).
    Let qπ₁ : pr11 q ⟶ pr1 C₁ := pb_cone_pr1 q.
    Let qπ₂ : pr11 q ⟶ pr1 totD₂ := pb_cone_pr2 q.
    Let qc : nat_iso (pb_cone_pr1 q ∙ F) (pb_cone_pr2 q ∙ π₂)
      := invertible_2cell_to_nat_iso _ _ (pb_cone_cell q).

    Definition test_data
      : disp_functor_data (qπ₁ ∙ F) (pr11 υ) (pr11 D₂).
    Proof.
      simple refine (_ ,, _).
      - exact (λ x _, transportf
                        _
                        (isotoid
                           _
                           (pr2 C₂)
                           (iso_inv_from_iso (nat_iso_pointwise_iso qc x)))
                        (pr2 (qπ₂ x))).
      - cbn.
        refine (λ x y _ _ f _, _).
        cbn.
        pose (pr2 (#qπ₂ f)) as m.
        cbn in m.
    Admitted.

    Definition test
      : disp_functor (qπ₁ ∙ F) (pr11 υ) (pr11 D₂).
    Proof.
      simple refine (_ ,, _).
      - simple refine (_ ,, _).
        + cbn.
          refine (λ x _, _).
          Check qπ₂ x.
          pose (qπ₂).
    Admitted.
  End UMP1.

  Definition cartesian_to_pb_ump_1
    : pb_ump_1 cartesian_to_cone.
  Proof.
    (*
    intro q.
    use make_pb_1cell.
    - pose (@cartesian_1cell_lift_1cell
              _ _ _ _ _ _ _ _
              HFF
              q
              (υ q)
              (pb_cone_pr1 q)).
      cbn in l.

      pose (pb_cone_pr2 q) as m.
      cbn in m.
      cbn.

      assert (disp_functor (pb_cone_pr1 q ∙ F) (unit_disp_cat (pr11 q)) (pr11 D₂)).
      {
        simple refine (_ ,, _).
        - simple refine (_ ,, _).
          + cbn.
            intros x y.
            refine (transportf
                      (pr11 D₂)
                      _
                      (pr2 (pr1 (pb_cone_pr2 q) x))).
            (*
            pose (pr11 (pb_cone_cell q) x) as i.
            cbn in i.
             *)
            apply TODO.
          + cbn.
            intros x y ? ? f ?.
            pose (#(pr1 (pb_cone_pr2 q)) f).
            cbn in p.
            apply TODO.
        - split ; apply TODO.
      }

      cbn.
      Check (pr12 q).
      destruct q as [q₁ [q₂ [q₃ q₄]]].
      cbn in q₁, q₂, q₃, q₄.
      cbn in l.
      cbn.
      use make_functor.
      + use make_functor_data.
        * refine (λ x, q₂ x ,, _).
          apply TODO.
        * simpl.
          refine (λ x y f, # q₂ f ,, _).
          apply TODO.
      + split.
        * intro x.
          cbn.
          apply TODO.
        * apply TODO.
    - cbn.
      use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      + use make_nat_trans.
        * intro x ; cbn.
          apply identity.
        * cbn.
          intros x y f ; cbn.
          rewrite id_left, id_right.
          apply idpath.
      + apply TODO.
    - cbn.
      use nat_iso_to_invertible_2cell.
      use make_nat_iso.
      + use make_nat_trans.
        * intro x ; cbn.
          simple refine (_ ,, _).
          ** exact (pr11 (pr222 q) x).
          ** cbn.
             apply TODO.
        * intros x y f.
          cbn.
          use total2_paths_f.
          ** exact (nat_trans_ax (pr1 (pr222 q)) x y f).
          ** cbn.
             apply TODO.
      + apply TODO.
    - use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      simpl.
      rewrite !id_left, !id_right.
      rewrite (functor_id F).
      rewrite id_left.
      cbn.
      apply TODO.
     *)
    apply TODO.
  Defined.

  Definition cartesian_to_pb_ump_2
    : pb_ump_2 cartesian_to_cone.
  Proof.
    (*
    intros q φ ψ.
    use make_pb_2cell.
    - use make_nat_trans.
      + intros x.
        (*
        simple refine (_ ,, _).
        * pose (pr11 (pb_1cell_pr1 φ) x) as p.
          refine (pr11 (pb_1cell_pr1 φ) x · _).
          apply TODO.
        * cbn.
          apply TODO.
         *)
        apply TODO.
      + apply TODO.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      apply TODO.
    - use nat_trans_eq ; [ apply homset_property | ].
      intro x ; cbn.
      use total2_paths_f.
      + cbn.
        apply TODO.
      + apply TODO.
     *)
    apply TODO.
  Defined.

  Definition cartesian_to_pb_ump_eq
    : pb_ump_eq cartesian_to_cone.
  Proof.
    intros q φ ψ η₁ η₂.
    use subtypePath.
    {
      intro.
      use isapropdirprod ; apply cellset_property.
    }
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    pose (nat_trans_eq_pointwise (pr12 η₁) x) as p₁.
    pose (nat_trans_eq_pointwise (pr22 η₁) x) as q₁.
    pose (nat_trans_eq_pointwise (pr12 η₂) x) as p₂.
    pose (nat_trans_eq_pointwise (pr22 η₂) x) as q₂.
    pose (r := p₁ @ !p₂).
    pose (r' := q₁ @ !q₂).
    cbn in p₁, q₁, p₂, q₂, r, r'.

    Check (isaprop_lift_of_lift_2cell
             disp_bicat_of_fibs).
             HFF).
    use total2_paths_f.

    - pose (base_paths _ _ r') as p.
      cbn in p.
      apply TODO.
    - apply TODO.
  Qed.

  Definition cartesian_to_pb_ump
    : has_pb_ump cartesian_to_cone.
  Proof.
    use make_has_pb_ump.
    - exact cartesian_to_pb_ump_1.
    - exact cartesian_to_pb_ump_2.
    - exact cartesian_to_pb_ump_eq.
  Defined.
                 End Cartesian1Cell.
                 *)

Definition cleaving_of_fibs_lift_mor_cartesian
           {C₁ C₂ : bicat_of_univ_cats}
           (D₂ : disp_bicat_of_fibs C₂)
           (F : C₁ --> C₂)
  : cartesian_1cell disp_bicat_of_fibs (cleaving_of_fibs_lift_mor D₂ F).
Proof.
  simple refine (_ ,, _).
  - intros C₃ D₃ H HH.
    exact (cleaving_of_fibs_lift_mor_lift_1cell HH).
  - intros C₃ D₃ H₁ H₂ HH₁ HH₂ α αα Lh Lh'.
    exact (cleaving_of_fibs_lift_mor_lift_2cell αα Lh Lh').
Defined.

Definition cleaving_of_fibs_global_cleaving
  : global_cleaving disp_bicat_of_fibs.
Proof.
  intros C₁ C₂ D₂ F.
  simple refine (_ ,, _ ,, _).
  - exact (cleaving_of_fibs_lift_obj D₂ F).
  - exact (cleaving_of_fibs_lift_mor D₂ F).
  - exact (cleaving_of_fibs_lift_mor_cartesian D₂ F).
Defined.

Definition cleaving_of_fibs
  : cleaving_of_bicats disp_bicat_of_fibs.
Proof.
  repeat split.
  - exact cleaving_of_fibs_local_cleaving.
  - exact cleaving_of_fibs_global_cleaving.
  - exact cleaving_of_fibs_lwhisker_cartesian.
  - exact cleaving_of_fibs_rwhisker_cartesian.
Defined.
