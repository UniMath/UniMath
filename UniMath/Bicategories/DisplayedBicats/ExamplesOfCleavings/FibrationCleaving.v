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

Local Open Scope cat.

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

Section CleavingOfFibsPointwiseCartesian.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F₁ F₂ : C₁ --> C₂}
          {α : F₁ ==> F₂}
          {D₁ : disp_bicat_of_fibs C₁}
          {D₂ : disp_bicat_of_fibs C₂}
          {FF₁ : D₁ -->[ F₁ ] D₂}
          {FF₂ : D₁ -->[ F₂ ] D₂}
          (αα : FF₁ ==>[ α ] FF₂)
          (Hαα : is_cartesian_2cell disp_bicat_of_fibs αα).

  Let lift_FF₂
    : disp_functor F₁ (pr11 D₁) (pr11 D₂)
    := cartesian_factorisation_disp_functor
           (pr2 D₂)
           (pr1 FF₂)
           α.
  Let lift_FF₂_fib
    : D₁ -->[ F₁ ] D₂.
  Proof.
    refine (lift_FF₂ ,, _).
    apply cartesian_factorisation_disp_functor_is_cartesian.
    apply (pr2 FF₂).
  Defined.

  Definition pointwise_cartesian_lift_data
    : disp_nat_trans_data
        (pr1 α)
        lift_FF₂
        (pr11 FF₂)
    := λ x xx, cleaving_mor (pr2 D₂) (pr1 α x) (pr11 FF₂ x xx).

  Definition pointwise_cartesian_lift_axioms
    : disp_nat_trans_axioms pointwise_cartesian_lift_data.
  Proof.
    intros x y f xx yy ff.
    apply cartesian_factorisation_commutes.
  Qed.

  Definition pointwise_cartesian_lift
    : disp_nat_trans
        α
        (cartesian_factorisation_disp_functor
           (pr2 D₂)
           (pr1 FF₂)
           α)
        (pr11 FF₂)
    := (pointwise_cartesian_lift_data ,, pointwise_cartesian_lift_axioms).

  Definition pointwise_cartesian_lift_fib
    : lift_FF₂_fib ==>[ α ] FF₂
    := (pointwise_cartesian_lift ,, tt).

  Definition pointwise_cartesian_lift_data_pointwise_cartesian
    : ∏ (x : (C₁ : univalent_category))
        (xx : (pr1 D₁ : disp_univalent_category _) x),
      is_cartesian (pointwise_cartesian_lift x xx).
  Proof.
    intros x xx.
    apply cartesian_lift_is_cartesian.
  Qed.

  Definition pointwise_cartesian_lift_data_is_cartesian
    : is_cartesian_2cell
        disp_bicat_of_fibs
        pointwise_cartesian_lift_fib.
  Proof.
    apply cleaving_of_fibs_is_cartesian_2cell.
    exact pointwise_cartesian_lift_data_pointwise_cartesian.
  Defined.

  Section PointwiseCartesian.
    Context (x : (C₁ : univalent_category))
            (xx : (pr1 D₁ : disp_univalent_category _) x).

    Local Lemma cleaving_of_fibs_cartesian_2cell_is_pointwise_cartesian_path
      : (pr11 αα) x xx
        =
        transportf
          (λ z, _ -->[ z ] _)
          (nat_trans_eq_pointwise (id2_left α) x)
          (cartesian_factorisation_disp_nat_trans_data
             pointwise_cartesian_lift
             (pr1
                (transportb
                   (λ z, ∑ _ : disp_nat_trans z (pr11 FF₁) (pr11 FF₂), unit)
                   (id2_left α) αα))
             pointwise_cartesian_lift_data_pointwise_cartesian
             x
             xx
           ;;
           pointwise_cartesian_lift_data x xx)%mor_disp.
    Proof.
      pose (maponpaths
            (λ z, pr11 z x xx)
            (is_cartesian_2cell_unique_iso_com
               Hαα
               pointwise_cartesian_lift_data_is_cartesian))
        as p.
      cbn in p.
      rewrite pr1_transportf in p.
      exact (p @ disp_nat_trans_transportf _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    Qed.

    Definition cleaving_of_fibs_cartesian_2cell_is_pointwise_cartesian
      : is_cartesian (pr11 αα x xx).
    Proof.
      refine (transportb
                is_cartesian
                cleaving_of_fibs_cartesian_2cell_is_pointwise_cartesian_path
                _).
      apply is_cartesian_transportf.
      use is_cartesian_comp_disp.
      - exact (is_cartesian_iso_disp
                 (disp_bicat_of_fibs_disp_invertible_2cell_pointwise_inv
                    _
                    _
                    (pr2 (is_cartesian_2cell_unique_iso
                            Hαα
                            pointwise_cartesian_lift_data_is_cartesian))
                    xx)).
      - apply pointwise_cartesian_lift_data_pointwise_cartesian.
    Defined.
  End PointwiseCartesian.
End CleavingOfFibsPointwiseCartesian.

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
  intros x xx.
  cbn.
  apply cleaving_of_fibs_cartesian_2cell_is_pointwise_cartesian.
  exact Hαα.
Defined.

Definition cleaving_of_fibs_rwhisker_cartesian
  : rwhisker_cartesian disp_bicat_of_fibs.
Proof.
  intros C₁ C₂ C₃ D₁ D₂ D₃ H F G HH FF GG α αα Hαα.
  apply cleaving_of_fibs_is_cartesian_2cell.
  intros x xx.
  pose (pr2 GG) as pr2GG.
  cbn ; cbn in pr2GG.
  apply pr2GG.
  apply cleaving_of_fibs_cartesian_2cell_is_pointwise_cartesian.
  exact Hαα.
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
