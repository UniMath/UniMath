(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

 Displayed bicategory of displayed structures on 1-categories.

 Contents
 1. The displayed bicategory of displayed categories
 2. Invertible 2-cells in the displayed bicategory of displayed categories
 3. The local univalence
 4. Adjoints equivalences
 5. The global univalence

 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Adjunctions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedFunctorEq.
Require Import UniMath.CategoryTheory.DisplayedCats.EquivalenceOverId.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayedCatEq.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(**
 1. The displayed bicategory of displayed categories
 *)
Definition disp_bicat_of_univ_disp_cats_disp_cat_data
  : disp_cat_data bicat_of_univ_cats.
Proof.
  use tpair.
  - use tpair.
    + exact (λ C : univalent_category, disp_univalent_category C).
    + intros C C' D D' F.
      exact (disp_functor F D D').
  - use tpair; cbn.
    + intros C D.
      apply disp_functor_identity.
    + cbn. intros C C' C'' F F' D D' D'' G G'.
      apply (disp_functor_composite G G').
Defined.

Definition disp_bicat_of_univ_disp_cats_1_id_comp_cells
  : disp_prebicat_1_id_comp_cells bicat_of_univ_cats.
Proof.
  exists disp_bicat_of_univ_disp_cats_disp_cat_data.
  cbn. intros C C' F F' a D D' G G'. cbn in *.
  apply (disp_nat_trans a G G').
Defined.

Definition disp_prebicat_of_univ_disp_cats_data : disp_prebicat_data bicat_of_univ_cats.
Proof.
  exists disp_bicat_of_univ_disp_cats_1_id_comp_cells.
  repeat split.
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id F').
  - intros ? ? ? ? ? ? ? ? ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id (disp_functor_composite_data (disp_functor_composite ff gg) F')).
  - intros ? ? ? ? ? ? ? ? ? ? ? ? ? F' ; cbn in *.
    exact (disp_nat_trans_id (disp_functor_composite_data (disp_functor_composite ff gg) F')).
  - intros C D ? ? ? ? ? ? ? ? ? ? rr ss ; cbn in *.
    exact (@disp_nat_trans_comp C _ _ _ _ _ _ _ _ _ _ _ rr ss).
  - intros C₁ C₂ C₃ f g₁ g₂ r D₁ D₂ D₃ ff gg₁ gg₂ rr ; cbn in *.
    exact (@pre_whisker_disp_nat_trans C₁ C₂ _ _ _ _ _ _ _ _ _ _ _ rr).
  - intros C₁ C₂ C₃ ? ? ? ? ? ? ? ? ? ? rr ; cbn in *.
    exact (@post_whisker_disp_nat_trans C₁ C₂ _ _ _ _ _ _ _ _ _ _ rr _).
Defined.

Lemma disp_prebicat_of_univ_disp_cats_laws
  : disp_prebicat_laws disp_prebicat_of_univ_disp_cats_data.
Proof.
  repeat split ; red
  ; intros; intros
  ; apply (@disp_nat_trans_eq)
  ; intros ; apply pathsinv0
  ; unfold transportb
  ; (etrans ; [ apply disp_nat_trans_transportf | ]).
  - apply pathsinv0.
    etrans. { apply id_left_disp. }
    apply pathsinv0; unfold transportb.
    apply maponpaths_2. apply homset_property.
  - apply pathsinv0.
    etrans. { apply id_right_disp. }
    apply pathsinv0; unfold transportb.
    apply maponpaths_2. apply homset_property.
  - apply pathsinv0.
    etrans. { apply assoc_disp. }
    apply pathsinv0; unfold transportb.
    apply maponpaths_2. apply homset_property.
  - apply transportf_set. apply homset_property.
  - apply pathsinv0.
    etrans.
    {
      cbn.
      apply disp_functor_id.
    }
    unfold transportb.
    apply maponpaths_2. apply homset_property.
  - apply transportf_set. apply homset_property.
  - cbn.
    etrans.
    {
      apply maponpaths.
      apply disp_functor_comp.
    }
    etrans. { apply transport_f_f. }
    apply transportf_set. apply homset_property.
  - cbn.
    etrans.
    {
      apply maponpaths.
      apply id_left_disp.
    }
    etrans. { apply transport_f_f. }
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    etrans. { apply maponpaths. apply id_left_disp. }
    etrans. { apply transport_f_f. }
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    etrans.
    {
      apply maponpaths.
      apply id_left_disp.
    }
    etrans. { apply transport_f_f. }
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    etrans. { apply maponpaths. apply id_left_disp. }
    etrans. { apply transport_f_f. }
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    etrans. { apply maponpaths. apply id_right_disp. }
    etrans. { apply transport_f_f. }
    apply pathsinv0.
    etrans. { apply id_left_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    set (RR := @disp_nat_trans_ax_var _ _ _ _ _ _ _ _ _ φφ).
    etrans. { apply maponpaths. apply RR. }
    etrans. { apply transport_f_f. }
    apply transportf_set. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. { apply id_right_disp. }
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. { apply id_left_disp. }
    etrans. { apply maponpaths. apply disp_functor_id. }
    etrans. { apply transport_f_f. }
    apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. { apply assoc_disp_var. }
    etrans. { apply maponpaths. apply id_left_disp. }
    etrans. { apply transport_f_f. }
    etrans. { apply maponpaths. apply id_left_disp. }
    etrans. { apply transport_f_f. }
    etrans. { apply maponpaths. apply disp_functor_id. }
    etrans. { apply transport_f_f. }
    apply pathsinv0.
    etrans. { apply maponpaths. apply id_left_disp. }
    etrans. { apply transport_f_f. }
    apply maponpaths_2. apply homset_property.
Qed.

Definition disp_prebicat_of_univ_disp_cats
  : disp_prebicat bicat_of_univ_cats
  := _ ,, disp_prebicat_of_univ_disp_cats_laws.

Definition disp_bicat_of_univ_disp_cats : disp_bicat bicat_of_univ_cats.
Proof.
  use tpair.
  - exact disp_prebicat_of_univ_disp_cats.
  - abstract
      (intros C₁ C₂ F₁ F₂ n D₁ D₂ FF₁ FF₂ ;
       simpl in * ;
       cbn ;
       exact (@isaset_disp_nat_trans C₁ C₂ D₁ D₂ F₁ F₂ n FF₁ FF₂)).
Defined.

(**
 2. Invertible 2-cells in the displayed bicategory of displayed categories
 *)
Definition disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell
           {C C' : bicat_of_univ_cats}
           {F : C --> C'}
           {D : disp_bicat_of_univ_disp_cats C}
           {D' : disp_bicat_of_univ_disp_cats C'}
           {FF : D -->[ F ] D'} {GG : D -->[ F ] D'}
           (αα : FF ==>[ id₂ F ] GG)
           (Hαα : is_disp_nat_z_iso (nat_z_iso_id _) αα)
  : is_disp_invertible_2cell (id2_invertible_2cell F) αα.
Proof.
  use tpair.
  - exact (pointwise_inverse_disp_nat_trans αα Hαα).
  - split.
    + abstract
        (cbn ;
         simpl in * ;
         use (@disp_nat_trans_eq C C') ;
         intros x xx ; cbn ;
         refine (inv_mor_after_z_iso_disp (Hαα x xx) @ _) ;
         refine (!_) ;
         refine (@disp_nat_trans_transportf
                   _ _ _ _ _ _
                   _ _
                   (!(@id2_left bicat_of_univ_cats _ _ _ _ (nat_trans_id F)))
                   _ _ _ _ _
                   @ _) ;
         apply transportf_paths ;
         apply homset_property).
    + abstract
        (cbn ;
         simpl in * ;
         use (@disp_nat_trans_eq C C') ;
         intros x xx ; cbn ;
         refine (z_iso_disp_after_inv_mor (Hαα x xx) @ _) ;
         refine (!_) ;
         refine (@disp_nat_trans_transportf
                   _ _ _ _ _ _
                   _ _
                   (!(@id2_left bicat_of_univ_cats _ _ _ _ (nat_trans_id F)))
                   _ _ _ _ _
                   @ _) ;
         apply transportf_paths ;
         apply homset_property).
Defined.

(**
 This function is more convenient to use in certain cases. In the proof of global
 univalence, we look at invertible 2-cells over the unitors. The data of these
 2-cells are equal to the identity transformations, but they have a different
 proof of invertibility.
 *)
Lemma disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell_help
      {C C' : bicat_of_univ_cats}
      {F : C --> C'}
      {D : disp_bicat_of_univ_disp_cats C}
      {D' : disp_bicat_of_univ_disp_cats C'}
      {FF : D -->[ F ] D'} {GG : D -->[ F ] D'}
      (αα : FF ==>[ id₂ F ] GG)
      (Hαα : is_disp_nat_z_iso (nat_z_iso_id _) αα)
      (H : @is_invertible_2cell
             bicat_of_univ_cats
             C C'
             F F
             (nat_trans_id _))
  : is_disp_invertible_2cell H αα.
Proof.
  refine (transportf
            (λ z, is_disp_invertible_2cell z αα)
            _
            (disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell αα Hαα)).
  apply isaprop_is_invertible_2cell.
Qed.

Definition from_disp_bicat_of_univ_disp_cats_disp_invertible_2cell
           {C C' : bicat_of_univ_cats}
           {F : C --> C'}
           {D : disp_bicat_of_univ_disp_cats C}
           {D' : disp_bicat_of_univ_disp_cats C'}
           {FF : D -->[ F ] D'} {GG : D -->[ F ] D'}
           (αα : FF ==>[ id₂ F ] GG)
           (Hαα : is_disp_invertible_2cell (id2_invertible_2cell F) αα)
  : is_disp_nat_z_iso (nat_z_iso_id _) αα.
Proof.
  intros x xx.
  simple refine (_ ,, _ ,, _).
  - exact (pr11 Hαα x xx).
  - abstract
      (refine (maponpaths (λ z, pr1 z x xx) (pr22 Hαα) @ _) ;
       cbn ;
       unfold transportb ;
       rewrite disp_nat_trans_transportf ;
       apply maponpaths_2 ;
       apply homset_property).
  - abstract
      (refine (maponpaths (λ z, pr1 z x xx) (pr12 Hαα) @ _) ;
       cbn ;
       unfold transportb ;
       rewrite disp_nat_trans_transportf ;
       apply maponpaths_2 ;
       apply homset_property).
Defined.

(**
 This function is more convenient to use in certain cases. In the proof of global
 univalence, we look at invertible 2-cells over the unitors. The data of these
 2-cells are equal to the identity transformations, but they have a different
 proof of invertibility.
 *)
Lemma from_disp_bicat_of_univ_disp_cats_disp_invertible_2cell_help
      {C C' : bicat_of_univ_cats}
      {F : C --> C'}
      {D : disp_bicat_of_univ_disp_cats C}
      {D' : disp_bicat_of_univ_disp_cats C'}
      {FF : D -->[ F ] D'} {GG : D -->[ F ] D'}
      (αα : FF ==>[ id₂ F ] GG)
      (H : @is_invertible_2cell
             bicat_of_univ_cats
             C C'
             F F
             (nat_trans_id _))
      (Hαα : is_disp_invertible_2cell H αα)
  : is_disp_nat_z_iso (nat_z_iso_id _) αα.
Proof.
  apply from_disp_bicat_of_univ_disp_cats_disp_invertible_2cell.
  refine (transportf
            (λ z, is_disp_invertible_2cell z αα)
            _
            Hαα).
  apply isaprop_is_invertible_2cell.
Qed.

Definition disp_bicat_of_univ_disp_cats_inv2cell_weq
           {C₁ C₂ : bicat_of_univ_cats}
           {F : C₁ --> C₂}
           {D₁ : disp_bicat_of_univ_disp_cats C₁}
           {D₂ : disp_bicat_of_univ_disp_cats C₂}
           (FF GG : D₁ -->[ F ] D₂)
  : disp_nat_z_iso FF GG (nat_z_iso_id F)
    ≃
    disp_invertible_2cell (id2_invertible_2cell F) FF GG.
Proof.
  use weqfibtototal.
  intro τ.
  use weqimplimpl.
  - exact (disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell τ).
  - exact (from_disp_bicat_of_univ_disp_cats_disp_invertible_2cell τ).
  - apply isaprop_is_disp_nat_z_iso.
  - apply isaprop_is_disp_invertible_2cell.
Defined.

(**
 3. The local univalence
 *)
Proposition disp_univalent_2_1_disp_bicat_of_univ_disp_cat
  : disp_univalent_2_1 disp_bicat_of_univ_disp_cats.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  intros C₁ C₂ F D₁ D₂ FF GG.
  use weqhomot.
  - exact (disp_bicat_of_univ_disp_cats_inv2cell_weq FF GG
           ∘ disp_functor_eq_weq FF GG (pr2 D₂))%weq.
  - abstract
      (intro p ;
       cbn in p ;
       induction p ;
       use subtypePath ; [ intro ; apply isaprop_is_disp_invertible_2cell | ] ;
       use disp_nat_trans_eq ;
       intros x xx ;
       cbn ;
       apply idpath).
Defined.

(**
 4. Adjoints equivalences
 *)
Definition disp_left_adjoint_equivalence_disp_bicat_of_univ_cats
           {C : bicat_of_univ_cats}
           {D₁ D₂ : disp_bicat_of_univ_disp_cats C}
           (F : D₁ -->[ functor_identity _ ] D₂)
           (HF : is_equiv_over_id F)
  : disp_left_adjoint_equivalence (internal_adjoint_equivalence_identity C) F.
Proof.
  simple refine ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _))).
  - exact (pr111 HF).
  - exact (pr1 (pr211 HF)).
  - exact (pr2 (pr211 HF)).
  - abstract
      (use disp_nat_trans_eq ;
       intros x xx ; cbn ;
       rewrite id_left_disp ;
       rewrite !id_right_disp ;
       unfold transportb ;
       rewrite !mor_disp_transportf_postwhisker ;
       rewrite !transport_f_f ;
       etrans ;
       [ apply maponpaths ;
         exact (pr121 HF x xx)
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       refine (!_) ;
       refine (disp_nat_trans_transportf
                 _ _
                 _ _
                 (!(internal_triangle1 (is_internal_adjunction_identity C)))
                 _ _
                 (disp_nat_trans_id _)
                 x xx
               @ _) ;
       apply maponpaths_2 ;
       apply homset_property).
  - abstract
      (use disp_nat_trans_eq ;
       intros x xx ; cbn ;
       rewrite id_left_disp ;
       rewrite !id_right_disp ;
       unfold transportb ;
       rewrite !mor_disp_transportf_postwhisker ;
       rewrite !transport_f_f ;
       etrans ;
       [ apply maponpaths ;
         exact (pr221 HF x xx)
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       refine (!_) ;
       refine (disp_nat_trans_transportf
                 _ _
                 _ _
                 (!(internal_triangle2 (is_internal_adjunction_identity C)))
                 _ _
                 (disp_nat_trans_id _)
                 x _
               @ _) ;
       apply maponpaths_2 ;
       apply homset_property).
  - abstract
      (use disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell_help ;
       cbn ;
       intros x xx ;
       exact (pr12 HF x xx)).
  - abstract
      (use disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell_help ;
       cbn ;
       intros x xx ;
       exact (pr22 HF x xx)).
Defined.

Definition from_disp_left_adjoint_equivalence_disp_bicat_of_univ_cats
           {C : bicat_of_univ_cats}
           {D₁ D₂ : disp_bicat_of_univ_disp_cats C}
           (F : D₁ -->[ functor_identity _ ] D₂)
           (HF : disp_left_adjoint_equivalence (internal_adjoint_equivalence_identity C) F)
  : is_equiv_over_id F.
Proof.
  simple refine (((_ ,, (_ ,, _)) ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (pr11 HF).
  - exact (pr121 HF).
  - exact (pr221 HF).
  - abstract
      (intros x xx ;
       cbn ;
       pose (maponpaths (λ z, pr1 z x xx) (pr112 HF)) as p ;
       cbn in p ;
       rewrite !id_left_disp in p ;
       rewrite !id_right_disp in p ;
       unfold transportb in p ;
       rewrite !mor_disp_transportf_postwhisker in p ;
       rewrite !transport_f_f in p ;
       refine (transportb_transpose_right p @ _) ;
       etrans ;
       [ apply maponpaths ;
         apply (disp_nat_trans_transportf
                  _ _
                  _ _
                  (!(internal_triangle1 (is_internal_adjunction_identity C)))
                  _ _
                  (disp_nat_trans_id _)
                  x xx)
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply homset_property).
  - abstract
      (intros x xx ;
       cbn ;
       pose (maponpaths (λ z, pr1 z x xx) (pr212 HF)) as p ;
       cbn in p ;
       rewrite !id_left_disp in p ;
       rewrite !id_right_disp in p ;
       unfold transportb in p ;
       rewrite !mor_disp_transportf_postwhisker in p ;
       rewrite !transport_f_f in p ;
       refine (transportb_transpose_right p @ _) ;
       etrans ;
       [ apply maponpaths ;
         apply (disp_nat_trans_transportf
                  _ _
                  _ _
                  (!(internal_triangle2 (is_internal_adjunction_identity C)))
                  _ _
                  (disp_nat_trans_id _)
                  x xx)
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply homset_property).
  - abstract
      (cbn ;
       intros x xx ;
       apply (from_disp_bicat_of_univ_disp_cats_disp_invertible_2cell_help
                _ _
                (pr122 HF))).
- abstract
      (cbn ;
       intros x xx ;
       apply (from_disp_bicat_of_univ_disp_cats_disp_invertible_2cell_help
                _ _
                (pr222 HF))).
Defined.

Definition disp_bicat_of_univ_disp_cats_adjequiv_weq
           {C : bicat_of_univ_cats}
           (D₁ : disp_bicat_of_univ_disp_cats C)
           (D₂ : disp_bicat_of_univ_disp_cats C)
  : (∑ (F : disp_functor (functor_identity _) (pr1 D₁) (pr1 D₂)), is_equiv_over_id F)
    ≃
    disp_adjoint_equivalence (internal_adjoint_equivalence_identity C) D₁ D₂.
Proof.
  use weqfibtototal.
  intro F.
  use weqimplimpl.
  - exact (disp_left_adjoint_equivalence_disp_bicat_of_univ_cats F).
  - exact (from_disp_left_adjoint_equivalence_disp_bicat_of_univ_cats F).
  - apply isaprop_is_equiv_over_id.
    + exact (pr2 D₁).
    + exact (pr2 D₂).
  - use isaprop_disp_left_adjoint_equivalence.
    + exact univalent_cat_is_univalent_2_1.
    + exact disp_univalent_2_1_disp_bicat_of_univ_disp_cat.
Defined.

(**
 5. The global univalence
 *)
Proposition disp_univalent_2_0_disp_bicat_of_univ_disp_cat
  : disp_univalent_2_0 disp_bicat_of_univ_disp_cats.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  intros C D₁ D₂.
  use weqhomot.
  - refine (disp_bicat_of_univ_disp_cats_adjequiv_weq D₁ D₂
            ∘ univ_disp_cat_eq (pr1 D₁) (pr1 D₂) (pr2 D₁) (pr2 D₂)
            ∘ path_sigma_hprop _ _ _ _)%weq.
    apply isaprop_is_univalent_disp.
  - abstract
      (intro p ;
       cbn in p ;
       induction p ;
       use subtypePath ;
       [ intro ;
         use (isaprop_disp_left_adjoint_equivalence
                _ _
                univalent_cat_is_univalent_2_1
                disp_univalent_2_1_disp_bicat_of_univ_disp_cat)
       | ] ;
       apply idpath).
Defined.

(** Displayed bicategory of fibrations *)
Definition disp_bicat_of_cleaving_ob_mor
  : disp_cat_ob_mor (total_bicat disp_bicat_of_univ_disp_cats).
Proof.
  use tpair.
  - exact (λ X, cleaving (pr12 X)).
  - exact (λ X Y fibX fibY F, is_cartesian_disp_functor (pr2 F)).
Defined.

Definition disp_bicat_of_cleaving_id_comp
  : disp_cat_id_comp (total_bicat disp_bicat_of_univ_disp_cats) disp_bicat_of_cleaving_ob_mor.
Proof.
  use tpair.
  - intros X fibX x y f xx yy ff p.
    exact p.
  - intros X Y Z F G fibX fibY fibZ cartF cartG x y f xx yy ff p ; simpl.
    apply cartG.
    apply cartF.
    exact p.
Qed.

Definition disp_bicat_of_cleaving_cat_data
  : disp_cat_data (total_bicat disp_bicat_of_univ_disp_cats).
Proof.
  use tpair.
  - exact disp_bicat_of_cleaving_ob_mor.
  - exact disp_bicat_of_cleaving_id_comp.
Defined.

Definition disp_bicat_of_cleaving_help
  : disp_bicat (total_bicat disp_bicat_of_univ_disp_cats).
Proof.
  use disp_cell_unit_bicat.
  exact disp_bicat_of_cleaving_cat_data.
Defined.

Definition disp_bicat_of_cleaving
  : disp_bicat bicat_of_univ_cats
  := sigma_bicat
       bicat_of_univ_cats
       disp_bicat_of_univ_disp_cats
       disp_bicat_of_cleaving_help.

Definition disp_bicat_of_cleaving_is_disp_invertible_2cell
           {C C' : bicat_of_univ_cats}
           {F : C --> C'}
           {D : disp_bicat_of_cleaving C} {D' : disp_bicat_of_cleaving C'}
           {FF : D -->[ F ] D'} {GG : D -->[ F ] D'}
           (αα : FF ==>[ id₂ F ] GG)
           (Hαα : ∏ (x : (C : univalent_category)) (xx : pr11 D x),
                  is_z_iso_disp
                    (identity_z_iso (pr1 F x))
                    (pr11 αα x xx))
  : is_disp_invertible_2cell (id2_invertible_2cell F) αα.
Proof.
  use tpair.
  - exact (pointwise_inverse_disp_nat_trans (pr1 αα) Hαα ,, tt).
  - split.
    + abstract
        (cbn ;
         simpl in * ;
         use subtypePath ; [intro ; apply isapropunit | ];
         use (@disp_nat_trans_eq C C') ;
         intros x xx ; cbn ;
         refine (inv_mor_after_z_iso_disp (Hαα x xx) @ _) ;
         refine (!_) ;
         unfold transportb ;
         rewrite pr1_transportf ;
         refine (@disp_nat_trans_transportf
                   _ _ _ _ _ _
                   _ _
                   (!(@id2_left bicat_of_univ_cats _ _ _ _ (nat_trans_id F)))
                   _ _ _ _ _
                   @ _) ;
         apply transportf_paths ;
         apply homset_property).
    + abstract
        (cbn ;
         simpl in * ;
         use subtypePath ; [intro ; apply isapropunit | ];
         use (@disp_nat_trans_eq C C') ;
         intros x xx ; cbn ;
         refine (z_iso_disp_after_inv_mor (Hαα x xx) @ _) ;
         refine (!_) ;
         unfold transportb ;
         rewrite pr1_transportf ;
         refine (@disp_nat_trans_transportf
                   _ _ _ _ _ _
                   _ _
                   (!(@id2_left bicat_of_univ_cats _ _ _ _ (nat_trans_id F)))
                   _ _ _ _ _
                   @ _) ;
         apply transportf_paths ;
         apply homset_property).
Defined.

Definition disp_bicat_of_cleaving_disp_invertible_2cell_pointwise_inv
           {C C' : bicat_of_univ_cats}
           {F G : C --> C'}
           {α : F ==> G}
           (Hα : is_invertible_2cell α)
           {D : disp_bicat_of_cleaving C} {D' : disp_bicat_of_cleaving C'}
           {FF : D -->[ F ] D'} {GG : D -->[ G ] D'}
           (αα : FF ==>[ α ] GG)
           (Hαα : is_disp_invertible_2cell Hα αα)
           {x : (C : univalent_category)}
           (xx : (pr1 D : disp_univalent_category _) x)
  : is_z_iso_disp
      (make_z_iso'
         (pr1 α x)
         (is_invertible_2cell_to_is_nat_z_iso _ Hα x))
      (pr11 αα x xx).
Proof.
  simple refine (_ ,, _).
  - exact (pr111 Hαα x xx).
  - split.
    + abstract
        (unfold transportb ;
         etrans ; [ apply (maponpaths (λ z, pr11 z x xx) (pr22 Hαα)) |] ;
         unfold transportb ;
         etrans ;
         [ refine (maponpaths (λ z, pr1 z x xx) _) ;
           exact (pr1_transportf
                    (!(vcomp_linv Hα))
                    (disp_nat_trans_id (pr11 GG),, tt))
         | ];
         etrans ;
         [ exact (@disp_nat_trans_transportf
                    _ _ _ _ _ _ _ _
                    (!(vcomp_linv Hα))
                    _ _
                    (disp_nat_trans_id (pr11 GG))
                    x xx)
         | ] ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (unfold transportb ;
         etrans ; [ apply (maponpaths (λ z, pr11 z x xx) (pr12 Hαα)) |] ;
         unfold transportb ;
         etrans ;
         [ refine (maponpaths (λ z, pr1 z x xx) _) ;
           exact (pr1_transportf
                    (!(vcomp_rinv Hα))
                    (disp_nat_trans_id (pr11 FF),, tt))
         | ] ;
         etrans ;
         [ exact (@disp_nat_trans_transportf
                    _ _ _ _ _ _ _ _
                    (!(vcomp_rinv Hα))
                    _ _
                    (disp_nat_trans_id (pr11 FF))
                    x xx)
         | ] ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.

(** Displayed bicategory of opfibrations *)
Definition disp_bicat_of_opcleaving_ob_mor
  : disp_cat_ob_mor (total_bicat disp_bicat_of_univ_disp_cats).
Proof.
  use tpair.
  - exact (λ X, opcleaving (pr12 X)).
  - exact (λ X Y fibX fibY F, is_opcartesian_disp_functor (pr2 F)).
Defined.

Definition disp_bicat_of_opcleaving_id_comp
  : disp_cat_id_comp (total_bicat disp_bicat_of_univ_disp_cats) disp_bicat_of_opcleaving_ob_mor.
Proof.
  use tpair.
  - intros X fibX x y f xx yy ff p.
    exact p.
  - intros X Y Z F G fibX fibY fibZ cartF cartG x y f xx yy ff p ; simpl.
    apply cartG.
    apply cartF.
    exact p.
Qed.

Definition disp_bicat_of_opcleaving_cat_data
  : disp_cat_data (total_bicat disp_bicat_of_univ_disp_cats).
Proof.
  use tpair.
  - exact disp_bicat_of_opcleaving_ob_mor.
  - exact disp_bicat_of_opcleaving_id_comp.
Defined.

Definition disp_bicat_of_opcleaving_help
  : disp_bicat (total_bicat disp_bicat_of_univ_disp_cats).
Proof.
  use disp_cell_unit_bicat.
  exact disp_bicat_of_opcleaving_cat_data.
Defined.

Definition disp_bicat_of_opcleaving
  : disp_bicat bicat_of_univ_cats
  := sigma_bicat
       bicat_of_univ_cats
       disp_bicat_of_univ_disp_cats
       disp_bicat_of_opcleaving_help.

Definition disp_bicat_of_opcleaving_is_disp_invertible_2cell
           {C C' : bicat_of_univ_cats}
           {F : C --> C'}
           {D : disp_bicat_of_opcleaving C} {D' : disp_bicat_of_opcleaving C'}
           {FF : D -->[ F ] D'} {GG : D -->[ F ] D'}
           (αα : FF ==>[ id₂ F ] GG)
           (Hαα : ∏ (x : (C : univalent_category)) (xx : pr11 D x),
                  is_z_iso_disp
                    (identity_z_iso (pr1 F x))
                    (pr11 αα x xx))
  : is_disp_invertible_2cell (id2_invertible_2cell F) αα.
Proof.
  use tpair.
  - exact (pointwise_inverse_disp_nat_trans (pr1 αα) Hαα ,, tt).
  - split.
    + abstract
        (cbn ;
         simpl in * ;
         use subtypePath ; [intro ; apply isapropunit | ];
         use (@disp_nat_trans_eq C C') ;
         intros x xx ; cbn ;
         refine (inv_mor_after_z_iso_disp (Hαα x xx) @ _) ;
         refine (!_) ;
         unfold transportb ;
         rewrite pr1_transportf ;
         refine (@disp_nat_trans_transportf
                   _ _ _ _ _ _
                   _ _
                   (!(@id2_left bicat_of_univ_cats _ _ _ _ (nat_trans_id F)))
                   _ _ _ _ _
                   @ _) ;
         apply transportf_paths ;
         apply homset_property).
    + abstract
        (cbn ;
         simpl in * ;
         use subtypePath ; [intro ; apply isapropunit | ];
         use (@disp_nat_trans_eq C C') ;
         intros x xx ; cbn ;
         refine (z_iso_disp_after_inv_mor (Hαα x xx) @ _) ;
         refine (!_) ;
         unfold transportb ;
         rewrite pr1_transportf ;
         refine (@disp_nat_trans_transportf
                   _ _ _ _ _ _
                   _ _
                   (!(@id2_left bicat_of_univ_cats _ _ _ _ (nat_trans_id F)))
                   _ _ _ _ _
                   @ _) ;
         apply transportf_paths ;
         apply homset_property).
Defined.

Definition disp_bicat_of_opcleaving_disp_invertible_2cell_pointwise_inv
           {C C' : bicat_of_univ_cats}
           {F G : C --> C'}
           {α : F ==> G}
           (Hα : is_invertible_2cell α)
           {D : disp_bicat_of_opcleaving C} {D' : disp_bicat_of_opcleaving C'}
           {FF : D -->[ F ] D'} {GG : D -->[ G ] D'}
           (αα : FF ==>[ α ] GG)
           (Hαα : is_disp_invertible_2cell Hα αα)
           {x : (C : univalent_category)}
           (xx : (pr1 D : disp_univalent_category _) x)
  : is_z_iso_disp
      (make_z_iso'
         (pr1 α x)
         (is_invertible_2cell_to_is_nat_z_iso _ Hα x))
      (pr11 αα x xx).
Proof.
  simple refine (_ ,, _).
  - exact (pr111 Hαα x xx).
  - split.
    + abstract
        (unfold transportb ;
         etrans ; [ apply (maponpaths (λ z, pr11 z x xx) (pr22 Hαα)) |] ;
         unfold transportb ;
         etrans ;
         [ refine (maponpaths (λ z, pr1 z x xx) _) ;
           exact (pr1_transportf
                    (!(vcomp_linv Hα))
                    (disp_nat_trans_id (pr11 GG),, tt))
         | ];
         etrans ;
         [ exact (@disp_nat_trans_transportf
                    _ _ _ _ _ _ _ _
                    (!(vcomp_linv Hα))
                    _ _
                    (disp_nat_trans_id (pr11 GG))
                    x xx)
         | ] ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (unfold transportb ;
         etrans ; [ apply (maponpaths (λ z, pr11 z x xx) (pr12 Hαα)) |] ;
         unfold transportb ;
         etrans ;
         [ refine (maponpaths (λ z, pr1 z x xx) _) ;
           exact (pr1_transportf
                    (!(vcomp_rinv Hα))
                    (disp_nat_trans_id (pr11 FF),, tt))
         | ] ;
         etrans ;
         [ exact (@disp_nat_trans_transportf
                    _ _ _ _ _ _ _ _
                    (!(vcomp_rinv Hα))
                    _ _
                    (disp_nat_trans_id (pr11 FF))
                    x xx)
         | ] ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.
