(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

 Displayed bicategory of displayed structures on 1-categories.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

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
    etrans. apply id_left_disp.
    apply pathsinv0; unfold transportb.
    apply maponpaths_2. apply homset_property.
  - apply pathsinv0.
    etrans. apply id_right_disp.
    apply pathsinv0; unfold transportb.
    apply maponpaths_2. apply homset_property.
  - apply pathsinv0.
    etrans. apply assoc_disp.
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
    etrans. apply transport_f_f.
    apply transportf_set. apply homset_property.
  - cbn.
    etrans.
    {
      apply maponpaths.
      apply id_left_disp.
    }
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    etrans.
    {
      apply maponpaths.
      apply id_left_disp.
    }
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    etrans. apply maponpaths. apply id_right_disp.
    etrans. apply transport_f_f.
    apply pathsinv0.
    etrans. apply id_left_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    set (RR := @disp_nat_trans_ax_var _ _ _ _ _ _ _ _ _ φφ).
    etrans. apply maponpaths. apply RR.
    etrans. apply transport_f_f.
    apply transportf_set. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. apply id_right_disp.
    unfold transportb. apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. apply id_left_disp.
    etrans. apply maponpaths. apply disp_functor_id.
    etrans. apply transport_f_f.
    apply maponpaths_2. apply homset_property.
  - cbn.
    apply pathsinv0.
    etrans. apply assoc_disp_var.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
    etrans. apply maponpaths. apply disp_functor_id.
    etrans. apply transport_f_f.

    apply pathsinv0.
    etrans. apply maponpaths. apply id_left_disp.
    etrans. apply transport_f_f.
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
       exact (isaset_disp_nat_trans C₁ C₂ D₁ D₂ F₁ F₂ n FF₁ FF₂)).
Defined.

(** Condition for displayed invertible 2-cells in this bicategory *)
Definition disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell_natural
           {C C' : category}
           {F : C ⟶ C'}
           {D : disp_cat C} {D' : disp_cat C'}
           {FF : disp_functor F D D'} {GG : disp_functor F D D'}
           (αα : disp_nat_trans (nat_trans_id F) FF GG)
           (Hαα : ∏ (x : C) (xx : D x),
                  is_iso_disp
                    (identity_iso (pr1 F x))
                    (pr1 αα x xx))
           {x y : pr1 C}
           {f : x --> y}
           {xx : D x} {yy : D y}
           (ff : xx -->[ f ] yy)
  : # GG ff;; inv_mor_disp_from_iso (Hαα y yy)
    =
    transportb
      (mor_disp (GG x xx) (FF y yy))
      (is_nat_trans_id F x y f)
      (inv_mor_disp_from_iso (Hαα x xx);; # FF ff).
Proof.
  use (precomp_with_iso_disp_is_inj (make_iso_disp _ (Hαα x xx))).
  simpl.
  refine (assoc_disp _ _ _ @ _).
  unfold transportb.
  rewrite mor_disp_transportf_prewhisker.
  rewrite assoc_disp.
  refine (!_).
  refine (transport_f_f _ _ _ _ @ _).
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply (inv_mor_after_iso_disp (Hαα x xx)).
  }
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply mor_disp_transportf_postwhisker.
    }
    etrans.
    {
      apply maponpaths.
      apply id_left_disp.
    }
    apply transport_f_f.
  }
  etrans.
  {
    apply transport_f_f.
  }
  assert (transportf
            (mor_disp (FF x xx) (GG y yy)) (nat_trans_ax (nat_trans_id F) x y f)
            (# FF ff;; pr1 αα y yy) =
          pr1 αα x xx;; # GG ff)
    as X.
  {
    apply transportf_transpose_left.
    exact (pr2 αα x y f xx yy ff).
  }
  refine (!_).
  apply transportf_transpose_left.
  etrans.
  {
    apply maponpaths_2.
    exact (!X).
  }
  rewrite mor_disp_transportf_postwhisker.
  etrans.
  {
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply assoc_disp_var.
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply (inv_mor_after_iso_disp (Hαα y yy)).
        }
        etrans.
        {
          apply mor_disp_transportf_prewhisker.
        }
        etrans.
        {
          apply maponpaths.
          apply id_right_disp.
        }
        apply transport_f_f.
      }
      apply transport_f_f.
    }
    apply transport_f_f.
  }
  refine (!_).
  etrans.
  {
    apply transport_f_f.
  }
  apply transportf_paths.
  apply C'.
Qed.

Definition disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell
           {C C' : bicat_of_univ_cats}
           {F : C --> C'}
           {D : disp_bicat_of_univ_disp_cats C}
           {D' : disp_bicat_of_univ_disp_cats C'}
           {FF : D -->[ F ] D'} {GG : D -->[ F ] D'}
           (αα : FF ==>[ id₂ F ] GG)
           (Hαα : ∏ (x : (C : univalent_category)) (xx : pr1 D x),
                  is_iso_disp
                    (identity_iso (pr1 F x))
                    (pr1 αα x xx))
  : is_disp_invertible_2cell (id2_invertible_2cell F) αα.
Proof.
  use tpair.
  - use tpair.
    + intros x xx ; cbn.
      exact (inv_mor_disp_from_iso (Hαα x xx)).
    + intros x xx y yy f ff ; cbn in *.
      apply (@disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell_natural
               C C').
  - split.
    + abstract
        (cbn ;
         simpl in * ;
         use (@disp_nat_trans_eq C C') ;
         intros x xx ; cbn ;
         refine (inv_mor_after_iso_disp (Hαα x xx) @ _) ;
         refine (!_) ;
         refine (disp_nat_trans_transportf
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
         refine (iso_disp_after_inv_mor (Hαα x xx) @ _) ;
         refine (!_) ;
         refine (disp_nat_trans_transportf
                   _ _ _ _ _ _
                   _ _
                   (!(@id2_left bicat_of_univ_cats _ _ _ _ (nat_trans_id F)))
                   _ _ _ _ _
                   @ _) ;
         apply transportf_paths ;
         apply homset_property).
Defined.

Definition disp_bicat_of_fibs_ob_mor
  : disp_cat_ob_mor (total_bicat disp_bicat_of_univ_disp_cats).
Proof.
  use tpair.
  - exact (λ X, cleaving (pr12 X)).
  - exact (λ X Y fibX fibY F, is_cartesian_disp_functor (pr2 F)).
Defined.

Definition disp_bicat_of_fibs_id_comp
  : disp_cat_id_comp (total_bicat disp_bicat_of_univ_disp_cats) disp_bicat_of_fibs_ob_mor.
Proof.
  use tpair.
  - intros X fibX x y f xx yy ff p.
    exact p.
  - intros X Y Z F G fibX fibY fibZ cartF cartG x y f xx yy ff p ; simpl.
    apply cartG.
    apply cartF.
    exact p.
Qed.

Definition disp_bicat_of_fibs_cat_data
  : disp_cat_data (total_bicat disp_bicat_of_univ_disp_cats).
Proof.
  use tpair.
  - exact disp_bicat_of_fibs_ob_mor.
  - exact disp_bicat_of_fibs_id_comp.
Defined.

Definition disp_bicat_of_fibs_help
  : disp_bicat (total_bicat disp_bicat_of_univ_disp_cats).
Proof.
  use disp_cell_unit_bicat.
  exact disp_bicat_of_fibs_cat_data.
Defined.

Definition disp_bicat_of_fibs
  : disp_bicat bicat_of_univ_cats
  := sigma_bicat
       bicat_of_univ_cats
       disp_bicat_of_univ_disp_cats
       disp_bicat_of_fibs_help.

Definition disp_bicat_of_fibs_is_disp_invertible_2cell
           {C C' : bicat_of_univ_cats}
           {F : C --> C'}
           {D : disp_bicat_of_fibs C} {D' : disp_bicat_of_fibs C'}
           {FF : D -->[ F ] D'} {GG : D -->[ F ] D'}
           (αα : FF ==>[ id₂ F ] GG)
           (Hαα : ∏ (x : (C : univalent_category)) (xx : pr11 D x),
                  is_iso_disp
                    (identity_iso (pr1 F x))
                    (pr11 αα x xx))
  : is_disp_invertible_2cell (id2_invertible_2cell F) αα.
Proof.
  use tpair.
  - refine (_ ,, tt).
    use tpair.
    + intros x xx ; cbn.
      exact (inv_mor_disp_from_iso (Hαα x xx)).
    + intros x xx y yy f ff ; cbn in *.
      apply (@disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell_natural
               C C').
  - split.
    + abstract
        (cbn ;
         simpl in * ;
         use subtypePath ; [intro ; apply isapropunit | ];
         use (@disp_nat_trans_eq C C') ;
         intros x xx ; cbn ;
         refine (inv_mor_after_iso_disp (Hαα x xx) @ _) ;
         refine (!_) ;
         unfold transportb ;
         rewrite pr1_transportf ;
         refine (disp_nat_trans_transportf
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
         refine (iso_disp_after_inv_mor (Hαα x xx) @ _) ;
         refine (!_) ;
         unfold transportb ;
         rewrite pr1_transportf ;
         refine (disp_nat_trans_transportf
                   _ _ _ _ _ _
                   _ _
                   (!(@id2_left bicat_of_univ_cats _ _ _ _ (nat_trans_id F)))
                   _ _ _ _ _
                   @ _) ;
         apply transportf_paths ;
         apply homset_property).
Defined.

Definition TODO { A : UU } : A .
Admitted.

Definition disp_bicat_of_fibs_disp_invertible_2cell_pointwise_inv
           {C C' : bicat_of_univ_cats}
           {F G : C --> C'}
           {α : F ==> G}
           (Hα : is_invertible_2cell α)
           {D : disp_bicat_of_fibs C} {D' : disp_bicat_of_fibs C'}
           {FF : D -->[ F ] D'} {GG : D -->[ G ] D'}
           (αα : FF ==>[ α ] GG)
           (Hαα : is_disp_invertible_2cell Hα αα)
           {x : (C : univalent_category)}
           (xx : (pr1 D : disp_univalent_category _) x)
  : is_iso_disp
      (make_iso
         (pr1 α x)
         (is_invertible_2cell_to_is_nat_iso _ Hα x))
      (pr11 αα x xx).
Proof.
  simple refine (_ ,, _ ,, _).
  - exact (transportf
             (λ z, _ -->[ z ] _)
             (!(id_right _))
             (pr111 Hαα x xx)).
  - (*unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    pose (p := maponpaths (λ z, pr11 z x xx) (pr22 Hαα)).
    cbn in p.
    cbn.
    refine (maponpaths (λ z, transportf _ _ z) p @ _) ; clear p.
    unfold transportb.*)
    apply TODO.
  - apply TODO.
    Time Defined.
(*  -
      (unfold transportb ;
       rewrite mor_disp_transportf_postwhisker ;
       pose (maponpaths (λ z, pr11 z x xx) (pr22 Hαα)) as p ;
       simpl in p ;
       unfold transportb in p ;
       rewrite pr1_transportf in p ;
       rewrite disp_nat_trans_transportf in p ;
       refine (maponpaths _ p @ _) ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply homset_property).
  -
      (unfold transportb ;
       rewrite mor_disp_transportf_prewhisker ;
       pose (maponpaths (λ z, pr11 z x xx) (pr12 Hαα)) as p ;
       simpl in p ;
       unfold transportb in p ;
       rewrite pr1_transportf in p ;
       rewrite disp_nat_trans_transportf in p ;
       refine (maponpaths _ p @ _) ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply homset_property).
Defined.
 *)
