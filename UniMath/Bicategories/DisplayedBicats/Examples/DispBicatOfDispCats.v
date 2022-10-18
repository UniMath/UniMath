(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

 Displayed bicategory of displayed structures on 1-categories.
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
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
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
       exact (@isaset_disp_nat_trans C₁ C₂ D₁ D₂ F₁ F₂ n FF₁ FF₂)).
Defined.

(** Condition for displayed invertible 2-cells in this bicategory *)
Definition disp_bicat_of_univ_disp_cats_is_disp_invertible_2cell
           {C C' : bicat_of_univ_cats}
           {F : C --> C'}
           {D : disp_bicat_of_univ_disp_cats C}
           {D' : disp_bicat_of_univ_disp_cats C'}
           {FF : D -->[ F ] D'} {GG : D -->[ F ] D'}
           (αα : FF ==>[ id₂ F ] GG)
           (Hαα : ∏ (x : (C : univalent_category)) (xx : pr1 D x),
                  is_z_iso_disp
                    (identity_z_iso (pr1 F x))
                    (pr1 αα x xx))
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
