(**

 Some properties of comprehension categories with a universe

 This file collects various properties of comprehension categories with a universe object.
 While in the file `UniverseType.v` the fiber category is consistently used, we use
 displayed morphisms and their operations in this file. The justification of the laws in
 this file is purely that we need them elsewhere.

 Contents
 1. Preservation of composition
 2. Naturality
 3. Preservation of the elements map

                                                                                             *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Preservation of composition *)
Proposition comp_cat_el_map_on_disp_concat
            {C : comp_cat_with_ob}
            (el : comp_cat_el_map C)
            {Γ : C}
            {t₁ t₂ t₃ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
            (q : t₂ = t₃)
  : (comp_cat_el_map_on_eq el p ;; comp_cat_el_map_on_eq el q)%mor_disp
    =
    transportf
      (λ z, _ -->[ z ] _)
      (!(id_right _))
      (comp_cat_el_map_on_eq el (p @ q)).
Proof.
  rewrite (comp_cat_el_map_on_concat el p q).
  cbn.
  rewrite transport_f_f.
  refine (!_).
  apply transportf_set.
  apply homset_property.
Qed.

Proposition comp_cat_el_map_on_disp_concat_comp_functor
            {C : comp_cat_with_ob}
            (el : comp_cat_el_map C)
            {Γ : C}
            {t₁ t₂ t₃ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
            (q : t₂ = t₃)
  : comprehension_functor_mor
      (comp_cat_comprehension C)
      (comp_cat_el_map_on_eq el p ;; comp_cat_el_map_on_eq el q)%mor_disp
    =
    comprehension_functor_mor (comp_cat_comprehension C) (comp_cat_el_map_on_eq el (p @ q)).
Proof.
  rewrite comp_cat_el_map_on_disp_concat.
  apply comprehension_functor_mor_transportf.
Qed.

Proposition comp_cat_univ_el_stable_inv_left
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : (comp_cat_univ_el_stable_inv el s t ;; comp_cat_univ_el_stable_mor el s t
     =
     transportf
       (λ z, _ -->[ z ] _)
       (!(id_left _))
       (id_disp _))%mor_disp.
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    refine (!_).
    exact (z_iso_after_z_iso_inv (comp_cat_univ_el_stable el s t)).
  }
  refine (transport_f_f _ _ _ _ @ _).
  apply transportf_set.
  apply homset_property.
Qed.

Proposition comp_cat_univ_el_stable_inv_right
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : (comp_cat_univ_el_stable_mor el s t ;; comp_cat_univ_el_stable_inv el s t
     =
     transportf
       (λ z, _ -->[ z ] _)
       (!(id_left _))
       (id_disp _))%mor_disp.
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    refine (!_).
    exact (z_iso_inv_after_z_iso (comp_cat_univ_el_stable el s t)).
  }
  cbn.
  rewrite transport_f_f.
  apply transportf_set.
  apply homset_property.
Qed.

(** * 2. Naturality *)
Proposition comp_cat_subst_natural
            {C : comp_cat_with_ob}
            (el : comp_cat_el_map C)
            {Γ₁ Γ₂ : C}
            (s : Γ₁ --> Γ₂)
            {t₁ t₂ : tm Γ₂ (comp_cat_univ Γ₂)}
            (p : t₁ = t₂)
  : (comp_cat_subst _ s
     ;; comp_cat_el_map_on_eq el p)%mor_disp
    =
    transportf
      (λ z, _ -->[ z ] _)
      (id_left _ @ !(id_right _))
      (coerce_subst_ty _ (comp_cat_el_map_on_eq el p)
       ;; comp_cat_subst _ s)%mor_disp.
Proof.
  induction p ; cbn.
  rewrite id_right_disp.
  rewrite cartesian_factorisation_commutes.
  rewrite transport_f_f.
  rewrite id_right_disp.
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_subst_natural_alt
            {C : comp_cat_with_ob}
            (el : comp_cat_el_map C)
            {Γ₁ Γ₂ : C}
            (s : Γ₁ --> Γ₂)
            {t₁ t₂ : tm Γ₂ (comp_cat_univ Γ₂)}
            (p : t₁ = t₂)
  : (coerce_subst_ty _ (comp_cat_el_map_on_eq el p)
     ;; comp_cat_subst _ s)%mor_disp
    =
    transportb
      (λ z, _ -->[ z ] _)
      (id_left _ @ !(id_right _))
      (comp_cat_subst _ s
       ;; comp_cat_el_map_on_eq el p)%mor_disp.
Proof.
  rewrite comp_cat_subst_natural.
  rewrite transportbfinv.
  apply idpath.
Qed.

Proposition comp_cat_univ_el_stable_natural_inv_disp
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {t₁ t₂ : tm Δ (comp_cat_univ Δ)}
            (p : t₁ = t₂)
  : (inv_from_z_iso (comp_cat_univ_el_stable el s t₁)
     ;; coerce_subst_ty s (comp_cat_el_map_on_eq el p)
     =
     transportf
       (λ z, _ -->[ z ] _)
       (id_left _ @ !(id_right _))
       (comp_cat_el_map_on_eq el (maponpaths (λ z, z [[ _ ]]tm ↑ _) p)
        ;; inv_from_z_iso (comp_cat_univ_el_stable el s t₂)))%mor_disp.
Proof.
  induction p ; cbn -[coerce_subst_ty].
  etrans.
  {
    apply maponpaths.
    apply id_coerce_subst_ty.
  }
  cbn.
  rewrite id_left_disp, id_right_disp.
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_univ_el_stable_natural_inv_disp_alt
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {t₁ t₂ : tm Δ (comp_cat_univ Δ)}
            (p : t₁ = t₂)
            (q : t₁ [[ s ]]tm ↑ sub_comp_cat_univ s
                 =
                 t₂ [[ s ]]tm ↑ sub_comp_cat_univ s)
  : (comp_cat_el_map_on_eq el q
     ;; inv_from_z_iso (comp_cat_univ_el_stable el s t₂)
     =
     transportf
       (λ z, _ -->[ z ] _)
       (id_right _ @ !(id_left _))
       (inv_from_z_iso (comp_cat_univ_el_stable el s t₁)
        ;; coerce_subst_ty s (comp_cat_el_map_on_eq el p)))%mor_disp.
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply comp_cat_univ_el_stable_natural_inv_disp.
  }
  rewrite transport_f_f.
  rewrite transportf_set ; [ | apply homset_property ].
  apply maponpaths_2.
  apply eq_comp_cat_el_map_on_eq.
Qed.

Proposition comp_cat_univ_el_stable_natural_disp
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {t₁ t₂ : tm Δ (comp_cat_univ Δ)}
            (p : t₁ = t₂)
  : (pr1 (comp_cat_univ_el_stable el s t₁)
     ;; comp_cat_el_map_on_eq
          el
          (maponpaths (λ z, z [[ s ]]tm ↑ sub_comp_cat_univ s) p))%mor_disp
    =
    (coerce_subst_ty s (comp_cat_el_map_on_eq el p)
     ;; pr1 (comp_cat_univ_el_stable el s t₂))%mor_disp.
Proof.
  induction p.
  refine (id_right_disp _ @ _).
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply id_coerce_subst_ty.
  }
  refine (id_left_disp _ @ _).
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_univ_el_stable_natural_disp_alt
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {t₁ t₂ : tm Δ (comp_cat_univ Δ)}
            (p : t₁ = t₂)
            (q : t₁ [[ s ]]tm ↑ sub_comp_cat_univ s
                 =
                 t₂ [[ s ]]tm ↑ sub_comp_cat_univ s)
  : (pr1 (comp_cat_univ_el_stable el s t₁)
     ;; comp_cat_el_map_on_eq el q)%mor_disp
    =
    (coerce_subst_ty s (comp_cat_el_map_on_eq el p)
     ;; pr1 (comp_cat_univ_el_stable el s t₂))%mor_disp.
Proof.
  induction p.
  etrans.
  {
    apply maponpaths.
    apply comp_cat_el_map_on_idpath.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply id_coerce_subst_ty.
  }
  cbn.
  rewrite id_left_disp, id_right_disp.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_functor_preserves_univ_type_el_mor_natural_disp
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {u₁ : comp_cat_univ_type C₁}
            {u₂ : comp_cat_univ_type C₂}
            (Fu : comp_cat_functor_preserves_univ_type F u₁ u₂)
            {Γ : C₁}
            {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
  : (♯(comp_cat_type_functor F) (comp_cat_el_map_on_eq _ p)
     ;; comp_cat_functor_preserves_univ_type_el_mor Fu t₂)%mor_disp
    =
    transportf
      _
      (id_right _ @ !(functor_id _ _) @ !(id_right _))
      (comp_cat_functor_preserves_univ_type_el_mor Fu t₁
       ;; comp_cat_el_map_on_eq
            _
            (comp_cat_functor_preserves_univ_type_el_mor_natural_path F p))%mor_disp.
Proof.
  induction p.
  rewrite !comp_cat_el_map_on_idpath.
  etrans.
  {
    apply maponpaths_2.
    apply disp_functor_id.
  }
  unfold transportb.
  rewrite mor_disp_transportf_postwhisker.
  etrans.
  {
    apply maponpaths.
    apply id_left_disp.
  }
  unfold transportb.
  rewrite transport_f_f.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply id_right_disp.
  }
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

Proposition comp_cat_functor_preserves_univ_type_el_iso_natural_path
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            (Γ : C₁)
  : identity _ · identity _ = #F (identity Γ) · identity _.
Proof.
  rewrite functor_id.
  apply idpath.
Qed.

Proposition comp_cat_functor_preserves_univ_type_el_iso_natural
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            (Fel : comp_cat_functor_preserves_univ_type F el₁ el₂)
            {Γ : C₁}
            {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
  : (♯(comp_cat_type_functor F) (comp_cat_el_map_on_eq el₁ p)
     ;; (comp_cat_functor_preserves_univ_type_el_iso Fel t₂ : _ --> _)
     =
     transportf
       (λ z, _ -->[ z ] _)
       (comp_cat_functor_preserves_univ_type_el_iso_natural_path F Γ)
       ((comp_cat_functor_preserves_univ_type_el_iso Fel t₁ : _ --> _)
        ;; comp_cat_el_map_on_eq
             el₂
             (maponpaths
                (λ z, comp_cat_functor_tm F z ↑ functor_comp_cat_on_univ F Γ)
                p)))%mor_disp.
Proof.
  induction p.
  simpl.
  rewrite !comp_cat_el_map_on_idpath.
  etrans.
  {
    apply maponpaths_2.
    apply disp_functor_id.
  }
  unfold transportb.
  rewrite mor_disp_transportf_postwhisker.
  rewrite id_left_disp.
  unfold transportb.
  rewrite transport_f_f.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply id_right_disp.
  }
  unfold transportb.
  rewrite transport_f_f.
  apply maponpaths_2.
  apply homset_property.
Qed.

(** * 3. Preservation of the elements map *)
Proposition comp_cat_functor_preserves_univ_type_el_stable_alt_inv
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : comp_cat_functor_subst_ty_coe F s _
    · coerce_subst_ty (#F s) (comp_cat_functor_preserves_univ_type_el_mor Fi t)
    =
    comp_cat_functor_coerce F (comp_cat_univ_el_stable el₁ s t : _ --> _)
    · comp_cat_functor_preserves_univ_type_el_iso Fi (t [[ s ]]tm ↑ sub_comp_cat_univ _)
    · comp_cat_el_map_on_eq_iso _ (comp_cat_functor_preserves_stable_el_path F s t)
    · inv_from_z_iso (comp_cat_univ_el_stable
                        el₂ (#F s)
                        (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Δ)).
Proof.
  rewrite <- comp_cat_functor_preserves_univ_type_el_stable.
  rewrite !assoc'.
  rewrite z_iso_inv_after_z_iso.
  rewrite id_right.
  apply idpath.
Qed.

Proposition comp_cat_functor_preserves_univ_type_el_stable_alt_inv_disp
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : comprehension_functor_mor
      (comp_cat_comprehension C₂)
      (comp_cat_functor_subst_ty_coe F s _
       ;; coerce_subst_ty _ (comp_cat_functor_preserves_univ_type_el_mor Fi t)
       ;; comp_cat_subst _ _)%mor_disp
    =
    comprehension_functor_mor
      (comp_cat_comprehension C₂)
      (comp_cat_functor_coerce F (comp_cat_univ_el_stable el₁ s t : _ --> _)
       ;; comp_cat_functor_preserves_univ_type_el_mor Fi (t [[ s ]]tm ↑ sub_comp_cat_univ _)
       ;; comp_cat_el_map_on_eq _ (comp_cat_functor_preserves_stable_el_path F s t)
       ;; inv_from_z_iso (comp_cat_univ_el_stable
                            el₂ _
                            (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Δ))
       ;; comp_cat_subst _ _)%mor_disp.
Proof.
  pose (maponpaths
          (λ z, comprehension_functor_mor
                  (comp_cat_comprehension C₂)
                  (z ;; comp_cat_subst _ _)%mor_disp)
          (comp_cat_functor_preserves_univ_type_el_stable_alt_inv Fi s t))
    as p.
  refine (_ @ p @ _) ; clear p.
  - refine (!_).
    etrans.
    {
      apply maponpaths.
      apply mor_disp_transportf_postwhisker.
    }
    apply comprehension_functor_mor_transportf.
  - etrans.
    {
      apply maponpaths.
      apply mor_disp_transportf_postwhisker.
    }
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply mor_disp_transportf_postwhisker.
    }
    rewrite mor_disp_transportf_postwhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply mor_disp_transportf_postwhisker.
    }
    rewrite !mor_disp_transportf_postwhisker.
    apply comprehension_functor_mor_transportf.
Qed.

Proposition comp_cat_functor_preserves_univ_type_el_stable_alt_inv_disp_alt
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : comprehension_functor_mor
      (comp_cat_comprehension C₂)
      (♯ (comp_cat_type_functor F) (comp_cat_subst _ _)
       ;; comp_cat_functor_preserves_univ_type_el_mor Fi t)%mor_disp
    =
    comprehension_functor_mor
      (comp_cat_comprehension C₂)
      (comp_cat_functor_coerce F (comp_cat_univ_el_stable el₁ s t : _ --> _)
       ;; comp_cat_functor_preserves_univ_type_el_mor Fi (t [[ s ]]tm ↑ sub_comp_cat_univ _)
       ;; comp_cat_el_map_on_eq _ (comp_cat_functor_preserves_stable_el_path F s t)
       ;; inv_from_z_iso (comp_cat_univ_el_stable
                            el₂ _
                            (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Δ))
       ;; comp_cat_subst _ _)%mor_disp.
Proof.
  refine (_ @ comp_cat_functor_preserves_univ_type_el_stable_alt_inv_disp Fi s t).
  refine (!_).
  etrans.
  {
    rewrite assoc_disp_var.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    rewrite mor_disp_transportf_prewhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    rewrite assoc_disp.
    unfold transportb.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply cartesian_factorisation_commutes.
    }
    rewrite mor_disp_transportf_postwhisker.
    apply comprehension_functor_mor_transportf.
  }
  apply idpath.
Qed.
