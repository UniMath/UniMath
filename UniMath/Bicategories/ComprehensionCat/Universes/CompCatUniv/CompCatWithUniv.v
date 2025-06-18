(**


                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.

Local Open Scope cat.
Local Open Scope comp_cat.

Proposition comp_cat_functor_preserves_univ_type_el_mor_two_comp_eq
            {C₁ C₂ C₃ C₄ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            (G : comp_cat_functor_ob C₂ C₃)
            (H : comp_cat_functor_ob C₃ C₄)
            {Γ : C₁}
            (t : tm Γ (comp_cat_univ Γ))
  : comp_cat_functor_tm (F · G · H : comp_cat_functor_ob _ _) t
    ↑ functor_comp_cat_on_univ (F · G · H) Γ
    =
    comp_cat_functor_tm (F · (G · H) : comp_cat_functor_ob _ _) t
    ↑ functor_comp_cat_on_univ (F · (G · H)) Γ.
Proof.
  etrans.
  {
    apply maponpaths.
    apply comp_comp_cat_functor_tm.
  }
  etrans.
  {
    do 2 apply maponpaths.
    apply comp_comp_cat_functor_tm.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply comp_comp_cat_functor_tm.
  }
  etrans.
  {
    apply maponpaths.
    apply (comp_comp_cat_functor_tm G H).
  }
  apply maponpaths_2.
  rewrite !comp_functor_comp_cat_on_univ.
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    apply maponpaths_2.
    apply (comp_comp_cat_functor_coerce G H).
  }
  refine (!_).
  apply (comp_cat_functor_coerce_on_comp H).
Qed.

Proposition comp_cat_functor_preserves_univ_type_el_mor_two_comp
            {C₁ C₂ C₃ C₄ : comp_cat_with_ob}
            {u₁ : comp_cat_univ_type C₁}
            {u₂ : comp_cat_univ_type C₂}
            {u₃ : comp_cat_univ_type C₃}
            {u₄ : comp_cat_univ_type C₄}
            {F : comp_cat_functor_ob C₁ C₂}
            {G : comp_cat_functor_ob C₂ C₃}
            {H : comp_cat_functor_ob C₃ C₄}
            (Fu : comp_cat_functor_preserves_univ_type F u₁ u₂)
            (Gu : comp_cat_functor_preserves_univ_type G u₂ u₃)
            (Hu : comp_cat_functor_preserves_univ_type H u₃ u₄)
            {Γ : C₁}
            (t : tm Γ (comp_cat_univ Γ))
  : comp_cat_functor_preserves_univ_type_el_mor
      (comp_comp_cat_functor_preserves_univ_type
         Fu
         (comp_comp_cat_functor_preserves_univ_type Gu Hu))
      t
    =
    comp_cat_functor_preserves_univ_type_el_mor
      (comp_comp_cat_functor_preserves_univ_type
         (comp_comp_cat_functor_preserves_univ_type Fu Gu)
         Hu)
      t
    · comp_cat_univ_el_on_eq
        u₄
        (comp_cat_functor_preserves_univ_type_el_mor_two_comp_eq F G H t).
Proof.
  etrans.
  {
    apply eq_comp_comp_cat_functor_preserves_univ.
  }
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    apply eq_comp_comp_cat_functor_preserves_univ.
  }
  etrans.
  {
    do 2 apply maponpaths_2.
    apply comp_comp_cat_functor_coerce.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply eq_comp_comp_cat_functor_preserves_univ.
  }
  etrans.
  {
    do 3 apply maponpaths_2.
    apply maponpaths.
    apply eq_comp_comp_cat_functor_preserves_univ.
  }
  rewrite !comp_cat_functor_coerce_on_comp.
  rewrite !assoc'.
  refine (maponpaths (λ z, _ · (_ · z)) _).
  rewrite !assoc.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply comp_cat_functor_preserves_el_natural.
  }
  rewrite !assoc'.
  refine (maponpaths (λ z, _ · z) _).
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply comp_cat_el_map_on_concat.
  }
  refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
  refine (_ @ comp_cat_el_map_on_concat _ _ _).
  apply eq_comp_cat_el_map_on_eq.
Qed.

Definition disp_ob_mor_comp_cat_ob_univ
  : disp_cat_ob_mor bicat_comp_cat_with_ob.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C : comp_cat_with_ob), comp_cat_univ_type C).
  - exact (λ (C₁ C₂ : comp_cat_with_ob)
             (u₁ : comp_cat_univ_type C₁)
             (u₂ : comp_cat_univ_type C₂)
             (F : comp_cat_functor_ob C₁ C₂),
           comp_cat_functor_preserves_univ_type F u₁ u₂).
Defined.

Definition disp_cat_id_comp_comp_cat_ob_univ
  : disp_cat_id_comp
      bicat_comp_cat_with_ob
      disp_ob_mor_comp_cat_ob_univ.
Proof.
  split.
  - exact (λ (C : comp_cat_with_ob)
             (u : comp_cat_univ_type C),
           id_comp_cat_functor_preserves_univ_type u).
  - exact (λ (C₁ C₂ C₃ : comp_cat_with_ob)
             (F : comp_cat_functor_ob C₁ C₂)
             (G : comp_cat_functor_ob C₂ C₃)
             (u₁ : comp_cat_univ_type C₁)
             (u₂ : comp_cat_univ_type C₂)
             (u₃ : comp_cat_univ_type C₃)
             (Fu : comp_cat_functor_preserves_univ_type F u₁ u₂)
             (Gu : comp_cat_functor_preserves_univ_type G u₂ u₃),
           comp_comp_cat_functor_preserves_univ_type Fu Gu).
Defined.

Definition disp_cat_data_comp_cat_ob_univ
  : disp_cat_data bicat_comp_cat_with_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_ob_mor_comp_cat_ob_univ.
  - exact disp_cat_id_comp_comp_cat_ob_univ.
Defined.

Definition disp_prebicat_1_id_comp_cells_comp_cat_ob_univ
  : disp_prebicat_1_id_comp_cells bicat_comp_cat_with_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_comp_cat_ob_univ.
  - exact (λ (C₁ C₂ : comp_cat_with_ob)
             (F G : comp_cat_functor_ob C₁ C₂)
             (τ : comp_cat_nat_trans_ob F G)
             (u₁ : comp_cat_univ_type C₁)
             (u₂ : comp_cat_univ_type C₂)
             (Fu : comp_cat_functor_preserves_univ_type F u₁ u₂)
             (Gu : comp_cat_functor_preserves_univ_type G u₁ u₂),
           comp_cat_nat_trans_preserves_univ_type τ Fu Gu).
Defined.

Definition TODO { A : UU } : A.
Admitted.

Proposition disp_prebicat_ops_comp_cat_ob_univ
  : disp_prebicat_ops
      disp_prebicat_1_id_comp_cells_comp_cat_ob_univ.
Proof.
  repeat split.
  - intros C₁ C₂ F u₁ u₂ Fu Γ a.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply comp_cat_univ_el_stable_id_coh_alt.
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_id2.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply z_iso_inv_after_z_iso.
      }
      apply id_left.
    }
    apply maponpaths.
    apply eq_comp_cat_el_map_on_eq.
  - intros C₁ C₂ F u₁ u₂ Fu Γ a.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply comp_cat_univ_el_stable_id_coh_alt.
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_lunitor.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply z_iso_inv_after_z_iso.
      }
      apply id_left.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply eq_comp_comp_cat_functor_preserves_univ.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      use comp_cat_functor_preserves_el_natural.
    }
    do 2 refine (assoc' _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
    apply eq_comp_cat_el_map_on_eq.
  - intros C₁ C₂ F u₁ u₂ Fu Γ a.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply comp_cat_univ_el_stable_id_coh_alt.
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_runitor.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply z_iso_inv_after_z_iso.
      }
      apply id_left.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply eq_comp_comp_cat_functor_preserves_univ.
    }
    etrans.
    {
      do 3 apply maponpaths_2.
      apply id_comp_cat_functor_coerce.
    }
    do 2 refine (assoc' _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
    apply eq_comp_cat_el_map_on_eq.
  - intros C₁ C₂ F u₁ u₂ Fu Γ a.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply comp_cat_univ_el_stable_id_coh_alt.
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_linvunitor.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply z_iso_inv_after_z_iso.
      }
      apply id_left.
    }
    etrans.
    {
      apply maponpaths_2.
      exact (eq_comp_comp_cat_functor_preserves_univ (id_disp u₁) Fu a).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      use comp_cat_functor_preserves_el_natural.
    }
    do 2 refine (assoc' _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
    apply eq_comp_cat_el_map_on_eq.
  - intros C₁ C₂ F u₁ u₂ Fu Γ a.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply comp_cat_univ_el_stable_id_coh_alt.
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_rinvunitor.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply z_iso_inv_after_z_iso.
      }
      apply id_left.
    }
    etrans.
    {
      apply maponpaths_2.
      exact (eq_comp_comp_cat_functor_preserves_univ Fu (id_disp u₂) a).
    }
    etrans.
    {
      do 3 apply maponpaths_2.
      apply id_comp_cat_functor_coerce.
    }
    do 2 refine (assoc' _ _ _ @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
    apply eq_comp_cat_el_map_on_eq.
  - intros C₁ C₂ C₃ C₄ F G H u₁ u₂ u₃ u₄ Fu Gu Hu Γ a.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply comp_cat_univ_el_stable_id_coh_alt.
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_rassociator.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply z_iso_inv_after_z_iso.
      }
      apply id_left.
    }
    etrans.
    {
      apply maponpaths_2.
      exact (comp_cat_functor_preserves_univ_type_el_mor_two_comp Fu Gu Hu a).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    apply maponpaths.
    apply eq_comp_cat_el_map_on_eq.
  - intros C₁ C₂ C₃ C₄ F G H u₁ u₂ u₃ u₄ Fu Gu Hu Γ a.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply comp_cat_univ_el_stable_id_coh_alt.
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_lassociator.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply z_iso_inv_after_z_iso.
      }
      apply id_left.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (comp_cat_functor_preserves_univ_type_el_mor_two_comp Fu Gu Hu a).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    apply maponpaths.
    apply eq_comp_cat_el_map_on_eq.
  - intros C₁ C₂ F G H τ₁ τ₂ u₁ u₂ Fu Gu Hu τu₁ τu₂ Γ A.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_vcomp.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (comp_cat_nat_trans_preserves_univ_type_alt τu₁).
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply (comp_cat_nat_trans_preserves_univ_type_alt τu₂).
    }
    rewrite !comp_coerce_subst_ty.
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply comp_subst_ty_natural.
      }
      rewrite !assoc'.
      apply idpath.
    }
    apply maponpaths.
    refine (comp_cat_univ_el_stable_comp_coh _ _ _ _ @ _).
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      use comp_cat_univ_el_stable_natural.
      abstract
        (apply maponpaths ;
         refine (maponpaths (λ z, z [[ _ ]]tm) _) ;
         rewrite subst_coerce_comp_cat_tm ;
         rewrite comp_coerce_comp_cat_tm ;
         rewrite (comp_cat_nat_trans_on_univ_comm_alt τ₂ Γ) ;
         rewrite <- !comp_coerce_comp_cat_tm ;
         do 2 apply maponpaths ;
         rewrite comp_cat_nat_trans_tm ;
         apply idpath).
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
    apply eq_comp_cat_el_map_on_eq.
  - intros C₁ C₂ C₃ F G₁ G₂ τ u₁ u₂ u₃ Fu Gu₁ Gu₂ τu Γ A.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_lwhisker.
    }
    etrans.
    {
      apply maponpaths_2.
      do 2 apply maponpaths.
      apply eq_comp_comp_cat_functor_preserves_univ.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply eq_comp_comp_cat_functor_preserves_univ.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (comp_cat_nat_trans_preserves_univ_type_alt τu).
    }
    etrans.
    {
      rewrite !assoc.
      do 5 apply maponpaths_2.
      refine (!_).
      apply comp_cat_type_fib_nat_trans_coerce.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !comp_coerce_subst_ty.
    rewrite !assoc'.
    do 2 apply maponpaths.
    refine (!_).
    etrans.
    {
      use comp_cat_univ_el_stable_natural.
      abstract
        (apply maponpaths ;
         refine (maponpaths (λ z, z [[ _ ]]tm) _) ;
         refine (!_) ;
         etrans ;
         [ apply maponpaths ;
           apply comp_comp_cat_functor_tm
         | ] ;
         etrans ;
         [ apply maponpaths_2 ;
           apply comp_functor_comp_cat_on_univ
         | ] ;
         rewrite comp_cat_functor_coerce_tm ;
         rewrite comp_coerce_comp_cat_tm ;
         apply idpath).
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
    apply eq_comp_cat_el_map_on_eq.
  - intros C₁ C₂ C₃ F₁ F₂ G τ u₁ u₂ u₃ Fu₁ Fu₂ Gu τu Γ A.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_rwhisker.
    }
    etrans.
    {
      apply maponpaths_2.
      do 2 apply maponpaths.
      apply eq_comp_comp_cat_functor_preserves_univ.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply eq_comp_comp_cat_functor_preserves_univ.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply (comp_cat_nat_trans_preserves_univ_type_alt τu).
    }
    rewrite !comp_cat_functor_coerce_on_comp.
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    rewrite !comp_coerce_subst_ty.
    etrans.
    {
      rewrite !assoc.
      do 3 apply maponpaths_2.
      refine (!_).
      apply (comp_cat_functor_subst_ty_natural (pr1 G)).
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      apply comp_cat_functor_preserves_univ_type_el_mor_natural.
    }
    etrans.
    {
      rewrite !assoc.
      do 3 apply maponpaths_2.
      apply (comp_cat_functor_preserves_stable_el_alt (pr2 Gu)).
    }
    rewrite !assoc'.
    do 2 apply maponpaths.
    refine (!_).
    etrans.
    {
      use comp_cat_univ_el_stable_natural.
      abstract
        (apply maponpaths ;
         refine (maponpaths (λ z, z [[ _ ]]tm) _) ;
         refine (!_) ;
         etrans ;
         [ apply maponpaths ;
           apply comp_comp_cat_functor_tm
         | ] ;
         etrans ;
         [ apply maponpaths_2 ;
           apply comp_functor_comp_cat_on_univ
         | ] ;
         rewrite comp_cat_functor_coerce_tm ;
         rewrite comp_coerce_comp_cat_tm ;
         apply idpath).
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
    apply eq_comp_cat_el_map_on_eq.
Qed.

Definition disp_prebicat_data_comp_cat_ob_univ
  : disp_prebicat_data bicat_comp_cat_with_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_comp_cat_ob_univ.
  - exact disp_prebicat_ops_comp_cat_ob_univ.
Defined.

Proposition disp_prebicat_laws_comp_cat_ob_univ
  : disp_prebicat_laws
      disp_prebicat_data_comp_cat_ob_univ.
Proof.
  repeat split ; intro ; intros ; apply isaprop_comp_cat_nat_trans_preserves_univ_type.
Qed.

Definition disp_prebicat_comp_cat_ob_univ
  : disp_prebicat bicat_comp_cat_with_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_comp_cat_ob_univ.
  - exact disp_prebicat_laws_comp_cat_ob_univ.
Defined.

Definition disp_bicat_comp_cat_ob_univ
  : disp_bicat bicat_comp_cat_with_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_comp_cat_ob_univ.
  - abstract
      (intro ; intros ;
       apply isasetaprop ;
       apply isaprop_comp_cat_nat_trans_preserves_univ_type).
Defined.
