(**

 The bicategory of univalent comprehension categories with a universe type

 In the file `UniverseType`, we defined what it means for a comprehension category to have
 a universe type and what it means for a functor and natural transformation to preserve
 universe types. In this file, we use these notions to construct the bicategory of univalent
 comprehension categories with a universe type. We also prove some basic properties of this
 bicategory, namely that it is univalent.

 For completeness, we recall what it means for a comprehension category to support a universe
 type. Let `C` be a comprehension category whose displayed category of types is denoted by `D`.
 A universe in `C` consists of
 - a type `u : D []` where `[]` denotes the empty context. By weakening, the type `u` gives
   rise to a type in every context `Γ`, which, for simplicity, we denote by `u` as well.
 - for each term `t` of type `u` in context `Γ`, a type `el t : D Γ`.
 - given a substitution `s : Γ --> Δ` and a term `t` of type `u` in context `Δ`, we have an
   isomorphism between `(el t) [[ s ]]` and `el (t [[ s ]]tm)`.
 We also require coherences, which simplify the isomorphisms given in the final in case that
 the substitution is either the identity or a composition. The formalized definitions,
 including preservation of universes by functors and natural transformations, is given in the
 file `UniverseType`.

 Note that these universes are Tarski style, since terms of the universe types are not
 necessarily types themselves, but we have a map that assigns to each such term an actual
 type. In addition, these universe are expressed in a syntactic way. Rather than expressing
 some universal property, we state all the required operations and coherences for universe
 types. The reason for that is that universes in type theory are, generally, not determined
 by a universal property, since they do not have an elimination rule with suitable β- and
 η-rules.

 The bicategory of univalent comprehension categories with a universe type is constructed
 using displayed bicategories. Specifically, it is constructed in two steps. First, we define
 a displayed bicategory over the bicategory of univalent comprehension categories, whose
 objects over `C` are types in the empty context. This was done in the file `CompCatOb`,
 and this gives us the type `u`. Over the total bicategory of the aforementioned displayed
 bicategory, we define a displayed bicategory that expresses that the type `u` is indeed a
 universe, which is done by adding the map `el` that is coherently stable under substitution.
 This displayed bicategory is defined in the current file. Finally, we use the sigma
 construction of displayed bicategories to obtain a displayed bicategory over the bicategory
 of univalent comprehension categories, whose objects over a comprehension category `C` are
 universes in `C`.

 Content
 1. Some useful computational lemmas
 2. The displayed bicategory of univalent comprehension categories with a universe
 3. 2-cells in this displayed bicategory are unique and invertible
 4. This displayed bicategory is locally univalent
 5. Adjoint equivalences in this displayed bicategory
 6. Global univalence
 7. The bicategory of comprehension categories with a universe
 8. The bicategory of full comprehension categories with a universe
 9. The bicategory of DFL full comprehension categories with a universe

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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.LiftDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Some useful computational lemmas *)
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

(** * 2. The displayed bicategory of univalent comprehension categories with a universe *)
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

(** * 3. 2-cells in this displayed bicategory are unique and invertible *)
Proposition disp_2cells_isaprop_disp_bicat_comp_cat_ob_univ
  : disp_2cells_isaprop disp_bicat_comp_cat_ob_univ.
Proof.
  intro ; intros.
  apply isaprop_comp_cat_nat_trans_preserves_univ_type.
Qed.

Proposition disp_locally_groupoid_disp_bicat_comp_cat_ob_univ
  : disp_locally_groupoid disp_bicat_comp_cat_ob_univ.
Proof.
  use make_disp_locally_groupoid_univalent_2_1.
  - refine (λ (C₁ C₂ : comp_cat_with_ob)
              (F : comp_cat_functor_ob C₁ C₂)
              (u₁ : comp_cat_univ_type C₁)
              (u₂ : comp_cat_univ_type C₂)
              (FF GG : comp_cat_functor_preserves_univ_type F u₁ u₂)
              (τ : comp_cat_nat_trans_preserves_univ_type (id₂ F) FF GG),
             _).
    simple refine (_ ,, _ ,, _) ;
      [
      | apply disp_2cells_isaprop_disp_bicat_comp_cat_ob_univ
      | apply disp_2cells_isaprop_disp_bicat_comp_cat_ob_univ ].
    intros Γ t.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_id2.
    }
    etrans.
    {
      apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (comp_cat_nat_trans_preserves_univ_type_alt τ t).
    }
    etrans.
    {
      do 5 apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_id2.
    }
    etrans.
    {
      do 4 apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply comp_cat_univ_el_stable_id_coh.
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply comp_cat_univ_el_stable_id_coh.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_univ_el_on_concat.
    }
    refine (!(comp_cat_univ_el_on_concat _ _ _) @ _).
    apply eq_comp_cat_el_map_on_eq.
  - exact is_univalent_2_1_bicat_comp_cat_with_ob.
Qed.

(** * 4. This displayed bicategory is locally univalent *)
Proposition disp_univalent_2_1_disp_bicat_comp_cat_ob_univ
  : disp_univalent_2_1 disp_bicat_comp_cat_ob_univ.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  refine (λ (C₁ C₂ : comp_cat_with_ob)
            (F : comp_cat_functor_ob C₁ C₂)
            (u₁ : comp_cat_univ_type C₁)
            (u₂ : comp_cat_univ_type C₂)
            (FF GG : comp_cat_functor_preserves_univ_type F u₁ u₂),
          _).
  use isweqimplimpl.
  - intro τu ; cbn.
    use comp_cat_functor_preserves_univ_type_eq.
    intros Γ t.
    pose (p := maponpaths
                 (λ z, z · comp_cat_univ_el_on_eq
                             u₂
                             (!(comp_cat_nat_trans_preserves_univ_type_path (id₂ F) t)))
                 (pr1 τu Γ t)).
    rewrite !assoc' in p.
    rewrite <- comp_cat_univ_el_on_concat in p.
    rewrite comp_cat_univ_el_on_idpath in p.
    rewrite id_right in p.
    refine (p @ _) ; clear p.
    etrans.
    {
      apply maponpaths_2.
      apply comp_cat_type_fib_nat_trans_on_id2.
    }
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply id_subst_ty_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply comp_cat_univ_el_stable_id_coh.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_univ_el_on_concat.
    }
    rewrite comp_cat_univ_el_on_idpath.
    apply id_right.
  - apply isaset_comp_cat_functor_preserves_univ_type.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_disp_invertible_2cell.
    + intros.
      apply disp_2cells_isaprop_disp_bicat_comp_cat_ob_univ.
Qed.

(** * 5. Adjoint equivalences in this displayed bicategory *)
Section DispAdjEquiv.
  Context {C : comp_cat_with_ob}
          (u₁ : comp_cat_univ_type C)
          (u₂ : comp_cat_univ_type C).

  Section ToDispAdjEquiv.
    Context (p : ∏ (Γ : C)
                   (t : tm Γ (comp_cat_univ Γ)),
                 z_iso
                   (C := fiber_category _ _)
                   (comp_cat_univ_el u₁ t)
                   (comp_cat_univ_el u₂ t))
              (q : ∏ (Γ Δ : C)
                     (s : Γ --> Δ)
                     (t : tm Δ (comp_cat_univ Δ)),
                   comp_cat_univ_el_stable u₁ s t
                   · p Γ (t [[s ]]tm ↑ sub_comp_cat_univ s)
                   =
                   coerce_subst_ty s (p Δ t : _ --> _)
                   · comp_cat_univ_el_stable u₂ s t).

    Lemma disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_path
          {Γ : C}
          (t : tm Γ (comp_cat_univ Γ))
      : t
        =
        comp_cat_functor_tm
          (id₁ C : comp_cat_functor_ob _ _) t
        ↑ functor_comp_cat_on_univ (id₁ C) Γ.
    Proof.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply id_comp_cat_functor_tm.
      }
      rewrite id_functor_comp_cat_on_univ.
      apply id_coerce_comp_cat_tm.
    Qed.

    Definition disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_preserves_el
      : comp_cat_functor_preserves_el (id₁ C) u₁ u₂.
    Proof.
      refine (λ Γ t, z_iso_comp (p Γ t) (comp_cat_el_map_on_eq_iso u₂ _)).
      apply disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_path.
    Defined.

    Proposition disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_preserves_stable_el
      : comp_cat_functor_preserves_stable_el
          u₁ u₂
          disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_preserves_el.
    Proof.
      intros Γ Δ s t.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply comp_coerce_subst_ty.
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        apply comp_cat_univ_el_stable_natural.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply q.
      }
      rewrite !assoc.
      assert (comp_cat_functor_subst_ty_coe
                (id₁ C : comp_cat_functor_ob _ _)
                s
                (comp_cat_univ_el u₁ t)
              =
              identity _)
        as ->.
      {
        apply id_comp_cat_functor_subst_ty_coe.
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        apply id_left.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        apply id_comp_cat_functor_coerce.
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    Qed.

    Definition disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor
      : comp_cat_functor_preserves_univ_type (id₁ C) u₁ u₂.
    Proof.
      use make_comp_cat_functor_preserves_univ_type.
      - exact disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_preserves_el.
      - exact disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_preserves_stable_el.
    Defined.

    Proposition disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_eq
                {Γ : C}
                (t : tm Γ (comp_cat_univ Γ))
      : comp_cat_functor_preserves_univ_type_el_mor
          disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor
          t
        =
        p Γ t
        · comp_cat_el_map_on_eq_iso u₂ (disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_path t).
    Proof.
      apply idpath.
    Qed.

    Definition disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv_preserves_el
      : comp_cat_functor_preserves_el (id₁ C) u₂ u₁.
    Proof.
      refine (λ Γ t, z_iso_comp (z_iso_inv (p Γ t)) (comp_cat_el_map_on_eq_iso u₁ _)).
      apply disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_path.
    Defined.

    Proposition disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv_preserves_stable_el
      : comp_cat_functor_preserves_stable_el
          u₂ u₁
          disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv_preserves_el.
    Proof.
      intros Γ Δ s t.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        apply comp_cat_el_map_on_concat.
      }
      rewrite !assoc.
      use z_iso_inv_to_right.
      refine (!_).
      use z_iso_inv_on_left.
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          refine (!_).
          apply comp_cat_el_map_on_inv.
        }
        rewrite assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          use comp_cat_univ_el_stable_natural.
          refine (!_).
          apply disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_path.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply q.
      }
      assert (comp_cat_functor_subst_ty_coe
                (id₁ C : comp_cat_functor_ob _ _)
                s
                (comp_cat_univ_el u₂ t)
              =
              identity _)
        as ->.
      {
        apply id_comp_cat_functor_subst_ty_coe.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- !comp_coerce_subst_ty.
        etrans.
        {
          apply maponpaths.
          do 2 refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
          apply comp_cat_el_map_on_idpath.
        }
        rewrite id_left.
        etrans.
        {
          apply maponpaths.
          apply z_iso_after_z_iso_inv.
        }
        apply id_coerce_subst_ty.
      }
      rewrite !id_left.
      apply idpath.
    Qed.

    Definition disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv
      : comp_cat_functor_preserves_univ_type (id₁ C) u₂ u₁.
    Proof.
      use make_comp_cat_functor_preserves_univ_type.
      - exact disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv_preserves_el.
      - exact disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv_preserves_stable_el.
    Defined.

    Lemma disp_bicat_comp_cat_ob_univ_to_adj_equiv_natural
          {Γ : C}
          {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
          (r : t₁ = t₂)
      : p Γ t₁ · comp_cat_el_map_on_eq _ r
        =
        comp_cat_el_map_on_eq _ r · p Γ t₂.
    Proof.
      induction r.
      exact (id_right _ @ !(id_left _)).
    Qed.

    Proposition disp_bicat_comp_cat_ob_univ_to_adj_equiv_unit
      : comp_cat_nat_trans_preserves_univ_type
          (left_adjoint_unit (internal_adjunction_data_identity C))
          (id_comp_cat_functor_preserves_univ_type u₁)
          (comp_comp_cat_functor_preserves_univ_type
             disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor
             disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv).
    Proof.
      intros Γ t.
      etrans.
      {
        refine (!_).
        apply (comp_cat_el_map_on_concat u₁).
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        apply comp_cat_type_fib_nat_trans_on_linvunitor.
      }
      etrans.
      {
        apply maponpaths_2.
        apply id_subst_ty_natural.
      }
      rewrite assoc'.
      etrans.
      {
        apply maponpaths.
        apply comp_cat_univ_el_stable_id_coh.
      }
      etrans.
      {
        apply maponpaths_2.
        exact (eq_comp_comp_cat_functor_preserves_univ
                 disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor
                 disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv
                 t).
      }
      etrans.
      {
        do 3 apply maponpaths_2.
        apply id_comp_cat_functor_coerce.
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        do 2 apply maponpaths_2.
        apply disp_bicat_comp_cat_ob_univ_to_adj_equiv_natural.
      }
      etrans.
      {
        do 3 apply maponpaths_2.
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply z_iso_inv_after_z_iso.
        }
        apply id_right.
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply (comp_cat_el_map_on_concat u₁).
      }
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (comp_cat_el_map_on_concat u₁).
      }
      refine (!(comp_cat_el_map_on_concat u₁ _ _) @ _).
      apply eq_comp_cat_el_map_on_eq.
    Qed.

    Proposition disp_bicat_comp_cat_ob_univ_to_adj_equiv_counit
      : comp_cat_nat_trans_preserves_univ_type
          (left_adjoint_counit (internal_adjunction_data_identity C))
          (comp_comp_cat_functor_preserves_univ_type
             disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv
             disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor)
          (id_comp_cat_functor_preserves_univ_type u₂).
    Proof.
      intros Γ t.
      etrans.
      {
        apply maponpaths_2.
        exact (eq_comp_comp_cat_functor_preserves_univ
                 disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv
                 disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor
                 t).
      }
      etrans.
      {
        do 3 apply maponpaths_2.
        apply id_comp_cat_functor_coerce.
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply disp_bicat_comp_cat_ob_univ_to_adj_equiv_natural.
        }
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply z_iso_after_z_iso_inv.
        }
        apply id_left.
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply (comp_cat_el_map_on_concat u₂).
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        apply comp_cat_type_fib_nat_trans_on_lunitor.
      }
      etrans.
      {
        apply maponpaths_2.
        exact (id_subst_ty_natural
                 (comp_cat_functor_preserves_univ_type_el_mor
                    (id_comp_cat_functor_preserves_univ_type u₂)
                    t)).
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply comp_cat_univ_el_stable_id_coh.
      }
      refine (!(comp_cat_el_map_on_concat u₂ _ _) @ _).
      refine (!_).
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (comp_cat_el_map_on_concat u₂).
      }
      etrans.
      {
        refine (!_).
        apply (comp_cat_el_map_on_concat u₂).
      }
      apply eq_comp_cat_el_map_on_eq.
    Qed.

    Definition disp_bicat_comp_cat_ob_univ_to_adj_equiv_data
      : disp_left_adjoint_data
          (D := disp_bicat_comp_cat_ob_univ)
          (internal_adjoint_equivalence_identity C)
          disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact disp_bicat_comp_cat_ob_univ_to_adj_equiv_inv.
      - exact disp_bicat_comp_cat_ob_univ_to_adj_equiv_unit.
      - exact disp_bicat_comp_cat_ob_univ_to_adj_equiv_counit.
    Defined.

    Definition  disp_bicat_comp_cat_ob_univ_to_adj_equiv
      : disp_adjoint_equivalence
          (D := disp_bicat_comp_cat_ob_univ)
          (internal_adjoint_equivalence_identity C)
          u₁
          u₂.
    Proof.
      refine (disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor
              ,,
              disp_bicat_comp_cat_ob_univ_to_adj_equiv_data
              ,,
              _).
      split.
      - abstract
          (split ; apply disp_2cells_isaprop_disp_bicat_comp_cat_ob_univ).
      - abstract
          (split ; apply disp_locally_groupoid_disp_bicat_comp_cat_ob_univ).
    Defined.
  End ToDispAdjEquiv.

  Section FromDispAdjEquiv.
    Context (f : disp_adjoint_equivalence
                   (D := disp_bicat_comp_cat_ob_univ)
                   (internal_adjoint_equivalence_identity C)
                   u₁
                   u₂).

    Let Fu : comp_cat_functor_preserves_univ_type (id₁ C) u₁ u₂
      := pr1 f.

    Definition disp_bicat_comp_cat_ob_univ_adj_equiv_to_iso
               {Γ : C}
               (t : tm Γ (comp_cat_univ Γ))
      : z_iso
          (C := fiber_category _ _)
          (comp_cat_univ_el u₁ t)
          (comp_cat_univ_el u₂ t).
    Proof.
      refine (z_iso_comp
                (comp_cat_functor_preserves_univ_type_el_iso Fu t)
                (comp_cat_el_map_on_eq_iso _ _)).
      exact (!(disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_path t)).
    Defined.

    Proposition disp_bicat_comp_cat_ob_univ_adj_equiv_to_eq
                {Γ Δ : C}
                (s : Γ --> Δ)
                (t : tm Δ (comp_cat_univ Δ))
      : comp_cat_univ_el_stable u₁ s t
        · disp_bicat_comp_cat_ob_univ_adj_equiv_to_iso
            (t [[s ]]tm ↑ sub_comp_cat_univ s)
        =
        coerce_subst_ty
          s
          (disp_bicat_comp_cat_ob_univ_adj_equiv_to_iso t : _ --> _)
        · comp_cat_univ_el_stable u₂ s t.
    Proof.
      assert ((comp_cat_functor_tm (id₁ C : comp_cat_functor_ob _ _) t
               ↑ functor_comp_cat_on_univ (id₁ C) Δ) [[ s ]]tm
              ↑ sub_comp_cat_univ s
              =
              t [[ s ]]tm ↑ sub_comp_cat_univ s)
        as q.
      {
        rewrite subst_coerce_comp_cat_tm.
        rewrite comp_coerce_comp_cat_tm.
        rewrite id_functor_comp_cat_on_univ.
        etrans.
        {
          apply maponpaths.
          refine (maponpaths (λ z, z [[ _ ]]tm) _).
          apply id_comp_cat_functor_tm.
        }
        apply maponpaths_2.
        refine (_ @ id_left _).
        apply maponpaths_2.
        apply id_coerce_subst_ty.
      }
      pose (comp_cat_functor_preserves_univ_type_el_stable Fu s t) as p.
      simple refine (_ @ maponpaths (λ z, z · comp_cat_el_map_on_eq _ q) (!p) @ _).
      - rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply id_comp_cat_functor_coerce.
        }
        apply maponpaths.
        refine (maponpaths (λ z, _ · z) _).
        refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
        apply eq_comp_cat_el_map_on_eq.
      - assert (comp_cat_functor_subst_ty_coe
                  (id₁ C : comp_cat_functor_ob _ _)
                  s
                  (comp_cat_univ_el u₁ t)
                =
                identity _)
          as ->.
        {
          apply id_comp_cat_functor_subst_ty_coe.
        }
        rewrite id_left.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply comp_coerce_subst_ty.
        }
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          use comp_cat_univ_el_stable_natural.
          apply q.
        }
        apply maponpaths.
        apply idpath.
    Qed.

    Definition disp_bicat_comp_cat_ob_univ_adj_equiv_to_iso_eq
      : ∑ (p : ∏ (Γ : C)
                 (t : tm Γ (comp_cat_univ Γ)),
               z_iso
                 (C := fiber_category _ _)
                 (comp_cat_univ_el u₁ t)
                 (comp_cat_univ_el u₂ t)),
        ∏ (Γ Δ : C)
          (s : Γ --> Δ)
          (t : tm Δ (comp_cat_univ Δ)),
        comp_cat_univ_el_stable u₁ s t
        · p Γ (t [[s ]]tm ↑ sub_comp_cat_univ s)
        =
        coerce_subst_ty s (p Δ t : _ --> _)
        · comp_cat_univ_el_stable u₂ s t.
    Proof.
      simple refine (_ ,, _).
      - exact (λ Γ t, disp_bicat_comp_cat_ob_univ_adj_equiv_to_iso t).
      - exact (λ Γ Δ s t, disp_bicat_comp_cat_ob_univ_adj_equiv_to_eq s t).
    Defined.
  End FromDispAdjEquiv.

  Proposition disp_bicat_comp_cat_ob_univ_adj_equiv_weq_left
              (f : ∑ (p : ∏ (Γ : C)
                            (t : tm Γ (comp_cat_univ Γ)),
                          z_iso
                            (C := fiber_category _ _)
                            (comp_cat_univ_el u₁ t)
                            (comp_cat_univ_el u₂ t)),
                   ∏ (Γ Δ : C)
                     (s : Γ --> Δ)
                     (t : tm Δ (comp_cat_univ Δ)),
                   comp_cat_univ_el_stable u₁ s t
                   · p Γ (t [[s ]]tm ↑ sub_comp_cat_univ s)
                   =
                   coerce_subst_ty s (p Δ t : _ --> _)
                   · comp_cat_univ_el_stable u₂ s t)
    : disp_bicat_comp_cat_ob_univ_adj_equiv_to_iso_eq
        (disp_bicat_comp_cat_ob_univ_to_adj_equiv (pr1 f) (pr2 f))
      =
      f.
  Proof.
    use subtypePath.
    {
      intro.
      repeat (use impred ; intro).
      apply homset_property.
    }
    use funextsec ; intro Γ.
    use funextsec ; intro t.
    use z_iso_eq.
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    rewrite comp_cat_el_map_on_idpath.
    apply id_right.
  Qed.

  Proposition disp_bicat_comp_cat_ob_univ_adj_equiv_weq_right
              (f : disp_adjoint_equivalence
                     (D := disp_bicat_comp_cat_ob_univ)
                     (internal_adjoint_equivalence_identity C)
                     u₁
                     u₂)
    : disp_bicat_comp_cat_ob_univ_to_adj_equiv
        _
        (λ Γ Δ s t, disp_bicat_comp_cat_ob_univ_adj_equiv_to_eq f s t)
      =
      f.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_disp_left_adjoint_equivalence.
      {
        exact is_univalent_2_1_bicat_comp_cat_with_ob.
      }
      exact disp_univalent_2_1_disp_bicat_comp_cat_ob_univ.
    }
    use comp_cat_functor_preserves_univ_type_eq.
    intros Γ t.
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    etrans.
    {
      apply maponpaths.
      apply comp_cat_el_map_on_idpath.
    }
    refine (id_right _ @ _).
    apply idpath.
  Qed.

  Definition disp_bicat_comp_cat_ob_univ_adj_equiv_weq
    : (∑ (p : ∏ (Γ : C)
                (t : tm Γ (comp_cat_univ Γ)),
              z_iso
                (C := fiber_category _ _)
                (comp_cat_univ_el u₁ t)
                (comp_cat_univ_el u₂ t)),
       ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (t : tm Δ (comp_cat_univ Δ)),
       comp_cat_univ_el_stable u₁ s t
       · p Γ (t [[s ]]tm ↑ sub_comp_cat_univ s)
       =
       coerce_subst_ty s (p Δ t : _ --> _)
       · comp_cat_univ_el_stable u₂ s t)
      ≃
      disp_adjoint_equivalence
        (D := disp_bicat_comp_cat_ob_univ)
        (internal_adjoint_equivalence_identity C)
        u₁
        u₂.
  Proof.
    use weq_iso.
    - intros pq.
      exact (disp_bicat_comp_cat_ob_univ_to_adj_equiv (pr1 pq) (pr2 pq)).
    - intros f.
      exact (disp_bicat_comp_cat_ob_univ_adj_equiv_to_iso_eq f).
    - apply disp_bicat_comp_cat_ob_univ_adj_equiv_weq_left.
    - apply disp_bicat_comp_cat_ob_univ_adj_equiv_weq_right.
  Defined.
End DispAdjEquiv.

(** * 6. Global univalence *)
Proposition disp_univalent_2_0_disp_bicat_comp_cat_ob_univ
  : disp_univalent_2_0 disp_bicat_comp_cat_ob_univ.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  intros C u₁ u₂.
  use weqhomot.
  - exact (disp_bicat_comp_cat_ob_univ_adj_equiv_weq u₁ u₂
           ∘ path_comp_cat_univ_type_weq u₁ u₂)%weq.
  - intro p ; cbn in p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_disp_left_adjoint_equivalence.
      {
        exact is_univalent_2_1_bicat_comp_cat_with_ob.
      }
      exact disp_univalent_2_1_disp_bicat_comp_cat_ob_univ.
    }
    use comp_cat_functor_preserves_univ_type_eq.
    intros Γ t.
    etrans.
    {
      apply disp_bicat_comp_cat_ob_univ_to_adj_equiv_mor_eq.
    }
    etrans.
    {
      apply id_left.
    }
    cbn in u₁.
    apply (eq_comp_cat_el_map_on_eq u₁).
Qed.

Proposition disp_univalent_2_disp_bicat_comp_cat_ob_univ
  : disp_univalent_2 disp_bicat_comp_cat_ob_univ.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_comp_cat_ob_univ.
  - exact disp_univalent_2_1_disp_bicat_comp_cat_ob_univ.
Qed.

(** * 7. The bicategory of comprehension categories with a universe *)
Definition disp_bicat_comp_cat_with_univ
  : disp_bicat bicat_comp_cat
  := sigma_bicat
       _
       _
       disp_bicat_comp_cat_ob_univ.

Proposition disp_univalent_2_disp_bicat_comp_cat_with_univ
  : disp_univalent_2 disp_bicat_comp_cat_with_univ.
Proof.
  use sigma_disp_univalent_2_with_props.
  - exact is_univalent_2_bicat_comp_cat.
  - exact disp_2cells_isaprop_disp_bicat_comp_cat_with_ob.
  - exact disp_2cells_isaprop_disp_bicat_comp_cat_ob_univ.
  - exact disp_univalent_2_1_disp_bicat_comp_cat_with_ob.
  - exact disp_univalent_2_1_disp_bicat_comp_cat_ob_univ.
  - exact disp_locally_groupoid_disp_bicat_comp_cat_with_ob.
  - exact disp_locally_groupoid_disp_bicat_comp_cat_ob_univ.
  - exact disp_univalent_2_disp_bicat_comp_cat_with_ob.
  - exact disp_univalent_2_disp_bicat_comp_cat_ob_univ.
Qed.

Proposition disp_univalent_2_0_disp_bicat_comp_cat_with_univ
  : disp_univalent_2_0 disp_bicat_comp_cat_with_univ.
Proof.
  exact (pr1 disp_univalent_2_disp_bicat_comp_cat_with_univ).
Qed.

Proposition disp_univalent_2_1_disp_bicat_comp_cat_with_univ
  : disp_univalent_2_1 disp_bicat_comp_cat_with_univ.
Proof.
  exact (pr2 disp_univalent_2_disp_bicat_comp_cat_with_univ).
Qed.

Proposition disp_2cells_isaprop_disp_bicat_comp_cat_with_univ
  : disp_2cells_isaprop disp_bicat_comp_cat_with_univ.
Proof.
  use disp_2cells_isaprop_sigma.
  - exact disp_2cells_isaprop_disp_bicat_comp_cat_with_ob.
  - exact disp_2cells_isaprop_disp_bicat_comp_cat_ob_univ.
Qed.

Proposition disp_locally_groupoid_disp_bicat_comp_cat_with_univ
  : disp_locally_groupoid disp_bicat_comp_cat_with_univ.
Proof.
  use disp_locally_groupoid_sigma.
  - exact is_univalent_2_bicat_comp_cat.
  - exact disp_2cells_isaprop_disp_bicat_comp_cat_with_ob.
  - exact disp_2cells_isaprop_disp_bicat_comp_cat_ob_univ.
  - exact disp_locally_groupoid_disp_bicat_comp_cat_with_ob.
  - exact disp_locally_groupoid_disp_bicat_comp_cat_ob_univ.
Qed.

(** * 8. The bicategory of full comprehension categories with a universe *)
Definition disp_bicat_full_comp_cat_with_univ
  : disp_bicat bicat_full_comp_cat
  := lift_disp_bicat
       _
       disp_bicat_comp_cat_with_univ.

Proposition disp_univalent_2_0_disp_bicat_full_comp_cat_with_univ
  : disp_univalent_2_0 disp_bicat_full_comp_cat_with_univ.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact disp_univalent_2_0_disp_bicat_comp_cat_with_univ.
  - exact disp_univalent_2_1_disp_bicat_comp_cat_with_univ.
  - exact is_univalent_2_1_bicat_comp_cat.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat.
Qed.

Proposition disp_univalent_2_1_disp_bicat_full_comp_cat_with_univ
  : disp_univalent_2_1 disp_bicat_full_comp_cat_with_univ.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact disp_univalent_2_1_disp_bicat_comp_cat_with_univ.
Qed.

Proposition disp_univalent_2_disp_bicat_full_comp_cat_with_univ
  : disp_univalent_2 disp_bicat_full_comp_cat_with_univ.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_full_comp_cat_with_univ.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat_with_univ.
Qed.

Proposition disp_2cells_isaprop_disp_bicat_full_comp_cat_with_univ
  : disp_2cells_isaprop disp_bicat_full_comp_cat_with_univ.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_comp_cat_with_univ.
Qed.

Proposition disp_locally_groupoid_disp_bicat_full_comp_cat_with_univ
  : disp_locally_groupoid disp_bicat_full_comp_cat_with_univ.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_comp_cat_with_univ.
Qed.

(** * 9. The bicategory of DFL full comprehension categories with a universe *)
Definition disp_bicat_dfl_full_comp_cat_with_univ
  : disp_bicat bicat_of_dfl_full_comp_cat
  := lift_disp_bicat
       _
       disp_bicat_full_comp_cat_with_univ.

Proposition disp_univalent_2_0_disp_bicat_dfl_full_comp_cat_with_univ
  : disp_univalent_2_0 disp_bicat_dfl_full_comp_cat_with_univ.
Proof.
  use disp_univalent_2_0_lift_disp_bicat.
  - exact disp_univalent_2_0_disp_bicat_full_comp_cat_with_univ.
  - exact disp_univalent_2_1_disp_bicat_full_comp_cat_with_univ.
  - exact is_univalent_2_1_bicat_full_comp_cat.
  - exact is_univalent_2_1_disp_bicat_of_dfl_full_comp_cat.
Qed.

Proposition disp_univalent_2_1_disp_bicat_dfl_full_comp_cat_with_univ
  : disp_univalent_2_1 disp_bicat_dfl_full_comp_cat_with_univ.
Proof.
  use disp_univalent_2_1_lift_disp_bicat.
  exact disp_univalent_2_1_disp_bicat_full_comp_cat_with_univ.
Qed.

Proposition disp_univalent_2_disp_bicat_dfl_full_comp_cat_with_univ
  : disp_univalent_2 disp_bicat_dfl_full_comp_cat_with_univ.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_dfl_full_comp_cat_with_univ.
  - exact disp_univalent_2_1_disp_bicat_dfl_full_comp_cat_with_univ.
Qed.

Proposition disp_2cells_isaprop_disp_bicat_dfl_full_comp_cat_with_univ
  : disp_2cells_isaprop disp_bicat_dfl_full_comp_cat_with_univ.
Proof.
  use disp_2cells_isaprop_lift_disp_bicat.
  exact disp_2cells_isaprop_disp_bicat_full_comp_cat_with_univ.
Qed.

Proposition disp_locally_groupoid_disp_bicat_dfl_full_comp_cat_with_univ
  : disp_locally_groupoid disp_bicat_dfl_full_comp_cat_with_univ.
Proof.
  use disp_locally_groupoid_lift_disp_bicat.
  exact disp_locally_groupoid_disp_bicat_full_comp_cat_with_univ.
Qed.
