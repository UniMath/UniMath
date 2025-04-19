(**

 The displayed bicategory of universes

 In this file, we define the bicategory of univalent categories with finite limits and a
 universe. For this we collect the material in `CatWithOb.v` and `UniverseInCat.v`. First, we
 define the bicategory of universe structures over the bicategory of univalent categories with
 finite limits and an object (see [disp_bicat_finlim_el]), and we prove that this displayed
 bicategory is univalent. The relevant definitions are given in the file `UniverseInCat.v`.
 Since we want a displayed bicategory over `bicat_of_univ_cat_with_finlim` (i.e., the bicategory
 of univalent categories with finite limits), we take the sigma construction to get the
 displayed bicategory [disp_bicat_finlim_universe].

 Content
 1. The displayed bicategory of universes over categories with finite limits and an object
 2. This displayed bicategory is univalent
 3. The displayed bicategory of universes over categories with finite limits
 4. Accessors

                                                                                               *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.

Local Open Scope cat.

(** * 1. The displayed bicategory of universes over categories with finite limits and an object *)
Definition disp_cat_ob_mor_finlim_el
  : disp_cat_ob_mor bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact cat_stable_el_map_coherent.
  - exact (λ (C₁ C₂ : univ_cat_with_finlim_ob)
             (el₁ : cat_stable_el_map_coherent C₁)
             (el₂ : cat_stable_el_map_coherent C₂)
             (F : functor_finlim_ob C₁ C₂),
           functor_preserves_el el₁ el₂ F).
Defined.

Definition disp_cat_id_comp_finlim_el
  : disp_cat_id_comp bicat_of_univ_cat_with_finlim_ob disp_cat_ob_mor_finlim_el.
Proof.
  simple refine (_ ,, _).
  - intros C el.
    exact (id_functor_preserves_el (pr1 el)).
  - intros C₁ C₂ C₃ F G el₁ el₂ el₃ Fel Gel.
    exact (comp_functor_preserves_el Fel Gel).
Defined.

Definition disp_cat_data_finlim_el
  : disp_cat_data bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_ob_mor_finlim_el.
  - exact disp_cat_id_comp_finlim_el.
Defined.

Definition disp_prebicat_1_id_comp_cells_finlim_el
  : disp_prebicat_1_id_comp_cells bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_cat_data_finlim_el.
  - exact (λ (C₁ C₂ : univ_cat_with_finlim_ob)
             (F G : functor_finlim_ob C₁ C₂)
             (τ : nat_trans_finlim_ob F G)
             (el₁ : cat_stable_el_map_coherent C₁)
             (el₂ : cat_stable_el_map_coherent C₂)
             (Fe : functor_preserves_el el₁ el₂ F)
             (Ge : functor_preserves_el el₁ el₂ G),
           nat_trans_preserves_el τ Fe Ge).
Defined.

Proposition disp_prebicat_ops_finlim_el
  : disp_prebicat_ops
      disp_prebicat_1_id_comp_cells_finlim_el.
Proof.
  repeat split.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    refine (!(id_right _) @ _).
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_id.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !assoc'.
    rewrite !cat_el_map_el_eq_comp.
    refine (!_).
    etrans.
    {
      exact (functor_el_map_iso_eq _ (id_right _)).
    }
    rewrite !assoc.
    use cat_el_map_el_eq_postcomp.
    apply maponpaths_2.
    apply maponpaths.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    rewrite !assoc'.
    refine (!(id_right _) @ _).
    apply maponpaths.
    rewrite !assoc.
    rewrite !cat_el_map_el_eq_comp.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_id.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths_2.
      exact (functor_el_map_iso_eq _ (id_right _)).
    }
    rewrite !assoc'.
    rewrite !cat_el_map_el_eq_comp.
    rewrite !assoc.
    refine (assoc _ _ _ @ _).
    use cat_el_map_el_eq_postcomp.
    apply maponpaths_2.
    apply maponpaths.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ F el₁ el₂ Fe Γ t.
    simpl.
    rewrite id_left.
    rewrite cat_el_map_el_eq_comp.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ C₃ C₄ F G H el₁ el₂ el₃ el₄ Fel Gel Hel Γ t.
    simpl.
    rewrite id_left.
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths_2.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply (functor_on_cat_el_map_el_eq (pr1 Hel)).
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      rewrite z_iso_after_z_iso_inv.
      rewrite id_left.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ C₃ C₄ F G H el₁ el₂ el₃ el₄ Fel Gel Hel Γ t.
    simpl.
    rewrite id_left.
    etrans.
    {
      apply maponpaths_2.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply (functor_on_cat_el_map_el_eq (pr1 Hel)).
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (assoc _ _ _ @ _).
      rewrite z_iso_after_z_iso_inv.
      rewrite id_left.
      apply idpath.
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ F G H τ θ el₁ el₂ Fel Gel Hel p q Γ t.
    simpl.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply q.
    }
    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply p.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_comp.
    }
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      rewrite assoc'.
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply nat_trans_ax.
      }
      rewrite !assoc'.
      apply maponpaths.
      apply θ.
    }
    refine (assoc _ _ _ @ _).
    refine (_ @ assoc' _ _ _).
    apply maponpaths_2.
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ C₃ F G₁ G₂ τ el₁ el₂ el₃ Fel Gel₁ Gel₂ p Γ t.
    simpl.
    etrans.
    {
      do 2 refine (assoc _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths_2.
        refine (!_).
        apply nat_trans_ax.
      }
      do 2 refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply p.
    }
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite cat_el_map_el_eq_comp.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      apply maponpaths.
      rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
  - intros C₁ C₂ C₃ F₁ F₂ G τ el₁ el₂ el₃ Fel₁ Fel₂ Gel p Γ t.
    simpl.
    etrans.
    {
      do 2 refine (assoc _ _ _ @ _).
      do 2 apply maponpaths_2.
      refine (!(functor_comp _ _ _) @ _).
      apply maponpaths.
      apply p.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      rewrite !assoc'.
      apply functor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply functor_comp.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply (functor_on_cat_el_map_el_eq (pr1 Gel)).
    }
    rewrite !assoc'.
    apply maponpaths.

    etrans.
    {
      do 2 apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply functor_preserves_el_path.
    }
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply z_iso_after_z_iso_inv.
    }
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      apply maponpaths.
      rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    }
    refine (assoc _ _ _ @ _ @ assoc' _ _ _).
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    rewrite !cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_eq.
Qed.

Definition disp_prebicat_data_finlim_el
  : disp_prebicat_data bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_1_id_comp_cells_finlim_el.
  - exact disp_prebicat_ops_finlim_el.
Defined.


Definition disp_prebicat_finlim_el
  : disp_prebicat bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_data_finlim_el.
  - abstract
      (repeat split ;
       intro ;
       intros ;
       apply isaprop_nat_trans_preserves_el).
Defined.

Definition disp_bicat_finlim_el
  : disp_bicat bicat_of_univ_cat_with_finlim_ob.
Proof.
  simple refine (_ ,, _).
  - exact disp_prebicat_finlim_el.
  - abstract
      (intro ; intros ;
       apply isasetaprop ;
       apply isaprop_nat_trans_preserves_el).
Defined.

(** * 2. This displayed bicategory is univalent *)
Proposition disp_2cells_isaprop_disp_bicat_finlim_el
  : disp_2cells_isaprop disp_bicat_finlim_el.
Proof.
  intro ; intros.
  apply isaprop_nat_trans_preserves_el.
Qed.

Proposition is_disp_invertible_2cell_disp_bicat_finlim_el
            {C₁ C₂ : bicat_of_univ_cat_with_finlim_ob}
            {F G : C₁ --> C₂}
            {τ : invertible_2cell F G}
            {u₁ : disp_bicat_finlim_el C₁}
            {u₂ : disp_bicat_finlim_el C₂}
            {f : u₁ -->[ F ] u₂}
            {g : u₁ -->[ G ] u₂}
            (p : f ==>[ τ ] g)
  : is_disp_invertible_2cell τ p.
Proof.
Admitted.

Proposition disp_locally_groupoid_disp_bicat_finlim_el
  : disp_locally_groupoid disp_bicat_finlim_el.
Proof.
  intro ; intros.
  apply is_disp_invertible_2cell_disp_bicat_finlim_el.
Qed.

Proposition disp_univalent_2_1_disp_bicat_finlim_el
  : disp_univalent_2_1 disp_bicat_finlim_el.
Proof.
Admitted.

Proposition disp_univalent_2_0_disp_bicat_finlim_el
  : disp_univalent_2_0 disp_bicat_finlim_el.
Proof.
Admitted.

Proposition disp_univalent_2_disp_bicat_finlim_el
  : disp_univalent_2 disp_bicat_finlim_el.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_finlim_el.
  - exact disp_univalent_2_1_disp_bicat_finlim_el.
Qed.

(** * 3. The displayed bicategory of universes over categories with finite limits *)
Definition disp_bicat_finlim_universe
  : disp_bicat bicat_of_univ_cat_with_finlim
  := sigma_bicat _ _ disp_bicat_finlim_el.

Proposition disp_univalent_2_1_disp_bicat_finlim_universe
  : disp_univalent_2_1 disp_bicat_finlim_universe.
Proof.
  use sigma_disp_univalent_2_1_with_props.
  - exact disp_2cells_isaprop_disp_bicat_finlim_ob.
  - exact disp_2cells_isaprop_disp_bicat_finlim_el.
  - exact disp_univalent_2_1_disp_bicat_finlim_ob.
  - exact disp_univalent_2_1_disp_bicat_finlim_el.
Qed.

Proposition disp_univalent_2_0_disp_bicat_finlim_universe
  : disp_univalent_2_0 disp_bicat_finlim_universe.
Proof.
  use sigma_disp_univalent_2_0_with_props.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
  - exact disp_2cells_isaprop_disp_bicat_finlim_ob.
  - exact disp_2cells_isaprop_disp_bicat_finlim_el.
  - exact disp_univalent_2_1_disp_bicat_finlim_ob.
  - exact disp_univalent_2_1_disp_bicat_finlim_el.
  - exact disp_locally_groupoid_disp_bicat_finlim_ob.
  - exact disp_locally_groupoid_disp_bicat_finlim_el.
  - exact disp_univalent_2_0_disp_bicat_finlim_ob.
  - exact disp_univalent_2_0_disp_bicat_finlim_el.
Qed.

Proposition disp_univalent_2_disp_bicat_finlim_universe
  : disp_univalent_2 disp_bicat_finlim_universe.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_finlim_universe.
  - exact disp_univalent_2_1_disp_bicat_finlim_universe.
Qed.

(** * 4. Accessors *)
