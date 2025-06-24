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
 2. Invertible 2-cells and local univalence
 3. Adjoint equivalences and global univalence
 4. The displayed bicategory of universes over categories with finite limits
 5. Accessors
 6. Adjoint equivalence between categories with finite limits and a universe
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

(** * 2. Invertible 2-cells and local univalence *)
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
  simple refine (_ ,, _ ,, _) ;
    [
    | apply disp_2cells_isaprop_disp_bicat_finlim_el
    | apply disp_2cells_isaprop_disp_bicat_finlim_el ].
  intros Γ t ; cbn.
  rewrite invertible_2cell_cat_with_finlim_ob.
  use z_iso_inv_on_right.
  cbn.
  rewrite !assoc.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    exact (p Γ t).
  }
  rewrite !assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (!_).
    use cat_el_map_pb_mor_eq.
    refine (!_).
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (maponpaths (λ z, pr111 z Γ) (vcomp_rinv τ)).
    }
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      exact (!(nat_trans_universe_eq (pr1 τ))).
    }
    rewrite !assoc.
    apply maponpaths_2.
    exact (nat_trans_ax (pr111 τ) _ _ t).
  }
  rewrite !assoc'.
  etrans.
  {
    do 2 apply maponpaths.
    apply cat_el_map_pb_mor_comp'.
  }
  etrans.
  {
    do 3 apply maponpaths.
    use cat_el_map_pb_mor_id'.
    refine (!_).
    exact (maponpaths (λ z, pr111 z Γ) (vcomp_rinv τ)).
  }
  rewrite !cat_el_map_el_eq_comp.
  apply cat_el_map_el_eq_id.
Qed.

Proposition disp_locally_groupoid_disp_bicat_finlim_el
  : disp_locally_groupoid disp_bicat_finlim_el.
Proof.
  intro ; intros.
  apply is_disp_invertible_2cell_disp_bicat_finlim_el.
Qed.

Proposition disp_univalent_2_1_disp_bicat_finlim_el
  : disp_univalent_2_1 disp_bicat_finlim_el.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  intros C₁ C₂ F u₁ u₂ f f'.
  use isweqimplimpl.
  - cbn ; intro τ.
    use subtypePath.
    {
      intro.
      apply isaprop_functor_stable_el_map.
    }
    use funextsec ; intro Γ.
    use funextsec ; intro t.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use z_iso_eq.
    pose (pr1 τ Γ t) as p.
    refine (_ @ !p @ id_left _).
    rewrite !assoc'.
    refine (!(id_right _) @ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_id.
    }
    rewrite cat_el_map_el_eq_comp.
    apply cat_el_map_el_eq_id.
  - apply isaset_functor_preserves_el.
  - use isaproptotal2.
    + intro.
      apply isaprop_is_disp_invertible_2cell.
    + intros.
      apply disp_2cells_isaprop_disp_bicat_finlim_el.
Qed.

(** * 3. Adjoint equivalences and global univalence *)
Section AdjEquiv.
  Context {C : univ_cat_with_finlim_ob}
          (u₁ u₂ : cat_stable_el_map_coherent C).

  Section ToMorIsAdjEquiv.
    Context (ff : mor_disp
                    (D := disp_bicat_finlim_el)
                    u₁
                    u₂
                    (identity _)).

    Definition disp_bicat_finlim_el_to_adjequiv_mor_z_iso
               (Γ : C)
               (t : Γ --> univ_cat_universe C)
      : z_iso (cat_el_map_el u₂ t) (cat_el_map_el u₁ (t · id₁ _))
      := z_iso_comp
           (z_iso_comp
              (cat_el_map_el_eq u₂ (!(id_right _)))
              (z_iso_inv (pr1 (pr1 ff Γ t))))
           (cat_el_map_el_eq u₁ (!(id_right _))).

    Definition disp_bicat_finlim_el_to_adjequiv_mor_el_map
      : functor_el_map u₂ u₁ (id₁ _).
    Proof.
      use make_functor_el_map.
      - exact disp_bicat_finlim_el_to_adjequiv_mor_z_iso.
      - cbn.
        abstract
          (intros Γ t ; cbn ;
           use (cancel_z_iso' (cat_el_map_el_eq u₂ (id_right _))) ;
           rewrite !assoc ;
           rewrite cat_el_map_el_eq_comp ;
           rewrite pathsinv0r ;
           rewrite !assoc' ;
           refine (_ @ !(id_left _)) ;
           refine (!_) ;
           use z_iso_inv_on_right ;
           rewrite cat_el_map_mor_eq ;
           refine (pr2 (pr1 ff Γ t) @ _) ;
           apply maponpaths ;
           rewrite cat_el_map_mor_eq ;
           apply idpath).
    Defined.

    Proposition disp_bicat_finlim_el_to_adjequiv_mor_stable
      : functor_stable_el_map disp_bicat_finlim_el_to_adjequiv_mor_el_map.
    Proof.
      intros Γ Δ s t ; cbn.
      rewrite !assoc'.
      use (cancel_z_iso' (cat_el_map_el_eq u₂ (id_right _))).
      rewrite !assoc.
      rewrite cat_el_map_el_eq_comp.
      rewrite pathsinv0r.
      rewrite !assoc'.
      refine (_ @ !(id_left _)).
      refine (!_).
      use z_iso_inv_on_right.
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        use cat_el_map_pb_mor_eq.
        abstract
          (rewrite id_right ;
           apply idpath).
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        do 2 refine (assoc _ _ _ @ _).
        refine (_ @ !(pr2 ff Γ Δ s t)).
        apply maponpaths_2.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        rewrite cat_el_map_el_eq_comp.
        apply cat_el_map_el_eq_eq.
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite z_iso_inv_after_z_iso.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        refine (!_).
        use cat_el_map_pb_mor_eq.
        abstract
          (rewrite id_right ;
           apply idpath).
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite cat_el_map_el_eq_comp.
      apply cat_el_map_el_eq_eq.
    Qed.

    Definition disp_bicat_finlim_el_to_adjequiv_inv
      : functor_preserves_el u₂ u₁ (id₁ C).
    Proof.
      use make_functor_preserves_el.
      - exact disp_bicat_finlim_el_to_adjequiv_mor_el_map.
      - exact disp_bicat_finlim_el_to_adjequiv_mor_stable.
    Defined.

    Proposition disp_bicat_finlim_el_to_adjequiv_unit
      : nat_trans_preserves_el
          (left_adjoint_unit (internal_adjunction_data_identity _))
          (id_functor_preserves_el u₁)
          (comp_functor_preserves_el
             ff
             disp_bicat_finlim_el_to_adjequiv_inv).
    Proof.
      intros Γ t ; simpl.
      refine (id_left _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_pb_mor_id.
      }
      rewrite !cat_el_map_el_eq_comp.
      rewrite !assoc'.
      rewrite !cat_el_map_el_eq_comp.
      rewrite !assoc.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths_2.
        use (functor_el_map_iso_eq (pr1 ff) (id_right _)).
      }
      etrans.
      {
        do 3 refine (assoc' _ _ _ @ _).
        apply maponpaths.
        do 2 refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        rewrite cat_el_map_el_eq_comp.
        etrans.
        {
          apply maponpaths_2.
          apply cat_el_map_el_eq_id.
        }
        apply id_left.
      }
      etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply z_iso_inv_after_z_iso.
        }
        apply id_left.
      }
      refine (cat_el_map_el_eq_comp _ _ _ @ _).
      apply cat_el_map_el_eq_eq.
    Qed.

    Proposition disp_bicat_finlim_el_to_adjequiv_counit
      : nat_trans_preserves_el
          (left_adjoint_counit (internal_adjunction_data_identity _))
          (comp_functor_preserves_el
             disp_bicat_finlim_el_to_adjequiv_inv
             ff)
          (id_functor_preserves_el u₂).
    Proof.
      intros Γ t ; simpl.
      refine (id_left _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_pb_mor_id.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        do 4 refine (assoc _ _ _ @ _).
        do 3 apply maponpaths_2.
        apply maponpaths.
        use (functor_el_map_iso_eq (pr1 ff) (!(id_right _))).
      }
      etrans.
      {
        apply maponpaths.
        do 3 apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            refine (assoc _ _ _ @ _).
            apply maponpaths_2.
            refine (cat_el_map_el_eq_comp _ _ _ @ _).
            apply cat_el_map_el_eq_id.
          }
          rewrite id_left.
          apply z_iso_after_z_iso_inv.
        }
        apply id_left.
      }
      rewrite !cat_el_map_el_eq_comp.
      apply cat_el_map_el_eq_eq.
    Qed.

    Definition to_disp_left_adjoint_equivalence_over_identity_finlim_ob
      : disp_left_adjoint_equivalence (internal_adjoint_equivalence_identity _) ff.
    Proof.
      simple refine (_ ,, _ ,, _) ;
        [
        | split ; apply disp_2cells_isaprop_disp_bicat_finlim_el
        | split ; apply disp_locally_groupoid_disp_bicat_finlim_el ].
      simple refine (_ ,, _ ,, _).
      - exact disp_bicat_finlim_el_to_adjequiv_inv.
      - exact disp_bicat_finlim_el_to_adjequiv_unit.
      - exact disp_bicat_finlim_el_to_adjequiv_counit.
    Defined.
  End ToMorIsAdjEquiv.

  Section ToAdjEquiv.
    Context {p : ∏ (Γ : C)
                   (t : Γ --> univ_cat_universe C),
                 z_iso (cat_el_map_el u₁ t) (cat_el_map_el u₂ t)}
            (q : ∏ (Γ : C)
                   (t : Γ --> univ_cat_universe C),
                 p Γ t · cat_el_map_mor u₂ t
                 =
                 cat_el_map_mor u₁ t)
            (r : ∏ (Γ Δ : C)
                   (s : Γ --> Δ)
                   (t : Δ --> univ_cat_universe C),
                 cat_el_map_pb_mor u₁ s t · p Δ t
                 =
                 p Γ (s · t) · cat_el_map_pb_mor u₂ s t).

    Definition disp_bicat_finlim_el_to_adjequiv_mor
      : functor_preserves_el u₁ u₂ (id₁ C).
    Proof.
      use make_functor_preserves_el.
      - use make_functor_el_map.
        + exact (λ Γ t, z_iso_comp (p Γ t) (cat_el_map_el_eq u₂ (!(id_right _)))).
        + abstract
            (intros Γ t ; cbn ;
             refine (!(q Γ t) @ _) ;
             rewrite !assoc' ;
             apply maponpaths ;
             rewrite cat_el_map_mor_eq ;
             apply idpath).
      - abstract
          (intros Γ Δ s t ; cbn ;
           rewrite !assoc ;
           rewrite (r Γ Δ s t) ;
           rewrite !assoc' ;
           apply maponpaths ;
           rewrite !assoc ;
           rewrite cat_el_map_el_eq_comp ;
           refine (!_) ;
           apply cat_el_map_pb_mor_eq).
    Defined.

    Definition disp_bicat_finlim_el_to_adjequiv
      : disp_adjoint_equivalence
          (D := disp_bicat_finlim_el)
          (internal_adjoint_equivalence_identity _) u₁ u₂.
    Proof.
      refine (disp_bicat_finlim_el_to_adjequiv_mor ,, _).
      apply to_disp_left_adjoint_equivalence_over_identity_finlim_ob.
    Defined.
  End ToAdjEquiv.

  Section FromAdjEquiv.
    Context (d : disp_adjoint_equivalence
                   (D := disp_bicat_finlim_el)
                   (internal_adjoint_equivalence_identity _) u₁ u₂).

    Definition disp_bicat_finlim_el_from_adjequiv_z_iso
               {Γ : C}
               (t : Γ --> univ_cat_universe C)
      : z_iso (cat_el_map_el u₁ t) (cat_el_map_el u₂ t)
      := z_iso_comp
           (functor_el_map_iso (pr11 d) t)
           (cat_el_map_el_eq u₂ (id_right _)).

    Proposition disp_bicat_finlim_el_from_adjequiv_comm
                {Γ : C}
                (t : Γ --> univ_cat_universe C)
      : disp_bicat_finlim_el_from_adjequiv_z_iso t · cat_el_map_mor u₂ t
        =
        cat_el_map_mor u₁ t.
    Proof.
      refine (_ @ !(functor_el_map_comm (pr11 d) t)) ; cbn.
      rewrite !assoc'.
      apply maponpaths.
      apply cat_el_map_mor_eq.
    Qed.

    Proposition disp_bicat_finlim_el_from_adjequiv_ob_mor
                {Γ Δ : C}
                (s : Γ --> Δ)
                (t : Δ --> univ_cat_universe C)
                (p₁ : t · id₁ _ = t)
                (p₂ : s · t · id₁ _ = s · t)
      : cat_el_map_pb_mor u₁ s t
        · (functor_el_map_iso (pr11 d) t
        · cat_el_map_el_eq u₂ p₁)
        =
        functor_el_map_iso (pr11 d) (s · t)
        · cat_el_map_el_eq u₂ p₂
        · cat_el_map_pb_mor u₂ s t.
    Proof.
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        exact (functor_preserves_el_path (pr1 d) s t).
      }
      cbn.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        use cat_el_map_pb_mor_eq.
        rewrite id_right.
        apply idpath.
      }
      rewrite !assoc.
      rewrite cat_el_map_el_eq_comp.
      apply maponpaths_2.
      apply cat_el_map_el_eq_eq.
    Qed.
  End FromAdjEquiv.

  Definition disp_bicat_finlim_el_adjequiv_weq
    : (∑ (pq : ∏ (Γ : C)
                 (t : Γ --> univ_cat_universe C),
               ∑ (p : z_iso (cat_el_map_el u₁ t) (cat_el_map_el u₂ t)),
               p · cat_el_map_mor u₂ t
               =
               cat_el_map_mor u₁ t),
       ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (t : Δ --> univ_cat_universe C),
       cat_el_map_pb_mor u₁ s t · pr1 (pq Δ t)
       =
       pr1 (pq Γ (s · t)) · cat_el_map_pb_mor u₂ s t)
      ≃
      disp_adjoint_equivalence
        (D := disp_bicat_finlim_el)
        (internal_adjoint_equivalence_identity _) u₁ u₂.
  Proof.
    use weq_iso.
    - intro p.
      exact (disp_bicat_finlim_el_to_adjequiv (λ Γ t, pr2 (pr1 p Γ t)) (pr2 p)).
    - intro d.
      simple refine (_ ,, _).
      + intros Γ t.
        simple refine (_ ,, _).
        * exact (disp_bicat_finlim_el_from_adjequiv_z_iso d t).
        * exact (disp_bicat_finlim_el_from_adjequiv_comm d t).
      + intros Γ Δ s t.
        exact (disp_bicat_finlim_el_from_adjequiv_ob_mor d s t _ _).
    - abstract
        (intro d ;
         use subtypePath ;
         [ intro ; repeat (use impred ; intro) ; apply homset_property | ] ;
         use funextsec ; intro Γ ;
         use funextsec ; intro t ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use z_iso_eq ; cbn ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         rewrite cat_el_map_el_eq_comp ;
         apply cat_el_map_el_eq_id).
    - abstract
        (intro d ;
         use subtypePath ;
         [ intro ;
           apply isaprop_disp_left_adjoint_equivalence ;
           [ apply is_univalent_2_1_bicat_of_univ_cat_with_finlim_ob
           | exact disp_univalent_2_1_disp_bicat_finlim_el ]
         | ] ;
         use subtypePath ; [ intro ; apply isaprop_functor_stable_el_map | ] ;
         use funextsec ; intro Γ ;
         use funextsec ; intro t ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use z_iso_eq ; cbn ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         rewrite cat_el_map_el_eq_comp ;
         apply cat_el_map_el_eq_id).
  Defined.
End AdjEquiv.

Definition to_disp_left_adjoint_equivalence_over_adjequiv_finlim_ob_help
           {C₁ C₂ : univ_cat_with_finlim_ob}
           {F : adjoint_equivalence C₁ C₂}
           {u₁ : cat_stable_el_map_coherent C₁}
           {u₂ : cat_stable_el_map_coherent C₂}
           (ff : mor_disp
                    (D := disp_bicat_finlim_el)
                    u₁
                    u₂
                    F)
  : disp_left_adjoint_equivalence F ff.
Proof.
  revert C₁ C₂ F u₁ u₂ ff.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_univ_cat_with_finlim_ob.
  }
  intros C u₁ u₂ ff.
  apply to_disp_left_adjoint_equivalence_over_identity_finlim_ob.
Qed.

Definition to_disp_left_adjoint_equivalence_over_adjequiv_finlim_ob
           {C₁ C₂ : univ_cat_with_finlim_ob}
           {F : C₁ --> C₂}
           (HF : left_adjoint_equivalence F)
           {u₁ : cat_stable_el_map_coherent C₁}
           {u₂ : cat_stable_el_map_coherent C₂}
           (ff : mor_disp
                    (D := disp_bicat_finlim_el)
                    u₁
                    u₂
                    F)
  : disp_left_adjoint_equivalence HF ff.
Proof.
  exact (to_disp_left_adjoint_equivalence_over_adjequiv_finlim_ob_help (F := F ,, HF) ff).
Qed.

Proposition disp_univalent_2_0_disp_bicat_finlim_el
  : disp_univalent_2_0 disp_bicat_finlim_el.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  intros C u₁ u₂.
  use weqhomot.
  - exact (disp_bicat_finlim_el_adjequiv_weq u₁ u₂ ∘ cat_el_map_eq_weq _ _)%weq.
  - intro p.
    cbn in p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_disp_left_adjoint_equivalence.
      {
        exact is_univalent_2_1_bicat_of_univ_cat_with_finlim_ob.
      }
      exact disp_univalent_2_1_disp_bicat_finlim_el.
    }
    use subtypePath.
    {
      intro.
      apply isaprop_functor_stable_el_map.
    }
    use funextsec ; intro Γ.
    use funextsec ; intro t.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use z_iso_eq ; cbn.
    apply id_left.
Qed.

Proposition disp_univalent_2_disp_bicat_finlim_el
  : disp_univalent_2 disp_bicat_finlim_el.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_finlim_el.
  - exact disp_univalent_2_1_disp_bicat_finlim_el.
Qed.

(** * 4. The displayed bicategory of universes over categories with finite limits *)
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

(** * 5. Accessors *)
Definition bicat_of_univ_cat_with_finlim_universe
  : bicat
  := total_bicat disp_bicat_finlim_universe.

Proposition is_univalent_2_bicat_of_univ_cat_with_finlim_universe
  : is_univalent_2 bicat_of_univ_cat_with_finlim_universe.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_finlim_universe.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
Qed.

Proposition is_univalent_2_1_bicat_of_univ_cat_with_finlim_universe
  : is_univalent_2_1 bicat_of_univ_cat_with_finlim_universe.
Proof.
  exact (pr2 is_univalent_2_bicat_of_univ_cat_with_finlim_universe).
Qed.

Proposition is_univalent_2_0_bicat_of_univ_cat_with_finlim_universe
  : is_univalent_2_0 bicat_of_univ_cat_with_finlim_universe.
Proof.
  exact (pr1 is_univalent_2_bicat_of_univ_cat_with_finlim_universe).
Qed.

Definition univ_cat_with_finlim_universe
  : UU
  := bicat_of_univ_cat_with_finlim_universe.

Coercion univ_cat_with_finlim_universe_to_univ_cat_finlim_ob
         (C : univ_cat_with_finlim_universe)
  : univ_cat_with_finlim_ob
  := pr1 C ,, pr12 C.

Definition univ_cat_cat_stable_el_map
           (C : univ_cat_with_finlim_universe)
  : cat_stable_el_map C
  := pr122 C.

Definition functor_finlim_universe
           (C₁ C₂ : univ_cat_with_finlim_universe)
  : UU
  := C₁ --> C₂.

Coercion functor_finlim_universe_to_functor_finlim_ob
         {C₁ C₂ : univ_cat_with_finlim_universe}
         (F : functor_finlim_universe C₁ C₂)
  : functor_finlim_ob C₁ C₂
  := pr1 F ,, pr12 F.

Definition functor_finlim_universe_preserves_el
           {C₁ C₂ : univ_cat_with_finlim_universe}
           (F : functor_finlim_universe C₁ C₂)
  : functor_preserves_el
      (univ_cat_cat_stable_el_map C₁)
      (univ_cat_cat_stable_el_map C₂)
      F
  := pr22 F.

Definition nat_trans_finlim_universe
           {C₁ C₂ : univ_cat_with_finlim_universe}
           (F G : functor_finlim_universe C₁ C₂)
  : UU
  := F ==> G.

Coercion nat_trans_finlim_ob_to_functor_nat_trans_ob
         {C₁ C₂ : univ_cat_with_finlim_universe}
         {F G : functor_finlim_universe C₁ C₂}
         (τ : nat_trans_finlim_universe F G)
  : nat_trans_finlim_ob F G
  := pr1 τ ,, pr12 τ.

Proposition nat_trans_universe_preserves_el
            {C₁ C₂ : univ_cat_with_finlim_universe}
            {F G : functor_finlim_universe C₁ C₂}
            (τ : nat_trans_finlim_universe F G)
  : nat_trans_preserves_el
      τ
      (functor_finlim_universe_preserves_el F)
      (functor_finlim_universe_preserves_el G).
Proof.
  exact (pr22 τ).
Defined.

(** * 6. Adjoint equivalence between categories with finite limits and a universe *)
Definition disp_left_adjoint_equivalence_finlim_universe
           {C₁ C₂ : univ_cat_with_finlim}
           {u₁ : disp_bicat_finlim_universe C₁}
           {u₂ : disp_bicat_finlim_universe C₂}
           {F : adjoint_equivalence C₁ C₂}
           (Fu : u₁ -->[ F ] u₂)
  : disp_left_adjoint_equivalence F Fu.
Proof.
  revert C₁ C₂ F u₁ u₂ Fu.
  use J_2_0.
  {
    exact is_univalent_2_0_bicat_of_univ_cat_with_finlim.
  }
  intros C u₁ u₂ Fu.
  use pair_disp_left_adjoint_equivalence_sigma.
  - exact is_univalent_2_bicat_of_univ_cat_with_finlim.
  - exact disp_2cells_isaprop_disp_bicat_finlim_ob.
  - exact disp_2cells_isaprop_disp_bicat_finlim_el.
  - exact disp_locally_groupoid_disp_bicat_finlim_ob.
  - exact disp_locally_groupoid_disp_bicat_finlim_el.
  - apply disp_bicat_finlim_ob_to_adj_equiv.
  - apply to_disp_left_adjoint_equivalence_over_adjequiv_finlim_ob.
Defined.
