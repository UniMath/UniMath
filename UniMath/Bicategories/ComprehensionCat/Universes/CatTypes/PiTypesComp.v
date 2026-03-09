(**

 Composition of functors that preserve codes for ∏-types

 The development on universes in locally Cartesian closed categories is split into two files.
 This is so that the files are shorter. The file (`PiTypes.v`) exports both files.

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodRightAdjoint.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.PiTypesBasics.

Local Open Scope cat.

(**
   This improves the performance in the next section
 *)
Unset Kernel Term Sharing.

Section CompPreservation.
  Context {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
          {HC₁ : is_locally_cartesian_closed
                   (pullbacks_univ_cat_with_finlim C₁)}
          {HC₂ : is_locally_cartesian_closed
                   (pullbacks_univ_cat_with_finlim C₂)}
          {HC₃ : is_locally_cartesian_closed
                   (pullbacks_univ_cat_with_finlim C₃)}
          {Π₁ : cat_univ_stable_codes_pi HC₁}
          {Π₂ : cat_univ_stable_codes_pi HC₂}
          {Π₃ : cat_univ_stable_codes_pi HC₃}
          {F : functor_finlim_universe C₁ C₂}
          {HF : preserves_locally_cartesian_closed
                  (functor_finlim_preserves_pullback F)
                  HC₁
                  HC₂}
          (Fc : functor_preserves_stable_codes_pi Π₁ Π₂ F HF)
          {G : functor_finlim_universe C₂ C₃}
          {HG : preserves_locally_cartesian_closed
                  (functor_finlim_preserves_pullback G)
                  HC₂
                  HC₃}
          (Gc : functor_preserves_stable_codes_pi Π₂ Π₃ G HG).

  Lemma comp_preserves_stable_codes_pi_ty_eq_1
        {Γ : C₁}
        (a : Γ --> univ_cat_universe C₁)
    : #G(#F a · functor_on_universe F) · functor_on_universe G
      =
      #G(#F a) · (#G (functor_on_universe F) · functor_on_universe G).
  Proof.
    rewrite functor_comp.
    rewrite !assoc'.
    apply idpath.
  Qed.

  Proposition comp_preserves_stable_codes_pi_ty
    : functor_preserves_stable_codes_pi_ty Π₁ Π₃ (F · G).
  Proof.
    intros Γ a b ; simpl.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      apply (functor_preserves_stable_codes_pi_on_code Fc).
    }
    etrans.
    {
      apply (functor_preserves_stable_codes_pi_on_code Gc).
    }
    use cat_univ_codes_pi_ty_eq.
    - apply comp_preserves_stable_codes_pi_ty_eq_1.
    - etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        refine (functor_comp _ _ _ @ _).
        apply maponpaths_2.
        apply functor_comp.
      }
      rewrite !assoc.
      do 3 apply maponpaths_2.
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      refine (!(id_left _) @ _).
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      rewrite (cat_el_map_el_eq_inv (univ_cat_cat_stable_el_map C₃)).
      rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
      refine (!_).
      apply cat_el_map_el_eq_id.
  Qed.

  Local Definition comp_preserves_stable_codes_pi_z_iso_help_mor
                   {Γ : C₁}
                   (a : Γ --> univ_cat_universe C₁)
    : functor_on_cod_fib F (cat_el_map_slice (univ_cat_cat_stable_el_map C₁) a)
      -->
      cat_el_map_slice (univ_cat_cat_stable_el_map C₂) (# F a · functor_on_universe F).
  Proof.
    use make_cod_fib_mor.
    - exact (functor_el_map_iso (functor_finlim_universe_preserves_el F) a).
    - abstract
        (simpl ;
         refine (!_) ;
         apply (functor_el_map_comm (functor_finlim_universe_preserves_el F))).
  Defined.

  Let φ {Γ : C₁} (a : Γ --> univ_cat_universe C₁)
    := comp_preserves_stable_codes_pi_z_iso_help_mor a.
  Let FG : functor_finlim_universe _ _ := F · G.

  Lemma comp_preserves_stable_codes_pi_z_iso_eq
        {Γ : C₁}
        (a : Γ --> univ_cat_universe C₁)
        (r₁ : #G(#F a · functor_on_universe F)
              · functor_on_universe G
              =
              #FG a · functor_on_universe FG)
    : functor_el_map_iso (functor_finlim_universe_preserves_el (F · G)) a
      · cat_el_map_el_eq (univ_cat_cat_stable_el_map C₃) (!r₁)
      =
      dom_mor (functor_on_cod_fib_mor G (φ a))
      · functor_el_map_iso
          (functor_finlim_universe_preserves_el G)
          (#F a · functor_on_universe F).
  Proof.
    simpl.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (assoc' _ _ _ @ _).
    refine (_ @ id_right _).
    apply maponpaths.
    refine (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃) _ _ @ _).
    apply (cat_el_map_el_eq_id (univ_cat_cat_stable_el_map C₃)).
  Qed.

  Proposition comp_preserves_stable_codes_pi_z_iso
    : functor_preserves_stable_codes_pi_z_iso
        (F · G)
        (comp_preserves_locally_cartesian_closed HF HG)
        comp_preserves_stable_codes_pi_ty.
  Proof.
    intros Γ a b.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_preserves_locally_cartesian_closed_z_iso.
    }
    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (!(functor_comp G _ _) @ _).
      apply maponpaths.
      apply (functor_preserves_stable_codes_pi_on_z_iso Fc).
    }
    etrans.
    {
      apply maponpaths_2.
      refine (functor_comp G _ _ @ _).
      apply maponpaths_2.
      refine (functor_comp G _ _ @ _).
      apply maponpaths_2.
      apply (functor_comp G).
    }
    do 3 refine (assoc' _ _ _ @ _).
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths_2.
      etrans.
      {
        apply (comp_functor_el_map_on_tm
                 (functor_finlim_universe_preserves_el F)
                 (functor_finlim_universe_preserves_el G)).
      }
      apply assoc'.
    }
    do 3 refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply (preserves_locally_cartesian_closed_natural
               HG
               (φ a)
               (functor_preserves_stable_codes_pi_z_iso_functor_slice a b)).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply (functor_preserves_stable_codes_pi_on_z_iso Gc).
    }
    rewrite !assoc.
    etrans.
    {
      do 4 apply maponpaths_2.
      apply functor_el_map_iso_eq_alt.
    }
    do 4 refine (assoc' _ _ _ @ _).
    do 3 refine (_ @ assoc _ _ _).
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply cat_el_map_el_eq_comp.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply cat_el_map_el_eq_comp.
    }
    assert (#G(#F a · functor_on_universe F)
            · functor_on_universe G
            =
            #FG a
            · functor_on_universe FG)
      as r₁.
    {
      exact (comp_functor_el_map_path F G a).
    }
    assert (inv_from_z_iso
              (functor_el_map_iso
                 (functor_finlim_universe_preserves_el G)
                 (#F a · functor_on_universe F))
            · #G (inv_from_z_iso
                    (functor_el_map_iso
                       (functor_finlim_universe_preserves_el F)
                       a)
                  · #F b
                  · functor_on_universe F)
            · functor_on_universe G
            =
            cat_el_map_el_eq (univ_cat_cat_stable_el_map C₃) r₁
            · (inv_from_z_iso
                 (functor_el_map_iso
                    (functor_finlim_universe_preserves_el FG)
                    a)
            · #FG b
            · functor_on_universe FG))
      as r₂.
    {
      do 2 refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      use z_iso_inv_on_right.
      refine (functor_comp _ _ _ @ _).
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      refine (functor_comp _ _ _ @ _).
      do 2 refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      use z_iso_inv_on_left.
      refine (!_).
      etrans.
      {
        do 2 refine (assoc _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!(functor_comp _ _ _) @ _).
          rewrite z_iso_after_z_iso_inv.
          apply functor_id.
        }
        rewrite id_left.
        apply idpath.
      }
      apply maponpaths.
      apply cat_el_map_el_eq_eq.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!_).
      exact (cat_univ_codes_pi_z_iso_eq' _ r₁ r₂).
    }
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      apply cat_el_map_el_eq_comp.
    }
    do 2 refine (assoc' _ _ _ @ _).
    do 2 refine (_ @ assoc _ _ _).
    use maponpaths_compose.
    {
      apply cat_el_map_el_eq_eq.
    }
    apply maponpaths.
    unfold cat_univ_codes_pi_z_iso_eq_functor.
    unfold functor_preserves_stable_codes_pi_z_iso_functor.
    refine (lccc_exp_functor_on_comp HC₃ _ _ _ _ @ _).
    refine (_ @ !(lccc_exp_functor_on_comp HC₃ _ _ _ _)).
    use lccc_exp_functor_eq.
    - exact (comp_preserves_stable_codes_pi_z_iso_eq a r₁).
    - refine (comp_in_cod_fib _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply comp_in_cod_fib.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (comp_in_cod_fib _ _ @ _).
        apply maponpaths_2.
        apply comp_in_cod_fib.
      }
      rewrite !cod_fiber_functor_on_mor.
      refine (!_).
      etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        do 3 refine (assoc _ _ _ @ _).
        do 3 apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        do 2 refine (assoc _ _ _ @ _).
        do 2 apply maponpaths_2.
        do 2 refine (assoc _ _ _ @ _).
        do 2 apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        do 5 apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        simpl.
        etrans.
        {
          apply maponpaths.
          apply functor_comp.
        }
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply (PullbackArrow_PullbackPr1 (functor_preserves_pullback_on_pullback _ _ _ _)).
      }
      do 2 refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        do 2 refine (assoc _ _ _ @ _).
        do 2 apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        do 2 refine (assoc _ _ _ @ _).
        do 2 apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      do 3 refine (assoc' _ _ _ @ _).
      do 6 refine (_ @ assoc _ _ _).
      apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        apply (functor_comp G).
      }
      do 3 refine (assoc _ _ _ @ _).
      do 5 refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      use z_iso_inv_on_left.
      refine (!_).
      use z_iso_inv_on_left.
      refine (!_).
      etrans.
      {
        do 4 refine (assoc' _ _ _ @ _).
        do 3 apply maponpaths.
        refine (assoc _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths_2.
          apply functor_comp.
        }
        do 2 refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply functor_preserves_el_path.
        }
        do 2 refine (assoc' _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          use cat_el_map_pb_mor_eq.
          abstract
            (apply maponpaths ;
             refine (_ @ assoc' _ _ _) ;
             apply maponpaths_2 ;
             apply (functor_comp G)).
        }
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
      }
      do 5 refine (assoc _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths_2.
        do 3 refine (assoc' _ _ _ @ _).
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply (functor_el_map_iso_eq_alt (functor_finlim_universe_preserves_el G)).
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
        apply maponpaths_2.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
        }
        refine (!_).
        use cat_el_map_pb_mor_eq.
        abstract
          (simpl ;
           apply maponpaths ;
           do 2 refine (_ @ assoc' _ _ _) ;
           apply maponpaths_2 ;
           rewrite !functor_comp ;
           apply idpath).
      }
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (!_).
        use cat_el_map_pb_mor_eq.
        abstract
          (apply maponpaths ;
           apply assoc').
      }
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
      }
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_pb_mor_comp.
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        refine (assoc _ _ _ @ _).
        apply maponpaths.
        apply cat_el_map_pb_mor_comp.
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
      }
      etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!_).
        use cat_el_map_pb_mor_eq.
        abstract
          (apply maponpaths ;
           do 2 refine (assoc' _ _ _ @ _) ;
           apply idpath).
      }
      etrans.
      {
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_pb_mor_comp'.
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
      }
      etrans.
      {
        apply maponpaths.
        use cat_el_map_pb_mor_id'.
        abstract
          (refine (!_) ;
           etrans ;
           [ apply maponpaths ;
             apply cat_el_map_el_eq_inv
           | ] ;
           refine (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃) _ _ @ _) ;
           apply cat_el_map_el_eq_id).
      }
      refine (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃) _ _ @ _).
      apply cat_el_map_el_eq_eq.
  Qed.

  Proposition comp_preserves_stable_codes_pi
    : functor_preserves_stable_codes_pi
        Π₁ Π₃
        (F · G)
        (comp_preserves_locally_cartesian_closed HF HG).
  Proof.
    use make_functor_preserves_stable_codes_pi.
    - exact comp_preserves_stable_codes_pi_ty.
    - exact comp_preserves_stable_codes_pi_z_iso.
  Qed.
End CompPreservation.
