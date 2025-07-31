(**

 From comprehension categories with a universe to categories with a universe

 Our goal is to define a pseudofunctor from the bicategory of (DFL, full, univalent)
 comprehension categories with a universe to the bicategory of univalent categories with
 finite limits and a universe. This is one of the necessary ingredients to extend the
 biequivalence between DFL full comprehension categories and categories with finite limits
 to universes. This pseudofunctor is constructed as a displayed pseudofunctor over the
 pseudofunctor that assigned to every comprehension category its category of context.

 This file defines the compositor of the desired pseudofunctor. The construction has been
 split up so that the resulting files are smaller and so that they can be compiled
 concurrently. The compositor is constructed by verifying two axioms.

 Contents
 1. Coherence for the universe
 2. Coherence for the associated types map
                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivActions.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.

Local Open Scope cat.
Local Open Scope comp_cat.

Section Compositor.
  Context {C₁ C₂ C₃ : dfl_full_comp_cat}
          {u₁ : ty ([] : C₁)}
          {u₂ : ty ([] : C₂)}
          {u₃ : ty ([] : C₃)}.

  Let Cu₁ : comp_cat_with_ob := pr11 C₁ ,, u₁.
  Let CCu₁ : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C₁ ,, dfl_full_comp_cat_to_finlim_ob u₁.
  Let Cu₂ : comp_cat_with_ob := pr11 C₂ ,, u₂.
  Let CCu₂ : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C₂ ,, dfl_full_comp_cat_to_finlim_ob u₂.
  Let Cu₃ : comp_cat_with_ob := pr11 C₃ ,, u₃.
  Let CCu₃ : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C₃ ,, dfl_full_comp_cat_to_finlim_ob u₃.

  Context {el₁ : comp_cat_univ_type Cu₁}
          {el₂ : comp_cat_univ_type Cu₂}
          {el₃ : comp_cat_univ_type Cu₃}
          {F : dfl_full_comp_cat_functor C₁ C₂}
          {G : dfl_full_comp_cat_functor C₂ C₃}
          (F_u : z_iso_disp
                   (comp_cat_functor_empty_context_z_iso F)
                   (comp_cat_type_functor F [] u₁)
                   u₂)
          (G_u : z_iso_disp
                   (comp_cat_functor_empty_context_z_iso G)
                   (comp_cat_type_functor G [] u₂)
                   u₃).

  Let Fob : comp_cat_functor_ob Cu₁ Cu₂ := pr11 F ,, F_u.
  Let Gob : comp_cat_functor_ob Cu₂ Cu₃ := pr11 G ,, G_u.

  Context (Fel : comp_cat_functor_preserves_univ_type Fob el₁ el₂)
          (Gel : comp_cat_functor_preserves_univ_type Gob el₂ el₃).

  Let FGob : functor_finlim_ob CCu₁ CCu₃
    := dfl_functor_comp_cat_to_finlim_functor F · dfl_functor_comp_cat_to_finlim_functor G
       ,,
       z_iso_comp
         (functor_on_z_iso G (dfl_full_comp_cat_functor_preserves_ob F F_u))
         (dfl_full_comp_cat_functor_preserves_ob G G_u).

  Let FG_u
    : z_iso_disp
        (comp_cat_functor_empty_context_z_iso (F · G : dfl_full_comp_cat_functor _ _))
        (comp_cat_type_functor (F · G : dfl_full_comp_cat_functor _ _) [] u₁)
        u₃.
  Proof.
    simpl.
    pose (disp_cat_comp_comp_cat_with_ob F_u G_u) as z.
    simpl in z.
    exact z.
  Defined.

  Let FGob' : functor_finlim_ob CCu₁ CCu₃
    := dfl_functor_comp_cat_to_finlim_functor (F · G)
       ,,
       dfl_full_comp_cat_functor_preserves_ob (F · G) FG_u.

  Proposition dfl_functor_comp_cat_to_finlim_univ_compositor_ob
    : pr2 FGob ==>[ dfl_functor_comp_cat_to_finlim_compositor F G ] pr2 FGob'.
  Proof.
    simpl.
    rewrite id_left.
    rewrite comprehension_functor_mor_transportf.
    rewrite functor_comp.
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply comprehension_nat_trans_comm.
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    rewrite !assoc.
    apply maponpaths_2.
    apply idpath.
  Qed.

  Definition dfl_functor_comp_cat_to_finlim_univ_compositor_nat_trans_ob
    : nat_trans_finlim_ob FGob FGob'
    := dfl_functor_comp_cat_to_finlim_compositor F G
       ,,
       dfl_functor_comp_cat_to_finlim_univ_compositor_ob.

  Proposition comprehension_nat_trans_mor_comp_comp_cat_functor
              {Γ : C₁}
              (A : ty Γ)
    : comprehension_nat_trans_mor
        (comp_cat_functor_comprehension
           (F · G : dfl_full_comp_cat_functor _ _))
        A
      =
      #G(comprehension_nat_trans_mor (comp_cat_functor_comprehension F) A)
      · comprehension_nat_trans_mor (comp_cat_functor_comprehension G) _.
  Proof.
    apply idpath.
  Qed.

  Definition TODO {A : UU} : A.
  Admitted.

  Definition dfl_functor_comp_cat_to_finlim_univ_compositor_preserves_el
    : nat_trans_preserves_el
        dfl_functor_comp_cat_to_finlim_univ_compositor_nat_trans_ob
        (comp_functor_preserves_el
           (dfl_full_comp_cat_functor_preserves_el F F_u Fel)
           (dfl_full_comp_cat_functor_preserves_el G G_u Gel))
        (dfl_full_comp_cat_functor_preserves_el
           (F · G)
           _
           (comp_comp_cat_functor_preserves_univ_type Fel Gel)).
  Proof.
    intros Γ t.
    refine (id_left _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (cat_el_map_pb_mor_id
               (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₃ el₃)).
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_el_eq_comp.
    }
    etrans.
    {
      apply maponpaths_2.
      exact (comp_functor_el_map_iso
               (dfl_full_comp_cat_functor_preserves_el F F_u Fel)
               (dfl_full_comp_cat_functor_preserves_el G G_u Gel)
               t).
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply cat_el_map_el_eq_comp.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply dfl_full_comp_cat_functor_preserves_el_map_on_iso.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply dfl_full_comp_cat_functor_preserves_el_map_on_iso.
    }
    etrans.
    {
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply (functor_comp G).
      }
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply (comprehension_nat_trans_comm (comp_cat_functor_comprehension G)).
    }
    refine (!_).
    etrans.
    {
      apply (dfl_full_comp_cat_functor_preserves_el_map_on_iso (F · G)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply comprehension_nat_trans_mor_comp_comp_cat_functor.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (maponpaths
              (λ z, comprehension_nat_trans_mor (comp_cat_functor_comprehension G) _ · z)
              _).
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply dfl_full_comp_cat_cat_el_map_el_eq.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (comprehension_functor_mor_comp (comp_cat_comprehension C₃)).
    }
    etrans.
    {
      refine (!_).
      apply (comprehension_functor_mor_comp (comp_cat_comprehension C₃)).
    }
    rewrite !assoc_disp_var.
    rewrite mor_disp_transportf_prewhisker.
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      do 3 apply maponpaths.
      apply (comp_cat_el_map_on_disp_concat el₃).
    }
    rewrite !mor_disp_transportf_prewhisker.
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply disp_functor_comp.
    }
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      rewrite assoc_disp_var.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        do 2 apply maponpaths.
        apply assoc_disp.
      }
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        apply (comp_cat_functor_preserves_univ_type_el_iso_natural Gob).
      }
      rewrite mor_disp_transportf_postwhisker.
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        do 3 apply maponpaths.
        apply (comp_cat_el_map_on_disp_concat el₃).
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply mor_disp_transportf_postwhisker.
    }
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply mor_disp_transportf_postwhisker.
    }
    rewrite mor_disp_transportf_postwhisker.
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        apply assoc_disp_var.
      }
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        do 2 apply maponpaths.
        apply mor_disp_transportf_postwhisker.
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        do 3 apply maponpaths.
        exact (comp_cat_el_map_on_disp_concat
                 el₃
                 _
                 (dfl_full_comp_cat_functor_preserves_el_map_eq
                    (F · G)
                    FG_u
                    t)).
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      apply (eq_comp_cat_el_map_on_eq el₃).
    }
    apply idpath.
  Qed.
End Compositor.
