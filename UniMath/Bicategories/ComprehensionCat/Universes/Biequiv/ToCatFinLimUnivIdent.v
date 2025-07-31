(**

 From comprehension categories with a universe to categories with a universe

 Our goal is to define a pseudofunctor from the bicategory of (DFL, full, univalent)
 comprehension categories with a universe to the bicategory of univalent categories with
 finite limits and a universe. This is one of the necessary ingredients to extend the
 biequivalence between DFL full comprehension categories and categories with finite limits
 to universes. This pseudofunctor is constructed as a displayed pseudofunctor over the
 pseudofunctor that assigned to every comprehension category its category of context.

 This file defines the identitor of the desired pseudofunctor. The construction has been
 split up so that the resulting files are smaller and so that they can be compiled
 concurrently. The identitor is constructed by verifying two axioms. There are several
 points in this file where trickery is used to guarantee acceptable compilation times.
 These points are highlighted and explained.

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

Section Identitor.
  Context {C : dfl_full_comp_cat}
          (u : ty ([] : C)).

  Let Cu : comp_cat_with_ob := pr11 C ,, u.
  Let CCu : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C ,, dfl_full_comp_cat_to_finlim_ob u.

  Context (el : comp_cat_univ_type Cu).

  (** * 1. Coherence for the universe *)
  Proposition dfl_functor_comp_cat_to_finlim_univ_identitor_ob
              (p : identity _ = comp_cat_functor_empty_context_z_iso (identity _))
    : identity _
      · (comprehension_nat_trans_mor (id_comprehension_nat_trans _) u
      · comprehension_functor_mor
          (comp_cat_comprehension C)
          (transportf
             (λ z, _ -->[ z ] _)
             p
             (id_disp _)))
      =
      identity _.
  Proof.
    rewrite id_left.
    rewrite comprehension_functor_mor_transportf.
    refine (id_left _ @ _).
    apply comprehension_functor_mor_id.
  Qed.

  Let F_id_u : functor_finlim_ob CCu CCu
    := dfl_functor_comp_cat_to_finlim_functor (identity C)
       ,,
       dfl_full_comp_cat_functor_preserves_ob
         (identity C)
         (id_disp (D := disp_bicat_comp_cat_with_ob) u).

  Let id_u : nat_trans_finlim_ob (identity _) F_id_u
    := dfl_functor_comp_cat_to_finlim_identitor C
       ,,
       dfl_functor_comp_cat_to_finlim_univ_identitor_ob _.

  (** * 2. Coherence for the associated types map *)

  (**
     The final coherence that we have to prove, is given in the following statement. This
     statement is factored out as a separate lemma due to compilation time (most likely
     caused by unification). If `cbn` or `simpl` would have been used in the statement
     [dfl_functor_comp_cat_to_finlim_univ_identitor_preserves_el], then the final `Qed`
     would take too much time. By writing out the full statement explicitly, neither `simpl`
     nor `cbn` is needed, and this reduces compilation time.
   *)
  Proposition dfl_functor_comp_cat_to_finlim_univ_identitor_preserves_el_lem
              {Γ : CCu}
              (t : Γ --> univ_cat_universe CCu)
              p
    : comprehension_functor_mor
        (comp_cat_comprehension C)
        (id_comp_cat_functor_preserves_el el Γ (dfl_full_comp_cat_mor_to_tm u t)
         · comp_cat_el_map_on_eq_iso
             el
             (dfl_full_comp_cat_functor_preserves_el_map_eq
                (identity _)
                (id_disp (D := disp_bicat_comp_cat_with_ob)
                   u)
                t))
      =
      functor_el_map_iso
        (id_functor_preserves_el (dfl_full_comp_cat_to_finlim_stable_el_map u el))
        t
      · cat_el_map_el_eq (dfl_full_comp_cat_to_finlim_el_map _ _) p
      · cat_el_map_pb_mor
          (dfl_full_comp_cat_to_finlim_stable_el_map u el)
          (id₁ Γ)
          (t
           · (comprehension_nat_trans_mor (id_disp (pr211 C)) u
           · comprehension_functor_mor
           (comp_cat_comprehension C)
           _)).
  Proof.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (cat_el_map_el_eq_comp (@dfl_full_comp_cat_to_finlim_el_map C u el)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply dfl_full_comp_cat_cat_el_map_el_eq.
    }
    etrans.
    {
      apply maponpaths.
      apply comprehension_functor_mor_transportf.
    }
    etrans.
    {
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    etrans.
    {
      rewrite !assoc_disp.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        apply (comp_cat_el_map_on_disp_concat el).
      }
      rewrite !mor_disp_transportf_postwhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply (comp_cat_univ_el_stable_id_coh_inv el).
        }
        apply mor_disp_transportf_prewhisker.
      }
      rewrite mor_disp_transportf_postwhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      rewrite !assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        do 3 apply maponpaths.
        apply cartesian_factorisation_commutes.
      }
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      rewrite id_right_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      cbn.
      exact (comp_cat_el_map_on_disp_concat_comp_functor el _ _).
    }
    refine (!_).
    etrans.
    {
      refine (_ @ comp_cat_el_map_on_disp_concat_comp_functor
                    el
                    (id_comp_cat_functor_preserves_el_lem
                       el
                       (dfl_full_comp_cat_mor_to_tm u t))
                    (dfl_full_comp_cat_functor_preserves_el_map_eq
                       (id₁ C)
                       (id_disp (D := disp_bicat_comp_cat_with_ob) u)
                       t)).
      (**
         In order for `apply idpath` to run in acceptable time, it is needed to
         do `cbn` before it.
       *)
      cbn.
      apply idpath.
    }
    apply (maponpaths (comprehension_functor_mor (comp_cat_comprehension C))).
    apply (eq_comp_cat_el_map_on_eq el).
  Qed.

  Proposition dfl_functor_comp_cat_to_finlim_univ_identitor_preserves_el
    : nat_trans_preserves_el
        id_u
        (id_functor_preserves_el _)
        (dfl_full_comp_cat_functor_preserves_el
           (identity _)
           _
           (id_comp_cat_functor_preserves_univ_type el)).
  Proof.
    intros Γ t.
    do 2 refine (id_left _ @ _).
    refine (dfl_functor_comp_cat_to_finlim_univ_identitor_preserves_el_lem t _ @ _).
    refine (maponpaths
              (λ z,
               z · cat_el_map_pb_mor (dfl_full_comp_cat_to_finlim_stable_el_map u el) _ _)
              _).
    apply idpath.
  Qed.
End Identitor.
