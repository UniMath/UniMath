(**

 Constructions of codes for propositional resizing in universes

 We have defined what it means for a universe in a category with finite limits and for a
 universe in a comprehension category to support propositional resizing. Our goal is to connect
 these two notions. To do so, we use the biequivalence between categories with finite limits
 and a universe and DFL full comprehension categories with a universe. Specifically, we showed
 that if `C` is a comprehension category with a universe `u`, then its category of contexts also
 has a universe. We construct an equivalence between the type that expresses that the universe
 in `C` supports resizing and the type that expresses that the universe in the category of
 contexts supports resizing.

 Our goal is to show that for every comprehension category `C` with a universe the type of
 resizing codes for `C` is equivalent to the type of resizing codes for the universe in the
 category of contexts. We take a slight detour to prove this: instead, we prove an analogous
 result for every category with finite limits and a universe. From this we can directly
 conclude the desired result.

 Contents
 1. Resizing in the codomain
 2. Resizing codes in the codomain
 3. The equivalence

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.HPropMono.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.FinLimToCompCatLemmas.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Resizing.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Resizing.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCompCatUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

Section ResizingInCatUniv.
  Context {C : univ_cat_with_finlim_universe}
          (resize : cat_univ_stable_codes_resizing C).

  (** * 1. Resizing in the codomain *)
  Definition resizing_in_cat_with_univ_to_comp_cat
    : resizing_in_comp_cat_univ
        (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C).
  Proof.
    use make_resizing_in_comp_cat_univ.
    - intros Γ A HA.
      use finlim_mor_to_univ_tm.
      exact (cat_univ_resize_monic resize (hprop_ty_to_monic HA)).
    - intros Γ A HA.
      refine (z_iso_comp
                _
                (cat_univ_resize_z_iso resize (hprop_ty_to_monic HA))).
      use cat_el_map_el_eq.
      apply finlim_mor_to_univ_tm_to_mor.
    - abstract
        (intros Γ A HA ; simpl ;
         refine (assoc' _ _ _ @ _) ;
         etrans ;
         [ apply maponpaths ;
           exact (cat_univ_resize_z_iso_comm resize _)
         | ] ;
         apply (cat_el_map_mor_eq (univ_cat_cat_stable_el_map C))).
  Defined.

  Proposition is_stable_resizing_in_cat_with_univ_to_comp_cat
    : resizing_in_comp_cat_univ_is_stable
        (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C)
        resizing_in_cat_with_univ_to_comp_cat.
  Proof.
    intros Γ Δ s A HA.
    use eq_comp_cat_tm ; simpl.
    use (MorphismsIntoPullbackEqual
           (isPullback_Pullback
              (comp_cat_pullback
                 (finlim_to_comp_cat_universe_ob C)
                 (TerminalArrow [] Γ)))).
    - rewrite PullbackArrow_PullbackPr1.
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ
                 (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C)
                 _).
      }
      simpl.
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply (PullbackArrow_PullbackPr1 (comp_cat_pullback (dfl_full_comp_cat_univ Δ) s)).
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply (PullbackArrow_PullbackPr1
                 (comp_cat_pullback
                    (finlim_to_comp_cat_universe_ob C)
                    (TerminalArrow [] Δ))).
      }
      refine (cat_univ_resize_monic_stable resize s (hprop_ty_to_monic HA) @ _).
      use cat_univ_resize_monic_eq.
      apply idpath.
    - rewrite PullbackArrow_PullbackPr2.
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply (comp_cat_comp_mor_comm (sub_dfl_comp_cat_univ s)).
      }
      apply (PullbackArrow_PullbackPr2 (comp_cat_pullback (dfl_full_comp_cat_univ Δ) s)).
  Qed.

  Definition stable_resizing_in_cat_with_univ_to_comp_cat
    : stable_resizing_in_comp_cat_univ
        (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C).
  Proof.
    use make_stable_resizing_in_comp_cat_univ.
    - exact resizing_in_cat_with_univ_to_comp_cat.
    - exact is_stable_resizing_in_cat_with_univ_to_comp_cat.
  Defined.
End ResizingInCatUniv.

Section ResizingToCatUniv.
  Context {C : univ_cat_with_finlim_universe}
          (resize : stable_resizing_in_comp_cat_univ
                      (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C)).

  (** * 2. Resizing codes in the codomain *)
  Definition resizing_in_cat_with_univ_from_comp_cat
    : cat_univ_codes_resizing C.
  Proof.
    use make_cat_univ_codes_resizing.
    - intros Γ A m.
      use finlim_univ_tm_to_mor.
      exact (resizing_in_comp_cat_univ_code resize
               _
               (finlim_comp_cat_monic_to_is_hprop_ty m)).
    - intros Γ A m.
      exact (resizing_in_comp_cat_univ_z_iso resize
               _
               (finlim_comp_cat_monic_to_is_hprop_ty m)).
    - abstract
        (intros Γ A m ; simpl ;
         apply (resizing_in_comp_cat_univ_comm resize)).
  Defined.

  Proposition is_stable_resizing_in_cat_with_univ_from_comp_cat
    : is_stable_cat_univ_codes_resizing
        resizing_in_cat_with_univ_from_comp_cat.
  Proof.
    intros Γ Δ A s HA.
    cbn.
    refine (!(finlim_to_comp_cat_stable_el_map_equality _ _) @ _).
    apply maponpaths.
    refine (stable_resizing_in_comp_cat_univ_code_stable resize s _ _ @ _).
    use eq_comp_cat_tm.
    refine (resizing_in_comp_cat_univ_code_on_eq resize _ _ _).
    apply idpath.
  Qed.

  Definition stable_resizing_in_cat_with_univ_from_comp_cat
    : cat_univ_stable_codes_resizing C.
  Proof.
    use make_cat_univ_stable_codes_resizing.
    - exact resizing_in_cat_with_univ_from_comp_cat.
    - exact is_stable_resizing_in_cat_with_univ_from_comp_cat.
  Defined.
End ResizingToCatUniv.

(** * 3. The equivalence *)
Definition stable_resizing_in_cat_with_univ_weq_comp_cat
           (C : univ_cat_with_finlim_universe)
  : stable_resizing_in_comp_cat_univ
      (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C)
    ≃
    cat_univ_stable_codes_resizing C.
Proof.
  use weq_iso.
  - exact stable_resizing_in_cat_with_univ_from_comp_cat.
  - exact stable_resizing_in_cat_with_univ_to_comp_cat.
  - abstract
      (intro resize ;
       use stable_resizing_in_comp_cat_univ_eq ;
       intros Γ A HA ;
       refine (finlim_univ_tm_to_mor_to_tm _ @ _) ;
       use eq_comp_cat_tm ;
       use resizing_in_comp_cat_univ_code_on_eq ;
       apply idpath).
  - abstract
      (intro resize ;
       use cat_univ_stable_codes_resizing_eq ;
       intros Γ A m ;
       refine (finlim_mor_to_univ_tm_to_mor _ @ _) ;
       use cat_univ_resize_monic_eq ;
       apply idpath).
Defined.

Definition stable_resizing_in_comp_cat_univ_eq_weq
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           (p : C₁ = C₂)
  : stable_resizing_in_comp_cat_univ C₁
    ≃
    stable_resizing_in_comp_cat_univ C₂.
Proof.
  induction p.
  exact (idweq _).
Defined.

Definition resizing_in_dfl_full_comp_cat_with_univ_weq_cat_finlim
           (C : dfl_full_comp_cat_with_univ)
  : stable_resizing_in_comp_cat_univ C
    ≃
    cat_univ_stable_codes_resizing
      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C).
Proof.
  refine (stable_resizing_in_cat_with_univ_weq_comp_cat _ ∘ _)%weq.
  use stable_resizing_in_comp_cat_univ_eq_weq.
  exact (univ_cat_with_finlim_universe_to_dfl_full_comp_cat_counit_eq C).
Defined.
