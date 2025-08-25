(**

 DFL full comprehension categories with a universe type

 In other files, we defined the universes in comprehension categories and when functors and
 natural transformations preserve universes. We defined this in a unbundled style, and in
 this file we give a bundled definition fo DFL full comprehension categories with a universe
 type. The reason why we add this definition, is for convenience when defining type formers
 in universes. Specifically, when we define type formers in universes, we assume that the
 comprehension category supports enough type formers, and for that we need to assume that it
 is a DFL full comprehension category and that it supports a universe type. We also provide
 accessors that allow us to move between DFL full comprehension categories with a universe
 type and univalent categories with finite limits and a universe.

 Contents
 1. The bicategory of DFL full comprehension categories with a universe type
 2. Accessors for objects
 3. Accessors for morphisms
 4. Accessors for cells
 5. Accessors for the biequivalence

                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.FinLimToCompCatLemmas.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivActions.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivIdent.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivComp.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivCell.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.UnitForUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.CounitForUnivMor.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. The bicategory of DFL full comprehension categories with a universe type *)
Definition bicat_dfl_full_comp_cat_with_univ
  : bicat
  := total_bicat disp_bicat_dfl_full_comp_cat_with_univ.

Proposition is_univalent_2_bicat_dfl_full_comp_cat_with_univ
  : is_univalent_2 bicat_dfl_full_comp_cat_with_univ.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_dfl_full_comp_cat_with_univ.
  - exact is_univalent_2_bicat_of_dfl_full_comp_cat.
Qed.

Proposition is_univalent_2_0_bicat_dfl_full_comp_cat_with_univ
  : is_univalent_2_0 bicat_dfl_full_comp_cat_with_univ.
Proof.
  exact (pr1 (is_univalent_2_bicat_dfl_full_comp_cat_with_univ)).
Qed.

Proposition is_univalent_2_1_bicat_dfl_full_comp_cat_with_univ
  : is_univalent_2_1 bicat_dfl_full_comp_cat_with_univ.
Proof.
  exact (pr2 (is_univalent_2_bicat_dfl_full_comp_cat_with_univ)).
Qed.

(** * 2. Accessors for objects *)
Definition dfl_full_comp_cat_with_univ
  : UU
  := bicat_dfl_full_comp_cat_with_univ.

Definition make_dfl_full_comp_cat_with_univ
           (C : dfl_full_comp_cat)
           (u : ty ([] : C))
           (el : comp_cat_univ_type (pr11 C ,, u))
  : dfl_full_comp_cat_with_univ
  := C ,, u ,, el.

Coercion dfl_full_comp_cat_with_univ_to_comp_cat
         (C : dfl_full_comp_cat_with_univ)
  : comp_cat
  := pr111 C.

Definition dfl_full_comp_cat_univ_ob
           (C : dfl_full_comp_cat_with_univ)
  : ty ([] : C)
  := pr12 C.

Definition dfl_full_comp_cat_ob
           (C : dfl_full_comp_cat_with_univ)
  : comp_cat_with_ob
  := dfl_full_comp_cat_with_univ_to_comp_cat C ,, dfl_full_comp_cat_univ_ob C.

Definition dfl_full_comp_cat_univ
           {C : dfl_full_comp_cat_with_univ}
           (Γ : C)
  : ty Γ
  := comp_cat_univ (Γ : dfl_full_comp_cat_ob C).

Definition dfl_full_comp_cat_univ_tm
           {C : dfl_full_comp_cat_with_univ}
           {Γ : C}
           (t : tm Γ (dfl_full_comp_cat_univ Γ))
  : tm Γ (comp_cat_univ (Γ : dfl_full_comp_cat_ob C))
  := t.

Definition sub_dfl_comp_cat_univ
           {C : dfl_full_comp_cat_with_univ}
           {Γ Δ : C}
           (s : Γ --> Δ)
  : dfl_full_comp_cat_univ Δ [[ s ]] <: dfl_full_comp_cat_univ Γ
  := sub_comp_cat_univ (C := dfl_full_comp_cat_ob C) s.

Definition dfl_full_comp_cat_with_univ_types
           (C : dfl_full_comp_cat_with_univ)
  : dfl_full_comp_cat
  := pr1 C.

Definition dfl_full_comp_cat_el
           (C : dfl_full_comp_cat_with_univ)
  : comp_cat_univ_type (dfl_full_comp_cat_ob C)
  := pr22 C.

Proposition dfl_full_comp_cat_univ_tm_eq
            {C : dfl_full_comp_cat_with_univ}
            {Γ : C}
            {t₁ t₂ : tm Γ (dfl_full_comp_cat_univ Γ)}
            (p : t₁ · PullbackPr1 (comp_cat_pullback _ _)
                 =
                 t₂ · PullbackPr1 (comp_cat_pullback _ _))
  : t₁ = t₂.
Proof.
  use eq_comp_cat_tm.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback _ _))).
  - exact p.
  - exact (comp_cat_tm_eq _ @ !(comp_cat_tm_eq _)).
Qed.

Proposition comp_cat_comp_mor_sub_dfl_comp_cat_univ
            (C : dfl_full_comp_cat_with_univ)
            {Γ Δ : dfl_full_comp_cat_with_univ_types C}
            (s : Γ --> Δ)
  : comp_cat_comp_mor (sub_dfl_comp_cat_univ s)
    · PullbackPr1 (comp_cat_pullback _ _)
    =
    PullbackPr1 (comp_cat_pullback _ _)
    · PullbackPr1 (comp_cat_pullback _ _).
Proof.
  etrans.
  {
    refine (!_).
    apply (comprehension_functor_mor_comp).
  }
  etrans.
  {
    apply maponpaths.
    apply mor_disp_transportf_postwhisker.
  }
  rewrite comprehension_functor_mor_transportf.
  rewrite assoc_disp_var.
  rewrite comprehension_functor_mor_transportf.
  etrans.
  {
    do 2 apply maponpaths.
    apply subst_ty_eq_disp_iso_comm.
  }
  rewrite mor_disp_transportf_prewhisker.
  rewrite comprehension_functor_mor_transportf.
  etrans.
  {
    apply maponpaths.
    apply cartesian_factorisation_commutes.
  }
  unfold transportb.
  rewrite comprehension_functor_mor_transportf.
  apply comprehension_functor_mor_comp.
Qed.

(** * 3. Accessors for morphisms *)
Definition dfl_full_comp_cat_with_univ_functor
           (C₁ C₂ : dfl_full_comp_cat_with_univ)
  : UU
  := C₁ --> C₂.

Definition make_dfl_full_comp_cat_with_univ_functor
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           (F : dfl_full_comp_cat_functor
                  (dfl_full_comp_cat_with_univ_types C₁)
                  (dfl_full_comp_cat_with_univ_types C₂))
           (Fu : z_iso_disp
                   (comp_cat_functor_empty_context_z_iso F)
                   (comp_cat_type_functor F _ (dfl_full_comp_cat_univ_ob C₁))
                   (dfl_full_comp_cat_univ_ob C₂))
           (Fel : comp_cat_functor_preserves_univ_type
                    (C₁ := dfl_full_comp_cat_ob C₁)
                    (C₂ := dfl_full_comp_cat_ob C₂)
                    (pr11 F ,, Fu)
                    (dfl_full_comp_cat_el C₁)
                    (dfl_full_comp_cat_el C₂))
  : dfl_full_comp_cat_with_univ_functor C₁ C₂
  := F ,, Fu ,, Fel.

Coercion dfl_full_comp_cat_with_univ_functor_to_comp_cat_functor
         {C₁ C₂ : dfl_full_comp_cat_with_univ}
         (F : dfl_full_comp_cat_with_univ_functor C₁ C₂)
  : comp_cat_functor C₁ C₂
  := pr111 F.

Definition dfl_full_comp_cat_with_univ_functor_types
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           (F : dfl_full_comp_cat_with_univ_functor C₁ C₂)
  : dfl_full_comp_cat_functor
      (dfl_full_comp_cat_with_univ_types C₁)
      (dfl_full_comp_cat_with_univ_types C₂)
  := pr1 F.

Definition dfl_full_comp_cat_functor_ob
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           (F : dfl_full_comp_cat_with_univ_functor C₁ C₂)
  : comp_cat_functor_ob
      (dfl_full_comp_cat_ob C₁)
      (dfl_full_comp_cat_ob C₂)
  := dfl_full_comp_cat_with_univ_functor_to_comp_cat_functor F ,, pr12 F.

Definition dfl_full_comp_cat_univ_functor_universe
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           (F : dfl_full_comp_cat_with_univ_functor C₁ C₂)
  : comp_cat_functor_preserves_univ_type
      (dfl_full_comp_cat_functor_ob F)
      (dfl_full_comp_cat_el C₁)
      (dfl_full_comp_cat_el C₂)
  := pr22 F.

(** * 4. Accessors for cells *)
Definition dfl_full_comp_cat_with_univ_nat_trans
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           (F G : dfl_full_comp_cat_with_univ_functor C₁ C₂)
  : UU
  := F ==> G.

Definition make_dfl_full_comp_cat_with_univ_nat_trans
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           {F G : dfl_full_comp_cat_with_univ_functor C₁ C₂}
           (τ : comp_cat_nat_trans_ob
                  (dfl_full_comp_cat_functor_ob F)
                  (dfl_full_comp_cat_functor_ob G))
           (τel : comp_cat_nat_trans_preserves_univ_type
                    τ
                    (dfl_full_comp_cat_univ_functor_universe F)
                    (dfl_full_comp_cat_univ_functor_universe G))
  : dfl_full_comp_cat_with_univ_nat_trans F G
  := make_dfl_full_comp_cat_nat_trans (make_full_comp_cat_nat_trans (pr1 τ))
     ,,
     pr2 τ
     ,,
     τel.

Coercion dfl_full_comp_cat_with_univ_nat_trans_to_comp_cat_nat_trans
         {C₁ C₂ : dfl_full_comp_cat_with_univ}
         {F G : dfl_full_comp_cat_with_univ_functor C₁ C₂}
         (τ : dfl_full_comp_cat_with_univ_nat_trans F G)
  : comp_cat_nat_trans F G
  := pr111 τ.

Definition dfl_full_comp_cat_nat_trans_ob
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           {F G : dfl_full_comp_cat_with_univ_functor C₁ C₂}
           (τ : dfl_full_comp_cat_with_univ_nat_trans F G)
  : comp_cat_nat_trans_ob
      (dfl_full_comp_cat_functor_ob F)
      (dfl_full_comp_cat_functor_ob G)
  := dfl_full_comp_cat_with_univ_nat_trans_to_comp_cat_nat_trans τ ,, pr12 τ.

Definition dfl_full_comp_cat_with_univ_nat_trans_universe
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           {F G : dfl_full_comp_cat_with_univ_functor C₁ C₂}
           (τ : dfl_full_comp_cat_with_univ_nat_trans F G)
  : comp_cat_nat_trans_preserves_univ_type
      (dfl_full_comp_cat_nat_trans_ob τ)
      (dfl_full_comp_cat_univ_functor_universe F)
      (dfl_full_comp_cat_univ_functor_universe G)
  := pr22 τ.

(** * 5. Accessors for the biequivalence *)
Definition dfl_full_comp_cat_with_univ_to_univ_cat_finlim_psfunctor
  : psfunctor
      bicat_dfl_full_comp_cat_with_univ
      bicat_of_univ_cat_with_finlim_universe
  := total_psfunctor _ _ _ dfl_comp_cat_to_finlim_disp_psfunctor_universe.


Definition dfl_full_comp_cat_with_univ_to_univ_cat_finlim
           (C : dfl_full_comp_cat_with_univ)
  : univ_cat_with_finlim_universe.
Proof.
  use make_univ_cat_with_finlim_universe.
  - exact (dfl_full_comp_cat_to_finlim (dfl_full_comp_cat_with_univ_types C)).
  - exact (dfl_full_comp_cat_to_finlim_ob (dfl_full_comp_cat_univ_ob C)).
  - exact (dfl_full_comp_cat_to_finlim_stable_el_map_coherent
             (dfl_full_comp_cat_univ_ob C)
             (dfl_full_comp_cat_el C)).
Defined.

Definition dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor
           {C₁ C₂ : dfl_full_comp_cat_with_univ}
           (F : dfl_full_comp_cat_with_univ_functor C₁ C₂)
  : functor_finlim_universe
      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C₁)
      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C₂).
Proof.
  use make_functor_finlim_universe.
  - exact (dfl_functor_comp_cat_to_finlim_functor
             (dfl_full_comp_cat_with_univ_functor_types F)).
  - exact (dfl_full_comp_cat_functor_preserves_ob
             (dfl_full_comp_cat_with_univ_functor_types F)
             (ob_of_functor_comp_cat_ob (dfl_full_comp_cat_functor_ob F))).
  - exact (dfl_full_comp_cat_functor_preserves_el
             (dfl_full_comp_cat_with_univ_functor_types F)
             (ob_of_functor_comp_cat_ob (dfl_full_comp_cat_functor_ob F))
             (dfl_full_comp_cat_univ_functor_universe F)).
Defined.

Definition univ_cat_with_finlim_universe_to_dfl_full_comp_cat
           (C : univ_cat_with_finlim_universe)
  : dfl_full_comp_cat_with_univ.
Proof.
  use make_dfl_full_comp_cat_with_univ.
  - exact (finlim_to_dfl_comp_cat C).
  - exact (finlim_to_comp_cat_universe_ob C).
  - exact (finlim_to_comp_cat_univ_type (univ_cat_cat_stable_el_map C)).
Defined.

Definition univ_cat_with_finlim_universe_to_dfl_full_comp_cat_functor
           {C₁ C₂ : univ_cat_with_finlim_universe}
           (F : functor_finlim_universe C₁ C₂)
  : dfl_full_comp_cat_with_univ_functor
      (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C₁)
      (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C₂).
Proof.
  use make_dfl_full_comp_cat_with_univ_functor.
  - exact (finlim_to_dfl_comp_cat_functor F).
  - exact (ob_of_functor_comp_cat_ob (finlim_to_comp_cat_functor_ob F)).
  - exact (finlim_to_comp_cat_functor_preserves_univ_type
             (functor_finlim_universe_preserves_el F)).
Defined.

Definition univ_cat_with_finlim_universe_to_dfl_full_comp_cat_unit
           (C : univ_cat_with_finlim_universe)
  : functor_finlim_universe
      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim
         (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C))
      C.
Proof.
  use make_functor_finlim_universe.
  - exact (finlim_dfl_comp_cat_unit_mor C).
  - exact (functor_on_universe
             (finlim_dfl_comp_cat_unit_ob (C := C))).
  - exact (finlim_dfl_comp_cat_unit_preserves_el
             (univ_cat_cat_stable_el_map C)).
Defined.

Definition univ_cat_with_finlim_universe_to_dfl_full_comp_cat_counit
           (C : dfl_full_comp_cat_with_univ)
  : dfl_full_comp_cat_with_univ_functor
      C
      (univ_cat_with_finlim_universe_to_dfl_full_comp_cat
         (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)).
Proof.
  use make_dfl_full_comp_cat_with_univ_functor.
  - exact (finlim_dfl_comp_cat_counit_mor
             (dfl_full_comp_cat_with_univ_types C)).
  - exact (finlim_dfl_comp_cat_counit_ob (dfl_full_comp_cat_univ_ob C)).
  - exact (finlim_dfl_comp_cat_counit_preserves_univ_type
             (dfl_full_comp_cat_univ_ob C)
             (dfl_full_comp_cat_el C)).
Defined.

Definition dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor_ident
           (C : dfl_full_comp_cat_with_univ)
  : invertible_2cell
      (identity _)
      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor (identity C))
  := psfunctor_id dfl_full_comp_cat_with_univ_to_univ_cat_finlim_psfunctor C.

Definition dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor_ident_eq
           (C : dfl_full_comp_cat_with_univ)
  : identity _
    =
    dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor (identity C).
Proof.
  use isotoid_2_1.
  {
    exact is_univalent_2_1_bicat_of_univ_cat_with_finlim_universe.
  }
  exact (dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor_ident C).
Defined.

Definition dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor_comp
           {C₁ C₂ C₃ : dfl_full_comp_cat_with_univ}
           (F : dfl_full_comp_cat_with_univ_functor C₁ C₂)
           (G : dfl_full_comp_cat_with_univ_functor C₂ C₃)
  : invertible_2cell
      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor F
       · dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor G)
      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor (F · G))
  := psfunctor_comp dfl_full_comp_cat_with_univ_to_univ_cat_finlim_psfunctor F G.

Definition dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor_comp_eq
           {C₁ C₂ C₃ : dfl_full_comp_cat_with_univ}
           (F : dfl_full_comp_cat_with_univ_functor C₁ C₂)
           (G : dfl_full_comp_cat_with_univ_functor C₂ C₃)
  : dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor F
    · dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor G
    =
    dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor (F · G).
Proof.
  use isotoid_2_1.
  {
    exact is_univalent_2_1_bicat_of_univ_cat_with_finlim_universe.
  }
  exact (dfl_full_comp_cat_with_univ_to_univ_cat_finlim_functor_comp F G).
Defined.

Proposition dfl_full_comp_cat_tm_to_mor_finlim_mor
            {C : univ_cat_with_finlim_universe}
            {Γ : C}
            (t : Γ --> univ_cat_universe C)
  : dfl_full_comp_cat_tm_to_mor_univ
      (dfl_full_comp_cat_univ_ob
         (univ_cat_with_finlim_universe_to_dfl_full_comp_cat C))
      (finlim_mor_to_univ_tm t)
    =
    t.
Proof.
  unfold dfl_full_comp_cat_tm_to_mor_univ, finlim_mor_to_univ_tm.
  simpl.
  apply (PullbackArrow_PullbackPr1
           (comp_cat_pullback (finlim_to_comp_cat_universe_ob C) (TerminalArrow _ Γ))).
Qed.

Proposition finlim_mor_dfl_full_comp_cat_tm_to_mor
            {C : univ_cat_with_finlim_universe}
            {Γ : univ_cat_with_finlim_universe_to_dfl_full_comp_cat C}
            (t : tm Γ (dfl_full_comp_cat_univ Γ))
  : finlim_univ_tm_to_mor
      (dfl_full_comp_cat_univ_tm
         (C := univ_cat_with_finlim_universe_to_dfl_full_comp_cat C)
         t)
    =
    pr1 t · PullbackPr1 _.
Proof.
  apply idpath.
Qed.

Proposition univ_cat_with_finlim_universe_to_dfl_full_comp_cat_mor_to_tm_pr1
            {C : univ_cat_with_finlim_universe}
            (Cu := univ_cat_with_finlim_universe_to_dfl_full_comp_cat C)
            {Γ Δ : finlim_to_comp_cat C}
            (s : Γ --> Δ)
            (t : Δ --> univ_cat_universe C)
  : ((finlim_mor_to_univ_tm (C := C) t) [[ s ]]tm
    ↑ sub_dfl_comp_cat_univ (C := Cu) s : _ --> _) · PullbackPr1 _
    =
    s · t.
Proof.
  etrans.
  {
    apply maponpaths_2.
    apply finlim_to_comp_cat_coerce_eq.
  }
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    exact (finlim_to_comp_cat_sub_comp_cat_univ_eq s).
  }
  etrans.
  {
    rewrite !assoc'.
    apply maponpaths.
    exact (finlim_to_comp_cat_sub_comp_cat_univ_mor_pr1 s).
  }
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    exact (finlim_to_comp_cat_subst_tm_pullback_pr1
             s
             (finlim_mor_to_univ_tm (C := C) t)).
  }
  refine (assoc' _ _ _ @ _).
  apply maponpaths.
  apply finlim_mor_to_univ_tm_pr1.
Qed.

Proposition univ_cat_with_finlim_universe_to_dfl_full_comp_cat_mor_to_tm_pr2
            {C : univ_cat_with_finlim_universe}
            (Cu := univ_cat_with_finlim_universe_to_dfl_full_comp_cat C)
            {Γ Δ : finlim_to_comp_cat C}
            (s : Γ --> Δ)
            (t : tm Δ (dfl_full_comp_cat_univ (C := Cu) Δ))
  : (t [[ s ]]tm ↑ sub_dfl_comp_cat_univ (C := Cu) s : _ --> _) · PullbackPr2 _
    =
    identity _.
Proof.
  exact (comp_cat_tm_eq (t [[ s ]]tm ↑ sub_dfl_comp_cat_univ (C := Cu) s)).
Qed.
