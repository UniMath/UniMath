(**

 Propositional truncation in comprehension categories

 We defined when a comprehension category is equipped with a universe type, and we constructed
 a biequivalence between the bicategory of univalent DFL full comprehension categories with a
 universe type and the bicategory of univalent categories with finite limits and a universe
 type. Our next goal is to extended this biequivalence to cover universes that are closed under
 certain type formers as well. We consider various type formers, and these are given in various
 files. In this file, we consider codes for the propositional truncation. We use the same ideas
 for each type former, and these are explained in the file `Constant.v`

 Contents
 1. Codes for propositional truncations
 2. Accessors and builders
 3. Stability

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.HPropMono.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionPreservation.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.

Local Open Scope cat.
Local Open Scope comp_cat.

Section TypesInCompCatUniv.
  Context (C : dfl_full_comp_cat_with_univ).

  Let el : comp_cat_univ_type (dfl_full_comp_cat_ob C)
    := dfl_full_comp_cat_el C.

  Section TruncationCode.
    Context (HC : fiberwise_cat_property
                    regular_local_property
                    (dfl_full_comp_cat_with_univ_types C)).

    (** * 1. Codes for propositional truncations *)
    Definition truncation_in_comp_cat_univ
      : UU
      := ∏ (Γ : C)
           (a : tm Γ (dfl_full_comp_cat_univ Γ))
           (A := comp_cat_univ_el el a),
         ∑ (trunc : tm Γ (dfl_full_comp_cat_univ Γ))
           (f : z_iso
                  (Γ & comp_cat_univ_el el trunc)
                  (Γ & regular_local_property_trunc HC A)),
         f · π _ = π _.

    Proposition isaset_truncation_in_comp_cat_univ
      : isaset truncation_in_comp_cat_univ.
    Proof.
      do 2 (use impred_isaset ; intro).
      use isaset_total2.
      - apply isaset_comp_cat_tm.
      - intro.
        use isaset_total2.
        + apply isaset_z_iso.
        + intro.
          apply isasetaprop.
          apply homset_property.
    Qed.

    (** * 2. Accessors and builders *)
    Definition make_truncation_in_comp_cat_univ
               (trunc : ∏ (Γ : C)
                          (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                       tm Γ (dfl_full_comp_cat_univ Γ))
               (f : ∏ (Γ : C)
                      (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                    z_iso
                      (Γ & comp_cat_univ_el el (trunc Γ a))
                      (Γ & regular_local_property_trunc
                             HC
                             (comp_cat_univ_el el a)))
               (p : ∏ (Γ : C)
                      (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                    f Γ a · π _ = π _)
    : truncation_in_comp_cat_univ
    := λ Γ a, trunc Γ a ,, f Γ a ,, p Γ a.

    Definition truncation_in_comp_cat_univ_code
               (trunc : truncation_in_comp_cat_univ)
               {Γ : C}
               (a : tm Γ (dfl_full_comp_cat_univ Γ))
      : tm Γ (dfl_full_comp_cat_univ Γ)
      := pr1 (trunc Γ a).

    Definition truncation_in_comp_cat_univ_z_iso
               (trunc : truncation_in_comp_cat_univ)
               {Γ : C}
               (a : tm Γ (dfl_full_comp_cat_univ Γ))
      : z_iso
          (Γ & comp_cat_univ_el el (truncation_in_comp_cat_univ_code trunc a))
          (Γ & regular_local_property_trunc
                 HC
                 (comp_cat_univ_el el a))
      := pr12 (trunc Γ a).

    Proposition truncation_in_comp_cat_univ_comm
                (trunc : truncation_in_comp_cat_univ)
                {Γ : C}
                (a : tm Γ (dfl_full_comp_cat_univ Γ))
      : truncation_in_comp_cat_univ_z_iso trunc a · π _ = π _.
    Proof.
      exact (pr22 (trunc Γ a)).
    Defined.

    Definition truncation_in_comp_cat_univ_z_iso_fiber
               (trunc : truncation_in_comp_cat_univ)
               {Γ : C}
               (a : tm Γ (dfl_full_comp_cat_univ Γ))
      : z_iso
          (C := fiber_category _ _)
          (comp_cat_univ_el el (truncation_in_comp_cat_univ_code trunc a))
          (regular_local_property_trunc
             HC
             (comp_cat_univ_el el a)).
    Proof.
      use cod_iso_to_type_iso.
      - exact (truncation_in_comp_cat_univ_z_iso trunc a).
      - exact (truncation_in_comp_cat_univ_comm trunc a).
    Defined.

    Proposition trunc_in_comp_cat_univ_eq
                {trunc₁ trunc₂ : truncation_in_comp_cat_univ}
                (p : ∏ (Γ : C)
                       (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                     truncation_in_comp_cat_univ_code trunc₁ a
                     =
                     truncation_in_comp_cat_univ_code trunc₂ a)
      : trunc₁ = trunc₂.
    Proof.
      use funextsec ; intro Γ.
      use funextsec ; intro a.
      use total2_paths_f.
      - exact (p Γ a).
      - use subtypePath.
        {
          intro.
          apply homset_property.
        }
        rewrite pr1_transportf.
        use z_iso_eq.
        etrans.
        {
          apply (pr1_transportf
                   (P := λ (x : tm Γ (dfl_full_comp_cat_univ Γ))
                           (f : Γ & comp_cat_univ_el el x --> _),
                      is_z_isomorphism _)).
        }
        etrans.
        {
          exact (transportf_comp_cat_univ_el el (p Γ a) _).
        }
        use (hprop_ty_to_mono_ty (is_hprop_ty_trunc HC (comp_cat_univ_el el a))).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          exact (truncation_in_comp_cat_univ_comm trunc₁ a).
        }
        rewrite comp_cat_comp_mor_comm.
        refine (!_).
        exact (truncation_in_comp_cat_univ_comm trunc₂ a).
    Qed.

    Proposition truncation_in_comp_cat_univ_code_eq
                (trunc : truncation_in_comp_cat_univ)
                {Γ : C}
                {a₁ a₂ : tm Γ (dfl_full_comp_cat_univ Γ)}
                (p : a₁ = a₂)
      : (truncation_in_comp_cat_univ_code trunc a₁ : _ --> _)
        =
        truncation_in_comp_cat_univ_code trunc a₂.
    Proof.
      induction p.
      apply idpath.
    Qed.

    (** * 3. Stability *)
    Definition trunc_in_comp_cat_univ_is_stable
               (trunc : truncation_in_comp_cat_univ)
      : UU
      := ∏ (Γ Δ : C)
           (s : Γ --> Δ)
           (a : tm Δ (dfl_full_comp_cat_univ Δ)),
         truncation_in_comp_cat_univ_code trunc a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
         =
         truncation_in_comp_cat_univ_code trunc (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s).

    Proposition isaprop_trunc_in_comp_cat_univ_is_stable
                (trunc : truncation_in_comp_cat_univ)
      : isaprop (trunc_in_comp_cat_univ_is_stable trunc).
    Proof.
      do 4 (use impred ; intro).
      apply isaset_comp_cat_tm.
    Qed.

    Definition stable_truncation_in_comp_cat_univ
      : UU
      := ∑ (trunc : truncation_in_comp_cat_univ),
         trunc_in_comp_cat_univ_is_stable trunc.

    Definition make_stable_truncation_in_comp_cat_univ
               (trunc : truncation_in_comp_cat_univ)
               (H : trunc_in_comp_cat_univ_is_stable trunc)
      : stable_truncation_in_comp_cat_univ
      := trunc ,, H.

    Proposition isaset_stable_truncation_in_comp_cat_univ
      : isaset stable_truncation_in_comp_cat_univ.
    Proof.
      use isaset_total2.
      - exact isaset_truncation_in_comp_cat_univ.
      - intro x.
        apply isasetaprop.
        apply isaprop_trunc_in_comp_cat_univ_is_stable.
    Qed.

    Coercion stable_truncation_in_comp_cat_univ_to_codes
             (trunc : stable_truncation_in_comp_cat_univ)
      : truncation_in_comp_cat_univ
      := pr1 trunc.

    Proposition stable_truncation_in_comp_cat_univ_code_stable
                (trunc : stable_truncation_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a : tm Δ (dfl_full_comp_cat_univ Δ))
      : truncation_in_comp_cat_univ_code trunc a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
        =
        truncation_in_comp_cat_univ_code trunc (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s).
    Proof.
      exact (pr2 trunc Γ Δ s a).
    Defined.

    Proposition stable_truncation_in_comp_cat_univ_code_stable_mor
                (trunc : stable_truncation_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a : tm Δ (dfl_full_comp_cat_univ Δ))
      : s
        · truncation_in_comp_cat_univ_code trunc a
        · comprehension_functor_mor
            (comp_cat_comprehension C)
            (cleaving_of_types _ _ _ _ _)
        =
        truncation_in_comp_cat_univ_code trunc
          (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        · PullbackPr1 (comp_cat_pullback _ _).
    Proof.
      pose (maponpaths pr1 (stable_truncation_in_comp_cat_univ_code_stable trunc s a)) as p.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (!p).
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply subst_comp_cat_tm_pr1.
    Qed.

    Proposition stable_truncation_in_comp_cat_univ_eq
                {trunc₁ trunc₂ : stable_truncation_in_comp_cat_univ}
                (p : ∏ (Γ : C)
                       (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                     truncation_in_comp_cat_univ_code trunc₁ a
                     =
                     truncation_in_comp_cat_univ_code trunc₂ a)
      : trunc₁ = trunc₂.
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_trunc_in_comp_cat_univ_is_stable.
      }
      use trunc_in_comp_cat_univ_eq.
      exact p.
    Qed.
  End TruncationCode.
End TypesInCompCatUniv.

Arguments truncation_in_comp_cat_univ_code {C} HC trunc {Γ} a.
Arguments truncation_in_comp_cat_univ_z_iso {C} HC trunc {Γ} a.
Arguments truncation_in_comp_cat_univ_comm {C} HC trunc {Γ} a.
Arguments truncation_in_comp_cat_univ_z_iso_fiber {C} HC trunc {Γ} a.
Arguments stable_truncation_in_comp_cat_univ_code_stable {C} HC trunc {Γ Δ} s a.
