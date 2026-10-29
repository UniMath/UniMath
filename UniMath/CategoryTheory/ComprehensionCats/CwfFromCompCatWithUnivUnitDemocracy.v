(** Theorems about the CwF constructed from a comprehension category with a universe
    closed under Σ- and unit types (and Π-types).
    Let UnivMod(U) be the constructed CwF.  This file is part 1 of 3.
    We show that UnivMod(U) has unit types and is democratic.

    Contents:

    1. Preservation of unit
    2. Democracy
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Core.Setcategories.

Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.

Require Import UniMath.CategoryTheory.ComprehensionCats.CompCats.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatTypeFormers.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatUniverse.
Require Import UniMath.CategoryTheory.ComprehensionCats.CwfFromCompCatWithUniv.
Require Import UniMath.CategoryTheory.CategoriesWithFamilies.CatsWithFams.
Require Import UniMath.CategoryTheory.CategoriesWithFamilies.CatsWithFamsTypeFormersWithSections.

Local Open Scope cat.
Local Open Scope comp_cat.


(** * 1. Preservation of unit *)

Section UnitPreservation.

  Context (C : comp_cat_with_universe)
    (Sigma : comp_cat_sigma C)
    (SigmaU : comp_cat_universe_closed_sigma C Sigma)
    (Unit : comp_cat_unit C)
    (UnitU : comp_cat_universe_closed_unit C Unit).

  Definition cwf_unit_form_from_comp_cat_with_u
    : unit_form (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU).
  Proof.
    intro Γ.
    refine (comp_cat_pb_term_univ _ _).
    apply (comp_cat_unit_code _ _ UnitU).
    exact (π (comp_cat_el Γ)).
  Defined.

  Definition cwf_unit_intro_from_comp_cat_with_u
    :  unit_intro (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)
         cwf_unit_form_from_comp_cat_with_u.
  Proof.
    intro Γ.
    refine (_ ↑ ⌈ comp_cat_el_iso _ _ ⌉).
    refine (comp_cat_unit_tt _ ↑ _ ↑ _).
    refine ( comp_cat_reindex_coercion (π (comp_cat_el Γ)) ( ⌈ comp_cat_unit_el_iso _ _ _⌉⁻¹) ).
    refine (⌈comp_cat_unit_sub_iso _ ⌉⁻¹).
  Defined.

  Definition cwf_unit_unique_from_comp_cat_with_u
    :   unit_unique (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)
          cwf_unit_form_from_comp_cat_with_u
          cwf_unit_intro_from_comp_cat_with_u.
  Proof.
    intros Γ t.
    apply comp_cat_coerce_tm_iso_inv.
    rewrite comp_cat_reindex_coercion_iso_inv_eq.
    apply comp_cat_coerce_tm_iso_inv'.
    apply comp_cat_coerce_tm_iso_inv'.
    apply comp_cat_unit_unique.
  Qed.

  Definition cwf_unit_subst_from_comp_cat_with_u
    :  unit_subst (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU) cwf_unit_form_from_comp_cat_with_u.
  Proof.
    intros Γ Δ s.
    refine (comp_cat_pb_term_univ_comp _ _ _ @ _).
    unfold cwf_unit_form_from_comp_cat_with_u.
    apply maponpaths.
    apply TerminalArrowEq.
  Qed.

  Theorem construction_pres_unit
    : (cwf_unit_structure (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)).
  Proof.
    use make_cwf_unit_structure.
    - exact cwf_unit_form_from_comp_cat_with_u.
    - exact cwf_unit_intro_from_comp_cat_with_u.
    - exact cwf_unit_unique_from_comp_cat_with_u.
    - exact cwf_unit_subst_from_comp_cat_with_u.
  Defined.

End UnitPreservation.


(** * 2. Democracy *)

(* The resulting model is democratic.  *)

Section Democracy.

  Context (CC : comp_cat_with_universe)
    (Sigma : comp_cat_sigma CC)
    (SigmaU : comp_cat_universe_closed_sigma CC Sigma)
    (Unit : comp_cat_unit CC)
    (UnitU : comp_cat_universe_closed_unit CC Unit)
    (C := cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)
    (el_terminal := comp_cat_el (terminal_context Unit UnitU)).

  Definition z_iso_context_from_comp_cat_with_u
    {Γ Δ : context_from_comp_cat_with_u}
    (f : z_iso (C := CC) ([] & comp_cat_el Γ) ([] & comp_cat_el Δ))
    : @z_iso precategory_data_context_from_comp_cat_with_u Γ Δ.
  Proof.
    use make_z_iso.
    - exact (morphism_from_z_iso _ _ f).
    - exact (inv_from_z_iso f).
    - split.
      + exact (z_iso_inv_after_z_iso f).
      + exact (z_iso_after_z_iso_inv f).
  Defined.

  Lemma iscontr_tm_el_unit_reindex
    {Γ : CC} (s : Γ --> ([] : CC))
    : iscontr (comp_cat_tm
                 (comp_cat_el (comp_cat_unit_code_weakened CC Unit UnitU ([] : CC)) [[ s ]])).
  Proof.
    refine (iscontr_tm_of_iso _ (z_iso_inv _)).
    - exact (term_unit_code _ _  UnitU _ ,, unique_term_unit_code _ _ UnitU).
    - refine (z_iso_comp (comp_cat_el_iso s _) _).
      apply idtoiso.
      apply maponpaths.
      apply comp_cat_unit_subst_law.
  Defined.

  Lemma is_z_iso_el_terminal :  is_z_isomorphism (π (comp_cat_el (terminal_context _ UnitU))).
  Proof.
    use make_is_z_isomorphism.
    - exact (term_unit_code _ _ UnitU []).
    - split.
      + unfold terminal_context.
        unfold comp_cat_unit_code_weakened.
        use (subst_eq_from_extend_subst_eq).
        * abstract (rewrite assoc';
                    rewrite id_left;
                    rewrite <- id_right;
                    apply maponpaths;
                    apply (pr2 (term_unit_code _ _ UnitU _))).
        * abstract (refine (proofirrelevance _ (isapropifcontr _) _ _);
                    apply (iscontr_tm_el_unit_reindex ((π _ · _) · π _))).
      + abstract (apply TerminalArrowEq).
  Defined.

  Theorem cwf_from_universe_is_democratic : cwf_democracy_data C.
  Proof.
    intros Γ.
    use tpair.
    - (* a type in the empty context *)
      exact (comp_cat_pb_term_univ Γ
               (π (comp_cat_el (comp_cat_unit_code_weakened CC Unit UnitU [])))).
    - (* the isomorphism *)
      use z_iso_context_from_comp_cat_with_u.
      refine (z_iso_comp _ (comp_cat_comp_iso (z_iso_inv (comp_cat_sigma_el_iso _ _ _ _ _)))).
      refine (z_iso_inv _).
      refine (z_iso_comp (comp_cat_sigma_pair_proj_iso _ _) _).
      refine (z_iso_comp
                (comp_cat_comp_iso (z_iso_comp (comp_cat_el_z_iso_from_eq _)
                                      (z_iso_inv (comp_cat_el_iso (π _) Γ))))
                _).
      + apply comp_cat_tm_eq. apply idpath.
      + apply (comp_cat_ext_subst_z_iso (make_z_iso' (π _) (is_z_iso_el_terminal)) _).
  Defined.

End Democracy.
