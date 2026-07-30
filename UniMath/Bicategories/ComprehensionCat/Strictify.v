(**

 Strictification of DFL comprehension categories with a universe

 In other files, it is shown how one can strictify comprehension categories with a universe.
 That development is based on comprehension categories that are not necessarily full, and
 the way the type formers are defined is similar to the definitions given by Lumsdaine and
 Warren. However, this formulation is different from what is used for DFL comprehension
 categories, since for those we interpret quantifiers as adjoints, which is valid since
 these comprehension categories are full.

 In this file, we translate the strictification construction to DFL comprehension categories
 with a universe. There are essentially two parts to this file. The first part is mostly
 administrative in nature: since the notion of comprehension category is formulated slightly
 differently, infrastructure is necessary to move between these two notions. Note that these
 differences are very minor, as they only involve the terminal object. The second part does
 the same, but for universes in DFL comprehension categories. In the end, we can directly
 instantiate the strictification construction.

 References
 - "The local universes model: An overlooked coherence construction for dependent type
   theories" by Lumsdaine and Warren

 Content
 1. From DFL comprehension categories to comprehension categories
 1.1. The basic construction
 1.2. Operations on terms
 1.3. Type formers
 2. Universes in comprehension categories
 2.1. Construction of the universe
 2.2. The unit is in the universe
 2.3. Closure under ∑-types
 2.4. Closure under ∏-types
 3. Strictification

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require UniMath.CategoryTheory.ComprehensionCats.CompCats.
Require UniMath.CategoryTheory.ComprehensionCats.CompCatTypeFormers.
Require UniMath.CategoryTheory.ComprehensionCats.CompCatUniverse.
Require UniMath.CategoryTheory.ComprehensionCats.CwfFromCompCatWithUniv.
Require Import UniMath.CategoryTheory.CategoriesWithFamilies.CatsWithFams.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.SigmaTypeNotations.
Require Import UniMath.Bicategories.ComprehensionCat.PiTypeNotations.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Constant.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Sigma.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Pi.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. From DFL comprehension categories to comprehension categories *)
(**
   Note: there are two definitions of `comp_cat`:
   1. one is given in `Bicategories.ComprehensionCat.BicatOfCompCat`
   2. one is given in `CategoryTheory.ComprehensionCats.CompCats`
   Here we give a map that go from the first to the second notion
 *)

(** * 1.1. The basic construction *)
Definition comp_cat_to_cat_comp_cat
           (C : comp_cat)
  : CompCats.comp_cat
  := _ ,, pr12 (comp_cat_to_comprehension_cat_structure C).

Definition comp_cat_to_cat_comp_cat_terminal
           (C : comp_cat)
  : CompCatUniverse.comp_cat_with_terminal
  := comp_cat_to_cat_comp_cat C ,, [].

(** * 1.2. Operations on terms *)
Proposition comp_cat_to_cat_comp_cat_coerce
            {C : comp_cat}
            {Γ : C}
            {A B : ty Γ}
            (f : A <: B)
            (t : tm Γ A)
  : CompCats.coerce_comp_cat_tm (C := comp_cat_to_cat_comp_cat C) f t = t ↑ f.
Proof.
  apply idpath.
Qed.

Proposition comp_cat_to_cat_comp_cat_subst
            {C : comp_cat}
            {Γ Δ : C}
            (s : Γ --> Δ)
            {A : ty Δ}
            (t : tm Δ A)
  : CompCats.comp_cat_subst_tm (C := comp_cat_to_cat_comp_cat C) s t = t [[ s ]]tm.
Proof.
  apply idpath.
Qed.

Proposition comp_cat_to_cat_comp_cat_reindex
            {C : comp_cat}
            {Γ Δ : C}
            (s : Γ --> Δ)
            {A B : ty Δ}
            (f : z_iso (C := fiber_category _ _) A B)
  : pr1 (CompCats.comp_cat_reindex_iso (C := comp_cat_to_cat_comp_cat C) s f)
    =
    coerce_subst_ty s (pr1 f).
Proof.
  apply idpath.
Qed.

(** * 1.3. Type formers *)
(**
   In full comprehension categories, type formers are interpreted as adjoints of weakening.
   However, for arbitrary comprehension categories, one uses a different approach, and
   here we collect the facts that show that interpretation of type formers in arbitrary
   comprehension categories generalises the way type formers are interpreted in full
   comprehension categories
 *)
Definition TODO { A : UU } : A.
Admitted.

Definition comp_cat_to_comp_cat_unit
           (C : dfl_full_comp_cat)
  : CompCatTypeFormers.comp_cat_unit (comp_cat_to_cat_comp_cat C).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
  - exact (λ Γ, dfl_full_comp_cat_unit (C := C) Γ).
  - exact (λ Γ, dfl_unit_tt (C := C) Γ).
  - apply TODO.
  - apply TODO.
  - exact (λ Γ t, dfl_unit_unique (C := C) t).
  - exact (λ Γ Δ s, dfl_comp_cat_unit_subst (C := C) s).
  - apply TODO.
  - apply TODO.
Defined.

Definition comp_cat_to_comp_cat_sigma
           (C : dfl_full_comp_cat)
  : CompCatTypeFormers.comp_cat_sigma (comp_cat_to_cat_comp_cat C).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
  - exact (λ Γ A B, dfl_sigma_type (C := C) A B).
  - exact (λ Γ A B, comp_cat_dep_sum_pair (C := C) A B).
  - intros Γ A B.
    exact (comp_cat_dep_sum_pair_comm (C := C) A B).
  - exact (λ Γ A B, comp_cat_dep_sum_pr (C := C) A B).
  - intros Γ A B.
    exact (comp_cat_dep_sum_beta (C := C) A B).
  - intros Γ A B.
    exact (comp_cat_dep_sum_eta (C := C) A B).
  - exact (λ Γ Δ s A B, z_iso_inv (comp_cat_dep_sum_subst (C := C) A B s)).
  - intros Γ Δ s A B.
    exact (comp_cat_dep_sum_pair_subst (C := C) A B s).
Defined.

Definition comp_cat_to_comp_cat_pi
           (C : dfl_full_comp_cat)
           (P : comp_cat_dependent_prod C)
  : CompCatTypeFormers.comp_cat_pi (comp_cat_to_cat_comp_cat C).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
  - exact (λ Γ A B, dep_prod_cc P A B).
  - exact (λ Γ A B t, comp_cat_pi_lam P t).
  - exact (λ Γ A B f, comp_cat_pi_app P f).
  - intros Γ A B f.
    exact (comp_cat_pi_beta P f).
  - intros Γ A B t.
    exact (comp_cat_pi_eta P t).
  - exact (λ Γ Δ s A B, comp_cat_pi_subst P A B s).
  - intros Γ Δ s A B t.
    exact (!(comp_cat_pi_lam_subst P s t)).
Defined.

(** * 2. Universes in comprehension categories *)

(** * 2.1. Construction of the universe *)
Definition dfl_comp_cat_univ_to_comp_cat_universe_data
           (C : dfl_full_comp_cat_with_univ)
  : CompCatUniverse.comp_cat_universe_data (comp_cat_to_cat_comp_cat_terminal C).
Proof.
  simple refine (_ ,, _ ,, _).
  - exact (dfl_full_comp_cat_univ_ob C).
  - exact (λ Γ t, comp_cat_univ_el (dfl_full_comp_cat_el C) t).
  - exact (λ Γ Δ s t, comp_cat_univ_el_stable (dfl_full_comp_cat_el C) s t).
Defined.

Proposition dfl_comp_cat_univ_to_comp_cat_universe_on_eq
            {C : dfl_full_comp_cat_with_univ}
            {Γ : C}
            {t₁ t₂ : tm Γ (dfl_full_comp_cat_univ Γ)}
            (p : t₁ = t₂)
  : CompCatUniverse.el_map (dfl_comp_cat_univ_to_comp_cat_universe_data C) _ p
    =
    comp_cat_el_map_on_eq (dfl_full_comp_cat_el C) p.
Proof.
  induction p.
  apply idpath.
Qed.

Proposition dfl_comp_cat_univ_to_comp_cat_universe_coherent
            (C : dfl_full_comp_cat_with_univ)
  : CompCatUniverse.comp_cat_universe_coherent
      (dfl_comp_cat_univ_to_comp_cat_universe_data C).
Proof.
  split.
  - intros Γ t.
    rewrite dfl_comp_cat_univ_to_comp_cat_universe_on_eq.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      exact (comp_cat_univ_el_stable_id_coh_alt (dfl_full_comp_cat_el C) t).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (z_iso_inv_after_z_iso (id_subst_ty_iso _)).
      }
      exact (id_left _).
    }
    etrans.
    {
      refine (!_).
      apply (comp_cat_el_map_on_concat (dfl_full_comp_cat_el C)).
    }
    apply (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C)).
  - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
    rewrite dfl_comp_cat_univ_to_comp_cat_universe_on_eq.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (comp_cat_univ_el_stable_comp_coh (dfl_full_comp_cat_el C) s₂ s₁ t).
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply (comp_cat_el_map_on_concat (dfl_full_comp_cat_el C)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (comp_cat_to_cat_comp_cat_reindex _ _).
    }
    apply maponpaths.
    refine (!(id_right _) @ _).
    apply maponpaths.
    refine (!_).
    apply (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C)).
Qed.

Definition dfl_comp_cat_univ_to_comp_cat_universe
           (C : dfl_full_comp_cat_with_univ)
  : CompCatUniverse.comp_cat_universe (comp_cat_to_cat_comp_cat_terminal C).
Proof.
  simple refine (_ ,, _).
  - exact (dfl_comp_cat_univ_to_comp_cat_universe_data C).
  - exact (dfl_comp_cat_univ_to_comp_cat_universe_coherent C).
Defined.

Definition dfl_comp_cat_univ_to_comp_cat_with_universe
           (C : dfl_full_comp_cat_with_univ)
  : CompCatUniverse.comp_cat_with_universe
  := _ ,,dfl_comp_cat_univ_to_comp_cat_universe C.

Proposition dfl_comp_cat_univ_to_comp_cat_with_universe_sub_univ_iso
            {C : dfl_full_comp_cat_with_univ}
            {Γ Δ : C}
            (s : Γ --> Δ)
  : CompCats.coe_from_z_iso
      (CompCatUniverse.sub_comp_cat_univ_iso
         (C := comp_cat_to_cat_comp_cat_terminal C)
         (dfl_full_comp_cat_univ_ob C)
         s)
    =
    sub_dfl_comp_cat_univ s.
Proof.
  apply idpath.
Qed.

(** * 2.2. The unit is in the universe *)
Definition dfl_comp_cat_univ_to_comp_cat_universe_closed_unit
           (C : dfl_full_comp_cat_with_univ)
           (un : unit_in_comp_cat_univ C)
  : CompCatUniverse.comp_cat_universe_closed_unit
      (dfl_comp_cat_univ_to_comp_cat_with_universe C)
      (comp_cat_to_comp_cat_unit _).
Proof.
  simple refine (_ ,, _).
  - exact (type_in_comp_cat_univ_code un).
  - exact (type_in_comp_cat_univ_z_iso_fiber un).
Defined.

(** * 2.3. Closure under ∑-types *)
Section ClosedSigma.
  Context (C : dfl_full_comp_cat_with_univ)
          (sig : stable_sigma_in_comp_cat_univ C).

  Definition dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma_form
    : CompCatUniverse.univ_sigma_form
        (dfl_comp_cat_univ_to_comp_cat_with_universe C)
    := λ Γ a b, sigma_in_comp_cat_univ_code sig a b.

  Definition dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma_iso
    : CompCatUniverse.univ_sigma_el_iso
        (dfl_comp_cat_univ_to_comp_cat_with_universe C)
        (comp_cat_to_comp_cat_sigma (pr1 C))
        dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma_form
    := λ Γ a b, sigma_in_comp_cat_univ_z_iso_fiber sig a b.

  Definition dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma_law
    : CompCatUniverse.univ_sigma_subst_law
        (dfl_comp_cat_univ_to_comp_cat_with_universe C)
        dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma_form.
  Proof.
    intros Γ Δ s a b.
    refine (stable_sigma_in_comp_cat_univ_code_stable sig s a b @ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply comp_cat_to_cat_comp_cat_coerce.
    }
    etrans.
    {
      apply maponpaths.
      apply comp_cat_to_cat_comp_cat_subst.
    }
    refine (maponpaths (λ z, _ ↑ z) _).
    exact (dfl_comp_cat_univ_to_comp_cat_with_universe_sub_univ_iso _).
  Qed.

  Definition dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma
    : CompCatUniverse.comp_cat_universe_closed_sigma
        (dfl_comp_cat_univ_to_comp_cat_with_universe C)
        (comp_cat_to_comp_cat_sigma _).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma_form.
    - exact dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma_iso.
    - exact dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma_law.
  Defined.
End ClosedSigma.

(** * 2.4. Closure under ∏-types *)
Section ClosedPi.
  Context (C : dfl_full_comp_cat_with_univ)
          (P : comp_cat_dependent_prod C)
          (pi : stable_pi_in_comp_cat_univ C P).

  Definition dfl_comp_cat_univ_to_comp_cat_universe_closed_pi_form
    : CompCatUniverse.univ_pi_form
        (dfl_comp_cat_univ_to_comp_cat_with_universe C)
    := λ Γ a b, pi_in_comp_cat_univ_code pi a b.

  Definition dfl_comp_cat_univ_to_comp_cat_universe_closed_pi_iso
    : CompCatUniverse.univ_pi_el_iso
        (dfl_comp_cat_univ_to_comp_cat_with_universe C)
        (comp_cat_to_comp_cat_pi (pr1 C) P)
        dfl_comp_cat_univ_to_comp_cat_universe_closed_pi_form
    := λ Γ a b, pi_in_comp_cat_univ_z_iso_fiber pi a b.

  Definition dfl_comp_cat_univ_to_comp_cat_universe_closed_pi_law
    : CompCatUniverse.univ_pi_subst_law
        (dfl_comp_cat_univ_to_comp_cat_with_universe C)
        dfl_comp_cat_univ_to_comp_cat_universe_closed_pi_form.
  Proof.
    intros Γ Δ s a b.
    refine (stable_pi_in_comp_cat_univ_code_stable pi s a b @ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply comp_cat_to_cat_comp_cat_coerce.
    }
    etrans.
    {
      apply maponpaths.
      apply comp_cat_to_cat_comp_cat_subst.
    }
    refine (maponpaths (λ z, _ ↑ z) _).
    exact (dfl_comp_cat_univ_to_comp_cat_with_universe_sub_univ_iso _).
  Qed.

  Definition dfl_comp_cat_univ_to_comp_cat_universe_closed_pi
    : CompCatUniverse.comp_cat_universe_closed_pi
        (dfl_comp_cat_univ_to_comp_cat_with_universe C)
        (comp_cat_to_comp_cat_pi _ P).
  Proof.
    simple refine (_ ,, _ ,, _).
    - exact dfl_comp_cat_univ_to_comp_cat_universe_closed_pi_form.
    - exact dfl_comp_cat_univ_to_comp_cat_universe_closed_pi_iso.
    - exact dfl_comp_cat_univ_to_comp_cat_universe_closed_pi_law.
  Defined.
End ClosedPi.

(** * 3. Strictification *)
Definition strictify_dfl_full_comp_cat_univ
           (C : dfl_full_comp_cat_with_univ)
           (un : unit_in_comp_cat_univ C)
           (sig : stable_sigma_in_comp_cat_univ C)
  : cwf
  := CwfFromCompCatWithUniv.cwf_from_comp_cat_with_u
       _
       (dfl_comp_cat_univ_to_comp_cat_universe_closed_sigma C sig)
       _
       (dfl_comp_cat_univ_to_comp_cat_universe_closed_unit C un).

(**
   We check that the contexts, types, and terms in the strictification are what we expect.
 *)
Section SanityChecks.
  Context (C : dfl_full_comp_cat_with_univ)
          (un : unit_in_comp_cat_univ C)
          (sig : stable_sigma_in_comp_cat_univ C).

  Let CC : cwf := strictify_dfl_full_comp_cat_univ C un sig.

  (** Contexts *)
  Goal (CC : UU) = tm [] (dfl_full_comp_cat_univ (C := C) []).
  Proof.
    apply idpath.
  Qed.

  (** Types *)
  Goal ∏ (Γ : tm [] (dfl_full_comp_cat_univ (C := C) [])),
       (cwf_ty (C := CC) Γ : UU)
       =
       tm ([] & comp_cat_univ_el (dfl_full_comp_cat_el C) Γ) (dfl_full_comp_cat_univ _).
  Proof.
    intro Γ.
    apply idpath.
  Qed.

  (** Terms *)
  Goal ∏ (Γ : tm [] (dfl_full_comp_cat_univ (C := C) []))
         (A : tm ([] & comp_cat_univ_el (dfl_full_comp_cat_el C) Γ)
                 (dfl_full_comp_cat_univ _)),
       (cwf_tm (C := CC) A : UU)
       =
       tm _ (comp_cat_univ_el (dfl_full_comp_cat_el C) A).
  Proof.
    intros Γ A.
    apply idpath.
  Qed.
End SanityChecks.
