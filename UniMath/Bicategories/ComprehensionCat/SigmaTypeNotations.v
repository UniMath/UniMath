(**

 Notations for ∑-types

 In the file `DFLCompCatNotations` we gave some basic accessors for ∑-types in DFL
 comprehension categories. In this file, we give more accessors for ∑-types. These
 accessors include the stability conditions of pairing and projection. It is worth
 that those statements do not immediately follow from the Beck-Chevalley condition.

 Content
 1. Preliminary definitions
 2. Pairing and projection
 3. Preservation under substitution

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.

Local Open Scope cat.
Local Open Scope comp_cat.

Section SigmaTypes.
  Context {C : dfl_full_comp_cat}.

  (** * 1. Preliminary definitions *)
  Definition dep_sum_functor
             {Γ : C}
             (A : ty Γ)
    : (disp_cat_of_types C)[{Γ & A}] ⟶ (disp_cat_of_types C)[{Γ}]
    := left_adjoint (pr11 (strong_dependent_sum_dfl_full_comp_cat C) Γ A).

  Definition dep_sum_unit_coercion
             {Γ : C}
             (A : ty Γ)
             (B : ty (Γ & A))
    : B <: dfl_sigma_type A B [[ π A ]]
    := dep_sum_unit_cc (pr1 (strong_dependent_sum_dfl_full_comp_cat C)) A B.

  Proposition dep_sum_unit_coercion_natural
             {Γ : C}
             (A : ty Γ)
             {B₁ B₂ : ty (Γ & A)}
             (f : B₁ <: B₂)
    : f · dep_sum_unit_coercion A B₂
      =
      dep_sum_unit_coercion A B₁
      · coerce_subst_ty _ (#(dep_sum_functor A) f).
  Proof.
    exact (nat_trans_ax
             (unit_from_right_adjoint
                (pr11 (strong_dependent_sum_dfl_full_comp_cat C) Γ A))
             _ _
             f).
  Qed.

  Definition dep_sum_counit_coercion
             {Γ : C}
             (A B : ty Γ)
    : dfl_sigma_type A (B [[ π A ]]) <: B
    := dep_sum_counit_cc (pr1 (strong_dependent_sum_dfl_full_comp_cat C)) A B.

  Proposition dep_sum_counit_coercion_natural
              {Γ : C}
              (A : ty Γ)
              {B₁ B₂ : ty Γ}
              (f : B₁ <: B₂)
    : #(dep_sum_functor A) (coerce_subst_ty _ f)
      · dep_sum_counit_coercion A B₂
      =
      dep_sum_counit_coercion A B₁ · f.
  Proof.
    exact (nat_trans_ax
             (counit_from_right_adjoint
                (pr11 (strong_dependent_sum_dfl_full_comp_cat C) Γ A))
             _ _
             f).
  Qed.

  Proposition dep_sum_triangle_1
              {Γ : C}
              (A : ty Γ)
              (B : ty (Γ & A))
    : #(dep_sum_functor A) (dep_sum_unit_coercion A B) · dep_sum_counit_coercion _ _
      =
      identity _.
  Proof.
    exact (triangle_1_statement_from_adjunction
             (right_adjoint_to_adjunction
                (pr11 (strong_dependent_sum_dfl_full_comp_cat C) Γ A))
             B).
  Qed.

  Proposition dep_sum_triangle_2
              {Γ : C}
              (A B : ty Γ)
    : dep_sum_unit_coercion _ _ · coerce_subst_ty _ (dep_sum_counit_coercion A B)
      =
      identity _.
  Proof.
    exact (triangle_2_statement_from_adjunction
             (right_adjoint_to_adjunction
                (pr11 (strong_dependent_sum_dfl_full_comp_cat C) Γ A))
             B).
  Qed.

  (** * 2. Pairing and projection *)
  Definition comp_cat_dep_sum_pair
             {Γ : C}
             (A : ty Γ)
             (B : ty (Γ & A))
    : Γ & A & B --> Γ & dfl_sigma_type A B
    := dfl_sigma_type_strong A B.

  Proposition comp_cat_dep_sum_pair_eq
              {Γ : C}
              (A : ty Γ)
              (B : ty (Γ & A))
    : comp_cat_dep_sum_pair A B
      =
      comp_cat_comp_mor (dep_sum_unit_coercion A B)
      · comp_cat_extend_over _ (π A).
  Proof.
    apply idpath.
  Qed.

  Proposition comp_cat_dep_sum_pair_comm
              {Γ : C}
              (A : ty Γ)
              (B : ty (Γ & A))
    : comp_cat_dep_sum_pair A B · π _ = π _ · π _.
  Proof.
    apply (dependent_sum_map_eq (pr1 (strong_dependent_sum_dfl_full_comp_cat C))).
  Qed.

  Definition comp_cat_dep_sum_pr
             {Γ : C}
             (A : ty Γ)
             (B : ty (Γ & A))
    : Γ & dfl_sigma_type A B --> Γ & A & B
    := inv_from_z_iso (dfl_sigma_type_strong A B).

  Proposition comp_cat_dep_sum_eta
              {Γ : C}
              (A : ty Γ)
              (B : ty (Γ & A))
    : comp_cat_dep_sum_pr A B · comp_cat_dep_sum_pair A B = identity _.
  Proof.
    apply z_iso_after_z_iso_inv.
  Qed.

  Proposition comp_cat_dep_sum_beta
              {Γ : C}
              (A : ty Γ)
              (B : ty (Γ & A))
    : comp_cat_dep_sum_pair A B · comp_cat_dep_sum_pr A B = identity _.
  Proof.
    apply z_iso_inv_after_z_iso.
  Qed.

  (** * 3. Preservation under substitution *)
  Definition comp_cat_dep_sum_subst
             {Γ Δ : C}
             (A : ty Δ)
             (B : ty (Δ & A))
             (s : Γ --> Δ)
    : z_iso
        (C := fiber_category _ _)
        (dfl_sigma_type
           (A [[ s ]])
           (B [[ comp_cat_extend_over _ s ]]))
        ((dfl_sigma_type A B) [[ s ]])
    := _
       ,,
       pr21 (strong_dependent_sum_dfl_full_comp_cat C)
               _ _ _ _ _ _ _
               (isPullback_Pullback (comp_cat_pullback A s))
               B.

  Definition comp_cat_dep_sum_subst_coerce
             {Γ Δ : C}
             (A : ty Δ)
             (B : ty (Δ & A))
             (s : Γ --> Δ)
    : (dfl_sigma_type (A [[ s ]]) (B [[ comp_cat_extend_over _ s ]])
       <:
       dfl_sigma_type A B [[ s ]])
    := pr1 (comp_cat_dep_sum_subst A B s).

  Proposition comp_cat_dep_sum_subst_coerce_eq
              {Γ Δ : C}
              (A : ty Δ)
              (B : ty (Δ & A))
              (s : Γ --> Δ)
    : comp_cat_dep_sum_subst_coerce A B s
      =
      #(dep_sum_functor (A [[ s ]])) (coerce_subst_ty _ (dep_sum_unit_coercion A B))
      · #(dep_sum_functor (A [[ s ]]))
            (comm_nat_z_iso
               (cleaving_of_types C)
               _ _ _ _
               (PullbackSqrCommutes (comp_cat_pullback A s)) _)
      · dep_sum_counit_coercion _ _.
  Proof.
    exact (left_beck_chevalley_nat_trans_ob
             (pr11 (strong_dependent_sum_dfl_full_comp_cat C) _ _)
             (pr11 (strong_dependent_sum_dfl_full_comp_cat C) _ _)
             (comm_nat_z_iso
                (cleaving_of_types C)
                _ _ _ _
                (PullbackSqrCommutes (comp_cat_pullback A s)))
             B).
  Qed.

  Definition comp_cat_dep_sum_subst_coerce_inv
             {Γ Δ : C}
             (A : ty Δ)
             (B : ty (Δ & A))
             (s : Γ --> Δ)
    : (dfl_sigma_type A B [[ s ]]
       <:
       dfl_sigma_type (A [[ s ]]) (B [[ comp_cat_extend_over _ s ]]))
    := inv_from_z_iso (comp_cat_dep_sum_subst A B s).

  Lemma comp_cat_dep_sum_pair_subst_lem
        {Γ Δ : C}
        (A : ty Δ)
        (B : ty (Δ & A))
        (s : Γ --> Δ)
    : dep_sum_unit_coercion (A [[s]]) (B [[comp_cat_extend_over A s]])
      · coerce_subst_ty _ (comp_cat_dep_sum_subst_coerce A B s)
      · comp_subst_ty _ _ _
      · eq_subst_ty_inv _ (comprehension_functor_mor_comm _ _)
      · comp_subst_ty_inv _ _ _
      =
      coerce_subst_ty _ (dep_sum_unit_coercion A B).
  Proof.
    refine (!_).
    use (z_iso_inv_on_left _ _ _ _ (comp_subst_ty_iso _ _ _)).
    refine (!_).
    use (z_iso_inv_on_left _ _ _ _ (eq_subst_ty_iso _ _)).
    rewrite comp_cat_dep_sum_subst_coerce_eq.
    rewrite !comp_coerce_subst_ty.
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      refine (!_).
      apply dep_sum_unit_coercion_natural.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply dep_sum_unit_coercion_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply dep_sum_triangle_2.
    }
    rewrite id_left.
    rewrite comm_nat_z_iso_ob.
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply (z_iso_after_z_iso_inv (comp_subst_ty_iso _ _ _)).
    }
    rewrite id_right.
    simpl.
    do 3 apply maponpaths.
    apply homset_property.
  Qed.

  Lemma comp_cat_dep_sum_pair_subst_lem_unit
        {Γ Δ : C}
        (A : ty Δ)
        (B : ty (Δ & A))
        (s : Γ --> Δ)
    : (comp_cat_subst B (comp_cat_extend_over A s) ;; dep_sum_unit_coercion A B)%mor_disp
      =
      transportf
        _
        (id_left _ @ !(id_right _))
        (coerce_subst_ty _ (dep_sum_unit_coercion A B) ;; comp_cat_subst _ _)%mor_disp.
  Proof.
    cbn.
    rewrite cartesian_factorisation_commutes.
    rewrite transport_f_f.
    refine (!_).
    apply transportf_set.
    apply homset_property.
  Qed.

  Proposition comp_cat_dep_sum_pair_subst
              {Γ Δ : C}
              (A : ty Δ)
              (B : ty (Δ & A))
              (s : Γ --> Δ)
    : comp_cat_dep_sum_pair (A [[ s ]]) (B [[ comp_cat_extend_over _ s ]])
      · comp_cat_comp_mor (comp_cat_dep_sum_subst_coerce A B s)
      · comp_cat_extend_over _ s
      =
      comp_cat_extend_over B (comp_cat_extend_over A s)
      · comp_cat_dep_sum_pair A B.
  Proof.
    rewrite !comp_cat_dep_sum_pair_eq.
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    refine (!(comprehension_functor_mor_comp _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    refine (!(comprehension_functor_mor_comp _ _ _) @ _).
    etrans.
    {
      rewrite assoc_disp.
      rewrite comprehension_functor_mor_transportb.
      rewrite comp_cat_dep_sum_pair_subst_lem_unit.
      rewrite mor_disp_transportf_postwhisker.
      rewrite comprehension_functor_mor_transportf.
      rewrite <- comp_cat_dep_sum_pair_subst_lem.
      cbn -[coerce_subst_ty
              comp_subst_ty comp_subst_ty_inv
              eq_subst_ty_inv
              comp_cat_dep_sum_subst_coerce].
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !comprehension_functor_mor_transportf.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        rewrite !assoc_disp_var.
        apply idpath.
      }
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !comprehension_functor_mor_transportf.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        do 4 apply maponpaths.
        apply cartesian_factorisation_commutes.
      }
      rewrite !assoc_disp_var.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !comprehension_functor_mor_transportf.
      rewrite cartesian_factorisation_commutes.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !comprehension_functor_mor_transportf.
      etrans.
      {
        do 4 apply maponpaths.
        apply subst_ty_eq_disp_iso_inv_comm.
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !comprehension_functor_mor_transportf.
      etrans.
      {
        do 3 apply maponpaths.
        apply cartesian_factorisation_commutes.
      }
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !comprehension_functor_mor_transportf.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite assoc_disp.
        apply idpath.
      }
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !comprehension_functor_mor_transportf.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        apply cartesian_factorisation_commutes.
      }
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !comprehension_functor_mor_transportf.
      apply idpath.
    }
    rewrite !assoc_disp_var.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !comprehension_functor_mor_transportf.
    apply idpath.
  Qed.
End SigmaTypes.
