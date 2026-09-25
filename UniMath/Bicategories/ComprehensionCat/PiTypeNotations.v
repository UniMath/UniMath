(**

 Accessors for ∏-types in comprehension categories

 We provide various accessors for ∏-types in comprehension categories. These accessors
 include functoriality (i.e., how ∏-types act on coercions, and the usual type theoretic
 rules (i.e., introduction, elimination, and substitution rules).

 Content
 1. Some preliminary definitions
 2. Functoriality of ∏-types
 3. λ-abstraction and application
 4. Computation rules for ∏-types
 5. Preservation under substitution

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
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.

Local Open Scope cat.
Local Open Scope comp_cat.

Section PiTypes.
  Context {C : dfl_full_comp_cat}
          (P : comp_cat_dependent_prod C).

  (** * 1. Some preliminary definitions *)
  Definition dep_prod_functor
             {Γ : C}
             (A : ty Γ)
    : (disp_cat_of_types C)[{Γ & A}] ⟶ (disp_cat_of_types C)[{Γ}]
    := right_adjoint (pr1 P Γ A).

  Definition dep_prod_unit_coercion
             {Γ : C}
             (A B : ty Γ)
    : B <: dep_prod_cc P A (B [[ π A ]])
    := dep_prod_unit_cc P A B.

  Proposition dep_prod_unit_coercion_natural
             {Γ : C}
             (A : ty Γ)
             {B₁ B₂ : ty Γ}
             (f : B₁ <: B₂)
    : f · dep_prod_unit_coercion A B₂
      =
      dep_prod_unit_coercion A B₁ · #(dep_prod_functor A) (coerce_subst_ty _ f).
  Proof.
    exact (nat_trans_ax (unit_from_left_adjoint (pr1 P Γ A)) _ _ f).
  Qed.

  Definition dep_prod_counit_coercion
             {Γ : C}
             (A : ty Γ)
             (B : ty (Γ & A))
    : dep_prod_cc P A B [[ π A ]] <: B
    := dep_prod_counit_cc P A B.

  Proposition dep_prod_counit_coercion_natural
              {Γ : C}
              (A : ty Γ)
              {B₁ B₂ : ty (Γ & A)}
              (f : B₁ <: B₂)
    : coerce_subst_ty _ (#(dep_prod_functor A) f) · dep_prod_counit_coercion A B₂
      =
      dep_prod_counit_coercion A B₁ · f.
  Proof.
    exact (nat_trans_ax (counit_from_left_adjoint (pr1 P Γ A)) _ _ f).
  Qed.

  Proposition dep_prod_triangle_1
              {Γ : C}
              (A B : ty Γ)
    : coerce_subst_ty _ (dep_prod_unit_coercion A B) · dep_prod_counit_coercion _ _
      =
      identity _.
  Proof.
    exact (triangle_1_statement_from_adjunction
             (left_adjoint_to_adjunction (pr1 P Γ A))
             B).
  Qed.

  Proposition dep_prod_triangle_2
              {Γ : C}
              (A : ty Γ)
              (B : ty (Γ & A))
    : dep_prod_unit_coercion _ _ · #(dep_prod_functor A) (dep_prod_counit_coercion A B)
      =
      identity _.
  Proof.
    exact (triangle_2_statement_from_adjunction
             (left_adjoint_to_adjunction (pr1 P Γ A))
             B).
  Qed.

  (** * 2. Functoriality of ∏-types *)
  Definition comp_cat_pi_coerce_mor
             {Γ : C}
             {A₁ A₂ : ty Γ}
             (f : A₂ <: A₁)
             {B₁ : ty (Γ & A₁)}
             {B₂ : ty (Γ & A₂)}
             (g : B₁ [[ comp_cat_comp_mor f ]] <: B₂)
    : dep_prod_cc P A₁ B₁ [[π A₂]] <: B₂
    := eq_subst_ty _ (!(comp_cat_comp_mor_comm f))
       · comp_subst_ty_inv (comp_cat_comp_mor f) (π A₁) (dep_prod_cc P A₁ B₁)
       · coerce_subst_ty (comp_cat_comp_mor f) (dep_prod_counit_coercion A₁ B₁)
       · g.

  Definition comp_cat_pi_coerce
             {Γ : C}
             {A₁ A₂ : ty Γ}
             (f : A₂ <: A₁)
             {B₁ : ty (Γ & A₁)}
             {B₂ : ty (Γ & A₂)}
             (g : B₁ [[ comp_cat_comp_mor f ]] <: B₂)
    : dep_prod_cc P A₁ B₁ <: dep_prod_cc P A₂ B₂
    := dep_prod_unit_coercion A₂ (dep_prod_cc P A₁ B₁)
       · #(dep_prod_functor A₂) (comp_cat_pi_coerce_mor f g).

  (** * 3. λ-abstraction and application *)
  Definition comp_cat_pi_app
             {Γ : C}
             {A : ty Γ}
             {B : ty (Γ & A)}
             (f : tm Γ (dep_prod_cc P A B))
    : tm (Γ & A) B.
  Proof.
    use dfl_full_comp_cat_mor_to_tm.
    exact (inv_from_z_iso (dfl_comp_cat_unit_subst (π A))
           · coerce_subst_ty (π A) (dfl_full_comp_cat_tm_to_mor f)
           · dep_prod_counit_coercion A B).
  Defined.

  Definition comp_cat_pi_lam
             {Γ : C}
             {A : ty Γ}
             {B : ty (Γ & A)}
             (t : tm (Γ & A) B)
    : tm Γ (dep_prod_cc P A B).
  Proof.
    use dfl_full_comp_cat_mor_to_tm.
    exact (dep_prod_unit_coercion A _
           · #(dep_prod_functor A) (TerminalArrow _ _ · dfl_full_comp_cat_tm_to_mor t)).
  Defined.

  (** * 4. Computation rules for ∏-types *)
  Proposition comp_cat_pi_beta
              {Γ : C}
              {A : ty Γ}
              {B : ty (Γ & A)}
              (t : tm (Γ & A) B)
    : comp_cat_pi_app (comp_cat_pi_lam t) = t.
  Proof.
    refine (_ @ dfl_full_comp_cat_tm_to_mor_to_tm t).
    unfold comp_cat_pi_app.
    apply maponpaths.
    rewrite !assoc'.
    use z_iso_inv_on_right.
    unfold comp_cat_pi_lam.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply dfl_full_comp_cat_mor_to_tm_to_mor.
    }
    rewrite comp_coerce_subst_ty.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply dep_prod_counit_coercion_natural.
    }
    do 2 refine (assoc _ _ _ @ _).
    refine (maponpaths (λ z, z · _) _).
    apply TerminalArrowEq.
  Qed.

  Proposition comp_cat_pi_eta
              {Γ : C}
              {A : ty Γ}
              {B : ty (Γ & A)}
              (t : tm Γ (dep_prod_cc P A B))
    : comp_cat_pi_lam (comp_cat_pi_app t) = t.
  Proof.
    refine (_ @ dfl_full_comp_cat_tm_to_mor_to_tm t).
    unfold comp_cat_pi_lam.
    apply maponpaths.
    unfold comp_cat_pi_app.
    etrans.
    {
      do 3 apply maponpaths.
      apply dfl_full_comp_cat_mor_to_tm_to_mor.
    }
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      exact (z_iso_inv_after_z_iso (dfl_comp_cat_unit_subst (π A))).
    }
    rewrite id_left.
    rewrite functor_comp.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply dep_prod_unit_coercion_natural.
    }
    refine (assoc' _ _ _ @ _ @ id_right _).
    apply maponpaths.
    exact (triangle_2_statement_from_adjunction
             (left_adjoint_to_adjunction (pr1 P Γ A))
             _).
  Qed.

  (** * 5. Preservation under substitution *)
  Definition comp_cat_pi_subst
             {Γ Δ : C}
             (A : ty Δ)
             (B : ty (Δ & A))
             (s : Γ --> Δ)
    : z_iso
        (C := fiber_category _ _)
        ((dep_prod_cc P A B) [[ s ]])
        (dep_prod_cc
           P
           (A [[ s ]])
           (B [[ comp_cat_extend_over _ s ]]))
    := _ ,, pr2 P _ _ _ _ _ _ _ (comp_cat_is_pullback A s) B.

  Definition comp_cat_pi_subst_coerce
             {Γ Δ : C}
             (A : ty Δ)
             (B : ty (Δ & A))
             (s : Γ --> Δ)
    : ((dep_prod_cc P A B) [[ s ]]
       <:
       dep_prod_cc P (A [[ s ]]) (B [[ comp_cat_extend_over _ s ]]))
    := pr1 (comp_cat_pi_subst A B s).

  Proposition comp_cat_pi_subst_coerce_eq
              {Γ Δ : C}
              (A : ty Δ)
              (B : ty (Δ & A))
              (s : Γ --> Δ)
    : comp_cat_pi_subst_coerce A B s
      =
      dep_prod_unit_coercion (A [[ s ]]) _
      · #(dep_prod_functor (A [[ s ]]))
           (comm_nat_z_iso_inv
              (cleaving_of_types C)
              _ _ _ _
              (comprehension_functor_mor_comm _ _) _)
      · #(dep_prod_functor (A [[ s ]])) (coerce_subst_ty _ (dep_prod_counit_coercion _ _)).
  Proof.
    exact (right_beck_chevalley_nat_trans_ob
             (pr1 P Δ A) (pr1 P Γ (A [[ s ]]))
             (comm_nat_z_iso_inv
                (cleaving_of_types C)
                _ _ _ _
                (comprehension_functor_mor_comm _ _))
             B).
  Qed.

  Proposition comp_cat_comm_nat_z_iso_inv_natural
              {Γ Δ : C}
              (s : Γ --> Δ)
              (A : ty Δ)
              {B₁ B₂ : ty Δ}
              (f : B₁ <: B₂)
    : coerce_subst_ty _ (coerce_subst_ty _ f)
      · comm_nat_z_iso_inv
          (cleaving_of_types C)
          _ _ _ _
          (comprehension_functor_mor_comm
             (comp_cat_comprehension C)
             (comp_cat_subst A s))
          B₂
      =
      comm_nat_z_iso_inv
        (cleaving_of_types C)
        _ _ _ _
        (comprehension_functor_mor_comm _ _) B₁
      · coerce_subst_ty _ (coerce_subst_ty _ f).
  Proof.
    exact (nat_trans_ax
             (comm_nat_z_iso_inv
                (cleaving_of_types C)
                _ _ _ _
                (comprehension_functor_mor_comm _ _))
             B₁ B₂
             f).
  Qed.

  Definition comp_cat_pi_subst_coerce_inv
             {Γ Δ : C}
             (A : ty Δ)
             (B : ty (Δ & A))
             (s : Γ --> Δ)
    : (dep_prod_cc P (A [[ s ]]) (B [[ comp_cat_extend_over _ s ]])
       <:
       (dep_prod_cc P A B) [[ s ]])
    := inv_from_z_iso (comp_cat_pi_subst A B s).

  Proposition comp_cat_pi_app_subst
              {Γ Δ : C}
              (s : Γ --> Δ)
              {A : ty Δ}
              {B : ty (Δ & A)}
              (f : tm Δ (dep_prod_cc P A B))
    : comp_cat_pi_app f [[ comp_cat_extend_over _ s ]]tm
      =
      comp_cat_pi_app (f [[ s ]]tm ↑ comp_cat_pi_subst_coerce A B s).
  Proof.
    unfold comp_cat_pi_app.
    rewrite dfl_full_comp_cat_mor_to_tm_subst.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      do 2 apply maponpaths.
      refine (dfl_full_comp_cat_tm_to_mor_coerce _ _ @ _).
      apply maponpaths_2.
      apply dfl_full_comp_cat_tm_to_mor_subst_tm.
    }
    rewrite !assoc'.
    rewrite comp_cat_pi_subst_coerce_eq.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite dep_prod_unit_coercion_natural.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(functor_comp (dep_prod_functor (A [[s]]))) _ _).
      }
      refine (!(functor_comp (dep_prod_functor (A [[s]])) _ _) @ _).
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply comp_cat_comm_nat_z_iso_inv_natural.
      }
      rewrite !assoc'.
      apply maponpaths.
      exact (!(comp_coerce_subst_ty _ _ _)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply comp_coerce_subst_ty.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        rewrite !functor_comp.
        rewrite !assoc.
        apply comp_coerce_subst_ty.
      }
      rewrite !assoc'.
      rewrite dep_prod_counit_coercion_natural.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite comp_coerce_subst_ty.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply dep_prod_counit_coercion_natural.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite comp_coerce_subst_ty.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply dep_prod_triangle_1.
      }
      apply id_right.
    }
    use z_iso_inv_on_right.
    refine (!(id_right _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!(id_coerce_subst_ty _ _) @ _).
      apply maponpaths.
      exact (!(z_iso_inv_after_z_iso (dfl_comp_cat_unit_subst (π A)))).
    }
    rewrite comp_coerce_subst_ty.
    rewrite !assoc.
    apply maponpaths_2.
    use z_iso_inv_on_left.
    apply TerminalArrowEq.
  Qed.

  Proposition comp_cat_pi_lam_subst_help
              {Γ Δ : C}
              (s : Γ --> Δ)
              {A : ty Δ}
              {B : ty (Δ & A)}
              (t : tm (Δ & A) B)
    : comp_cat_pi_lam t [[ s ]]tm ↑ comp_cat_pi_subst_coerce A B s
      =
      comp_cat_pi_lam (t [[ comp_cat_extend_over _ s ]]tm).
  Proof.
    unfold comp_cat_pi_lam.
    rewrite dfl_full_comp_cat_mor_to_tm_subst.
    rewrite dfl_full_comp_cat_mor_to_tm_coerce.
    apply maponpaths.
    rewrite !assoc'.
    use z_iso_inv_on_right.
    rewrite comp_coerce_subst_ty.
    rewrite comp_cat_pi_subst_coerce_eq.
    rewrite !assoc.
    rewrite !dep_prod_unit_coercion_natural.
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ functor_comp _ _ _).
    etrans.
    {
      apply maponpaths.
      exact (!(functor_comp _ _ _)).
    }
    refine (!(functor_comp _ _ _) @ _).
    apply maponpaths.
    rewrite !assoc.
    rewrite <- comp_coerce_subst_ty.
    etrans.
    {
      apply maponpaths_2.
      apply comp_cat_comm_nat_z_iso_inv_natural.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!(comp_coerce_subst_ty _ _ _) @ _).
      apply maponpaths.
      rewrite comp_coerce_subst_ty.
      rewrite !assoc'.
      apply maponpaths.
      apply dep_prod_counit_coercion_natural.
    }
    rewrite !assoc.
    rewrite comp_coerce_subst_ty.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths.
      apply dfl_full_comp_cat_tm_to_mor_coerce_subst_ty.
    }
    rewrite !assoc.
    apply maponpaths_2.
    apply TerminalArrowEq.
  Qed.

  Proposition comp_cat_pi_lam_subst
              {Γ Δ : C}
              (s : Γ --> Δ)
              {A : ty Δ}
              {B : ty (Δ & A)}
              (t : tm (Δ & A) B)
    : comp_cat_pi_lam t [[ s ]]tm
      =
      comp_cat_pi_lam (t [[ comp_cat_extend_over _ s ]]tm)
      ↑
      comp_cat_pi_subst_coerce_inv A B s.
  Proof.
    rewrite <- comp_cat_pi_lam_subst_help.
    rewrite comp_coerce_comp_cat_tm.
    refine (!(id_coerce_comp_cat_tm _) @ _).
    apply maponpaths_2.
    refine (!_).
    exact (z_iso_inv_after_z_iso (comp_cat_pi_subst A B s)).
  Qed.
End PiTypes.
