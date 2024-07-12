(**************************************************************************************************

  Scott's original representation theorem

  In 1980, Dana Scott showed that a every λ-theory L arises as the endomorphism theory of λ x, x in
  the category of retracts of L. This file constructs the endomorphism theory, describes its
  operations more explicitly and constructs the isomorphism.

  Contents
  1. The endomorphism theory [E]
  1.1. An explicit description of its operations [E_var] [E_subst] [E_abs] [E_app]
  2. The isomorphism [representation_theorem_iso]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.CategoryOfRetracts.
Require Import UniMath.AlgebraicTheories.Combinators.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.

Require Import Ltac2.Ltac2.

Local Open Scope cat.
Local Open Scope algebraic_theories.
Local Open Scope lambda_calculus.

(** * 1. The endomorphism theory *)

Section EndomorphismTheory.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).
  Context {n : nat}.

  Definition E
    : lambda_theory.
  Proof.
    refine '(endomorphism_lambda_theory _ _ _ _ _ _).
    - exact (R (n := n) L Lβ).
    - exact (R_terminal _ _ (c := abs (var (stnweq (inr tt))))).
    - apply R_binproducts.
    - exact (U L Lβ).
    - apply R_exponentials.
    - apply R_section.
    - apply R_retraction.
  Defined.

  Definition Eβ
    : has_β E.
  Proof.
    apply endomorphism_theory_has_β.
    apply R_retraction_is_retraction.
  Qed.

(** ** 1.1. An explicit description of its operations *)

  Lemma U_compose_n_π
    {m : nat}
    (i : stn m)
    : U (n := n) L Lβ ∘ n_π i = n_π i.
  Proof.
    induction m as [ | m IHm].
    - apply fromempty.
      apply negstn0.
      apply i.
    - unfold n_π.
      unfold nat_rect.
      induction (invmap stnweq i) as [i' | i'];
        apply (U_compose _ Lβ).
  Qed.

  Lemma E_var
    {m : nat}
    (i : stn m)
    : R_mor_to_L _ (var (T := E) i) = n_π (L := L) i.
  Proof.
    refine '(R_power_projection_is_n_π _ _ _ _ @ _).
    apply U_compose_n_π.
  Qed.

  Lemma E_subst
    {l m : nat}
    (f : E l)
    (g : stn l → E m)
    : R_mor_to_L _ (f • g) = (R_mor_to_L _ f) ∘ (n_tuple_arrow (λ i, R_mor_to_L _ (g i))).
  Proof.
    exact (maponpaths _ (R_power_arrow_is_n_tuple_arrow _ _ _ _ _)).
  Qed.

  Lemma E_abs
    {m : nat}
    (f : E (S m))
    : R_mor_to_L _ (abs f) = Combinators.curry (R_mor_to_L _ f).
  Proof.
    refine '(maponpaths
      (λ (x : R _ _ ⟦_, _⟧), R_section L Lβ _ ∘ (R_mor_to_L _ x))
      (φ_adj_from_partial _ _ _ (is_universal_arrow L Lβ _) _ _ f) @ _).
    apply R_mor_is_mor_left.
    exact Lβ.
  Qed.

  Lemma E_app
    {m : nat}
    (f : E m)
    : R_mor_to_L _ (appx f)
    = Combinators.uncurry (R_mor_to_L _ f).
  Proof.
    refine '(ev_compose_pair_arrow _ Lβ _ _ _ _ @ _).
    refine '(maponpaths (λ x, (abs (app _ (app (app (inflate x) _) _)))) (compose_assoc _ Lβ _ _ _) @ _).
    refine '(!maponpaths (λ x, (abs (app _ (app (app (inflate (x ∘ _)) _) _)))) (compose_assoc _ Lβ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app (app (inflate (_ ∘ x ∘ _)) _) _)))) (R_mor_is_mor_right _ Lβ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app (inflate x) _)))))) (compose_assoc _ Lβ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app (inflate (x ∘ _)) _)))))) (R_ob_idempotent _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app (app x _) _)))) (inflate_compose _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app x _)))))) (inflate_compose _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app (app (x ∘ _) _) _)))) (inflate_compose _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app (app (_ ∘ x) _) _)))) (inflate_π1 _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app _ (app (_ ∘ x) _)))))) (inflate_π2 _) @ _).
    refine '(maponpaths (λ x, (abs (app x (app _ (app x (app (x ∘ _) _)))))) (subst_U_term _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ x)))) (app_U _ Lβ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ (app _ (app x _))))) (U_compose _ Lβ _ : _ = π2) @ _).
    refine '(maponpaths (λ x, (abs x)) (app_U _ Lβ _) @ _).
    refine '(maponpaths (λ x, (abs (app (app (((inflate x) ∘ _) ∘ _) _) _))) (exponential_term_is_compose _ Lβ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app (app ((x ∘ _) ∘ _) _) _))) (inflate_abs _ _) @ _).
    refine '(maponpaths (λ x, (abs (app (app (((abs x) ∘ _) ∘ _) _) _))) (subst_compose _ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app (app (((abs (x ∘ _)) ∘ _) ∘ _) _) _))) (subst_compose _ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app (app (((abs (_ ∘ x)) ∘ _) ∘ _) _) _))) (subst_inflate _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app (app (((abs ((x ∘ _) ∘ _)) ∘ _) ∘ _) _) _))) (subst_inflate _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app (app (((abs ((_ ∘ x) ∘ _)) ∘ _) ∘ _) _) _))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app (app (((abs ((_ ∘ x) ∘ _)) ∘ _) ∘ _) _) _))) (extend_tuple_inr _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app (app (((abs ((x ∘ _) ∘ x)) ∘ _) ∘ _) _) _))) (subst_U_term _ _) @ _).
    refine '(maponpaths (λ x, abs (app x _)) (app_compose _ Lβ _ _ _) @ _).
    refine '(maponpaths (λ x, abs (app x _)) (app_compose _ Lβ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app x _))) (beta_equality _ Lβ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app x _))) (subst_compose _ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app (x ∘ _) _))) (subst_compose _ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app ((_ ∘ x) ∘ _) _))) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app ((_ ∘ x) ∘ _) _))) (extend_tuple_inr _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app ((x ∘ _) ∘ x) _))) (subst_U_term _ _) @ _).
    do 2 (refine '(maponpaths (λ x, (abs x)) (app_compose _ Lβ _ _ _) @ _)).
    refine '(maponpaths (λ x, (abs x)) (app_U _ Lβ _) @ _).
    exact (maponpaths (λ x, (abs (app _ x))) (app_U _ Lβ _)).
  Qed.

End EndomorphismTheory.

(** * 2. The isomorphism *)

Section Isomorphism.

  Context (L : lambda_theory).
  Context (Lβ : has_β L).

  Let E
    : lambda_theory
    := E L Lβ (n := 0).

  Definition representation_theorem_iso_mor
    {m : nat}
    : E m → L m
    := λ (s : R_mor _ _ _), app (lift_constant _ s) (n_tuple var).

  Definition representation_theorem_iso_inv_data
    (n : nat)
    (s : L n)
    : L 0
    := abs
      (s • (λ i,
        app
        (n_π i)
        (var (stnweq (inr tt))))).

  Lemma representation_theorem_iso_inv_is_mor
    {n : nat}
    (s : L n)
    : U L Lβ ∘
      representation_theorem_iso_inv_data n s ∘
      R_ob_to_L _ (ProductObject _ _
        (bin_product_power (R L Lβ) (U L Lβ) (R_chosen_terminal L Lβ) (R_binproducts L Lβ) n))
    = representation_theorem_iso_inv_data n s.
  Proof.
    refine '(maponpaths (λ x, (x ∘ _)) (U_compose _ Lβ _) @ _).
    refine '(abs_compose _ Lβ _ _ @ _).
    refine '(maponpaths abs (subst_subst _ _ _ _) @ _).
    apply (maponpaths (λ x, abs (s • x))).
    apply funextfun.
    intro i.
    refine '(subst_app _ _ _ _ @ _).
    refine '(maponpaths (λ x, (app x _)) (subst_n_π _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ x)) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ x)) (extend_tuple_inr _ _ _) @ _).
    refine '(maponpaths (λ x, app _ (app (inflate x) _)) (R_power_object_is_n_tuple_arrow _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ (app x _))) (inflate_n_tuple_arrow _ _) @ _).
    refine '(maponpaths (λ x, (app _ x)) (app_n_tuple_arrow _ Lβ _ _) @ _).
    refine '(n_π_tuple _ Lβ _ _ @ _).
    apply (maponpaths (λ x, app x _)).
    refine '(inflate_compose _ _ _ @ _).
    refine '(maponpaths (λ x, x ∘ _) (subst_U_term _ _) @ _).
    refine '(maponpaths (λ x, _ ∘ x) (inflate_n_π _ _) @ _).
    exact (U_compose_n_π _ Lβ _).
  Qed.

  Definition representation_theorem_iso_inv
    {n : nat}
    (s : L n)
    : E n
    := _ ,, representation_theorem_iso_inv_is_mor s.

  Lemma representation_theorem_iso_inv_after_mor
    {n : nat}
    (s : E n)
    : representation_theorem_iso_inv (representation_theorem_iso_mor s) = s.
  Proof.
    apply R_mor_eq.
    refine '(maponpaths (λ x, (abs x)) (subst_app _ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app x _))) (subst_subst _ _ _ _) @ _).
    refine '(maponpaths (λ x, (abs (app _ x))) (subst_n_tuple _ _ _) @ _).
    refine '(_ @ R_mor_is_mor_right _ Lβ s).
    refine '(_ @ !maponpaths (λ x, _ ∘ x) (R_power_object_is_n_tuple_arrow _ _ _)).
    refine '(_ @ !maponpaths (λ x, _ ∘ n_tuple_arrow x) (funextfun _ _ (λ i, U_compose_n_π _ Lβ _))).
    refine '(_ @ !maponpaths (λ x, abs (app _ (app x _))) (inflate_n_tuple_arrow _ _)).
    refine '(_ @ !maponpaths (λ x, abs (app _ x)) (app_n_tuple_arrow _ Lβ _ _)).
    do 2 (refine '(maponpaths (λ x, abs (app (R_mor_to_L _ s • x) _))
      (iscontr_uniqueness (iscontr_empty_tuple _) _) @ !_)).
    apply (maponpaths (λ x, abs (app (R_mor_to_L _ s • _) (n_tuple x)))).
    apply funextfun.
    intro i.
    refine '(_ @ !maponpaths (λ x, (app x _)) (inflate_n_π _ _)).
    apply var_subst.
  Qed.

  Lemma representation_theorem_iso_mor_after_inv
    {n : nat}
    (s : L n)
    : representation_theorem_iso_mor (representation_theorem_iso_inv s) = s.
  Proof.
    refine '(maponpaths (λ x, (app x _)) (subst_abs _ _ _) @ _).
    refine '(beta_equality _ Lβ _ _ @ _).
    refine '(subst_subst _ (s • _) _ _ @ _).
    refine '(subst_subst _ s _ _ @ _).
    refine '(_ @ subst_var _ s).
    apply maponpaths.
    apply funextfun.
    intro i.
    refine '(subst_app _ _ _ _ @ _).
    refine '(maponpaths (λ x, (app x _)) (subst_n_π _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ x)) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ (x • _))) (extend_tuple_inr _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ x)) (var_subst _ _ _) @ _).
    refine '(maponpaths (λ x, (app _ x)) (extend_tuple_inr _ _ _) @ _).
    apply n_π_tuple.
    exact Lβ.
  Qed.

  Lemma representation_theorem_iso_mor_preserves_var
    (m : nat)
    (i : stn m)
    : representation_theorem_iso_mor (var (T := E) i) = var i.
  Proof.
    refine '(maponpaths (λ x, app (lift_constant _ x) _) (E_var _ _ _) @ _).
    refine '(maponpaths (λ x, (app x _)) (subst_n_π _ _ _) @ _).
    apply n_π_tuple.
    exact Lβ.
  Qed.

  Lemma representation_theorem_iso_mor_preserves_subst
    (m n : nat)
    (f : E m)
    (g : stn m → E n)
    : representation_theorem_iso_mor (f • g)
    = (representation_theorem_iso_mor f) • (λ i, representation_theorem_iso_mor (g i)).
  Proof.
    refine '(maponpaths (λ x, app (lift_constant _ x) _) (E_subst _ _ _ _) @ _).
    refine '(maponpaths (λ x, (app x _)) (subst_compose _ _ _ _) @ _).
    refine '(maponpaths (λ x, (app (_ ∘ x) _)) (subst_n_tuple_arrow _ _ _) @ _).
    refine '(app_compose _ Lβ _ _ _ @ _).
    refine '(maponpaths (λ x, app _ x) (app_n_tuple_arrow _ Lβ _ _) @ _).
    refine '(_ @ !subst_app _ _ _ _).
    refine '(_ @ !maponpaths (λ x, (app x _)) (subst_subst _ _ _ _)).
    refine '(_ @ !maponpaths (λ x, (app _ x)) (subst_n_tuple _ _ _)).
    refine '(_ @ maponpaths (λ x, app (L := L) ((R_mor_to_L _ f) • x) _)
      (!iscontr_uniqueness (iscontr_empty_tuple _) _)).
    apply (maponpaths (λ x, app ((R_mor_to_L _ f) • _) (n_tuple x))).
    apply funextfun.
    intro i.
    exact (!var_subst _ _ _).
  Qed.

  Lemma representation_theorem_iso_mor_preserves_abs
    (n : nat)
    (f : E (S n))
    : representation_theorem_iso_mor (abs f) = abs (representation_theorem_iso_mor f).
  Proof.
    refine '(maponpaths (λ x, app (lift_constant _ x) _) (E_abs _ _ _) @ _).
    refine '(maponpaths (λ x, (app x _)) (subst_curry _ _ _) @ _).
    refine '(app_curry _ Lβ _ _ @ _).
    refine '(maponpaths (λ x, (abs (app x _))) (inflate_subst _ _ _) @ _).
    refine '(maponpaths (λ x, abs (app ((R_mor_to_L _ f) • x) _))
      (iscontr_uniqueness (iscontr_empty_tuple _) _) @ _).
    refine '(maponpaths (λ x, abs (app (R_mor_to_L _ f • _) ⟨x, _⟩)) (inflate_n_tuple _ _) @ _).
    apply (maponpaths (λ x, abs (app (R_mor_to_L _ f • _) ⟨n_tuple x, _⟩))).
    apply funextfun.
    intro i.
    apply inflate_var.
  Qed.

  Lemma representation_theorem_iso_mor_preserves_appx
    (n : nat)
    (f : E n)
    : representation_theorem_iso_mor (appx f) = appx (representation_theorem_iso_mor f).
  Proof.
    refine '(maponpaths (λ x, app (lift_constant _ x) _) (E_app _ _ _) @ _).
    refine '(maponpaths (λ x, (app x _)) (subst_uncurry _ _ _) @ _).
    refine '(app_uncurry_pair _ Lβ _ _ _ @ _).
    refine '(_ @ !appx_to_app _).
    refine '(_ @ !maponpaths (λ x, (app x _)) (inflate_app _ _ _)).
    refine '(_ @ !maponpaths (λ x, (app (app x _) _)) (inflate_subst _ _ _)).
    refine '(_ @ !maponpaths (λ x, app (app (R_mor_to_L _ f • x) _) _)
      (iscontr_uniqueness (iscontr_empty_tuple _) _)).
    refine '(_ @ !maponpaths (λ x, app (app (R_mor_to_L _ f • _) x) _) (inflate_n_tuple _ _)).
    apply (maponpaths (λ x, app (app (R_mor_to_L _ f • _) (n_tuple x)) _)).
    apply funextfun.
    intro i.
    exact (!inflate_var _ _).
  Qed.

  Definition representation_theorem_iso
    : z_iso (C := lambda_theory_cat) E L.
  Proof.
    refine '(make_lambda_theory_z_iso _ _ _ _ _).
    - refine '(make_algebraic_theory_z_iso _ _ _ _ _).
      + intro n.
        refine '(make_z_iso _ _ _).
        * exact representation_theorem_iso_mor.
        * exact representation_theorem_iso_inv.
        * split;
            apply funextfun.
          -- exact representation_theorem_iso_inv_after_mor.
          -- exact representation_theorem_iso_mor_after_inv.
      + exact representation_theorem_iso_mor_preserves_var.
      + exact representation_theorem_iso_mor_preserves_subst.
    - exact representation_theorem_iso_mor_preserves_appx.
    - exact representation_theorem_iso_mor_preserves_abs.
  Defined.

End Isomorphism.
