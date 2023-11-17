 (**************************************************************************************************

  Scott's representation theorem

  A proof of the representation theorem for the λ-calculus, first proven by Dana Scott in 1980.
  It shows that any model for the λ-calculus can be viewed as the set of endomorphisms of some
  (reflexive) object in some category.

  Contents
  1. A proof that the object (theory_presheaf) can be exponentiated [theory_presheaf_exponentiable]
  2. A construction of the lambda endomorphism theory of theory_presheaf [presheaf_lambda_theory]
  3. An isomorphism between the two λ-theories [presheaf_lambda_theory_iso]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms2.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.Examples.Plus1Presheaf.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.PresheafCategory.
Require Import UniMath.AlgebraicTheories.PresheafMorphisms.
Require Import UniMath.AlgebraicTheories.Presheaves.
Require Import UniMath.Combinatorics.Tuples.

Local Open Scope algebraic_theories.
Local Open Scope cat.
Local Open Scope mor_disp.

(** * 1. A proof that the object (theory_presheaf) can be exponentiated *)

Section RepresentationTheorem.

  Context (L : lambda_theory).

  Let pow
    (n : nat)
    : Product (stn n) (presheaf_cat L) (λ _, theory_presheaf L)
    := bin_product_power (presheaf_cat L) (theory_presheaf L) (terminal_presheaf_cat _) (bin_products_presheaf_cat _) n.

  Let PO
    (n : nat)
    : presheaf L
    := ProductObject _ _ (pow n).

  Let pow'
    (n : nat)
    : Product (stn n) (presheaf_cat L) (λ _, theory_presheaf L)
    := products_presheaf_cat L (stn n) (λ _, (theory_presheaf L)).

  Let PO'
    (n : nat)
    : presheaf L
    := ProductObject _ _ (pow' n).

  Let pow_iso
    (n : nat)
    : z_iso (pow n) (pow' n)
    := z_iso_between_Product (pow n) (pow' n).

  Let pow_f
    (n : nat)
    : presheaf_morphism (PO n) (PO' n)
    := morphism_from_z_iso _ _ (pow_iso n).

  Let pow_f_inv
    (n : nat)
    : presheaf_morphism (PO' n) (PO n)
    := inv_from_z_iso (pow_iso n).

  Local Definition BPO
    (P P' : presheaf L)
    : presheaf L
    := BinProductObject _ (bin_products_presheaf_cat _ P P').

  Section Exponentiable.

    Definition presheaf_exponent_morphism_data
      (P : presheaf L)
      (n : nat)
      (t : (BPO (theory_presheaf L) (plus_1_presheaf P) n : hSet))
      : (P n : hSet).
    Proof.
      refine (action (P := P) (pr2 t) _).
      intro i.
      induction (invmap stnweq i) as [i' | i'].
      - exact (pr i').
      - exact (pr1 t).
    Defined.

    Lemma presheaf_exponent_is_morphism
      (P : presheaf L)
      (m n : nat)
      (a : (BPO (theory_presheaf L) (plus_1_presheaf P) m : hSet))
      (f : stn m → pr1 L n : hSet)
      : presheaf_exponent_morphism_data P n (action a f)
      = action (presheaf_exponent_morphism_data P m a) f.
    Proof.
      do 2 refine (presheaf_is_assoc _ _ _ _ _ _ _ @ !_).
      apply (maponpaths (action (pr2 a : (P _ : hSet)))).
      apply funextfun.
      intro i.
      induction (invmap stnweq i) as [i' | i'].
      - refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ !_).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (!algebraic_theory_comp_identity_projections _ _ _ @ !_).
        apply maponpaths.
        apply funextfun.
        intro j.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

    Definition presheaf_exponent_morphism
      (P : presheaf L)
      : presheaf_morphism (BPO (theory_presheaf L) (plus_1_presheaf P)) P
      := make_presheaf_morphism' _ (presheaf_exponent_is_morphism P).

    Definition presheaf_exponent_induced_morphism_data
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      (n : nat)
      (t : (P' n : hSet))
      : plus_1_presheaf P n : hSet.
    Proof.
      refine (F (1 + n) _).
      split.
      - exact (pr (stnweq (inr tt))).
      - apply (action t).
        intro i.
        exact (pr (stnweq (inl i))).
    Defined.

    Lemma presheaf_exponent_induced_is_morphism
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      (m n : finite_set_skeleton_category)
      (a : P' m : hSet)
      (f : (⟦ m ⟧)%stn → L n : hSet)
      : presheaf_exponent_induced_morphism_data F n (action a f)
      = action (presheaf_exponent_induced_morphism_data F m a) f.
    Proof.
      refine (!_ @ presheaf_morphism_commutes_with_action F _ _).
      apply (maponpaths (F (1 + n))).
      apply pathsdirprod.
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
      - do 2 refine (presheaf_is_assoc _ _ _ _ _ _ _ @ !_).
        apply maponpaths.
        apply funextfun.
        intro i.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

    Definition presheaf_exponent_induced_morphism
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      : presheaf_morphism P' (plus_1_presheaf P)
      := make_presheaf_morphism' _ (presheaf_exponent_induced_is_morphism F).

    Lemma presheaf_exponent_induced_morphism_commutes
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      : F
      = # (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L))
        (presheaf_exponent_induced_morphism F : presheaf_cat L⟦P', plus_1_presheaf P⟧)
        · presheaf_exponent_morphism P.
    Proof.
      apply (presheaf_morphism_eq F _).
      intro n.
      refine (!(presheaf_mor_comp (P := BPO _ _) _ _ _ @ _)).
      apply funextfun.
      intro t.
      refine (maponpaths
        (λ x, action (P := P) (x t) _)
        (presheaf_mor_comp (P := BPO _ _) (P'' := plus_1_presheaf P) _ _ _)
      @ _).
      refine (!presheaf_morphism_commutes_with_action F _ _ @ _).
      apply maponpaths.
      apply pathsdirprod.
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq stnweq _) @ _).
        exact (maponpaths
          (λ x, pr11 x n t)
          (id_right (BinProductPr1 _ ((bin_products_presheaf_cat _) _ _)))
        ).
      - refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
        refine (_ @ presheaf_identity_projections _ _ _).
        apply maponpaths.
        apply funextfun.
        intro i.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

    Lemma presheaf_exponent_induced_morphism_unique
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      (F' : ∑ (f' : presheaf_morphism P' (plus_1_presheaf P)),
        F
        = # (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L))
        (f' : presheaf_cat L ⟦P', plus_1_presheaf P⟧)
        · presheaf_exponent_morphism P
      )
      : F'
      = presheaf_exponent_induced_morphism F,, presheaf_exponent_induced_morphism_commutes F.
    Proof.
      apply subtypePairEquality.
      {
        intro.
        apply (homset_property (presheaf_cat L)).
      }
      apply (presheaf_morphism_eq (pr1 F') _).
      intro n.
      apply funextfun.
      intro t.
      refine (_ @ maponpaths (λ x, pr11 x _ _) (!pr2 F')).
      refine (!(maponpaths (λ x, x _) (presheaf_mor_comp (P := BPO _ _) _ _ _) @ _)).
      refine (maponpaths
        (λ x, action (x _ : P _ : hSet) _)
        (presheaf_mor_comp _ (pr1 F' : presheaf_cat L ⟦P', plus_1_presheaf P⟧) _)
      @ _).
      refine (maponpaths
        (λ x, (pr12 P) _ _ (x : P _ : hSet) _)
        (presheaf_morphism_commutes_with_action (pr1 F') _ _)
      @ _).
      refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
      refine (_ @ presheaf_identity_projections _ _ _).
      apply maponpaths.
      apply funextfun.
      intro i.
      refine (_ @ maponpaths pr (homotweqinvweq stnweq i)).
      induction (invmap stnweq i) as [i' | i'].
      - refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ _).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq stnweq _) @ _).
        refine (maponpaths
          (λ x, pr1 (pr1 x) _ _)
          (id_right (BinProductPr1 _ ((bin_products_presheaf_cat _) (theory_presheaf L) P')))
        @ _).
        apply (maponpaths (λ x, (pr (stnweq (inr x))))).
        exact (!pr2 iscontrunit i').
    Qed.

    Definition theory_presheaf_exponentiable
      : is_exponentiable (bin_products_presheaf_cat _) (theory_presheaf L).
    Proof.
      use left_adjoint_from_partial.
      - exact plus_1_presheaf.
      - exact presheaf_exponent_morphism.
      - intros P P' F.
        use make_iscontr.
        + use tpair.
          * exact (presheaf_exponent_induced_morphism F).
          * exact (presheaf_exponent_induced_morphism_commutes F).
        + exact (presheaf_exponent_induced_morphism_unique F).
    Defined.

    Lemma invmap_hom_weq_eq
      {m n : nat}
      (G : presheaf_cat L ⟦pow n, pr1 theory_presheaf_exponentiable (theory_presheaf L)⟧)
      (l : ((PO (S n)) m : hSet))
      : pr11 (φ_adj_inv (pr2 theory_presheaf_exponentiable) G) m l
      = pr11 G m (pr2 l) • (extend_tuple pr (pr1 l)).
    Proof.
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := theory_presheaf L) _ _ _) @ _).
      refine (maponpaths (λ x, x • _) _ @ maponpaths (λ x, (pr11 G) m (pr2 l) • x) _).
      - exact (maponpaths (λ x, x _) (presheaf_mor_comp _ G _)).
      - refine (!extend_tuple_eq _ _).
        + intro i.
          exact (!maponpaths _ (homotinvweqweq _ (inl i))).
        + refine (!_ @ !maponpaths _ (homotinvweqweq _ (inr tt))).
          exact (maponpaths
            (λ x, pr11 x _ _)
            (id_right (BinProductPr1 _ (bin_products_presheaf_cat _ (theory_presheaf L) _)))
          ).
    Qed.

    Lemma hom_weq_eq
      {m n : nat}
      (G : presheaf_cat L ⟦pow (S n), theory_presheaf L⟧)
      (l : ((PO n) m : hSet))
      : pr11 (φ_adj (pr2 theory_presheaf_exponentiable) G) m l
      = pr11 G (S m) (pr (stnweq (inr tt)) ,, action l (λ i, pr (stnweq (inl i)))).
    Proof.
      refine (maponpaths
        (λ x, x _)
        (presheaf_mor_comp (P'' := plus_1_presheaf (theory_presheaf L)) _ _ _)
      @ _).
      refine (maponpaths
        (λ x, x _)
        (presheaf_mor_comp (P := BPO _ _) (P'' := theory_presheaf L) _ G _)
      @ _).
      refine (maponpaths (pr11 G (S m)) _).
      apply pathsdirprod.
      - refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ _).
        refine (maponpaths (λ x, pr1 x • _) (presheaf_identity_on_element (PO (S n)) _) @ _).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (maponpaths (λ x, _ x • _) (homotinvweqweq stnweq _) @ _).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths (λ x, _ x) (homotinvweqweq stnweq _)).
      - refine (maponpaths
          (λ x, action (pr2 (action (P := (plus_1_presheaf (PO (S n)))) x _)) _)
          (presheaf_identity_on_element (PO (S n)) _)
        @ _).
        do 2 refine (presheaf_is_assoc _ _ _ _ _ _ _ @ _).
        apply maponpaths.
        apply funextfun.
        intro i.
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (maponpaths (λ x, _ x • _) (homotinvweqweq stnweq _) @ _).
        refine (maponpaths (λ x, x • _) (algebraic_theory_comp_projects_component _ _ _ _ _) @ _).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

  End Exponentiable.

  (** * 2. A construction of the lambda endomorphism theory of theory_presheaf *)

  Lemma presheaf_lambda_theory_aux
    {m n : nat}
    (f : stn m → (L _ : hSet))
    : extend_tuple (λ i : stn m, # L (dni lastelement) (f i)) (pr lastelement)
    = (λ i, let c := invmap (stnweq) i in
        coprod_rect (λ _, (L (1 + n) : hSet))
          (λ i', f i' • (λ j, pr (stnweq (inl j))))
          (λ i', pr (stnweq (inr i'))) c).
  Proof.
    apply extend_tuple_eq.
    - intro i.
      refine (algebraic_theory_functor_uses_projections _ _ _ _ _ @ !_).
      exact (maponpaths _ (homotinvweqweq _ _)).
    - exact (!maponpaths (λ x, let c := x in _) (homotinvweqweq _ _)).
  Qed.

  Definition presheaf_lambda_theory : lambda_theory.
  Proof.
    pose (exponential_object := pr1 theory_presheaf_exponentiable (theory_presheaf L) : presheaf L).
    use endomorphism_lambda_theory.
    - exact (presheaf_cat L).
    - exact (terminal_presheaf_cat _).
    - exact (bin_products_presheaf_cat _).
    - exact (theory_presheaf L).
    - exact theory_presheaf_exponentiable.
    - use (make_presheaf_morphism' (P := exponential_object) (P' := theory_presheaf L)).
      + intro.
        apply abs.
      + abstract (
          intros m n a f;
          refine (_ @ lambda_theory_abs_compatible_with_comp _ _);
          apply (maponpaths (λ x, abs (a • x)));
          symmetry;
          apply presheaf_lambda_theory_aux
        ).
    - use (make_presheaf_morphism' (P := theory_presheaf L) (P' := exponential_object)).
      + intros n.
        apply app.
      + abstract (
          intros m n a f;
          refine (lambda_theory_app_compatible_with_comp _ _ @ _);
          apply (maponpaths (λ x, app a • x));
          apply presheaf_lambda_theory_aux
        ).
  Defined.

  (** * 3. An isomorphism between the two λ-theories *)

  Section Iso.

    Definition presheaf_to_L
      : algebraic_theory_morphism'_data presheaf_lambda_theory L.
    Proof.
      intros n f.
      refine ((f : presheaf_morphism (PO n) (theory_presheaf L)) n _).
      refine (pow_f_inv n n _).
      exact pr.
    Defined.

    Definition L_to_presheaf
      : algebraic_theory_morphism'_data L presheaf_lambda_theory.
    Proof.
      intros n s.
      unfold presheaf_lambda_theory.
      use (make_presheaf_morphism' (P := PO n) (P' := (theory_presheaf L))).
      - intros n' t.
        refine (s • _).
        intro i.
        exact (pow_f n n' t i).
      - abstract (
          intros;
          refine (_ @ !algebraic_theory_comp_is_assoc _ _ _ _ _ _ _);
          apply maponpaths;
          apply funextfun;
          intro;
          now rewrite presheaf_morphism_commutes_with_action
        ).
    Defined.

    Lemma L_to_presheaf_to_L
      (n : nat)
      (l : (L n : hSet))
      : presheaf_to_L n (L_to_presheaf n l) = l.
    Proof.
      refine (_ @ algebraic_theory_comp_identity_projections _ _ _).
      apply (maponpaths (comp l)).
      apply funextfun.
      intro i.
      refine (maponpaths
        (λ x, x _ _)
        (!presheaf_mor_comp _ (pow_f n : presheaf_cat L⟦PO n, PO' n⟧) _)
      @ _).
      refine (maponpaths (λ x, pr11 x _ _ _) (z_iso_after_z_iso_inv (pow_iso n)) @ _).
      refine (maponpaths (λ x, x _) (presheaf_identity_on_element (PO' n) _)).
    Qed.

    Lemma presheaf_to_L_to_presheaf
      (n : nat)
      (l : (presheaf_lambda_theory n : hSet))
      : L_to_presheaf n (presheaf_to_L n l) = l.
    Proof.
      apply (presheaf_morphism_eq _ (l : presheaf_morphism (PO n) ((theory_presheaf L)))).
      intro m.
      apply funextfun.
      intro x.
      refine (!presheaf_morphism_commutes_with_action
        (l : presheaf_morphism (PO n) (theory_presheaf L))
      _ _ @ _).
      apply maponpaths.
      refine (!presheaf_morphism_commutes_with_action (pow_f_inv n) _ _ @ _).
      refine (_ @ presheaf_identity_on_element _ _).
      refine (!_ @ maponpaths (λ x, pr11 x _ _) (z_iso_inv_after_z_iso (pow_iso n))).
      refine (maponpaths (λ x, x _) (presheaf_mor_comp _ _ _) @ _).
      apply (maponpaths (pow_f_inv n _)).
      apply funextsec.
      intro.
      exact (!algebraic_theory_comp_projects_component _ _ _ _ _).
    Qed.

    Lemma L_to_presheaf_preserves_pr
      (n : nat)
      (i : stn n)
      : L_to_presheaf n (pr i) = pr i.
    Proof.
      apply (presheaf_morphism_eq (P := PO n) (P' := theory_presheaf L)).
      intro m.
      refine (_ @ !presheaf_mor_comp (P'' := theory_presheaf L) _ _ _).
      apply funextfun.
      intro t.
      apply algebraic_theory_comp_projects_component.
    Qed.

    Lemma L_to_presheaf_preserves_comp
      (m n : nat)
      (f : (L m : hSet))
      (g : stn m → (L n : hSet))
      : L_to_presheaf n (f • g) = (L_to_presheaf m f) • (λ i, L_to_presheaf n (g i)).
    Proof.
      apply (presheaf_morphism_eq (P := PO n) (P' := theory_presheaf L)).
      intro l.
      refine (_ @ !presheaf_mor_comp (P'' := theory_presheaf L) _ _ _).
      apply funextfun.
      intro t.
      refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ !_).
      apply (maponpaths (comp f)).
      apply funextfun.
      intro i.
      exact (maponpaths (λ x, x t) (!presheaf_mor_comp _ _ _) @
          maponpaths (λ x, pr11 x l t) (ProductPrCommutes _ _ _ (pow m) _ _ i)).
    Qed.

    Local Lemma aux2
      (n : nat)
      : pr2 (pow_f_inv (S n) (S n) pr)
      = action (P := PO n) (pow_f_inv n n pr) (λ i, pr (stnweq (inl i))).
    Proof.
      do 2 refine (!presheaf_identity_on_element _ _ @ !_).
      do 2 refine (maponpaths (λ x, pr11 x _ _) (!z_iso_inv_after_z_iso (pow_iso n)) @ !_).
      do 2 refine (maponpaths (λ x, x _) (presheaf_mor_comp _ _ _) @ !_).
      apply (maponpaths (pr11 _ (S n))).
      apply funextsec.
      intro i.
      refine (maponpaths
        (λ x, x pr)
        (!presheaf_mor_comp (P := PO' (S n)) (P'' := theory_presheaf L) _ _ _)
      @ !_).
      rewrite (ProductPrCommutes _ _ _ (pow n) _ _ i).
      refine (eqtohomot (presheaf_morphism_commutes_with_action (pow_f n) _ _) i @ _).
      refine (maponpaths
        (λ x, action (P := PO' n) (x pr) _ _)
        (!presheaf_mor_comp (P := PO' n) (P'' := PO' n) _ (pow_f _) _)
      @ _).
      refine (maponpaths
        (λ x, action (P := PO' n) (pr11 x n pr) _ _)
        (z_iso_after_z_iso_inv (pow_iso n))
      @ _).
      refine (maponpaths
        (λ x, action (P := PO' n) x _ _)
        (presheaf_identity_on_element (PO' n) _)
      @ _).
      exact (algebraic_theory_comp_projects_component _ _ _ _ _).
    Qed.

    Lemma presheaf_to_L_preserves_app
      (n : nat)
      (s : (presheaf_lambda_theory n : hSet))
      : presheaf_to_L (S n) (app s) = app (presheaf_to_L n s).
    Proof.
      refine (invmap_hom_weq_eq _ _ @ _).
      match goal with
      | [ |- pr11 ?x1 _ _ • _ = _ ] => pose (x1' := x1)
      end.
      refine (maponpaths (λ x, pr11 x1' _ x • _) (aux2 n) @ _).
      refine (maponpaths (λ x, x • _) (presheaf_morphism_commutes_with_action
        (x1' : presheaf_morphism (PO n) (pr1 theory_presheaf_exponentiable _ : presheaf L))
      _ _) @ _).
      refine (algebraic_theory_comp_is_assoc _ _ _ _ _ _ _ @ _).
      refine (maponpaths
        (λ x, x _ • _)
        (presheaf_mor_comp (P'' := plus_1_presheaf (theory_presheaf L)) _ _ _)
      @ _).
      refine (_ @ algebraic_theory_comp_identity_projections _ _ _).
      apply maponpaths.
      apply funextfun.
      intro i.
      refine (_ @ maponpaths _ (homotweqinvweq stnweq i)).
      induction (invmap stnweq i) as [i' | i'].
      - refine (maponpaths (λ x, x • _) (algebraic_theory_comp_projects_component _ _ _ _ _) @ _).
        refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        refine (extend_tuple_i _ _ _ _ (dni_last_lt _) @ _).
        apply maponpaths.
        apply stn_eq.
        apply di_eq1.
        exact (stnlt (dni lastelement i')).
      - refine (algebraic_theory_comp_projects_component _ _ _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq _ _)).
    Qed.

    Lemma presheaf_to_L_preserves_abs
      (n : nat)
      (s : (presheaf_lambda_theory (S n) : hSet))
      : presheaf_to_L n (abs s) = abs (presheaf_to_L (S n) s).
    Proof.
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := theory_presheaf L) _ _ _) @ _).
      apply (maponpaths abs).
      refine (hom_weq_eq _ _ @ _).
      apply (maponpaths (λ x, (pr11 s) _ x)).
      refine (!presheaf_identity_on_element _ _ @ _).
      refine (maponpaths (λ x, pr11 x _ _) (!z_iso_inv_after_z_iso (pow_iso _)) @ _).
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := pow _) _ _ _) @ _).
      apply (maponpaths (pow_f_inv (S n) _)).
      apply funextsec.
      intro i.
      rewrite <- (homotweqinvweq stnweq i).
      induction (invmap stnweq i) as [i' | i'];
        refine (maponpaths (λ x, (_ x : presheaf_morphism _ _) _ _) (homotinvweqweq stnweq _) @ _).
      - refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := theory_presheaf L) _ _ _) @ _).
        refine (presheaf_morphism_commutes_with_action
          (ProductPr _ _ (pow n) _ : presheaf_morphism (PO _) (theory_presheaf L))
        _ _ @ _).
        refine (maponpaths
          (λ x, x _ • _)
          (!presheaf_mor_comp (P'' := theory_presheaf L) _ _ _)
        @ _).
        refine (maponpaths (λ x, pr11 x _ _ • _) (ProductPrCommutes _ _ _ (pow _) _ _ _) @ _).
        apply algebraic_theory_comp_projects_component.
      - apply idpath.
    Qed.

    Definition presheaf_lambda_theory_iso
      : z_iso (C := lambda_theory_cat) presheaf_lambda_theory L.
    Proof.
      use make_lambda_theory_z_iso.
      - apply z_iso_inv.
        use make_algebraic_theory_z_iso.
        + intro n.
          use make_z_iso.
          * exact (λ l, L_to_presheaf n l).
          * exact (λ l, presheaf_to_L n l).
          * abstract (
              split;
              apply funextfun;
              intro l;
              [ exact (L_to_presheaf_to_L n l)
              | exact (presheaf_to_L_to_presheaf n l) ]
            ).
        + exact L_to_presheaf_preserves_pr.
        + exact L_to_presheaf_preserves_comp.
      - exact presheaf_to_L_preserves_app.
      - exact presheaf_to_L_preserves_abs.
    Defined.

  End Iso.

End RepresentationTheorem.
