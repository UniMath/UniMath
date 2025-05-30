(**

  The Monoid of a Lambda Theory

  From a lambda theory L with β-equality, we can construct a monoid. The underlying set consists of
  the terms f : L 0 that satisfy η-equality, or, equivalently, the terms for which there exists
  g : L 1 such that f = abs g. The operation is given by 'function composition' and the unit is
  λ x, x. We need η-equality to make the unit laws work.
  This monoid is isomorphic to the 'algebraic theory monoid' L 1.
  If we consider the monoid as a category and take its setcategory Karoubi envelope RS, the result
  is equal to the 'category of retracts' R of L, because the constructions of R and R^S are
  parallel.

  Contents
  1. The monoid [lambda_theory_to_monoid]
  2. It is isomorphic to the algebraic theory monoid [lambda_theory_to_monoid_iso]
  3. The setcategory Karoubi envelope is equal to the category of retracts
    [lambda_theory_to_monoid_cat_equality]

 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.SetKaroubi.
Require Import UniMath.CategoryTheory.Categories.KaroubiEnvelope.Core.
Require Import UniMath.CategoryTheory.Categories.Monoid.
Require Import UniMath.CategoryTheory.Categories.MonoidToCategory.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryToMonoid.
Require Import UniMath.AlgebraicTheories.CategoryOfRetracts.
Require Import UniMath.AlgebraicTheories.Combinators.
Require Import UniMath.AlgebraicTheories.LambdaTheories.

Local Open Scope cat.
Local Open Scope lambda_calculus.

Section Monoid.

  Context (L : β_lambda_theory).
  Let Lβ : has_β L := β_lambda_theory_has_β L.

(** * 1. The monoid *)

  Definition satisfies_η
    {n : nat}
    (f : L n)
    : hProp
    := (abs (appx f) = f)%logic.

  Definition abs_satisfies_η
    {n : nat}
    (f : L (S n))
    : satisfies_η (abs f)
    := maponpaths abs (Lβ _ _).

  Definition lambda_theory_to_monoid_set
    : hSet
    := carrier_subset (X := L 0) satisfies_η.

  Coercion lambda_theory_to_monoid_set_to_lambda
    (f : lambda_theory_to_monoid_set)
    : L 0
    := pr1 f.

  Definition lambda_theory_to_monoid_set_satisfies_η
    (f : lambda_theory_to_monoid_set)
    : satisfies_η f
    := pr2 f.

  Definition lambda_theory_to_monoid_set_eq
    (f g : lambda_theory_to_monoid_set)
    (H : (f : L 0) = g)
    : f = g
    := subtypePath (λ x, propproperty _) H.

  Definition make_lambda_theory_to_monoid_set
    (f : L 0)
    (H : satisfies_η f)
    : lambda_theory_to_monoid_set
    := f ,, H.

  Definition lambda_theory_to_monoid_binop
    : binop lambda_theory_to_monoid_set.
  Proof.
    intros f g.
    use make_lambda_theory_to_monoid_set.
    - exact (f ∘ g).
    - abstract apply abs_satisfies_η.
  Defined.

  Lemma lambda_theory_to_monoid_assoc
    : isassoc lambda_theory_to_monoid_binop.
  Proof.
    intros f g h.
    apply lambda_theory_to_monoid_set_eq.
    exact (!compose_assoc L Lβ _ _ _).
  Qed.

  Definition lambda_theory_to_monoid_unit
    : lambda_theory_to_monoid_set.
  Proof.
    use make_lambda_theory_to_monoid_set.
    - exact (U L Lβ).
    - abstract apply abs_satisfies_η.
  Defined.

  Lemma lambda_theory_to_monoid_isunit
    : isunit lambda_theory_to_monoid_binop lambda_theory_to_monoid_unit.
  Proof.
    apply make_isunit;
      intro f;
      apply lambda_theory_to_monoid_set_eq;
      simpl;
      rewrite <- (lambda_theory_to_monoid_set_satisfies_η f).
    - apply (U_compose L Lβ).
    - apply (compose_U L Lβ).
  Qed.

  Definition lambda_theory_to_monoid
    : monoid
    := make_monoid
      (make_setwithbinop
          lambda_theory_to_monoid_set
          lambda_theory_to_monoid_binop)
      (make_ismonoidop
        lambda_theory_to_monoid_assoc
        (make_isunital
          lambda_theory_to_monoid_unit
          lambda_theory_to_monoid_isunit)).

(** * 2. The isomorphism with the algebraic theory monoid *)

  Definition lambda_theory_to_monoid_iso_mor
    (f : lambda_theory_to_monoid)
    : (algebraic_theory_to_monoid (L : algebraic_theory)) : monoid
    := appx (f : lambda_theory_to_monoid_set).

  Definition lambda_theory_to_monoid_iso_inv
    (f : (algebraic_theory_to_monoid (L : algebraic_theory)) : monoid)
    : lambda_theory_to_monoid
    := make_lambda_theory_to_monoid_set (abs f) (abs_satisfies_η _).

  Lemma lambda_theory_to_monoid_iso_is_inverse
    : is_inverse_in_precat (C := HSET) lambda_theory_to_monoid_iso_mor lambda_theory_to_monoid_iso_inv.
  Proof.
    apply make_is_inverse_in_precat;
      apply funextfun;
      intro f.
    - apply lambda_theory_to_monoid_set_eq.
      apply lambda_theory_to_monoid_set_satisfies_η.
    - apply Lβ.
  Qed.

  Lemma lambda_theory_to_monoid_is_monoidfun
    : ismonoidfun lambda_theory_to_monoid_iso_mor.
  Proof.
    apply make_ismonoidfun;
      unfold lambda_theory_to_monoid_iso_mor, isbinopfun;
      simpl.
    - intros f g.
      rewrite !appx_to_app.
      rewrite inflate_compose.
      rewrite (app_compose _ Lβ).
      rewrite subst_app.
      rewrite subst_inflate.
      rewrite var_subst.
      apply (maponpaths (λ x, app (subst _ x) _)).
      apply (proofirrelevancecontr (iscontr_empty_tuple _)).
    - now rewrite !appx_to_app,
        inflate_U_term,
        (app_U _ Lβ).
  Qed.

  Definition lambda_theory_to_monoid_iso
    : z_iso lambda_theory_to_monoid (algebraic_theory_to_monoid (L : algebraic_theory))
    := make_monoid_z_iso
      (make_z_iso (C := HSET)
          lambda_theory_to_monoid_iso_mor
          lambda_theory_to_monoid_iso_inv
          lambda_theory_to_monoid_iso_is_inverse)
      lambda_theory_to_monoid_is_monoidfun.

(** * 3. The setcategory Karoubi envelope is equal to the category of retracts *)

  Definition lambda_theory_to_monoid_cat
    : setcategory
    := monoid_to_category lambda_theory_to_monoid.

  Definition R_setcategory
    : setcategory
    := make_setcategory
      (R (n := 0) L Lβ)
      (isaset_carrier_subset _ (λ l, make_hProp _ (setproperty _ _ _))).

  Definition lambda_theory_to_monoid_cat_equality_functor_data
    : functor_data (set_karoubi lambda_theory_to_monoid_cat) R_setcategory.
  Proof.
    use make_functor_data.
    - intro A.
      apply (make_R_ob _ (((set_karoubi_ob_idempotent _ A) : _ --> _) : lambda_theory_to_monoid_set)).
      abstract exact (base_paths _ _ (idempotent_is_idempotent (set_karoubi_ob_idempotent _ A))).
    - intros A B f.
      apply (make_R_mor _ ((set_karoubi_mor_morphism _ f) : lambda_theory_to_monoid_set)).
      + abstract exact (base_paths _ _ (set_karoubi_mor_commutes_left _ f)).
      + abstract exact (base_paths _ _ (set_karoubi_mor_commutes_right _ f)).
  Defined.

  Lemma lambda_theory_to_monoid_cat_equality_is_functor
    : is_functor lambda_theory_to_monoid_cat_equality_functor_data.
  Proof.
    abstract (
      apply make_is_functor;
      repeat intro;
      now apply R_mor_eq
    ).
  Qed.

  Definition lambda_theory_to_monoid_cat_equality_functor
    : set_karoubi lambda_theory_to_monoid_cat ⟶ R_setcategory
    := make_functor
      lambda_theory_to_monoid_cat_equality_functor_data
      lambda_theory_to_monoid_cat_equality_is_functor.

  Section FullyFaithful.

    Context (A B : set_karoubi lambda_theory_to_monoid_cat).

    Definition lambda_theory_to_monoid_cat_equality_fully_faithful_inv
      (f : R_mor _ (lambda_theory_to_monoid_cat_equality_functor A) (lambda_theory_to_monoid_cat_equality_functor B))
      : set_karoubi lambda_theory_to_monoid_cat⟦A, B⟧.
    Proof.
      use make_set_karoubi_mor.
      - apply (make_lambda_theory_to_monoid_set f).
        abstract refine (transportf satisfies_η (R_mor_is_mor _ f) (abs_satisfies_η _)).
      - abstract apply lambda_theory_to_monoid_set_eq, (R_mor_is_mor_right _ f).
      - abstract apply lambda_theory_to_monoid_set_eq, (R_mor_is_mor_left _ f).
    Defined.

    Lemma lambda_theory_to_monoid_cat_equality_fully_faithful_weqinvweq
      (f : set_karoubi lambda_theory_to_monoid_cat⟦A, B⟧)
      : lambda_theory_to_monoid_cat_equality_fully_faithful_inv (#lambda_theory_to_monoid_cat_equality_functor f) = f.
    Proof.
      apply set_karoubi_mor_eq.
      now apply lambda_theory_to_monoid_set_eq.
    Qed.

    Lemma lambda_theory_to_monoid_cat_equality_fully_faithful_invweqweq
      (f : R_setcategory⟦lambda_theory_to_monoid_cat_equality_functor A, lambda_theory_to_monoid_cat_equality_functor B⟧)
      : #lambda_theory_to_monoid_cat_equality_functor (lambda_theory_to_monoid_cat_equality_fully_faithful_inv f) = f.
    Proof.
      now apply R_mor_eq.
    Qed.

    Definition lambda_theory_to_monoid_cat_equality_fully_faithful
      : isweq (λ (f : set_karoubi lambda_theory_to_monoid_cat⟦A, B⟧), #lambda_theory_to_monoid_cat_equality_functor f)
      := isweq_iso _
        lambda_theory_to_monoid_cat_equality_fully_faithful_inv
        lambda_theory_to_monoid_cat_equality_fully_faithful_weqinvweq
        lambda_theory_to_monoid_cat_equality_fully_faithful_invweqweq.

  End FullyFaithful.

  Definition lambda_theory_to_monoid_cat_equality_object_equivalence_inv
    (A : R_ob (n := 0) L)
    : set_karoubi lambda_theory_to_monoid_cat.
  Proof.
    use (make_set_karoubi_ob).
    - exact tt.
    - apply (make_lambda_theory_to_monoid_set A).
      abstract exact (transportf satisfies_η (R_ob_idempotent _ A) (abs_satisfies_η _)).
    - abstract apply lambda_theory_to_monoid_set_eq, R_ob_idempotent.
  Defined.

  Lemma lambda_theory_to_monoid_cat_equality_object_equivalence_weqinvweq
    (A : set_karoubi lambda_theory_to_monoid_cat)
    : lambda_theory_to_monoid_cat_equality_object_equivalence_inv (lambda_theory_to_monoid_cat_equality_functor A) = A.
  Proof.
    refine (pathsdirprod (Y := idempotent (tt : lambda_theory_to_monoid_cat)) _ _).
    - now induction (pr1 A).
    - apply subtypePath.
      {
        intro.
        apply (setproperty lambda_theory_to_monoid_set).
      }
      now apply lambda_theory_to_monoid_set_eq.
  Qed.

  Lemma lambda_theory_to_monoid_cat_equality_object_equivalence_invweqweq
    (A : R_setcategory)
    : lambda_theory_to_monoid_cat_equality_functor (lambda_theory_to_monoid_cat_equality_object_equivalence_inv  A) = A.
  Proof.
    now apply R_ob_eq.
  Qed.

  Definition lambda_theory_to_monoid_cat_equality_object_equivalence
    : isweq lambda_theory_to_monoid_cat_equality_functor
    := isweq_iso _
        lambda_theory_to_monoid_cat_equality_object_equivalence_inv
        lambda_theory_to_monoid_cat_equality_object_equivalence_weqinvweq
        lambda_theory_to_monoid_cat_equality_object_equivalence_invweqweq.

  Definition lambda_theory_to_monoid_cat_equality_is_isomorphism
    : is_z_isomorphism (C := cat_of_setcategory) (a := set_set_karoubi lambda_theory_to_monoid_cat) lambda_theory_to_monoid_cat_equality_functor
    := is_catiso_weq_is_z_isomorphism (C := set_set_karoubi _) _ (make_dirprod lambda_theory_to_monoid_cat_equality_fully_faithful lambda_theory_to_monoid_cat_equality_object_equivalence).

  Definition lambda_theory_to_monoid_cat_equality_iso
    : z_iso (C := cat_of_setcategory) (set_set_karoubi lambda_theory_to_monoid_cat) R_setcategory
    := make_z_iso' (C := cat_of_setcategory) (a := set_set_karoubi lambda_theory_to_monoid_cat)
      lambda_theory_to_monoid_cat_equality_functor
      lambda_theory_to_monoid_cat_equality_is_isomorphism.

  Definition lambda_theory_to_monoid_cat_equality
    : set_set_karoubi lambda_theory_to_monoid_cat = R_setcategory
    := isotoid _ (is_univalent_cat_of_setcategory) lambda_theory_to_monoid_cat_equality_iso.

End Monoid.
