(**************************************************************************************************

  The monoid of terms in one variable, of an algebraic theory

  If we have an algebraic theory T, we can give T_1 a monoid structure, with substitution as the
  operation and x_1 as the unit. This construction is functorial in T. The monoid, when viewed as a
  category, can be embedded into the Lawvere theory associated to T.

  Contents
  1. The construction of the monoid [algebraic_theory_to_monoid]
  2. The embedding into the Lawvere theory [theory_monoid_to_lawvere]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Categories.Monoid.
Require Import UniMath.CategoryTheory.Categories.MonoidToCategory.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryToLawvereTheory.

Local Open Scope algebraic_theories.
Local Open Scope cat.
Local Open Scope stn.

(** * 1. The construction of the monoid *)

Section AlgebraicTheoryToMonoid.

  Section Ob.

    Context (T : algebraic_theory).

    Definition algebraic_theory_to_monoid_ob : monoid.
    Proof.
      use make_monoid.
      - use make_setwithbinop.
        + exact (T 1).
        + intros a b.
          exact (a • (λ _, b)).
      - use make_ismonoidop.
        + abstract (
            intros a b c;
            apply subst_subst
          ).
        + exists (var (● 0 : stn 1)).
          abstract (
            split;
            [ intro m;
              apply var_subst
            | intro m;
              refine (_ @ subst_var _ _);
              apply (maponpaths (subst m));
              apply funextfun;
              intro i;
              apply maponpaths;
              symmetry;
              apply (iscontr_uniqueness (iscontrstn1)) ]
          ).
    Defined.

  End Ob.

  Section Mor.

    Context {T T' : algebraic_theory}.
    Context (f : algebraic_theory_morphism T T').

    Lemma algebraic_theory_morphism_to_ismonoidfun
      : ismonoidfun (X := algebraic_theory_to_monoid_ob T) (Y := algebraic_theory_to_monoid_ob T') (f 1).
    Proof.
      use make_ismonoidfun.
      - intros s t.
        apply mor_subst.
      - apply mor_var.
    Qed.

    Definition algebraic_theory_morphism_to_monoidfun
      : monoidfun (algebraic_theory_to_monoid_ob T) (algebraic_theory_to_monoid_ob T')
      := make_monoidfun algebraic_theory_morphism_to_ismonoidfun.

  End Mor.

  Definition algebraic_theory_to_monoid_functor_data
    : functor_data algebraic_theory_cat monoid_category
    := make_functor_data (C' := monoid_category)
      algebraic_theory_to_monoid_ob
      (λ _ _, algebraic_theory_morphism_to_monoidfun).

  Lemma algebraic_theory_to_monoid_is_functor
    : is_functor algebraic_theory_to_monoid_functor_data.
  Proof.
    split.
    - intro T.
      now apply monoidfun_paths.
    - intros T T' T'' f f'.
      now apply monoidfun_paths.
  Qed.

  Definition algebraic_theory_to_monoid
    : algebraic_theory_cat ⟶ monoid_category
    := make_functor
      algebraic_theory_to_monoid_functor_data
      algebraic_theory_to_monoid_is_functor.

End AlgebraicTheoryToMonoid.

(** * 2. The embedding into the Lawvere theory *)

Section Lawvere.

  Context (T : algebraic_theory).

  Definition algebraic_theory_monoid_category
    : setcategory
    := monoid_to_category (algebraic_theory_to_monoid T).

  Definition theory_monoid_to_lawvere
    : algebraic_theory_monoid_category ⟶ (algebraic_theory_to_lawvere T : setcategory).
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro t.
        exact 1.
      + intros t t' f i.
        exact f.
    - split.
      + abstract (
          intro t;
          apply funextfun;
          intro i;
          apply (maponpaths var);
          apply proofirrelevancecontr;
          apply iscontrstn1
        ).
      + abstract easy.
  Defined.

  Definition theory_monoid_to_lawvere_fully_faithful
    : fully_faithful theory_monoid_to_lawvere.
  Proof.
    intros t t'.
    use isweq_iso.
    - intro f.
      exact (f (● 0 : stn 1)).
    - abstract trivial.
    - abstract (
        intro f;
        apply funextfun;
        intro i;
        apply (maponpaths f);
        apply proofirrelevancecontr;
        apply iscontrstn1
      ).
  Defined.

End Lawvere.
