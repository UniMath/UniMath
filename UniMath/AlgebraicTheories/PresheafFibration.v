Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.Presheaves.
Require Import UniMath.AlgebraicTheories.PresheafCategory.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.

Local Open Scope cat.
Local Open Scope mor_disp.

Section lift.

  Context {c c' : algebraic_theory}.
  Context (f : algebraic_theory_morphism c' c).
  Context (d : presheaf c).

  Definition lifted_presheaf_data
    : presheaf_data c'.
  Proof.
    use make_presheaf_data.
    - exact (pr1 d).
    - intros m n s t.
      exact (action (P := d) s (λ i, f _ (t i))).
  Defined.

  Definition lifted_is_presheaf
    : is_presheaf lifted_presheaf_data.
  Proof.
    use make_is_presheaf.
    - do 6 intro.
      cbn.
      refine (presheaf_is_assoc d _ _ _ _ _ _ @ _).
      apply maponpaths.
      apply funextfun.
      intro.
      symmetry.
      apply algebraic_theory_morphism_preserves_composition.
    - do 2 intro.
      cbn.
      refine (_ @ presheaf_identity_projections d _ _).
      apply maponpaths.
      apply funextfun.
      intro.
      apply algebraic_theory_morphism_preserves_projections.
    - do 6 intro.
      apply presheaf_action_is_natural.
  Qed.

  Definition lifted_presheaf
    : presheaf c'
    := make_presheaf _ lifted_is_presheaf.

  Definition lifted_presheaf_morphism
    : (lifted_presheaf : presheaf_disp_cat c') -->[f] d.
  Proof.
    use tpair.
    - apply nat_trans_id.
    - refine (_ ,, tt).
      now do 4 intro.
  Defined.

  Section cartesian.

    Context {c'': algebraic_theory}.
    Context {g: algebraic_theory_morphism c'' c'}.
    Context {d'': presheaf c''}.
    Context (hh: (d'' : presheaf_disp_cat c'') -->[(g : algebraic_theory_cat ⟦ _, _ ⟧) · f] d).

    Definition induced_morphism
      : (d'' : presheaf_disp_cat c'') -->[ g] lifted_presheaf.
    Proof.
      use tpair.
      - exact (pr1 hh).
      - refine (_ ,, tt).
        do 4 intro.
        exact (pr12 hh _ _ _ _).
    Defined.

    Lemma induced_morphism_commutes
      : (induced_morphism ;; lifted_presheaf_morphism) = hh.
    Proof.
      apply displayed_presheaf_morphism_eq.
      refine (comp_disp_cartesian _ _ _ _ @ _).
      apply (nat_trans_eq (homset_property HSET)).
      intro.
      apply funextfun.
      now intro.
    Qed.

    Lemma induced_morphism_unique
      (t : ∑ induced_morphism', (induced_morphism' ;; lifted_presheaf_morphism) = hh)
      : t = induced_morphism ,, induced_morphism_commutes.
    Proof.
      apply subtypePairEquality'; [ | apply homsets_disp].
      apply displayed_presheaf_morphism_eq.
      refine (
        nat_trans_eq (homset_property HSET) _ _ _ _ _ @
        !comp_disp_cartesian _ _ (pr11 t) _ @
        maponpaths _ (pr2 t)
      ).
      intro.
      apply funextfun.
      now intro.
    Qed.

  End cartesian.

  Definition lifted_presheaf_morphism_is_cartesian
    : is_cartesian lifted_presheaf_morphism.
  Proof.
    intros c'' g d'' hh.
    use ((_ ,, _) ,, _).
    - exact (induced_morphism hh).
    - exact (induced_morphism_commutes hh).
    - exact (induced_morphism_unique hh).
  Defined.

End lift.

Definition presheaf_cleaving
  : cleaving presheaf_disp_cat
  := λ c c' f d,
    (lifted_presheaf f d) ,,
    (lifted_presheaf_morphism f d) ,,
    (lifted_presheaf_morphism_is_cartesian f d).

Definition presheaf_fibration
  : fibration algebraic_theory_cat
  := presheaf_disp_cat ,, presheaf_cleaving.
