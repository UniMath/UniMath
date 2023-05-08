(* Shows that algebraic theory algebras are fibered over algebraic theories. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.

Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebraCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebras.

Local Open Scope cat.
Local Open Scope mor_disp.

Lemma unit_equality_is_idpath
  {C : precategory}
  {T T' T'' : C}
  (F : C⟦T', T⟧)
  (F' : C⟦T'', T'⟧)
  (H :  # (functor_to_unit C) F' · # (functor_to_unit C) F = # (functor_to_unit C) (F' · F))
  : H = idpath _.
Proof.
  apply isasetunit.
Qed.

Lemma concat_displayed_cartesian_morphisms
  {C C' : category}
  (D := disp_cartesian C C')
  {c c' c'' : C}
  {F : C⟦c, c'⟧} {F' : C⟦c', c''⟧}
  {A : D c} {A' : D c'} {A'' : D c''}
  (G : A -->[F] A') (G' : A' -->[F'] A'')
  : (G ;; G') = G · G'.
Proof.
  unfold comp_disp.
  simpl.
  now rewrite (unit_equality_is_idpath F' F _).
Qed.

Definition algebra_cleaving_algebra_data
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T' T)
  (A : algebraic_theory_algebra T)
  : algebraic_theory_algebra_data T'.
Proof.
  use tpair.
  - exact A.
  - intros n f a.
    exact (action (F _ f) a).
Defined.

Lemma algebra_cleaving_is_algebra
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T' T)
  (A : algebraic_theory_algebra T)
  : is_algebraic_theory_algebra (algebra_cleaving_algebra_data F A).
Proof.
  use (_ ,, _ ,, _).
  - do 5 intro.
    simpl.
    rewrite (algebraic_theory_morphism_preserves_composition F).
    apply algebraic_theory_algebra_is_assoc.
  - intro.
    rewrite <- algebraic_theory_algebra_is_unital.
    simpl.
    apply (maponpaths (λ i, _ _ i _)).
    apply algebraic_theory_morphism_preserves_id_pr.
  - do 5 intro.
    simpl.
    rewrite (maponpaths (λ x, x _) (nat_trans_ax (F : algebraic_theory_morphism _ _) _ _ _
      : (λ x, _ _ (# (T' : algebraic_theory) _ _)) = _)).
    apply algebraic_theory_algebra_is_natural.
Qed.

Definition algebra_cleaving_algebra
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T' T)
  (A : algebraic_theory_algebra T)
  : algebraic_theory_algebra T'
  := make_algebraic_theory_algebra _ (algebra_cleaving_is_algebra F A).

Definition algebra_cleaving_morphism
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T' T)
  (A : algebraic_theory_algebra T)
  : (algebra_cleaving_algebra F A : algebraic_theory_algebra_disp_cat _) -->[F] A.
Proof.
  use (idfun _ ,, _ ,, tt).
  abstract now do 3 intro.
Defined.

Definition algebra_cleaving_induced_morphism
  {T T' T'' : algebraic_theory}
  {A : algebraic_theory_algebra T}
  {A'' : algebraic_theory_algebra T''}
  (F : algebraic_theory_morphism T' T)
  (F' : algebraic_theory_morphism T'' T')
  (G' : (A'' : algebraic_theory_algebra_disp_cat _) -->[(F' : algebraic_theory_cat⟦_, _⟧) · F] A)
  : (A'' : algebraic_theory_algebra_disp_cat _) -->[F'] algebra_cleaving_algebra F A.
Proof.
  use (pr1 G' ,, _ ,, tt).
  abstract (do 3 intro; now rewrite (pr12 G')).
Defined.

Definition algebra_lift
  {T T' T'' : algebraic_theory}
  {A : algebraic_theory_algebra T}
  {A'' : algebraic_theory_algebra T''}
  (F : algebraic_theory_morphism T' T)
  (F' : algebraic_theory_morphism T'' T')
  (G' : (A'' : algebraic_theory_algebra_disp_cat _) -->[(F' : algebraic_theory_cat⟦_, _⟧) · F] A)
  : ∑ gg, (gg ;; algebra_cleaving_morphism F A) = G'.
Proof.
  exists (algebra_cleaving_induced_morphism F F' G').
  apply displayed_algebra_morphism_eq.
  exact (concat_displayed_cartesian_morphisms _ _).
Defined.

Lemma algebra_lift_is_unique
  {T T' T'' : algebraic_theory}
  {A : algebraic_theory_algebra T}
  {A'' : algebraic_theory_algebra T''}
  (F : algebraic_theory_morphism T' T)
  (F' : algebraic_theory_morphism T'' T')
  (G' : (A'' : algebraic_theory_algebra_disp_cat _) -->[(F' : algebraic_theory_cat⟦_, _⟧) · F] A)
  : ∏ t : (∑ gg, (gg ;; algebra_cleaving_morphism F A) = G'), t = (algebra_lift F F' G').
Proof.
  intro.
  apply subtypePairEquality'.
  + apply displayed_algebra_morphism_eq.
    exact (!concat_displayed_cartesian_morphisms (pr11 t) _ @ maponpaths _ (pr2 t)).
  + apply homsets_disp.
Qed.

Definition algebra_cleaving_is_cartesian
  {T T' : algebraic_theory}
  (F : algebraic_theory_morphism T' T)
  (A : algebraic_theory_algebra T)
  : is_cartesian (algebra_cleaving_morphism F A)
  := (λ _ F' _ G', algebra_lift F F' G' ,, algebra_lift_is_unique F F' G').

Definition algebra_cleaving
  : cleaving algebraic_theory_algebra_disp_cat
  := λ _ _ F A,
    algebra_cleaving_algebra F A ,,
    algebra_cleaving_morphism F A ,,
    algebra_cleaving_is_cartesian F A.

Definition algebra_fibration
  : fibration algebraic_theory_cat
  := _ ,, algebra_cleaving.
