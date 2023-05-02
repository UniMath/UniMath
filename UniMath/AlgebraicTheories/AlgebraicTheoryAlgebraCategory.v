Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebras.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryAlgebraMorphisms.

Local Open Scope cat.
Local Open Scope algebraic_theories.
Local Open Scope mor_disp.

Definition algebraic_theory_algebra_data_full_disp_cat
  : disp_cat (cartesian algebraic_theory_cat HSET).
Proof.
  use disp_struct.
  - intro X.
    pose (T := pr1 X : algebraic_theory).
    pose (A := pr2 X : hSet).
    exact (∏ n, (T n : hSet) → (stn n → A) → A).
  - intros X X' action action' Y.
    pose (A := make_algebraic_theory_algebra_data (pr2 X) action).
    pose (A' := make_algebraic_theory_algebra_data (pr2 X') action').
    pose (F := pr1 Y : algebraic_theory_morphism _ _).
    pose (G := pr2 Y : A → A').
    exact (∏ n f a, G (action n f a) = action' n (F _ f) (λ i, G (a i))).
  - intros.
    repeat (apply impred_isaprop; intro).
    apply setproperty.
  - intros X action n f a.
    pose (A := pr2 X : hSet).
    assert (H : pr2 (identity X) = identity (A : HSET)).
    + apply (eqtohomot (transportf_const _ (A → A))).
    + now rewrite H.
  - intros X X' X'' action action' action'' y y' Gcommutes G'commutes n f a.
    pose (A := pr2 X : hSet).
    pose (A' := pr2 X' : hSet).
    pose (A'' := pr2 X'' : hSet).
    pose (G := pr2 y : A → A').
    pose (G' := pr2 y' : A' → A'').
    assert (H : pr2 (y · y') = (G : HSET⟦A, A'⟧) · G').
    + apply (eqtohomot (transportf_const _ (A → A''))).
    + rewrite H.
      unfold compose.
      simpl.
      now rewrite Gcommutes, G'commutes.
Defined.

Definition algebraic_theory_algebra_data_full_cat : category
  := total_category algebraic_theory_algebra_data_full_disp_cat.

Definition algebraic_theory_algebra_full_disp_cat : disp_cat algebraic_theory_algebra_data_full_cat.
Proof.
  use disp_struct.
  - intro X.
    pose (A := make_algebraic_theory_algebra_data (pr21 X) (pr2 X)).
    exact (is_algebraic_theory_algebra A).
  - exact (λ _ _ _ _ _, unit).
  - intros.
    exact isapropunit.
  - intros.
    exact tt.
  - intros.
    exact tt.
Defined.

Definition algebraic_theory_algebra_full_cat : category
  := total_category algebraic_theory_algebra_full_disp_cat.

Definition algebraic_theory_algebra_disp_cat
  : disp_cat algebraic_theory_cat
  := sigma_disp_cat (sigma_disp_cat algebraic_theory_algebra_full_disp_cat).

Definition algebraic_theory_algebra_cat
  (T : algebraic_theory)
  := fiber_category algebraic_theory_algebra_disp_cat T.

Lemma displayed_algebra_morphism_eq
  {T T' : algebraic_theory}
  {F : algebraic_theory_morphism T T'}
  {A : algebraic_theory_algebra T}
  {A' : algebraic_theory_algebra T'}
  (G G' : (A : algebraic_theory_algebra_disp_cat _) -->[F] A')
  (H : pr1 G = pr1 G')
  : G = G'.
Proof.
  apply (subtypePairEquality' H).
  use (isapropdirprod _ _ _ isapropunit).
  repeat (apply impred_isaprop; intro).
  apply setproperty.
Qed.

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

Lemma concat_displayed_algebra_morphisms
  {C C' : category}
  {D : disp_cat (cartesian C C')}
  {D' : disp_cat (total_category D)}
  (E := sigma_disp_cat (sigma_disp_cat D'))
  {c c' c'' : C}
  {A : E c}
  {A' : E c'}
  {A'' : E c''}
  {F : C⟦c', c⟧}
  {F' : C⟦c'', c'⟧}
  (G' : A'' -->[F'] A')
  (G : A' -->[F] A)
  : pr1 (G' ;; G) = (pr1 G') · (pr1 G).
Proof.
  simpl.
  unfold comp_disp.
  simpl.
  unfold transportb, comp_disp.
  simpl.
  now rewrite (transportf_paths _ (unit_equality_is_idpath F F' _)),
    idpath_transportf.
Qed.

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
  exact (concat_displayed_algebra_morphisms (algebra_cleaving_induced_morphism _ _ _) _).
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
    exact (!concat_displayed_algebra_morphisms _ _ @ maponpaths _ (pr2 t)).
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
