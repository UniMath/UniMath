(**************************************************************************************************

  Properties of the category of algebraic theory algebras

  The displayed category structure is leveraged to show that the category univalent. The total
  category of algebras forms a fibration over the category of algebraic theories. Also, a
  characterization of isomorphisms is given.

  Contents
  1. Univalence [is_univalent_algebra_cat]
  2. Algebras are fibered over theories [algebra_fibration]
  3. A characterization of iso's of algebras [make_algebra_z_iso]
  4. Algebra pullback functor along an algebraic theory morphism [algebra_pullback]

 **************************************************************************************************)
Require Export UniMath.AlgebraicTheories.AlgebraCategoryCore.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Algebras.

Local Open Scope cat.
Local Open Scope mor_disp.

(** * 1. Univalence *)

Lemma is_univalent_disp_algebra_data_full_disp_cat
  : is_univalent_disp algebra_data_full_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros TA action action'.
  use isweq_iso.
  - intro f.
    do 3 (apply funextsec; intro).
    apply (z_iso_mor f _).
  - intro.
    do 3 (apply impred_isaset; intro).
    apply setproperty.
  - intro.
    apply z_iso_eq.
    do 3 (apply impred_isaprop; intro).
    apply setproperty.
Qed.

Lemma is_univalent_algebra_data_full_cat
  : is_univalent algebra_data_full_cat.
Proof.
  use is_univalent_total_category.
  - exact (is_univalent_cartesian' _ _ is_univalent_algebraic_theory_cat is_univalent_HSET).
  - exact is_univalent_disp_algebra_data_full_disp_cat.
Qed.

Lemma is_univalent_disp_algebra_full_disp_cat
  : is_univalent_disp algebra_full_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact (λ _, isaprop_full_is_algebra _).
Qed.

Lemma is_univalent_algebra_full_cat
  : is_univalent algebra_full_cat.
Proof.
  apply (is_univalent_total_category is_univalent_algebra_data_full_cat).
  exact is_univalent_disp_algebra_full_disp_cat.
Qed.

Lemma is_univalent_algebra_cat (T : algebraic_theory)
  : is_univalent (algebra_cat T).
Proof.
  refine (is_univalent_fiber_cat _ _ _).
  unfold algebra_disp_cat.
  repeat use is_univalent_sigma_disp.
  - apply is_univalent_disp_cartesian'.
    apply is_univalent_HSET.
  - exact is_univalent_disp_algebra_data_full_disp_cat.
  - exact is_univalent_disp_algebra_full_disp_cat.
Qed.

(** * 2. Algebras are fibered over theories *)

Section Cleaving.

  Context {T T' : algebraic_theory}.
  Context (F : algebraic_theory_morphism T' T).
  Context (A : algebra T).

  Definition algebra_cleaving_algebra_data
    : algebra_data T'.
  Proof.
    use tpair.
    - exact A.
    - intros n f a.
      exact (action (F _ f) a).
  Defined.

  Lemma algebra_cleaving_is_algebra
    : is_algebra algebra_cleaving_algebra_data.
  Proof.
    repeat split.
    - do 5 intro.
      refine (maponpaths (λ x, _ x a) (mor_subst F _ _) @ _).
      apply (subst_action A).
    - intros n i a.
      refine (_ @ var_action A _ _).
      apply (maponpaths (λ f, action (A := A) f _)).
      apply mor_var.
  Qed.

  Definition algebra_cleaving_algebra
    : algebra T'
    := make_algebra _ algebra_cleaving_is_algebra.

  Definition algebra_cleaving_morphism
    : (algebra_cleaving_algebra : algebra_disp_cat _) -->[F] A.
  Proof.
    refine (idfun _ ,, _ ,, tt).
    abstract now do 3 intro.
  Defined.

  Section Lift.

    Context {T'' : algebraic_theory}.
    Context {A'' : algebra T''}.
    Context (F' : algebraic_theory_morphism T'' T').
    Context (G' : (A'' : algebra_disp_cat _) -->[(F' : algebraic_theory_cat⟦_, _⟧) · F] A).

    Definition algebra_cleaving_induced_morphism
      : (A'' : algebra_disp_cat _) -->[F'] algebra_cleaving_algebra.
    Proof.
      refine (pr1 G' ,, _ ,, tt).
      abstract (do 3 intro; apply (pr12 G' _)).
    Defined.

    Definition algebra_lift
      : ∑ gg, (gg ;; algebra_cleaving_morphism) = G'.
    Proof.
      exists algebra_cleaving_induced_morphism.
      now apply displayed_algebra_morphism_eq.
    Defined.

    Lemma algebra_lift_is_unique
      : ∏ t : (∑ gg, (gg ;; algebra_cleaving_morphism) = G'), t = algebra_lift.
    Proof.
      intro t.
      apply subtypePath.
      {
        intro.
        apply homsets_disp.
      }
      apply displayed_algebra_morphism_eq.
      exact (maponpaths _ (pr2 t)).
    Qed.

  End Lift.

  Definition algebra_cleaving_is_cartesian
    : is_cartesian algebra_cleaving_morphism
    := (λ _ F' _ G', algebra_lift F' G' ,, algebra_lift_is_unique F' G').

End Cleaving.

Definition algebra_cleaving
  : cleaving algebra_disp_cat
  := λ _ _ F A,
    algebra_cleaving_algebra F A ,,
    algebra_cleaving_morphism F A ,,
    algebra_cleaving_is_cartesian F A.

Definition algebra_fibration
  : fibration algebraic_theory_cat
  := _ ,, algebra_cleaving.


(** * 3. A characterization of iso's of algebras *)

Section Iso.

  Context (T : algebraic_theory).
  Context (A A' : algebra T).
  Context (F : z_iso (C := HSET) (A : hSet) (A' : hSet)).
  Context (Haction : ∏ n f a, mor_action_ax (identity T) (z_iso_mor F) (@action T A) (@action T A') n f a).

  Definition make_algebra_z_iso_mor
    : algebra_morphism A A'
    := make_algebra_morphism _ Haction.

  Definition make_algebra_z_iso_inv_data
    : A' → A
    := inv_from_z_iso F.

  Lemma make_algebra_z_iso_inv_action_ax
    : ∏ n f a, mor_action_ax (identity T) make_algebra_z_iso_inv_data (@action T A') (@action T A) n f a.
  Proof.
    intros n f a.
    refine (!_ @ maponpaths (λ x, x _) (z_iso_inv_after_z_iso F)).
    apply (maponpaths (inv_from_z_iso F)).
    refine (Haction _ _ _ @ _).
    apply maponpaths.
    apply funextfun.
    intro i.
    apply (eqtohomot (z_iso_after_z_iso_inv F)).
  Qed.

  Definition make_algebra_z_iso_inv
    : algebra_morphism A' A
    := make_algebra_morphism _ make_algebra_z_iso_inv_action_ax.

  Lemma make_algebra_z_iso_is_iso
    : is_inverse_in_precat (C := algebra_cat T)
      make_algebra_z_iso_mor
      make_algebra_z_iso_inv.
  Proof.
    split;
      apply algebra_morphism_eq;
      refine (algebra_mor_comp _ _ @ _).
    - apply (z_iso_inv_after_z_iso F).
    - apply (z_iso_after_z_iso_inv F).
  Qed.

  Definition make_algebra_z_iso
    : z_iso (C := algebra_cat T) A A'
    := make_z_iso (C := algebra_cat T)
      make_algebra_z_iso_mor
      make_algebra_z_iso_inv
      make_algebra_z_iso_is_iso.

End Iso.

(** * 4. Algebra pullback functor along an algebraic theory morphism *)

Section Pullback.

  Context {T T' : algebraic_theory}.
  Context (F : algebraic_theory_morphism T T').

  Section Ob.

    Context (A : algebra T').

    Definition algebra_pullback_ob_data
      : algebra_data T
      := make_algebra_data
        A
        (λ n f a, action (F _ f) a).

    Lemma algebra_pullback_ob_is_algebra
      : is_algebra algebra_pullback_ob_data.
    Proof.
      use make_is_algebra.
      - intros m n f g a.
        refine (maponpaths (λ x, action (A := A) x a) (mor_subst _ _ _) @ _).
        apply subst_action.
      - intros n i a.
        refine (maponpaths (λ x, action (A := A) x a) (mor_var _ _) @ _).
        apply var_action.
    Qed.

    Definition algebra_pullback_ob
      : algebra T
      := make_algebra _ algebra_pullback_ob_is_algebra.

  End Ob.

  Section Mor.

    Context {A A' : algebra T'}.
    Context (G : algebra_morphism A A').

    Definition algebra_pullback_mor_data
      : algebra_pullback_ob A → algebra_pullback_ob A'
      := G.

    Lemma algebra_pullback_mor_is_morphism
      : is_algebra_morphism algebra_pullback_mor_data.
    Proof.
      do 3 intro.
      apply (mor_action G).
    Qed.

    Definition algebra_pullback_mor
      : algebra_morphism (algebra_pullback_ob A) (algebra_pullback_ob A')
      := make_algebra_morphism _ algebra_pullback_mor_is_morphism.

  End Mor.

  Definition algebra_pullback_data
    : functor_data (algebra_cat T') (algebra_cat T)
    := make_functor_data
      algebra_pullback_ob
      (λ _ _, algebra_pullback_mor).

  Lemma algebra_pullback_is_functor
    : is_functor algebra_pullback_data.
  Proof.
    split.
    - intro A.
      now apply algebra_morphism_eq.
    - intros A A' A'' f g.
      apply algebra_morphism_eq.
      refine (_ @ !algebra_mor_comp _ _).
      refine (pr1_transportf (B := λ _, _ → _) _ _ @ _).
      exact (maponpaths (λ z, z _) (transportf_const _ _)).
  Qed.

  Definition algebra_pullback
    : algebra_cat T' ⟶ algebra_cat T
    := make_functor
      algebra_pullback_data
      algebra_pullback_is_functor.

End Pullback.
