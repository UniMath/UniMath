(**************************************************************************************************

  The category of algebraic theory algebras

  Defines the category of algebras for an algebraic theory. First, the category of dependent pairs
  of theories and algebras is formalized as a stack of displayed categories, then the category of
  algebras is a fiber of a (repeated) sigma category of this.

  Contents
  1. The dependent product category of theories and algebras [algebra_full_cat]
  1.1. The full category of algebra data [algebra_data_full_cat]
  1.1.1. Temporary accessors
  1.2. The full category of algebras
  1.2.1. A lemma about algebras [isaprop_full_is_algebra]
  2. The category of algebras [algebra_cat]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Section AlgebraCategory.

(** * 1. The dependent product category of theories and algebras *)
(** ** 1.1. The full category of algebra data *)

  Definition action_ax
    (T : algebraic_theory)
    (A : hSet)
    (n : nat)
    (f : T n)
    (a : stn n → A)
    : UU
    := A.

  Definition mor_action_ax
    {T T' : algebraic_theory}
    {A A' : hSet}
    (F : algebraic_theory_morphism T T')
    (G : A → A')
    (action : ∏ n f a, action_ax T A n f a)
    (action' : ∏ n f a, action_ax T' A' n f a)
    (n : nat)
    (f : T n)
    (a : stn n → A)
    : UU
    := G (action n f a) = action' n (F _ f) (λ i, G (a i)).

  Definition algebra_data_full_disp_cat
    : disp_cat (cartesian' algebraic_theory_cat HSET).
  Proof.
    use disp_struct.
    - intro X.
      exact (∏ n f a, action_ax (pr1 X) (pr2 X) n f a).
    - intros X X' action action' Y.
      exact (∏ n f a, mor_action_ax (pr1 Y) (pr2 Y) action action' n f a).
    - abstract (
        intros;
        do 3 (apply impred_isaprop; intro);
        apply setproperty
      ).
    - abstract easy.
    - abstract (
        intros X X' X'' action action' action'' y y' Gcommutes G'commutes n f a;
        exact (maponpaths _ (Gcommutes _ _ _) @ G'commutes _ _ _)
      ).
  Defined.

  Definition algebra_data_full_cat : category
    := total_category algebra_data_full_disp_cat.

(** *** 1.1.1. Temporary accessors *)

  Let data_theory
    (A : algebra_data_full_cat)
    : algebraic_theory
    := pr11 A.

  Let data_set
    (A : algebra_data_full_cat)
    : hSet
    := pr21 A.

  Let data_action
    {A : algebra_data_full_cat}
    {n : nat}
    (f : data_theory A n)
    (a : stn n → data_set A)
    : action_ax _ _ n f a
    := pr2 A n f a.

  Let data_mor_theory
    {A A' : algebra_data_full_cat}
    (F : algebra_data_full_cat⟦A, A'⟧)
    : algebraic_theory_morphism (data_theory A) (data_theory A')
    := pr11 F.

  Let data_mor_set
    {A A' : algebra_data_full_cat}
    (F : algebra_data_full_cat⟦A, A'⟧)
    : data_set A → data_set A'
    := pr21 F.

  Let data_mor_action
    {A A' : algebra_data_full_cat}
    (F : algebra_data_full_cat⟦A, A'⟧)
    {n : nat}
    (f : data_theory A n)
    (a : stn n → data_set A)
    : mor_action_ax (data_mor_theory F) (data_mor_set F) (@data_action A) (@data_action A') n f a
    := pr2 F n f a.

(** ** 1.2. The full category of algebras *)

  Definition subst_action_ax
    (T : algebraic_theory)
    (A : hSet)
    (action : ∏ n f a, action_ax T A n f a)
    (m n : nat)
    (f : T m)
    (g : stn m → T n)
    (a : stn n → A)
    : UU
    := action n (f • g) a = action m f (λ i, action n (g i) a).

  Definition var_action_ax
    (T : algebraic_theory)
    (A : hSet)
    (action : ∏ n f a, action_ax T A n f a)
    (n : nat)
    (i : stn n)
    (a : stn n → A)
    : UU
    := action n (var i) a = a i.

  Definition full_is_algebra
    (A : algebra_data_full_cat)
    : UU
    := (∏ m n f g a, subst_action_ax _ _ (pr2 A) m n f g a) ×
      (∏ n i a, var_action_ax _ _ (pr2 A) n i a).

  Definition algebra_full_disp_cat
    : disp_cat algebra_data_full_cat
    := disp_full_sub algebra_data_full_cat full_is_algebra.

  Definition algebra_full_cat : category
    := total_category algebra_full_disp_cat.

(** *** 1.2.1. A lemma about algebras *)

  Lemma isaprop_full_is_algebra
    (A : algebra_data_full_cat)
    : isaprop (full_is_algebra A).
  Proof.
    repeat apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
      apply setproperty.
  Qed.

(** * 2. The category of algebras *)

  Definition algebra_disp_cat
    : disp_cat algebraic_theory_cat
    := sigma_disp_cat (sigma_disp_cat algebra_full_disp_cat).

  Definition algebra_cat
    (T : algebraic_theory)
    := fiber_category algebra_disp_cat T.

  Lemma displayed_algebra_morphism_eq
    {T T' : algebraic_theory}
    {F : algebraic_theory_morphism T T'}
    {A : algebra_cat T}
    {A' : algebra_cat T'}
    (G G' : (A : algebra_disp_cat _) -->[F] A')
    (H : pr1 G = pr1 G')
    : G = G'.
  Proof.
    refine (subtypePath _ H).
    intro x.
    use (isapropdirprod _ _ _ isapropunit).
    repeat (apply impred_isaprop; intro).
    apply setproperty.
  Qed.

End AlgebraCategory.

Arguments action_ax /.
Arguments mor_action_ax /.
Arguments subst_action_ax /.
Arguments var_action_ax /.
