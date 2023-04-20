Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractCloneMorphisms.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Definition base_nat_trans
  (T T' : base_functor)
  : UU
  := T ⟹ T'.

Coercion base_nat_trans_to_nat_trans
  (T T' : base_functor)
  (F : base_nat_trans T T')
  : T ⟹ T'
  := F.

Definition pointed_functor_morphism
  (T T' : pointed_functor)
  : UU
  := ∑ (F : T ⟹ T'), F _ id_pr = id_pr.

Coercion pointed_functor_morphism_to_nat_trans {T T' : pointed_functor} (F : pointed_functor_morphism T T') : nat_trans T T' := pr1 F.

Definition algebraic_theory_data_morphism
  (T T' : algebraic_theory_data)
  : UU
  := ∑ (F : pointed_functor_morphism T T'), ∏ m n f g, (F n (f • g)) = (F m f) • (λ i, F n (g i)).

Coercion algebraic_theory_data_morphism_to_pointed_functor_morphism {T T' : algebraic_theory_data} (F : algebraic_theory_data_morphism T T') : pointed_functor_morphism T T' := pr1 F.

Definition algebraic_theory_morphism
  (T T' : algebraic_theory)
  : UU
  := algebraic_theory_data_morphism T T'.

(* Constructors for the algebraic theory morphism type *)


(* Defininig an algebraic theory morphism in another way *)
(* Definition make_algebraic_theory_morphism'
  (T T: )
  (C : abstract_clone_morphism)
  := abstract_clone_to_algebraic_theory. *)


(* Accessors for the properties of an algebraic theory *)

(* Accessors for the properties of an algebraic theory morphism *)


(* Definitions for the categories *)
Definition base_functor_category
  : category
  := [finite_set_skeleton_category, HSET].

Definition pointed_functor_disp_cat
  : disp_cat base_functor_category.
Proof.
  use disp_struct.
  - intro T.
    exact ((T : base_functor) 1 : hSet).
  - intros T T' Tdata T'data F.
    exact ((F : base_nat_trans _ _) _ Tdata = T'data).
  - abstract (intros; apply setproperty).
  - now intros.
  - intros T T' T'' e e' e'' F F' HF HF'.
    now rewrite (!HF'), (!HF).
Defined.

Definition pointed_functor_cat
  : category
  := total_category pointed_functor_disp_cat.

Definition algebraic_theory_data_disp_cat
  : disp_cat pointed_functor_cat.
Proof.
  use disp_struct.
  - exact (λ (T : pointed_functor), ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet)).
  - exact (λ T T' Tdata T'data (F : pointed_functor_morphism T T'),
      ∏ m n f g, (F _ (Tdata m n f g)) = T'data m n (F _ f) (λ i, F _ (g i))).
  - intros.
    repeat (apply impred_isaprop; intro).
    apply setproperty.
  - now intros.
  - intros T T' T'' Tdata T'data T''data F F' Fdata F'data.
    cbn.
    intros.
    now rewrite Fdata, F'data.
Defined.

Definition algebraic_theory_data_cat
  : category
  := total_category algebraic_theory_data_disp_cat.

Definition algebraic_theory_disp_cat
  : disp_cat algebraic_theory_data_cat.
Proof.
  use disp_struct.
  - exact is_algebraic_theory.
  - intros.
    exact unit.
  - intros.
    exact isapropunit.
  - now intros.
  - intros.
    exact tt.
Defined.

Definition algebraic_theory_cat
  : category
  := total_category algebraic_theory_disp_cat.
