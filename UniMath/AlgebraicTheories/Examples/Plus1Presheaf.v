(**************************************************************************************************

  The "plus 1" presheaf

  Given a presheaf P, we can construct another presheaf P' with P'(n) = P(S n), in which the op
  of the algebraic theory leaves the last variable unchanged.

  Contents
  1. The definition of the plus 1 presheaf [plus_1_presheaf]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Presheaves.
Require Import UniMath.AlgebraicTheories.PresheafCategoryCore.
Require Import UniMath.Combinatorics.Tuples.

Local Open Scope algebraic_theories.

(** * 1. The definition of the plus 1 presheaf *)

Definition plus_1_presheaf_data
  {T : algebraic_theory}
  (P : presheaf T)
  : presheaf_data T.
Proof.
  use make_presheaf_data.
  - exact (λ n, P (1 + n)).
  - intros m n s t.
    refine (op (T := T) (P := P) s _).
    intro i.
    induction (invmap stnweq i) as [i' | i'].
    + refine (t i' • (λ j, var (stnweq (inl j)))).
    + exact (var (stnweq (inr i'))).
Defined.

Lemma plus_1_is_presheaf
  {T : algebraic_theory}
  (P : presheaf T)
  : is_presheaf (plus_1_presheaf_data P).
Proof.
  use make_is_presheaf.
  - intros l m n x f g.
    refine (op_op P x _ _ @ _).
    apply (maponpaths (op (x : P _))).
    apply funextfun.
    intro i.
    induction (invmap stnweq i) as [i' | i'].
    + refine (subst_subst T (f i') _ _ @ !_).
      refine (subst_subst T (f i') g _ @ !_).
      apply maponpaths.
      apply funextfun.
      intro.
      refine (var_subst _ _ _ @ _).
      exact (maponpaths _ (homotinvweqweq stnweq _)).
    + refine (var_subst _ _ _ @ _).
      exact (maponpaths _ (homotinvweqweq stnweq _)).
  - intros n x.
    refine (_ @ op_var _ _).
    apply (maponpaths (op (x : P _))).
    apply funextfun.
    intro i.
    refine (_ @ maponpaths _ (homotweqinvweq stnweq i)).
    induction (invmap stnweq i) as [i' | i'].
    + apply var_subst.
    + apply idpath.
Qed.

Definition plus_1_presheaf
  {T : algebraic_theory}
  (P : presheaf T)
: presheaf T
:= make_presheaf _ (plus_1_is_presheaf P).
