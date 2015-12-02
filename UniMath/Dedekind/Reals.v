(** * A library about decidable Dedekind Cuts *)
(** Author: Catherine LELAY. Oct 2015 - *)
(** Additional results about Dedekind cuts which cannot be proved *)
(** without decidability *)

Require Import UniMath.Dedekind.Complements.
Require Import UniMath.Dedekind.Sets.
Require Import UniMath.Dedekind.NonnegativeRationals.
Require Export UniMath.Dedekind.NonnegativeReals.

Open Scope Dcuts_scope.

(** ** Definition *)

Definition hr_commrng : commrng := commrigtocommrng NonnegativeReals.

Definition NR_to_hr : NonnegativeReals × NonnegativeReals -> hr_commrng.
Proof.
  intros x.
  assert (Hx : ∀ y : NonnegativeReals × NonnegativeReals, isaprop (pr1 x + pr2 y = pr1 y + pr2 x)).
  { intros y ; apply (pr2 Dcuts_set). }
  exists (λ y, hProppair _ (Hx y)).
  split.
  - apply hinhpr.
    exists x ; simpl.
    reflexivity.
  - split.
    + intros x1 x2 H Heq.
      revert H ; apply hinhuniv ; intros (x0,H) ; simpl in * |- *.
      apply plusNonnegativeReals_eqcompat_r with x0.
Defined.

Definition hr_zero : hr_commrng := 0%rng.
Definition hr_one : hr_commrng := 1%rng.
Definition hr_plus : binop hr_commrng := λ x y, (x + y)%rng.
Definition hr_mult : binop hr_commrng := λ x y, (x * y)%rng.
