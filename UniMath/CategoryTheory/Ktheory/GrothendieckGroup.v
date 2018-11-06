(** Grothendieck groups of exact categories  *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Ktheory.ExactCategories.
Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Local Open Scope multmonoid.

Local Notation "'π₀' X" := (pi0 X) (at level 40).

Definition K_0 (M:ExactCategory) : abgr.
Proof.
  set (G := free_abgr (π₀ (ob M))).
  set (toG := λ A:M, @free_abgr_unit (π₀ (ob M)) (setquotpr (pathseqrel (ob M)) A)).
  set (R := λ g h:G, ∃ E : ShortExactSequence M,
                g = toG (Ob2 E) ×
                h = toG (Ob1 E) * toG (Ob3 E)).
  exact (presented_abgr (π₀ (ob M)) R).
Defined.

Definition K_0_map {M N:ExactCategory} (F:ExactFunctor M N) : monoidfun (K_0 M) (K_0 N).
Proof.
  use presented_abgrfun.


Defined.