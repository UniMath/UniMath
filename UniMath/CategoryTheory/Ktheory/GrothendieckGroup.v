(** Grothendieck groups of exact categories  *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Ktheory.ExactCategories.
Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Import AddNotation.
Local Open Scope addmonoid.
Local Notation "'π₀' X" := (pi0 X) (at level 40).
Definition component {X:Type} : X -> π₀ X := setquotpr (pathseqrel X).
Definition π₀_map {X Y:Type} : (X -> Y) -> (π₀ X -> π₀ Y)
  := λ f, setquotfun (pathseqrel X) (pathseqrel Y) f (λ x x', hinhfun (maponpaths f)).
Definition K_0_hrel (M:ExactCategory) : hrel (free_abgr (π₀ (ob M))).
Proof.
  set (toG := λ A:M, @free_abgr_unit (π₀ (ob M)) (component A)).
  exact (λ g h, ∃ E : ShortExactSequence M,
      g = toG (Ob2 E) ×
      h = toG (Ob1 E) + toG (Ob3 E)).
Defined.
Definition K_0 (M:ExactCategory) : abgr
  := presented_abgr (π₀ (ob M)) (K_0_hrel M).
Definition K_0_map {M N:ExactCategory} (F:ExactFunctor M N) : monoidfun (K_0 M) (K_0 N).
Proof.
  use (presented_abgrfun (π₀_map (functor_on_objects F))). intros g h.
  use hinhfun. intros [E [e e']]. exists (applyFunctorToShortExactSequence F E).
  now induction (!e), (!e').
Defined.
