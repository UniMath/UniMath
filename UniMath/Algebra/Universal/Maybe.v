(** * A simple implementation of the maybe/option monad *)

Require Import UniMath.Foundations.All.

Definition maybe (A: UU):= A ⨿ unit.

Definition just {A: UU}: A → maybe A := ii1.

Definition nothing {A: UU}: maybe A := ii2 tt.

Theorem isasetmaybe {A: UU} (H: isaset A): isaset (maybe A).
Proof.
  apply isasetcoprod.
  - exact H.
  - exact isasetunit.
Defined.

Definition flatmap {A B: UU} (f: A → maybe B): maybe A → maybe B
  := coprod_rect _ f (λ _, nothing).

Lemma flatmap_just {A B: UU} (f: A → maybe B) (a: A)
  : flatmap f (ii1 a) = f a.
Proof.
  apply idpath.
Defined.

Lemma flatmap_nothing {A B: UU} (f: A → maybe B)
  : flatmap f nothing = nothing.
Proof.
  apply idpath.
Defined.


Local Definition flatmap_comp {A B C: UU} {f: A → B} {g: B → C} {a: maybe A}:
   flatmap (λ x: B, just (g x)) (flatmap (λ y: A, just (f y)) a) = flatmap (λ y:A, just (g (f y))) a.
Proof.
   induction a as [a' | aerror]  ; apply idpath.
Defined.

Definition just_injectivity {A: UU}: ∏ (x y: A), just x = just y → x = y := ii1_injectivity.

Lemma flatmap_ind {A B: UU} (P: ∏ (x: maybe A),  UU): (P nothing) → (∏ a: A, P (just a)) → ∏ x: maybe A, P x.
Proof.
  intros Pnothing Pjust.
  induction x as [ok | error].
  - exact (Pjust ok).
  - induction error.
    exact Pnothing.
Defined.
