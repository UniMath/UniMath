(** * A simple implementation of the maybe/option monad *)

Require Import UniMath.Foundations.All.

Definition maybe (A: UU):= A ⨿ unit.

Definition just {A: UU}: A → maybe A := ii1.

Definition nothing {A: UU}: maybe A := ii2 tt.

Context {A: UU}.

Theorem isasetmaybe (H: isaset A): isaset (maybe A).
Proof.
  apply isasetcoprod.
  - exact H.
  - exact isasetunit.
Defined.

Definition flatmap {B: UU} (f: A → maybe B): maybe A → maybe B
  := coprod_rect _ f (λ _, nothing).

Lemma flatmap_some {B: UU} (f: A → maybe B) (a: A)
  : flatmap f (just a) = f a.
Proof.
  apply idpath.
Defined.

Lemma flatmap_error {B: UU} (f: A → maybe B)
  : flatmap f nothing = nothing.
Proof.
  apply idpath.
Defined.

