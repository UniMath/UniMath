(** * A simple implementation of the maybe/option monad which does not require category theory. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)

Require Import UniMath.Foundations.PartC.

Definition maybe (A: UU):= A ⨿ unit.

Definition just {A: UU}: A → maybe A := ii1.

Definition nothing {A: UU}: maybe A := ii2 tt.

Definition just_injectivity {A: UU}: ∏ (x y: A), just x = just y → x = y := ii1_injectivity.

Lemma isasetmaybe {A: UU} (H: isaset A): isaset (maybe A).
Proof.
  apply isasetcoprod.
  - exact H.
  - exact isasetunit.
Defined.

Definition flatmap {A B: UU} (f: A → maybe B): maybe A → maybe B
  := coprod_rect _ f (λ _, nothing).

Lemma flatmap_just {A B: UU} (f: A → maybe B) (a: A)
  : flatmap f (just a) = f a.
Proof.
  apply idpath.
Defined.

Lemma flatmap_nothing {A B: UU} (f: A → maybe B)
  : flatmap f nothing = nothing.
Proof.
  apply idpath.
Defined.

Lemma flatmap_ind {A B: UU} (P: ∏ (x: maybe A),  UU): (P nothing) → (∏ a: A, P (just a)) → ∏ x: maybe A, P x.
Proof.
  intros Pnothing Pjust.
  induction x as [ok | error].
  - exact (Pjust ok).
  - induction error.
    exact Pnothing.
Defined.
