(** * Equations and equation algebra (varieties) *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Algebra.Universal.

Local Open Scope stn.
Local Open Scope nat.

Definition vsignature (sigma : signature) : signature
  := setcoprod (names sigma) natset,,
               sumofmaps (@arity sigma) (λ _, 0).

Definition vterm (sigma : signature) := term (vsignature sigma).

Definition var {sigma} (n : nat) : vterm sigma
  := build_term_curried (inr n : names (vsignature sigma)).

Definition equation (sigma : signature) : UU
  := vterm sigma × vterm sigma.

Definition lhs {sigma : signature} : equation sigma → vterm sigma := pr1.
Definition rhs {sigma : signature} : equation sigma → vterm sigma := pr2.

Section Evaluation.

  Context {sigma : signature}.

  Definition fromvterm {A:UU}
             (R : (∏ (nm : names sigma), Vector A (arity nm) → A))
             (Q : nat → A)
    : vterm sigma → A.
  Proof.
    refine (@fromterm (vsignature sigma) A _).
    induction nm as [nm | nm].
    - exact (R nm).
    - exact (λ rec, Q nm).
  Defined.

  Definition vsubst (f:nat -> term sigma)
    : vterm sigma → term sigma
    := fromvterm (λ nm , build_term nm) f.

  Definition veval (a : algebra sigma) (f:nat->support a)
    : vterm sigma → support a
    := fromvterm (λ nm rec, op a nm rec) f.

  Definition holds (a:algebra sigma) (e:equation sigma)
    : UU
    := ∏ f, veval a f (lhs e) = veval a f (rhs e).

End Evaluation.

Definition sysequations (sigma : signature) : UU
  := ∑ E : hSet, E → equation sigma.

Definition eqidx {sigma : signature} : sysequations sigma → hSet := pr1.
Coercion eqidx : sysequations >-> hSet.

Definition geteq {sigma : signature} {sys : sysequations sigma}
  : sys → equation sigma
  := pr2 sys.

Definition eqsignature : UU
  := ∑ sigma : signature, sysequations sigma.

Definition signature_of_eqsignature : eqsignature → signature := pr1.
Coercion signature_of_eqsignature : eqsignature >-> signature.

Definition eqs (sigma : eqsignature) : sysequations sigma := pr2 sigma.

Definition is_eqalgebra {sigma : eqsignature} (a : algebra sigma) : UU
  := ∏ e : eqs sigma, holds a (geteq e).

Definition eqalgebra (sigma : eqsignature) : UU
  := ∑ a : algebra sigma, is_eqalgebra a.

Definition algebra_of_eqalgebra {sigma : eqsignature}
  : eqalgebra sigma -> algebra sigma
  := pr1.
Coercion algebra_of_eqalgebra : eqalgebra >-> algebra.

Definition eqalgebra_is_eqalgebra {sigma : eqsignature} (a : eqalgebra sigma)
  : is_eqalgebra a
  := pr2 a.
