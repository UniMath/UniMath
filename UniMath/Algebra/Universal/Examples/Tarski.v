(** Semantics for boolean formulas. **)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Bool.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.FiniteSets.

Require Import UniMath.Algebra.Universal.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.Equations.

Open Scope stn.

(** Boolean signature **)

Definition bool_signature := make_signature_simple_single_sorted [0; 0; 1; 2; 2; 2].

Definition Vars := make_varspec bool_signature natset (λ _, tt).
Definition σ := vsignature bool_signature Vars.
Definition T := vterm bool_signature Vars tt.

(** Terms and boolean operators **)

Definition bot    : T         := build_term_curried (inl (●0) : names σ).
Definition top    : T         := build_term_curried (inl (●1) : names σ).
Definition neg    : T → T     := build_term_curried (inl (●2) : names σ).
Definition conj   : T → T → T := build_term_curried (inl (●3) : names σ).
Definition disj   : T → T → T := build_term_curried (inl (●4) : names σ).
Definition impl   : T → T → T := build_term_curried (inl (●5) : names σ).

(** Boolean Algebra **)

Definition bool_algebra := make_algebra_simple_single_sorted bool_signature boolset
  [(
    λ _, false ;
    λ _, true ; 
    λ x, negb (pr1 x) ;
    λ x, andb (pr1 x) (pr12 x) ; 
    λ x, orb (pr1 x) (pr12 x) ;
    λ x, implb (pr1 x) (pr12 x)
  )].

(** Interpretation of propositional formulas **)

Definition interp (α: assignment bool_algebra Vars) (t: T) : bool :=
  fromvterm (ops bool_algebra) α tt t.

(** Computations and interactive proofs **)

Definition x : T := varterm (0: Vars).
Definition y : T := varterm (1: Vars).
Definition z : T := varterm (2: Vars).

(* x & (neg y & z)*)
Eval lazy in
    interp (λ n, match n with 0 => true | 1 => true | _ => false end)
           (conj x (conj (neg y) z)).

(* x & (z -> neg y)*)
Eval lazy in
    interp (λ n, match n with 0 => true | 1 => true | _ => false end)
           (conj x (impl z (neg y))).

(*Dummett tautology*)
Lemma Dummett : ∏ i, interp i (disj (impl x y) (impl y x)) = true.
Proof.
  intro i.
  lazy.
  induction (i 0). induction (i 1).
  - apply idpath.
  - apply idpath.
  - apply idpath.
Qed.

(* x or (neg(y & z -> x))*)
Lemma not_tautology : ∑ i, interp i (disj x (neg (impl (conj y z) x))) = false.
Proof.
  use tpair.
 - exact (λ n, match n with  _ => false end).
 - lazy.
   apply idpath.
Qed.




































(** Tests.
Eval lazy in interp f (conj x top).
Eval lazy in interp f (conj x y).
Eval lazy in interp f (disj x y).
Eval lazy in interp f (disj x (conj y bot)).

Definition f (n : nat) : bool.
Proof.
  induction n as [|n Hn].
  - exact true.
  - exact false.
Defined.**)
