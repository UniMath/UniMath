(** Author: Floris van Doorn, december 2017 *)
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.MoreFoundations.Subtypes.

(** Graphs.

Contents:
- paths in a graph (called gpaths to disambiguate from the identity type)
- operations on paths
*)


(** In this file we consider graphs with a type of vertices and a type of edges between any pair of
   vertices. We could restrict to sets, but there is no reason to do that here. *)

Definition issymmetric {V : UU} (E : V → V → UU) : UU :=
  ∏u v, E u v ≃ E v u.

Definition gpaths_of_length {V : UU} (E : V → V → UU) (v w : V) (n : nat) : UU.
Proof.
  revert v. induction n as [|n IH].
  - intro v. exact (v = w).
  - intro v. exact (∑u, E v u × IH u).
Defined.

Definition gpaths {V : UU} (E : V → V → UU) (v w : V) : UU :=
  ∑n, gpaths_of_length E v w n.

Definition nil {V : UU} {E : V → V → UU} (v : V) : gpaths E v v :=
  (0,, idpath v).

Definition cons {V : UU} {E : V → V → UU} {w u v : V} (e : E u v) (p : gpaths E v w) : gpaths E u w :=
  (S (pr1 p),, (v,, (e,, pr2 p))).

Local Notation "[]" := (nil _) (at level 0, format "[]").
Local Infix "::" := cons.

Lemma gpaths_ind {V : UU} {E : V → V → UU} {w : V} (P : ∏{u}, gpaths E u w → UU)
      (H1 : P []) (H2 : ∏{u v} (e : E u v) (p : gpaths E v w), P p → P (e :: p))
      {u : V} (p : gpaths E u w) : P p.
Proof.
  induction p as [n p]. revert u p. induction n as [|n IH].
  - induction p. exact H1.
  - induction p as [v x]. induction x as [e p]. apply (H2 _ _ _ (n,, p)).
    apply IH.
Defined.

Definition foldr {V : UU} {E : V → V → UU} {w : V} {B : V → UU} (f : ∏{u v}, E u v → B v → B u)
           (b : B w) : ∏{u : V}, gpaths E u w → B u.
Proof. apply gpaths_ind. exact b. exact (λ u v e _ b, f u v e b). Defined.

Definition concat {V : UU} {E : V → V → UU} {u v w : V} (p : gpaths E u v) (q : gpaths E v w) :
  gpaths E u w :=
  foldr (λ _ _ , cons) q p.

Local Infix "++" := concat.

Definition append {V : UU} {E : V → V → UU} {u v w : V} (p : gpaths E u v) (e : E v w) :
  gpaths E u w :=
  p ++ e::[].

Definition reverse {V : UU} {E : V → V → UU} (H : issymmetric E) {u v : V} (p : gpaths E u v) :
  gpaths E v u.
Proof.
  revert u p. apply gpaths_ind.
  - exact [].
  - intros u u' e p q. exact (append q (invmap (H u' u) e)).
Defined.

Definition symmetric_closure {V : UU} (E : V → V → UU) (u v : V) : UU :=
E u v ⨿ E v u.

Definition issymmetric_symmetric_closure {V : UU} (E : V → V → UU) :
  issymmetric (symmetric_closure E) :=
  λ u v, weqcoprodcomm (E u v) (E v u).

Definition reverse_in_closure {V : UU} {E : V → V → UU} {u v : V}
           (p : gpaths (symmetric_closure E) u v) : gpaths (symmetric_closure E) v u :=
  reverse (issymmetric_symmetric_closure E) p.
