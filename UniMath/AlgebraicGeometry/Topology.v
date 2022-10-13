(* Additional definitions and facts from topology. Maybe this should go in UniMath.Topology. *)

Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.Topology.Topology.

Local Open Scope subtype.

Section union.
  Context {X : TopologicalSpace}.

  Definition union_open_hsubtype (A : hsubtype Open) : hsubtype X :=
    union (λ U, ∃ H : isOpen U, A (U ,, H)).

  Lemma is_open_union_open_hsubtype (A : hsubtype Open) : isOpen (union_open_hsubtype A).
  Proof.
    apply isOpen_union. intros U HU.
    use (hinhuniv _ HU); intros H. exact (pr1 H).
  Qed.

  Definition union_open (A : hsubtype Open) : Open :=
    union_open_hsubtype A ,, is_open_union_open_hsubtype A.
End union.

Declare Scope open_scope.
Delimit Scope open_scope with open.
Open Scope open.

Notation "⋃ S" := (union_open S) (at level 100, no associativity) : open_scope.


Section union_facts.
  Context {X : TopologicalSpace}
          {A : hsubtype (@Open X)}.

  Lemma contained_in_union_open (U : A) :
    pr1 U ⊆ ⋃ A.
  Proof.
    intros x Hx. apply hinhpr. exists (pr1 U). use make_dirprod.
    - apply hinhpr. exists (pr21 U). exact (pr2 U).
    - exact Hx.
  Qed.

  Lemma hexists_open_neighborhood (p : carrier (⋃ A)):
    ∃ U : A, pr1 U (pr1 p).
  Proof.
    induction p as [p Hp]. simpl in Hp.
    use (hinhuniv _ Hp); intro Hu.
    induction Hu as [u Hu]. induction Hu as [Hu Hup].
    use (hinhfun _ Hu); intro H.
    induction H as [H HUu].
    exists (make_carrier _ _ HUu). exact Hup.
  Qed.
End union_facts.


Definition binary_intersection_open {X : TopologicalSpace} (u v : @Open X) : Open :=
  (λ x : X, u x ∧ v x) ,, isOpen_and _ _ (pr2 u) (pr2 v).

Notation "u ∩ v" := (binary_intersection_open u v)  (at level 40, left associativity) : open_scope.


Section intersection_facts.
  Context {X : TopologicalSpace} (u v : @Open X).

  Definition intersection_contained1 : (u ∩ v) ⊆ u :=
    λ _ Hx, pr1 Hx.

  Definition intersection_contained2 : (u ∩ v) ⊆ v :=
    λ _ Hx, pr2 Hx.
End intersection_facts.
