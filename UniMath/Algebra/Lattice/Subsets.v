(** * Lattice of subsets *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Sets.
Require Import UniMath.MoreFoundations.Subtypes.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Lattice.Lattice.
Require Import UniMath.Algebra.Lattice.Bounded.
Require Import UniMath.Algebra.Lattice.Distributive.
Require Import UniMath.Algebra.Lattice.Complement.

Section Subsets.
  Context {X : hSet}.

  Definition intersection_binop : binop (subtype_set X).
  Proof.
    apply infinitary_op_to_binop; exact (@subtype_intersection X).
  Defined.

  Lemma isassoc_intersection_binop : isassoc intersection_binop.
  Proof.
    intros W Y Z.
    apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond.
    use dirprodpair; cbn; intros z f b; induction b; cbn in *.
    + (** [z ∈ W] *)
      exact (f true true).
    + intro b; induction b; cbn in *.
      * (** [z ∈ Y] *)
        exact (f true false).
      * (** [z ∈ Z] *)
        exact (f false).
    + intro b; induction b; cbn in *.
      * exact (f true).
      * exact (f false true).
    + exact (f false false).
  Qed.

  Lemma iscomm_intersection_binop : iscomm intersection_binop.
  Proof.
    intros ? ?; unfold intersection_binop, infinitary_op_to_binop; cbn.
    apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond.
    use dirprodpair; intro; cbn; intros f b; induction b.
    - exact (f false).
    - exact (f true).
    - exact (f false).
    - exact (f true).
  Qed.

  Definition union_binop : binop (subtype_set X).
  Proof.
    apply infinitary_op_to_binop; exact (@subtype_union X).
  Defined.

  Local Lemma squash_to_prop_ishinh {Y Q : UU} :
    ∥ Y ∥ → (Y → ∥ Q ∥) → ∥ Q ∥.
  Proof.
    intros z ?.
    apply (squash_to_prop z); [apply isapropishinh|].
    assumption.
  Qed.

  Lemma isassoc_union_binop : isassoc union_binop.
  Proof.
    intros ? ? ?.
    apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond.
    use dirprodpair; cbn; intros ? ain;
      apply (squash_to_prop_ishinh ain);
        clear ain; intro ain; induction ain as [b bin].
    - induction b; cbn in bin.
      + apply (squash_to_prop_ishinh bin); clear bin; intro bin.
        induction bin as [c cin].
        induction c.
        * apply hinhpr; exists true; assumption.
        * apply hinhpr; exists false; cbn in *.
          apply hinhpr; exists true; assumption.
      + do 2 (apply hinhpr; exists false); assumption.
    - induction b; cbn in bin.
      + do 2 (apply hinhpr; exists true); assumption.
      + apply (squash_to_prop_ishinh bin); clear bin; intro bin.
        induction bin as [c cin].
        induction c.
        * apply hinhpr; exists true; cbn in *.
          apply hinhpr; exists false; assumption.
        * apply hinhpr; exists false; assumption.
  Qed.

  Lemma iscomm_union_binop : iscomm union_binop.
    intros ? ?; unfold union_binop, infinitary_op_to_binop; cbn.
    apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond.
    use dirprodpair; intro; cbn; intros ain;
      apply (squash_to_prop_ishinh ain); clear ain; intro ain;
        induction ain as [b bin]; induction b; cbn in *;
          apply hinhpr.
    - exists false; assumption.
    - exists true; assumption.
    - exists false; assumption.
    - exists true; assumption.
  Qed.

  Lemma subset_lattice : lattice (subtype_set X).
  Proof.
    use mklattice.
    - exact intersection_binop. (** [Lmin] *)
    - exact union_binop. (** [Lmax] *)
    - (** TODO: constructor for this *)
      apply dirprodpair; [apply dirprodpair|apply dirprodpair; [apply dirprodpair|apply dirprodpair]].
      + apply isassoc_intersection_binop.
      + apply iscomm_intersection_binop.
      + apply isassoc_union_binop.
      + apply iscomm_union_binop.
      + intros ? ?.
        apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond.
        use dirprodpair.
        * intros ? f; exact (f true).
        * intros ? ?.
          intros b; induction b; cbn.
          -- assumption.
          -- apply hinhpr; exists true; assumption.
      + intros ? ?.
        apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond.
        use dirprodpair.
        * intros ? f; cbn in f.
          refine (hinhuniv _ f); clear f; intro f.
          induction f as [b bin]; induction b; cbn in bin.
          -- assumption.
          -- apply (bin true).
        * intros ? ?; apply hinhpr; exists true; assumption.
  Qed.

End Subsets.