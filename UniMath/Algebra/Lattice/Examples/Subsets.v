(** * Lattice of subsets *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Sets.
Require Export UniMath.MoreFoundations.Propositions.
Require Export UniMath.MoreFoundations.Subtypes.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Lattice.Lattice.
Require Import UniMath.Algebra.Lattice.Bounded.
Require Import UniMath.Algebra.Lattice.Distributive.
Require Import UniMath.Algebra.Lattice.Complement.
Require Import UniMath.Algebra.Lattice.Boolean.

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
    use make_dirprod; cbn; intros z f b; induction b; cbn in *.
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
    use make_dirprod; intro; cbn; intros f b; induction b.
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
    use make_dirprod; cbn; intros ? ain;
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
    use make_dirprod; intro; cbn; intros ain;
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
      apply make_dirprod; [apply make_dirprod|apply make_dirprod; [apply make_dirprod|apply make_dirprod]].
      + apply isassoc_intersection_binop.
      + apply iscomm_intersection_binop.
      + apply isassoc_union_binop.
      + apply iscomm_union_binop.
      + intros ? ?.
        apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond.
        use make_dirprod.
        * intros ? f; exact (f true).
        * intros ? ?.
          intros b; induction b; cbn.
          -- assumption.
          -- apply hinhpr; exists true; assumption.
      + intros ? ?.
        apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond.
        use make_dirprod.
        * intros ? f; cbn in f.
          refine (hinhuniv _ f); clear f; intro f.
          induction f as [b bin]; induction b; cbn in bin.
          -- assumption.
          -- apply (bin true).
        * intros ? ?; apply hinhpr; exists true; assumption.
  Defined.

  Lemma subset_lattice_is_bounded :
    bounded_latticeop subset_lattice (emptysubtype X) (totalsubtype X).
  Proof.
    (** TODO: constructor *)
    use make_dirprod.
    - intros x; cbn.
      apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond;
        use make_dirprod.
      + intros ? in_union.
        refine (hinhuniv _ in_union); clear in_union; intro in_union.
        induction in_union as [b bin]; induction b; cbn in bin.
        * induction bin. (* can't be in the empty subset *)
        * assumption.
      + intros ? ?; apply hinhpr; exists false; assumption.
    - intros x; cbn.
      apply (invweq (hsubtype_univalence _ _)), subtype_equal_cond;
        use make_dirprod.
      + intros ? in_intersection; exact (in_intersection false).
      + intros ? ? b; induction b; cbn.
        * exact tt. (* always in total subtype *)
        * assumption.
  Qed.

  (** Using [LEM], we can show the lattice is complemented *)
  Lemma subset_lattice_is_complemented :
    LEM -> complemented_structure (mkbounded_lattice subset_lattice_is_bounded).
  Proof.
    intros lem sub.
    exists (subtype_complement sub).
    use make_dirprod.
    - apply (invweq (hsubtype_univalence _ _)).
      apply (subtype_complement_union sub lem).
      + exists true; reflexivity.
      + exists false; reflexivity.
    - (** We don't need [LEM] for this branch. *)
      apply (invweq (hsubtype_univalence _ _)).
      apply (subtype_complement_intersection_empty sub).
      + exists true; reflexivity.
      + exists false; reflexivity.
  Defined.

  Definition subset_bounded_lattice : bounded_lattice (subtype_set X).
  Proof.
    use mkbounded_lattice.
    - exact subset_lattice.
    - exact (emptysubtype X).
    - exact (totalsubtype X).
    - exact subset_lattice_is_bounded.
  Defined.

  Lemma subset_lattice_is_distributive : is_distributive subset_lattice.
  Proof.
  Abort.

  Definition subset_lattice_is_boolean :
    LEM -> is_boolean subset_bounded_lattice.
  Proof.
    intros lem.
    use make_is_boolean.
    2: apply (subset_lattice_is_complemented lem).
  Abort.

End Subsets.