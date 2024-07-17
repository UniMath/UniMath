(**********************************************************************************************

 Lattices from posets

 One can construct a poset from a lattice if there is a suitable minimum and maximum operation.
 The difference lies in how the laws are phrased. A lattice is given by an equational theory:
 this means that we have laws (associativity, commutativity, and absorbption) that are equational.
 However, in this file, we consider laws that are phrased using the order of the poset.

 Content
 1. Minimum and maximum operations in posets
 2. Lattices from posets

 **********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Lattice.Lattice.
Require Import UniMath.OrderTheory.Lattice.Bounded.

Local Open Scope poset.

(** * 1. Minimum and maximum operations in posets *)
Definition min_operation
           (X : Poset)
  : UU
  := ∏ (x y : X),
     ∑ (m : X),
     m ≤ x
     ×
     m ≤ y
     ×
     ∏ (z : X), z ≤ x → z ≤ y → z ≤ m.

Definition min_op
           {X : Poset}
           (min : min_operation X)
           (x y : X)
  : X
  := pr1 (min x y).

Proposition min_op_l
            {X : Poset}
            (min : min_operation X)
            (x y : X)
  : min_op min x y ≤ x.
Proof.
  exact (pr12 (min x y)).
Qed.

Proposition min_op_r
            {X : Poset}
            (min : min_operation X)
            (x y : X)
  : min_op min x y ≤ y.
Proof.
  exact (pr122 (min x y)).
Qed.

Proposition le_min_op
            {X : Poset}
            (min : min_operation X)
            {x y z : X}
            (p : z ≤ x)
            (q : z ≤ y)
  : z ≤ min_op min x y.
Proof.
  exact (pr222 (min x y) z p q).
Qed.

Definition max_operation
           (X : Poset)
  : UU
  := ∏ (x y : X),
     ∑ (m : X),
     x ≤ m
     ×
     y ≤ m
     ×
     ∏ (z : X), x ≤ z → y ≤ z → m ≤ z.

Definition max_op
           {X : Poset}
           (max : max_operation X)
           (x y : X)
  : X
  := pr1 (max x y).

Proposition max_op_l
            {X : Poset}
            (max : max_operation X)
            (x y : X)
  : x ≤ max_op max x y.
Proof.
  exact (pr12 (max x y)).
Qed.

Proposition max_op_r
            {X : Poset}
            (max : max_operation X)
            (x y : X)
  : y ≤ max_op max x y.
Proof.
  exact (pr122 (max x y)).
Qed.

Proposition max_op_le
            {X : Poset}
            (max : max_operation X)
            {x y z : X}
            (p : x ≤ z)
            (q : y ≤ z)
  : max_op max x y ≤ z.
Proof.
  exact (pr222 (max x y) z p q).
Qed.

Definition min_el
           (X : Poset)
  : UU
  := ∑ (x : X), ∏ (y : X), x ≤ y.

Coercion min_el_to_el
         {X : Poset}
         (m : min_el X)
  : X.
Proof.
  exact (pr1 m).
Defined.

Proposition is_min_min_el
            {X : Poset}
            (m : min_el X)
            (y : X)
  : m ≤ y.
Proof.
  exact (pr2 m y).
Qed.

Definition max_el
           (X : Poset)
  : UU
  := ∑ (x : X), ∏ (y : X), y ≤ x.

Coercion max_el_to_el
         {X : Poset}
         (m : max_el X)
  : X.
Proof.
  exact (pr1 m).
Defined.

Proposition is_max_max_el
            {X : Poset}
            (m : max_el X)
            (y : X)
  : y ≤ m.
Proof.
  exact (pr2 m y).
Qed.

(** * 2. Lattices from posets *)
Section FixAPoset.
  Context (X : Poset)
          (min : min_operation X)
          (max : max_operation X).

  Proposition poset_to_lattice_laws
    : islatticeop
        (min_op min)
        (max_op max).
  Proof.
    repeat split.
    - intros x y z.
      use isantisymm_posetRelation.
      + use le_min_op.
        * refine (istrans_posetRelation _ _ _ _ _ _) ; [ apply min_op_l | ].
          apply min_op_l.
        * use le_min_op.
          ** refine (istrans_posetRelation _ _ _ _ _ _) ; [ apply min_op_l | ].
             apply min_op_r.
          ** apply min_op_r.
      + use le_min_op.
        * use le_min_op.
          ** apply min_op_l.
          ** refine (istrans_posetRelation _ _ _ _ _ _) ; [ apply min_op_r | ].
             apply min_op_l.
        * refine (istrans_posetRelation _ _ _ _ _ _) ; [ apply min_op_r | ].
          apply min_op_r.
    - intros x y.
      use isantisymm_posetRelation.
      + use le_min_op.
        * apply min_op_r.
        * apply min_op_l.
      + use le_min_op.
        * apply min_op_r.
        * apply min_op_l.
    - intros x y z.
      use isantisymm_posetRelation.
      + use max_op_le.
        * use max_op_le.
          ** apply max_op_l.
          ** refine (istrans_posetRelation _ _ _ _ _ _) ; [ | apply max_op_r ].
             apply max_op_l.
        * refine (istrans_posetRelation _ _ _ _ _ _) ; [ | apply max_op_r ].
          apply max_op_r.
      + use max_op_le.
        * refine (istrans_posetRelation _ _ _ _ _ _) ; [ | apply max_op_l ].
          apply max_op_l.
        * use max_op_le.
          ** refine (istrans_posetRelation _ _ _ _ _ _) ; [ | apply max_op_l ].
             apply max_op_r.
          ** apply max_op_r.
    - intros x y.
      use isantisymm_posetRelation.
      + use max_op_le.
        * apply max_op_r.
        * apply max_op_l.
      + use max_op_le.
        * apply max_op_r.
        * apply max_op_l.
    - intros x y.
      use isantisymm_posetRelation.
      + apply min_op_l.
      + use le_min_op.
        * apply isrefl_posetRelation.
        * apply max_op_l.
    - intros x y.
      use isantisymm_posetRelation.
      + apply max_op_le.
        * apply isrefl_posetRelation.
        * apply min_op_l.
      + use max_op_l.
  Qed.

  Definition poset_to_lattice : lattice X.
  Proof.
    use make_lattice.
    - exact (min_op min).
    - exact (max_op max).
    - exact poset_to_lattice_laws.
  Defined.

  Context (bot : min_el X)
          (top : max_el X).

  Proposition poset_to_bounded_lattice_laws
    : bounded_latticeop poset_to_lattice bot top.
  Proof.
    repeat split ; intro x ; cbn ; use isantisymm_posetRelation.
    - use max_op_le.
      * apply is_min_min_el.
      * apply isrefl_posetRelation.
    - apply max_op_r.
    - apply min_op_r.
    - use le_min_op.
      * apply is_max_max_el.
      * apply isrefl_posetRelation.
  Qed.

  Definition poset_to_bounded_lattice
    : bounded_lattice X.
  Proof.
    use make_bounded_lattice.
    - exact poset_to_lattice.
    - exact bot.
    - exact top.
    - exact poset_to_bounded_lattice_laws.
  Defined.
End FixAPoset.
