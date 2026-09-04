(**

 Some examples of sections

 This file contains some elementary examples of sections.

 Content
 1. Coercing sections along a triangle
 2. Pullbacks of sections

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Local Open Scope cat.

(** * 1. Coercing sections along a triangle *)
Proposition coerce_section_of_mor_eq
            {C : category}
            {x y z : C}
            {f : x --> z}
            {g : y --> z}
            (h : x --> y)
            (p : h · g = f · identity _)
            (s : section_of_mor f)
  : s · h · g = identity z.
Proof.
  rewrite !assoc'.
  rewrite p.
  rewrite id_right.
  apply section_of_mor_eq.
Qed.

Definition coerce_section_of_mor
           {C : category}
           {x y z : C}
           {f : x --> z}
           {g : y --> z}
           (h : x --> y)
           (p : h · g = f · identity _)
           (s : section_of_mor f)
  : section_of_mor g.
Proof.
  use make_section_of_mor.
  - exact (s · h).
  - exact (coerce_section_of_mor_eq h p s).
Defined.

(** * 2. Pullbacks of sections *)
Proposition section_of_mor_pullback_pb_eq
            {C : category}
            {x y z : C}
            {f : x --> z}
            {g : y --> z}
            (P : Pullback f g)
            (s : section_of_mor f)
  : g · s · f = identity y · g.
Proof.
  rewrite id_left.
  rewrite !assoc'.
  rewrite section_of_mor_eq.
  apply id_right.
Qed.

Definition section_of_mor_pullback
           {C : category}
           {x y z : C}
           {f : x --> z}
           {g : y --> z}
           (P : Pullback f g)
           (s : section_of_mor f)
  : section_of_mor (PullbackPr2 P).
Proof.
  use make_section_of_mor.
  - use PullbackArrow.
    + exact (g · s).
    + apply identity.
    + exact (section_of_mor_pullback_pb_eq P s).
  - apply PullbackArrow_PullbackPr2.
Defined.
