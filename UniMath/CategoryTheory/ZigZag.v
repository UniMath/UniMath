From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac Batch Debug.
(*********************************************************************

 Zig-zags in categories

 A zig-zag in a category is a finite chain of morphisms like this

 x1 --> x2 <-- x3 --> x4 <-- x5

 In this file, we define the notion of zig-zags and a number of
 operations on them.

 Contents:
 1. Definition of zig-zags
 2. Constructors for zig-zags
 3. Action of functors on zig-zags
 4. Appending zig-zags
 5. Reversing zig-zags
 6. Zig-zags in groupoids give morphisms
 7. Examples of zig-zag notation

 *********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Groupoids.

Local Open Scope cat.

(**
 1. Definition of zig-zags
 *)
Definition zig_zag_of_length
           {C : category}
           (n : ℕ)
  : ∏ (x y : C), UU.
Proof.
  induction n as [ | n IHn ].
  - exact (λ x y, z_iso x y).
  - exact (λ x y, ∑ (z : C), ((x --> z) ⨿ (z --> x)) × IHn z y).
Defined.

Definition zig_zag
           {C : category}
           (x y : C)
  : UU
  := ∑ (n : ℕ), zig_zag_of_length n x y.

Definition length_of_zig_zag
           {C : category}
           {x y : C}
           (gs : zig_zag x y)
  : ℕ
  := pr1 gs.

(**
 2. Constructors for zig-zags
 *)
Definition empty_zig_zag
           {C : category}
           (x : C)
  : zig_zag x x
  := 0 ,, identity_z_iso x.

Notation "x ■" := (empty_zig_zag x) (at level 40) : cat.

Definition left_cons_zig_zag
           {C : category}
           {x z y : C}
           (f : x --> z)
           (gs : zig_zag z y)
  : zig_zag x y
  := 1 + length_of_zig_zag gs ,, (z ,, (inl f ,, pr2 gs)).

Notation "x -[ f ]-> gs" := (@left_cons_zig_zag _ x _ _ f gs)
                              (at level 41, right associativity) : cat.

Definition right_cons_zig_zag
           {C : category}
           {x z y : C}
           (f : z --> x)
           (gs : zig_zag z y)
  : zig_zag x y
  := 1 + length_of_zig_zag gs ,, (z ,, (inr f ,, pr2 gs)).

Notation "x <-[ f ]- gs" := (@right_cons_zig_zag _ x _ _ f gs)
                              (at level 41, right associativity) : cat.

(**
 3. Action of functors on zig-zags
 *)
Definition functor_on_zig_zag_of_length
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           {x y : C₁}
           {n : ℕ}
           (gs : zig_zag_of_length n x y)
  : zig_zag_of_length n (F x) (F y).
Proof.
  revert x y gs.
  induction n as [ | n IHn ].
  - intros x y gs.
    exact (functor_on_z_iso F gs).
  - intros x y gs.
    induction gs as [ z gs ].
    induction gs as [ g gs ].
    induction g as [ g | g ].
    + exact (F z ,, inl (#F g) ,, IHn _ _ gs).
    + exact (F z ,, inr (#F g) ,, IHn _ _ gs).
Defined.

Definition functor_on_zig_zag
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           {x y : C₁}
           (gs : zig_zag x y)
  : zig_zag (F x) (F y)
  := length_of_zig_zag gs ,, functor_on_zig_zag_of_length F (pr2 gs).

(**
 4. Appending zig-zags
 *)
Definition precomp_z_iso_zig_zag_of_length
           {C : category}
           {n : ℕ}
           {x y z : C}
           (fs : zig_zag_of_length n y z)
           (i : z_iso x y)
  : zig_zag_of_length n x z.
Proof.
  revert x y z fs i.
  induction n as [ | n IHn ].
  - intros x y z fs i.
    exact (z_iso_comp i fs).
  - intros x y z fs i.
    induction fs as [ w fs ].
    induction fs as [ f fs ].
    induction f as [ f | f ].
    + exact (w ,, inl (i · f) ,, fs).
    + exact (w ,, inr (f · inv_from_z_iso i) ,, fs).
Defined.

Definition append_zig_zag_of_length
           {C : category}
           {n m : ℕ}
           {x y z : C}
           (fs : zig_zag_of_length n x y)
           (gs : zig_zag_of_length m y z)
  : zig_zag_of_length (n + m) x z.
Proof.
  revert x y z fs gs.
  induction n as [ | n IHn ].
  - intros x y z fs gs.
    exact (precomp_z_iso_zig_zag_of_length gs fs).
  - intros x y z fs gs.
    induction fs as [ w fs ].
    induction fs as [ f fs ].
    induction f as [ f | f ].
    + exact (w ,, inl f ,, IHn w y z fs gs).
    + exact (w ,, inr f ,, IHn w y z fs gs).
Defined.

Definition append_zig_zag
           {C : category}
           {x y z : C}
           (fs : zig_zag x y)
           (gs : zig_zag y z)
  : zig_zag x z
  := length_of_zig_zag fs + length_of_zig_zag gs
     ,,
     append_zig_zag_of_length (pr2 fs) (pr2 gs).

(**
 5. Reversing zig-zags
 *)
Definition post_cons_left_zig_zag_of_length
           {C : category}
           {n : ℕ}
           {x y z : C}
           (gs : zig_zag_of_length n x y)
           (f : y --> z)
  : zig_zag_of_length (S n) x z.
Proof.
  revert x y z gs f.
  induction n as [ | n IHn ].
  - intros x y z gs f.
    exact (z ,, inl (pr1 gs · f) ,, identity_z_iso z).
  - intros x y z gs f.
    induction gs as [ w gs ].
    induction gs as [ g gs ].
    induction g as [ g | g ].
    + exact (w ,, inl g ,, IHn _ _ _ gs f).
    + exact (w ,, inr g ,, IHn _ _ _ gs f).
Defined.

Definition post_cons_right_zig_zag_of_length
           {C : category}
           {n : ℕ}
           {x y z : C}
           (gs : zig_zag_of_length n x y)
           (f : z --> y)
  : zig_zag_of_length (S n) x z.
Proof.
  revert x y z gs f.
  induction n as [ | n IHn ].
  - intros x y z gs f.
    exact (z ,, inr (f · inv_from_z_iso gs) ,, identity_z_iso z).
  - intros x y z gs f.
    induction gs as [ w gs ].
    induction gs as [ g gs ].
    induction g as [ g | g ].
    + exact (w ,, inl g ,, IHn _ _ _ gs f).
    + exact (w ,, inr g ,, IHn _ _ _ gs f).
Defined.

Definition reverse_zig_zag_of_length
           {C : category}
           {n : ℕ}
           {x y : C}
           (gs : zig_zag_of_length n x y)
  : zig_zag_of_length n y x.
Proof.
  revert x y gs.
  induction n as [ | n IHn ].
  - intros x y gs.
    exact (z_iso_inv gs).
  - intros x y gs.
    induction gs as [ z gs ].
    induction gs as [ g gs ].
    induction g as [ g | g ].
    + exact (post_cons_right_zig_zag_of_length (IHn _ _ gs) g).
    + exact (post_cons_left_zig_zag_of_length (IHn _ _ gs) g).
Defined.

Definition reverse_zig_zag
           {C : category}
           {x y : C}
           (gs : zig_zag x y)
  : zig_zag y x
  := length_of_zig_zag gs ,, reverse_zig_zag_of_length (pr2 gs).

(**
 6. Zig-zags in groupoids give morphisms
 *)
Definition zig_zag_of_length_in_grpd_to_mor
           {G : groupoid}
           {n : ℕ}
           {x y : G}
           (gs : zig_zag_of_length n x y)
  : x --> y.
Proof.
  revert x y gs.
  induction n as [ | n IHn ].
  - intros x y gs.
    exact (pr1 gs).
  - intros x y gs.
    induction gs as [ z gs ].
    induction gs as [ g gs ].
    induction g as [ g | g ].
    + exact (g · IHn _ _ gs).
    + exact (inv_from_z_iso (g ,, pr2 G _ _ _) · IHn _ _ gs).
Defined.

Definition zig_zag_in_grpd_to_mor
           {G : groupoid}
           {x y : G}
           (gs : zig_zag x y)
  : x --> y
  := zig_zag_of_length_in_grpd_to_mor (pr2 gs).

(**
 7. Examples of zig-zag notation
 *)
Local Example zig_zag_notation_1
              {C : category}
              {w x y z : C}
              (f : w --> x)
              (g : y --> x)
              (h : y --> z)
  : zig_zag w z
  := w -[ f ]-> x <-[ g ]- y -[ h ]-> z ■.

Local Example zig_zag_notation_2
              {C : category}
              {w x y z : C}
              (f : w --> x)
              (g : x --> y)
              (h : z --> y)
  : zig_zag w z
  := w -[ f ]-> x -[ g ]-> y <-[ h ]- z ■.
