From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
(***************************************************************************

 Connected categories and groupoids

 A category is called connected if it is inhabited and for every two objects
 there is a zig-zag between them. A groupoid is called connected if it is
 inhabited and if for every two objects there is a morphism between them.

 Note: these two notions are in general not a proposition. The reason for
 that is that the choice of the zig-zag or of the morphism is not required
 to be natural. As such, different choices do not have to be equal up to
 isomorphism.

 Contents
 1. Definition of connected categories
 2. Categories with a (weak) terminal object are connected
 3. Categories with a (weak) initial object are connected
 4. Connected groupoids and connected categories

 ***************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.ZigZag.

Local Open Scope cat.

(**
 1. Definition of connected categories
 *)
Definition connected_category
           (C : category)
  : UU
  := ob C × ∏ (x y : C), zig_zag x y.

Definition ob_of_connected_category
           {C : category}
           (H : connected_category C)
  : C
  := pr1 H.

Definition zig_zag_of_connected_category
           {C : category}
           (H : connected_category C)
           (x y : C)
  : zig_zag x y
  := pr2 H x y.

Definition make_connected_category
           {C : category}
           (c : C)
           (zs : ∏ (x y : C), zig_zag x y)
  : connected_category C
  := c ,, zs.

(**
 2. Categories with a (weak) terminal object are connected
 *)
Definition weakly_terminal_to_connected
           {C : category}
           (c : C)
           (fs : ∏ (w : C), w --> c)
  : connected_category C.
Proof.
  use make_connected_category.
  - exact c.
  - exact (λ x y, x -[ fs x ]-> c <-[ fs y ]- y ■).
Defined.

Definition terminal_to_connected
           {C : category}
           (T : Terminal C)
  : connected_category C.
Proof.
  use weakly_terminal_to_connected.
  - exact T.
  - exact (λ x, TerminalArrow T x).
Defined.

Definition HSET_connected_terminal
  : connected_category HSET.
Proof.
  use terminal_to_connected.
  exact TerminalHSET.
Defined.

(**
 3. Categories with a (weak) initial object are connected
 *)
Definition weakly_initial_to_connected
           {C : category}
           (c : C)
           (fs : ∏ (w : C), c --> w)
  : connected_category C.
Proof.
  use make_connected_category.
  - exact c.
  - exact (λ x y, x <-[ fs x ]- c -[ fs y ]-> y ■).
Defined.

Definition initial_to_connected
           {C : category}
           (I : Initial C)
  : connected_category C.
Proof.
  use weakly_initial_to_connected.
  - exact I.
  - exact (λ x, InitialArrow I x).
Defined.

Definition HSET_connected_initial
  : connected_category HSET.
Proof.
  use initial_to_connected.
  exact InitialHSET.
Defined.

(**
 4. Connected groupoids and connected categories
 *)
Definition connected_groupoid
           (G : groupoid)
  : UU
  := ob G × ∏ (x y : G), x --> y.

Definition ob_of_connected_groupoid
           {G : groupoid}
           (H : connected_groupoid G)
  : G
  := pr1 H.

Definition mor_of_connected_groupoid
           {G : groupoid}
           (H : connected_groupoid G)
           (x y : G)
  : x --> y
  := pr2 H x y.

Definition make_connected_groupoid
           {G : groupoid}
           (c : G)
           (zs : ∏ (x y : G), x --> y)
  : connected_groupoid G
  := c ,, zs.

Definition connected_groupoid_to_connected_category
           {G : groupoid}
           (H : connected_groupoid G)
  : connected_category G.
Proof.
  use make_connected_category.
  - exact (ob_of_connected_groupoid H).
  - exact (λ x y, x -[ mor_of_connected_groupoid H x y ]-> y ■).
Defined.

Definition connected_category_to_connected_groupoid
           {G : groupoid}
           (H : connected_category G)
  : connected_groupoid G.
Proof.
  use make_connected_groupoid.
  - exact (ob_of_connected_category H).
  - exact (λ x y, zig_zag_in_grpd_to_mor (zig_zag_of_connected_category H x y)).
Defined.

Definition unit_connected_category
  : connected_category unit_category.
Proof.
  apply connected_groupoid_to_connected_category.
  use make_connected_groupoid.
  - exact tt.
  - apply isapropunit.
Defined.
