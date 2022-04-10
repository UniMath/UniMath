(****************************************************************************

 Equifiers in bicategories

 Contents
 1. Cones
 2. The universal mapping property
 3. Bicategories with equifiers
 4. Equifiers are fully faithful

 ****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.

Local Open Scope cat.

Section Equifiers.
  Context {B : bicat}
          {b₁ b₂ : B}
          {f g : b₁ --> b₂}
          {α β : f ==> g}.

  (**
   1. Cones
   *)
  Definition equifier_cone
    : UU
    := ∑ (i : B)
         (m : i --> b₁),
       m ◃ α = m ◃ β.

  Definition make_equifier_cone
             (i : B)
             (m : i --> b₁)
             (α : m ◃ α = m ◃ β)
    : equifier_cone
    := i ,, m ,, α.

  Coercion equifier_cone_ob
           (cone : equifier_cone)
    : B
    := pr1 cone.

  Definition equifier_cone_pr1
             (cone : equifier_cone)
    : cone --> b₁
    := pr12 cone.

  Definition equifier_cone_eq
             (cone : equifier_cone)
    : equifier_cone_pr1 cone ◃ α = equifier_cone_pr1 cone ◃ β
    := pr22 cone.

  Definition equifier_1cell
             (cone₁ cone₂ : equifier_cone)
    : UU
    := ∑ (k : cone₁ --> cone₂),
       invertible_2cell
         (k · equifier_cone_pr1 cone₂)
         (equifier_cone_pr1 cone₁).

  Definition make_equifier_1cell
             {cone₁ cone₂ : equifier_cone}
             (k : cone₁ --> cone₂)
             (α : invertible_2cell
                    (k · equifier_cone_pr1 cone₂)
                    (equifier_cone_pr1 cone₁))
    : equifier_1cell cone₁ cone₂
    := k ,, α.

  Coercion equifier_1cell_mor
           {cone₁ cone₂ : equifier_cone}
           (u : equifier_1cell cone₁ cone₂)
    : cone₁ --> cone₂
    := pr1 u.

  Definition equifier_1cell_pr1
             {cone₁ cone₂ : equifier_cone}
             (u : equifier_1cell cone₁ cone₂)
    : invertible_2cell
        (u · equifier_cone_pr1 cone₂)
        (equifier_cone_pr1 cone₁)
    := pr2 u.

  (**
   2. The universal mapping property
   *)
  Section UniversalMappingProperty.
    Context (cone : equifier_cone).

    Definition has_equifier_ump_1
      : UU
      := ∏ (other_cone : equifier_cone),
         equifier_1cell other_cone cone.

    Definition has_equifier_ump_2
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (α : u₁ · equifier_cone_pr1 cone
                ==>
                u₂ · equifier_cone_pr1 cone),
         ∑ (ζ : u₁ ==> u₂),
         ζ ▹ equifier_cone_pr1 cone = α.

    Definition has_equifier_ump_eq
      : UU
      := ∏ (x : B)
           (u₁ u₂ : x --> cone)
           (α : u₁ · equifier_cone_pr1 cone
                ==>
                u₂ · equifier_cone_pr1 cone)
           (φ₁ φ₂ : u₁ ==> u₂)
           (q₁ : φ₁ ▹ equifier_cone_pr1 cone = α)
           (q₂ : φ₂ ▹ equifier_cone_pr1 cone = α),
         φ₁ = φ₂.

    Definition has_equifier_ump
      : UU
      := has_equifier_ump_1 × has_equifier_ump_2 × has_equifier_ump_eq.
  End UniversalMappingProperty.

  Section Projections.
    Context {cone : equifier_cone}
            (H : has_equifier_ump cone).

    Definition equifier_ump_mor
               {i : B}
               (m : i --> b₁)
               (p : m ◃ α = m ◃ β)
      : i --> cone
      := pr1 H (make_equifier_cone i m p).

    Definition equifier_ump_mor_pr1
               {i : B}
               (m : i --> b₁)
               (p : m ◃ α = m ◃ β)
      : invertible_2cell
          (equifier_ump_mor m p · equifier_cone_pr1 cone)
          m
      := equifier_1cell_pr1 (pr1 H (make_equifier_cone i m p)).

    Definition equifier_ump_cell
               {x : B}
               {u₁ u₂ : x --> cone}
               (ζ : u₁ · equifier_cone_pr1 cone
                    ==>
                    u₂ · equifier_cone_pr1 cone)
      : u₁ ==> u₂
      := pr1 (pr12 H x u₁ u₂ ζ).

    Definition equifier_ump_cell_pr1
               {x : B}
               {u₁ u₂ : x --> cone}
               (ζ : u₁ · equifier_cone_pr1 cone
                    ==>
                    u₂ · equifier_cone_pr1 cone)
      : equifier_ump_cell ζ ▹ equifier_cone_pr1 cone = ζ
      := pr2 (pr12 H x u₁ u₂ ζ).

    Definition equifier_ump_eq
               {x : B}
               {u₁ u₂ : x --> cone}
               (ζ : u₁ · equifier_cone_pr1 cone
                    ==>
                    u₂ · equifier_cone_pr1 cone)
               (φ₁ φ₂ : u₁ ==> u₂)
               (q₁ : φ₁ ▹ equifier_cone_pr1 cone = ζ)
               (q₂ : φ₂ ▹ equifier_cone_pr1 cone = ζ)
      : φ₁ = φ₂
      := pr22 H x u₁ u₂ ζ φ₁ φ₂ q₁ q₂.

    Definition equifier_ump_eq_alt
               {x : B}
               {u₁ u₂ : x --> cone}
               (ζ : u₁ · equifier_cone_pr1 cone
                    ==>
                    u₂ · equifier_cone_pr1 cone)
               (φ₁ φ₂ : u₁ ==> u₂)
               (q : φ₁ ▹ equifier_cone_pr1 cone
                    =
                    φ₂ ▹ equifier_cone_pr1 cone)
      : φ₁ = φ₂.
    Proof.
      use equifier_ump_eq.
      - exact (φ₁ ▹ equifier_cone_pr1 cone).
      - apply idpath.
      - exact (!q).
    Qed.
  End Projections.
End Equifiers.

Arguments equifier_cone {_ _ _} _ _.

(**
 3. Bicategories with equifiers
 *)
Definition has_equifiers
           (B : bicat)
  : UU
  := ∏ (b₁ b₂ : B)
       (f g : b₁ --> b₂)
       (α β : f ==> g),
     ∑ (i : B)
       (m : i --> b₁)
       (p : m ◃ α = m ◃ β),
     has_equifier_ump (make_equifier_cone i m p).

(**
 4. Equifiers are fully faithful
 *)
Definition equifier_faithful
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {α β : f ==> g}
           {i : B}
           (m : i --> b₁)
           (p :  m ◃ α = m ◃ β)
           (H : has_equifier_ump (make_equifier_cone i m p))
  : faithful_1cell m.
Proof.
  intros x g₁ g₂ β₁ β₂ q.
  use (equifier_ump_eq_alt H) ; cbn.
  - exact (β₁ ▹ m).
  - exact q.
Defined.

Definition equifier_fully_faithful
           {B : bicat}
           {b₁ b₂ : B}
           {f g : b₁ --> b₂}
           {α β : f ==> g}
           {i : B}
           (m : i --> b₁)
           (p :  m ◃ α = m ◃ β)
           (H : has_equifier_ump (make_equifier_cone i m p))
  : fully_faithful_1cell m.
Proof.
  use make_fully_faithful.
  - exact (equifier_faithful m p H).
  - intros z g₁ g₂ βf.
    simple refine (_ ,, _).
    + exact (equifier_ump_cell H βf).
    + exact (equifier_ump_cell_pr1 H βf).
Defined.
