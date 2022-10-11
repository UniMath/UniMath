(**
 Discrete morphisms in bicategories

 Contents:
 1. Conservative 1-cells
 2. Characterization of conservative 1-cells
 3. Pseudomonic 1-cells and fully faithful 1-cells are conservative
 4. Discrete 1-cells
 5. Pseudomonic and fully faithful 1-cells are discrete
 6. Conservative 1-cells in locally groupoidal bicategories
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.

Local Open Scope cat.

(**
 1. Conservative 1-cells
 *)
Definition conservative_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : UU
  := ∏ (x : B)
       (g₁ g₂ : x --> a)
       (α : g₁ ==> g₂),
     is_invertible_2cell (α ▹ f)
     →
     is_invertible_2cell α.

Definition conservative_1cell_reflect_iso
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : conservative_1cell f)
           {x : B}
           {g₁ g₂ : x --> a}
           (α : g₁ ==> g₂)
           (Hα : is_invertible_2cell (α ▹ f))
  : is_invertible_2cell α
  := Hf x g₁ g₂ α Hα.

Definition isaprop_conservative_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : isaprop (conservative_1cell f).
Proof.
  do 5 (use impred ; intro).
  apply isaprop_is_invertible_2cell.
Qed.

(**
 2. Characterization of conservative 1-cells
 *)
Definition conservative_1cell_to_conservative
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : conservative_1cell f)
           (x : B)
  : conservative (post_comp x f).
Proof.
  intros g₁ g₂ α Hα.
  apply is_inv2cell_to_is_z_iso.
  apply Hf.
  exact (z_iso_to_inv2cell (make_z_iso' _ Hα)).
Defined.

Definition conservative_to_conservative_1cell
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : ∏ (x : B), conservative (post_comp x f))
  : conservative_1cell f.
Proof.
  intros x g₁ g₂ α Hα.
  apply is_z_iso_to_is_inv2cell.
  apply Hf.
  apply is_inv2cell_to_is_z_iso.
  exact Hα.
Defined.

Definition conservative_1cell_weq_conservative
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : conservative_1cell f ≃ ∏ (x : B), conservative (post_comp x f).
Proof.
  use weqimplimpl.
  - exact conservative_1cell_to_conservative.
  - exact conservative_to_conservative_1cell.
  - exact (isaprop_conservative_1cell f).
  - use impred ; intro.
    apply isaprop_conservative.
Defined.

(**
 3. Pseudomonic and fully faithful 1-cells are conservative
 *)
Definition pseudomonic_is_conservative
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : pseudomonic_1cell f)
  : conservative_1cell f.
Proof.
  intros x g₁ g₂ α Hα.
  pose (H := is_invertible_2cell_pseudomonic_1cell_inv_map Hf (α ▹ f) Hα).
  use make_is_invertible_2cell.
  - exact (H^-1).
  - abstract
      (use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
       rewrite id2_left ;
       apply (pseudomonic_1cell_faithful Hf) ;
       exact (!(pseudomonic_1cell_inv_map_eq Hf (α ▹ f) Hα))).
  - abstract
      (use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
       rewrite id2_right ;
       apply (pseudomonic_1cell_faithful Hf) ;
       exact (!(pseudomonic_1cell_inv_map_eq Hf (α ▹ f) Hα))).
Defined.

Definition fully_faithful_to_conservative
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
  : conservative_1cell f.
Proof.
  apply pseudomonic_is_conservative.
  apply fully_faithful_is_pseudomonic.
  exact Hf.
Defined.

(**
 4. Discrete 1-cells
 *)
Definition discrete_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : UU
  := faithful_1cell f × conservative_1cell f.

Definition isaprop_discrete_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : isaprop (discrete_1cell f).
Proof.
  use isapropdirprod.
  - apply isaprop_faithful_1cell.
  - apply isaprop_conservative_1cell.
Qed.

(**
 5. Pseudomonic 1-cells and fully faithful 1-cells are discrete
 *)
Definition pseudomonic_is_discrete
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : pseudomonic_1cell f)
  : discrete_1cell f.
Proof.
  split.
  - exact (pseudomonic_1cell_faithful Hf).
  - exact (pseudomonic_is_conservative Hf).
Defined.

Definition fully_faithful_is_discrete
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
  : discrete_1cell f.
Proof.
  split.
  - exact (fully_faithful_1cell_faithful Hf).
  - exact (fully_faithful_to_conservative Hf).
Defined.

(**
 6. Conservative 1-cells in locally groupoidal bicategories
 *)
Definition conservative_1cell_locally_groupoid
           {B : bicat}
           (HB : locally_groupoid B)
           {a b : B}
           (f : a --> b)
  : conservative_1cell f.
Proof.
  intros x g₁ g₂ α Hα.
  apply HB.
Defined.

Definition discrete_1cell_weq_faithful_locally_groupoid
           {B : bicat}
           (HB : locally_groupoid B)
           {a b : B}
           (f : a --> b)
  : discrete_1cell f ≃ faithful_1cell f.
Proof.
  use weqimplimpl.
  - exact (λ Hf, pr1 Hf).
  - intro Hf.
    split.
    + exact Hf.
    + exact (conservative_1cell_locally_groupoid HB f).
  - apply isaprop_discrete_1cell.
  - apply isaprop_faithful_1cell.
Defined.
