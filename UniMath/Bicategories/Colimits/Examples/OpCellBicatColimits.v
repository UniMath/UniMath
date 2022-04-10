(*****************************************************************

 Colimits in op2 bicat

 Contents:
 1. Biinitial object
 2. Coproducts
 3. Extensive
 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInOp2Bicat.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.
Require Import UniMath.Bicategories.Colimits.Extensive.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.CommaObjects.
Require Import UniMath.Bicategories.Limits.Examples.OpCellBicatLimits.

Local Open Scope cat.

(**
 1. Biinitial object
 *)
Section OpCellBiinitial.
  Context {B : bicat}
          (b : B)
          (H : is_biinitial b).

  Definition op_cell_is_biinitial
    : @is_biinitial (op2_bicat B) b.
  Proof.
    use make_is_biinitial.
    - exact (λ y, is_biinitial_1cell_property H y).
    - exact (λ y f g, is_biinitial_2cell_property H _ g f).
    - exact (λ y f g α β, is_biinitial_eq_property H _ _ _ α β).
  Defined.
End OpCellBiinitial.

Definition op_cell_biinitial
           {B : bicat}
           (I : biinitial_obj B)
  : biinitial_obj (op2_bicat B)
  := pr1 I ,, op_cell_is_biinitial _ (pr2 I).

(**
 2. Coproducts
 *)
Section OpCellCoproduct.
  Context {B : bicat}
          {b₁ b₂ s : B}
          (ι₁ : b₁ --> s)
          (ι₂ : b₂ --> s)
          (cocone := make_bincoprod_cocone s ι₁ ι₂)
          (ump : has_bincoprod_ump cocone).

  Definition op_cell_cocone
    : @bincoprod_cocone (op2_bicat B) b₁ b₂
    := make_bincoprod_cocone s ι₁ ι₂.

  Definition has_bincoprod_ump_1_op_cell
             (q : @bincoprod_cocone (op2_bicat B) b₁ b₂)
    : bincoprod_1cell op_cell_cocone q.
  Proof.
    pose (k₁ := bincoprod_cocone_inl q).
    pose (k₂ := bincoprod_cocone_inr q).
    use make_bincoprod_1cell.
    - exact (bincoprod_ump_1cell ump k₁ k₂).
    - apply weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell (bincoprod_ump_1cell_inl ump _ k₁ k₂)).
    - apply weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell (bincoprod_ump_1cell_inr ump _ k₁ k₂)).
  Defined.

  Definition has_bincoprod_ump_2_op_cell
    : bincoprod_ump_2 op_cell_cocone.
  Proof.
    intros q φ ψ α β.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         exact (bincoprod_ump_2cell_unique_alt
                  ump
                  _ _
                  (pr12 φ₁ @ !(pr12 φ₂))
                  (pr22 φ₁ @ !(pr22 φ₂)))).
    - simple refine (_ ,, _ ,, _).
      + exact (bincoprod_ump_2cell ump α β).
      + exact (bincoprod_ump_2cell_inl ump α β).
      + exact (bincoprod_ump_2cell_inr ump α β).
  Defined.

  Definition has_bincoprod_ump_op_cell
    : has_bincoprod_ump op_cell_cocone.
  Proof.
    split.
    - exact has_bincoprod_ump_1_op_cell.
    - exact has_bincoprod_ump_2_op_cell.
  Defined.
End OpCellCoproduct.

Definition op2_bicat_has_bincoprod
           {B : bicat}
           (HB : has_bincoprod B)
  : has_bincoprod (op2_bicat B)
  := λ x y, _ ,, has_bincoprod_ump_op_cell _ _ (pr2 (HB x y)).

Definition op2_bicat_biinitial_coproduct
           (B : bicat_with_biinitial_bincoprod)
  : bicat_with_biinitial_bincoprod
  := op2_bicat B ,, op_cell_biinitial (pr12 B) ,, op2_bicat_has_bincoprod (pr22 B).

(**
 3. Extensive
 *)
Definition op2_bicat_is_extensive
           (B : bicat_with_biinitial_bincoprod)
           (HB : is_extensive B)
  : is_extensive (op2_bicat_biinitial_coproduct B).
Proof.
  intros x y.
  split.
  - simple refine (_ ,, _ ,, _ ,, _).
    + apply fully_faithful_op2_bicat.
      exact (pr1 (pr1 (HB x y))).
    + apply fully_faithful_op2_bicat.
      exact (pr12 (pr1 (HB x y))).
    + exact (op2_comma_has_comma_ump (pr222 (pr1 (HB x y)))).
    + exact (op2_comma_has_comma_ump (pr122 (pr1 (HB x y)))).
  - intros z h.
    pose (H := pr2 (HB x y) z h).
    refine (pr1 H ,, pr12 H ,, pr122 H ,, _).
    refine (pr1 (pr222 H) ,, pr12 (pr222 H) ,, pr122 (pr222 H) ,, _).
    refine (weq_op2_invertible_2cell
              _ _
              (inv_of_invertible_2cell (pr1 (pr222 (pr222 H))))
            ,,
            _).
    refine (weq_op2_invertible_2cell
              _ _
              (inv_of_invertible_2cell (pr12 (pr222 (pr222 H))))
            ,,
            _).
    simple refine (_ ,, _ ,, _).
    + exact (to_op2_has_pb_ump _ (pr122 (pr222 (pr222 H)))).
    + exact (to_op2_has_pb_ump _ (pr1 (pr222 (pr222 (pr222 H))))).
    + exact (has_bincoprod_ump_op_cell _ _ (pr2 (pr222 (pr222 (pr222 H))))).
Defined.
