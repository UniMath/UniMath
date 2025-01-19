(*****************************************************************************************

 Companion pairs of adjoint equivalences

 We show that the companion of an adjoint equivalence is again an adjoint equivalence. For
 this, we assume the following that the vertical 2-cells correspond to squares.

 The idea behind the proof is as follows: if a Verity double bicategory has all companion
 pairs, then we have a pseudofunctor from the horizontal bicategory to the vertical
 bicategory which is the identity on objects and which sends every horizontal morphism to
 its companion. Since pseudofunctors preserve adjoint equivalences, we immediately obtain
 that the companion pair of an adjoint equivalence is again an adjoint equivalence.

 Concretely, we first construct an action on 2-cells of this pseudofunctor (which we do in
 [cell_are_companions]) and then on invertible 2-cells ([inv2cell_are_companions]). We show
 that this action preserves identities and compositions. We also use that the composition
 of companion pairs is given by composition of the vertical and horizontal morphism.

 Contents
 1. Cells between companion pairs
 2. Invertible 2-cells between companions
 3. Companions of adjoint equivalences
 4. Vertical equivalences in Verity double bicategories with all companions

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairs.

Local Open Scope cat.
Local Open Scope double_bicat.

(** * 1. Cells between companion pairs *)
Definition cell_are_companions
           {B : verity_double_bicat}
           (H : vertically_saturated B)
           {x y : B}
           {h₁ h₂ : x --> y}
           (τ : h₂ ==> h₁)
           {v₁ v₂ : x -|-> y}
           (c₁ : are_companions h₁ v₁)
           (c₂ : are_companions h₂ v₂)
  : v₁ ==> v₂
  := let φ₁ := unit_are_companions c₁ in
     let ψ₂ := τ ▿s counit_are_companions c₂ in
     square_to_vertical_cell H (linvunitor _ ◃s (runitor _ ▹s ψ₂ ⋆v φ₁)).

Proposition cell_are_companions_id
            {B : verity_double_bicat}
            (H : vertically_saturated B)
            {x y : B}
            {h : x --> y}
            {v : x -|-> y}
            (c : are_companions h v)
  : cell_are_companions H (id2 h) c c = id2 v.
Proof.
  unfold cell_are_companions.
  rewrite <- (square_to_vertical_cell_id H).
  apply maponpaths.
  rewrite dwhisker_square_id.
  rewrite are_companions_left'.
  rewrite <- rwhisker_square_comp.
  rewrite rinvunitor_runitor.
  rewrite rwhisker_square_id.
  rewrite <- lwhisker_square_comp.
  rewrite linvunitor_lunitor.
  rewrite lwhisker_square_id.
  apply idpath.
Qed.

Proposition cell_are_companions_comp
            {B : verity_double_bicat}
            (H : vertically_saturated B)
            {x y : B}
            {h₁ h₂ h₃ : x --> y}
            (τ₁ : h₂ ==> h₁)
            (τ₂ : h₃ ==> h₂)
            {v₁ v₂ v₃ : x -|-> y}
            (c₁ : are_companions h₁ v₁)
            (c₂ : are_companions h₂ v₂)
            (c₃ : are_companions h₃ v₃)
  : cell_are_companions H (τ₂ • τ₁) c₁ c₃
    =
    cell_are_companions H τ₁ c₁ c₂ • cell_are_companions H τ₂ c₂ c₃.
Proof.
  unfold cell_are_companions.
  rewrite <- square_to_vertical_cell_comp.
  apply maponpaths.
  unfold comp_ver_globular_square.
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    rewrite <- lwhisker_hcomp_square.
    apply maponpaths.
    rewrite <- rwhisker_lwhisker_square.
    rewrite <- rwhisker_hcomp_square.
    apply idpath.
  }
  rewrite <- lwhisker_dwhisker_square.
  rewrite <- lwhisker_uwhisker_square.
  apply maponpaths.
  rewrite <- rwhisker_dwhisker_square.
  rewrite <- rwhisker_uwhisker_square.
  apply maponpaths.
  etrans.
  {
    do 2 apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply lunitor_v_comp_square''.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply runitor_v_comp_square''.
    }
    rewrite <- rwhisker_hcomp_square.
    apply maponpaths.
    rewrite rwhisker_lwhisker_square.
    rewrite <- lwhisker_hcomp_square.
    apply maponpaths.
    rewrite lrwhisker_hcomp_square.
    rewrite <- rwhisker_square_comp.
    rewrite r_rwhisker_v_comp_square.
    rewrite <- rwhisker_square_comp.
    rewrite !vassocr.
    rewrite vcomp_lunitor.
    rewrite !vassocl.
    rewrite runitor_rinvunitor.
    rewrite id2_right.
    rewrite l_lwhisker_v_comp_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths.
      apply lassociator_v_comp_square'.
    }
    rewrite <- lrwhisker_hcomp_square.
    rewrite <- !lwhisker_square_comp.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- linvunitor_assoc.
      apply lunitor_linvunitor.
    }
    rewrite lwhisker_square_id.
    rewrite <- rwhisker_hcomp_square.
    apply maponpaths.
    rewrite double_bicat_interchange.
    rewrite double_bicat_interchange.
    rewrite l_dwhisker_h_comp_square.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply are_companions_right'.
    }
    rewrite uwhisker_id_v_square.
    rewrite <- !dwhisker_square_comp.
    rewrite <- ud_whisker_vcomp_square.
    rewrite lunitor_v_comp_square'.
    apply idpath.
  }
  rewrite r_rwhisker_v_comp_square.
  rewrite <- !rwhisker_lwhisker_square.
  rewrite <- !rwhisker_square_comp.
  rewrite r_lwhisker_v_comp_square.
  rewrite <- !lwhisker_square_comp.
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    rewrite <- runitor_triangle.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      apply id2_left.
    }
    rewrite runitor_lunitor_identity.
    rewrite lwhisker_vcomp.
    rewrite linvunitor_lunitor.
    apply lwhisker_id2.
  }
  rewrite rwhisker_square_id.
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    rewrite linvunitor_assoc.
    rewrite !vassocl.
    rewrite lunitor_lwhisker.
    rewrite runitor_lunitor_identity.
    rewrite rwhisker_vcomp.
    rewrite linvunitor_lunitor.
    apply id2_rwhisker.
  }
  rewrite lwhisker_square_id.
  rewrite ud_whisker_vcomp_square.
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpaths_2.
    rewrite r_dwhisker_h_comp_square.
    rewrite <- !dwhisker_square_comp.
    apply maponpaths_2.
    rewrite !vassocr.
    rewrite vcomp_lunitor.
    rewrite !vassocl.
    rewrite rwhisker_hcomp.
    rewrite <- rinvunitor_natural.
    apply idpath.
  }
  rewrite dwhisker_vcomp_square.
  rewrite uwhisker_vcomp_square.
  rewrite <- !id_h_square_bicat_id.
  rewrite lunitor_h_comp_square'.
  rewrite runitor_h_comp_square'.
  rewrite <- !dwhisker_vcomp_square.
  rewrite <- uwhisker_vcomp_square.
  rewrite <- !dwhisker_square_comp.
  rewrite lunitor_runitor_identity.
  rewrite rinvunitor_runitor.
  rewrite dwhisker_square_id.
  rewrite dwhisker_uwhisker_square.
  rewrite <- uwhisker_vcomp_square.
  rewrite <- uwhisker_square_comp.
  rewrite linvunitor_lunitor.
  rewrite uwhisker_square_id.
  rewrite ud_whisker_vcomp_square.
  apply maponpaths_2.
  rewrite <- dwhisker_square_comp.
  apply maponpaths_2.
  rewrite !vassocl.
  rewrite rinvunitor_runitor.
  rewrite !id2_right.
  rewrite !vassocr.
  rewrite linvunitor_lunitor.
  rewrite id2_left.
  apply idpath.
Qed.

(** * 2. Invertible 2-cells between companions *)
Definition inv2cell_are_companions
           {B : verity_double_bicat}
           (H : vertically_saturated B)
           {x y : B}
           {h₁ h₂ : x --> y}
           (τ : invertible_2cell h₁ h₂)
           {v₁ v₂ : x -|-> y}
           (c₁ : are_companions h₁ v₁)
           (c₂ : are_companions h₂ v₂)
  : invertible_2cell v₁ v₂.
Proof.
  use make_invertible_2cell.
  - exact (cell_are_companions H (τ^-1) c₁ c₂).
  - use make_is_invertible_2cell.
    + exact (cell_are_companions H τ c₂ c₁).
    + abstract
        (rewrite <- cell_are_companions_comp ;
         rewrite vcomp_rinv ;
         apply cell_are_companions_id).
    + abstract
        (rewrite <- cell_are_companions_comp ;
         rewrite vcomp_linv ;
         apply cell_are_companions_id).
Defined.

(** * 3. Companions of adjoint equivalences *)
Section CompanionOfAdjequiv.
  Context {B : verity_double_bicat}
          (H : vertically_saturated B)
          {x y : B}
          {h : x --> y}
          {v : x -|-> y}
          (c : are_companions h v)
          (Hh : left_adjoint_equivalence h)
          {v' : y -|-> x}
          (c' : are_companions (left_adjoint_right_adjoint Hh) v').

  Let h' : y --> x := left_adjoint_right_adjoint Hh.
  Let η : invertible_2cell (id_h x) (h · h')
    := left_equivalence_unit_iso Hh.
  Let ε : invertible_2cell (h' · h) (id_h y)
    := left_equivalence_counit_iso Hh.

  Definition companion_of_adjequiv_equiv
    : left_equivalence v.
  Proof.
    simple refine ((v' ,, (_ ,, _)) ,, (_ ,, _)).
    - exact (inv2cell_are_companions
               H
               η
               (id_are_companions x)
               (comp_are_companions c c')).
    - exact (inv2cell_are_companions
               H
               ε
               (comp_are_companions c' c)
               (id_are_companions y)).
    - apply property_from_invertible_2cell.
    - apply property_from_invertible_2cell.
  Defined.

  Definition companion_of_adjequiv
    : left_adjoint_equivalence v.
  Proof.
    use equiv_to_adjequiv.
    exact companion_of_adjequiv_equiv.
  Defined.
End CompanionOfAdjequiv.

(** * 4. Vertical equivalences in Verity double bicategories with all companions *)
Definition all_equivs_companions_adjequiv
           {B : verity_double_bicat}
           (H : vertically_saturated B)
           (H' : weakly_hor_invariant B)
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (c : are_companions h v)
           (Hh : left_adjoint_equivalence h)
  : left_adjoint_equivalence v.
Proof.
  use companion_of_adjequiv.
  - exact H.
  - exact h.
  - exact c.
  - exact Hh.
  - exact (pr1 (H' _ _ _ (inv_left_adjoint_equivalence Hh))).
  - exact (pr2 (H' _ _ _ (inv_left_adjoint_equivalence Hh))).
Defined.

Definition all_companions_adjequiv
           {B : verity_double_bicat}
           (H : vertically_saturated B)
           (H' : all_companions B)
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (c : are_companions h v)
           (Hh : left_adjoint_equivalence h)
  : left_adjoint_equivalence v.
Proof.
  use all_equivs_companions_adjequiv.
  - exact H.
  - use all_companions_to_weakly_hor_invariant.
    exact H'.
  - exact h.
  - exact c.
  - exact Hh.
Defined.
