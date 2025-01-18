(*****************************************************************************************

 Local univalence of Verity double bicategories

 Every Verity bicategory has multiple underlying 1-categories, and for each of these, we
 have a univalence condition.

 The first two underlying categories that we have, are the categories whose objects are
 horizontal/vertical 1-cells and whose morphisms are horizontal/vertical 2-cells. From this,
 we get two local univalence conditions, and these express that the underlying horizontal
 and the underlying vertical bicategory are locally univalent respectively. We also have
 the underlying categories whose objects are horizontal/vertical 1-cells and whose morphisms
 are "vertical/horizontal squares" (squares with two sides being identities). For these, we also have local univalence conditions.

 If we assume that 2-cells are the same as squares with identity sides in the corresponding
 direction, then these two univalence conditions are equivalent.

 Contents
 1. Local horizontal univalence
 2. Local horizontal univalence via squares
 3. Equivalence between the different local horizontal univalence conditions
 4. Local vertical univalence
 5. Local vertical univalence via squares
 6. Equivalence between the different local vertical univalence conditions
 7. Locally univalent vertical bicategories

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.

Local Open Scope cat.
Local Open Scope double_bicat.

(** * 1. Local horizontal univalence *)
Definition hor_locally_univalent
           (B : verity_double_bicat)
  : UU
  := is_univalent_2_1 (hor_bicat_of_verity_double_bicat B).

Proposition isaprop_hor_locally_univalent
            (B : verity_double_bicat)
  : isaprop (hor_locally_univalent B).
Proof.
  apply isaprop_is_univalent_2_1.
Qed.

(** * 2. Local horizontal univalence via squares *)
Definition hor_sq_locally_univalent
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B), is_univalent (hom_h_sq B x y).

Proposition isaprop_hor_sq_locally_univalent
            (B : verity_double_bicat)
  : isaprop (hor_sq_locally_univalent B).
Proof.
  do 2 (use impred ; intro).
  apply isaprop_is_univalent.
Qed.

(** * 3. Equivalence between the different local horizontal univalence conditions *)
Section IsoWeqH.
  Context {B : verity_double_bicat}
          (H : horizontally_saturated B)
          {x y : B}
          (h₁ h₂ : x --> y).

  Definition hom_h_to_hom_h_sq_z_iso
             (τ : z_iso (C := hom_h B x y) h₁ h₂)
    : z_iso (C := hom_h_sq B x y) h₁ h₂.
  Proof.
    use make_z_iso ; cbn.
    - exact (horizontal_cell_to_square (pr1 τ)).
    - exact (horizontal_cell_to_square (inv_from_z_iso τ)).
    - split.
      + abstract
          (cbn -[horizontal_cell_to_square comp_hor_globular_square] ;
           rewrite <- horizontal_cell_to_square_comp ;
           refine (_ @ horizontal_cell_to_square_id _) ;
           apply maponpaths ;
           apply (z_iso_inv_after_z_iso τ)).
      + abstract
          (cbn -[horizontal_cell_to_square comp_hor_globular_square] ;
           rewrite <- horizontal_cell_to_square_comp ;
           refine (_ @ horizontal_cell_to_square_id _) ;
           apply maponpaths ;
           apply (z_iso_after_z_iso_inv τ)).
  Defined.

  Definition hom_h_sq_to_hom_h_z_iso
             (τ : z_iso (C := hom_h_sq B x y) h₁ h₂)
    : z_iso (C := hom_h B x y) h₁ h₂.
  Proof.
    use make_z_iso ; cbn.
    - exact (square_to_horizontal_cell H (pr1 τ)).
    - exact (square_to_horizontal_cell H (inv_from_z_iso τ)).
    - split.
      + abstract
          (cbn ;
           refine (!(square_to_horizontal_cell_comp _ _ _) @ _) ;
           refine (_ @ square_to_horizontal_cell_id H _) ;
           apply maponpaths ;
           exact (z_iso_inv_after_z_iso τ)).
      + abstract
          (cbn ;
           refine (!(square_to_horizontal_cell_comp _ _ _) @ _) ;
           refine (_ @ square_to_horizontal_cell_id H _) ;
           apply maponpaths ;
           exact (z_iso_after_z_iso_inv τ)).
  Defined.

  Definition hom_h_hom_h_sq_z_iso_weq
    : z_iso (C := hom_h B x y) h₁ h₂ ≃ z_iso (C := hom_h_sq B x y) h₁ h₂.
  Proof.
    use weq_iso.
    - exact hom_h_to_hom_h_sq_z_iso.
    - exact hom_h_sq_to_hom_h_z_iso.
    - abstract
        (intro f ;
         use z_iso_eq ; cbn ;
         apply horizontal_cell_to_square_to_horizontal_cell).
    - abstract
        (intro f ;
         use z_iso_eq ; cbn ;
         apply square_to_horizontal_cell_to_square).
  Defined.
End IsoWeqH.

Definition is_univalent_hom_h_weq_is_univalent_hom_h_sq
           {B : verity_double_bicat}
           (H : horizontally_saturated B)
           (x y : B)
  : is_univalent (hom_h B x y) ≃ is_univalent (hom_h_sq B x y).
Proof.
  use weqimplimpl.
  - intros H' h₁ h₂.
    use weqhomot.
    + exact (hom_h_hom_h_sq_z_iso_weq H h₁ h₂ ∘ make_weq _ (H' h₁ h₂))%weq.
    + intro p.
      induction p.
      use z_iso_eq ; cbn.
      apply horizontal_cell_to_square_id.
  - intros H' h₁ h₂.
    use weqhomot.
    + exact (invweq (hom_h_hom_h_sq_z_iso_weq H h₁ h₂) ∘ make_weq _ (H' h₁ h₂))%weq.
    + intro p.
      induction p.
      use z_iso_eq ; cbn.
      apply square_to_horizontal_cell_id.
  - apply isaprop_is_univalent.
  - apply isaprop_is_univalent.
Qed.

Definition hor_sq_weq_hor_locally_univalent
           {B : verity_double_bicat}
           (H : horizontally_saturated B)
  : hor_locally_univalent B
    ≃
    hor_sq_locally_univalent B
  := (weqonsecfibers
        _ _
        (λ x, weqonsecfibers
                _ _
                (λ y, is_univalent_hom_h_weq_is_univalent_hom_h_sq H x y))
      ∘ is_univalent_2_1_weq_local_univ _)%weq.

Definition h_sq_idtoiso_2_1
           {B : verity_double_bicat}
           {x y : B}
           {h₁ h₂ : x --> y}
           (p : h₁ = h₂)
  : invertible_horizontal_square h₁ h₂
  := invertible_2cell_to_horizontal_square (idtoiso_2_1 _ _ p).

Definition h_sq_isotoid_2_1
           {B : verity_double_bicat}
           (H : horizontally_saturated B)
           (HB_2_1 : hor_locally_univalent B)
           {x y : B}
           {h₁ h₂ : x --> y}
           (τ : invertible_horizontal_square h₁ h₂)
  : h₁ = h₂
  := isotoid_2_1 HB_2_1 (horizontal_square_to_invertible_2cell H τ).

Proposition h_sq_idtoiso_isotoid_2_1
            {B : verity_double_bicat}
            (H : horizontally_saturated B)
            (HB_2_1 : hor_locally_univalent B)
            {x y : B}
            {h₁ h₂ : x --> y}
            (τ : invertible_horizontal_square h₁ h₂)
  : h_sq_idtoiso_2_1 (h_sq_isotoid_2_1 H HB_2_1 τ) = τ.
Proof.
  unfold h_sq_idtoiso_2_1, h_sq_isotoid_2_1.
  rewrite idtoiso_2_1_isotoid_2_1.
  exact (homotinvweqweq (horizontal_square_weq_invertible_2cell H h₁ h₂) τ).
Qed.

Proposition h_sq_isotoid_idtoiso_2_1
            {B : verity_double_bicat}
            (H : horizontally_saturated B)
            (HB_2_1 : hor_locally_univalent B)
            {x y : B}
            {h₁ h₂ : x --> y}
            (p : h₁ = h₂)
  : h_sq_isotoid_2_1 H HB_2_1 (h_sq_idtoiso_2_1 p) = p.
Proof.
  unfold h_sq_idtoiso_2_1, h_sq_isotoid_2_1.
  etrans.
  {
    apply maponpaths.
    exact (homotweqinvweq
             (horizontal_square_weq_invertible_2cell H h₁ h₂)
             (idtoiso_2_1 h₁ h₂ p)).
  }
  apply isotoid_2_1_idtoiso_2_1.
Qed.

(** * 4. Local vertical univalence *)
Definition ver_locally_univalent
           (B : verity_double_bicat)
  : UU
  := is_univalent_2_1 (ver_bicat_of_verity_double_bicat B).

Proposition isaprop_ver_locally_univalent
            (B : verity_double_bicat)
  : isaprop (ver_locally_univalent B).
Proof.
  apply isaprop_is_univalent_2_1.
Qed.

(** * 5. Local vertical univalence via squares *)
Definition ver_sq_locally_univalent
           (B : verity_double_bicat)
  : UU
  := ∏ (x y : B), is_univalent (hom_v_sq B x y).

Proposition isaprop_ver_sq_locally_univalent
            (B : verity_double_bicat)
  : isaprop (ver_sq_locally_univalent B).
Proof.
  do 2 (use impred ; intro).
  apply isaprop_is_univalent.
Qed.

(** * 6. Equivalence between the different local vertical univalence conditions *)
Section IsoWeqV.
  Context {B : verity_double_bicat}
          (H : vertically_saturated B)
          {x y : B}
          (v₁ v₂ : x -|-> y).

  Definition hom_v_to_hom_v_sq_z_iso
             (τ : z_iso (C := hom_v B x y) v₁ v₂)
    : z_iso (C := hom_v_sq B x y) v₁ v₂.
  Proof.
    use make_z_iso ; cbn.
    - exact (vertical_cell_to_square (pr1 τ)).
    - exact (vertical_cell_to_square (inv_from_z_iso τ)).
    - split.
      + abstract
          (cbn -[vertical_cell_to_square comp_ver_globular_square] ;
           rewrite <- vertical_cell_to_square_comp ;
           refine (_ @ vertical_cell_to_square_id _) ;
           apply maponpaths ;
           apply (z_iso_inv_after_z_iso τ)).
      + abstract
          (cbn -[vertical_cell_to_square comp_ver_globular_square] ;
           rewrite <- vertical_cell_to_square_comp ;
           refine (_ @ vertical_cell_to_square_id _) ;
           apply maponpaths ;
           apply (z_iso_after_z_iso_inv τ)).
  Defined.

  Definition hom_v_sq_to_hom_v_z_iso
             (τ : z_iso (C := hom_v_sq B x y) v₁ v₂)
    : z_iso (C := hom_v B x y) v₁ v₂.
  Proof.
    use make_z_iso ; cbn.
    - exact (square_to_vertical_cell H (pr1 τ)).
    - exact (square_to_vertical_cell H (inv_from_z_iso τ)).
    - split.
      + abstract
          (cbn ;
           refine (!(square_to_vertical_cell_comp _ _ _) @ _) ;
           refine (_ @ square_to_vertical_cell_id H _) ;
           apply maponpaths ;
           exact (z_iso_inv_after_z_iso τ)).
      + abstract
          (cbn ;
           refine (!(square_to_vertical_cell_comp _ _ _) @ _) ;
           refine (_ @ square_to_vertical_cell_id H _) ;
           apply maponpaths ;
           exact (z_iso_after_z_iso_inv τ)).
  Defined.

  Definition hom_v_hom_v_sq_z_iso_weq
    : z_iso (C := hom_v B x y) v₁ v₂ ≃ z_iso (C := hom_v_sq B x y) v₁ v₂.
  Proof.
    use weq_iso.
    - exact hom_v_to_hom_v_sq_z_iso.
    - exact hom_v_sq_to_hom_v_z_iso.
    - abstract
        (intro f ;
         use z_iso_eq ; cbn ;
         apply vertical_cell_to_square_to_vertical_cell).
    - abstract
        (intro f ;
         use z_iso_eq ; cbn ;
         apply square_to_vertical_cell_to_square).
  Defined.
End IsoWeqV.

Definition is_univalent_hom_v_weq_is_univalent_hom_v_sq
           {B : verity_double_bicat}
           (H : vertically_saturated B)
           (x y : B)
  : is_univalent (hom_v B x y) ≃ is_univalent (hom_v_sq B x y).
Proof.
  use weqimplimpl.
  - intros H' v₁ v₂.
    use weqhomot.
    + exact (hom_v_hom_v_sq_z_iso_weq H v₁ v₂ ∘ make_weq _ (H' v₁ v₂))%weq.
    + intro p.
      induction p.
      use z_iso_eq ; cbn.
      apply vertical_cell_to_square_id.
  - intros H' v₁ v₂.
    use weqhomot.
    + exact (invweq (hom_v_hom_v_sq_z_iso_weq H v₁ v₂) ∘ make_weq _ (H' v₁ v₂))%weq.
    + intro p.
      induction p.
      use z_iso_eq ; cbn.
      apply square_to_vertical_cell_id.
  - apply isaprop_is_univalent.
  - apply isaprop_is_univalent.
Qed.

Definition ver_sq_weq_ver_locally_univalent
           {B : verity_double_bicat}
           (H : vertically_saturated B)
  : ver_locally_univalent B
    ≃
    ver_sq_locally_univalent B
  := (weqonsecfibers
        _ _
        (λ x, weqonsecfibers
                _ _
                (λ y, is_univalent_hom_v_weq_is_univalent_hom_v_sq H x y))
      ∘ is_univalent_2_1_weq_local_univ (ver_bicat_of_verity_double_bicat B))%weq.

Definition v_sq_idtoiso_2_1
           {B : verity_double_bicat}
           {x y : B}
           {v₁ v₂ : x -|-> y}
           (p : v₁ = v₂)
  : invertible_vertical_square v₁ v₂
  := invertible_2cell_to_vertical_square (idtoiso_2_1 _ _ p).

Definition v_sq_isotoid_2_1
           {B : verity_double_bicat}
           (H : vertically_saturated B)
           (HB_2_1 : ver_locally_univalent B)
           {x y : B}
           {v₁ v₂ : x -|-> y}
           (τ : invertible_vertical_square v₁ v₂)
  : v₁ = v₂
  := isotoid_2_1 HB_2_1 (vertical_square_to_invertible_2cell H τ).

Proposition v_sq_idtoiso_isotoid_2_1
            {B : verity_double_bicat}
            (H : vertically_saturated B)
            (HB_2_1 : ver_locally_univalent B)
            {x y : B}
            {v₁ v₂ : x -|-> y}
            (τ : invertible_vertical_square v₁ v₂)
  : v_sq_idtoiso_2_1 (v_sq_isotoid_2_1 H HB_2_1 τ) = τ.
Proof.
  unfold v_sq_idtoiso_2_1, v_sq_isotoid_2_1.
  rewrite idtoiso_2_1_isotoid_2_1.
  exact (homotinvweqweq (vertical_square_weq_invertible_2cell H v₁ v₂) τ).
Qed.

Proposition v_sq_isotoid_idtoiso_2_1
            {B : verity_double_bicat}
            (H : vertically_saturated B)
            (HB_2_1 : ver_locally_univalent B)
            {x y : B}
            {v₁ v₂ : x -|-> y}
            (p : v₁ = v₂)
  : v_sq_isotoid_2_1 H HB_2_1 (v_sq_idtoiso_2_1 p) = p.
Proof.
  unfold v_sq_idtoiso_2_1, v_sq_isotoid_2_1.
  etrans.
  {
    apply maponpaths.
    exact (homotweqinvweq
             (vertical_square_weq_invertible_2cell H v₁ v₂)
             (idtoiso_2_1 v₁ v₂ p)).
  }
  apply isotoid_2_1_idtoiso_2_1.
Qed.

(** * 7. Locally univalent vertical bicategories *)
Definition locally_univalent_verity_double_bicat
           (B : verity_double_bicat)
  : UU
  := hor_locally_univalent B
     ×
     ver_locally_univalent B.

Coercion locally_univalent_verity_double_bicat_hor_locally_univalent
         {B : verity_double_bicat}
         (H : locally_univalent_verity_double_bicat B)
  : hor_locally_univalent B
  := pr1 H.

Coercion locally_univalent_verity_double_bicat_ver_locally_univalent
         {B : verity_double_bicat}
         (H : locally_univalent_verity_double_bicat B)
  : ver_locally_univalent B
  := pr2 H.

Proposition isaprop_locally_univalent_verity_double_bicat
            (B : verity_double_bicat)
  : isaprop (locally_univalent_verity_double_bicat B).
Proof.
  apply isapropdirprod.
  - exact (isaprop_hor_locally_univalent B).
  - exact (isaprop_ver_locally_univalent B).
Qed.
