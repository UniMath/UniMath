(*****************************************************************************************

 Local univalence of Verity double bicategories

 Every Verity bicategory has multiple underlying 1-categories, and for each of these, we
 have a univalence condition.

 The first two underlying categories that we have, are the categories whose objects are
 horizontal/vertical 1-cells and whose morphisms are horizontal/vertical 2-cells. From this,
 we get two local univalence conditions, and these express that the underlying horizontal
 and the underlying vertical bicategory are locally univalent respectively. We also have
 the underlying categories whose objects are horizontal/vertical 1-cells and whose morphisms
 are squares. For these, we also have local univalence conditions.

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

Section LocalUnivalence.
  Context (B : verity_double_bicat).

  (** * 1. Local horizontal univalence *)
  Definition hor_locally_univalent
    : UU
    := is_univalent_2_1 (hor_bicat_of_verity_double_bicat B).

  Proposition isaprop_hor_locally_univalent
    : isaprop hor_locally_univalent.
  Proof.
    apply isaprop_is_univalent_2_1.
  Qed.

  (** * 2. Local horizontal univalence via squares *)
  Definition hor_sq_locally_univalent
    : UU
    := ∏ (x y : B), is_univalent (hom_h_sq B x y).

  Proposition isaprop_hor_sq_locally_univalent
    : isaprop hor_sq_locally_univalent.
  Proof.
    do 2 (use impred ; intro).
    apply isaprop_is_univalent.
  Qed.

  Definition h_sq_isotoid_2_1
             (H : hor_sq_locally_univalent)
             {x y : B}
             {h₁ h₂ : x --> y}
             (τ : invertible_horizontal_square h₁ h₂)
    : h₁ = h₂.
  Proof.
    use (isotoid _ (H x y)).
    use make_z_iso.
    - exact (cell_of_invertible_horizontal_square τ).
    - exact (inv_of_invertible_horizontal_square τ).
    - split.
      + exact (pr12 τ).
      + exact (pr22 τ).
  Defined.

  (** * 3. Equivalence between the different local horizontal univalence conditions *)
  Section IsoWeqH.
    Context (H : horizontal_cells_are_squares B)
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
             (H : horizontal_cells_are_squares B)
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
             (H : horizontal_cells_are_squares B)
    : hor_locally_univalent
      ≃
      hor_sq_locally_univalent
    := (weqonsecfibers
          _ _
          (λ x, weqonsecfibers
                  _ _
                  (λ y, is_univalent_hom_h_weq_is_univalent_hom_h_sq H x y))
        ∘ is_univalent_2_1_weq_local_univ _)%weq.

  (** * 4. Local vertical univalence *)
  Definition ver_locally_univalent
    : UU
    := is_univalent_2_1 (ver_bicat_of_verity_double_bicat B).

  Proposition isaprop_ver_locally_univalent
    : isaprop ver_locally_univalent.
  Proof.
    apply isaprop_is_univalent_2_1.
  Qed.

  (** * 5. Local vertical univalence via squares *)
  Definition ver_sq_locally_univalent
    : UU
    := ∏ (x y : B), is_univalent (hom_v_sq B x y).

  Proposition isaprop_ver_sq_locally_univalent
    : isaprop ver_sq_locally_univalent.
  Proof.
    do 2 (use impred ; intro).
    apply isaprop_is_univalent.
  Qed.

  Definition v_sq_isotoid_2_1
             (H : ver_sq_locally_univalent)
             {x y : B}
             {v₁ v₂ : x -|-> y}
             (τ : invertible_vertical_square v₁ v₂)
    : v₁ = v₂.
  Proof.
    use (isotoid _ (H x y)).
    use make_z_iso.
    - exact (cell_of_invertible_vertical_square τ).
    - exact (inv_of_invertible_vertical_square τ).
    - split.
      + exact (pr12 τ).
      + exact (pr22 τ).
  Defined.

  (** * 6. Equivalence between the different local vertical univalence conditions *)
  Section IsoWeqV.
    Context (H : vertical_cells_are_squares B)
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
             (H : vertical_cells_are_squares B)
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
             (H : vertical_cells_are_squares B)
    : ver_locally_univalent
      ≃
      ver_sq_locally_univalent
    := (weqonsecfibers
          _ _
          (λ x, weqonsecfibers
                  _ _
                  (λ y, is_univalent_hom_v_weq_is_univalent_hom_v_sq H x y))
       ∘ is_univalent_2_1_weq_local_univ (ver_bicat_of_verity_double_bicat B))%weq.

  (** * 7. Locally univalent vertical bicategories *)
  Definition locally_univalent_verity_double_bicat
    : UU
    := hor_locally_univalent
       ×
       ver_locally_univalent.

  Coercion locally_univalent_verity_double_bicat_hor_locally_univalent
           (H : locally_univalent_verity_double_bicat)
    : hor_locally_univalent
    := pr1 H.

  Coercion locally_univalent_verity_double_bicat_ver_locally_univalent
           (H : locally_univalent_verity_double_bicat)
    : ver_locally_univalent
    := pr2 H.

  Proposition isaprop_locally_univalent_verity_double_bicat
    : isaprop locally_univalent_verity_double_bicat.
  Proof.
    apply isapropdirprod.
    - exact isaprop_hor_locally_univalent.
    - exact isaprop_ver_locally_univalent.
  Qed.
End LocalUnivalence.
