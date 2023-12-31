(*****************************************************************************************


 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.VerityDoubleBicat.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.DerivedLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.UnderlyingCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CellsAndSquares.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.LocalUnivalence.
Require Import UniMath.Bicategories.DoubleCategories.DoubleBicat.CompanionPairs.

Local Open Scope cat.
Local Open Scope double_bicat.

Section GregariousEquivalence.
  Context {B : verity_double_bicat}.

  Definition is_gregarious_equivalence
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
    : UU
    := are_companions h v
       ×
       left_adjoint_equivalence h
       ×
       left_adjoint_equivalence v.

  Coercion is_gregarious_equivalence_to_are_companions
           {x y : B}
           {h : x --> y}
           {v : x -|-> y}
           (H : is_gregarious_equivalence h v)
    : are_companions h v
    := pr1 H.

  Definition gregarious_equivalence
             (x y : B)
    : UU
    := ∑ (h : x --> y)
         (v : x -|-> y),
       is_gregarious_equivalence h v.

  Definition make_gregarious_equivalence
             {x y : B}
             (h : x --> y)
             (v : x -|-> y)
             (H : is_gregarious_equivalence h v)
    : gregarious_equivalence x y
    := h ,, v ,, H.

  Definition id_is_gregarious_equivalence
             (x : B)
    : is_gregarious_equivalence (id_h x) (id_v x).
  Proof.
    repeat split.
    - apply id_are_companions.
    - apply internal_adjoint_equivalence_identity.
    - apply internal_adjoint_equivalence_identity.
  Defined.

  Definition id_gregarious_equivalence
             (x : B)
    : gregarious_equivalence x x.
  Proof.
    use make_gregarious_equivalence.
    - apply id_h.
    - apply id_v.
    - apply id_is_gregarious_equivalence.
  Defined.

  Definition id_to_gregarious_equivalence
             {x y : B}
             (p : x = y)
    : gregarious_equivalence x y.
  Proof.
    induction p.
    exact (id_gregarious_equivalence x).
  Defined.

  Definition is_hor_gregarious_equivalence
             {x y : B}
             (h : x --> y)
    : UU
    := ∑ (v : x -|-> y), is_gregarious_equivalence h v.

  Coercion is_hor_gregarious_equivalence_to_mor
           {x y : B}
           {h : x --> y}
           (v : is_hor_gregarious_equivalence h)
    : x -|-> y
    := pr1 v.

  Coercion is_hor_gregarious_equivalence_to_is_gregarious_equivalence
           {x y : B}
           {h : x --> y}
           (v : is_hor_gregarious_equivalence h)
    : is_gregarious_equivalence h v
    := pr2 v.

  Lemma path_is_hor_gregarious_equivalence
        (HB_2_1 : is_univalent_2_1 B)
        (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
        {x y : B}
        {h : x --> y}
        (φ₁ φ₂ : is_hor_gregarious_equivalence h)
        (p : pr1 φ₁ = pr1 φ₂)
        (q₁ : lunitor _ ▿s (linvunitor _ ▵s vertical_cell_to_square (idtoiso_2_1 (C := ver_bicat_of_verity_double_bicat B) _ _ p)
             ⋆h
             unit_are_companions φ₂) = unit_are_companions φ₁)
        (q₂ : runitor _ ▿s (linvunitor _ ▵s counit_are_companions φ₁ ⋆h vertical_cell_to_square (idtoiso_2_1 (C := ver_bicat_of_verity_double_bicat B) _ _ p)) = counit_are_companions φ₂)
    : φ₁ = φ₂.
  Proof.
    induction φ₁ as [ v₁ [ c₁ [ Hh₁ Hv₁ ] ] ].
    induction φ₂ as [ v₂ [ c₂ [ Hh₂ Hv₂ ] ] ].
    cbn in p.
    induction p.
    cbn in *.
    apply maponpaths.
    repeat (use dirprodeq).
    - cbn.
      use eq_are_companions.
      + refine (!q₁ @ _).
        unfold vertical_cell_to_square.
        rewrite lwhisker_square_id.
        rewrite lunitor_h_comp_square'.
        rewrite !dwhisker_uwhisker_square.
        rewrite <- uwhisker_square_comp.
        rewrite <- dwhisker_square_comp.
        rewrite !linvunitor_lunitor.
        rewrite uwhisker_square_id, dwhisker_square_id.
        apply idpath.
      + refine (_ @ q₂).
        unfold vertical_cell_to_square.
        rewrite lwhisker_square_id.
        rewrite runitor_h_comp_square'.
        rewrite !dwhisker_uwhisker_square.
        rewrite <- uwhisker_square_comp.
        rewrite <- dwhisker_square_comp.
        rewrite runitor_lunitor_identity.
        rewrite linvunitor_lunitor.
        rewrite rinvunitor_runitor.
        rewrite uwhisker_square_id, dwhisker_square_id.
        apply idpath.
    - apply isaprop_left_adjoint_equivalence.
      exact HB_2_1.
    - apply isaprop_left_adjoint_equivalence.
      exact HB_2_1'.
  Qed.

  Proposition isaprop_is_hor_gregarious_equivalence
              (H : vertical_cells_are_squares B)
              (HB_2_1 : is_univalent_2_1 B)
              (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
              {x y : B}
              (h : x --> y)
    : isaprop (is_hor_gregarious_equivalence h).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use (path_is_hor_gregarious_equivalence HB_2_1 HB_2_1').
    - use (isotoid_2_1 HB_2_1').
      use (vertical_square_to_invertible_2cell H).
      use make_invertible_vertical_square.
      + use make_invertible_vertical_square_data.
        * use (square_between_companions φ₁).
          apply (pr12 φ₂).
        * use (square_between_companions φ₂).
          apply (pr12 φ₁).
      + admit.
    - rewrite idtoiso_2_1_isotoid_2_1.
      cbn.
      rewrite square_to_vertical_cell_to_square.
      unfold square_between_companions.
      admit.
    - rewrite idtoiso_2_1_isotoid_2_1.
      cbn.
      rewrite square_to_vertical_cell_to_square.
      unfold square_between_companions.
      admit.
  Admitted.

  Definition hor_left_adjoint_equivalence_to_gregarious_equivalence
             (H : vertical_cells_are_squares B)
             (H' : all_equivs_companions B)
             {x y : B}
             (h : x --> y)
             (Hh : left_adjoint_equivalence h)
    : is_hor_gregarious_equivalence h.
  Proof.
    pose (c := H' _ _ h Hh).
    induction c as [ v c ].
    refine (v ,, _).
    repeat split.
    - exact c.
    - exact Hh.
    - use all_equivs_companions_adjequiv.
      + exact H.
      + exact H'.
      + exact h.
      + exact c.
      + exact Hh.
  Qed.

  Definition hor_gregarious_equivalence_to_left_adjoint_equivalence
             {x y : B}
             (h : x --> y)
             (Hh : is_hor_gregarious_equivalence h)
    : left_adjoint_equivalence h.
  Proof.
    apply Hh.
  Qed.

  Definition hor_left_adjoint_equivalence_weq_gregarious_equivalence
             (HB_2_1 : is_univalent_2_1 B)
             (HB_2_1' : is_univalent_2_1 (ver_bicat_of_verity_double_bicat B))
             (H : all_equivs_companions B)
             (H' : vertical_cells_are_squares B)
             {x y : B}
             (h : x --> y)
    : left_adjoint_equivalence h ≃ is_hor_gregarious_equivalence h.
  Proof.
    use weqimplimpl.
    - apply (hor_left_adjoint_equivalence_to_gregarious_equivalence H' H).
    - apply hor_gregarious_equivalence_to_left_adjoint_equivalence.
    - apply isaprop_left_adjoint_equivalence.
      exact HB_2_1.
    - apply (isaprop_is_hor_gregarious_equivalence H' HB_2_1 HB_2_1').
  Qed.
End GregariousEquivalence.
