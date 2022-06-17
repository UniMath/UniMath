(************************************************************************

 Equivalences for coproducts

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.ContainsAdjEquiv.
Require Import UniMath.Bicategories.Colimits.Coproducts.

Local Open Scope cat.

(**
   Suppose, we have a diagram as follows

         ι₁        ι₂
   x₁ ------> p <------ x₂
   |          |         |
   l₁    ≃    l₃   ≃    l₂
   |     γ₁   |    γ₂   |
   V          V         V
   y₁ ------> q <------ y₂
         λ₁        κ₂

   where l₁, l₂, and l₃ are adjoint equivalences.
   If the top row is a product cone, then so is the bottom row
 *)
Section CoproductEquivalence.
  Context {B : bicat}
          {x₁ x₂ p y₁ y₂ q : B}
          (ι₁ : x₁ --> p)
          (ι₂ : x₂ --> p)
          (cone₁ := make_bincoprod_cocone p ι₁ ι₂)
          (Hp : has_bincoprod_ump cone₁)
          (κ₁ : y₁ --> q)
          (κ₂ : y₂ --> q)
          (cone₂ := make_bincoprod_cocone q κ₁ κ₂)
          (l₁ : x₁ --> y₁)
          (l₂ : x₂ --> y₂)
          (l₃ : p --> q)
          (Hl₁ : left_adjoint_equivalence l₁)
          (Hl₂ : left_adjoint_equivalence l₂)
          (Hl₃ : left_adjoint_equivalence l₃)
          (γ₁ : invertible_2cell
                  (l₁ · κ₁)
                  (ι₁ · l₃))
          (γ₂ : invertible_2cell
                  (l₂ · κ₂)
                  (ι₂ · l₃)).

  Let r₁ : y₁ --> x₁
    := left_adjoint_right_adjoint Hl₁.
  Let η₁ : invertible_2cell (id₁ _) (l₁ · r₁)
    := left_equivalence_unit_iso Hl₁.
  Let ε₁ : invertible_2cell (r₁ · l₁) (id₁ _)
    := left_equivalence_counit_iso Hl₁.

  Let r₂ : y₂ --> x₂
    := left_adjoint_right_adjoint Hl₂.
  Let η₂ : invertible_2cell (id₁ _) (l₂ · r₂)
    := left_equivalence_unit_iso Hl₂.
  Let ε₂ : invertible_2cell (r₂ · l₂) (id₁ _)
    := left_equivalence_counit_iso Hl₂.

  Let r₃ : q --> p
    := left_adjoint_right_adjoint Hl₃.
  Let η₃ : invertible_2cell (id₁ _) (l₃ · r₃)
    := left_equivalence_unit_iso Hl₃.
  Let ε₃ : invertible_2cell (r₃ · l₃) (id₁ _)
    := left_equivalence_counit_iso Hl₃.

  Let γ₁' : invertible_2cell (κ₁ · r₃) (r₁ · ι₁)
    := comp_of_invertible_2cell
         (linvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (rwhisker_of_invertible_2cell
               _
               (inv_of_invertible_2cell ε₁))
            (comp_of_invertible_2cell
               (rassociator_invertible_2cell _ _ _)
               (lwhisker_of_invertible_2cell
                  _
                  (comp_of_invertible_2cell
                     (lassociator_invertible_2cell _ _ _)
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           γ₁)
                        (comp_of_invertible_2cell
                           (rassociator_invertible_2cell _ _ _)
                           (comp_of_invertible_2cell
                              (lwhisker_of_invertible_2cell
                                 _
                                 (inv_of_invertible_2cell η₃))
                              (runitor_invertible_2cell _)))))))).

  Let γ₂' : invertible_2cell (κ₂ · r₃) (r₂ · ι₂)
    := comp_of_invertible_2cell
         (linvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (rwhisker_of_invertible_2cell
               _
               (inv_of_invertible_2cell ε₂))
            (comp_of_invertible_2cell
               (rassociator_invertible_2cell _ _ _)
               (lwhisker_of_invertible_2cell
                  _
                  (comp_of_invertible_2cell
                     (lassociator_invertible_2cell _ _ _)
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           γ₂)
                        (comp_of_invertible_2cell
                           (rassociator_invertible_2cell _ _ _)
                           (comp_of_invertible_2cell
                              (lwhisker_of_invertible_2cell
                                 _
                                 (inv_of_invertible_2cell η₃))
                              (runitor_invertible_2cell _)))))))).

  Definition has_bincoprod_ump_1_left_adjoint_equivalence
    : bincoprod_ump_1 cone₂.
  Proof.
    intros c.
    use make_bincoprod_1cell.
    - refine (r₃ · _).
      exact (bincoprod_ump_1cell
                Hp
                (l₁ · bincoprod_cocone_inl c)
                (l₂ · bincoprod_cocone_inr c)).
    - exact (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell _ γ₁')
                  (comp_of_invertible_2cell
                     (rassociator_invertible_2cell _ _ _)
                     (comp_of_invertible_2cell
                        (lwhisker_of_invertible_2cell
                           _
                           (bincoprod_ump_1cell_inl Hp _ _ _))
                        (comp_of_invertible_2cell
                           (lassociator_invertible_2cell _ _ _)
                           (comp_of_invertible_2cell
                              (rwhisker_of_invertible_2cell
                                 _
                                 ε₁)
                              (lunitor_invertible_2cell _))))))).
    - exact (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell _ γ₂')
                  (comp_of_invertible_2cell
                     (rassociator_invertible_2cell _ _ _)
                     (comp_of_invertible_2cell
                        (lwhisker_of_invertible_2cell
                           _
                           (bincoprod_ump_1cell_inr Hp _ _ _))
                        (comp_of_invertible_2cell
                           (lassociator_invertible_2cell _ _ _)
                           (comp_of_invertible_2cell
                              (rwhisker_of_invertible_2cell
                                 _
                                 ε₂)
                              (lunitor_invertible_2cell _))))))).
  Defined.

  Section UMP2.
    Context {c : B}
            {φ ψ : q --> c}
            (α : κ₁ · φ ==> κ₁ · ψ)
            (β : κ₂ · φ ==> κ₂ · ψ).

    Definition has_bincoprod_ump_2_left_adjoint_equivalence_unique
      : isaprop (∑ (γ : φ ==> ψ), κ₁ ◃ γ = α × κ₂ ◃ γ = β).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      apply (adj_equiv_faithful
               (bicat_left_adjoint_equivalence_to_op1_bicat_left_adjoint_equivalence
                  _
                  Hl₃)).
      cbn.
      use (bincoprod_ump_2cell_unique_alt Hp) ; cbn.
      - use (vcomp_lcancel (rassociator _ _ _)).
        {
          is_iso.
        }
        rewrite !lwhisker_lwhisker_rassociator.
        apply maponpaths_2.
        use (vcomp_lcancel (γ₁ ▹ _)).
        {
          is_iso.
          apply property_from_invertible_2cell.
        }
        rewrite !vcomp_whisker.
        apply maponpaths_2.
        use (vcomp_lcancel (lassociator _ _ _)).
        {
          is_iso.
        }
        rewrite <- !lwhisker_lwhisker.
        apply maponpaths_2.
        apply maponpaths.
        exact (pr12 ζ₁ @ !(pr12 ζ₂)).
      - use (vcomp_lcancel (rassociator _ _ _)).
        {
          is_iso.
        }
        rewrite !lwhisker_lwhisker_rassociator.
        apply maponpaths_2.
        use (vcomp_lcancel (γ₂ ▹ _)).
        {
          is_iso.
          apply property_from_invertible_2cell.
        }
        rewrite !vcomp_whisker.
        apply maponpaths_2.
        use (vcomp_lcancel (lassociator _ _ _)).
        {
          is_iso.
        }
        rewrite <- !lwhisker_lwhisker.
        apply maponpaths_2.
        apply maponpaths.
        exact (pr22 ζ₁ @ !(pr22 ζ₂)).
    Qed.

    Let Hr₁ : @left_adjoint_equivalence (op1_bicat B) _ _ r₁
      := bicat_left_adjoint_equivalence_to_op1_bicat_left_adjoint_equivalence
           _
           (pr2 (inv_adjequiv (_ ,, Hl₁))).

    Let Hr₂ : @left_adjoint_equivalence (op1_bicat B) _ _ r₂
      := bicat_left_adjoint_equivalence_to_op1_bicat_left_adjoint_equivalence
           _
           (pr2 (inv_adjequiv (_ ,, Hl₂))).

    Let α' : ι₁ · (l₃ · φ) ==> ι₁ · (l₃ · ψ)
      := fully_faithful_1cell_inv_map
           (adj_equiv_fully_faithful Hr₁)
           (lassociator _ _ _
            • ((γ₁')^-1 ▹ _)
            • rassociator _ _ _
            • (_ ◃ lassociator _ _ _)
            • (_ ◃ (ε₃ ▹ _))
            • (_ ◃ lunitor φ)
            • α
            • (_ ◃ linvunitor ψ)
            • (_ ◃ (ε₃^-1 ▹ _))
            • (_ ◃ rassociator _ _ _)
            • lassociator _ _ _
            • (γ₁' ▹ _)
            • rassociator _ _ _).

    Let β' : ι₂ · (l₃ · φ) ==> ι₂ · (l₃ · ψ)
      := fully_faithful_1cell_inv_map
           (adj_equiv_fully_faithful Hr₂)
           (lassociator _ _ _
            • ((γ₂')^-1 ▹ _)
            • rassociator _ _ _
            • (_ ◃ lassociator _ _ _)
            • (_ ◃ (ε₃ ▹ _))
            • (_ ◃ lunitor _)
            • β
            • (_ ◃ linvunitor _)
            • (_ ◃ (ε₃^-1 ▹ _))
            • (_ ◃ rassociator _ _ _)
            • lassociator _ _ _
            • (γ₂' ▹ _)
            • rassociator _ _ _).

    Definition has_bincoprod_ump_2_left_adjoint_equivalence_cell
      : φ ==> ψ
      := linvunitor _
         • (ε₃^-1 ▹ _)
         • rassociator _ _ _
         • (_ ◃ bincoprod_ump_2cell Hp α' β')
         • lassociator _ _ _
         • (ε₃ ▹ _)
         • lunitor _.

    Definition has_bincoprod_ump_2_left_adjoint_equivalence_inl
      : κ₁ ◃ has_bincoprod_ump_2_left_adjoint_equivalence_cell = α.
    Proof.
      unfold has_bincoprod_ump_2_left_adjoint_equivalence_cell.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 3 (use vcomp_move_R_pM ; [ is_iso | ]).
      cbn -[ε₃ α' β'].
      use (vcomp_lcancel (rassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite lwhisker_lwhisker_rassociator.
      use (vcomp_lcancel ((γ₁')^-1 ▹ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite vcomp_whisker.
      use (vcomp_lcancel (lassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply( bincoprod_ump_2cell_inl Hp).
      }
      use vcomp_move_R_Mp.
      {
        is_iso.
        apply ε₃.
      }
      cbn -[ε₃ γ₁' α'].
      rewrite !vassocr.
      apply (fully_faithful_1cell_inv_map_eq (adj_equiv_fully_faithful Hr₁)).
    Qed.

    Definition has_bincoprod_ump_2_left_adjoint_equivalence_inr
      : κ₂ ◃ has_bincoprod_ump_2_left_adjoint_equivalence_cell = β.
    Proof.
      unfold has_bincoprod_ump_2_left_adjoint_equivalence_cell.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 3 (use vcomp_move_R_pM ; [ is_iso | ]).
      cbn -[ε₃ α' β'].
      use (vcomp_lcancel (rassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite lwhisker_lwhisker_rassociator.
      use (vcomp_lcancel ((γ₂')^-1 ▹ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite vcomp_whisker.
      use (vcomp_lcancel (lassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply( bincoprod_ump_2cell_inr Hp).
      }
      use vcomp_move_R_Mp.
      {
        is_iso.
        apply ε₃.
      }
      cbn -[ε₃ γ₂' β'].
      rewrite !vassocr.
      apply (fully_faithful_1cell_inv_map_eq (adj_equiv_fully_faithful Hr₂)).
    Qed.
  End UMP2.

  Definition has_bincoprod_ump_2_left_adjoint_equivalence
    : bincoprod_ump_2 cone₂.
  Proof.
    intros c φ ψ α β.
    use iscontraprop1.
    - exact (has_bincoprod_ump_2_left_adjoint_equivalence_unique α β).
    - simple refine (_ ,, _ ,, _).
      + exact (has_bincoprod_ump_2_left_adjoint_equivalence_cell α β).
      + exact (has_bincoprod_ump_2_left_adjoint_equivalence_inl α β).
      + exact (has_bincoprod_ump_2_left_adjoint_equivalence_inr α β).
  Defined.

  Definition has_bincoprod_ump_left_adjoint_equivalence
    : has_bincoprod_ump cone₂.
  Proof.
    simple refine (_ ,, _).
    - exact has_bincoprod_ump_1_left_adjoint_equivalence.
    - exact has_bincoprod_ump_2_left_adjoint_equivalence.
  Defined.
End CoproductEquivalence.
