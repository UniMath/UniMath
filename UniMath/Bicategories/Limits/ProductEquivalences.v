(************************************************************************

 Equivalences for products

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.ContainsAdjEquiv.
Require Import UniMath.Bicategories.Limits.Products.

Local Open Scope cat.

(**
   Suppose, we have a diagram as follows

         π₁       π₂
   x₁ <------ p ------> x₂
   |          |         |
   l₁    ≃    l₃   ≃    l₂
   |     γ₁   |    γ₂   |
   V          V         V
   y₁ <------ q ------> y₂
         ρ₁       ρ₂

   where l₁, l₂, and l₃ are adjoint equivalences.
   If the top row is a product cone, then so is the bottom row
 *)
Section ProductEquivalence.
  Context {B : bicat}
          {x₁ x₂ p y₁ y₂ q : B}
          (π₁ : p --> x₁)
          (π₂ : p --> x₂)
          (cone₁ := make_binprod_cone p π₁ π₂)
          (Hp : has_binprod_ump cone₁)
          (ρ₁ : q --> y₁)
          (ρ₂ : q --> y₂)
          (cone₂ := make_binprod_cone q ρ₁ ρ₂)
          (l₁ : x₁ --> y₁)
          (l₂ : x₂ --> y₂)
          (l₃ : p --> q)
          (Hl₁ : left_adjoint_equivalence l₁)
          (Hl₂ : left_adjoint_equivalence l₂)
          (Hl₃ : left_adjoint_equivalence l₃)
          (γ₁ : invertible_2cell
                  (l₃ · ρ₁)
                  (π₁ · l₁))
          (γ₂ : invertible_2cell
                  (l₃ · ρ₂)
                  (π₂ · l₂)).

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

  Definition has_binprod_ump_1_left_adjoint_equivalence
    : binprod_ump_1 cone₂.
  Proof.
    intros c.
    use make_binprod_1cell.
    - refine (_ · l₃).
      exact (binprod_ump_1cell
               Hp
               (binprod_cone_pr1 c · r₁)
               (binprod_cone_pr2 c · r₂)).
    - exact (comp_of_invertible_2cell
               (rassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (lwhisker_of_invertible_2cell
                     _
                     γ₁)
                  (comp_of_invertible_2cell
                     (lassociator_invertible_2cell _ _ _)
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (binprod_ump_1cell_pr1
                              Hp
                              _
                              (binprod_cone_pr1 c · r₁)
                              (binprod_cone_pr2 c · r₂)))
                        (comp_of_invertible_2cell
                           (rassociator_invertible_2cell _ _ _)
                           (comp_of_invertible_2cell
                              (lwhisker_of_invertible_2cell
                                 _
                                 ε₁)
                              (runitor_invertible_2cell _))))))).
    - exact (comp_of_invertible_2cell
               (rassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (lwhisker_of_invertible_2cell
                     _
                     γ₂)
                  (comp_of_invertible_2cell
                     (lassociator_invertible_2cell _ _ _)
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (binprod_ump_1cell_pr2
                              Hp
                              _
                              (binprod_cone_pr1 c · r₁)
                              (binprod_cone_pr2 c · r₂)))
                        (comp_of_invertible_2cell
                           (rassociator_invertible_2cell _ _ _)
                           (comp_of_invertible_2cell
                              (lwhisker_of_invertible_2cell
                                 _
                                 ε₂)
                              (runitor_invertible_2cell _))))))).
  Defined.

  Section UMP2.
    Context {c : B}
            {φ ψ : c --> q}
            (α : φ · ρ₁ ==> ψ · ρ₁)
            (β : φ · ρ₂ ==> ψ · ρ₂).

    Let γ₁' : invertible_2cell (r₃ · π₁) (ρ₁ · r₁)
      := comp_of_invertible_2cell
           (rinvunitor_invertible_2cell _)
           (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 η₁)
              (comp_of_invertible_2cell
                 (rassociator_invertible_2cell _ _ _)
                 (comp_of_invertible_2cell
                    (lwhisker_of_invertible_2cell
                       _
                       (lassociator_invertible_2cell _ _ _))
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell
                          _
                          (rwhisker_of_invertible_2cell
                             _
                             (inv_of_invertible_2cell γ₁)))
                       (comp_of_invertible_2cell
                          (lassociator_invertible_2cell _ _ _)
                          (comp_of_invertible_2cell
                             (rwhisker_of_invertible_2cell
                                _
                                (lassociator_invertible_2cell _ _ _))
                             (comp_of_invertible_2cell
                                (rwhisker_of_invertible_2cell
                                   _
                                   (rwhisker_of_invertible_2cell
                                      _
                                      ε₃))
                                (rwhisker_of_invertible_2cell
                                   _
                                   (lunitor_invertible_2cell _))))))))).

    Let γ₂' : invertible_2cell (r₃ · π₂) (ρ₂ · r₂)
      := comp_of_invertible_2cell
           (rinvunitor_invertible_2cell _)
           (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 η₂)
              (comp_of_invertible_2cell
                 (rassociator_invertible_2cell _ _ _)
                 (comp_of_invertible_2cell
                    (lwhisker_of_invertible_2cell
                       _
                       (lassociator_invertible_2cell _ _ _))
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell
                          _
                          (rwhisker_of_invertible_2cell
                             _
                             (inv_of_invertible_2cell γ₂)))
                       (comp_of_invertible_2cell
                          (lassociator_invertible_2cell _ _ _)
                          (comp_of_invertible_2cell
                             (rwhisker_of_invertible_2cell
                                _
                                (lassociator_invertible_2cell _ _ _))
                             (comp_of_invertible_2cell
                                (rwhisker_of_invertible_2cell
                                   _
                                   (rwhisker_of_invertible_2cell
                                      _
                                      ε₃))
                                (rwhisker_of_invertible_2cell
                                   _
                                   (lunitor_invertible_2cell _))))))))).

    Definition has_binprod_ump_2_left_adjoint_equivalence_unique
      : isaprop
          (∑ (ζ : φ ==> ψ),
           ζ ▹ binprod_cone_pr1 cone₂ = α
           ×
           ζ ▹ binprod_cone_pr2 cone₂ = β).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      enough (pr1 ζ₁ ▹ r₃ = pr1 ζ₂ ▹ r₃) as H.
      {
        use (faithful_1cell_eq_cell
               (pr1 (adj_equiv_fully_faithful (inv_adjequiv (_ ,, Hl₃))))).
        exact H.
      }
      use (binprod_ump_2cell_unique_alt Hp) ; cbn.
      - use (vcomp_lcancel (lassociator _ _ _)).
        {
          is_iso.
        }
        rewrite !rwhisker_rwhisker.
        apply maponpaths_2.
        use (vcomp_lcancel (_ ◃ γ₁'^-1)).
        {
          is_iso.
        }
        rewrite <- !vcomp_whisker.
        apply maponpaths_2.
        use (vcomp_lcancel (rassociator _ _ _)).
        {
          is_iso.
        }
        rewrite <- !rwhisker_rwhisker_alt.
        apply maponpaths_2.
        apply maponpaths.
        exact (pr12 ζ₁ @ !(pr12 ζ₂)).
      - use (vcomp_lcancel (lassociator _ _ _)).
        {
          is_iso.
        }
        rewrite !rwhisker_rwhisker.
        apply maponpaths_2.
        use (vcomp_lcancel (_ ◃ γ₂'^-1)).
        {
          is_iso.
        }
        rewrite <- !vcomp_whisker.
        apply maponpaths_2.
        use (vcomp_lcancel (rassociator _ _ _)).
        {
          is_iso.
        }
        rewrite <- !rwhisker_rwhisker_alt.
        apply maponpaths_2.
        apply maponpaths.
        exact (pr22 ζ₁ @ !(pr22 ζ₂)).
    Qed.

    Let α' : φ · r₃ · π₁ ==> ψ · r₃ · π₁
      := fully_faithful_1cell_inv_map
           (adj_equiv_fully_faithful Hl₁)
           (rassociator _ _ _
            • (_ ◃ γ₁ ^-1)
            • lassociator _ _ _
            • (rassociator _ _ _ ▹ _)
            • ((_ ◃ ε₃) ▹ _)
            • (runitor _ ▹ _)
            • α
            • (rinvunitor _ ▹ _)
            • ((_ ◃ ε₃^-1) ▹ _)
            • (lassociator _ _ _ ▹ _)
            • rassociator _ _ _
            • (_ ◃ γ₁)
            • lassociator _ _ _).

    Let β' : φ · r₃ · π₂ ==> ψ · r₃ · π₂
      := fully_faithful_1cell_inv_map
           (adj_equiv_fully_faithful Hl₂)
           (rassociator _ _ _
            • (_ ◃ γ₂^-1)
            • lassociator _ _ _
            • (rassociator _ _ _ ▹ _)
            • ((_ ◃ ε₃) ▹ _)
            • (runitor _ ▹ _)
            • β
            • (rinvunitor _ ▹ _)
            • ((_ ◃ ε₃^-1) ▹ _)
            • (lassociator _ _ _ ▹ _)
            • rassociator _ _ _
            • (_ ◃ γ₂)
            • lassociator _ _ _).

    Definition has_binprod_ump_2_left_adjoint_equivalence_cell
      : φ ==> ψ
      := rinvunitor _
         • (_ ◃ ε₃^-1)
         • lassociator _ _ _
         • (binprod_ump_2cell Hp α' β' ▹ l₃)
         • rassociator _ _ _
         • (_ ◃ ε₃)
         • runitor _.

    Definition has_binprod_ump_2_left_adjoint_equivalence_pr1
      : has_binprod_ump_2_left_adjoint_equivalence_cell ▹ ρ₁ = α.
    Proof.
      unfold has_binprod_ump_2_left_adjoint_equivalence_cell.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      do 3 (use vcomp_move_R_pM ; [ is_iso | ]).
      cbn - [ε₃].
      use (vcomp_lcancel (lassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      use (vcomp_lcancel (_ ◃ γ₁^-1)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      use (vcomp_lcancel (rassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply( binprod_ump_2cell_pr1 Hp).
      }
      use vcomp_move_R_Mp.
      {
        is_iso.
        apply ε₃.
      }
      cbn -[ε₃].
      rewrite !vassocl.
      apply (fully_faithful_1cell_inv_map_eq
               (adj_equiv_fully_faithful Hl₁)).
    Qed.

    Definition has_binprod_ump_2_left_adjoint_equivalence_pr2
      : has_binprod_ump_2_left_adjoint_equivalence_cell ▹ ρ₂ = β.
    Proof.
      unfold has_binprod_ump_2_left_adjoint_equivalence_cell.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      do 3 (use vcomp_move_R_pM ; [ is_iso | ]).
      cbn - [ε₃].
      use (vcomp_lcancel (lassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      use (vcomp_lcancel (_ ◃ γ₂^-1)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      use (vcomp_lcancel (rassociator _ _ _)).
      {
        is_iso.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply( binprod_ump_2cell_pr2 Hp).
      }
      use vcomp_move_R_Mp.
      {
        is_iso.
        apply ε₃.
      }
      cbn -[ε₃].
      rewrite !vassocl.
      apply (fully_faithful_1cell_inv_map_eq
               (adj_equiv_fully_faithful Hl₂)).
    Qed.
  End UMP2.

  Definition has_binprod_ump_2_left_adjoint_equivalence
    : binprod_ump_2 cone₂.
  Proof.
    intros c φ ψ α β.
    use iscontraprop1.
    - exact (has_binprod_ump_2_left_adjoint_equivalence_unique α β).
    - simple refine (_ ,, _ ,, _).
      + exact (has_binprod_ump_2_left_adjoint_equivalence_cell α β).
      + exact (has_binprod_ump_2_left_adjoint_equivalence_pr1 α β).
      + exact (has_binprod_ump_2_left_adjoint_equivalence_pr2 α β).
  Defined.

  Definition has_binprod_ump_left_adjoint_equivalence
    : has_binprod_ump cone₂.
  Proof.
    simple refine (_ ,, _).
    - exact has_binprod_ump_1_left_adjoint_equivalence.
    - exact has_binprod_ump_2_left_adjoint_equivalence.
  Defined.
End ProductEquivalence.
