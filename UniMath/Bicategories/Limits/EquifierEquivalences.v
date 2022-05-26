(************************************************************************

 Equivalences for equifiers

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.ContainsAdjEquiv.
Require Import UniMath.Bicategories.Limits.Equifiers.

Local Open Scope cat.

(**

  Suppose, we have a diagram as follows


                        ---- f₁ ---->
     p₁ ---- i₁ ----> x₁              y₁
                        ---- g₁ ---->
     |                |               |
     |                |               |
     l₃      ≃        l₁     ≃        l₂
     |                |               |
     |                |               |
     V                V               V
                        ---- f₂ ---->
     p₂ ---- i₂ ----> x₁              y₂
                        ---- g₂ ---->


  where the columns are adjoint equivalences and both rows are equifier cones.
  If the top row is an equifier, then so is the bottom row.

 *)
Section EquifierEquivalence.
  Context {B : bicat}
          {p₁ x₁ y₁ p₂ x₂ y₂ : B}
          {e₁ : p₁ --> x₁}
          {f₁ g₁ : x₁ --> y₁}
          {α₁ β₁ : f₁ ==> g₁}
          {e₂ : p₂ --> x₂}
          {f₂ g₂ : x₂ --> y₂}
          {α₂ β₂ : f₂ ==> g₂}
          (ep₁ : e₁ ◃ α₁ = e₁ ◃ β₁)
          (ep₂ : e₂ ◃ α₂ = e₂ ◃ β₂)
          (cone₁ := make_equifier_cone p₁ e₁ ep₁)
          (cone₂ := make_equifier_cone p₂ e₂ ep₂)
          (lx : x₁ --> x₂)
          (ly : y₁ --> y₂)
          (lp : p₁ --> p₂)
          (Hlx : left_adjoint_equivalence lx)
          (Hly : left_adjoint_equivalence ly)
          (Hlp : left_adjoint_equivalence lp)
          (γ₁ : invertible_2cell (lp · e₂) (e₁ · lx))
          (γ₂ : invertible_2cell (lx · f₂) (f₁ · ly))
          (γ₃ : invertible_2cell (lx · g₂) (g₁ · ly))
          (H : has_equifier_ump cone₁)
          (pα : lx ◃ α₂ • γ₃
                =
                γ₂ • (α₁ ▹ _))
          (pβ : lx ◃ β₂ • γ₃
                =
                γ₂ • (β₁ ▹ _)).

  Let rx : x₂ --> x₁
    := left_adjoint_right_adjoint Hlx.
  Let ηx : invertible_2cell (id₁ _) (lx · rx)
    := left_equivalence_unit_iso Hlx.
  Let εx : invertible_2cell (rx · lx) (id₁ _)
    := left_equivalence_counit_iso Hlx.

  Let ry : y₂ --> y₁
    := left_adjoint_right_adjoint Hly.
  Let ηy : invertible_2cell (id₁ _) (ly · ry)
    := left_equivalence_unit_iso Hly.
  Let εy : invertible_2cell (ry · ly) (id₁ _)
    := left_equivalence_counit_iso Hly.

  Let rp : p₂ --> p₁
    := left_adjoint_right_adjoint Hlp.
  Let ηp : invertible_2cell (id₁ _) (lp · rp)
    := left_equivalence_unit_iso Hlp.
  Let εp : invertible_2cell (rp · lp) (id₁ _)
    := left_equivalence_counit_iso Hlp.

  Definition has_equifier_ump_1_left_adjoint_equivalence_path
             (q : equifier_cone f₂ g₂ α₂ β₂)
    : equifier_cone_pr1 q · rx ◃ α₁
      =
      equifier_cone_pr1 q · rx ◃ β₁.
  Proof.
    use (adj_equiv_faithful Hly).
    use (vcomp_lcancel (lassociator _ _ _)).
    {
      is_iso.
    }
    rewrite <- !rwhisker_lwhisker.
    apply maponpaths_2.
    use (vcomp_lcancel (lassociator _ _ _)).
    {
      is_iso.
    }
    rewrite <- !lwhisker_lwhisker.
    apply maponpaths_2.
    use (vcomp_lcancel (_ ◃ (_ ◃ γ₂))).
    {
      is_iso.
      apply property_from_invertible_2cell.
    }
    rewrite !lwhisker_vcomp.
    rewrite <- pα, <- pβ.
    rewrite <- !lwhisker_vcomp.
    apply maponpaths_2.
    use (vcomp_lcancel (_ ◃ rassociator _ _ _)).
    {
      is_iso.
    }
    rewrite !lwhisker_vcomp.
    rewrite !lwhisker_lwhisker_rassociator.
    rewrite <- !lwhisker_vcomp.
    apply maponpaths_2.
    use (vcomp_lcancel (_ ◃ (εx^-1 ▹ _))).
    {
      is_iso.
    }
    rewrite !lwhisker_vcomp.
    rewrite !vcomp_whisker.
    rewrite <- !lwhisker_vcomp.
    apply maponpaths_2.
    use (vcomp_lcancel (_ ◃ linvunitor _)).
    {
      is_iso.
    }
    rewrite !lwhisker_vcomp.
    rewrite !lwhisker_hcomp.
    rewrite <- !linvunitor_natural.
    rewrite <- !lwhisker_hcomp.
    rewrite <- !lwhisker_vcomp.
    apply maponpaths_2.
    exact (equifier_cone_eq q).
  Qed.

  Definition has_equifier_ump_1_left_adjoint_equivalence_mor
             (q : equifier_cone f₂ g₂ α₂ β₂)
    : q --> p₂
    := equifier_ump_mor
         H
         (equifier_cone_pr1 q · rx)
         (has_equifier_ump_1_left_adjoint_equivalence_path q)
       · lp.

  Definition has_equifier_ump_1_left_adjoint_equivalence_pr1
             (q : equifier_cone f₂ g₂ α₂ β₂)
    : invertible_2cell
        (has_equifier_ump_1_left_adjoint_equivalence_mor q
         · equifier_cone_pr1 cone₂)
        (equifier_cone_pr1 q)
    := comp_of_invertible_2cell
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
                     (equifier_ump_mor_pr1 H _ _))
                  (comp_of_invertible_2cell
                     (rassociator_invertible_2cell _ _ _)
                     (comp_of_invertible_2cell
                        (lwhisker_of_invertible_2cell
                           _
                           εx)
                        (runitor_invertible_2cell _)))))).

  Definition has_equifier_ump_1_left_adjoint_equivalence
    : has_equifier_ump_1 cone₂.
  Proof.
    intro q.
    use make_equifier_1cell.
    - exact (has_equifier_ump_1_left_adjoint_equivalence_mor q).
    - exact (has_equifier_ump_1_left_adjoint_equivalence_pr1 q).
  Defined.

  Let γ₁' : invertible_2cell (rp · e₁) (e₂ · rx)
    := comp_of_invertible_2cell
         (rinvunitor_invertible_2cell _)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               ηx)
            (comp_of_invertible_2cell
               (lassociator_invertible_2cell _ _ _)
               (comp_of_invertible_2cell
                  (rwhisker_of_invertible_2cell
                     _
                     (rassociator_invertible_2cell _ _ _))
                  (comp_of_invertible_2cell
                     (rwhisker_of_invertible_2cell
                        _
                        (lwhisker_of_invertible_2cell
                           _
                           (inv_of_invertible_2cell γ₁)))
                     (comp_of_invertible_2cell
                        (rwhisker_of_invertible_2cell
                           _
                           (lassociator_invertible_2cell _ _ _))
                        (comp_of_invertible_2cell
                           (rwhisker_of_invertible_2cell
                              _
                              (rwhisker_of_invertible_2cell
                                 _
                                 εp))
                           (rwhisker_of_invertible_2cell
                              _
                              (lunitor_invertible_2cell _)))))))).

  Section UMP2.
    Context {z : B}
            (u₁ u₂ : z --> p₂)
            (ξ : u₁ · e₂ ==> u₂ · e₂).

    Let ξ' : u₁ · rp · e₁ ==> u₂ · rp · e₁
      := fully_faithful_1cell_inv_map
           (adj_equiv_fully_faithful Hlx)
           (rassociator _ _ _
            • (_ ◃ γ₁^-1)
            • lassociator _ _ _
            • (rassociator _ _ _ ▹ _)
            • ((_ ◃ εp) ▹ _)
            • (runitor _ ▹ _)
            • ξ
            • (rinvunitor _ ▹ _)
            • ((_ ◃ εp ^-1) ▹ _)
            • (lassociator _ _ _ ▹ _)
            • rassociator _ _ _
            • (_ ◃ γ₁)
            • lassociator _ _ _).

    Definition has_equifier_ump_2_left_adjoint_equivalence_cell
      : u₁ ==> u₂
      := rinvunitor _
         • (_ ◃ εp^-1)
         • lassociator _ _ _
         • (equifier_ump_cell H ξ' ▹ _)
         • rassociator _ _ _
         • (_ ◃ εp)
         • runitor _.

    Definition has_equifier_ump_2_left_adjoint_equivalence_pr1
      : has_equifier_ump_2_left_adjoint_equivalence_cell ▹ e₂ = ξ.
    Proof.
      unfold has_equifier_ump_2_left_adjoint_equivalence_cell.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      do 3 (use vcomp_move_R_pM ; [ is_iso | ]).
      cbn -[εp ξ'].
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      use (vcomp_lcancel (_ ◃ γ₁^-1)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (equifier_ump_cell_pr1 H ξ').
      }
      use vcomp_move_R_Mp.
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      cbn -[εp ξ'].
      rewrite !vassocr.
      apply fully_faithful_1cell_inv_map_eq.
    Qed.
  End UMP2.

  Definition has_equifier_ump_2_left_adjoint_equivalence
    : has_equifier_ump_2 cone₂.
  Proof.
    intros z u₁ u₂ ξ.
    simple refine (_ ,, _).
    - exact (has_equifier_ump_2_left_adjoint_equivalence_cell u₁ u₂ ξ).
    - exact (has_equifier_ump_2_left_adjoint_equivalence_pr1 u₁ u₂ ξ).
  Defined.

  Definition has_equifier_ump_eq_left_adjoint_equivalence
    : has_equifier_ump_eq cone₂.
  Proof.
    intros z u₁ u₂ ξ φ₁ φ₂ q₁ q₂.
    enough (φ₁ ▹ rp = φ₂ ▹ rp) as H'.
    {
      use (adj_equiv_faithful (inv_adjequiv (_ ,, Hlp))).
      exact H'.
    }
    use (equifier_ump_eq H) ; cbn.
    - simple refine (rassociator _ _ _
              • (_ ◃ γ₁')
              • lassociator _ _ _
              • (ξ ▹ _)
              • rassociator _ _ _
              • (_ ◃ (γ₁')^-1)
              • lassociator _ _ _) ; cbn.
    - rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn -[γ₁'].
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      {
        apply property_from_invertible_2cell.
      }
      cbn -[γ₁'].
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn.
      rewrite <- rwhisker_rwhisker_alt.
      apply maponpaths_2.
      apply maponpaths.
      exact q₁.
    - rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn -[γ₁'].
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      {
        apply property_from_invertible_2cell.
      }
      cbn -[γ₁'].
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn.
      rewrite <- rwhisker_rwhisker_alt.
      apply maponpaths_2.
      apply maponpaths.
      exact q₂.
  Qed.

  Definition has_equifier_ump_left_adjoint_equivalence
    : has_equifier_ump cone₂.
  Proof.
    refine (_ ,, _ ,, _).
    - exact has_equifier_ump_1_left_adjoint_equivalence.
    - exact has_equifier_ump_2_left_adjoint_equivalence.
    - exact has_equifier_ump_eq_left_adjoint_equivalence.
  Defined.
End EquifierEquivalence.
