(*****************************************************************************

 Properties of eso 1-cells

 Esos are defined as 1-cells that satisfy a certain lifting property with
 respect to fully faithful 1-cells. From this definition, we can deduce
 numerous properties about eso 1-cells.
 Note: these statements hold not only for esos, but for all classes of 1-cells
 defined via suitable lifting properties.

 Contents
 1. Identity is eso
 2. Adjoint equivalences are eso
 3. Esos are closed under invertible 2-cells
 4. Esos are closed under composition
 5. Eso+ff implies adjoint equivalence
 6. Factoring esos via ffs

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.Eso.
Require Import UniMath.Bicategories.Limits.Pullbacks.

Local Open Scope cat.

(**
 1. Identity is eso
 *)
Section IdEso.
  Context {B : bicat}
          (HB_2_1 : is_univalent_2_1 B)
          (b : B).

  Definition id_is_eso_full_eq_1
             {c₁ : B}
             {l₁ l₂ : b --> c₁}
             (k₁ : id₁ b · l₁ ==> id₁ b · l₂)
    : id₁ b ◃ ((linvunitor l₁ • k₁) • lunitor l₂) = k₁.
  Proof.
    rewrite <- !lwhisker_vcomp.
    use (vcomp_lcancel (lunitor _)) ; [ is_iso | ].
    refine (!_).
    etrans.
    {
      rewrite <- vcomp_lunitor.
      rewrite <- lunitor_triangle.
      rewrite lunitor_runitor_identity.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    refine (!(id2_left _) @ _).
    apply maponpaths_2.
    rewrite <- lunitor_triangle.
    rewrite lunitor_runitor_identity.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_r.
    rewrite <- lwhisker_hcomp.
    rewrite lwhisker_vcomp.
    rewrite lunitor_linvunitor.
    rewrite lwhisker_id2.
    apply idpath.
  Qed.

  Definition id_is_eso_full_eq_2
             {c₁ c₂ : B}
             (m : c₁ --> c₂)
             {l₁ l₂ : b --> c₁}
             (k₁ : id₁ b · l₁ ==> id₁ b · l₂)
             (k₂ : l₁ · m ==> l₂ · m)
             (p : (k₁ ▹ m) • rassociator (id₁ b) l₂ m
                  =
                  rassociator (id₁ b) l₁ m • (id₁ b ◃ k₂))
    : (linvunitor l₁ • k₁ • lunitor l₂) ▹ m = k₂.
  Proof.
    rewrite <- !rwhisker_vcomp.
    assert ((k₁ ▹ m)
            =
            rassociator _ _ _ • (id₁ b ◃ k₂) • lassociator _ _ _)
      as H.
    {
      use vcomp_move_L_Mp ; [ is_iso | ].
      exact p.
    }
    rewrite H.
    rewrite !vassocl.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    rewrite !vassocr.
    refine (_ @ id2_left _).
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite <- lunitor_triangle.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      apply id2_left.
    }
    rewrite rwhisker_vcomp.
    rewrite linvunitor_lunitor.
    apply id2_rwhisker.
  Qed.

  Definition id_is_eso_full
    : is_eso_full (id₁ b).
  Proof.
    intros c₁ c₂ m Hm l₁ l₂ k₁ k₂ p.
    simple refine (_ ,, _ ,, _).
    - exact (linvunitor _ • k₁ • lunitor _).
    - apply id_is_eso_full_eq_1.
    - apply id_is_eso_full_eq_2.
      exact p.
  Defined.

  Definition id_is_eso_faithful
    : is_eso_faithful (id₁ b).
  Proof.
    intros c₁ c₂ m Hm l₁ l₂ ζ₁ ζ₂ p₁ p₂.
    use (vcomp_lcancel (lunitor _)) ; [ is_iso | ].
    rewrite <- !vcomp_lunitor.
    rewrite p₁.
    apply idpath.
  Qed.

  Definition id_is_eso_essentially_surjective_eq
             {c₁ c₂ : B}
             {m : c₁ --> c₂}
             (g₁ : b --> c₁)
             (g₂ : b --> c₂)
             (α : invertible_2cell (g₁ · m) (id₁ b · g₂))
    : (lunitor g₁ ▹ m) • α
      =
      rassociator (id₁ b) g₁ m • (id₁ b ◃ (α • lunitor g₂)).
  Proof.
    rewrite <- !lwhisker_vcomp.
    use vcomp_move_L_pM ; [ is_iso | ].
    cbn.
    rewrite !vassocr.
    rewrite lunitor_triangle.
    rewrite <- vcomp_lunitor.
    apply maponpaths.
    rewrite <- lunitor_triangle.
    rewrite lunitor_runitor_identity.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_r.
    rewrite <- lwhisker_hcomp.
    apply idpath.
  Qed.

  Definition id_is_eso_essentially_surjective
    : is_eso_essentially_surjective (id₁ b).
  Proof.
    intros c₁ c₂ m Hm g₁ g₂ α.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact g₁.
    - exact (lunitor_invertible_2cell _).
    - exact (comp_of_invertible_2cell α (lunitor_invertible_2cell _)).
    - apply id_is_eso_essentially_surjective_eq.
  Defined.

  Definition id_is_eso
    : is_eso (id₁ b).
  Proof.
    use make_is_eso.
    - exact HB_2_1.
    - exact id_is_eso_full.
    - exact id_is_eso_faithful.
    - exact id_is_eso_essentially_surjective.
  Defined.
End IdEso.

(**
 2. Adjoint equivalences are eso
 *)
Section AdjequivEso.
  Context {B : bicat}
          (HB_2_1 : is_univalent_2_1 B)
          {b₁ b₂ : B}
          {l : b₁ --> b₂}
          (Hl : left_adjoint_equivalence l).

  Let r : b₂ --> b₁
    := left_adjoint_right_adjoint Hl.
  Let η : invertible_2cell (id₁ _) (l · r)
    := left_equivalence_unit_iso Hl.
  Let ε : invertible_2cell (r · l) (id₁ _)
    := left_equivalence_counit_iso Hl.

  Section AdjEquivEsoFull.
    Context {c₁ c₂ : B}
            {m : c₁ --> c₂}
            (Hm : fully_faithful_1cell m)
            {f₁ f₂ : b₂ --> c₁}
            (k₁ : l · f₁ ==> l · f₂)
            (k₂ : f₁ · m ==> f₂ · m)
            (p : (k₁ ▹ m) • rassociator l f₂ m
                 =
                 rassociator l f₁ m • (l ◃ k₂)).

    Definition adj_equiv_is_eso_lift_2
      : f₁ ==> f₂
      := linvunitor _
         • (ε^-1 ▹ _)
         • rassociator _ _ _
         • (_ ◃ k₁)
         • lassociator _ _ _
         • (ε ▹ _)
         • lunitor _.

    Definition adj_equiv_is_eso_lift_2_left
      : l ◃ adj_equiv_is_eso_lift_2 = k₁.
    Proof.
      unfold adj_equiv_is_eso_lift_2.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      use (vcomp_lcancel (lunitor _)) ; [ is_iso | ] ; cbn -[ε].
      refine (!_).
      rewrite <- vcomp_lunitor.
      use (vcomp_lcancel (η^-1 ▹ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      assert (lassociator _ _ _
              • (η ^-1 ▹ _)
              • lunitor _
              • (_ ◃ linvunitor f₁)
              • (_ ◃ (ε ^-1 ▹ _))
              • (_ ◃ rassociator _ _ _)
              =
              id2 _)
        as p'.
      {
        rewrite !vassocl.
        do 2 (use vcomp_move_R_pM ; [ is_iso | ]) ; cbn -[η ε].
        rewrite !vassocr.
        do 2 (use vcomp_move_R_Mp ; [ is_iso | ]) ; cbn -[η ε].
        rewrite id2_right.
        rewrite <- lunitor_triangle.
        rewrite !vassocl.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn -[η ε].
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker_alt.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite <- rassociator_rassociator.
          rewrite !vassocl.
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite rassociator_lassociator.
          rewrite lwhisker_id2.
          apply id2_left.
        }
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocr.
        use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[η ε].
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite lwhisker_hcomp.
          rewrite triangle_l_inv.
          rewrite <- rwhisker_hcomp.
          apply idpath.
        }
        rewrite !rwhisker_vcomp.
        apply maponpaths.
        use vcomp_move_R_pM ; [ is_iso | ] ; cbn -[η ε].
        refine (!(id2_left _) @ _).
        use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[η ε].
        rewrite !vassocr.
        exact (!(internal_triangle1 Hl)).
      }
      rewrite !vassocr.
      rewrite p'.
      rewrite id2_left.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lunitor_triangle.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- lassociator_lassociator.
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn -[η ε].
      rewrite !vassocr.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      do 2 (use vcomp_move_R_pM ; [ is_iso | ]) ; cbn -[η ε].
      refine (!(id2_right _) @ _).
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn -[η ε].
      rewrite !vassocr.
      refine (!_).
      exact (internal_triangle1 Hl).
    Qed.

    Definition adj_equiv_is_eso_lift_2_right
      : adj_equiv_is_eso_lift_2 ▹ m = k₂.
    Proof.
      unfold adj_equiv_is_eso_lift_2.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      do 3 (use vcomp_move_R_pM ; [ is_iso | ]) ; cbn -[ε].
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      assert (k₁ ▹ m = rassociator _ _ _ • (_ ◃ k₂) • lassociator _ _ _) as p'.
      {
        use vcomp_move_L_Mp ; [ is_iso | ].
        exact p.
      }
      rewrite p' ; clear p'.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        rewrite lunitor_triangle.
        apply idpath.
      }
      do 2 (use vcomp_move_L_pM ; [ is_iso | ]).
      cbn -[ε].
      rewrite !vassocr.
      rewrite rassociator_rassociator.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        rewrite vcomp_lunitor.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      apply id2_left.
    Qed.
  End AdjEquivEsoFull.

  Definition adj_equiv_is_eso_full
    : is_eso_full l.
  Proof.
    intros c₁ c₂ m Hm f₁ f₂ k₁ k₂ p.
    simple refine (_ ,, _ ,, _).
    - apply adj_equiv_is_eso_lift_2.
      exact k₁.
    - exact (adj_equiv_is_eso_lift_2_left k₁).
    - apply adj_equiv_is_eso_lift_2_right.
      exact p.
  Defined.

  Definition adj_equiv_is_eso_faithful
    : is_eso_faithful l.
  Proof.
    intros c₁ c₂ m Hm f₁ f₂ ζ₁ ζ₂ p₁ p₂.
    use (vcomp_lcancel (lunitor _)) ; [ is_iso | ].
    rewrite <- !vcomp_lunitor.
    use (vcomp_lcancel (ε ▹ _)).
    {
      is_iso.
      apply property_from_invertible_2cell.
    }
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vcomp_whisker.
    apply maponpaths_2.
    use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
    rewrite <- !lwhisker_lwhisker.
    apply maponpaths_2.
    rewrite p₁.
    apply idpath.
  Qed.

  Section AdjEquivEssentiallySurjective.
    Context {c₁ c₂ : B}
            {m : c₁ --> c₂}
            (Hm : fully_faithful_1cell m)
            (g₁ : b₁ --> c₁)
            (g₂ : b₂ --> c₂)
            (α : invertible_2cell (g₁ · m) (l · g₂)).

    Definition adj_equiv_is_eso_essentially_surjective_lift_1
      : b₂ --> c₁
      := r · g₁.

    Definition adj_equiv_is_eso_essentially_surjective_lift_1_left
      : invertible_2cell
          (l · adj_equiv_is_eso_essentially_surjective_lift_1)
          g₁
      := comp_of_invertible_2cell
           (lassociator_invertible_2cell _ _ _)
           (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell η))
              (lunitor_invertible_2cell _)).

    Definition adj_equiv_is_eso_essentially_surjective_lift_1_right
      : invertible_2cell
          (adj_equiv_is_eso_essentially_surjective_lift_1 · m)
          g₂
      := comp_of_invertible_2cell
           (rassociator_invertible_2cell _ _ _)
           (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell _ α)
              (comp_of_invertible_2cell
                 (lassociator_invertible_2cell _ _ _)
                 (comp_of_invertible_2cell
                    (rwhisker_of_invertible_2cell _ ε)
                    (lunitor_invertible_2cell _)))).

    Definition adj_equiv_is_eso_essentially_surjective_eq
      : (adj_equiv_is_eso_essentially_surjective_lift_1_left ▹ m) • α
        =
        rassociator _ _ _ • (l ◃ adj_equiv_is_eso_essentially_surjective_lift_1_right).
    Proof.
      cbn -[ε η].
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn -[ε η].
      rewrite !vassocr.
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths_2.
        apply rassociator_rassociator.
      }
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn -[ε η].
      rewrite !vassocr.
      rewrite lwhisker_lwhisker_rassociator.
      rewrite rwhisker_rwhisker.
      refine (!_).
      etrans.
      {
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lunitor_triangle.
        rewrite <- vcomp_lunitor.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_hcomp.
        rewrite inverse_pentagon_4.
        rewrite <- rwhisker_hcomp.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite lwhisker_hcomp.
        rewrite triangle_l.
        rewrite <- rwhisker_hcomp.
        apply idpath.
      }
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn -[η ε].
      refine (_ @ id2_right _).
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn -[η ε].
      rewrite !vassocr.
      exact (internal_triangle1 Hl).
    Qed.
  End AdjEquivEssentiallySurjective.

  Definition adj_equiv_is_eso_essentially_surjective
    : is_eso_essentially_surjective l.
  Proof.
    intros c₁ c₂ m Hm g₁ g₂ α.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (adj_equiv_is_eso_essentially_surjective_lift_1 g₁).
    - exact (adj_equiv_is_eso_essentially_surjective_lift_1_left g₁).
    - exact (adj_equiv_is_eso_essentially_surjective_lift_1_right _ _ α).
    - exact (adj_equiv_is_eso_essentially_surjective_eq _ _ α).
  Defined.

  Definition adj_equiv_is_eso
    : is_eso l.
  Proof.
    use make_is_eso.
    - exact HB_2_1.
    - exact adj_equiv_is_eso_full.
    - exact adj_equiv_is_eso_faithful.
    - exact adj_equiv_is_eso_essentially_surjective.
  Defined.
End AdjequivEso.

(**
 3. Esos are closed under invertible 2-cells
 *)
Section EsoClosedUnderInvertible.
  Context {B : bicat}
          (HB_2_1 : is_univalent_2_1 B)
          {b₁ b₂ : B}
          {e₁ e₂ : b₁ --> b₂}
          (He : is_eso e₁)
          (α : e₁ ==> e₂)
          (Hα : is_invertible_2cell α).

  Definition invertible_is_eso_full
    : is_eso_full e₂.
  Proof.
    intros c₁ c₂ m Hm l₁ l₂ k₁ k₂ p.
    simple refine (_ ,, _ ,, _).
    - simple refine (is_eso_lift_2 _ He Hm l₁ l₂ _ k₂ _).
      + exact ((α ▹ l₁) • k₁ • (Hα^-1 ▹ l₂)).
      + abstract
          (rewrite <- !rwhisker_vcomp ;
           rewrite !vassocl ;
           rewrite rwhisker_rwhisker_alt ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocl ;
           rewrite p ;
           rewrite <- vcomp_whisker ;
           rewrite !vassocr ;
           apply maponpaths_2 ;
           rewrite rwhisker_rwhisker_alt ;
           apply idpath).
    - abstract
        (cbn ;
         use (vcomp_lcancel (α ▹ _)) ; [ is_iso | ] ;
         rewrite vcomp_whisker ;
         rewrite is_eso_lift_2_left ;
         rewrite !vassocl ;
         rewrite rwhisker_vcomp ;
         rewrite vcomp_linv ;
         rewrite id2_rwhisker ;
         rewrite id2_right ;
         apply idpath).
    - apply is_eso_lift_2_right.
  Defined.

  Definition invertible_is_eso_faithful
    : is_eso_faithful e₂.
  Proof.
    intros c₁ c₂ m Hm l₁ l₂ ζ₁ ζ₂ p₁ p₂.
    refine (is_eso_lift_eq _ He Hm _ _ _ p₂).
    use (vcomp_rcancel (α ▹ _)) ; [ is_iso | ].
    rewrite <- !vcomp_whisker.
    rewrite p₁.
    apply idpath.
  Qed.

  Definition invertible_is_eso_essentially_surjective
    : is_eso_essentially_surjective e₂.
  Proof.
    intros c₁ c₂ m Hm g₁ g₂ γ.
    pose (αinv := make_invertible_2cell Hα).
    pose (γhelp := comp_of_invertible_2cell
                     γ
                     (rwhisker_of_invertible_2cell
                        _
                        (inv_of_invertible_2cell αinv))).
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (is_eso_lift_1 _ He Hm g₁ g₂ γhelp).
    - exact (comp_of_invertible_2cell
               (rwhisker_of_invertible_2cell
                  _
                  (inv_of_invertible_2cell αinv))
               (is_eso_lift_1_comm_left _ He Hm g₁ g₂ γhelp)).
    - exact (is_eso_lift_1_comm_right _ He Hm g₁ g₂ γhelp).
    - abstract
        (cbn -[is_eso_lift_1_comm_left is_eso_lift_1_comm_right] ;
         pose (is_eso_lift_1_eq _ He Hm g₁ g₂ γhelp) as p ;
         cbn -[is_eso_lift_1_comm_left is_eso_lift_1_comm_right] in p ;
         use (vcomp_rcancel (Hα^-1 ▹ _)) ; [ is_iso | ] ;
         rewrite <- !rwhisker_vcomp ;
         rewrite !vassocl ;
         rewrite p ;
         rewrite !vassocr ;
         rewrite rwhisker_rwhisker_alt ;
         rewrite !vassocl ;
         rewrite vcomp_whisker ;
         apply idpath).
  Defined.

  Definition invertible_is_eso
    : is_eso e₂.
  Proof.
    use make_is_eso.
    - exact HB_2_1.
    - exact invertible_is_eso_full.
    - exact invertible_is_eso_faithful.
    - exact invertible_is_eso_essentially_surjective.
  Defined.
End EsoClosedUnderInvertible.

(**
 4. Esos are closed under composition
 *)
Section EsoClosedUnderComposition.
  Context {B : bicat}
          (HB_2_1 : is_univalent_2_1 B)
          {b₁ b₂ b₃ : B}
          {e₁ : b₁ --> b₂}
          (He₁ : is_eso e₁)
          {e₂ : b₂ --> b₃}
          (He₂ : is_eso e₂).

  Section CompositionFull.
    Context {c₁ c₂ : B}
            {m : c₁ --> c₂}
            (Hm : fully_faithful_1cell m)
            (l₁ l₂ : b₃ --> c₁)
            (k₁ : e₁ · e₂ · l₁ ==> e₁ · e₂ · l₂)
            (k₂ : l₁ · m ==> l₂ · m)
            (p : (k₁ ▹ m) • rassociator (e₁ · e₂) l₂ m
                 =
                 rassociator (e₁ · e₂) l₁ m • (e₁ · e₂ ◃ k₂)).

    Local Lemma composition_is_eso_full_lift_path_1
      : ((lassociator _ _ _ • k₁ • rassociator _ _ _) ▹ m)
        • rassociator _ _ _
        =
        rassociator _ _ _
        • (e₁ ◃ (rassociator _ _ _ • (e₂ ◃ k₂) • lassociator _ _ _)).
    Proof.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite p.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- rassociator_rassociator.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    Qed.

    Definition composition_is_eso_full_lift_1
      : e₂ · l₁ ==> e₂ · l₂
      := is_eso_lift_2
           _
           He₁
           Hm
           (e₂ · l₁) (e₂ · l₂)
           (lassociator _ _ _ • k₁ • rassociator _ _ _)
           (rassociator _ _ _ • (e₂ ◃ k₂) • lassociator _ _ _)
           composition_is_eso_full_lift_path_1.

    Let ℓ := composition_is_eso_full_lift_1.

    Local Lemma composition_is_eso_full_lift_path_2
      : (ℓ ▹ m) • rassociator _ _ _
        =
        rassociator _ _ _ • (e₂ ◃ k₂).
    Proof.
      unfold ℓ, composition_is_eso_full_lift_1.
      rewrite is_eso_lift_2_right.
      rewrite !vassocl.
      rewrite lassociator_rassociator.
      rewrite id2_right.
      apply idpath.
    Qed.

    Definition composition_is_eso_full_lift
      : l₁ ==> l₂
      := is_eso_lift_2
           _
           He₂
           Hm
           l₁ l₂
           ℓ
           k₂
           composition_is_eso_full_lift_path_2.

    Definition composition_is_eso_full_lift_left
      : e₁ · e₂ ◃ composition_is_eso_full_lift
        =
        k₁.
    Proof.
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite <- lwhisker_lwhisker.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply is_eso_lift_2_left.
      }
      etrans.
      {
        apply maponpaths_2.
        apply is_eso_lift_2_left.
      }
      rewrite !vassocl.
      rewrite rassociator_lassociator.
      rewrite id2_right.
      apply idpath.
    Qed.

    Definition composition_is_eso_full_lift_right
      : composition_is_eso_full_lift ▹ m
        =
        k₂.
    Proof.
      apply is_eso_lift_2_right.
    Qed.
  End CompositionFull.

  Definition composition_is_eso_full
    : is_eso_full (e₁ · e₂).
  Proof.
    intros c₁ c₂ m Hm l₁ l₂ k₁ k₂ p.
    simple refine (_ ,, _ ,, _).
    - exact (composition_is_eso_full_lift Hm _ _ _ _ p).
    - exact (composition_is_eso_full_lift_left Hm _ _ _ _ p).
    - exact (composition_is_eso_full_lift_right Hm _ _ _ _ p).
  Defined.

  Definition composition_is_eso_faithful
    : is_eso_faithful (e₁ · e₂).
  Proof.
    intros c₁ c₂ m Hm l₁ l₂ ζ₁ ζ₂ p₁ p₂.
    use (is_eso_lift_eq _ He₂ Hm _ _ _ p₂).
    use (is_eso_lift_eq _ He₁ Hm _ _ _).
    - use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !lwhisker_lwhisker.
      rewrite p₁.
      apply idpath.
    - use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite <- !rwhisker_lwhisker.
      rewrite p₂.
      apply idpath.
  Qed.

  Section CompositionEssentiallySurjective.
    Context {c₁ c₂ : B}
            {m : c₁ --> c₂}
            (Hm : fully_faithful_1cell m)
            (g₁ : b₁ --> c₁)
            (g₂ : b₃ --> c₂)
            (α : invertible_2cell (g₁ · m) (e₁ · e₂ · g₂)).

    Let γ : invertible_2cell (g₁ · m) (e₁ · (e₂ · g₂))
      := comp_of_invertible_2cell
           α
           (rassociator_invertible_2cell _ _ _).

    Let ℓ : b₂ --> c₁
      := is_eso_lift_1 _ He₁ Hm g₁ (e₂ · g₂) γ.

    Let γ' : invertible_2cell (ℓ · m) (e₂ · g₂)
      := is_eso_lift_1_comm_right _ He₁ Hm g₁ (e₂ · g₂) γ.

    Definition composition_is_eso_lift_1
      : b₃ --> c₁
      := is_eso_lift_1 _ He₂ Hm ℓ g₂ γ'.

    Definition composition_is_eso_lift_1_left
      : invertible_2cell
          (e₁ · e₂ · composition_is_eso_lift_1)
          g₁
      := comp_of_invertible_2cell
           (rassociator_invertible_2cell _ _ _)
           (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (is_eso_lift_1_comm_left _ _ _ _ _ _))
              (is_eso_lift_1_comm_left _ _ _ _ _ _)).

    Definition composition_is_eso_lift_1_right
      : invertible_2cell
          (composition_is_eso_lift_1 · m)
          g₂
      := is_eso_lift_1_comm_right _ _ _ _ _ _.

    Definition composition_is_eso_lift_1_eq
      : (composition_is_eso_lift_1_left ▹ m) • α
        =
        rassociator _ _ _ • (e₁ · e₂ ◃ composition_is_eso_lift_1_right).
    Proof.
      cbn -[is_eso_lift_1_comm_left is_eso_lift_1_comm_right].
      pose (is_eso_lift_1_eq _ He₂ Hm ℓ g₂ γ') as p1.
      pose (is_eso_lift_1_eq _ He₁ Hm g₁ (e₂ · g₂) γ) as p2.
      cbn -[is_eso_lift_1_comm_left is_eso_lift_1_comm_right] in p1, p2.
      use (vcomp_rcancel (rassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocl.
      rewrite <- lwhisker_lwhisker_rassociator.
      assert (e₂ ◃ is_eso_lift_1_comm_right e₂ He₂ Hm ℓ g₂ γ'
              =
              lassociator _ _ _
              • (is_eso_lift_1_comm_left e₂ He₂ Hm ℓ g₂ γ' ▹ m)
              • γ')
        as p1'.
      {
        rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ].
        exact (!p1).
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        exact p1'.
      }
      clear p1 p1'.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- rassociator_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator.
        rewrite lwhisker_id2.
        rewrite id2_left.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact p2.
      }
      clear p2.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      apply idpath.
    Qed.
  End CompositionEssentiallySurjective.

  Definition composition_is_eso_essentially_surjective
    : is_eso_essentially_surjective (e₁ · e₂).
  Proof.
    intros c₁ c₂ m Hm g₁ g₂ α.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (composition_is_eso_lift_1 Hm _ _ α).
    - exact (composition_is_eso_lift_1_left Hm _ _ α).
    - exact (composition_is_eso_lift_1_right Hm _ _ α).
    - exact (composition_is_eso_lift_1_eq Hm _ _ α).
  Defined.

  Definition composition_is_eso
    : is_eso (e₁ · e₂).
  Proof.
    use make_is_eso.
    - exact HB_2_1.
    - exact composition_is_eso_full.
    - exact composition_is_eso_faithful.
    - exact composition_is_eso_essentially_surjective.
  Defined.
End EsoClosedUnderComposition.

(**
 5. Eso+ff implies adjoint equivalence
 *)
Section EsoAndFF.
  Context {B : bicat}
          {b₁ b₂ : B}
          {e : b₁ --> b₂}
          (He₁ : is_eso e)
          (He₂ : fully_faithful_1cell e).

  Let α : invertible_2cell (id₁ b₁ · e) (e · id₁ b₂)
    := comp_of_invertible_2cell
         (lunitor_invertible_2cell _)
         (rinvunitor_invertible_2cell _).

  Definition eso_ff_is_equiv
    : left_equivalence e.
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
    - exact (is_eso_lift_1 _ He₁ He₂ (id₁ _) (id₁ _) α).
    - exact (inv_of_invertible_2cell (is_eso_lift_1_comm_left _ He₁ He₂ (id₁ _) (id₁ _) α)).
    - exact ((is_eso_lift_1_comm_right _ He₁ He₂ (id₁ _) (id₁ _) α)).
    - apply property_from_invertible_2cell.
    - apply property_from_invertible_2cell.
  Defined.

  Definition eso_ff_is_adj_equiv
    : left_adjoint_equivalence e.
  Proof.
    use equiv_to_adjequiv.
    exact eso_ff_is_equiv.
  Defined.
End EsoAndFF.

(**
 6. Factoring esos via ffs
 *)
(**
 If we can factor an eso

            e
     x₁ -----------> x₂

 as
     x₁ ---> x₂ ---> x₃
         f       m

 where m is ff, then m is an equivalence

 Note: this property only holds for esos and it doesn't generalize to
 arbitrary classes of morphisms defined via lifting properties.
 *)
Section FactorEso.
  Context {B : bicat}
          {x₁ x₂ x₃ : B}
          {e : x₁ --> x₃}
          (He : is_eso e)
          {f : x₁ --> x₂}
          {m : x₂ --> x₃}
          (Hm: fully_faithful_1cell m)
          (γ : invertible_2cell (f · m) e).

  Let γ' : invertible_2cell (f · m) (e · id₁ x₃)
    := comp_of_invertible_2cell γ (rinvunitor_invertible_2cell _).

  Let inv : x₃ --> x₂
    := is_eso_lift_1 _ He Hm f (id₁ _) γ'.
  Let ε : invertible_2cell (inv · m) (id₁ x₃)
    := is_eso_lift_1_comm_right _ He Hm f (id₁ _) γ'.

  Definition factor_eso_ff_equiv
    : left_equivalence m.
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
    - exact inv.
    - use (fully_faithful_1cell_inv_map Hm).
      exact (lunitor _ • rinvunitor _ • (m ◃ ε^-1) • lassociator _ _ _).
    - exact ε.
    - apply (fully_faithful_to_conservative Hm).
      use (eq_is_invertible_2cell
             (!(fully_faithful_1cell_inv_map_eq Hm _))).
      cbn -[ε].
      is_iso.
    - apply property_from_invertible_2cell.
  Defined.

  Definition factor_eso_ff_adj_equiv
    : left_adjoint_equivalence m.
  Proof.
    use equiv_to_adjequiv.
    exact factor_eso_ff_equiv.
  Defined.
End FactorEso.
