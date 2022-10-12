(****************************************************************************

 Pullbacks and equivalences

 Content:
 1. Any two pullbacks are equivalent
 2. Objects equivalent to pullbacks are pullbacks themselves

 ****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderInvertibles.
Require Import UniMath.Bicategories.Limits.Pullbacks.

Local Open Scope cat.

(**
 1. Any two pullbacks are equivalent
 *)
Section UmpMorEquiv.
  Context {B : bicat}
          {b₁ b₂ b₃ : B}
          {f : b₁ --> b₃}
          {g : b₂ --> b₃}
          (cone₁ cone₂ : pb_cone f g)
          (H₁ : has_pb_ump cone₁)
          (H₂ : has_pb_ump cone₂).

  Definition pb_ump_mor_left_adjoint_equivalence_unit_pr1
    : id₁ cone₂ · pb_cone_pr1 cone₂
      ==>
      pr1 (pr1 H₁ cone₂) · pb_ump_mor H₂ cone₁ · pb_cone_pr1 cone₂
    := lunitor _
       • (pb_ump_mor_pr1 H₁ cone₂)^-1
       • (_ ◃ (pb_ump_mor_pr1 H₂ cone₁)^-1)
       • lassociator _ _ _.

  Definition pb_ump_mor_left_adjoint_equivalence_unit_pr2
    : id₁ cone₂ · pb_cone_pr2 cone₂
      ==>
      pr1 (pr1 H₁ cone₂) · pb_ump_mor H₂ cone₁ · pb_cone_pr2 cone₂
    := lunitor _
       • (pb_ump_mor_pr2 H₁ cone₂)^-1
       • (_ ◃ (pb_ump_mor_pr2 H₂ cone₁)^-1)
       • lassociator _ _ _.

  Definition pb_ump_mor_left_adjoint_equivalence_unit_cell
    : (_ ◃ pb_cone_cell cone₂)
      • lassociator _ _ _
      • (pb_ump_mor_left_adjoint_equivalence_unit_pr2 ▹ _)
      • rassociator _ _ _
      =
      lassociator _ _ _
      • (pb_ump_mor_left_adjoint_equivalence_unit_pr1 ▹ _)
      • rassociator _ _ _
      • (_ ◃ pb_cone_cell cone₂).
  Proof.
    unfold pb_ump_mor_left_adjoint_equivalence_unit_pr1.
    unfold pb_ump_mor_left_adjoint_equivalence_unit_pr2.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_triangle.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      rewrite lunitor_triangle.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    use (vcomp_rcancel (rassociator _ _ _)) ; [ is_iso | ].
    rewrite !vassocl.
    rewrite <- lwhisker_lwhisker_rassociator.
    rewrite <- rassociator_rassociator.
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_left.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rassociator_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite (pb_ump_mor_cell H₂).
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp, rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker, lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      exact (pb_ump_mor_cell H₁ cone₂).
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    do 2 apply maponpaths.
    rewrite rwhisker_lwhisker_rassociator.
    apply idpath.
  Qed.

  Definition pb_ump_mor_left_adjoint_equivalence_unit
    : id₁ cone₂
      ==>
      pr1 (pr1 H₁ cone₂) · pb_ump_mor H₂ cone₁.
  Proof.
    use (pb_ump_cell H₂) ; cbn.
    - exact pb_ump_mor_left_adjoint_equivalence_unit_pr1.
    - exact pb_ump_mor_left_adjoint_equivalence_unit_pr2.
    - exact pb_ump_mor_left_adjoint_equivalence_unit_cell.
  Defined.

  Definition pb_ump_mor_left_adjoint_equivalence_unit_inv2cell
    : is_invertible_2cell pb_ump_mor_left_adjoint_equivalence_unit.
  Proof.
    use is_invertible_2cell_pb_ump_cell.
    - unfold pb_ump_mor_left_adjoint_equivalence_unit_pr1.
      is_iso.
    - unfold pb_ump_mor_left_adjoint_equivalence_unit_pr2.
      is_iso.
  Defined.
End UmpMorEquiv.

Definition pb_ump_mor_left_adjoint_equivalence
           {B : bicat}
           {b₁ b₂ b₃ : B}
           {f : b₁ --> b₃}
           {g : b₂ --> b₃}
           (cone₁ cone₂ : pb_cone f g)
           (H₁ : has_pb_ump cone₁)
           (H₂ : has_pb_ump cone₂)
  : left_adjoint_equivalence (pb_ump_mor H₁ cone₂).
Proof.
  use equiv_to_adjequiv.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (pb_ump_mor H₂ cone₁).
  - exact (pb_ump_mor_left_adjoint_equivalence_unit cone₁ cone₂ H₁ H₂).
  - exact ((pb_ump_mor_left_adjoint_equivalence_unit_inv2cell cone₂ cone₁ H₂  H₁)^-1).
  - apply pb_ump_mor_left_adjoint_equivalence_unit_inv2cell.
  - apply is_invertible_2cell_inv.
Defined.

(**
 2. Objects equivalent to pullbacks are pullbacks themselves
 *)
Section IdEquivalenceToPB.
  Context {B : bicat}
          {b₁ b₂ b₃ : B}
          {f : b₁ --> b₃}
          {g : b₂ --> b₃}
          {q : B}
          {qpr1 qpr1' : q --> b₁}
          {qpr2 qpr2' : q --> b₂}
          (qγ : invertible_2cell (qpr1 · f) (qpr2 · g))
          (qγ' : invertible_2cell (qpr1' · f) (qpr2' · g))
          (H₂ : has_pb_ump (make_pb_cone q qpr1' qpr2' qγ'))
          (lpr1 : invertible_2cell qpr1 qpr1')
          (lpr2 : invertible_2cell qpr2 qpr2')
          (lc : qγ • (lpr2 ▹ g) = (lpr1 ▹ f) • qγ').

  Definition id_left_adjoint_equivalence_to_pb_ump_1
    : pb_ump_1 (make_pb_cone q qpr1 qpr2 qγ).
  Proof.
    intro qc.
    use make_pb_1cell.
    - exact (pb_ump_mor H₂ qc).
    - exact (comp_of_invertible_2cell
               (lwhisker_of_invertible_2cell _ lpr1)
               (pb_ump_mor_pr1 H₂ qc)).
    - exact (comp_of_invertible_2cell
               (lwhisker_of_invertible_2cell _ lpr2)
               (pb_ump_mor_pr2 H₂ qc)).
    - abstract
        (cbn ;
         use (vcomp_rcancel (_ ◃ (lpr2 ▹ g))) ;
         [ is_iso ; apply property_from_invertible_2cell | ] ;
         rewrite lwhisker_vcomp ;
         rewrite lc ;
         rewrite <- lwhisker_vcomp ;
         refine (maponpaths (λ z, _ • z) (pb_ump_mor_cell H₂ qc) @ _) ;
         cbn ;
         rewrite !vassocr ;
         rewrite rwhisker_lwhisker ;
         rewrite !vassocl ;
         apply maponpaths ;
         rewrite <- rwhisker_vcomp ;
         rewrite !vassocl ;
         do 3 apply maponpaths ;
         rewrite rwhisker_lwhisker_rassociator ;
         rewrite !vassocr ;
         apply maponpaths_2 ;
         rewrite rwhisker_vcomp ;
         rewrite !vassocl ;
         rewrite lwhisker_vcomp ;
         rewrite vcomp_linv ;
         rewrite lwhisker_id2 ;
         rewrite id2_right ;
         apply idpath).
  Defined.

  Section UMP2.
    Context {qc : B}
            {φ ψ : qc --> q}
            (α : φ · qpr1 ==> ψ · qpr1)
            (β : φ · qpr2 ==> ψ · qpr2)
            (p : (φ ◃ qγ) • lassociator _ _ _ • (β ▹ g) • rassociator _ _ _
                 =
                 lassociator _ _ _ • (α ▹ f) • rassociator _ _ _ • (ψ ◃ qγ)).

    Lemma id_left_adjoint_equivalence_to_pb_ump_2_cell_eq
      : (φ ◃ qγ')
          • lassociator _ _ _
          • (((φ ◃ lpr2 ^-1) • β • (ψ ◃ lpr2)) ▹ g)
          • rassociator _ _ _
        =
        lassociator _ _ _
        • (((φ ◃ lpr1 ^-1) • α • (ψ ◃ lpr1)) ▹ f)
        • rassociator ψ qpr1' f
        • (ψ ◃ qγ').
    Proof.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      refine (!_).
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite <- lc.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lwhisker_vcomp.
        rewrite vcomp_rinv.
        rewrite lwhisker_id2.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        rewrite <- rwhisker_lwhisker_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite p.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite lwhisker_vcomp.
      rewrite lc.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_lwhisker_rassociator.
      apply idpath.
    Qed.

    Definition id_left_adjoint_equivalence_to_pb_ump_2_cell
      : φ ==> ψ.
    Proof.
      use (pb_ump_cell H₂).
      - exact ((_ ◃ lpr1^-1) • α • (_ ◃ lpr1)).
      - exact ((_ ◃ lpr2^-1) • β • (_ ◃ lpr2)).
      - exact id_left_adjoint_equivalence_to_pb_ump_2_cell_eq.
    Defined.

    Definition id_left_adjoint_equivalence_to_pb_ump_2_cell_pr1
      : id_left_adjoint_equivalence_to_pb_ump_2_cell ▹ qpr1
        =
        α.
    Proof.
      unfold id_left_adjoint_equivalence_to_pb_ump_2_cell.
      use (vcomp_lcancel (φ ◃ lpr1 ^-1)).
      {
        is_iso.
      }
      use (vcomp_rcancel (ψ ◃ lpr1)).
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      rewrite <- vcomp_whisker.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply (pb_ump_cell_pr1 H₂).
      }
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      rewrite id2_right.
      apply idpath.
    Qed.

    Definition id_left_adjoint_equivalence_to_pb_ump_2_cell_pr2
      : id_left_adjoint_equivalence_to_pb_ump_2_cell ▹ qpr2
        =
        β.
    Proof.
      unfold id_left_adjoint_equivalence_to_pb_ump_2_cell.
      use (vcomp_lcancel (φ ◃ lpr2 ^-1)).
      {
        is_iso.
      }
      use (vcomp_rcancel (ψ ◃ lpr2)).
      {
        is_iso.
        apply property_from_invertible_2cell.
      }
      rewrite <- vcomp_whisker.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply (pb_ump_cell_pr2 H₂).
      }
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      rewrite id2_right.
      apply idpath.
    Qed.

    Definition id_left_adjoint_equivalence_to_pb_ump_2_unique
      : isaprop (∑ (γ : φ ==> ψ), γ ▹ qpr1 = α × γ ▹ qpr2 = β).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      use (pb_ump_eq H₂) ; cbn.
      - exact ((_ ◃ lpr1^-1) • α • (_ ◃ lpr1)).
      - exact ((_ ◃ lpr2^-1) • β • (_ ◃ lpr2)).
      - exact id_left_adjoint_equivalence_to_pb_ump_2_cell_eq.
      - rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        rewrite <- vcomp_whisker.
        apply maponpaths_2.
        exact (pr12 ζ₁).
      - rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        rewrite <- vcomp_whisker.
        apply maponpaths_2.
        exact (pr22 ζ₁).
      - rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        rewrite <- vcomp_whisker.
        apply maponpaths_2.
        exact (pr12 ζ₂).
      - rewrite !vassocl.
        use vcomp_move_L_pM ; [ is_iso | ].
        cbn.
        rewrite <- vcomp_whisker.
        apply maponpaths_2.
        exact (pr22 ζ₂).
    Qed.
  End UMP2.

  Definition id_left_adjoint_equivalence_to_pb_ump_2
    : pb_ump_2 (make_pb_cone q qpr1 qpr2 qγ).
  Proof.
    intros qc φ ψ α β p.
    use iscontraprop1.
    - exact (id_left_adjoint_equivalence_to_pb_ump_2_unique _ _ p).
    - simple refine (_ ,, _ ,, _).
      + exact (id_left_adjoint_equivalence_to_pb_ump_2_cell _ _ p).
      + exact (id_left_adjoint_equivalence_to_pb_ump_2_cell_pr1 _ _ p).
      + exact (id_left_adjoint_equivalence_to_pb_ump_2_cell_pr2 _ _ p).
  Defined.

  Definition id_left_adjoint_equivalence_to_pb
    : has_pb_ump (make_pb_cone q qpr1 qpr2 qγ).
  Proof.
    split.
    - exact id_left_adjoint_equivalence_to_pb_ump_1.
    - exact id_left_adjoint_equivalence_to_pb_ump_2.
  Defined.
End IdEquivalenceToPB.

Definition left_adjoint_equivalence_eq_to_pb
           {B : bicat}
           {b₁ b₂ b₃ : B}
           {f : b₁ --> b₃}
           {g : b₂ --> b₃}
           (cone₁ cone₂ : pb_cone f g)
           (H₂ : has_pb_ump cone₂)
           (p : pr1 cone₁ = pr1 cone₂)
           (qp1 : invertible_2cell
                    (idtoiso_2_0 _ _ (!p) · pb_cone_pr1 cone₁)
                    (pb_cone_pr1 cone₂))
           (qp2 : invertible_2cell
                    (idtoiso_2_0 _ _ (!p) · pb_cone_pr2 cone₁)
                    (pb_cone_pr2 cone₂))
           (path : (qp1^-1 ▹ f)
                   • rassociator _ _ _
                   • (_ ◃ pb_cone_cell cone₁)
                   • lassociator _ _ _
                   • (qp2 ▹ g)
                   =
                   pr1 (pb_cone_cell cone₂))
  : has_pb_ump cone₁.
Proof.
  induction cone₁ as [ q cone ].
  induction cone as [ qp₁ cone ].
  induction cone as [ qp₂ γ ].
  induction cone₂ as [ q' cone ].
  induction cone as [ qp₁' cone ].
  induction cone as [ qp₂' γ' ].
  cbn in *.
  induction p ; cbn in *.
  use (id_left_adjoint_equivalence_to_pb _ _ H₂).
  - exact (comp_of_invertible_2cell (linvunitor_invertible_2cell _) qp1).
  - exact (comp_of_invertible_2cell (linvunitor_invertible_2cell _) qp2).
  - abstract
      (cbn ;
       use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ; cbn ;
       refine (_ @ path) ;
       rewrite <- !rwhisker_vcomp ;
       rewrite !vassocl ;
       apply maponpaths ;
       rewrite !vassocr ;
       apply maponpaths_2 ;
       use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
       rewrite !vassocl ;
       rewrite lunitor_triangle ;
       rewrite vcomp_lunitor ;
       rewrite !vassocr ;
       apply maponpaths_2 ;
       rewrite <- lunitor_triangle ;
       rewrite !vassocr ;
       rewrite rassociator_lassociator ;
       rewrite id2_left ;
       apply idpath).
Defined.

Section EquivalenceToPBHelp.
  Context {B : bicat}
          (HB_2_0 : is_univalent_2_0 B)
          {b₁ b₂ b₃ : B}
          {f : b₁ --> b₃}
          {g : b₂ --> b₃}
          (cone₁ cone₂ : pb_cone f g)
          (H₂ : has_pb_ump cone₂)
          (l : cone₁ --> cone₂)
          (Hl : left_adjoint_equivalence l)
          (r := left_adjoint_right_adjoint Hl)
          (rpr1 : invertible_2cell
                    (r · pb_cone_pr1 cone₁)
                    (pb_cone_pr1 cone₂))
          (rpr2 : invertible_2cell
                    (r · pb_cone_pr2 cone₁)
                    (pb_cone_pr2 cone₂))
          (path : (r ◃ pb_cone_cell cone₁) • lassociator _ _ _ • (rpr2 ▹ g)
                  =
                  lassociator _ _ _ • (rpr1 ▹ f) • pr1 (pb_cone_cell cone₂)).

  Local Definition help_inv2cell
    : invertible_2cell
        (idtoiso_2_0 _ _ (! isotoid_2_0 HB_2_0 (l,, Hl)))
        r.
  Proof.
    apply idtoiso_2_1.
    cbn.
    rewrite idtoiso_2_0_inv.
    rewrite idtoiso_2_0_isotoid_2_0.
    apply idpath.
  Qed.

  Definition left_adjoint_equivalence_to_pb_help_pr1
    : invertible_2cell
        (idtoiso_2_0 _ _ (! isotoid_2_0 HB_2_0 (l,, Hl))
         ·
         pb_cone_pr1 cone₁)
        (pb_cone_pr1 cone₂)
    := comp_of_invertible_2cell
         (rwhisker_of_invertible_2cell
            _
            help_inv2cell)
         rpr1.

  Definition left_adjoint_equivalence_to_pb_help_pr2
    : invertible_2cell
        (idtoiso_2_0 _ _ (! isotoid_2_0 HB_2_0 (l,, Hl))
         ·
         pb_cone_pr2 cone₁)
        (pb_cone_pr2 cone₂)
    := comp_of_invertible_2cell
         (rwhisker_of_invertible_2cell
            _
            help_inv2cell)
         rpr2.

  Definition left_adjoint_equivalence_to_pb_help_path
    : (left_adjoint_equivalence_to_pb_help_pr1^-1 ▹ f)
      • rassociator _ _ _
      • (_ ◃ pb_cone_cell cone₁)
      • lassociator _ _ _
      • (left_adjoint_equivalence_to_pb_help_pr2 ▹ g)
      =
      pr1 (pb_cone_cell cone₂).
  Proof.
    cbn.
    rewrite !vassocl.
    use vcomp_move_R_pM ; [ is_iso | ].
    cbn.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite <- rwhisker_rwhisker_alt.
    rewrite !vassocl.
    apply maponpaths.
    use vcomp_move_R_pM ; [ is_iso | ].
    rewrite !vassocr.
    exact path.
  Qed.

  Definition left_adjoint_equivalence_to_pb_help
    : has_pb_ump cone₁.
  Proof.
    use (left_adjoint_equivalence_eq_to_pb _ _ H₂).
    - exact (isotoid_2_0 HB_2_0 (l ,, Hl)).
    - exact left_adjoint_equivalence_to_pb_help_pr1.
    - exact left_adjoint_equivalence_to_pb_help_pr2.
    - exact left_adjoint_equivalence_to_pb_help_path.
  Defined.
End EquivalenceToPBHelp.

Section LeftAdjointEquivalenceToPB.
  Context {B : bicat}
          (HB_2_0 : is_univalent_2_0 B)
          {b₁ b₂ b₃ : B}
          {f : b₁ --> b₃}
          {g : b₂ --> b₃}
          (cone₁ cone₂ : pb_cone f g)
          (H₂ : has_pb_ump cone₂)
          (l : cone₁ --> cone₂)
          (Hl : left_adjoint_equivalence l)
          (lpr1 : invertible_2cell
                    (l · pb_cone_pr1 cone₂)
                    (pb_cone_pr1 cone₁))
          (lpr2 : invertible_2cell
                    (l · pb_cone_pr2 cone₂)
                    (pb_cone_pr2 cone₁))
          (path : (_ ◃ pb_cone_cell cone₂) • lassociator _ _ _ • (lpr2 ▹ g)
                  =
                  lassociator _ _ _ • (lpr1 ▹ f) • pb_cone_cell cone₁).

  Let r : cone₂ --> cone₁
    := left_adjoint_right_adjoint Hl.
  Let η : invertible_2cell (id₁ _) (l · r)
    := left_equivalence_unit_iso Hl.
  Let ε : invertible_2cell (r · l) (id₁ _)
    := left_equivalence_counit_iso Hl.

  Definition left_adjoint_equivalence_to_pb_pr1
    : invertible_2cell
        (r · pb_cone_pr1 cone₁)
        (pb_cone_pr1 cone₂)
    := comp_of_invertible_2cell
         (lwhisker_of_invertible_2cell
            _
            (inv_of_invertible_2cell lpr1))
         (comp_of_invertible_2cell
            (lassociator_invertible_2cell _ _ _)
            (comp_of_invertible_2cell
               (rwhisker_of_invertible_2cell _ ε)
               (lunitor_invertible_2cell _))).

  Definition left_adjoint_equivalence_to_pb_pr2
    : invertible_2cell
        (r · pb_cone_pr2 cone₁)
        (pb_cone_pr2 cone₂)
    := comp_of_invertible_2cell
         (lwhisker_of_invertible_2cell
            _
            (inv_of_invertible_2cell lpr2))
         (comp_of_invertible_2cell
            (lassociator_invertible_2cell _ _ _)
            (comp_of_invertible_2cell
               (rwhisker_of_invertible_2cell _ ε)
               (lunitor_invertible_2cell _))).

  Definition left_adjoint_equivalence_to_pb_eq
    : (r ◃ pb_cone_cell cone₁)
      • lassociator _ _ _
      • (left_adjoint_equivalence_to_pb_pr2 ▹ g)
      =
      lassociator _ _ _
      • (left_adjoint_equivalence_to_pb_pr1 ▹ f)
      • pr1 (pb_cone_cell cone₂).
  Proof.
    cbn.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
    use (vcomp_lcancel (r ◃ lassociator _ _ _)) ; [ is_iso | ].
    rewrite !vassocr.
    rewrite lassociator_lassociator.
    rewrite !lwhisker_vcomp.
    rewrite <- path.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite rwhisker_vcomp.
        rewrite vcomp_rinv.
        rewrite id2_rwhisker.
        rewrite lwhisker_id2.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lassociator_lassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lwhisker_lwhisker.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    rewrite <- vcomp_whisker.
    rewrite rwhisker_rwhisker.
    rewrite !vassocl.
    apply maponpaths.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    rewrite !vassocr.
    rewrite lunitor_triangle.
    apply idpath.
  Qed.

  Definition left_adjoint_equivalence_to_pb
    : has_pb_ump cone₁.
  Proof.
    use (left_adjoint_equivalence_to_pb_help HB_2_0 _ _ H₂ l Hl).
    - exact left_adjoint_equivalence_to_pb_pr1.
    - exact left_adjoint_equivalence_to_pb_pr2.
    - exact left_adjoint_equivalence_to_pb_eq.
  Defined.
End LeftAdjointEquivalenceToPB.
