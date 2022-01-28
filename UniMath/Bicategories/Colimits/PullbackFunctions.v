Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Colimits.Pullback.

Local Open Scope cat.

Section Functions.
  Context {B : bicat_with_pb}.

  Definition pb_obj
             {b₁ b₂ b₃ : B}
             (f : b₁ --> b₃)
             (g : b₂ --> b₃)
    : B
    := pr1 (pr2 B _ _ _ f g).

  Local Notation "f '/≃' g" := (pb_obj f g) (at level 40).

  Definition pb_pr1
             {b₁ b₂ b₃ : B}
             (f : b₁ --> b₃)
             (g : b₂ --> b₃)
    : f /≃ g --> b₁
    := pb_cone_pr1 (pr1 (pr2 B _ _ _ f g)).

  Local Notation "'π₁'" := (pb_pr1 _ _).

  Definition pb_pr2
             {b₁ b₂ b₃ : B}
             (f : b₁ --> b₃)
             (g : b₂ --> b₃)
    : f /≃ g --> b₂
    := pb_cone_pr2 (pr1 (pr2 B _ _ _ f g)).

  Local Notation "'π₂'" := (pb_pr2 _ _).

  Definition pb_cell
             {b₁ b₂ b₃ : B}
             (f : b₁ --> b₃)
             (g : b₂ --> b₃)
    : invertible_2cell (π₁ · f) (π₂ · g)
    := pb_cone_cell (pr1 (pr2 B _ _ _ f g)).

  Definition pb_obj_has_pb_ump
             {b₁ b₂ b₃ : B}
             (f : b₁ --> b₃)
             (g : b₂ --> b₃)
    : has_pb_ump (make_pb_cone (f /≃ g) π₁ π₂ (pb_cell f g))
    := pr2 (pr2 B _ _ _ f g).

  Definition mor_to_pb_obj
             {a b₁ b₂ b₃ : B}
             {f : b₁ --> b₃}
             {g : b₂ --> b₃}
             (h₁ : a --> b₁)
             (h₂ : a --> b₂)
             (γ : invertible_2cell (h₁ · f) (h₂ · g))
    : a --> f /≃ g.
  Proof.
    pose (q := make_pb_cone a h₁ h₂ γ : pb_cone f g).
    exact (pb_ump_mor (pr2 (pr2 B _ _ _ f g)) q).
  Defined.

  Local Notation "h₁ ⊗[ γ ] h₂" := (mor_to_pb_obj h₁ h₂ γ) (at level 10).

  Definition mor_to_pb_obj_pr1
             {a b₁ b₂ b₃ : B}
             {f : b₁ --> b₃}
             {g : b₂ --> b₃}
             (h₁ : a --> b₁)
             (h₂ : a --> b₂)
             (γ : invertible_2cell (h₁ · f) (h₂ · g))
    : invertible_2cell (h₁ ⊗[ γ ] h₂ · π₁) h₁.
  Proof.
    pose (q := make_pb_cone a h₁ h₂ γ : pb_cone f g).
    exact (pb_ump_mor_pr1 (pr2 (pr2 B _ _ _ f g)) q).
  Defined.

  Definition mor_to_pb_obj_pr2
             {a b₁ b₂ b₃ : B}
             {f : b₁ --> b₃}
             {g : b₂ --> b₃}
             (h₁ : a --> b₁)
             (h₂ : a --> b₂)
             (γ : invertible_2cell (h₁ · f) (h₂ · g))
    : invertible_2cell (h₁ ⊗[ γ ] h₂ · π₂) h₂.
  Proof.
    pose (q := make_pb_cone a h₁ h₂ γ : pb_cone f g).
    exact (pb_ump_mor_pr2 (pr2 (pr2 B _ _ _ f g)) q).
  Defined.

  Definition mor_to_pb_obj_cell
             {a b₁ b₂ b₃ : B}
             {f : b₁ --> b₃}
             {g : b₂ --> b₃}
             (h₁ : a --> b₁)
             (h₂ : a --> b₂)
             (γ : invertible_2cell (h₁ · f) (h₂ · g))
    : (h₁ ⊗[ γ ] h₂) ◃ pb_cell f g
      =
      lassociator _ _ _
                  • (mor_to_pb_obj_pr1 h₁ h₂ γ ▹ f)
                  • γ
                  • ((mor_to_pb_obj_pr2 h₁ h₂ γ)^-1 ▹ g)
                  • rassociator _ _ _.
  Proof.
    pose (q := make_pb_cone a h₁ h₂ γ : pb_cone f g).
    exact (pb_ump_mor_cell (pr2 (pr2 B _ _ _ f g)) q).
  Defined.

  Definition cell_to_pb_obj_homot
             {a b₁ b₂ b₃ : B}
             {f : b₁ --> b₃}
             {g : b₂ --> b₃}
             {h₁ h₂ : a --> f /≃ g}
             (α : h₁ · π₁ ==> h₂ · π₁)
             (β : h₁ · π₂ ==> h₂ · π₂)
    : UU
    := (h₁ ◃ pb_cell f g)
         • lassociator _ _ _
         • (β ▹ g)
         • rassociator _ _ _
       =
       lassociator _ _ _
                   • (α ▹ f)
                   • rassociator _ _ _
                   • (h₂ ◃ pb_cell f g).

  Definition cell_to_pb_obj
             {a b₁ b₂ b₃ : B}
             {f : b₁ --> b₃}
             {g : b₂ --> b₃}
             {h₁ h₂ : a --> f /≃ g}
             (α : h₁ · π₁ ==> h₂ · π₁)
             (β : h₁ · π₂ ==> h₂ · π₂)
             (p : cell_to_pb_obj_homot α β)
    : h₁ ==> h₂
    := pb_ump_cell
         (pr2 (pr2 B _ _ _ f g))
         h₁ h₂
         α β
         p.

  Definition cell_to_pb_obj_pr1
             {a b₁ b₂ b₃ : B}
             {f : b₁ --> b₃}
             {g : b₂ --> b₃}
             {h₁ h₂ : a --> f /≃ g}
             (α : h₁ · π₁ ==> h₂ · π₁)
             (β : h₁ · π₂ ==> h₂ · π₂)
             (p : cell_to_pb_obj_homot α β)
    : cell_to_pb_obj α β p ▹ π₁ = α.
  Proof.
    exact (pb_ump_cell_pr1
             (pr2 (pr2 B _ _ _ f g))
             h₁ h₂
             α β
             p).
  Qed.

  Definition cell_to_pb_obj_pr2
             {a b₁ b₂ b₃ : B}
             {f : b₁ --> b₃}
             {g : b₂ --> b₃}
             {h₁ h₂ : a --> f /≃ g}
             (α : h₁ · π₁ ==> h₂ · π₁)
             (β : h₁ · π₂ ==> h₂ · π₂)
             (p : cell_to_pb_obj_homot α β)
    : cell_to_pb_obj α β p ▹ π₂ = β.
  Proof.
    exact (pb_ump_cell_pr2
             (pr2 (pr2 B _ _ _ f g))
             h₁ h₂
             α β
             p).
  Qed.

  Definition eq_to_pb_obj
             {a b₁ b₂ b₃ : B}
             {f : b₁ --> b₃}
             {g : b₂ --> b₃}
             {h₁ h₂ : a --> f /≃ g}
             {φ ψ : h₁ ==> h₂}
             {p : cell_to_pb_obj_homot (φ ▹ π₁) (φ ▹ π₂)}
             (φψpr1 : φ ▹ π₁ = ψ ▹ π₁)
             (φψpr2 : φ ▹ π₂ = ψ ▹ π₂)
    : φ = ψ
    := pb_ump_eq
         (pr2 (pr2 B _ _ _ f g))
         h₁ h₂
         (φ ▹ π₁) (φ ▹ π₂)
         p
         φ ψ
         (idpath _) (idpath _)
         (!φψpr1) (!φψpr2).

  Definition help_pb_on_1cell
             {b₁ b₂ c₂ b₃ : B}
             (f : b₁ --> b₃)
             {g₁ : b₂ --> b₃}
             {g₂ : c₂ --> b₃}
             {h : b₂ --> c₂}
             (β : invertible_2cell g₁ (h · g₂))
    : invertible_2cell (π₁ · f) (π₂ · h · g₂)
    := comp_of_invertible_2cell
         (pb_cell f g₁)
         (comp_of_invertible_2cell
            (lwhisker_of_invertible_2cell
               _
               β)
            (lassociator_invertible_2cell _ _ _)).

  Definition pb_on_1cell
             {b₁ b₂ c₂ b₃ : B}
             (f : b₁ --> b₃)
             {g₁ : b₂ --> b₃}
             {g₂ : c₂ --> b₃}
             {h : b₂ --> c₂}
             (β : invertible_2cell g₁ (h · g₂))
    : f /≃ g₁ --> f /≃ g₂.
  Proof.
    simple refine (_ ⊗[ _ ] _).
    - exact π₁.
    - exact (π₂ · h).
    - exact (help_pb_on_1cell f β).
  Defined.

  Local Notation "f /≃₁ β" := (pb_on_1cell f β) (at level 40).

  Definition pb_on_1cell_pr1
             {b₁ b₂ c₂ b₃ : B}
             (f : b₁ --> b₃)
             {g₁ : b₂ --> b₃}
             {g₂ : c₂ --> b₃}
             {h : b₂ --> c₂}
             (β : invertible_2cell g₁ (h · g₂))
    : invertible_2cell (f /≃₁ β · π₁) π₁.
  Proof.
    apply mor_to_pb_obj_pr1.
  Defined.

  Definition pb_on_1cell_pr2
             {b₁ b₂ c₂ b₃ : B}
             (f : b₁ --> b₃)
             {g₁ : b₂ --> b₃}
             {g₂ : c₂ --> b₃}
             {h : b₂ --> c₂}
             (β : invertible_2cell g₁ (h · g₂))
    : invertible_2cell (f /≃₁ β · π₂) (π₂ · h).
  Proof.
    apply mor_to_pb_obj_pr2.
  Defined.

  Definition pb_on_1cell_cell
             {b₁ b₂ c₂ b₃ : B}
             (f : b₁ --> b₃)
             {g₁ : b₂ --> b₃}
             {g₂ : c₂ --> b₃}
             {h : b₂ --> c₂}
             (β : invertible_2cell g₁ (h · g₂))
    : f /≃₁ β ◃ pb_cell f g₂
      =
      lassociator _ _ _
      • (pb_on_1cell_pr1 f β ▹ f)
      • pb_cell f g₁
      • (π₂ ◃ β)
      • lassociator _ _ _
      • ((pb_on_1cell_pr2 f β)^-1 ▹ g₂)
      • rassociator _ _ _.
  Proof.
    pose (mor_to_pb_obj_cell
            π₁ (π₂ · h)
            (comp_of_invertible_2cell
               (pb_cell f g₁)
               (comp_of_invertible_2cell
                  (lwhisker_of_invertible_2cell
                     _
                     β)
                  (lassociator_invertible_2cell _ _ _)))).
    cbn in p.
    refine (p @ _).
    rewrite !vassocl.
    apply idpath.
  Qed.

  Section PBOn2Cell.
    Context {b₁ b₂ c₂ b₃ : B}
            (f : b₁ --> b₃)
            {g₁ : b₂ --> b₃}
            {g₂ : c₂ --> b₃}
            {h₁ h₂ : b₂ --> c₂}
            {β₁ : invertible_2cell g₁ (h₁ · g₂)}
            {β₂ : invertible_2cell g₁ (h₂ · g₂)}
            {α : h₁ ==> h₂}
            (p : β₁ • (α ▹ g₂) = β₂).

    Let k₁ : f /≃₁ β₁ · π₁ ==> f /≃₁ β₂ · π₁
      := pb_on_1cell_pr1 _ _ • (pb_on_1cell_pr1 _ _)^-1.

    Let k₂ : f /≃₁ β₁ · π₂ ==> f /≃₁ β₂ · π₂
      := pb_on_1cell_pr2 _ _ • (π₂ ◃ α) • (pb_on_1cell_pr2 _ _)^-1.

    Lemma pb_on_2cell_homot
      : cell_to_pb_obj_homot k₁ k₂.
    Proof.
      unfold cell_to_pb_obj_homot, k₁, k₂.
      rewrite pb_on_1cell_cell.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_lassociator.
          rewrite id2_left.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite pb_on_1cell_cell.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      apply maponpaths.
      exact (!p).
    Qed.

    Definition pb_on_2cell
      : f /≃₁ β₁ ==> f /≃₁ β₂.
    Proof.
      use cell_to_pb_obj.
      - exact k₁.
      - exact k₂.
      - exact pb_on_2cell_homot.
    Defined.

    Definition pb_on_2cell_pr1
      : pb_on_2cell ▹ π₁ = k₁.
    Proof.
      apply cell_to_pb_obj_pr1.
    Qed.

    Definition pb_on_2cell_pr2
      : pb_on_2cell ▹ π₂ = k₂.
    Proof.
      apply cell_to_pb_obj_pr2.
    Qed.
  End PBOn2Cell.

  Local Notation "f /≃₂ p" := (pb_on_2cell f p) (at level 40).

  Section PBOnId.
    Context {a b₁ b₂ : B}
            (f : b₁ --> b₂)
            (g : a --> b₂).

    Let k₁ : id₁ (f /≃ g) · π₁ ==> f /≃₁ linvunitor_invertible_2cell g · π₁
      := lunitor _ • (pb_on_1cell_pr1 _ _)^-1.

    Let k₂ : id₁ (f /≃ g) · π₂ ==> f /≃₁ linvunitor_invertible_2cell g · π₂
      := lunitor _ • rinvunitor _ • (pb_on_1cell_pr2 _ _)^-1.

    Lemma pb_1cell_on_id_homot
      : cell_to_pb_obj_homot k₁ k₂.
    Proof.
      unfold cell_to_pb_obj_homot, k₁, k₂.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      pose (pb_on_1cell_cell f (linvunitor_invertible_2cell g)) as p.
      cbn in p.
      rewrite p.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite lunitor_triangle.
      rewrite <- vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lunitor_triangle.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv.
      rewrite <- rwhisker_hcomp.
      apply idpath.
    Qed.

    Definition pb_1cell_on_id
      : id₁ (f /≃ g) ==> f /≃₁ linvunitor_invertible_2cell g.
    Proof.
      use cell_to_pb_obj.
      - exact k₁.
      - exact k₂.
      - exact pb_1cell_on_id_homot.
    Defined.

    Definition pb_1cell_on_id_pr1
      : pb_1cell_on_id ▹ π₁ = k₁.
    Proof.
      apply cell_to_pb_obj_pr1.
    Qed.

    Definition pb_1cell_on_id_pr2
      : pb_1cell_on_id ▹ π₂ = k₂.
    Proof.
      apply cell_to_pb_obj_pr2.
    Qed.
  End PBOnId.

  Section PBOnComp.
    Context {a₁ a₂ a₃ b₁ b₂ : B}
            (f : b₁ --> b₂)
            {g₁ : a₁ --> b₂}
            {g₂ : a₂ --> b₂}
            {g₃ : a₃ --> b₂}
            {h₁ : a₁ --> a₂}
            {h₂ : a₂ --> a₃}
            (α : invertible_2cell g₁ (h₁ · g₂))
            (β : invertible_2cell g₂ (h₂ · g₃)).

    Let γ : invertible_2cell g₁ (h₁ · h₂ · g₃)
      := comp_of_invertible_2cell
           α
           (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell _ β)
              (lassociator_invertible_2cell _ _ _)).

    Let k₁ : f /≃₁ α · (f /≃₁ β) · π₁ ==> f /≃₁ γ · π₁
      := rassociator _ _ _
                     • (_ ◃ pb_on_1cell_pr1 _ _)
                     • pb_on_1cell_pr1 _ _
                     • (pb_on_1cell_pr1 _ _)^-1.
    Let k₂ : f /≃₁ α · (f /≃₁ β) · π₂ ==> f /≃₁ γ · π₂
      := rassociator _ _ _
                     • (_ ◃ pb_on_1cell_pr2 _ _)
                     • lassociator _ _ _
                     • (pb_on_1cell_pr2 _ _ ▹ _)
                     • rassociator _ _ _
                     • (pb_on_1cell_pr2 _ _)^-1.

    Lemma pb_1cell_on_comp_homot
      : cell_to_pb_obj_homot k₁ k₂.
    Proof.
      unfold cell_to_pb_obj_homot, k₁, k₂.
      rewrite <- !rwhisker_vcomp.
      rewrite (pb_on_1cell_cell f γ).
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite <- lassociator_lassociator.
      rewrite (pb_on_1cell_cell f β).
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 6 apply maponpaths.
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        do 4 apply maponpaths_2.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_right.
        apply idpath.
      }
      etrans.
      {
        do 5 apply maponpaths.
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
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_lwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_lassociator.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      cbn.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      do 2 (use vcomp_move_R_Mp ; [ is_iso | ] ; cbn).
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rassociator_rassociator.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- vcomp_whisker.
        rewrite !vassocl.
        rewrite <- lwhisker_lwhisker_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite (pb_on_1cell_cell f α).
      rewrite !vassocl.
      do 3 apply maponpaths.
      refine (_ @ id2_right _).
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      apply lassociator_rassociator.
    Qed.

    Definition pb_1cell_on_comp
      : f /≃₁ α · (f /≃₁ β) ==> f /≃₁ γ.
    Proof.
      use cell_to_pb_obj.
      - exact k₁.
      - exact k₂.
      - exact pb_1cell_on_comp_homot.
    Defined.

    Definition pb_1cell_on_comp_pr1
      : pb_1cell_on_comp ▹ π₁ = k₁.
    Proof.
      apply cell_to_pb_obj_pr1.
    Qed.

    Definition pb_1cell_on_comp_pr2
      : pb_1cell_on_comp ▹ π₂ = k₂.
    Proof.
      apply cell_to_pb_obj_pr2.
    Qed.
  End PBOnComp.

  Definition pb_2cell_on_id
             {a₁ a₂ b₁ b₂ : B}
             {f : b₁ --> b₂}
             {g₁ : a₁ --> b₂}
             {g₂ : a₂ --> b₂}
             {h : a₁ --> a₂}
             (α : invertible_2cell g₁ (h · g₂))
             (p : α • (id₂ h ▹ g₂) = α)
    : f /≃₂ p = id₂ _.
  Proof.
    use eq_to_pb_obj.
    - unfold cell_to_pb_obj_homot.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite vcomp_whisker.
      apply maponpaths.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    - rewrite pb_on_2cell_pr1, id2_rwhisker.
      apply vcomp_rinv.
    - rewrite pb_on_2cell_pr2, id2_rwhisker, lwhisker_id2.
      rewrite id2_right.
      apply vcomp_rinv.
  Qed.

  Definition pb_on_2cell_coh
             {a₁ a₂ b₁ b₂ : B}
             {f : b₁ --> b₂}
             {g₁ : a₁ --> b₂}
             {g₂ : a₂ --> b₂}
             {h₁ h₂ : a₁ --> a₂}
             (α : invertible_2cell g₁ (h₁ · g₂))
             (β : invertible_2cell g₁ (h₂ · g₂))
             (γ : h₁ ==> h₂)
             (p : α • (γ ▹ _) = β)
    : (pb_on_1cell_pr1 f α)^-1 • (f /≃₂ p ▹ π₁)
      =
      (pb_on_1cell_pr1 f β)^-1.
  Proof.
    cbn.
    rewrite pb_on_2cell_pr1.
    rewrite !vassocr.
    rewrite vcomp_linv.
    rewrite id2_left.
    apply idpath.
  Qed.

  Definition pb_1cell_on_id_coh
             {a b₁ b₂ : B}
             (f : b₁ --> b₂)
             (g : a --> b₂)
    : linvunitor π₁ • (pb_1cell_on_id f g ▹ π₁)
      =
      (pb_on_1cell_pr1 f (linvunitor_invertible_2cell g))^-1.
  Proof.
    cbn.
    rewrite pb_1cell_on_id_pr1.
    rewrite !vassocr.
    rewrite linvunitor_lunitor.
    rewrite id2_left.
    apply idpath.
  Qed.

  Definition pb_1cell_on_comp_coh
             {a₁ a₂ a₃ b₁ b₂ : B}
             (f : b₁ --> b₂)
             {g₁ : a₁ --> b₂}
             {g₂ : a₂ --> b₂}
             {g₃ : a₃ --> b₂}
             {h₁ : a₁ --> a₂}
             {h₂ : a₂ --> a₃}
             (α : invertible_2cell g₁ (h₁ · g₂))
             (β : invertible_2cell g₂ (h₂ · g₃))
    : (pb_on_1cell_pr1 f α)^-1
                           • ((f /≃₁ α ◃ (pb_on_1cell_pr1 f β)^-1)
                                • lassociator (f /≃₁ α) (f /≃₁ β) π₁)
                           • (pb_1cell_on_comp f α β ▹ π₁)
      =
      (pb_on_1cell_pr1
         f
         (comp_of_invertible_2cell
            α
            (comp_of_invertible_2cell
               (lwhisker_of_invertible_2cell h₁ β)
               (lassociator_invertible_2cell _ _ _)))) ^-1.
  Proof.
    rewrite pb_1cell_on_comp_pr1.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      rewrite id2_left.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite vcomp_linv.
    apply id2_left.
  Qed.

  Definition pb_2cell_on_comp
             {a₁ a₂ b₁ b₂ : B}
             (f : b₁ --> b₂)
             {g₁ : a₁ --> b₂}
             {g₂ : a₂ --> b₂}
             {h₁ h₂ h₃ : a₁ --> a₂}
             {α : invertible_2cell g₁ (h₁ · g₂)}
             {β : invertible_2cell g₁ (h₂ · g₂)}
             {γ : invertible_2cell g₁ (h₃ · g₂)}
             (δ₁ : h₁ ==> h₂)
             (p : α • (δ₁ ▹ g₂) = β)
             (δ₂ : h₂ ==> h₃)
             (q : β • (δ₂ ▹ g₂) = γ)
             (r : α • ((δ₁ • δ₂) ▹ g₂) = γ)
    : f /≃₂ r = f /≃₂ p • f /≃₂ q.
  Proof.
    use eq_to_pb_obj.
    - unfold cell_to_pb_obj_homot.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite lassociator_rassociator.
      rewrite id2_right.
      rewrite <- vcomp_whisker.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    - rewrite <- rwhisker_vcomp.
      rewrite !pb_on_2cell_pr1.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
    - rewrite <- rwhisker_vcomp.
      rewrite !pb_on_2cell_pr2.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
  Qed.

  Definition pb_2cell_on_lunitor
             {a₁ a₂ b₁ b₂ : B}
             (f : b₁ --> b₂)
             {g₁ : a₁ --> b₂}
             {g₂ : a₂ --> b₂}
             {h : a₁ --> a₂}
             (α : invertible_2cell g₁ (h · g₂))
             (p : comp_of_invertible_2cell
                    (linvunitor_invertible_2cell g₁)
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell (id₁ a₁) α)
                       (lassociator_invertible_2cell (id₁ a₁) h g₂))
                    • (lunitor h ▹ g₂)
                  = α)
    : lunitor (f /≃₁ α)
      =
      (pb_1cell_on_id f g₁ ▹ f /≃₁ α)
        • pb_1cell_on_comp f (linvunitor_invertible_2cell g₁) α
        • f /≃₂ p.
  Proof.
    use eq_to_pb_obj.
    - unfold cell_to_pb_obj_homot.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite vcomp_whisker.
      apply maponpaths.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite pb_on_2cell_pr1, pb_1cell_on_comp_pr1.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite pb_1cell_on_id_pr1.
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      rewrite vcomp_lunitor.
      rewrite !vassocr.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite pb_on_2cell_pr2, pb_1cell_on_comp_pr2.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      do 2 (use vcomp_move_L_Mp ; [ is_iso | ] ; cbn).
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite pb_1cell_on_id_pr2.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite lunitor_lwhisker.
      rewrite rwhisker_vcomp.
      rewrite rinvunitor_runitor.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      apply id2_left.
  Qed.

  Definition pb_2cell_on_runitor
             {a₁ a₂ b₁ b₂ : B}
             (f : b₁ --> b₂)
             {g₁ : a₁ --> b₂}
             {g₂ : a₂ --> b₂}
             {h : a₁ --> a₂}
             (α : invertible_2cell g₁ (h · g₂))
             (p : comp_of_invertible_2cell
                    α
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell
                          h
                          (linvunitor_invertible_2cell g₂))
                       (lassociator_invertible_2cell h (id₁ a₂) g₂))
                    • (runitor h ▹ g₂)
                  = α)
    : runitor (f /≃₁ α)
      =
      (f /≃₁ α ◃ pb_1cell_on_id f g₂)
        • pb_1cell_on_comp f α (linvunitor_invertible_2cell g₂)
        • f /≃₂ p.
  Proof.
    use eq_to_pb_obj.
    - unfold cell_to_pb_obj_homot.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite vcomp_whisker.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      rewrite pb_on_2cell_pr1, pb_1cell_on_comp_pr1.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
      }
      rewrite vcomp_rinv.
      rewrite id2_right.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      rewrite pb_1cell_on_id_pr1.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      rewrite lunitor_lwhisker.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      rewrite pb_on_2cell_pr2, pb_1cell_on_comp_pr2.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 6 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_linv.
        rewrite id2_left.
        apply idpath.
      }
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !vassocr.
        rewrite runitor_triangle.
        rewrite <- vcomp_runitor.
        apply idpath.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_rinv.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite pb_1cell_on_id_pr2.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      }
      rewrite <- runitor_triangle.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite rinvunitor_runitor.
      rewrite id2_right.
      rewrite lunitor_lwhisker.
      apply idpath.
  Qed.

  Definition pb_2cell_on_lassociator
             {a₁ a₂ a₃ a₄ b₁ b₂ : B}
             (f : b₁ --> b₂)
             {g₁ : a₁ --> b₂}
             {g₂ : a₂ --> b₂}
             {g₃ : a₃ --> b₂}
             {g₄ : a₄ --> b₂}
             {h₁ : a₁ --> a₂}
             {h₂ : a₂ --> a₃}
             {h₃ : a₃ --> a₄}
             (α : invertible_2cell g₁ (h₁ · g₂))
             (β : invertible_2cell g₂ (h₂ · g₃))
             (γ : invertible_2cell g₃ (h₃ · g₄))
             (p : comp_of_invertible_2cell
                    α
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell
                          h₁
                          (comp_of_invertible_2cell
                             β
                             (comp_of_invertible_2cell
                                (lwhisker_of_invertible_2cell h₂ γ)
                                (lassociator_invertible_2cell h₂ h₃ g₄))))
                       (lassociator_invertible_2cell h₁ (h₂ · h₃) g₄))
                    • (lassociator h₁ h₂ h₃ ▹ g₄)
                  =
                  comp_of_invertible_2cell
                    (comp_of_invertible_2cell
                       α
                       (comp_of_invertible_2cell
                          (lwhisker_of_invertible_2cell h₁ β)
                          (lassociator_invertible_2cell h₁ h₂ g₃)))
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell (h₁ · h₂) γ)
                       (lassociator_invertible_2cell (h₁ · h₂) h₃ g₄)))
    : (f /≃₁ α ◃ pb_1cell_on_comp f β γ)
        • pb_1cell_on_comp f α _
        • f /≃₂ p
      =
      lassociator _ _ _
                  • (pb_1cell_on_comp f α β ▹ _)
                  • pb_1cell_on_comp f _ γ.
  Proof.
    cbn in p.
    use eq_to_pb_obj.
    - unfold cell_to_pb_obj_homot.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        apply id2_right.
      }
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      etrans.
      {
        rewrite !pb_1cell_on_comp_pr1, !pb_on_2cell_pr1.
        rewrite !vassocl.
        etrans.
        {
          do 4 apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_linv.
          apply id2_left.
        }
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite pb_1cell_on_comp_pr1.
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite lwhisker_vcomp.
          rewrite !vassocl.
          rewrite vcomp_linv.
          rewrite id2_right.
          apply idpath.
        }
        apply idpath.
      }
      rewrite pb_1cell_on_comp_pr1.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        apply idpath.
      }
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite pb_1cell_on_comp_pr1.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite rassociator_rassociator.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      rewrite pb_on_2cell_pr2, !pb_1cell_on_comp_pr2.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      etrans.
      {
        do 6 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite <- rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        rewrite pb_1cell_on_comp_pr2.
        apply maponpaths.
        rewrite !vassocr.
        rewrite lwhisker_vcomp.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_whisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        rewrite <- rwhisker_rwhisker.
        rewrite !vassocl.
        apply maponpaths.
        rewrite pb_1cell_on_comp_pr2.
        rewrite !vassocr.
        rewrite !rwhisker_vcomp.
        rewrite !vassocl.
        rewrite vcomp_linv.
        rewrite id2_right.
        apply idpath.
      }
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      do 2 (use vcomp_move_L_pM ; [ is_iso | ] ; cbn).
      rewrite !vassocr.
      rewrite lassociator_lassociator.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lwhisker_lwhisker.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite <- lassociator_lassociator.
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        rewrite !vassocl.
        apply idpath.
      }
      apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite lassociator_lassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite <- rassociator_rassociator.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2.
      rewrite id2_right.
      apply idpath.
  Qed.

  Definition pb_2cell_on_lwhisker
             {a₁ a₂ a₃ b₁ b₂ : B}
             (f : b₁ --> b₂)
             {g₁ : a₁ --> b₂}
             {g₂ : a₂ --> b₂}
             {g₃ : a₃ --> b₂}
             {h₁ : a₁ --> a₂}
             {h₂ h₃ : a₂ --> a₃}
             (α : invertible_2cell g₁ (h₁ · g₂))
             {β₁ : invertible_2cell g₂ (h₂ · g₃)}
             {β₂ : invertible_2cell g₂ (h₃ · g₃)}
             {γ : h₂ ==> h₃}
             (p : β₁ • (γ ▹ g₃) = β₂)
             (q : comp_of_invertible_2cell
                    α
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell h₁ β₁)
                       (lassociator_invertible_2cell h₁ h₂ g₃))
                    •
                    ((h₁ ◃ γ) ▹ g₃)
                  =
                  comp_of_invertible_2cell
                    α
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell h₁ β₂)
                       (lassociator_invertible_2cell h₁ h₃ g₃)))
    : pb_1cell_on_comp f α β₁ • f /≃₂ q
      =
      (f /≃₁ α ◃ f /≃₂ p) • pb_1cell_on_comp f α β₂.
  Proof.
    use eq_to_pb_obj.
    - unfold cell_to_pb_obj_homot.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        apply id2_right.
      }
      rewrite !vassocr.
      rewrite rwhisker_rwhisker.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite vcomp_whisker.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      rewrite pb_on_2cell_pr1, !pb_1cell_on_comp_pr1.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite pb_on_2cell_pr1.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      rewrite id2_left.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      apply id2_left.
    - rewrite <- !rwhisker_vcomp.
      rewrite pb_on_2cell_pr2, !pb_1cell_on_comp_pr2.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite pb_on_2cell_pr2.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite !lwhisker_vcomp.
        rewrite vcomp_linv.
        rewrite lwhisker_id2.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lwhisker_lwhisker_rassociator.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      rewrite id2_left.
      apply idpath.
  Qed.

  Definition pb_2cell_on_rwhisker
             {a₁ a₂ a₃ b₁ b₂ : B}
             (f : b₁ --> b₂)
             {g₁ : a₁ --> b₂}
             {g₂ : a₂ --> b₂}
             {g₃ : a₃ --> b₂}
             {h₁ h₂ : a₁ --> a₂}
             {h₃ : a₂ --> a₃}
             {α₁ : invertible_2cell g₁ (h₁ · g₂)}
             {α₂ : invertible_2cell g₁ (h₂ · g₂)}
             (β : invertible_2cell g₂ (h₃ · g₃))
             {γ : h₁ ==> h₂}
             (p : α₁ • (γ ▹ g₂) = α₂)
             (q : comp_of_invertible_2cell
                    α₁
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell h₁ β)
                       (lassociator_invertible_2cell h₁ h₃ g₃))
                    • ((γ ▹ h₃) ▹ g₃)
                  =
                  comp_of_invertible_2cell
                    α₂
                    (comp_of_invertible_2cell
                       (lwhisker_of_invertible_2cell h₂ β)
                       (lassociator_invertible_2cell h₂ h₃ g₃)))
    : pb_1cell_on_comp f α₁ β • f /≃₂ q
      =
      (f /≃₂ p ▹ f /≃₁ β) • pb_1cell_on_comp f α₂ β.
  Proof.
    use eq_to_pb_obj.
    - unfold cell_to_pb_obj_homot.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        rewrite rwhisker_rwhisker_alt.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite rwhisker_rwhisker.
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        apply id2_right.
      }
      rewrite vcomp_whisker.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      rewrite pb_on_2cell_pr1, !pb_1cell_on_comp_pr1.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      apply maponpaths_2.
      rewrite !vassocl.
      apply maponpaths.
      rewrite vcomp_linv.
      rewrite id2_right.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite pb_on_2cell_pr1.
      rewrite !vassocl.
      apply maponpaths.
      rewrite vcomp_linv.
      rewrite id2_right.
      apply idpath.
    - rewrite <- !rwhisker_vcomp.
      rewrite pb_on_2cell_pr2, !pb_1cell_on_comp_pr2.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_linv.
        apply id2_left.
      }
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      rewrite pb_on_2cell_pr2.
      rewrite !vassocl.
      rewrite vcomp_linv.
      rewrite id2_right.
      apply idpath.
  Qed.
End Functions.

Module Notations.
  Notation "f '/≃' g" := (pb_obj f g) (at level 40).
  Notation "'π₁'" := (pb_pr1 _ _).
  Notation "'π₂'" := (pb_pr2 _ _).
  Notation "h₁ ⊗[ γ ] h₂" := (mor_to_pb_obj h₁ h₂ γ) (at level 10).
  Notation "f /≃₁ β" := (pb_on_1cell f β) (at level 40).
  Notation "f /≃₂ p" := (pb_on_2cell f p) (at level 40).
End Notations.
