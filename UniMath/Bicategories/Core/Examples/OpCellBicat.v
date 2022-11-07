(* ----------------------------------------------------------------------------------- *)
(** ** op2 bicategory.

    Bicategory obtained by formally reversing 2-cells.

    Benedikt Ahrens, Marco Maggesi
    February 2018                                                                      *)
(* ----------------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.

Local Open Scope cat.

Section OpCell.
  Context (B : bicat).

  Definition op2_prebicat_data
    : prebicat_data.
  Proof.
    use build_prebicat_data.
    - exact B.
    - exact (λ x y, x --> y).
    - exact (λ x y f g, g ==> f).
    - exact (λ x, id₁ _).
    - exact (λ x y z f g, f · g).
    - exact (λ x y f, id₂ _).
    - exact (λ x y f g h α β, β • α).
    - exact (λ x y z f g h α, f ◃ α).
    - exact (λ x y z g h f α, α ▹ f).
    - exact (λ x y f, linvunitor f).
    - exact (λ x y f, lunitor f).
    - exact (λ x y f, rinvunitor f).
    - exact (λ x y f, runitor f).
    - exact (λ w x y z f g h, rassociator f g h).
    - exact (λ w x y z f g h, lassociator f g h).
  Defined.

  Lemma op2_prebicat_laws : prebicat_laws op2_prebicat_data.
  Proof.
    repeat split; intros; cbn.
    - apply id2_right.
    - apply id2_left.
    - apply (!vassocr _ _ _ ).
    - apply lwhisker_id2.
    - apply id2_rwhisker.
    - apply lwhisker_vcomp.
    - apply rwhisker_vcomp.
    - use lhs_left_invert_cell; [ apply is_invertible_2cell_linvunitor |].
      cbn.
      apply pathsinv0.
      etrans. { apply vassocr. }
      use lhs_right_invert_cell; [ apply is_invertible_2cell_linvunitor |].
      cbn.
      apply pathsinv0. apply vcomp_lunitor.
    - use lhs_left_invert_cell; [ apply is_invertible_2cell_rinvunitor |].
      cbn.
      apply pathsinv0.
      etrans. { apply vassocr. }
      use lhs_right_invert_cell; [ apply is_invertible_2cell_rinvunitor |].
      cbn.
      apply pathsinv0. apply vcomp_runitor.
    - apply lassociator_to_rassociator_pre.
      apply pathsinv0.
      etrans. { apply (vassocr _ _ _ ). }
      apply lassociator_to_rassociator_post.
      apply pathsinv0. apply lwhisker_lwhisker.
    - apply lassociator_to_rassociator_pre.
      apply pathsinv0.
      etrans. { apply (vassocr _ _ _ ). }
      apply lassociator_to_rassociator_post.
      apply pathsinv0. apply rwhisker_lwhisker.
    - apply pathsinv0, lassociator_to_rassociator_pre.
      apply pathsinv0.
      etrans. { apply (vassocr _ _ _ ). }
      apply lassociator_to_rassociator_post.
      apply rwhisker_rwhisker.
    - apply (!vcomp_whisker _ _  ).
    - apply lunitor_linvunitor.
    - apply linvunitor_lunitor.
    - apply runitor_rinvunitor.
    - apply rinvunitor_runitor.
    - apply lassociator_rassociator.
    - apply rassociator_lassociator.
    - use lhs_left_invert_cell.
      { use is_invertible_2cell_rwhisker.
        apply is_invertible_2cell_rinvunitor.
      } cbn.
      apply pathsinv0.
      use lhs_right_invert_cell.
      { use is_invertible_2cell_lwhisker.
        apply is_invertible_2cell_linvunitor.
      } cbn.
      apply pathsinv0.
      apply lassociator_to_rassociator_pre.
      apply pathsinv0, runitor_rwhisker.
    - use lhs_left_invert_cell.
      { use is_invertible_2cell_rwhisker.
        apply is_invertible_2cell_rassociator.
      } cbn.
      apply pathsinv0.
      etrans. { apply vassocr. }
      use lhs_right_invert_cell.
      { apply is_invertible_2cell_rassociator.
      } cbn.
      use lhs_right_invert_cell.
      { apply is_invertible_2cell_rassociator.
      } cbn.
      apply pathsinv0.
      repeat rewrite <- vassocr.
      use lhs_left_invert_cell.
      { apply is_invertible_2cell_rassociator.
      } cbn.
      use lhs_left_invert_cell.
      { apply is_invertible_2cell_lwhisker.
        apply is_invertible_2cell_rassociator.
      } cbn.
      apply pathsinv0.
      rewrite vassocr.
      apply lassociator_lassociator.
  Qed.

  Definition op2_prebicat
    : prebicat
    := op2_prebicat_data ,, op2_prebicat_laws.

  Definition op2_bicat
    : bicat.
  Proof.
    refine (op2_prebicat ,, _).
    intro ; intros.
    apply cellset_property.
  Defined.
End OpCell.

Definition from_op2_is_invertible_2cell
           {B : bicat}
           {x y : op2_bicat B}
           {f g : x --> y}
           {α : f ==> g}
           (Hα : is_invertible_2cell α)
  : @is_invertible_2cell B x y g f α.
Proof.
  use make_is_invertible_2cell.
  - exact (Hα^-1).
  - exact (vcomp_linv Hα).
  - exact (vcomp_rinv Hα).
Defined.

Definition to_op2_is_invertible_2cell
           {B : bicat}
           {x y : op2_bicat B}
           {f g : x --> y}
           {α : f ==> g}
           (Hα : @is_invertible_2cell B x y g f α)
  : is_invertible_2cell α.
Proof.
  use make_is_invertible_2cell.
  - exact (Hα^-1).
  - exact (vcomp_linv Hα).
  - exact (vcomp_rinv Hα).
Defined.

Definition weq_op2_is_invertible_2cell
           {B : bicat}
           {x y : op2_bicat B}
           {f g : x --> y}
           (α : f ==> g)
  : @is_invertible_2cell B x y g f α
    ≃
    is_invertible_2cell α.
Proof.
  use weqimplimpl.
  - exact to_op2_is_invertible_2cell.
  - exact from_op2_is_invertible_2cell.
  - apply isaprop_is_invertible_2cell.
  - apply isaprop_is_invertible_2cell.
Defined.

Definition weq_op2_invertible_2cell
           {B : bicat}
           {x y : op2_bicat B}
           (f g : x --> y)
  : @invertible_2cell B x y g f ≃ invertible_2cell f g.
Proof.
  use weqfibtototal.
  intro α.
  apply weq_op2_is_invertible_2cell.
Defined.

Definition from_op2_left_adjequiv
           {B : bicat}
           {x y : op2_bicat B}
           (f : x --> y)
  : left_adjoint_equivalence f → @left_adjoint_equivalence B x y f.
Proof.
  intros Hf.
  simple refine ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _))).
  - exact (left_adjoint_right_adjoint Hf).
  - exact ((left_equivalence_unit_iso Hf)^-1).
  - exact ((left_equivalence_counit_iso Hf)^-1).
  - abstract
      (use inv_cell_eq ; cbn ;
       [ is_iso ;
         [ apply from_op2_is_invertible_2cell ;
           is_iso
         | apply from_op2_is_invertible_2cell ;
           is_iso
         ]
       | is_iso
       | exact (internal_triangle1 Hf) ]).
  - abstract
      (use inv_cell_eq ; cbn ;
       [ is_iso ;
         [ apply from_op2_is_invertible_2cell ;
           is_iso
         | apply from_op2_is_invertible_2cell ;
           is_iso ]
       | is_iso
       | exact (internal_triangle2 Hf) ]).
  - cbn.
    apply from_op2_is_invertible_2cell.
    is_iso.
  - cbn.
    apply from_op2_is_invertible_2cell.
    is_iso.
Defined.

Definition to_op2_left_adjequiv
           {B : bicat}
           {x y : op2_bicat B}
           (f : x --> y)
  : @left_adjoint_equivalence B x y f → left_adjoint_equivalence f.
Proof.
  intros Hf.
  simple refine ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _))).
  - exact (left_adjoint_right_adjoint Hf).
  - exact ((left_equivalence_unit_iso Hf)^-1).
  - exact ((left_equivalence_counit_iso Hf)^-1).
  - abstract
      (use inv_cell_eq ; cbn ;
       [ apply to_op2_is_invertible_2cell ;
         is_iso
       | apply to_op2_is_invertible_2cell ;
         is_iso
       | exact (internal_triangle1 Hf) ]).
  - abstract
      (use inv_cell_eq ; cbn ;
       [ apply to_op2_is_invertible_2cell ;
         is_iso
       | apply to_op2_is_invertible_2cell ;
         is_iso
       | exact (internal_triangle2 Hf)]).
  - cbn.
    apply to_op2_is_invertible_2cell.
    is_iso.
  - cbn.
    apply to_op2_is_invertible_2cell.
    is_iso.
Defined.

Definition weq_op2_left_adjequiv
           {B : bicat}
           {x y : op2_bicat B}
           (f : x --> y)
  : @left_adjoint_equivalence B x y f ≃ left_adjoint_equivalence f.
Proof.
  use make_weq.
  - exact (to_op2_left_adjequiv f).
  - use isweq_iso.
    + exact (from_op2_left_adjequiv f).
    + abstract
        (intros Hf ;
         refine (maponpaths (λ z, _ ,, z) _) ;
         apply isapropdirprod ;
         [ apply isapropdirprod ; apply cellset_property
         | apply isapropdirprod ; apply isaprop_is_invertible_2cell ]).
    + abstract
        (intros Hf ;
         refine (maponpaths (λ z, _ ,, z) _) ;
         apply isapropdirprod ;
         [ apply isapropdirprod ; apply cellset_property
         | apply isapropdirprod ; apply isaprop_is_invertible_2cell ]).
Defined.

Definition weq_op2_adjequiv
           {B : bicat}
           (x y : op2_bicat B)
  : @adjoint_equivalence B x y ≃ adjoint_equivalence x y.
Proof.
  use weqfibtototal.
  intro α.
  apply weq_op2_left_adjequiv.
Defined.
