Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

Section Op2PseudoFunctor.
  Context {B : bicat}
          (F : psfunctor (op2_bicat B) B).

  Definition op2_psfunctor_data
    : psfunctor_data B (op2_bicat B).
  Proof.
    use make_psfunctor_data.
    - exact (λ b, F b).
    - exact (λ _ _ f, #F f).
    - exact (λ _ _ _ _ α, ##F α).
    - exact (λ b, (psfunctor_id F b)^-1).
    - exact (λ _ _ _ f g, (psfunctor_comp F f g)^-1).
  Defined.

  Definition op2_psfunctor_laws
    : psfunctor_laws op2_psfunctor_data.
  Proof.
    repeat split.
    - intros ? ? f ; cbn.
      exact (psfunctor_id2 F f).
    - intros ? ? ? ? ? α β ; cbn.
      exact (psfunctor_vcomp F β α).
    - intros ? ? f ; cbn -[psfunctor_id psfunctor_comp].
      pose (psfunctor_linvunitor F f) as p.
      cbn -[psfunctor_id psfunctor_comp] in p.
      rewrite p.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite vassocr.
        rewrite vcomp_rinv.
        apply id2_left.
      }
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite id2_rwhisker.
      apply id2_right.
    - intros ? ? f ; cbn -[psfunctor_id psfunctor_comp].
      pose (psfunctor_rinvunitor F f) as p.
      cbn -[psfunctor_id psfunctor_comp] in p.
      rewrite p.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite vassocr.
        rewrite vcomp_rinv.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_right.
    - intros ? ? ? ? f g h ; cbn -[psfunctor_comp].
      pose (psfunctor_rassociator F f g h) as p.
      cbn -[psfunctor_id psfunctor_comp] in p.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn -[psfunctor_comp].
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn -[psfunctor_comp].
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[psfunctor_comp].
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[psfunctor_comp].
      exact p.
    - intros ? ? ? f ? ? α ; cbn -[psfunctor_comp].
      pose (psfunctor_lwhisker F f α) as p.
      cbn -[psfunctor_comp] in p.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn -[psfunctor_comp].
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[psfunctor_comp].
      exact p.
    - intros ? ? ? ? ? g α ; cbn -[psfunctor_comp].
      pose (psfunctor_rwhisker F g α) as p.
      cbn -[psfunctor_comp] in p.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn -[psfunctor_comp].
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[psfunctor_comp].
      exact p.
  Qed.

  Definition op2_psfunctor_invertible_cells
    : invertible_cells op2_psfunctor_data.
  Proof.
    split.
    - intros.
      apply to_op2_is_invertible_2cell.
      cbn - [psfunctor_id].
      is_iso.
    - intros.
      apply to_op2_is_invertible_2cell.
      cbn - [psfunctor_id].
      is_iso.
  Defined.

  Definition op2_psfunctor
    : psfunctor B (op2_bicat B).
  Proof.
    use make_psfunctor.
    - exact op2_psfunctor_data.
    - exact op2_psfunctor_laws.
    - exact op2_psfunctor_invertible_cells.
  Defined.
End Op2PseudoFunctor.
