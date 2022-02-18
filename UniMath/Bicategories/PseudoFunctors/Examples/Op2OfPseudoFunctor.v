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

(*
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.

Definition psfunctor_invertible_2cell
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
           {b₁ b₂ : B₁}
           {f g : b₁ --> b₂}
           (α : invertible_2cell f g)
  : invertible_2cell (#F f) (#F g).
Proof.
  use make_invertible_2cell.
  - exact (##F α).
  - apply psfunctor_is_iso.
Defined.

Definition help_data
           {B : bicat}
           (F : psfunctor (op2_bicat B) B)
           (η : pstrans
                  (id_psfunctor (op2_bicat B))
                  (comp_psfunctor (op2_psfunctor F) F))
  : pstrans_data
      (comp_psfunctor F (id_psfunctor (op2_bicat B)))
      (comp_psfunctor F (comp_psfunctor (op2_psfunctor F) F)).
Proof.
  use make_pstrans_data.
  - exact (λ b, #F (η b)).
  - refine (λ b₁ b₂ f, _) ; cbn.
    exact (comp_of_invertible_2cell
             (psfunctor_comp F _ _)
             (comp_of_invertible_2cell
                (psfunctor_invertible_2cell F (psnaturality_of η f))
                (inv_of_invertible_2cell (psfunctor_comp F _ _)))).
Defined.

Definition help_is_pstrans
           {B : bicat}
           (F : psfunctor (op2_bicat B) B)
           (η : pstrans
                  (id_psfunctor (op2_bicat B))
                  (comp_psfunctor (op2_psfunctor F) F))
  : is_pstrans (help_data F η).
Proof.
  repeat split.
  - intros b₁ b₂ f g α ; cbn -[psfunctor_id psfunctor_comp].
    rewrite !vassocr.
    rewrite <- (psfunctor_lwhisker F).
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    use vcomp_move_R_Mp ; [ is_iso | ] ; cbn -[psfunctor_id psfunctor_comp].
    rewrite !vassocl.
    rewrite <- (psfunctor_rwhisker F).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_linv.
      apply id2_left.
    }
    rewrite <- !(psfunctor_vcomp F).
    apply maponpaths.
    exact (!(psnaturality_natural η _ _ _ _ α)).
  - intro b ; cbn -[psfunctor_id psfunctor_comp].
    pose (pstrans_id_alt η b) as p.
    cbn -[psfunctor_id psfunctor_comp] in p.
    rewrite p.
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      do 3 (refine (psfunctor_vcomp F _ _ @ _) ; apply maponpaths_2).
      apply idpath.
    }
    rewrite !vassocl.
    etrans.
    {
      do 4 apply maponpaths.
      apply maponpaths_2.
      exact (psfunctor_linvunitor F (η b)).
    }
    etrans.
    {
      do 3 apply maponpaths.
      apply maponpaths_2.
      exact (psfunctor_F_runitor F (η b)).
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      do 8 apply maponpaths_2.
      apply (psfunctor_lwhisker F).
    }
    rewrite !vassocl.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_rinv.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      do 6 apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        apply maponpaths_2.
        apply (psfunctor_rwhisker F).
      }
      rewrite !vassocl.
      rewrite vcomp_rinv.
      refine (id2_right _ @ _).
      apply maponpaths.
      apply psfunctor_id2.
    }
    rewrite id2_rwhisker.
    rewrite id2_right.
    rewrite !vassocr.
    etrans.
    {
      do 3 apply maponpaths_2.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
Admitted.

Definition TODO {A : UU} : A.
Admitted.

Definition help
           {B : bicat}
           (F : psfunctor (op2_bicat B) B)
           (η : pstrans
                  (id_psfunctor (op2_bicat B))
                  (comp_psfunctor (op2_psfunctor F) F))
  : pstrans
      (comp_psfunctor F (id_psfunctor (op2_bicat B)))
      (comp_psfunctor F (comp_psfunctor (op2_psfunctor F) F)).
Proof.
  use make_pstrans.
  - exact (help_data F η).
  - apply TODO.
Defined.

Section DualityInvolution.
  Context (B : bicat).


  Definition duality_involution_data
    : UU
    := ∑ (F : psfunctor (op2_bicat B) B)
         (η : pstrans
                (id_psfunctor _)
                (comp_psfunctor
                   (op2_psfunctor F)
                   F)),
       invertible_modification
         (left_whisker F η)
         (help F η).
End DualityInvolution.

Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.OpFunctor.

Definition test_pstrans_data
  : pstrans_data
      (id_psfunctor (op2_bicat bicat_of_univ_cats))
      (comp_psfunctor (op2_psfunctor op_psfunctor) op_psfunctor).
Proof.
  use make_pstrans_data.
  - exact (λ C, functor_identity (pr1 C)).
  - refine (λ C₁ C₂ F, _).
    simple refine (_ ,, _).
    + use make_nat_trans.
      * exact (λ _, identity _).
      * abstract
          (intros x y f ; cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    + use bicat_is_invertible_2cell_to_op2_bicat_is_invertible_2cell.
      use is_nat_iso_to_is_invertible_2cell.
      intro x ; cbn.
      apply TODO.
Defined.

Definition test_is_pstrans
  : is_pstrans test_pstrans_data.
Proof.
  repeat split ; intro ; intros ;
    (use nat_trans_eq ; [ apply homset_property | ]) ;
    intro ; cbn ;
      rewrite !id_left, ?id_right.
  - apply idpath.
  - apply idpath.
  - exact (!(functor_id _ _)).
Qed.

Definition test_pstrans
  : pstrans
      (id_psfunctor (op2_bicat bicat_of_univ_cats))
      (comp_psfunctor (op2_psfunctor op_psfunctor) op_psfunctor).
Proof.
  use make_pstrans.
  - exact test_pstrans_data.
  - exact test_is_pstrans.
Defined.

Definition test_modif
  : invertible_modification
      (op_psfunctor ◅ test_pstrans)
      (help op_psfunctor test_pstrans).
Proof.
  use make_invertible_modification.
  - intro C.
    use nat_iso_to_invertible_2cell.
    use make_nat_iso.
    + use make_nat_trans.
      * exact (λ _, identity _).
      * intros ? ? f ; cbn.
        rewrite id_left, id_right.
        apply idpath.
    + cbn.
      apply TODO.
  - intros C₁ C₂ F.
    use nat_trans_eq ; [ apply homset_property | ] ; cbn.
    intro x.
    rewrite !id_left.
    rewrite functor_id.
    apply idpath.
Defined.

Definition test
  : duality_involution_data bicat_of_univ_cats.
Proof.
  simple refine (op_psfunctor ,, test_pstrans ,, test_modif).
Defined.


(*
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.OpFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Definition test
  : pstrans
      (id_psfunctor _)
      (comp_psfunctor
         ( op_psfunctor)
         op_psfunctor).
Proof.
  use make_pstrans.
  - use make_pstrans_data.
    + intro C ; cbn.
      apply functor_identity.
    + cbn.
    _data.
  refine ().
 *)
 *)
