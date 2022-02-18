(**
 Duality involutions of bicategories

 Contents:
 1. Data of duality involutions
 2. Counit of duality involution
 3. Laws of duality involutions
 4. Duality involutions
 5. Duality involution on categories
 6. Duality involution on locally groupoidal bicategory
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Op2OfPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.OpFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.

Local Open Scope cat.

(**
 1. Data of duality involutions
 *)
Section DualityInvolutionData.
  Context {B : bicat}
          (L : psfunctor (op2_bicat B) B).

  Let R : psfunctor B (op2_bicat B)
    := op2_psfunctor L.

  Definition duality_involution_data
    : UU
    := ∑ (η : pstrans
                (id_psfunctor B)
                (comp_psfunctor L R))
         (ηinv : pstrans
                   (comp_psfunctor L R)
                   (id_psfunctor B)),
       (invertible_modification
          (id₁ _)
          (η · ηinv))
       ×
       (invertible_modification
          (ηinv · η)
          (id₁ _))
       ×
       (∏ (x : op2_bicat B),
        invertible_2cell
          (η (L x))
          (#L (η x))).

  Definition make_duality_involution_data
             (η : pstrans
                    (id_psfunctor B)
                    (comp_psfunctor L R))
             (ηinv : pstrans
                       (comp_psfunctor L R)
                       (id_psfunctor B))
             (m₁ : invertible_modification
                     (id₁ _)
                     (η · ηinv))
             (m₂ : invertible_modification
                     (ηinv · η)
                     (id₁ _))
             (t : ∏ (x : op2_bicat B),
                  invertible_2cell
                    (η (L x))
                    (#L (η x)))
    : duality_involution_data
    := η ,, ηinv ,, m₁ ,, m₂ ,, t.
End DualityInvolutionData.

Section Projections.
  Context {B : bicat}
          {L : psfunctor (op2_bicat B) B}
          (d : duality_involution_data L).

  Let R : psfunctor B (op2_bicat B)
    := op2_psfunctor L.

  Definition unit_of_duality
    : pstrans
        (id_psfunctor B)
        (comp_psfunctor L R)
    := pr1 d.

  Let η := unit_of_duality.

  Definition unit_inv_of_duality
    : pstrans
        (comp_psfunctor L R)
        (id_psfunctor B)
    := pr12 d.

  Let ηinv := unit_inv_of_duality.

  Definition unit_unit_inv_of_duality
    : invertible_modification
        (id₁ _)
        (η · ηinv)
    := pr122 d.

  Definition unit_inv_unit_of_duality
    : invertible_modification
          (ηinv · η)
          (id₁ _)
    := pr1 (pr222 d).

  Definition triangle_data_of_duality
             (x : op2_bicat B)
    : invertible_2cell
        (η (L x))
        (#L (η x))
    := pr2 (pr222 d) x.
End Projections.

(**
 2. Counit of duality involution
 *)
Section CounitFromDualityInvolution.
  Context {B : bicat}
          {L : psfunctor (op2_bicat B) B}
          (d : duality_involution_data L).

  Let R : psfunctor B (op2_bicat B)
    := op2_psfunctor L.

  Let η := unit_of_duality d.
  Let ηinv := unit_inv_of_duality d.
  Let ηηinv := unit_unit_inv_of_duality d.
  Let ηinvη := unit_inv_unit_of_duality d.
  Let t := triangle_data_of_duality d.

  Definition left_adjoint_equivalance_duality_unit
    : left_adjoint_equivalence η.
  Proof.
    use equiv_to_adjequiv.
    simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
    - exact ηinv.
    - exact (pr1 ηηinv).
    - exact (pr1 ηinvη).
    - apply property_from_invertible_2cell.
    - apply property_from_invertible_2cell.
  Defined.

  Definition duality_counit_data
    : pstrans_data
        (comp_psfunctor R L)
        (id_psfunctor (op2_bicat B)).
  Proof.
    use make_pstrans_data.
    - refine (λ x, _).
      exact (ηinv x : L(L x) --> x).
    - intros x y f ; cbn.
      use weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell (psnaturality_of ηinv f)).
  Defined.

  Definition duality_counit_is_pstrans
    : is_pstrans duality_counit_data.
  Proof.
    repeat split.
    - intros x y f g α ; cbn.
      use vcomp_move_R_pM ; [ is_iso | ].
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn.
      exact (psnaturality_natural ηinv _ _ _ _ α).
    - intro x ; cbn.
      rewrite lwhisker_id2, id2_right.
      pose (pstrans_id ηinv x) as p.
      cbn in p.
      rewrite lwhisker_id2 in p.
      rewrite id2_left in p.
      use vcomp_move_L_pM.
      {
        is_iso.
        exact (psfunctor_is_iso L (weq_op2_invertible_2cell _ _ (psfunctor_id L x))).
      }
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      exact (!p).
    - intros x y z f g ; cbn.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite lwhisker_id2.
      pose (p := pstrans_comp ηinv f g).
      cbn in p.
      rewrite lwhisker_id2, id2_left in p.
      use vcomp_move_L_Mp ; [ is_iso | ].
      {
        exact (psfunctor_is_iso L (weq_op2_invertible_2cell _ _ (psfunctor_comp L f g))).
      }
      refine (id2_left _ @ _).
      exact (!p).
  Qed.

  Definition duality_counit
    : pstrans
        (comp_psfunctor R L)
        (id_psfunctor (op2_bicat B)).
  Proof.
    use make_pstrans.
    - exact duality_counit_data.
    - exact duality_counit_is_pstrans.
  Defined.

  Let ε : pstrans
            (comp_psfunctor R L)
            (id_psfunctor (op2_bicat B))
    := duality_counit.

  Definition duality_counit_inv_data
    : pstrans_data
        (id_psfunctor (op2_bicat B))
        (comp_psfunctor R L).
  Proof.
    use make_pstrans_data.
    - refine (λ x, _).
      exact (η x : x --> L(L x)).
    - intros x y f ; cbn.
      use weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell (psnaturality_of η f)).
  Defined.

  Definition duality_counit_inv_is_pstrans
    : is_pstrans duality_counit_inv_data.
  Proof.
    repeat split.
    - intros x y f g α ; cbn.
      use vcomp_move_R_pM ; [ is_iso | ].
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn.
      exact (psnaturality_natural η _ _ _ _ α).
    - intro x ; cbn.
      rewrite id2_rwhisker, id2_left.
      pose (pstrans_id η x) as p.
      cbn in p.
      rewrite id2_rwhisker in p.
      rewrite id2_right in p.
      use vcomp_move_R_Mp.
      {
        is_iso.
        exact (psfunctor_is_iso L (weq_op2_invertible_2cell _ _ (psfunctor_id L x))).
      }
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      exact (!p).
    - intros x y z f g ; cbn.
      rewrite id2_rwhisker, id2_left.
      pose (p := pstrans_comp η f g).
      cbn in p.
      rewrite id2_rwhisker, id2_right in p.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      use vcomp_move_R_pM.
      {
        is_iso.
        exact (psfunctor_is_iso L (weq_op2_invertible_2cell _ _ (psfunctor_comp L f g))).
      }
      exact (!p).
  Qed.

  Definition duality_counit_inv
    : pstrans
        (id_psfunctor (op2_bicat B))
        (comp_psfunctor R L).
  Proof.
    use make_pstrans.
    - exact duality_counit_inv_data.
    - exact duality_counit_inv_is_pstrans.
  Defined.

  Let εinv : pstrans
               (id_psfunctor (op2_bicat B))
               (comp_psfunctor R L)
    := duality_counit_inv.

  Definition duality_counit_counit_inv_data
    : invertible_modification_data
        (id₁ _)
        (ε · εinv).
  Proof.
    intro x ; cbn.
    use weq_op2_invertible_2cell.
    exact (invertible_modcomponent_of ηinvη x).
  Defined.

  Definition duality_counit_counit_inv_is_modif
    : is_modification duality_counit_counit_inv_data.
  Proof.
    intros x y f.
    use vcomp_move_R_pM.
    {
      apply property_from_invertible_2cell.
    }
    refine (_ @ vassocl _ _ _).
    use vcomp_move_L_Mp.
    {
      is_iso.
      apply property_from_invertible_2cell.
    }
    exact (modnaturality_of (pr1 ηinvη) _ _ f).
  Qed.

  Definition duality_counit_counit_inv
    : invertible_modification
        (id₁ _)
        (ε · εinv).
  Proof.
    use make_invertible_modification.
    - exact duality_counit_counit_inv_data.
    - exact duality_counit_counit_inv_is_modif.
  Defined.

  Definition duality_counit_inv_counit_data
    : invertible_modification_data
        (εinv · ε)
        (id₁ _).
  Proof.
    intro x ; cbn.
    use weq_op2_invertible_2cell.
    exact (invertible_modcomponent_of ηηinv x).
  Defined.

  Opaque comp_psfunctor.

  Definition duality_counit_inv_counit_is_modif
    : is_modification duality_counit_inv_counit_data.
  Proof.
    intros x y f.
    use vcomp_move_R_pM.
    {
      apply property_from_invertible_2cell.
    }
    refine (_ @ vassocl _ _ _).
    use vcomp_move_L_Mp.
    {
      is_iso.
      apply property_from_invertible_2cell.
    }
    etrans.
    {
      apply maponpaths.
      cbn.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      cbn.
      apply idpath.
    }
    pose (p := modnaturality_of (pr1 ηηinv) _ _ f).
    cbn in p.
    exact (!p).
  Qed.

  Transparent comp_psfunctor.

  Definition duality_counit_inv_counit
    : invertible_modification
        (εinv · ε)
        (id₁ _).
  Proof.
    use make_invertible_modification.
    - exact duality_counit_inv_counit_data.
    - exact duality_counit_inv_counit_is_modif.
  Defined.

  Definition left_equivalance_duality_counit
    : left_equivalence ε.
  Proof.
    simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
    - exact εinv.
    - exact (pr1 duality_counit_counit_inv).
    - exact (pr1 duality_counit_inv_counit).
    - exact (pr2 duality_counit_counit_inv).
    - exact (pr2 duality_counit_inv_counit).
  Defined.

  Definition left_adjoint_equivalance_duality_counit
    : left_adjoint_equivalence ε
    := equiv_to_adjequiv
         ε
         left_equivalance_duality_counit.
End CounitFromDualityInvolution.

(**
 3. Laws of duality involutions
 *)
Section LawsDualityInvolution.
  Context {B : bicat}
          {L : psfunctor (op2_bicat B) B}
          (d : duality_involution_data L).

  Let R : psfunctor B (op2_bicat B)
    := op2_psfunctor L.

  Let η := unit_of_duality d.
  Let ηinv := unit_inv_of_duality d.
  Let ηηinv := unit_unit_inv_of_duality d.
  Let ηinvη := unit_inv_unit_of_duality d.
  Let t := triangle_data_of_duality d.

  Definition duality_coherency_lhs
             (x : B)
    : η x · # L (# L (η x)) ==> η x · # L (η (L x))
    := psnaturality_of η (η x) • (η x ◃ t (L x)).

  Definition duality_coherency_rhs
             (x : B)
    : η x · # L (# L (η x)) ==> η x · # L (η (L x))
    := η x ◃ ##L (t x).

  Definition duality_coherency
    := ∏ (x : B),
       duality_coherency_lhs x
       =
       duality_coherency_rhs x.

  Let εinv := duality_counit_inv d.

  Definition duality_modification_data
    : invertible_modification_data
        (linvunitor_pstrans _
         · right_whisker L η)
        (rinvunitor_pstrans _
         · left_whisker L εinv
         · lassociator_pstrans _ _ _).
  Proof.
    intros x ; cbn.
    exact (comp_of_invertible_2cell
             (lunitor_invertible_2cell _)
             (comp_of_invertible_2cell
                (t x)
                (comp_of_invertible_2cell
                   (linvunitor_invertible_2cell _)
                   (rinvunitor_invertible_2cell _)))).
  Defined.

  Definition duality_involution_laws
    : UU
    := duality_coherency
       ×
       is_modification duality_modification_data.
End LawsDualityInvolution.

(**
 4. Duality involutions
 *)
Definition duality_involution
           {B : bicat}
           (L : psfunctor (op2_bicat B) B)
  : UU
  := ∑ (d : duality_involution_data L),
     duality_involution_laws d.

Definition duality_involution_to_data
           {B : bicat}
           {L : psfunctor (op2_bicat B) B}
           (d : duality_involution L)
  : duality_involution_data L
  := pr1 d.

Definition duality_involution_to_laws
           {B : bicat}
           {L : psfunctor (op2_bicat B) B}
           (d : duality_involution L)
  : duality_involution_laws (duality_involution_to_data d)
  := pr2 d.

(**
 5. Duality involution on categories
 *)
Definition op_unit_nat_trans
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : functor_identity C₁ ∙ functor_opp (functor_opp F)
    ⟹
    F ∙ functor_identity C₂.
Proof.
  use make_nat_trans.
  - exact (λ x, identity (F x)).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_nat_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : nat_iso
      (functor_identity C₁ ∙ functor_opp (functor_opp F))
      (F ∙ functor_identity C₂).
Proof.
  use make_nat_iso.
  - exact (op_unit_nat_trans F).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_unit_data
  : pstrans_data
      (id_psfunctor _)
      (comp_psfunctor op_psfunctor (op2_psfunctor op_psfunctor)).
Proof.
  use make_pstrans_data.
  - exact (λ C, functor_identity _).
  - intros C₁ C₂ F.
    use nat_iso_to_invertible_2cell.
    exact (op_unit_nat_iso F).
Defined.

Definition op_unit_is_pstrans
  : is_pstrans op_unit_data.
Proof.
  repeat split ; intro ; intros ;
    (use nat_trans_eq ; [ apply homset_property | ]) ; intro ; cbn ;
    rewrite ?id_left, ?id_right.
  - apply idpath.
  - apply idpath.
  - exact (!(functor_id _ _)).
Qed.

Definition op_unit
  : pstrans
      (id_psfunctor _)
      (comp_psfunctor op_psfunctor (op2_psfunctor op_psfunctor)).
Proof.
  use make_pstrans.
  - exact op_unit_data.
  - exact op_unit_is_pstrans.
Defined.

Definition op_unit_inv_nat_trans
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : functor_identity _ ∙ F
    ⟹
    functor_opp (functor_opp F) ∙ functor_identity _.
Proof.
  use make_nat_trans.
  - exact (λ x, identity (F x)).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_inv_nat_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : nat_iso
      (functor_identity _ ∙ F)
      (functor_opp (functor_opp F) ∙ functor_identity _).
Proof.
  use make_nat_iso.
  - exact (op_unit_inv_nat_trans F).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_unit_inv_data
  : pstrans_data
      (comp_psfunctor op_psfunctor (op2_psfunctor op_psfunctor))
      (id_psfunctor _).
Proof.
  use make_pstrans_data.
  - exact (λ C, functor_identity _).
  - intros C₁ C₂ F.
    use nat_iso_to_invertible_2cell.
    exact (op_unit_inv_nat_iso F).
Defined.

Definition op_unit_inv_is_pstrans
  : is_pstrans op_unit_inv_data.
Proof.
  repeat split ; intro ; intros ;
    (use nat_trans_eq ; [ apply homset_property | ]) ; intro ; cbn ;
    rewrite ?id_left, ?id_right.
  - apply idpath.
  - apply idpath.
  - exact (!(functor_id _ _)).
Qed.

Definition op_unit_inv
  : pstrans
      (comp_psfunctor op_psfunctor (op2_psfunctor op_psfunctor))
      (id_psfunctor _).
Proof.
  use make_pstrans.
  - exact op_unit_inv_data.
  - exact op_unit_inv_is_pstrans.
Defined.

Definition op_triangle_nat_trans
           (C : category)
  : functor_identity _ ⟹ functor_opp (functor_identity C).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_triangle_nat_iso
           (C : category)
  : nat_iso
      (functor_identity _)
      (functor_opp (functor_identity C)).
Proof.
  use make_nat_iso.
  - exact (op_triangle_nat_trans C).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_triangle
           (C : op2_bicat bicat_of_univ_cats)
  : invertible_2cell
      (op_unit (op_psfunctor C))
      (# op_psfunctor (op_unit C)).
Proof.
  use nat_iso_to_invertible_2cell.
  exact (op_triangle_nat_iso _).
Defined.

Definition op_unit_unit_inv_nat_trans
           (C : category)
  : nat_trans
      (functor_identity C)
      (functor_identity C ∙ functor_identity ((C^op)^op)).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_unit_inv_nat_iso
           (C : category)
  : nat_iso
      (functor_identity C)
      (functor_identity C ∙ functor_identity ((C^op)^op)).
Proof.
  use make_nat_iso.
  - exact (op_unit_unit_inv_nat_trans C).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_unit_unit_inv_data
  : invertible_modification_data
      (id₁ _)
      (op_unit · op_unit_inv).
Proof.
  intro C.
  use nat_iso_to_invertible_2cell.
  exact (op_unit_unit_inv_nat_iso _).
Defined.

Definition op_unit_unit_inv_is_modif
  : is_modification op_unit_unit_inv_data.
Proof.
  intros C₁ C₂ F.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x ; cbn.
  rewrite !id_left, !id_right.
  exact (!(functor_id _ _)).
Qed.

Definition op_unit_unit_inv
  : invertible_modification
      (id₁ _)
      (op_unit · op_unit_inv).
Proof.
  use make_invertible_modification.
  - exact op_unit_unit_inv_data.
  - exact op_unit_unit_inv_is_modif.
Defined.

Definition op_unit_inv_unit_nat_trans
           (C : category)
  : nat_trans
      (functor_identity ((C^op)^op) ∙ functor_identity C)
      (functor_identity ((C^op)^op)).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_inv_unit_nat_iso
           (C : category)
  : nat_iso
      (functor_identity ((C^op)^op) ∙ functor_identity C)
      (functor_identity ((C^op)^op)).
Proof.
  use make_nat_iso.
  - exact (op_unit_inv_unit_nat_trans C).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_unit_inv_unit_data
  : invertible_modification_data
      (op_unit_inv · op_unit)
      (id₁ _).
Proof.
  intro C.
  use nat_iso_to_invertible_2cell.
  exact (op_unit_inv_unit_nat_iso _).
Defined.

Definition op_unit_inv_unit_is_modif
  : is_modification op_unit_inv_unit_data.
Proof.
  intros C₁ C₂ F.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x ; cbn.
  rewrite !id_left, !id_right.
  exact (!(functor_id _ _)).
Qed.

Definition op_unit_inv_unit
  : invertible_modification
      (op_unit_inv · op_unit)
      (id₁ _).
Proof.
  use make_invertible_modification.
  - exact op_unit_inv_unit_data.
  - exact op_unit_inv_unit_is_modif.
Defined.

Definition bicat_of_univ_cat_duality_involution_data
  : duality_involution_data op_psfunctor.
Proof.
  use make_duality_involution_data.
  - exact op_unit.
  - exact op_unit_inv.
  - exact op_unit_unit_inv.
  - exact op_unit_inv_unit.
  - exact op_triangle.
Defined.

Definition bicat_of_univ_cat_duality_laws
  : duality_involution_laws bicat_of_univ_cat_duality_involution_data.
Proof.
  split.
  - intro C.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x ; cbn.
    apply id_left.
  - intros C₁ C₂ F.
    use nat_trans_eq ; [ apply homset_property | ].
    intro  ; cbn.
    rewrite !id_left.
    exact (!(functor_id _ _)).
Qed.

Definition bicat_of_univ_cat_duality
  : duality_involution op_psfunctor
  := bicat_of_univ_cat_duality_involution_data ,, bicat_of_univ_cat_duality_laws.

(**
 6. Duality involution on locally groupoidal bicategory
 *)
Section DualityInvolutionLocallyGroupoidal.
  Context (B : bicat)
          (inv_B : locally_groupoid B).

  Definition op_locally_groupoid_data
    : psfunctor_data (op2_bicat B) B.
  Proof.
    use make_psfunctor_data.
    - exact (λ z, z).
    - exact (λ _ _ f, f).
    - exact (λ _ _ _ _ α, (inv_B _ _ _ _ α)^-1).
    - exact (λ _, id2 _).
    - exact (λ _ _ _ _ _, id2 _).
  Defined.

  Definition op_locally_groupoid_laws
    : psfunctor_laws op_locally_groupoid_data.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - refine (!(id2_right _) @ _).
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite id2_right.
      apply idpath.
    - use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      apply idpath.
    - use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite lunitor_linvunitor.
      rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite runitor_rinvunitor.
      rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - rewrite lwhisker_id2, id2_rwhisker.
      rewrite !id2_left, !id2_right.
      refine (!(id2_right _) @ _).
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite rassociator_lassociator.
      apply idpath.
    - use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_left, id2_right.
      apply idpath.
    - use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_left, id2_right.
      apply idpath.
  Qed.

  Definition op_locally_groupoid_invertible_cells
    : invertible_cells op_locally_groupoid_data.
  Proof.
    split ; intro ; intros ; cbn ; is_iso.
  Defined.

  Definition op_locally_groupoid
    : psfunctor (op2_bicat B) B.
  Proof.
    use make_psfunctor.
    - exact op_locally_groupoid_data.
    - exact op_locally_groupoid_laws.
    - exact op_locally_groupoid_invertible_cells.
  Defined.

  Definition locally_groupoid_duality_involution_unit_data
    : pstrans_data
        (id_psfunctor B)
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid)).
  Proof.
    use make_pstrans_data.
    - exact (λ x, id₁ _).
    - exact (λ _ _ f,
             comp_of_invertible_2cell
               (lunitor_invertible_2cell _)
               (rinvunitor_invertible_2cell _)).
  Defined.

  Definition locally_groupoid_duality_involution_unit_is_pstrans
    : is_pstrans locally_groupoid_duality_involution_unit_data.
  Proof.
    repeat split.
    - intros x y f g α ; cbn.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite !vassocr.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    - intro x ; cbn.
      rewrite !id2_left.
      rewrite id2_rwhisker, id2_right.
      use vcomp_move_R_pM ; [ is_iso | ].
      cbn.
      rewrite lwhisker_id2, id2_left.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - intros x y z f g ; cbn.
      rewrite id2_left.
      rewrite id2_rwhisker, id2_right.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      rewrite lwhisker_id2, id2_left.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_l_inv.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition locally_groupoid_duality_involution_unit
    : pstrans
        (id_psfunctor B)
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid)).
  Proof.
    use make_pstrans.
    - exact locally_groupoid_duality_involution_unit_data.
    - exact locally_groupoid_duality_involution_unit_is_pstrans.
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_data
    : pstrans_data
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid))
        (id_psfunctor B).
  Proof.
    use make_pstrans_data.
    - exact (λ _, id₁ _).
    - exact (λ _ _ f,
             comp_of_invertible_2cell
               (lunitor_invertible_2cell _)
               (rinvunitor_invertible_2cell _)).
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_is_pstrans
    : is_pstrans locally_groupoid_duality_involution_unit_inv_data.
  Proof.
    repeat split.
    - intros x y f g α ; cbn.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite rwhisker_hcomp.
      rewrite <- rinvunitor_natural.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      rewrite vcomp_rinv.
      apply id2_right.
    - intro x ; cbn.
      rewrite lwhisker_id2, id2_left.
      rewrite id2_left.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite runitor_lunitor_identity.
      rewrite lunitor_V_id_is_left_unit_V_id.
      apply idpath.
    - intros x y z f g ; cbn.
      rewrite lwhisker_id2, !id2_left.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite <- lunitor_triangle.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      do 2 apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_l_inv.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        apply id2_left.
      }
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
      Opaque comp_psfunctor.
  Qed.

  Transparent comp_psfunctor.

  Definition locally_groupoid_duality_involution_unit_inv
    : pstrans
        (comp_psfunctor op_locally_groupoid (op2_psfunctor op_locally_groupoid))
        (id_psfunctor B).
  Proof.
    use make_pstrans.
    - exact locally_groupoid_duality_involution_unit_inv_data.
    - exact locally_groupoid_duality_involution_unit_inv_is_pstrans.
  Defined.

  Definition locally_groupoid_duality_involution_unit_unit_inv_data
    : invertible_modification_data
        (id₁ (id_psfunctor B))
        (locally_groupoid_duality_involution_unit
         · locally_groupoid_duality_involution_unit_inv).
  Proof.
    intro x ; cbn.
    exact (linvunitor_invertible_2cell _).
  Defined.

  Definition locally_groupoid_duality_involution_unit_unit_inv_is_modif
    : is_modification
        locally_groupoid_duality_involution_unit_unit_inv_data.
  Proof.
    intros x y f ; cbn.
    rewrite <- rwhisker_vcomp.
    rewrite !vassocl.
    rewrite (rwhisker_hcomp _ (rinvunitor f)).
    rewrite <- triangle_r_inv.
    rewrite <- lwhisker_hcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite lunitor_V_id_is_left_unit_V_id.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_l_inv.
    rewrite <- lwhisker_hcomp.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite lwhisker_vcomp.
    rewrite !vassocr.
    rewrite linvunitor_lunitor.
    rewrite id2_left.
    rewrite !vassocl.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    apply idpath.
  Qed.

  Definition locally_groupoid_duality_involution_unit_unit_inv
    : invertible_modification
        (id₁ (id_psfunctor B))
        (locally_groupoid_duality_involution_unit
         · locally_groupoid_duality_involution_unit_inv).
  Proof.
    use make_invertible_modification.
    - exact locally_groupoid_duality_involution_unit_unit_inv_data.
    - exact locally_groupoid_duality_involution_unit_unit_inv_is_modif.
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_unit_data
    : invertible_modification_data
        (locally_groupoid_duality_involution_unit_inv
         · locally_groupoid_duality_involution_unit)
        (id₁ _).
  Proof.
    intro x ; cbn.
    exact (lunitor_invertible_2cell _).
  Defined.

  Definition locally_groupoid_duality_involution_unit_inv_unit_is_modif
    : is_modification
        locally_groupoid_duality_involution_unit_inv_unit_data.
  Proof.
    intros x y f ; cbn.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    rewrite lunitor_lwhisker.
    rewrite !vassocl.
    rewrite runitor_lunitor_identity.
    apply maponpaths.
    rewrite lunitor_lwhisker.
    rewrite rwhisker_vcomp.
    rewrite !vassocl.
    rewrite rinvunitor_runitor.
    rewrite id2_right.
    rewrite lunitor_triangle.
    rewrite vcomp_lunitor.
    apply idpath.
  Qed.

  Definition locally_groupoid_duality_involution_unit_inv_unit
    : invertible_modification
        (locally_groupoid_duality_involution_unit_inv
         · locally_groupoid_duality_involution_unit)
        (id₁ _).
  Proof.
    use make_invertible_modification.
    - exact locally_groupoid_duality_involution_unit_inv_unit_data.
    - exact locally_groupoid_duality_involution_unit_inv_unit_is_modif.
  Defined.

  Definition locally_groupoid_duality_involution_triangle
             (x : B)
    : invertible_2cell (id₁ x) (id₁ x)
    := id2_invertible_2cell _.

  Definition locally_groupoid_duality_involution_data
    : duality_involution_data op_locally_groupoid
    := make_duality_involution_data
         op_locally_groupoid
         locally_groupoid_duality_involution_unit
         locally_groupoid_duality_involution_unit_inv
         locally_groupoid_duality_involution_unit_unit_inv
         locally_groupoid_duality_involution_unit_inv_unit
         locally_groupoid_duality_involution_triangle.

  Definition locally_groupoid_duality_involution_laws_coh
             (x : B)
    : lunitor (id₁ x)
      • rinvunitor (id₁ x)
      • (id₁ x ◃ id₂ (id₁ x))
      =
      id₁ x ◃ (inv_B x x (id₁ x) (id₁ x) (id₂ (id₁ x)))^-1.
  Proof.
    rewrite lunitor_runitor_identity.
    rewrite runitor_rinvunitor.
    rewrite lwhisker_id2.
    rewrite !id2_left.
    refine (_ @ id2_right _).
    use vcomp_move_L_pM ; [ is_iso | ] ; cbn.
    rewrite lwhisker_id2.
    apply id2_left.
  Qed.

  Definition locally_groupoid_duality_involution_laws
    : duality_involution_laws locally_groupoid_duality_involution_data.
  Proof.
    split.
    - exact locally_groupoid_duality_involution_laws_coh.
    - intros x y f ; cbn.
      rewrite !id2_left, !id2_right.
      rewrite !vassocr.
      rewrite !lunitor_linvunitor.
      rewrite !id2_left.
      rewrite !vassocl.
      use vcomp_move_L_pM ; [ is_iso | ].
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn.
      rewrite !vassocr.
      rewrite runitor_rwhisker.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lunitor_lwhisker.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- rinvunitor_triangle.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      use vcomp_move_R_Mp ; [ is_iso | ] ; cbn.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite lwhisker_lwhisker_rassociator.
      refine (!_).
      etrans.
      {
        do 6 apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_rassociator.
        apply idpath.
      }
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      do 3 (use vcomp_move_R_pM ; [ is_iso | ]) ; cbn.
      rewrite rwhisker_rwhisker_alt.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker_alt.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocr.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      rewrite <- rassociator_rassociator.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_left.
      rewrite !vassocl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_hcomp.
          rewrite <- triangle_l.
          rewrite <- lwhisker_hcomp.
          rewrite !vassocl.
          apply idpath.
        }
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite !vassocl.
        rewrite <- rassociator_rassociator.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !lwhisker_vcomp.
      apply maponpaths.
      rewrite <- lunitor_triangle.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rassociator_lassociator.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      rewrite !vassocl.
      rewrite linvunitor_lunitor.
      rewrite id2_right.
      refine (_ @ id2_right _).
      use vcomp_move_L_pM ; [ is_iso | ].
      cbn.
      rewrite !vassocr.
      rewrite runitor_rwhisker.
      rewrite lunitor_runitor_identity.
      rewrite lwhisker_vcomp.
      rewrite runitor_rinvunitor.
      rewrite lwhisker_id2.
      apply idpath.
  Qed.

  Definition locally_groupoid_duality_involution
    : duality_involution op_locally_groupoid
    := locally_groupoid_duality_involution_data
       ,,
       locally_groupoid_duality_involution_laws.
End DualityInvolutionLocallyGroupoidal.
