(**
 Duality involutions of bicategories

 Contents:
 1. Data of duality involutions
 2. Counit of duality involution
 3. Laws of duality involutions
 4. Duality involutions
 5. Accessors for duality involutions
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

Coercion duality_involution_to_data
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
 5. Accessors for duality involutions
 *)
Section DualityInvolutionAccessors.
  Context {B : bicat}
          (L : psfunctor (op2_bicat B) B)
          (HL : duality_involution L).

  Let R : psfunctor B (op2_bicat B) := op2_psfunctor L.
  Let ε : pstrans (comp_psfunctor R L) (id_psfunctor _) := duality_counit HL.

  Definition duality_transpose
             {x y : B}
             (f : x --> L y)
    : L x --> y
    := #L f · ε y.

  Definition duality_transpose_cell
             {x y : B}
             {f₁ f₂ : x --> L y}
             (τ : f₂ ==> f₁)
    : duality_transpose f₁ ==> duality_transpose f₂
    := ##L τ ▹ ε y.

  Definition duality_transpose_functor_data
             (x y : B)
    : functor_data
        (@hom (op2_bicat B) x (L y))
        (hom (L x) y).
  Proof.
    use make_functor_data.
    - exact duality_transpose.
    - exact (λ _ _ τ, duality_transpose_cell τ).
  Defined.

  Definition duality_transpose_is_functor
             (x y : B)
    : is_functor (duality_transpose_functor_data x y).
  Proof.
    split.
    - intro f ; cbn.
      refine (_ @ id2_rwhisker _ _).
      apply maponpaths.
      apply (psfunctor_id2 L).
    - intros f₁ f₂ f₃ τ₁ τ₂ ; cbn.
      refine (_ @ !(rwhisker_vcomp _ _ _)).
      apply maponpaths.
      apply (psfunctor_vcomp L).
  Qed.

  Definition duality_transpose_functor
             (x y : B)
    : @hom (op2_bicat B) x (L y) ⟶ hom (L x) y.
  Proof.
    use make_functor.
    - exact (duality_transpose_functor_data x y).
    - exact (duality_transpose_is_functor x y).
  Defined.
End DualityInvolutionAccessors.
