(***********************************************************************************

 Duality involutions of bicategories

 In this file, we define the notion of duality involutions. Duality involutions
 generalize the opposite category. More specifically, we have a pseudofunctor going
 from `Cat^co` to `Cat` sending every category `C` to its opposite category. Since
 taking the opposite twice gives the identity of categories, this pseudofunctor is
 actually a biequivalence. For categories enriched over a symmetric monoidal
 category, we also have an opposite category construction which satisfies similar
 properties.

 The data of a duality involution consists of:
 - A pseudonatural equivalence, which is the unit of the biequivalence. This is
   formalized by two pseudonatural transformations and two invertible modifcation.
   This gives rise to an adjoint equivalence in the category of pseudofunctors, which
   is shown in [left_adjoint_equivalance_duality_unit].
 - An invertible modification that witnesses the triangle equality.
 The laws of a duality involution witness the so-called swallowtail equations for
 biadjunctions.

 Our definition of duality involutions is slightly different compared to the
 literature. Usually, one would express the triangle law via an invertible
 modification (see [duality_triangle_modification]). However, the naturality
 condition of this modification is rather complicated: it is filled with
 several associators and unitors ([is_modification_duality_triangle_lem]). Instead
 we give a simplified version of this naturality condition ([duality_triangle_law]).
 This condition is easier to use and easier to prove, and it is strong enough to
 deduce that the triangle law actually is an invertible modification, which we prove
 in the statement [duality_triangle_modification]).

 References
 - Michael Shulman, Contravariance through Enrichment
   Definition 2.1
   https://arxiv.org/pdf/1606.05058

 Contents
 1. Data of duality involutions
 2. Counit of duality involution
 3. Laws of duality involutions
 4. Duality involutions
 5. Accessors for the laws of duality involutions

 ***********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.UnivalenceOp.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Op2OfPseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.

Local Open Scope cat.

(** * 1. Data of duality involutions *)
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

  Definition triangle_data_of_duality_inv
             (x : op2_bicat B)
    : invertible_2cell
        (ηinv (L x))
        (#L (ηinv x)).
  Proof.
    refine (comp_of_invertible_2cell
              (rinvunitor_invertible_2cell _)
              _).
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell
                 _
                 (psfunctor_id L _))
              _).
    refine (comp_of_invertible_2cell
              _
              (lunitor_invertible_2cell _)).
    refine (comp_of_invertible_2cell
              _
              (rwhisker_of_invertible_2cell
                 _
                 (invertible_modcomponent_of
                    unit_inv_unit_of_duality
                    (L x)))).
    refine (comp_of_invertible_2cell
              _
              (lassociator_invertible_2cell _ _ _)).
    refine (lwhisker_of_invertible_2cell _ _).
    refine (comp_of_invertible_2cell
              _
              (rwhisker_of_invertible_2cell
                 _
                 (inv_of_invertible_2cell (triangle_data_of_duality x)))).
    refine (comp_of_invertible_2cell
              _
              (inv_of_invertible_2cell (psfunctor_comp L _ _))).
    use psfunctor_inv2cell.
    use make_invertible_2cell.
    - exact (inv_of_invertible_2cell
               (invertible_modcomponent_of unit_unit_inv_of_duality x)).
    - use to_op2_is_invertible_2cell.
      apply property_from_invertible_2cell.
  Defined.
End Projections.

(** * 2. Counit of duality involution *)
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

  Definition left_adjoint_equivalance_duality_unit_pointwise
             (x : B)
    : left_adjoint_equivalence (η x)
    := pointwise_adjequiv _ left_adjoint_equivalance_duality_unit x.

  Definition left_adjoint_equivalance_duality_unit_inv
    : left_adjoint_equivalence ηinv
    := inv_left_adjoint_equivalence left_adjoint_equivalance_duality_unit.

  Definition left_adjoint_equivalance_duality_unit_inv_pointwise
             (x : B)
    : left_adjoint_equivalence (ηinv x)
    := pointwise_adjequiv _ left_adjoint_equivalance_duality_unit_inv x.

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

(** * 3. Laws of duality involutions *)
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
    : UU
    := ∏ (x : B),
       duality_coherency_lhs x
       =
       duality_coherency_rhs x.

  Definition duality_triangle_law_lhs
             {x y : B}
             (f : x --> y)
    : η (L x) · #L(#L(#L f)) ==> #L(η x · #L(#L f))
    := (t x ▹ #L (#L (#L f)))
       • psfunctor_comp L (η x) (#L (#L f)).

  Definition duality_triangle_law_rhs
             {x y : B}
             (f : x --> y)
    : η (L x) · #L(#L(#L f)) ==> #L(η x · #L(#L f))
    := psnaturality_of η (# L f)
       • (#L f ◃ t y)
       • psfunctor_comp L f (η y)
       • ##L (psnaturality_of η f).

  Definition duality_triangle_law
    : UU
    := ∏ (x y : B)
         (f : x --> y),
       duality_triangle_law_lhs f = duality_triangle_law_rhs f.

  Definition duality_involution_laws
    : UU
    := duality_coherency
       ×
       duality_triangle_law.
End LawsDualityInvolution.

(** * 4. Duality involutions *)
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

(** * 5. Accessors for the laws of duality involutions *)
Section Accessors.
  Context {B : bicat}
          {L : psfunctor (op2_bicat B) B}
          (d : duality_involution L).

  Let R : psfunctor B (op2_bicat B)
    := op2_psfunctor L.

  Let η := unit_of_duality d.
  Let ηinv := unit_inv_of_duality d.
  Let ηηinv := unit_unit_inv_of_duality d.
  Let ηinvη := unit_inv_unit_of_duality d.
  Let t := triangle_data_of_duality d.

  Proposition duality_to_duality_coherency
    : duality_coherency d.
  Proof.
    exact (pr12 d).
  Qed.

  Proposition duality_to_triangle_law
              {x y : B}
              (f : x --> y)
    : (t x ▹ #L (#L (#L f)))
       • psfunctor_comp L (η x) (#L (#L f))
       =
       psnaturality_of η (# L f)
       • (#L f ◃ t y)
       • psfunctor_comp L f (η y)
       • ##L (psnaturality_of η f).
  Proof.
    exact (pr22 d x y f).
  Qed.

  Let εinv := duality_counit_inv d.

  Definition duality_triangle_modification_data
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


  Lemma is_modification_duality_triangle_lem
        {x y : B}
        (f : x --> y)
    : ((((rassociator (id₁ (L x)) (η (L x)) (#L (#L (#L f)))
      • (id₁ (L x) ◃ psnaturality_of η (# L f)))
      • lassociator (id₁ (L x)) (#L f) (η (L y)))
      • ((lunitor (#L f) • rinvunitor (#L f)) ▹ η (L y)))
      • rassociator ((pr211 L) x y f) (id₁ (L y)) (η (L y)))
      • (#L f ◃ (lunitor (unit_of_duality d (L y))
                 • (t y
                 • (linvunitor (#L (η y))
                 • rinvunitor (id₁ (L y) · #L(η y))))))
      =
      ((lunitor (η (L x))
        • (t x
        • (linvunitor (#L (η x))
        • rinvunitor (id₁ (L x) · # L (η x))))) ▹ #L (#L (#L f)))
      • ((((rassociator (id₁ (L x) · #L (η x)) (id₁ (L (L (L x)))) (#L (#L (#L f)))
      • (id₁ (L x) · # L(η x) ◃ (lunitor (#L (#L (#L f))) • rinvunitor (#L (#L (#L f))))))
      • lassociator (id₁ (L x) · # L (η x)) (#L (#L (#L f))) (id₁ (L (L (L y)))))
      • (((((rassociator (id₁ (L x)) (#L (η x)) (#L (#L (#L f)))
      • (id₁ (L x) ◃ ((psfunctor_comp L (η x) (#L (#L f))
                      • ##L ((psnaturality_of η f) ^-1))
                      • (psfunctor_comp L f (η y)) ^-1)))
      • lassociator (id₁ (L x)) (#L f) (#L (η y)))
      • ((lunitor (#L f) • rinvunitor (#L f)) ▹ #L (η y)))
      • rassociator (#L f) (id₁ (L y)) (#L (η y))) ▹ id₁ (L (L (L y)))))
      • rassociator (#L f) (id₁ (L y) · # L (η y)) (id₁ (L (L (L y))))).
  Proof.
    rewrite !vassocl.
    etrans.
    {
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      do 3 apply maponpaths_2.
      rewrite !vassocl.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocl.
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      apply idpath.
    }
    etrans.
    {
      rewrite !vassocr.
      rewrite <- lunitor_triangle.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      rewrite id2_left.
      rewrite !vassocl.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    etrans.
    {
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite lunitor_lwhisker.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite rinvunitor_runitor.
        rewrite id2_rwhisker.
        rewrite id2_left.
        rewrite rinvunitor_triangle.
        do 6 apply maponpaths_2.
        rewrite rwhisker_hcomp.
        rewrite <- rinvunitor_natural.
        apply idpath.
      }
      etrans.
      {
        rewrite !vassocl.
        do 2 apply maponpaths.
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite !rwhisker_vcomp.
        rewrite rwhisker_hcomp.
        rewrite <- rinvunitor_natural.
        rewrite !vassocl.
        apply idpath.
      }
      rewrite !vassocl.
      rewrite <- left_unit_inv_assoc.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    etrans.
    {
      rewrite !vassocl.
      do 8 apply maponpaths.
      rewrite rwhisker_hcomp.
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    etrans.
    {
      rewrite lunitor_triangle.
      do 3 apply maponpaths.
      rewrite !vassocr.
      rewrite !lwhisker_vcomp.
      rewrite vcomp_lunitor.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      do 3 apply maponpaths_2.
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
    }
    rewrite id2_left.
    rewrite !vassocr.
    use vcomp_move_R_Mp ; [ is_iso | ].
    use vcomp_move_R_Mp.
    {
      use (psfunctor_is_iso L (make_invertible_2cell _)).
      use to_op2_is_invertible_2cell.
      apply (inv_of_invertible_2cell (psnaturality_of (unit_of_duality d) f)).
    }
    exact (duality_to_triangle_law f).
  Qed.

  Unset Kernel Term Sharing.

  Proposition is_modification_duality_triangle
    : is_modification duality_triangle_modification_data.
  Proof.
    intros x y f.
    simpl.
    refine (_ @ is_modification_duality_triangle_lem f @ _).
    - apply idpath.
    - apply idpath.
  Qed.

  Definition duality_triangle_modification
    : invertible_modification
        (linvunitor_pstrans _
         · right_whisker L η)
        (rinvunitor_pstrans _
         · left_whisker L εinv
         · lassociator_pstrans _ _ _).
  Proof.
    use make_invertible_modification.
    - exact duality_triangle_modification_data.
    - exact is_modification_duality_triangle.
  Defined.
End Accessors.
