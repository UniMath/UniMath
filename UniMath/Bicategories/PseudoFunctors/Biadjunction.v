(* ******************************************************************************* *)
(** Biadjunctions between bicategories.
    The biadjunctions are incoherent and do not necessarily satisfy the swallowtail equations.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Definition left_biadj_unit_counit
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
  := ∑ (R : psfunctor B₂ B₁),
     (pstrans
       (ps_id_functor B₁)
       (ps_comp R L))
     ×
     (pstrans
        (ps_comp L R)
        (ps_id_functor B₂)).

Section BiadjunctionProjections.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}.
  Variable (R : left_biadj_unit_counit L).

  Definition biadj_right_adjoint
    : psfunctor B₂ B₁
    := pr1 R.

  Definition biadj_unit
    : pstrans
        (ps_id_functor B₁)
        (ps_comp biadj_right_adjoint L)
    := pr12 R.

  Definition biadj_counit
    : pstrans
        (ps_comp L biadj_right_adjoint)
        (ps_id_functor B₂)
    := pr22 R.
End BiadjunctionProjections.

Coercion biadj_right_adjoint : left_biadj_unit_counit >-> psfunctor.

Section BiadjunctionTriangleLaws.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}.
  Variable (R : left_biadj_unit_counit L).

  Local Notation "'η'" := (biadj_unit R).
  Local Notation "'ε'" := (biadj_counit R).

  Definition biadj_triangle_l_lhs
    : pstrans L L
    := comp_trans
         (pstrans_rinvunitor L)
         (comp_trans
            (L ◅ η)
            (comp_trans
               (pstrans_lassociator L R L)
               (comp_trans
                  (ε ▻ L)
                  (pstrans_lunitor L)))).

  Definition biadj_triangle_l_law
    : UU
    := invertible_modification
         biadj_triangle_l_lhs
         (id_trans L).

  Definition biadj_triangle_r_lhs
    : pstrans R R
    := comp_trans
         (pstrans_linvunitor R)
         (comp_trans
            (η ▻ R)
            (comp_trans
               (pstrans_rassociator R L R)
                    (comp_trans
                       (R ◅ ε)
                       (pstrans_runitor R)))).

  Definition biadj_triangle_r_law
    : UU
    := invertible_modification
         biadj_triangle_r_lhs
         (id_trans R).
End BiadjunctionTriangleLaws.

Definition left_biadj_data
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
  : UU
  := ∑ (R : left_biadj_unit_counit L),
     biadj_triangle_l_law R × biadj_triangle_r_law R.

Section BiadjunctionDataProjections.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}.
  Variable (R : left_biadj_data L).

  Definition left_biadj_data_to_left_biadj_unit_counit
    : left_biadj_unit_counit L
    := pr1 R.

  Definition biadj_triangle_l
    : invertible_modification
        (biadj_triangle_l_lhs (pr1 R))
        (id_trans L)
    := pr12 R.

  Definition biadj_triangle_r
    : invertible_modification
        (biadj_triangle_r_lhs (pr1 R))
        (id_trans (pr1 R))
    := pr22 R.
End BiadjunctionDataProjections.

Coercion left_biadj_data_to_left_biadj_unit_counit
  : left_biadj_data >-> left_biadj_unit_counit.

Definition make_biadj_unit_counit
           {B₁ B₂ : bicat}
           {L : psfunctor B₁ B₂}
           (R : psfunctor B₂ B₁)
           (η : pstrans
                  (ps_id_functor B₁)
                  (ps_comp R L))
           (ε : pstrans
                  (ps_comp L R)
                  (ps_id_functor B₂))
  : left_biadj_unit_counit L
  := R ,, η ,, ε.

Definition make_biadj_data
           {B₁ B₂ : bicat}
           {L : psfunctor B₁ B₂}
           (R : left_biadj_unit_counit L)
           (tl : biadj_triangle_l_law R)
           (tr : biadj_triangle_r_law R)
  : left_biadj_data L
  := R ,, (tl ,, tr).

(** Biadjunctions give equivalences on hom categories *)
Section BiadjunctionHom.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L)
          (X : B₁) (Y : B₂).

  Local Notation "'η'" := (biadj_unit R).
  Local Notation "'ε'" := (biadj_counit R).

  Local Definition biadj_left_hom_data
    : functor_data (hom X (R Y)) (hom (L X) Y).
  Proof.
    use make_functor_data.
    - cbn ; intro f.
      exact (#L f · ε Y).
    - cbn ; intros f g α.
      exact ((##L α) ▹ ε Y).
  Defined.

  Local Definition biadj_left_hom_is_functor
    : is_functor biadj_left_hom_data.
  Proof.
    split.
    - intros f.
      cbn in f ; cbn.
      rewrite psfunctor_id2, id2_rwhisker.
      apply idpath.
    - intros f g h α β.
      cbn in f, g, h, α, β ; cbn.
      rewrite rwhisker_vcomp, psfunctor_vcomp.
      apply idpath.
  Qed.

  Definition biadj_left_hom
    : hom X (R Y) ⟶ hom (L X) Y.
  Proof.
    use make_functor.
    - exact biadj_left_hom_data.
    - exact biadj_left_hom_is_functor.
  Defined.

  Definition biadj_right_hom_data
    : functor_data (hom (L X) Y) (hom X (R Y)).
  Proof.
    use make_functor_data.
    - cbn ; intro f.
      exact (η X · #R f).
    - cbn ; intros f g α.
      exact (η X ◃ ##R α).
  Defined.

  Definition biadj_right_hom_is_functor
    : is_functor biadj_right_hom_data.
  Proof.
    split.
    - intros f.
      cbn in f ; cbn.
      rewrite psfunctor_id2, lwhisker_id2.
      apply idpath.
    - intros f g h α β.
      cbn in f, g, h, α, β ; cbn.
      rewrite psfunctor_vcomp, lwhisker_vcomp.
      apply idpath.
  Qed.

  Definition biadj_right_hom
    : hom (L X) Y ⟶ hom X (R Y).
  Proof.
    use make_functor.
    - exact biadj_right_hom_data.
    - exact biadj_right_hom_is_functor.
  Defined.

  Definition biadj_hom_left_right_data
    : nat_trans_data
        (functor_identity (hom X (R Y)))
        (biadj_left_hom ∙ biadj_right_hom).
  Proof.
    intros f.
    cbn in f ; cbn.
    exact ((rinvunitor f)
             • (f ◃ (((invertible_modcomponent_of (biadj_triangle_r R) Y)^-1)
                       • lunitor _
                       • (_ ◃ (lunitor _ • runitor _))))
             • lassociator _ _ _
             • ((psnaturality_of η f)^-1 ▹ _)
             • rassociator _ _ _
             • (_ ◃ psfunctor_comp R (#L f) (ε Y))).
  Defined.

  Definition biadj_hom_left_right_is_nat_trans
    : is_nat_trans _ _ biadj_hom_left_right_data.
  Proof.
    intros f g α.
    cbn in f, g, α ; cbn.
    unfold biadj_hom_left_right_data ; simpl.
    etrans.
    {
      rewrite !vassocr.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      apply idpath.
    }
    rewrite !vassocl.
    do 2 apply maponpaths.
    etrans.
    {
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    apply maponpaths.
    rewrite lwhisker_vcomp.
    rewrite psfunctor_rwhisker.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !vassocl.
    rewrite rwhisker_lwhisker_rassociator.
    rewrite !vassocr.
    apply maponpaths_2.
    use vcomp_move_L_pM.
    { is_iso. }
    simpl.
    rewrite !vassocr.
    use vcomp_move_R_Mp.
    { is_iso. }
    simpl.
    rewrite !rwhisker_vcomp.
    apply maponpaths.
    exact (!(psnaturality_natural η _ _ f g α)).
  Qed.

  Definition biadj_hom_left_right
    : (functor_identity (hom X (R Y)))
        ⟹
        biadj_left_hom ∙ biadj_right_hom.
  Proof.
    use make_nat_trans.
    - exact biadj_hom_left_right_data.
    - exact biadj_hom_left_right_is_nat_trans.
  Defined.

  Definition biadj_hom_right_left_data
    : nat_trans_data
        (biadj_right_hom ∙ biadj_left_hom)
        (functor_identity (hom (L X) Y)).
  Proof.
    intros f.
    cbn in f ; cbn.
    exact (((psfunctor_comp L (η X) (#R f))^-1 ▹ (ε Y))
             • rassociator _ _ _
             • (#L (η X) ◃ (psnaturality_of ε f)^-1)
             • lassociator _ _ _
             • (((_ ◃ (rinvunitor _ • linvunitor _))
                   • linvunitor _
                   • (invertible_modcomponent_of (biadj_triangle_l R) X)) ▹ f)
             • lunitor f).
  Defined.

  Definition biadj_hom_right_left_is_nat_trans
    : is_nat_trans _ _ biadj_hom_right_left_data.
  Proof.
    intros f g α.
    cbn in f, g, α ; cbn.
    unfold biadj_hom_right_left_data.
    simpl.
    refine (!_).
    etrans.
    {
      rewrite !vassocl.
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!(vcomp_lunitor f _ α)).
      }
      rewrite !vassocr.
      rewrite vcomp_whisker.
      apply idpath.
    }
    rewrite !vassocr.
    do 2 apply maponpaths_2.
    rewrite !vassocl.
    rewrite <- lwhisker_lwhisker.
    rewrite !vassocr.
    apply maponpaths_2.
    use vcomp_move_L_Mp.
    { is_iso. }
    simpl.
    rewrite !vassocl.
    use vcomp_move_R_pM.
    { is_iso. }
    simpl.
    rewrite !lwhisker_vcomp.
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (psnaturality_natural ε _ _ _ _ α).
      }
      rewrite !vassocr.
      rewrite vcomp_linv, id2_left.
      apply idpath.
    }
    rewrite rwhisker_lwhisker_rassociator.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite !rwhisker_vcomp.
    apply maponpaths.
    refine (!_).
    rewrite psfunctor_lwhisker.
    rewrite !vassocl.
    rewrite vcomp_rinv, id2_right.
    apply idpath.
  Qed.

  Definition biadj_hom_right_left
    : (biadj_right_hom ∙ biadj_left_hom)
        ⟹
        (functor_identity (hom (L X) Y)).
  Proof.
    use make_nat_trans.
    - exact biadj_hom_right_left_data.
    - exact biadj_hom_right_left_is_nat_trans.
  Defined.

  Definition biadj_hom_equivalence
    : equivalence_of_precats (hom X (R Y)) (hom (L X) Y).
  Proof.
    use tpair.
    - use tpair.
      + exact biadj_left_hom.
      + use tpair.
        * exact biadj_right_hom.
        * split.
          ** exact biadj_hom_left_right.
          ** exact biadj_hom_right_left.
    - split ; simpl.
      + intro a.
        apply is_inv2cell_to_is_iso.
        unfold biadj_hom_left_right_data.
        is_iso.
        apply (psfunctor_comp R).
      + intro a.
        apply is_inv2cell_to_is_iso.
        unfold biadj_hom_right_left_data.
        is_iso.
        apply (invertible_modcomponent_of (biadj_triangle_l R)).
  Defined.

  Definition biadj_hom_equiv
    : adj_equivalence_of_precats biadj_left_hom.
  Proof.
    refine (@adjointificiation
              (make_category (hom X (R Y)) _)
              (make_category (hom (L X) Y) _)
              biadj_hom_equivalence).
    - intros x y.
      apply B₁.
    - intros x y.
      apply B₂.
  Defined.
End BiadjunctionHom.

(** Biadjunctions preserve unique maps *)
Section BiadjunctionUniqueMaps.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L)
          (H₂ : is_univalent_2_1 B₂)
          (X : B₁) (HX : unique_maps X).

  Definition biadj_preserves_unique_maps
    : is_biinitial H₂ (L X).
  Proof.
    intros Y.
    unfold is_biinitial in *.
    use equiv_to_adjequiv.
    use iso_equiv.
    - exact ((pr11 (biadj_hom_equiv R X Y))
               ∙ functor_to_unit (hom X (R Y))).
    - pose (comp_adj_equivalence_of_precats
              (adj_equivalence_of_precats_inv (biadj_hom_equiv R X Y))
              (HX (R Y))) as A.
      exact (@adj_equivalence_to_left_equivalence
               (univ_hom H₂ (L X) Y)
               unit_category
               _ A).
    - use make_nat_trans.
      + exact (λ _, idpath _).
      + intros f g α.
        apply isapropunit.
    - apply is_nat_iso_to_is_invertible_2cell.
      intros f.
      use is_iso_qinv ; cbn.
      + apply idpath.
      + split ; apply idpath.
  Defined.
End BiadjunctionUniqueMaps.

(** Biadjunctions preserve biinitial objects. *)
Section BiadjunctionInitial.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L)
          (H₁ : is_univalent_2_1 B₁)
          (H₂ : is_univalent_2_1 B₂)
          (X : B₁) (HX : is_biinitial H₁ X).

  Definition biadj_preserves_biinitial
    : is_biinitial H₂ (L X).
  Proof.
    apply biadj_preserves_unique_maps.
    - exact R.
    - use biinitial_to_unique_maps.
      + exact H₁.
      + apply HX.
  Defined.
End BiadjunctionInitial.
