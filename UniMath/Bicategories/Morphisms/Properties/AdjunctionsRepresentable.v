(*******************************************************************************

 Representable definitions of adjunctions/adjoint equivalence

 We look at representable versions of adjunctions and adjoint equivalences.

 The first thing we notice, is that every adjunction in a bicategory gives rise
 to an adjunction on the hom-categories. However, note that in general, we do
 not get an adjunction from an adjunction on the hom-categories.

 For adjoint equivalences, the situation is different: for those, the two
 definitions are actually equivalent.

 Contents
 1. Every adjunction gives rise to an adjunction on the hom-categories
 2. Representable definition of adjoint equivalences
 3. Adjoint equivalence to homwise adjoint equivalence
 4. Homwise adjoint equivalence to adjoint equivalence
 5. The two definitions are equivalent

 *******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.

Local Open Scope cat.


Definition left_adjoint_repr
           {B : bicat}
           {x y : B}
           (l : x --> y)
  : UU
  := ∏ (w : B), is_left_adjoint (post_comp w l).

Section LeftAdjointToLeftAdjointRepr.
  Context {B : bicat}
          {x y : B}
          (l : x --> y)
          (Hl : left_adjoint l).

  Let r : y --> x := left_adjoint_right_adjoint Hl.
  Let η : id₁ _ ==> l · r := left_adjoint_unit Hl.
  Let ε : r · l ==> id₁ _ := left_adjoint_counit Hl.

  Section AdjointRepr.
    Context (w : B).

    Definition left_adjoint_to_repr_unit
      : functor_identity _
        ⟹
        post_comp w l ∙ post_comp w r.
    Proof.
      use make_nat_trans.
      - exact (λ f, rinvunitor _ • (f ◃ η) • lassociator _ _ _).
      - abstract
          (intros f₁ f₂ τ ; cbn ;
           rewrite !vassocl ;
           rewrite rwhisker_rwhisker ;
           rewrite !vassocr ;
           rewrite rinvunitor_natural ;
           rewrite <- rwhisker_hcomp ;
           apply maponpaths_2 ;
           rewrite !vassocl ;
           rewrite vcomp_whisker ;
           apply idpath).
    Defined.

    Definition left_adjoint_to_repr_counit
      : post_comp w r ∙ post_comp w l
        ⟹
        functor_identity _.
    Proof.
      use make_nat_trans.
      - exact (λ f, rassociator _ _ _ • (f ◃ ε) • runitor _).
      - abstract
          (intros f₁ f₂ τ ; cbn ;
           rewrite !vassocr ;
           rewrite rwhisker_rwhisker_alt ;
           rewrite !vassocl ;
           rewrite <- vcomp_runitor ;
           apply maponpaths ;
           rewrite !vassocr ;
           rewrite vcomp_whisker ;
           apply idpath).
    Defined.
  End AdjointRepr.

  Definition left_adjoint_to_left_adjoint_repr_form_adjunction
             (w : B)
    : form_adjunction
        (post_comp w l)
        (post_comp w r)
        (left_adjoint_to_repr_unit w)
        (left_adjoint_to_repr_counit w).
  Proof.
    split.
    - intro f ; cbn.
      rewrite !vassocl.
      refine (_ @ lwhisker_id2 _ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (!(internal_triangle1 Hl)).
      }
      rewrite <- runitor_triangle.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- rassociator_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite lassociator_rassociator.
      rewrite id2_right.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp, lwhisker_hcomp.
      rewrite triangle_r_inv.
      apply idpath.
    - intro f ; cbn.
      rewrite !vassocl.
      refine (_ @ lwhisker_id2 _ _).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (!(internal_triangle2 Hl)).
      }
      rewrite <- rinvunitor_triangle.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- lassociator_lassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite lassociator_rassociator.
      rewrite id2_left.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      refine (!_).
      apply runitor_rwhisker.
  Qed.

  Definition left_adjoint_to_left_adjoint_repr_are_adjoints
             (w : B)
    : are_adjoints (post_comp w l) (post_comp w r).
  Proof.
    use make_are_adjoints.
    - exact (left_adjoint_to_repr_unit w).
    - exact (left_adjoint_to_repr_counit w).
    - exact (left_adjoint_to_left_adjoint_repr_form_adjunction w).
  Defined.

  Definition left_adjoint_to_left_adjoint_repr
    : left_adjoint_repr l
    := λ w,
       post_comp w r
       ,,
       left_adjoint_to_left_adjoint_repr_are_adjoints w.

  Definition left_adjoint_to_adjunction_cat
             (w : B)
             (HB_2_1 : is_univalent_2_1 B)
    : @adjunction bicat_of_univ_cats (univ_hom HB_2_1 w x) (univ_hom HB_2_1 w y).
  Proof.
    refine (post_comp w l
            ,,
            ((post_comp w r
            ,,
            (left_adjoint_to_repr_unit w
            ,,
            left_adjoint_to_repr_counit w))
            ,,
            (_ ,, _))).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         cbn ;
         intro ;
         rewrite !id2_right, id2_left ;
         apply left_adjoint_to_left_adjoint_repr_form_adjunction).
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         cbn ;
         intro ;
         rewrite !id2_right, id2_left ;
         apply left_adjoint_to_left_adjoint_repr_form_adjunction).
  Defined.
End LeftAdjointToLeftAdjointRepr.

(**
 2. Representable definition of adjoint equivalences
 *)
Definition left_adjoint_equivalence_repr
           {B : bicat}
           {x y : B}
           (l : x --> y)
  : UU
  := ∏ (w : B), adj_equivalence_of_cats (post_comp w l).

Definition isaprop_left_adjoint_equivalence_repr
           {B : bicat}
           (HB_2_1 : is_univalent_2_1 B)
           {x y : B}
           (l : x --> y)
  : isaprop (left_adjoint_equivalence_repr l).
Proof.
  use impred ; intro w.
  use isofhlevelweqf.
  - exact (@left_adjoint_equivalence
             bicat_of_univ_cats
             (univ_hom HB_2_1 _ _)
             (univ_hom HB_2_1 _ _)
             (post_comp w l)).
  - exact (@adj_equiv_is_equiv_cat
             (univ_hom HB_2_1 _ _)
             _
             _).
  - apply isaprop_left_adjoint_equivalence.
    exact univalent_cat_is_univalent_2_1.
Qed.

(**
 3. Adjoint equivalence to homwise adjoint equivalence
 *)
Section LeftAdjointToLeftAdjointRepr.
  Context {B : bicat}
          {x y : B}
          (l : x --> y)
          (Hl : left_adjoint_equivalence l).

  Let r : y --> x := left_adjoint_right_adjoint Hl.
  Let η : invertible_2cell (id₁ _) (l · r) := left_equivalence_unit_iso Hl.
  Let ε : invertible_2cell (r · l) (id₁ _) := left_equivalence_counit_iso Hl.

  Section ToEquivalence.
    Context (w : B).

    Let L : hom w x ⟶ hom w y := post_comp w l.
    Let R : hom w y ⟶ hom w x := post_comp w r.

    Definition left_adjequiv_to_left_adjequiv_repr_equiv
      : equivalence_of_cats (hom w x) (hom w y).
    Proof.
      use make_equivalence_of_cats.
      - use make_adjunction_data.
        + exact L.
        + exact R.
        + apply left_adjoint_to_repr_unit.
        + apply left_adjoint_to_repr_counit.
      - split.
        + intro f.
          apply is_inv2cell_to_is_z_iso ; cbn.
          is_iso.
          exact (pr2 (left_equivalence_unit_iso Hl)).
        + intro f.
          apply is_inv2cell_to_is_z_iso ; cbn.
          is_iso.
          exact (pr2 (left_equivalence_counit_iso Hl)).
    Defined.
  End ToEquivalence.

  Definition left_adjequiv_to_left_adjequiv_repr
    : left_adjoint_equivalence_repr l
    := λ w, adjointificiation (left_adjequiv_to_left_adjequiv_repr_equiv w).
End LeftAdjointToLeftAdjointRepr.

(**
 4. Homwise adjoint equivalence to adjoint equivalence
 *)
Section LeftAdjointReprToLeftAdjoint.
  Context {B : bicat}
          {x y : B}
          (l : x --> y)
          (Hl : left_adjoint_equivalence_repr l).

  Let r : y --> x := right_adjoint (Hl y) (id₁ y).
  Let η : invertible_2cell (r · l) (id₁ y)
    := nat_z_iso_pointwise_z_iso
         (counit_nat_z_iso_from_adj_equivalence_of_cats
            (Hl y))
         (id₁ y).

  Definition left_adjoint_repr_to_left_adjoint_counit
    : invertible_2cell (l · r) (id₁ x).
  Proof.
    apply z_iso_to_inv2cell.
    pose ((nat_z_iso_pointwise_z_iso
                       (unit_nat_z_iso_from_adj_equivalence_of_cats
                          (Hl x))
                       (id₁ x))).
    cbn in z.
    refine (z_iso_comp
              (nat_z_iso_pointwise_z_iso
                 (unit_nat_z_iso_from_adj_equivalence_of_cats
                    (Hl x))
                 (l · r))
              (z_iso_comp
                 (functor_on_z_iso
                    (right_adjoint (Hl x))
                    _)
                 (z_iso_inv
                    (nat_z_iso_pointwise_z_iso
                       (unit_nat_z_iso_from_adj_equivalence_of_cats
                          (Hl x))
                       (id₁ x))))).
   cbn.
   apply inv2cell_to_z_iso.
   exact (comp_of_invertible_2cell
            (rassociator_invertible_2cell _ _ _)
            (comp_of_invertible_2cell
               (lwhisker_of_invertible_2cell _ η)
               (comp_of_invertible_2cell
                  (runitor_invertible_2cell _)
                  (linvunitor_invertible_2cell _)))).
  Defined.

  Definition left_adjoint_repr_to_left_adjoint_data
    : left_adjoint_data l
    := r ,, (left_adjoint_repr_to_left_adjoint_counit^-1 ,, pr1 η).

  Definition left_adjoint_repr_to_left_adjoint_axioms
    : left_equivalence_axioms left_adjoint_repr_to_left_adjoint_data.
  Proof.
    simple refine (_ ,, _).
    - apply is_invertible_2cell_inv.
    - exact (pr2 η).
  Defined.

  Definition left_adjoint_repr_to_left_adjoint_equivalence
    : left_adjoint_equivalence l
    := equiv_to_adjequiv
         _
         (left_adjoint_repr_to_left_adjoint_data
          ,,
          left_adjoint_repr_to_left_adjoint_axioms).
End LeftAdjointReprToLeftAdjoint.

(**
 5. The two definitions are equivalent
 *)
Definition left_adjoint_equivalence_weq_left_adjoint_equivalence_repr
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {x y : B}
           (l : x --> y)
  : left_adjoint_equivalence_repr l ≃ left_adjoint_equivalence l.
Proof.
  use weqimplimpl.
  - exact (left_adjoint_repr_to_left_adjoint_equivalence l).
  - exact (left_adjequiv_to_left_adjequiv_repr l).
  - apply isaprop_left_adjoint_equivalence_repr.
    exact HB.
  - apply isaprop_left_adjoint_equivalence.
    exact HB.
Defined.
