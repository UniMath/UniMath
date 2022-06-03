(* ******************************************************************************* *)
(** * Biinitial object in a bicategory
    Niccolò Veltri, Niels van der Weide
    April 2019
    Marco Maggesi,
    July 2019

   Contents:
   1. Definition of biinitial objects
   2. Representable definition of biinitial objects
   3. Equivalence between the two definitions
   4. Bicategories with biinitial objects
   5. Biinitial objects are unique
   6. Biinitial objects are closed under equivalence
   7. Strict biinitial objects
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Section Initial.
  Context {B : bicat}.

  (**
   1. Definition of biinitial objects
   *)
  Definition biinitial_1cell_property (X : B) : UU
    := ∏ (Y : B), X --> Y.

  Definition biinitial_2cell_property
             (X Y : B)
    : UU
    := ∏ (f g : X --> Y), f ==> g.

  Definition biinitial_eq_property (X Y : B) : UU
    := ∏ (f g : X --> Y) (α β : f ==> g), α = β.

  Definition is_biinitial
             (X : B)
    := biinitial_1cell_property X
       ×
       ∏ (Y : B), biinitial_2cell_property X Y
                  ×
                  biinitial_eq_property X Y.

  Definition is_biinitial_1cell_property
             {X : B}
             (HX : is_biinitial X)
    : biinitial_1cell_property X
    := pr1 HX.

  Definition is_biinitial_2cell_property
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : biinitial_2cell_property X Y
    := pr1 (pr2 HX Y).

  Definition is_biinitial_eq_property
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : biinitial_eq_property X Y
    := pr2 (pr2 HX Y).

  Definition is_biinitial_invertible_2cell_property
             {X : B}
             (HX : is_biinitial X)
             {Y : B}
             (f g : X --> Y)
    : invertible_2cell f g.
  Proof.
    use make_invertible_2cell.
    - apply (is_biinitial_2cell_property HX Y).
    - use make_is_invertible_2cell.
      + apply (is_biinitial_2cell_property HX Y).
      + apply (is_biinitial_eq_property HX Y).
      + apply (is_biinitial_eq_property HX Y).
  Defined.

  Definition make_is_biinitial
             (X : B)
             (H1 : biinitial_1cell_property X)
             (H2 : ∏ (Y : B), biinitial_2cell_property X Y)
             (H3 : ∏ (Y : B), biinitial_eq_property X Y)
    : is_biinitial X.
  Proof.
    refine (H1,, _).
    intro Y.
    exact (H2 Y,, H3 Y).
  Defined.

  Definition isaprop_biinitial_2cell_property
             {X Y : B}
             (H : biinitial_eq_property X Y)
    : isaprop (biinitial_2cell_property X Y).
  Proof.
    apply impred ; intro f.
    apply impred ; intro g.
    use invproofirrelevance.
    intros α β.
    apply H.
  Qed.

  Definition isaprop_biinitial_eq_property
             (X Y : B)
    : isaprop (biinitial_eq_property X Y).
  Proof.
    repeat (apply impred ; intro).
    apply cellset_property.
  Qed.

  Definition isaprop_is_biinitial
             (H : is_univalent_2_1 B)
             (X : B)
    : isaprop (is_biinitial X).
  Proof.
    apply invproofirrelevance.
    intros x y.
    induction x as [f Hf].
    induction y as [g Hg].
    use subtypePath.
    - intro ; simpl.
      apply impred ; intro Y.
      apply isapropdirprod.
      + apply isaprop_biinitial_2cell_property.
        apply Hf.
      + apply isaprop_biinitial_eq_property.
    - simpl.
    apply funextsec ; intro Y.
    apply (isotoid_2_1 H).
    apply (is_biinitial_invertible_2cell_property (f ,, Hf)).
  Qed.

  (** 2. Representable definition of biinitial objects *)
  Definition is_biinitial_repr (X : B) : UU
    := ∏ (Y : B),
       adj_equivalence_of_cats (functor_to_unit (hom X Y)).

  Definition isaprop_is_biinitial_repr
             (H : is_univalent_2_1 B)
             (X : B)
    : isaprop (is_biinitial_repr X).
  Proof.
    use impred.
    intros Y.
    use (isofhlevelweqf
             _
             (adj_equiv_is_equiv_cat (functor_to_unit (univ_hom H X Y)))).
    apply isaprop_left_adjoint_equivalence.
    exact univalent_cat_is_univalent_2_1.
  Qed.

  (**
   3. Equivalence between the two definitions
   *)
  Definition biinitial_repr_1cell
             {X : B}
             (HX : is_biinitial_repr X)
    : biinitial_1cell_property X
    := λ Y, right_adjoint (HX Y) tt.

  Definition biinitial_repr_2cell
             {X : B}
             (HX : is_biinitial_repr X)
             {Y : B}
    : biinitial_2cell_property X Y.
  Proof.
    intros f g.
    pose (L := functor_to_unit (hom Y X)).
    pose (R := right_adjoint (HX Y)).
    pose (η := unit_nat_z_iso_from_adj_equivalence_of_cats (HX Y)).
    pose (θ₁ := z_iso_to_inv2cell (nat_z_iso_pointwise_z_iso η f)).
    pose (θ₂ := z_iso_to_inv2cell (nat_z_iso_pointwise_z_iso η g)).
    exact (comp_of_invertible_2cell θ₁ (inv_of_invertible_2cell θ₂)).
  Defined.

  Definition biinitial_repr_eq
             {X : B}
             (HX : is_biinitial_repr X)
             {Y : B}
    : biinitial_eq_property X Y.
  Proof.
    intros f g α β.
    pose (L := functor_to_unit (hom Y X)).
    pose (R := right_adjoint (HX Y)).
    pose (η := unit_nat_z_iso_from_adj_equivalence_of_cats (HX Y)).
    pose (θ₁ := z_iso_to_inv2cell (nat_z_iso_pointwise_z_iso η f)).
    pose (θ₂ := z_iso_to_inv2cell (nat_z_iso_pointwise_z_iso η g)).
    use (invmaponpathsincl
           _
           (isinclweq
              _ _ _
              (fully_faithful_from_equivalence _ _ _ (HX Y) _ _))).
    apply idpath.
  Qed.

  Definition is_biinitial_repr_to_is_biinitial
             {X : B}
             (HX : is_biinitial_repr X)
    : is_biinitial X.
  Proof.
    repeat split.
    - exact (biinitial_repr_1cell HX).
    - exact (biinitial_repr_2cell HX).
    - exact (biinitial_repr_eq HX).
  Defined.

  Definition biinitial_inv_data
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : functor_data unit_category (hom X Y).
  Proof.
    use make_functor_data.
    - exact (λ _, is_biinitial_1cell_property HX Y).
    - exact (λ _ _ _, id₂ _).
  Defined.

  Definition biinitial_inv_is_functor
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : is_functor (biinitial_inv_data HX Y).
  Proof.
    split.
    - intro ; intros.
      apply idpath.
    - intro ; intros.
      cbn.
      rewrite id2_left.
      apply idpath.
  Qed.

  Definition biinitial_inv
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : unit_category ⟶ hom X Y.
  Proof.
    use make_functor.
    - exact (biinitial_inv_data HX Y).
    - exact (biinitial_inv_is_functor HX Y).
  Defined.

  Definition biinitial_inv_unit_data
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : nat_trans_data
        (functor_identity (hom X Y))
        (functor_composite
           (functor_to_unit (hom X Y))
           (biinitial_inv HX Y))
    := λ f, is_biinitial_2cell_property HX Y f (is_biinitial_1cell_property HX Y).

  Definition biinitial_inv_unit_is_nat_trans
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : is_nat_trans _ _ (biinitial_inv_unit_data HX Y).
  Proof.
    intros f g α.
    simpl in * ; cbn.
    rewrite id2_right.
    apply (is_biinitial_eq_property HX Y).
  Qed.

  Definition biinitial_inv_unit
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : (functor_identity (hom X Y))
        ⟹
        functor_composite
        (functor_to_unit (hom X Y))
        (biinitial_inv HX Y).
  Proof.
    use make_nat_trans.
    - exact (biinitial_inv_unit_data HX Y).
    - exact (biinitial_inv_unit_is_nat_trans HX Y).
  Defined.

  Definition biinitial_inv_counit_data
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : nat_trans_data
        (functor_composite
           (biinitial_inv HX Y)
           (functor_to_unit (hom X Y)))
        (functor_identity _).
  Proof.
    intros f.
    apply isapropunit.
  Defined.

  Definition biinitial_inv_counit_is_nat_trans
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : is_nat_trans _ _ (biinitial_inv_counit_data HX Y).
  Proof.
    intros f g α.
    apply isasetunit.
  Qed.

  Definition biinitial_inv_counit
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : (functor_composite
         (biinitial_inv HX Y)
         (functor_to_unit (hom X Y)))
        ⟹
        (functor_identity _).
  Proof.
    use make_nat_trans.
    - exact (biinitial_inv_counit_data HX Y).
    - exact (biinitial_inv_counit_is_nat_trans HX Y).
  Defined.

  Definition is_biinitial_to_is_biinitial_repr_help
             {X : B}
             (HX : is_biinitial X)
             (Y : B)
    : equivalence_of_cats (hom X Y) unit_category.
  Proof.
    simple refine ((_ ,, (_ ,, (_ ,, _))) ,, (_ ,, _)).
    - exact (functor_to_unit _).
    - exact (biinitial_inv HX Y).
    - exact (biinitial_inv_unit HX Y).
    - exact (biinitial_inv_counit HX Y).
    - intros f.
      cbn ; unfold biinitial_inv_unit_data.
      apply is_inv2cell_to_is_z_iso.
      apply is_biinitial_invertible_2cell_property.
    - intro g.
      cbn.
      apply path_univalent_groupoid.
  Defined.

  Definition is_biinitial_to_is_biinitial_repr
             {X : B}
             (HX : is_biinitial X)
    : is_biinitial_repr X.
  Proof.
    intros Y.
    exact (adjointificiation (is_biinitial_to_is_biinitial_repr_help HX Y)).
  Defined.

  Definition is_biinitial_weq_is_biinitial_repr
             (H : is_univalent_2_1 B)
             (X : B)
    : is_biinitial X ≃ is_biinitial_repr X.
  Proof.
    use weqimplimpl.
    - exact is_biinitial_to_is_biinitial_repr.
    - exact is_biinitial_repr_to_is_biinitial.
    - exact (isaprop_is_biinitial H X).
    - exact (isaprop_is_biinitial_repr H X).
  Defined.
End Initial.

(**
 4. Bicategories with biinitial objects
 *)
Definition biinitial_obj (B : bicat) : UU
  := ∑ (X : B), is_biinitial X.

Definition has_biinitial (B : bicat) : UU := ∥ biinitial_obj B ∥.

Definition bicat_with_biinitial
  : UU
  := ∑ (B : bicat), biinitial_obj B.

Coercion bicat_with_biinitial_to_bicat
         (B : bicat_with_biinitial)
  : bicat
  := pr1 B.

Definition biinitial_of
           (B : bicat_with_biinitial)
  : biinitial_obj B
  := pr2 B.

(**
 5. Biinitial objects are unique
 *)
Section Uniqueness.
  Context {B : bicat}
          (HB : is_univalent_2 B)
          {X : B} (HX : is_biinitial X)
          {Y : B} (HY : is_biinitial Y).

  Let HC0 : is_univalent_2_0 B := pr1 HB.
  Let HC1 : is_univalent_2_1 B := pr2 HB.

  Definition biinitial_unique_adj_unit
    : id₁ Y
      ==>
      is_biinitial_1cell_property HY X · is_biinitial_1cell_property HX Y
    := is_biinitial_2cell_property HY _ _ _.

  Definition biinitial_unique_adj_counit
    : is_biinitial_1cell_property HX Y · is_biinitial_1cell_property HY X
      ==>
      id₁ X
    := is_biinitial_2cell_property HX _ _ _.

  Definition biinitial_unique_adj_data
    : left_adjoint_data (is_biinitial_1cell_property HY X)
    := is_biinitial_1cell_property HX Y
       ,,
       biinitial_unique_adj_unit
       ,,
       biinitial_unique_adj_counit.

  Lemma biinitial_unique_left_eqv
    : left_equivalence_axioms biinitial_unique_adj_data.
  Proof.
    split.
    - apply is_biinitial_invertible_2cell_property.
    - apply is_biinitial_invertible_2cell_property.
  Qed.

  Definition biinitial_unique_adj_eqv
    : left_adjoint_equivalence (is_biinitial_1cell_property HY X).
  Proof.
    apply equiv_to_isadjequiv.
    unfold left_equivalence.
    exact (biinitial_unique_adj_data ,, biinitial_unique_left_eqv).
  Defined.

  Definition biinitial_unique : Y = X
    := isotoid_2_0 HC0 (_ ,, biinitial_unique_adj_eqv).
End Uniqueness.

(**
 6. Biinitial objects are closed under equivalence
 *)
Section EquivToBiinitial.
  Context {B : bicat}
          {X Y : B}
          (HX : is_biinitial X)
          {l : X --> Y}
          (Hl : left_adjoint_equivalence l).

  Let r : Y --> X
    := left_adjoint_right_adjoint Hl.
  Let ε : invertible_2cell (r · l) (id₁ Y)
    := left_equivalence_counit_iso Hl.

  Definition equiv_from_biinitial
    : is_biinitial Y.
  Proof.
    use make_is_biinitial.
    - exact (λ Z, r · is_biinitial_1cell_property HX Z).
    - exact (λ Z f g,
             linvunitor _
             • (ε^-1 ▹ f)
             • rassociator _ _ _
             • (r ◃ is_biinitial_2cell_property HX _ (l · f) (l · g))
             • lassociator _ _ _
             • (ε ▹ g)
             • lunitor _).
    - abstract
        (intros Z f g α β ;
         use (vcomp_lcancel (lunitor _)) ; [ is_iso | ] ;
         rewrite <- !vcomp_lunitor ;
         apply maponpaths_2 ;
         use (vcomp_lcancel (ε ▹ f)) ; [ is_iso ; apply property_from_invertible_2cell | ] ;
         rewrite !vcomp_whisker ;
         apply maponpaths_2 ;
         use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ] ;
         rewrite <- !lwhisker_lwhisker ;
         apply maponpaths_2 ;
         apply maponpaths ;
         apply (is_biinitial_eq_property HX)).
  Defined.
End EquivToBiinitial.

Definition equiv_to_biinitial
           {B : bicat}
           {X Y : B}
           (HX : is_biinitial X)
           {l : Y --> X}
           (Hl : left_adjoint_equivalence l)
  : is_biinitial Y
  := equiv_from_biinitial HX (inv_adjequiv (l ,, Hl)).

(**
 7. Strict biinitial objects
 *)
Definition biinitial_is_strict_biinitial_obj
           {B : bicat}
           {X : B}
           (HX : is_biinitial X)
  : UU
  := ∏ (Y : B) (f : Y --> X), left_adjoint_equivalence f.

Definition is_strict_biinitial_obj
           {B : bicat}
           (X : B)
  : UU
  := ∑ (HX : is_biinitial X), biinitial_is_strict_biinitial_obj HX.

Definition strict_biinitial_obj
           (B : bicat)
  : UU
  := ∑ (X : B), is_strict_biinitial_obj X.

Definition bicat_with_strict_biinitial
  : UU
  := ∑ (B : bicat), strict_biinitial_obj B.

Coercion bicat_with_strict_biinitial_to_bicat
         (B : bicat_with_strict_biinitial)
  : bicat
  := pr1 B.

Definition strict_biinitial_of
           (B : bicat_with_strict_biinitial)
  : strict_biinitial_obj B
  := pr2 B.

Definition map_to_strict_biinitial_is_biinitial
           {B : bicat}
           {X Y : B}
           (HX : is_strict_biinitial_obj X)
           (f : Y --> X)
  : is_biinitial Y
  := equiv_to_biinitial (pr1 HX) (pr2 HX _ f).
