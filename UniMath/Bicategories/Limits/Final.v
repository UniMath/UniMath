(* ******************************************************************************* *)
(** * Bifinal object in a bicategory
    Niccolò Veltri, Niels van der Weide
    April 2019
    Marco Maggesi,
    July 2019

   Contents:
   1. Definition of bifinal objects
   2. Representable definition of bifinal objects
   3. Equivalence between the two definitions
   4. Bicategories with bifinal objects
   5. Bifinal objects are unique
   6. Being bifinal is preserved under equivalence
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
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.ContainsAdjEquiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Section Final.
  Context {B : bicat}.

  (**
   1. Definition of bifinal objects
   *)
  Definition bifinal_1cell_property (X : B) : UU
    := ∏ (Y : B), Y --> X.

  Definition bifinal_2cell_property
             (X Y : B)
    : UU
    := ∏ (f g : Y --> X), f ==> g.

  Definition bifinal_eq_property (X Y : B) : UU
    := ∏ (f g : Y --> X) (α β : f ==> g), α = β.

  Definition is_bifinal
             (X : B)
    := bifinal_1cell_property X
       ×
       ∏ (Y : B), bifinal_2cell_property X Y
                  ×
                  bifinal_eq_property X Y.

  Definition is_bifinal_1cell_property
             {X : B}
             (HX : is_bifinal X)
    : bifinal_1cell_property X
    := pr1 HX.

  Definition is_bifinal_2cell_property
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : bifinal_2cell_property X Y
    := pr1 (pr2 HX Y).

  Definition is_bifinal_eq_property
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : bifinal_eq_property X Y
    := pr2 (pr2 HX Y).

  Definition is_bifinal_invertible_2cell_property
             {X : B}
             (HX : is_bifinal X)
             {Y : B}
             (f g : Y --> X)
    : invertible_2cell f g.
  Proof.
    use make_invertible_2cell.
    - apply (is_bifinal_2cell_property HX Y).
    - use make_is_invertible_2cell.
      + apply (is_bifinal_2cell_property HX Y).
      + apply (is_bifinal_eq_property HX Y).
      + apply (is_bifinal_eq_property HX Y).
  Defined.

  Definition make_is_bifinal
             (X : B)
             (H1 : bifinal_1cell_property X)
             (H2 : ∏ (Y : B), bifinal_2cell_property X Y)
             (H3 : ∏ (Y : B), bifinal_eq_property X Y)
    : is_bifinal X.
  Proof.
    refine (H1,, _).
    intro Y.
    exact (H2 Y,, H3 Y).
  Defined.

  Definition isaprop_bifinal_2cell_property
             {X Y : B}
             (H : bifinal_eq_property X Y)
    : isaprop (bifinal_2cell_property X Y).
  Proof.
    apply impred ; intro f.
    apply impred ; intro g.
    use invproofirrelevance.
    intros α β.
    apply H.
  Qed.

  Definition isaprop_bifinal_eq_property
             (X Y : B)
    : isaprop (bifinal_eq_property X Y).
  Proof.
    repeat (apply impred ; intro).
    apply cellset_property.
  Qed.

  Definition isaprop_is_bifinal
             (H : is_univalent_2_1 B)
             (X : B)
    : isaprop (is_bifinal X).
  Proof.
    apply invproofirrelevance.
    intros x y.
    induction x as [f Hf].
    induction y as [g Hg].
    use subtypePath.
    - intro ; simpl.
      apply impred ; intro Y.
      apply isapropdirprod.
      + apply isaprop_bifinal_2cell_property.
        apply Hf.
      + apply isaprop_bifinal_eq_property.
    - simpl.
    apply funextsec ; intro Y.
    apply (isotoid_2_1 H).
    apply (is_bifinal_invertible_2cell_property (f ,, Hf)).
  Qed.

  (** 2. Representable definition of bifinal objects *)
  Definition is_bifinal_repr (X : B) : UU
    := ∏ (Y : B),
       adj_equivalence_of_cats (functor_to_unit (hom Y X)).

  Definition isaprop_is_bifinal_repr
             (H : is_univalent_2_1 B)
             (X : B)
    : isaprop (is_bifinal_repr X).
  Proof.
    use impred.
    intros Y.
    use (isofhlevelweqf
             _
             (adj_equiv_is_equiv_cat (functor_to_unit (univ_hom H Y X)))).
    apply isaprop_left_adjoint_equivalence.
    exact univalent_cat_is_univalent_2_1.
  Qed.

  (**
   3. Equivalence between the two definitions
   *)
  Definition bifinal_repr_1cell
             {X : B}
             (HX : is_bifinal_repr X)
    : bifinal_1cell_property X
    := λ Y, right_adjoint (HX Y) tt.

  Definition bifinal_repr_2cell
             {X : B}
             (HX : is_bifinal_repr X)
             {Y : B}
    : bifinal_2cell_property X Y.
  Proof.
    intros f g.
    pose (L := functor_to_unit (hom Y X)).
    pose (R := right_adjoint (HX Y)).
    pose (η := unit_nat_z_iso_from_adj_equivalence_of_cats (HX Y)).
    pose (θ₁ := z_iso_to_inv2cell (nat_z_iso_pointwise_z_iso η f)).
    pose (θ₂ := z_iso_to_inv2cell (nat_z_iso_pointwise_z_iso η g)).
    exact (comp_of_invertible_2cell θ₁ (inv_of_invertible_2cell θ₂)).
  Defined.

  Definition bifinal_repr_eq
             {X : B}
             (HX : is_bifinal_repr X)
             {Y : B}
    : bifinal_eq_property X Y.
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

  Definition is_bifinal_repr_to_is_bifinal
             {X : B}
             (HX : is_bifinal_repr X)
    : is_bifinal X.
  Proof.
    repeat split.
    - exact (bifinal_repr_1cell HX).
    - exact (bifinal_repr_2cell HX).
    - exact (bifinal_repr_eq HX).
  Defined.

  Definition bifinal_inv_data
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : functor_data unit_category (hom Y X).
  Proof.
    use make_functor_data.
    - exact (λ _, is_bifinal_1cell_property HX Y).
    - exact (λ _ _ _, id₂ _).
  Defined.

  Definition bifinal_inv_is_functor
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : is_functor (bifinal_inv_data HX Y).
  Proof.
    split.
    - intro ; intros.
      apply idpath.
    - intro ; intros.
      cbn.
      rewrite id2_left.
      apply idpath.
  Qed.

  Definition bifinal_inv
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : unit_category ⟶ hom Y X.
  Proof.
    use make_functor.
    - exact (bifinal_inv_data HX Y).
    - exact (bifinal_inv_is_functor HX Y).
  Defined.

  Definition bifinal_inv_unit_data
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : nat_trans_data
        (functor_identity (hom Y X))
        (functor_composite
           (functor_to_unit (hom Y X))
           (bifinal_inv HX Y))
    := λ f, is_bifinal_2cell_property HX Y f (is_bifinal_1cell_property HX Y).

  Definition bifinal_inv_unit_is_nat_trans
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : is_nat_trans _ _ (bifinal_inv_unit_data HX Y).
  Proof.
    intros f g α.
    simpl in * ; cbn.
    rewrite id2_right.
    apply (is_bifinal_eq_property HX Y).
  Qed.

  Definition bifinal_inv_unit
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : functor_identity (hom Y X)
      ⟹
      functor_composite
        (functor_to_unit (hom Y X))
        (bifinal_inv HX Y).
  Proof.
    use make_nat_trans.
    - exact (bifinal_inv_unit_data HX Y).
    - exact (bifinal_inv_unit_is_nat_trans HX Y).
  Defined.

  Definition bifinal_inv_counit_data
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : nat_trans_data
        (functor_composite
           (bifinal_inv HX Y)
           (functor_to_unit (hom Y X)))
        (functor_identity _).
  Proof.
    intros f.
    apply isapropunit.
  Defined.

  Definition bifinal_inv_counit_is_nat_trans
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : is_nat_trans _ _ (bifinal_inv_counit_data HX Y).
  Proof.
    intros f g α.
    apply isasetunit.
  Qed.

  Definition bifinal_inv_counit
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : functor_composite
        (bifinal_inv HX Y)
        (functor_to_unit (hom Y X))
      ⟹
      functor_identity _.
  Proof.
    use make_nat_trans.
    - exact (bifinal_inv_counit_data HX Y).
    - exact (bifinal_inv_counit_is_nat_trans HX Y).
  Defined.

  Definition is_bifinal_to_is_bifinal_repr_help
             {X : B}
             (HX : is_bifinal X)
             (Y : B)
    : equivalence_of_cats (hom Y X) unit_category.
  Proof.
    simple refine ((_ ,, (_ ,, (_ ,, _))) ,, (_ ,, _)).
    - exact (functor_to_unit _).
    - exact (bifinal_inv HX Y).
    - exact (bifinal_inv_unit HX Y).
    - exact (bifinal_inv_counit HX Y).
    - intros f.
      cbn ; unfold bifinal_inv_unit_data.
      apply is_inv2cell_to_is_z_iso.
      apply is_bifinal_invertible_2cell_property.
    - intro g.
      cbn.
      apply path_univalent_groupoid.
  Defined.

  Definition is_bifinal_to_is_bifinal_repr
             {X : B}
             (HX : is_bifinal X)
    : is_bifinal_repr X.
  Proof.
    intros Y.
    exact (adjointificiation (is_bifinal_to_is_bifinal_repr_help HX Y)).
  Defined.

  Definition is_bifinal_weq_is_bifinal_repr
             (H : is_univalent_2_1 B)
             (X : B)
    : is_bifinal X ≃ is_bifinal_repr X.
  Proof.
    use weqimplimpl.
    - exact is_bifinal_to_is_bifinal_repr.
    - exact is_bifinal_repr_to_is_bifinal.
    - exact (isaprop_is_bifinal H X).
    - exact (isaprop_is_bifinal_repr H X).
  Defined.
End Final.

(**
 4. Bicategories with bifinal objects
 *)
Definition bifinal_obj (B : bicat) : UU
  := ∑ (X : B), is_bifinal X.

Definition has_bifinal (B : bicat) : UU := ∥ bifinal_obj B ∥.

(**
 5. Bifinal objects are unique
 *)
Section Uniqueness.
  Context {B : bicat}
          (HB : is_univalent_2 B)
          {X : B} (HX : is_bifinal X)
          {Y : B} (HY : is_bifinal Y).

  Let HC0 : is_univalent_2_0 B := pr1 HB.
  Let HC1 : is_univalent_2_1 B := pr2 HB.

  Definition bifinal_unique_adj_unit
    : id₁ X
      ==>
      is_bifinal_1cell_property HY X · is_bifinal_1cell_property HX Y
    := is_bifinal_2cell_property HX _ _ _.

  Definition bifinal_unique_adj_counit
    : is_bifinal_1cell_property HX Y · is_bifinal_1cell_property HY X
      ==>
      id₁ Y
    := is_bifinal_2cell_property HY _ _ _.

  Definition bifinal_unique_adj_data
    : left_adjoint_data (is_bifinal_1cell_property HY X)
    := is_bifinal_1cell_property HX Y
       ,,
       bifinal_unique_adj_unit
       ,,
       bifinal_unique_adj_counit.

  Lemma bifinal_unique_left_eqv
    : left_equivalence_axioms bifinal_unique_adj_data.
  Proof.
    split.
    - apply is_bifinal_invertible_2cell_property.
    - apply is_bifinal_invertible_2cell_property.
  Qed.

  Definition bifinal_unique_adj_eqv
    : left_adjoint_equivalence (is_bifinal_1cell_property HY X).
  Proof.
    apply equiv_to_isadjequiv.
    unfold left_equivalence.
    exact (bifinal_unique_adj_data ,, bifinal_unique_left_eqv).
  Defined.

  Definition bifinal_unique : X = Y
    := isotoid_2_0 HC0 (_ ,, bifinal_unique_adj_eqv).
End Uniqueness.

(**
 6. Being bifinal is preserved under equivalence
 *)
Section FinalEquivalence.
  Context {B : bicat}
          {x y : B}
          (l : x --> y)
          (Hl : left_adjoint_equivalence l)
          (Hx : is_bifinal x).

  Let r : y --> x
    := left_adjoint_right_adjoint Hl.
  Let η : invertible_2cell (id₁ _) (l · r)
    := left_equivalence_unit_iso Hl.
  Let ε : invertible_2cell (r · l) (id₁ _)
    := left_equivalence_counit_iso Hl.

  Definition is_bifinal_1cell_left_adjoint_equivalence
    : bifinal_1cell_property y
    := λ z, is_bifinal_1cell_property Hx z · l.

  Definition is_bifinal_2cell_left_adjoint_equivalence
             (z : B)
    : bifinal_2cell_property y z
    := λ f g,
       rinvunitor _
       • (_ ◃ ε^-1)
       • lassociator _ _ _
       • (is_bifinal_2cell_property Hx z (f · r) (g · r) ▹ l)
       • rassociator _ _ _
       • (_ ◃ ε)
       • runitor _.

  Definition is_bifinal_eq_left_adjoint_equivalence
             (z : B)
    : bifinal_eq_property y z.
  Proof.
    intros f g α β.
    enough (α ▹ r = β ▹ r) as H.
    {
      use (faithful_1cell_eq_cell
             (pr1 (adj_equiv_fully_faithful (inv_adjequiv (_ ,, Hl))))).
      exact H.
    }
    exact (is_bifinal_eq_property Hx z (f · r) (g · r) (α ▹ r) (β ▹ r)).
  Qed.

  Definition is_bifinal_left_adjoint_equivalence
    : is_bifinal y.
  Proof.
    use make_is_bifinal.
    - exact is_bifinal_1cell_left_adjoint_equivalence.
    - exact is_bifinal_2cell_left_adjoint_equivalence.
    - exact is_bifinal_eq_left_adjoint_equivalence.
  Defined.
End FinalEquivalence.
