(* ******************************************************************************* *)
(** * Bifinal object in a bicategory
    Niccolò Veltri, Niels van der Weide
    April 2019
    Marco Maggesi,
    July 2019
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.EquivToAdjequiv.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.catiso.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Definition isweq_isinj
           {A B : UU}
           {f : A → B}
           (Hf : isweq f)
  : ∏ {x y : A}, f x = f y → x = y.
Proof.
  intros x y p.
  pose (ff := make_weq f Hf).
  refine (!_ @ maponpaths (invmap ff) p @ _).
  - exact (homotinvweqweq ff x).
  - exact (homotinvweqweq ff y).
Defined.

Section Final.
  Context {C : bicat}.
  Variable (C_is_univalent_2_1 : is_univalent_2_1 C).

  Definition is_bifinal (X : C) : UU
    := ∏ (Y : C),
       @left_adjoint_equivalence
         bicat_of_cats
         _ _
         (functor_to_unit (univ_hom C_is_univalent_2_1 Y X)).

  Definition BiFinal : UU := ∑ (X : C), is_bifinal X.

  Definition has_bifinal : hProp := ∥ BiFinal ∥.

  Definition isaprop_is_bifinal (X : C) : isaprop (is_bifinal X).
  Proof.
    use impred.
    intros Y.
    apply isaprop_left_adjoint_equivalence.
    exact univalent_cat_is_univalent_2_1.
  Qed.

  Definition bifinal_1cell_property (X : C) : UU
    := ∏ (Y : C), Y --> X.

  Definition bifinal_1cell
             {X : C}
             (HX : is_bifinal X)
    : bifinal_1cell_property X
    := λ Y, (left_adjoint_right_adjoint (HX Y) : functor _ _) tt.

  Definition bifinal_2cell_property
             (X Y : C)
    : UU
    := ∏ (f g : Y --> X), invertible_2cell f g.

  Definition bifinal_2cell
             {X : C}
             (HX : is_bifinal X)
             {Y : C}
    : bifinal_2cell_property X Y.
  Proof.
    intros f g.
    pose (L := functor_to_unit (univ_hom C_is_univalent_2_1 Y X)).
    pose (R := (left_adjoint_right_adjoint (HX Y) : functor _ _)).
    pose (θ₁ := iso_to_inv2cell
                  _ _
                  (CompositesAndInverses.nat_iso_to_pointwise_iso
                     (invertible_2cell_to_nat_iso
                        _ _
                        (left_equivalence_unit_iso (HX Y)))
                     f)).
    pose (θ₃ := iso_to_inv2cell
                  _ _
                  (CompositesAndInverses.nat_iso_to_pointwise_iso
                     (invertible_2cell_to_nat_iso
                        _ _
                        (inv_of_invertible_2cell
                           (left_equivalence_unit_iso (HX Y))))
                     g)).
    pose (θ₂ := iso_to_inv2cell
                  _ _
                  (functor_on_iso R (idtoiso (idpath _ : L f = L g)))).
    exact (comp_of_invertible_2cell θ₁ (comp_of_invertible_2cell θ₂ θ₃)).
  Defined.

  Definition bifinal_eq_property (X Y : C) : UU
    := ∏ (f g : Y --> X) (α β : f ==> g), α = β.

  Definition bifinal_eq
             {X : C}
             (HX : is_bifinal X)
             {Y : C}
    : bifinal_eq_property X Y.
  Proof.
    intros f g α β.
    pose (L := functor_to_unit (univ_hom C_is_univalent_2_1 Y X)).
    pose (R := (left_adjoint_right_adjoint (HX Y) : functor _ _)).
    pose (pr1 (left_adjoint_equivalence_to_is_catiso _ (HX Y))) as HL.
    pose (pr1 (left_adjoint_equivalence_to_is_catiso
                 _
                 (@inv_adjequiv bicat_of_cats _ _ (_ ,, HX Y))))
      as HR.
    refine (isweq_isinj (HL _ _) (isweq_isinj (HR _ _) _)).
    apply idpath.
  Qed.

  Definition is_bifinal'
             (X : C)
    := bifinal_1cell_property X ×
       ∏ (Y : C), bifinal_2cell_property X Y ×
                  bifinal_eq_property X Y.

  Definition make_is_bifinal' (X : C)
             (H1 : bifinal_1cell_property X)
             (H2 : ∏ Y : C, bifinal_2cell_property X Y)
             (H3 : ∏ Y : C, bifinal_eq_property X Y)
    : is_bifinal' X.
  Proof.
    refine (H1,, _).
    intro Y.
    - exact (H2 Y,, H3 Y).
  Defined.

  Definition is_bifinal_to_is_bifinal'
             (X : C)
    : is_bifinal X → is_bifinal' X.
  Proof.
    intros HX.
    repeat split.
    - exact (bifinal_1cell HX).
    - exact (bifinal_2cell HX).
    - exact (bifinal_eq HX).
  Defined.

  Definition bifinal_inv_data
             {X : C}
             (HX : is_bifinal' X)
    : ∏ (Y : C),
      functor_data
        unit_category
        (univ_hom C_is_univalent_2_1 Y X).
  Proof.
    intros Y.
    use make_functor_data.
    - intro.
      exact (pr1 HX Y).
    - intros ; simpl.
      exact (id₂ _).
  Defined.

  Definition bifinal_inv_is_functor
             {X : C}
             (HX : is_bifinal' X)
    : ∏ (Y : C),
      is_functor (bifinal_inv_data HX Y).
  Proof.
    intros Y.
    split ; simpl.
    - intro.
      reflexivity.
    - intros ? ? ? ? ?.
      cbn.
      rewrite id2_left.
      reflexivity.
  Qed.

  Definition bifinal_inv
             {X : C}
             (HX : is_bifinal' X)
    : ∏ (Y : C),
      unit_category ⟶ univ_hom C_is_univalent_2_1 Y X.
  Proof.
    intros Y.
    use make_functor.
    - exact (bifinal_inv_data HX Y).
    - exact (bifinal_inv_is_functor HX Y).
  Defined.

  Definition is_bifinal'_1cell_property
             {X : C}
             (HX : is_bifinal' X)
    : bifinal_1cell_property X := pr1 HX.

  Definition is_bifinal'_2cell_property
             {X : C}
             (HX : is_bifinal' X)
             (Y : C)
    : bifinal_2cell_property X Y := pr1 (pr2 HX Y).

  Definition is_bifinal'_eq_property
             {X : C}
             (HX : is_bifinal' X)
             (Y : C)
    : bifinal_eq_property X Y := pr2 (pr2 HX Y).

  Definition bifinal_inv_unit_data
             {X : C}
             (HX : is_bifinal' X)
             (Y : C)
    : nat_trans_data
        (functor_identity (hom Y X))
        (functor_composite
           (functor_to_unit (hom Y X))
           (bifinal_inv HX Y)).
  Proof.
    intros f.
    simpl.
    exact (is_bifinal'_2cell_property HX Y f (is_bifinal'_1cell_property HX Y)).
  Defined.

  Definition bifinal_inv_unit_is_nat_trans
             {X : C}
             (HX : is_bifinal' X)
             (Y : C)
    : is_nat_trans _ _ (bifinal_inv_unit_data HX Y).
  Proof.
    intros f g α.
    simpl in * ; cbn.
    rewrite id2_right.
    apply (is_bifinal'_eq_property HX Y).
  Qed.

  Definition bifinal_inv_unit
             {X : C}
             (HX : is_bifinal' X)
             (Y : C)
    : (functor_identity (hom Y X))
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
             {X : C}
             (HX : is_bifinal' X)
             (Y : C)
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
             {X : C}
             (HX : is_bifinal' X)
             (Y : C)
    : is_nat_trans _ _ (bifinal_inv_counit_data HX Y).
  Proof.
    intros f g α.
    apply isasetunit.
  Qed.

  Definition bifinal_inv_counit
             {X : C}
             (HX : is_bifinal' X)
             (Y : C)
    : (functor_composite
         (bifinal_inv HX Y)
         (functor_to_unit (hom Y X)))
        ⟹
        (functor_identity _).
  Proof.
    use make_nat_trans.
    - exact (bifinal_inv_counit_data HX Y).
    - exact (bifinal_inv_counit_is_nat_trans HX Y).
  Defined.

  Definition is_bifinal'_to_is_bifinal
             (X : C)
    : is_bifinal' X → is_bifinal X.
  Proof.
    intros HX Y.
    use equiv_to_adjequiv.
    use tpair.
    - use tpair.
      + exact (bifinal_inv HX Y).
      + split.
        * exact (bifinal_inv_unit HX Y).
        * exact (bifinal_inv_counit HX Y).
    - split.
      + apply is_nat_iso_to_is_invertible_2cell.
        intro g.
        cbn in * ; unfold bifinal_inv_unit_data.
        apply inv2cell_to_iso.
      + apply is_nat_iso_to_is_invertible_2cell.
        intro g.
        cbn.
        apply path_univalent_groupoid.
  Defined.

  Definition isaprop_bifinal_2cell_property
             {X Y : C}
             (H : bifinal_eq_property X Y)
    : isaprop (bifinal_2cell_property X Y).
  Proof.
    apply impred ; intro f.
    apply impred ; intro g.
    apply isaproptotal2.
    - intro.
      apply isaprop_is_invertible_2cell.
    - intros α β Hα Hβ.
      apply H.
  Qed.

  Definition isaprop_bifinal_eq_property
             (X Y : C)
    : isaprop (bifinal_eq_property X Y).
  Proof.
    repeat (apply impred ; intro).
    apply C.
  Qed.

  Definition isaprop_is_bifinal'
             (X : C)
    : isaprop (is_bifinal' X).
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
    apply (isotoid_2_1 C_is_univalent_2_1).
    apply Hf.
  Qed.
End Final.

Definition make_is_bifinal
           {C : bicat}
           (C_is_univalent_2_1 : is_univalent_2_1 C)
           (X : C)
           (HX₁ : bifinal_1cell_property X)
           (HX₂ : ∏ (Y : C), bifinal_2cell_property X Y)
           (HX₃ : ∏ (Y : C), bifinal_eq_property X Y)
  : is_bifinal C_is_univalent_2_1 X.
Proof.
  apply is_bifinal'_to_is_bifinal.
  exact (HX₁ ,, λ Y, (HX₂ Y ,, HX₃ Y)).
Defined.

Lemma isofhlevel_unit n : isofhlevel n unit.
  apply isofhlevelcontr.
  exact iscontrunit.
Qed.

Definition isofhleve_unit n : isofhlevel n unit
  := isofhlevelcontr n iscontrunit.

Definition unit_1_type : one_types
  := (unit,, isofhleve_unit 3).

Definition bifinal_1_types
  : is_bifinal one_types_is_univalent_2_1 unit_1_type.
Proof.
  use make_is_bifinal.
  - intros X.
    exact tounit.
  - intros Y f g.
    use make_invertible_2cell.
    + intros z.
      apply isapropunit.
    + apply one_type_2cell_iso.
  - intros Y f g α β.
    cbn in *.
    apply funextsec ; intro z.
    unfold homotsec in α,β.
    apply isasetunit.
Defined.

Lemma nat_trans_to_unit_eq {X : category} (F G : X ⟶ unit_category) (α β : F ⟹ G) : α = β.
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro z. apply isasetunit.
Qed.

Definition bifinal_cats
  : is_bifinal univalent_cat_is_univalent_2_1 unit_category.
Proof.
  use make_is_bifinal.
  - intros C.
    apply functor_to_unit.
  - intro Y.
    change (∏ f g : (Y:univalent_category) ⟶ unit_category,
                    invertible_2cell (C := bicat_of_cats) f g).
    intros F G.
    use make_invertible_2cell.
    + use make_nat_trans.
      * unfold nat_trans_data.
        intro z.
        apply isapropunit.
      * unfold is_nat_trans.
        intros.
        apply isasetunit.
    + use make_is_invertible_2cell.
      * use make_nat_trans.
        ** intro z. apply isapropunit.
        ** unfold is_nat_trans.
           intros. apply isasetunit.
      * apply nat_trans_to_unit_eq.
      * apply nat_trans_to_unit_eq.
  - intros Y f g α β.
    apply nat_trans_to_unit_eq.
Defined.

(** ** Bifinal object is unique. *)

Section Uniqueness.

Variable (C : bicat) (HC : is_univalent_2 C).

Definition HC0 : is_univalent_2_0 C := pr1 HC.
Definition HC1 : is_univalent_2_1 C := pr2 HC.

Variable (X : C) (HX : is_bifinal HC1 X).
Variable (Y : C) (HY : is_bifinal HC1 Y).

Definition bifinal_unique_adj_unit
  : id₁ X ==> bifinal_1cell HC1 HY X · bifinal_1cell HC1 HX Y
  := bifinal_2cell HC1 HX
                   (id₁ X)
                   (bifinal_1cell HC1 HY X · bifinal_1cell HC1 HX Y).

Definition bifinal_unique_adj_counit
  : bifinal_1cell HC1 HX Y · bifinal_1cell HC1 HY X ==> id₁ Y
  := bifinal_2cell HC1 HY
                   (bifinal_1cell HC1 HX Y · bifinal_1cell HC1 HY X)
                   (id₁ Y).

Definition bifinal_unique_adj_data
  : left_adjoint_data (bifinal_1cell HC1 HY X)
  := (bifinal_1cell HC1 HX Y,,
      bifinal_unique_adj_unit,,
      bifinal_unique_adj_counit).

Lemma bifinal_unique_left_eqv
  : left_equivalence_axioms bifinal_unique_adj_data.
Proof.
  apply make_dirprod; apply property_from_invertible_2cell.
Qed.

Definition bifinal_unique_adj_eqv
  : left_adjoint_equivalence (bifinal_1cell HC1 HY X).
Proof.
  apply equiv_to_isadjequiv.
  unfold left_equivalence.
  exact (bifinal_unique_adj_data,, bifinal_unique_left_eqv).
Defined.

Definition bifinal_unique : X = Y
  := isotoid_2_0 HC0 ((bifinal_1cell HC1 HY X),, bifinal_unique_adj_eqv).

End Uniqueness.
