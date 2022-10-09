(**
Author: Niels van der Weide

Suppose, we have a set `X` with a binary operation `f : X → X → X`.
Since init elments for `f` are unique, the type of unit elements of `f` is a proposition.

This means we have two ways of defining a univalent category of sets with a unital binary operations:
1. We define it as a full subcategory of the category of sets with a binary operation
2. We use algebras of the signature describing sets with a binary operation and a unit, which satisfy the necessary axioms.
Note that in the first category the morphismms are all functions between sets which preserve the binary relation, while the morphisms in the second category must preserve the unit element as well.
As a consequence, the forgetful is full and faithful in the first construction, while in the second it is only faithful.

On the nLab, there are definitions which describe when functors forget properties and when functors forget stuff.
https://ncatlab.org/nlab/show/stuff%2C+structure%2C+property#definitions
With this terminology, we can argue why the first approach adds the unit as a property while in the second approach it is added as structure.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.binproducts.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.

Local Open Scope cat.

(**
Let us start by defining sets with a binary operation on them.
To do so, we use algebras on the diagonal functor.
Let us repeat the diagonal.
After that, we show we have a univalent category of sets with a binary operation.
 *)
Definition diag
  : HSET ⟶ HSET.
Proof.
  exact (bindelta_functor HSET ∙ binproduct_functor BinProductsHSET).
Defined.

Definition binop_category
  : category.
Proof.
  simple refine (FunctorAlg diag).
Defined.

Definition is_univalent_binop
  : is_univalent binop_category.
Proof.
  exact (is_univalent_FunctorAlg is_univalent_HSET diag).
Defined.

Definition binop
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact binop_category.
  - exact is_univalent_binop.
Defined.

(**
In the remainder, we need some projections.
 *)
Section ProjectionsBinop.
  Variable (m : binop).

  Definition carrier
    : hSet
    := pr1 m.

  Definition operation
    : carrier → carrier → carrier
    := λ x y, pr2 m (x ,, y).
End ProjectionsBinop.

(**
Now we look at two ways of defining a category of sets with a binary operation and a unit.
The first way, is by using the full subcategory.
This gives rise to a univalent category since unit elements are unique.
 *)
Definition is_unit
           (m : binop)
           (e : carrier m)
  : UU
  := (∏ (x : carrier m), operation m x e = x)
     ×
     (∏ (x : carrier m), operation m e x = x).

Definition has_unit
           (m : binop)
  : UU
  := ∑ (e : carrier m), is_unit m e.

Definition isaprop_has_unit
           (m : binop)
  : isaprop (has_unit m).
Proof.
  use invproofirrelevance.
  intros e₁ e₂.
  use subtypePath.
  { intro ; apply isapropdirprod ; use impred ; intro ; apply setproperty. }
  exact (!(pr22 e₂ (pr1 e₁)) @ pr12 e₁ (pr1 e₂)).
Defined.

Definition unit_binop_property_disp_cat
  : disp_cat binop
  := disp_full_sub binop has_unit.

Definition unit_binop_property_cat
  : category
  := total_category unit_binop_property_disp_cat.

Definition is_univalent_property_unit_binop
  : is_univalent unit_binop_property_cat.
Proof.
  use is_univalent_total_category.
  - exact is_univalent_binop.
  - use disp_full_sub_univalent.
    exact isaprop_has_unit.
Defined.

Definition unit_binop_property
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact unit_binop_property_cat.
  - exact is_univalent_property_unit_binop.
Defined.

(**
To argue that the unit element is really added as a property, we look at the forgetful functor to sets with binary operations.
This functor only forgets the unit and, since the unit was added as a property, it is full and faithful.
Note that in this displayed category:
- the displayed objects form a proposition
- the displayed morphisms are contractible
 *)
Definition forget_unit_property_adds_properties
  : adds_properties unit_binop_property_disp_cat.
Proof.
  apply pr1_category_fully_faithful.
  intro ; intros.
  apply iscontrunit.
Defined.

(**
Next we show how to define sets with a binary operation and a unit where the unit is added as structure.
To do so, we use displayed categories.
To prove univalence of the total category, we use displayed univalence.
 *)
Definition point_disp_cat_ob_mor
  : disp_cat_ob_mor binop.
Proof.
  use make_disp_cat_ob_mor ; cbn.
  - exact (λ X, carrier X).
  - exact (λ X Y x y f, pr1 f x = y).
Defined.

Definition point_disp_cat_id_comp
  : disp_cat_id_comp binop point_disp_cat_ob_mor.
Proof.
  use tpair.
  - exact (λ _ _, idpath _).
  - exact (λ X Y Z f g x y z p q, maponpaths (pr1 g) p @ q).
Defined.

Definition point_disp_cat_data
  : disp_cat_data binop.
Proof.
  use tpair.
  - exact point_disp_cat_ob_mor.
  - exact point_disp_cat_id_comp.
Defined.

Definition point_disp_cat_laws
  : disp_cat_axioms binop point_disp_cat_data.
Proof.
  repeat split.
  - cbn ; intros ; apply setproperty.
  - cbn ; intros ; apply setproperty.
  - cbn ; intros ; apply setproperty.
  - cbn ; intros.
    apply isasetaprop.
    apply setproperty.
Qed.

Definition point_disp_cat
  : disp_cat binop.
Proof.
  use tpair.
  - exact point_disp_cat_data.
  - exact point_disp_cat_laws.
Defined.

Definition point_disp_cat_disp_univalent
  : is_univalent_disp point_disp_cat.
Proof.
  use is_univalent_disp_from_fibers.
  intros X x y.
  use isweq_iso.
  - intros f.
    exact (pr1 f).
  - intros e.
    induction e ; cbn.
    apply idpath.
  - intros e.
    use subtypePath.
    { intro ; apply isaprop_is_z_iso_disp. }
    cbn.
    induction (pr1 e).
    apply idpath.
Defined.

Definition pointed_binop_category
  : category
  := total_category point_disp_cat.

Definition pointed_binop
  : univalent_category.
Proof.
  simple refine (_ ,, _).
  - exact pointed_binop_category.
  - refine (is_univalent_total_category
              _
              point_disp_cat_disp_univalent).
    exact is_univalent_binop.
Defined.

(**
Some projections of sets with a binary operation and a point.
 *)
Section ProjectionsPointedBinop.
  Variable (m : pointed_binop).

  Definition pointed_carrier
    : hSet
    := pr11 m.

  Definition pointed_operation
    : pointed_carrier → pointed_carrier → pointed_carrier
    := λ x y, pr21 m (x ,, y).

  Definition point_of
    : pointed_carrier
    := pr2 m.
End ProjectionsPointedBinop.

(**
Up to now, we only added the element which represents the unit.
Beside that, we also need to add the necessary laws.
 *)
Definition is_unit_point
  : pointed_binop → UU
  := λ X, is_unit (pr1 X) (pr2 X).

Definition isaprop_is_unit_point
           (X : pointed_binop)
  : isaprop (is_unit_point X).
Proof.
  use isapropdirprod ; use impred ; intro ; apply setproperty.
Defined.

Definition unit_binop_structure_disp_cat
  : disp_cat binop
  := sigma_disp_cat (disp_full_sub pointed_binop is_unit_point).

Definition unit_binop_structure_cat
  : category
  := total_category unit_binop_structure_disp_cat.

Definition is_univalent_structure_unit_binop
  : is_univalent unit_binop_structure_cat.
Proof.
  use is_univalent_total_category.
  - apply binop.
  - apply is_univalent_disp_from_fibers.
    intros x xx yy.
    use isweqimplimpl.
    + intros f.
      use subtypePath.
      {
        intro ; apply isapropdirprod ; use impred ; intro ; apply setproperty.
      }
      exact (pr11 f).
    + apply isapropifcontr.
      apply isaprop_has_unit.
    + use invproofirrelevance.
      intros f g.
      use subtypePath.
      { intro ; apply isaprop_is_z_iso_disp. }
      use subtypePath.
      { intro ; apply isapropunit. }
      apply setproperty.
Defined.

Definition unit_binop_structure
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact unit_binop_structure_cat.
  - exact is_univalent_structure_unit_binop.
Defined.

(**
We finish by arguing that the unit is indeed added structure for this construction.
To do so, we prove that the forgetful functor is faithful.
 *)
Definition forget_unit_structure_faithful
  : adds_structure unit_binop_structure_disp_cat.
Proof.
  intros m₁ m₂ f.
  apply pr1_category_faithful.
  intro ; intros ; simpl.
  use (@isaprop_total2 (make_hProp _ _) (λ _, make_hProp _ _)).
  - apply setproperty.
  - apply isapropunit.
Defined.

(**
We can also show that this forgetful functor isn't full.
This is because not every homomorphism between sets with binary operations preserve the unit element.
For that, we use the following example.
 *)
Definition nat_unit_binop_structure
  : unit_binop_structure.
Proof.
  simple refine ((natset ,, _) ,, _ ,, _) ; cbn.
  - exact (λ n, pr1 n + pr2 n).
  - exact 0.
  - split ; cbn.
    + apply natplusr0.
    + apply natplusl0.
Defined.

Definition bool_unit_binop_structure
  : unit_binop_structure.
Proof.
  simple refine ((boolset ,, _) ,, _ ,, _) ; cbn.
  - exact (λ b, orb (pr1 b) (pr2 b)).
  - exact false.
  - split ; cbn ; intro x ; induction x ; apply idpath.
Defined.

Definition nat_to_bool
  : nat → bool
  := λ _, true.

Definition nat_plus_to_bool_or
  : pr1_category _ nat_unit_binop_structure
    -->
    pr1_category _ bool_unit_binop_structure.
Proof.
  refine (nat_to_bool ,, _).
  use funextsec.
  intro x ; apply idpath.
Defined.

Definition unit_binop_structure_disp_cat_not_adds_properties
  : ¬(adds_properties unit_binop_structure_disp_cat).
Proof.
  intros H.
  induction H as [H₁ H₂].
  clear H₂.
  specialize (H₁ _ _ nat_plus_to_bool_or).
  revert H₁.
  use (@hinhuniv _ hfalse).
  intros H ; cbn.
  pose (pr121 H) as p.
  cbn in p.
  pose (eqtohomot (maponpaths pr1 (pr2 H)) 0) as q.
  cbn in q.
  pose (!q @ p) as r.
  unfold nat_to_bool in r.
  exact (nopathstruetofalse r).
Qed.

(**
Now let us look at the hlevels of the displayed objects and morphisms of this displayed category.
More specifically, both the type of displayed objects and the type of displayed morphisms form propositions.
 *)
Definition unit_binop_structure_disp_cat_mor_prop
  : locally_propositional unit_binop_structure_disp_cat.
Proof.
  apply disp_cat_is_locally_propositional.
  apply forget_unit_structure_faithful.
Defined.

Definition unit_binop_structure_disp_cat_mor_not_contr
  : ¬(locally_contractible unit_binop_structure_disp_cat).
Proof.
  intro H.
  apply unit_binop_structure_disp_cat_not_adds_properties.
  apply pr1_category_fully_faithful.
  exact H.
Defined.

Definition unit_binop_structure_disp_cat_ob_prop
           (X : binop)
  : isaprop (unit_binop_structure_disp_cat X).
Proof.
  apply isaprop_has_unit.
Defined.
