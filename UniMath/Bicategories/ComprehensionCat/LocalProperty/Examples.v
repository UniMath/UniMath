(**************************************************************************************

 Examples of local properties

 In this file, we collect various examples of local properties. More specifically, we
 have the following examples.
 - We can take the conjunction of local properties ([local_property_conj]).
 - We can take subproperty of local properties ([sub_local_property]).
 - We have a local property of strict initial objects ([strict_initial_local_property]).
 - We have a local property of binary coproducts that are stable under pullback
   ([stable_bincoproducts_local_property]).
 - We have a local property of being lextensive ([lextensive_local_property]).
 Note: we use local properties in the context of finitely complete categories, so we
 shall tacitly assume that the involved categories are finitely complete.

 Of the aforementioned local properties, the one that requires the most explanation, is
 the subproperty of a local property. To demonstrate this, we shall look at lextensive
 categories. A lextensive category is an extensive category with finite limits. More
 specifically, a lextensive category is a category with
 - finite limits
 - finite coproducts
 - coproducts are stable under pullback
 - coproducts are disjoint
 Every lextensive category has an initial object (nullary coproduct) and this initial
 object is strict. We can slightly reformulate the definition of a lextensive category,
 namely as a category with finite limits together with
 - a strict initial object (which is automatically stable under pullback)
 - binary coproducts that are stable under pullback
 - the binary coproducts are disjoint
 For the first two, we can formulate local properties, which are given by
 [strict_initial_local_property] and [stable_bincoproducts_local_property].

 To specify the disjointness, we use a subproperty. The first important thing to notice
 here, is that the formulation of disjointness ([disjoint_bincoproducts]) presupposes
 the existence of binary coproducts and of an initial object. For this reason, we need
 to express disjointness as an additional property on categories with binary coproducts
 and an initial object. In addition, disjointness is an additional axiom that a category
 may satisfy, so we do not ask for a preservation requirement.

 The notion of subproperty is designed to incorporate such examples. It has a predicate
 on categories satisfying some local property ([sub_property_of_local_property_data]).
 The only two laws for subproperties is that this predicate is a proposition and that
 this predicate is closed under slicing.

 In the file `Biequivalence/LocalProperty.v`, we lift the biequivalence between categories
 with finite limits and DFL comprehension categories to incorporate a local property.
 Each of these properties can be instantiated meaning that we can get such a biequivalence
 for, for example, lextensive categories.

 Contents
 1. Conjunction of local properties
 2. Subproperties of local properties
 3. Strict initial objects
 4. Stable binary coproducts
 5. Disjoint binary coproducts

 **************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.ColimitProperties.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.DisjointBinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.

Local Open Scope cat.

(** * 1. Conjunction of local properties *)
Definition cat_property_data_conj
           (P₁ P₂ : cat_property_data)
  : cat_property_data.
Proof.
  use make_cat_property_data.
  - exact (λ C, P₁ C × P₂ C).
  - exact (λ C₁ C₂ H₁ H₂ F,
           cat_property_functor P₁ (pr1 H₁) (pr1 H₂) F
           ×
           cat_property_functor P₂ (pr2 H₁) (pr2 H₂) F).
Defined.

Proposition cat_property_laws_conj
            (P₁ P₂ : cat_property)
  : cat_property_laws (cat_property_data_conj P₁ P₂).
Proof.
  refine (_ ,, _ ,, _ ,, _).
  - intros C.
    apply isapropdirprod.
    + apply isaprop_cat_property_ob.
    + apply isaprop_cat_property_ob.
  - intros C₁ C₂ H₁ H₂ F.
    apply isapropdirprod.
    + apply isaprop_cat_property_functor.
    + apply isaprop_cat_property_functor.
  - intros C H.
    split.
    + apply cat_property_id_functor.
    + apply cat_property_id_functor.
  - intros C₁ C₂ C₃ H₁ H₂ H₃ F G HF HG.
    split.
    + exact (cat_property_comp_functor P₁ (pr1 HF) (pr1 HG)).
    + exact (cat_property_comp_functor P₂ (pr2 HF) (pr2 HG)).
Qed.

Definition cat_property_conj
           (P₁ P₂ : cat_property)
  : cat_property.
Proof.
  use make_cat_property.
  - exact (cat_property_data_conj P₁ P₂).
  - exact (cat_property_laws_conj P₁ P₂).
Defined.

Proposition is_local_property_conj
            (P₁ P₂ : local_property)
  : is_local_property (cat_property_conj P₁ P₂).
Proof.
  use make_is_local_property.
  - intros C x H.
    split.
    + exact (local_property_slice P₁ C x (pr1 H)).
    + exact (local_property_slice P₂ C x (pr2 H)).
  - intros C H x y f.
    split.
    + exact (local_property_pb P₁ (pr1 H) f).
    + exact (local_property_pb P₂ (pr2 H) f).
  - intros C₁ C₂ H₁ H₂ F HF x.
    split.
    + exact (local_property_fiber_functor P₁ (pr1 H₁) (pr1 H₂) F (pr1 HF) x).
    + exact (local_property_fiber_functor P₂ (pr2 H₁) (pr2 H₂) F (pr2 HF) x).
Defined.

Definition local_property_conj
           (P₁ P₂ : local_property)
  : local_property.
Proof.
  use make_local_property.
  - exact (cat_property_conj P₁ P₂).
  - exact (is_local_property_conj P₁ P₂).
Defined.

(** * 2. Subproperties of local properties *)
(**
   For subproperties, we further refine the categorical by adding another predicate
   on categories (not on the functors).
 *)
Definition sub_property_of_local_property_data
           (P : local_property)
  : UU
  := ∏ (C : category), P C → UU.

Definition sub_property_of_local_property_laws
           (P : local_property)
           (Q : sub_property_of_local_property_data P)
  : UU
  := (∏ (C : univalent_category)
        (H : P C),
      isaprop (Q C H))
     ×
     (∏ (C : univ_cat_with_finlim)
        (x : C)
        (H : P C),
      Q C H
      →
      Q (C/x) (local_property_slice P C x H)).

Definition sub_property_of_local_property
           (P : local_property)
  : UU
  := ∑ (Q : sub_property_of_local_property_data P),
     sub_property_of_local_property_laws P Q.

Definition make_sub_property_of_local_property
           {P : local_property}
           (Q : sub_property_of_local_property_data P)
           (H : sub_property_of_local_property_laws P Q)
  : sub_property_of_local_property P
  := Q ,, H.

Definition sub_property_of_local_property_to_data
           {P : local_property}
           (Q : sub_property_of_local_property P)
           (C : category)
           (H : P C)
  : UU
  := pr1 Q C H.

Coercion sub_property_of_local_property_to_data
  : sub_property_of_local_property >-> Funclass.

Proposition isaprop_sub_property_of_local_property
            {P : local_property}
            (Q : sub_property_of_local_property P)
            (C : univalent_category)
            (H : P C)
  : isaprop (Q C H).
Proof.
  exact (pr12 Q C H).
Defined.

Proposition sub_property_of_local_property_slice
            {P : local_property}
            (Q : sub_property_of_local_property P)
            (C : univ_cat_with_finlim)
            (x : C)
            (H : P C)
            (H' : Q C H)
  : Q (C/x) (local_property_slice P C x H).
Proof.
  exact (pr22 Q C x H H').
Defined.

Section SubLocalProperty.
  Context (P : local_property)
          (Q : sub_property_of_local_property P).

  Definition sub_cat_property_data
    : cat_property_data.
  Proof.
    use make_cat_property_data.
    - exact (λ C, ∑ (H : P C), Q C H).
    - exact (λ C₁ C₂ H₁ H₂ F, cat_property_functor P (pr1 H₁) (pr1 H₂) F).
  Defined.

  Proposition sub_cat_property_laws
    : cat_property_laws sub_cat_property_data.
  Proof.
    repeat split.
    - intros C.
      use isaproptotal2.
      + intro.
        apply isaprop_sub_property_of_local_property.
      + intros.
        apply isaprop_cat_property_ob.
    - intros.
      apply isaprop_cat_property_functor.
    - intros.
      apply cat_property_id_functor.
    - intros C₁ C₂ C₃ H₁ H₂ H₃ F G HF HG.
      exact (cat_property_comp_functor P HF HG).
  Qed.

  Definition sub_cat_property
    : cat_property.
  Proof.
    use make_cat_property.
    - exact sub_cat_property_data.
    - exact sub_cat_property_laws.
  Defined.

  Proposition is_local_property_sub_cat_property
    : is_local_property sub_cat_property.
  Proof.
    use make_is_local_property.
    - intros C x H.
      refine (local_property_slice P C x (pr1 H) ,, _).
      apply sub_property_of_local_property_slice.
      exact (pr2 H).
    - intros.
      apply local_property_pb.
    - intros C₁ C₂ H₁ H₂ F HF x.
      exact (local_property_fiber_functor P _ _ _ HF x).
  Defined.

  Definition sub_local_property
    : local_property.
  Proof.
    use make_local_property.
    - exact sub_cat_property.
    - exact is_local_property_sub_cat_property.
  Defined.
End SubLocalProperty.

(** * 3. Strict initial objects *)
Definition strict_initial_cat_property_data
  : cat_property_data.
Proof.
  use make_cat_property_data.
  - exact (λ C, strict_initial_object C).
  - exact (λ _ _ _ _ F, preserves_initial F).
Defined.

Proposition strict_initial_cat_property_laws
  : cat_property_laws strict_initial_cat_property_data.
Proof.
  repeat split.
  - intro C.
    apply isaprop_strict_initial_object.
  - intros.
    apply isaprop_preserves_initial.
  - intros.
    apply identity_preserves_initial.
  - intros ? ? ? ? ? ? ? ? HF HG.
    exact (composition_preserves_initial HF HG).
Qed.

Definition strict_initial_cat_property
  : cat_property.
Proof.
  use make_cat_property.
  - exact strict_initial_cat_property_data.
  - exact strict_initial_cat_property_laws.
Defined.

Proposition is_local_property_strict_initial_cat_property
  : is_local_property strict_initial_cat_property.
Proof.
  use make_is_local_property.
  - intros C x I.
    exact (strict_initial_cod_fib x I).
  - intros C I x y f ; cbn.
    apply stict_initial_stable.
    exact I.
  - intros C₁ C₂ I₁ I₂ F HF x.
    apply preserves_initial_fiber_functor_disp_codomain.
    + exact (pr1 I₁).
    + exact HF.
Defined.

Definition strict_initial_local_property
  : local_property.
Proof.
  use make_local_property.
  - exact strict_initial_cat_property.
  - exact is_local_property_strict_initial_cat_property.
Defined.

(** * 4. Stable binary coproducts *)
Definition stable_bincoproducts_cat_property_data
  : cat_property_data.
Proof.
  use make_cat_property_data.
  - exact (λ C, ∑ (BC : BinCoproducts C), stable_bincoproducts BC).
  - exact (λ C₁ C₂ H₁ H₂ F, preserves_bincoproduct F).
Defined.

Proposition stable_bincoproducts_cat_property_laws
  : cat_property_laws stable_bincoproducts_cat_property_data.
Proof.
  repeat split.
  - intros C.
    use isaproptotal2.
    + intro.
      apply isaprop_stable_bincoproducts.
    + intros.
      apply isaprop_BinCoproducts.
  - intros.
    apply isaprop_preserves_bincoproduct.
  - intros.
    apply identity_preserves_bincoproduct.
  - intros ? ? ? ? ? ? ? ? HF HG.
    exact (composition_preserves_bincoproduct HF HG).
Qed.

Definition stable_bincoproducts_cat_property
  : cat_property.
Proof.
  use make_cat_property.
  - exact stable_bincoproducts_cat_property_data.
  - exact stable_bincoproducts_cat_property_laws.
Defined.

Proposition is_local_property_stable_bincoproducts_cat_property
  : is_local_property stable_bincoproducts_cat_property.
Proof.
  use make_is_local_property.
  - intros C x BC.
    simple refine (_ ,, _).
    + exact (bincoproducts_cod_fib x (pr1 BC)).
    + apply stable_bincoproducts_cod_fib.
      * exact (pullbacks_univ_cat_with_finlim C).
      * exact (pr2 BC).
  - intros C HC x y f ; cbn.
    use pb_preserves_bincoproduct_from_stable_bincoproducts.
    + exact (pr1 HC).
    + exact (pr2 HC).
  - intros C₁ C₂ HC₁ HC₂ F HF x ; cbn.
    apply preserves_bincoproducts_fiber_functor_disp_codomain.
    + exact (pr1 HC₁).
    + exact HF.
Defined.

Definition stable_bincoproducts_local_property
  : local_property.
Proof.
  use make_local_property.
  - exact stable_bincoproducts_cat_property.
  - exact is_local_property_stable_bincoproducts_cat_property.
Defined.

(** * 5. Disjoint binary coproducts *)
Definition strict_initial_stable_bincoprod_local_property
  : local_property
  := local_property_conj
       strict_initial_local_property
       stable_bincoproducts_local_property.

Definition disjoint_bincoprod_subproperty_data
  : sub_property_of_local_property_data
      strict_initial_stable_bincoprod_local_property
  := λ C HC, disjoint_bincoproducts (pr12 HC) (pr11 HC).

Arguments disjoint_bincoprod_subproperty_data /.

Proposition disjoint_bincoprod_subproperty_laws
  : sub_property_of_local_property_laws
      strict_initial_stable_bincoprod_local_property
      disjoint_bincoprod_subproperty_data.
Proof.
  split.
  - intros.
    apply isaprop_disjoint_bincoproducts.
  - intros C x HC H ; cbn.
    exact (disjoint_bincoproducts_cod_fib x (pr11 HC) (pr12 HC) H).
Qed.

Definition disjoint_bincoprod_subproperty
  : sub_property_of_local_property
      strict_initial_stable_bincoprod_local_property.
Proof.
  use make_sub_property_of_local_property.
  - exact disjoint_bincoprod_subproperty_data.
  - exact disjoint_bincoprod_subproperty_laws.
Defined.

Definition lextensive_local_property
  : local_property
  := sub_local_property
       _
       disjoint_bincoprod_subproperty.
