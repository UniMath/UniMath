(**

 Types formers in universes of comprehension categories

 We defined when a comprehension category is equipped with a universe type, and we constructed
 a biequivalence between the bicategory of univalent DFL full comprehension categories with a
 universe type and the bicategory of univalent categories with finite limits and a universe
 type. Our next goal is to extended this biequivalence to cover universes that are closed under
 certain type formers as well. We consider various type formers, and these are given in various
 files. In this file, we consider codes for a fixed type in the empty context, and we instantiate
 that to the unit type, empty type, natural numbers, and subobject classifier.

 There are several design decisions in the development. First, to express that a universe has a
 code for a certain type former, we assume that the comprehension category supports that type
 former and we say that we have codes whose associated type is isomorphic to the given type
 former. For instance, to say that we have codes for the propositional truncation, we assume
 that the comprehension category is fiberwise a regular category (and that substitution preserves
 regular epimorphisms), and then we say that for each small type (i.e., a term in the universe)
 there is another term in the universe that is isomorphic to the propositional truncation of
 the given type. As a consequence, codes for each type former is expressed using terms of the
 universe type and an isomorphism. This isomorphism is required to live in the slice category
 of the category of contexts, which is sufficient to obtain an isomorphism betwteen types.
 The codes and isomorphism are required to be stable under substitution, which we express
 using two equalities. One of them is an equality of codes and the other says that some
 diagram commutes. Each of the type formers in this file is expressed this way, and thus
 they all are quite similar. Note that we can capture the unit type, empty type, the type of
 natural numbers, and the subobject classifier type with a uniform construction. Specifically,
 for these types it is sufficient to only require a code in the empty context, and we give a
 single generalizing construction for them.

 Finally, we do not define when a functor preserves codes in this file. Our strategy to define
 this is as follows. First we connect type formers in universes for a comprehension category to
 type formers in universes for the category of contexts. For instance, we show that whenever a
 universe in a comprehension category supports propositional resizing, then the universe in the
 category of contexts does so as well. This allows us to express preservation of type formers
 in comprehension categories via preservation of type formers in categories, which simplifies
 the development.

 Contents
 1. Codes for a type in the empty context
 2. Codes for the unit type
 3. Codes for the empty type
 4. Codes for the type of natural numbers
 5. Codes for the subobject classifier type

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.HPropMono.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionPreservation.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.

Local Open Scope cat.
Local Open Scope comp_cat.

Section TypesInCompCatUniv.
  Context (C : dfl_full_comp_cat_with_univ).

  Let el : comp_cat_univ_type (dfl_full_comp_cat_ob C)
    := dfl_full_comp_cat_el C.

  (** * 1. Codes for a type in the empty context *)
  Section FixAType.
    Context {A : ty ([] : C)}.

    Definition type_in_comp_cat_univ
      : UU
      := ∑ (a : tm [] (comp_cat_univ [])),
         z_iso ([] & comp_cat_univ_el el a) ([] & A).

    Proposition isaset_type_in_comp_cat_univ
      : isaset type_in_comp_cat_univ.
    Proof.
      use isaset_total2.
      - apply isaset_comp_cat_tm.
      - intro.
        apply isaset_z_iso.
    Qed.

    Definition make_type_in_comp_cat_univ
               (a : tm [] (comp_cat_univ []))
               (f : z_iso ([] & comp_cat_univ_el el a) ([] & A))
      : type_in_comp_cat_univ
      := a ,, f.

    Definition type_in_comp_cat_univ_code
               (a : type_in_comp_cat_univ)
      : tm [] (comp_cat_univ [])
      := pr1 a.

    Definition type_in_comp_cat_univ_z_iso
               (a : type_in_comp_cat_univ)
      : z_iso ([] & comp_cat_univ_el el (type_in_comp_cat_univ_code a)) ([] & A)
      := pr2 a.

    Definition type_in_comp_cat_univ_z_iso_fiber
               (a : type_in_comp_cat_univ)
      : z_iso
          (C := fiber_category _ _)
          (comp_cat_univ_el el (type_in_comp_cat_univ_code a))
          A.
    Proof.
      use cod_iso_to_type_iso.
      - exact (type_in_comp_cat_univ_z_iso a).
      - abstract
          (apply TerminalArrowEq).
    Defined.

    Proposition type_in_comp_cat_univ_eq
                {a₁ a₂ : type_in_comp_cat_univ}
                (p : type_in_comp_cat_univ_code a₁ = type_in_comp_cat_univ_code a₂)
                (q : comp_cat_comp_mor (comp_cat_el_map_on_eq el p)
                     · type_in_comp_cat_univ_z_iso a₂
                     =
                     type_in_comp_cat_univ_z_iso a₁)
      : a₁ = a₂.
    Proof.
      induction a₁ as [ a₁ f₁ ].
      induction a₂ as [ a₂ f₂ ].
      cbn in p.
      induction p.
      apply maponpaths.
      use z_iso_eq.
      refine (!q @ _) ; cbn.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply comp_cat_comp_mor_id.
    Qed.
  End FixAType.

  Arguments type_in_comp_cat_univ A : clear implicits.

  (** ** 2. Codes for the unit type *)
  Definition unit_in_comp_cat_univ
    : UU
    := type_in_comp_cat_univ (dfl_full_comp_cat_unit ([] : C)).

  Proposition unit_in_comp_cat_univ_eq
              {a₁ a₂ : unit_in_comp_cat_univ}
              (p : type_in_comp_cat_univ_code a₁ = type_in_comp_cat_univ_code a₂)
    : a₁ = a₂.
  Proof.
    induction a₁ as [ a₁ f₁ ].
    induction a₂ as [ a₂ f₂ ].
    cbn in p.
    induction p.
    apply maponpaths.
    use z_iso_eq.
    use (cancel_z_iso
           _ _
           (dfl_full_comp_cat_extend_unit_z_iso
              (C := dfl_full_comp_cat_with_univ_types C)
              [])).
    apply TerminalArrowEq.
  Qed.

  (** ** 3. Codes for the empty type *)
  Definition empty_in_comp_cat_univ
             (I : fiberwise_cat_property
                    strict_initial_local_property
                    (dfl_full_comp_cat_with_univ_types C))
    : UU
    := type_in_comp_cat_univ
         (InitialObject
            (strict_initial_to_initial
               (fiberwise_cat_property_ob I []))).

  Proposition empty_in_comp_cat_univ_eq
              {I : fiberwise_cat_property
                    strict_initial_local_property
                    (dfl_full_comp_cat_with_univ_types C)}
              {a₁ a₂ : empty_in_comp_cat_univ I}
              (p : type_in_comp_cat_univ_code a₁ = type_in_comp_cat_univ_code a₂)
    : a₁ = a₂.
  Proof.
    induction a₁ as [ a₁ f₁ ].
    induction a₂ as [ a₂ f₂ ].
    cbn in p.
    induction p.
    apply maponpaths.
    use z_iso_eq_inv.
    use (InitialArrowEq
           (O := make_Initial
                   _
                   (preserves_initial_dfl_full_comp_cat_adjequiv_base_functor I _ _))).
    apply (strict_initial_to_initial (I [])).
  Qed.

  (** ** 4. Codes for the type of natural numbers *)
  Definition pnno_in_comp_cat_univ
             (N : fiberwise_cat_property
                    parameterized_NNO_local_property
                    (dfl_full_comp_cat_with_univ_types C))
    : UU
    := type_in_comp_cat_univ
         (parameterized_NNO_carrier
            (fiberwise_cat_property_ob N [])).

  (** ** 5. Codes for the subobject classifier type *)
  Definition subobject_classifier_in_comp_cat_univ
             (Ω : fiberwise_cat_property
                    subobject_classifier_local_property
                    (dfl_full_comp_cat_with_univ_types C))
    : UU
    := type_in_comp_cat_univ
         (subobject_classifier_object
            (fiberwise_cat_property_ob Ω [])).
End TypesInCompCatUniv.

Arguments type_in_comp_cat_univ {C} A.
Arguments type_in_comp_cat_univ_code {C A} a.
Arguments type_in_comp_cat_univ_z_iso {C A} a.
Arguments type_in_comp_cat_univ_z_iso_fiber {C A} a.
