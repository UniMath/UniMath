(**

 Equivalences for types in the empty context

 We have defined the following notions:
 - what it means for a universe in a category with finite limits to contain the unit,
   empty, NNO, and subobject classifier types
 - what it means for a universe in a comprehension category limits to contain the unit,
   empty, NNO, and subobject classifier types
 In this file, we connect these two notions. More specifically, if `C` is a comprehension
 category with a universe `u`, then its category of contexts, which for clarity we denote
 by `Cu` (this category is, in fact `C`, but to distinguish it from the comprehension
 category `C`, we give it a different name), also has a universe. We show that the universe
 in `C` containing the aforementioned type formers is equivalent to `Cu` containing the
 aforementioned type formers. We express this as an equivalence of types, since both types
 are sets.

 Contents
 1. Unit type
 2. Empty type
 3. Parameterized natural numbers object
 4. Subobject classifiers

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.StrictInitial.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionPreservation.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatExamples.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Constant.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Constant.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.UnitForUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.CounitForUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Unit type *)
Definition terminal_in_dfl_full_comp_cat_to_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           (unit_c : unit_in_comp_cat_univ C)
  : terminal_in_cat_univ
      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C).
Proof.
  use make_type_in_cat_univ.
  - use (dfl_full_comp_cat_tm_to_mor_univ (C := dfl_full_comp_cat_with_univ_types C)).
    exact (type_in_comp_cat_univ_code unit_c).
  - refine (z_iso_comp (z_iso_comp _ (type_in_comp_cat_univ_z_iso unit_c)) _).
    + use comp_cat_comp_fiber_z_iso.
      use (comp_cat_el_map_on_eq_iso _).
      apply dfl_full_comp_cat_tm_to_mor_to_tm_univ.
    + apply (dfl_full_comp_cat_extend_unit_z_iso (C := dfl_full_comp_cat_with_univ_types C)).
Defined.

Definition terminal_in_dfl_full_comp_cat_from_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           (unit_c : terminal_in_cat_univ
                       (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
  : unit_in_comp_cat_univ C.
Proof.
  use make_type_in_comp_cat_univ.
  - use (dfl_full_comp_cat_mor_to_tm_univ (C := dfl_full_comp_cat_with_univ_types C)).
    exact (type_in_cat_univ_code unit_c).
  - refine (z_iso_comp (type_in_cat_univ_z_iso unit_c) _).
    exact (z_iso_inv
             (dfl_full_comp_cat_extend_unit_z_iso
                (C := dfl_full_comp_cat_with_univ_types C)
                _)).
Defined.

Definition terminal_in_dfl_full_comp_cat_weq_finlim_univ
           (C : dfl_full_comp_cat_with_univ)
  : unit_in_comp_cat_univ C
    ≃
    terminal_in_cat_univ
      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C).
Proof.
  use weq_iso.
  - exact terminal_in_dfl_full_comp_cat_to_finlim_univ.
  - exact terminal_in_dfl_full_comp_cat_from_finlim_univ.
  - abstract
      (intro unit_c ;
       use unit_in_comp_cat_univ_eq ; cbn ;
       exact (dfl_full_comp_cat_tm_to_mor_to_tm_univ
                _
                (type_in_comp_cat_univ_code unit_c))).
  - abstract
      (intro unit_c ;
       use terminal_in_cat_univ_eq ;
       cbn ;
       apply dfl_full_comp_cat_mor_to_tm_to_mor_univ).
Defined.

(** * 2. Empty type *)
Definition empty_in_dfl_full_comp_cat_to_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           {I : fiberwise_cat_property
                  strict_initial_local_property
                  (dfl_full_comp_cat_with_univ_types C)}
           (empty_c : empty_in_comp_cat_univ C I)
  : initial_in_cat_univ
      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
      (strict_initial_to_initial
         (local_property_in_dfl_comp_cat _ _ I)).
Proof.
  use make_type_in_cat_univ.
  - use (dfl_full_comp_cat_tm_to_mor_univ (C := dfl_full_comp_cat_with_univ_types C)).
    exact (type_in_comp_cat_univ_code empty_c).
  - refine (z_iso_comp (z_iso_comp _ (type_in_comp_cat_univ_z_iso empty_c)) _).
    + use comp_cat_comp_fiber_z_iso.
      use (comp_cat_el_map_on_eq_iso _).
      apply dfl_full_comp_cat_tm_to_mor_to_tm_univ.
    + exact (preserves_initial_to_z_iso
               _
               (preserves_initial_dfl_full_comp_cat_adjequiv_base_functor I)
               _ _).
Defined.

Definition empty_in_dfl_full_comp_cat_from_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           {I : fiberwise_cat_property
                  strict_initial_local_property
                  (dfl_full_comp_cat_with_univ_types C)}
           (empty_c : initial_in_cat_univ
                        (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                        (strict_initial_to_initial
                           (local_property_in_dfl_comp_cat _ _ I)))
  : empty_in_comp_cat_univ C I.
Proof.
  use make_type_in_comp_cat_univ.
  - use (dfl_full_comp_cat_mor_to_tm_univ (C := dfl_full_comp_cat_with_univ_types C)).
    exact (type_in_cat_univ_code empty_c).
  - refine (z_iso_comp (type_in_cat_univ_z_iso empty_c) _) ; cbn.
    use z_iso_inv.
    exact (preserves_initial_to_z_iso
             _
             (preserves_initial_dfl_full_comp_cat_adjequiv_base_functor I)
             _ _).
Defined.

Definition empty_in_dfl_full_comp_cat_weq_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           (I : fiberwise_cat_property
                  strict_initial_local_property
                  (dfl_full_comp_cat_with_univ_types C))
  : empty_in_comp_cat_univ C I
    ≃
    initial_in_cat_univ
      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
      (strict_initial_to_initial
         (local_property_in_dfl_comp_cat _ _ I)).
Proof.
  use weq_iso.
  - exact empty_in_dfl_full_comp_cat_to_finlim_univ.
  - exact empty_in_dfl_full_comp_cat_from_finlim_univ.
  - abstract
      (intro empty_c ;
       use empty_in_comp_cat_univ_eq ; cbn ;
       exact (dfl_full_comp_cat_tm_to_mor_to_tm_univ
                _
                (type_in_comp_cat_univ_code empty_c))).
  - abstract
      (intro empty_c ;
       use initial_in_cat_univ_eq ;
       cbn ;
       apply dfl_full_comp_cat_mor_to_tm_to_mor_univ).
Defined.

(** * 3. Parameterized natural numbers object *)
Definition pnno_in_dfl_full_comp_cat_to_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           {N : fiberwise_cat_property
                  parameterized_NNO_local_property
                  (dfl_full_comp_cat_with_univ_types C)}
           (N_c : pnno_in_comp_cat_univ C N)
  : pnno_in_cat_univ
      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
      (local_property_in_dfl_comp_cat _ _ N).
Proof.
  use make_type_in_cat_univ.
  - use (dfl_full_comp_cat_tm_to_mor_univ (C := dfl_full_comp_cat_with_univ_types C)).
    exact (type_in_comp_cat_univ_code N_c).
  - refine (z_iso_comp (z_iso_comp _ (type_in_comp_cat_univ_z_iso N_c)) _).
    + use comp_cat_comp_fiber_z_iso.
      use (comp_cat_el_map_on_eq_iso _).
      apply dfl_full_comp_cat_tm_to_mor_to_tm_univ.
    + exact (preserves_parameterized_NNO_z_iso
               (preserves_pnno_dfl_full_comp_cat_adjequiv_base_functor N)).
Defined.

Definition pnno_in_dfl_full_comp_cat_from_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           {N : fiberwise_cat_property
                  parameterized_NNO_local_property
                  (dfl_full_comp_cat_with_univ_types C)}
           (N_c : pnno_in_cat_univ
                    (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                    (local_property_in_dfl_comp_cat _ _ N))
  : pnno_in_comp_cat_univ C N.
Proof.
  use make_type_in_comp_cat_univ.
  - use (dfl_full_comp_cat_mor_to_tm_univ (C := dfl_full_comp_cat_with_univ_types C)).
    exact (type_in_cat_univ_code N_c).
  - refine (z_iso_comp (type_in_cat_univ_z_iso N_c) _).
    use z_iso_inv.
    exact (preserves_parameterized_NNO_z_iso
             (preserves_pnno_dfl_full_comp_cat_adjequiv_base_functor N)).
Defined.

Proposition pnno_in_dfl_full_comp_cat_weq_finlim_univ_left
            {C : dfl_full_comp_cat_with_univ}
            (N : fiberwise_cat_property
                   parameterized_NNO_local_property
                   (dfl_full_comp_cat_with_univ_types C))
            (c : pnno_in_comp_cat_univ C N)
  : pnno_in_dfl_full_comp_cat_from_finlim_univ
      (pnno_in_dfl_full_comp_cat_to_finlim_univ c)
    =
    c.
Proof.
  use type_in_comp_cat_univ_eq.
  - exact (dfl_full_comp_cat_tm_to_mor_to_tm_univ
             _
             (type_in_comp_cat_univ_code c)).
  - simpl.
    refine (!(id_right _) @ _).
    rewrite !assoc'.
    do 2 apply maponpaths.
    refine (!_).
    use z_iso_inv_on_right.
    rewrite id_right.
    apply idpath.
Qed.

Proposition pnno_in_dfl_full_comp_cat_weq_finlim_univ_right
            {C : dfl_full_comp_cat_with_univ}
            (N : fiberwise_cat_property
                   parameterized_NNO_local_property
                   (dfl_full_comp_cat_with_univ_types C))
            (c : pnno_in_cat_univ
                   (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                   (local_property_in_dfl_comp_cat _ _ N))
  : pnno_in_dfl_full_comp_cat_to_finlim_univ
      (pnno_in_dfl_full_comp_cat_from_finlim_univ c)
    =
    c.
Proof.
  use type_in_cat_univ_eq.
  - apply dfl_full_comp_cat_mor_to_tm_to_mor_univ.
  - simpl.
    refine (!(id_right _) @ _).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths_2.
      apply (dfl_full_comp_cat_cat_el_map_el_eq (C := dfl_full_comp_cat_with_univ_types C)).
    }
    rewrite !assoc.
    use z_iso_inv_on_left.
    rewrite id_right.
    do 2 apply maponpaths_2.
    use (maponpaths (λ z, comprehension_functor_mor _ z)).
    apply (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C)).
Qed.

Definition pnno_in_dfl_full_comp_cat_weq_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           (N : fiberwise_cat_property
                  parameterized_NNO_local_property
                  (dfl_full_comp_cat_with_univ_types C))
  : pnno_in_comp_cat_univ C N
    ≃
    pnno_in_cat_univ
      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
      (local_property_in_dfl_comp_cat _ _ N).
Proof.
  use weq_iso.
  - exact pnno_in_dfl_full_comp_cat_to_finlim_univ.
  - exact pnno_in_dfl_full_comp_cat_from_finlim_univ.
  - exact (pnno_in_dfl_full_comp_cat_weq_finlim_univ_left N).
  - exact (pnno_in_dfl_full_comp_cat_weq_finlim_univ_right N).
Defined.

(** * 4. Subobject classifiers *)
Definition subobject_classifier_in_dfl_full_comp_cat_to_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           {Ω : fiberwise_cat_property
                  subobject_classifier_local_property
                  (dfl_full_comp_cat_with_univ_types C)}
           (Ω_c : subobject_classifier_in_comp_cat_univ C Ω)
  : subobject_classifier_in_cat_univ
      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
      (local_property_in_dfl_comp_cat _ _ Ω).
Proof.
  use make_type_in_cat_univ.
  - use (dfl_full_comp_cat_tm_to_mor_univ (C := dfl_full_comp_cat_with_univ_types C)).
    exact (type_in_comp_cat_univ_code Ω_c).
  - refine (z_iso_comp (z_iso_comp _ (type_in_comp_cat_univ_z_iso Ω_c)) _).
    + use comp_cat_comp_fiber_z_iso.
      use (comp_cat_el_map_on_eq_iso _).
      apply dfl_full_comp_cat_tm_to_mor_to_tm_univ.
    + exact (preserves_subobject_classifier_z_iso
               (preserves_subobj_classifier_dfl_full_comp_cat_adjequiv_base_functor Ω)
               _
               _).
Defined.

Definition subobject_classifier_in_dfl_full_comp_cat_from_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           {Ω : fiberwise_cat_property
                  subobject_classifier_local_property
                  (dfl_full_comp_cat_with_univ_types C)}
           (Ω_c : subobject_classifier_in_cat_univ
                    (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                    (local_property_in_dfl_comp_cat _ _ Ω))
  : subobject_classifier_in_comp_cat_univ C Ω.
Proof.
  use make_type_in_comp_cat_univ.
  - use (dfl_full_comp_cat_mor_to_tm_univ (C := dfl_full_comp_cat_with_univ_types C)).
    exact (type_in_cat_univ_code Ω_c).
  - refine (z_iso_comp (type_in_cat_univ_z_iso Ω_c) _).
    use z_iso_inv.
    exact (preserves_subobject_classifier_z_iso
             (preserves_subobj_classifier_dfl_full_comp_cat_adjequiv_base_functor Ω)
             _
             _).
Defined.

Proposition subobject_classifier_in_dfl_full_comp_cat_weq_finlim_univ_left
            {C : dfl_full_comp_cat_with_univ}
            (Ω : fiberwise_cat_property
                   subobject_classifier_local_property
                   (dfl_full_comp_cat_with_univ_types C))
            (c : subobject_classifier_in_comp_cat_univ C Ω)
  : subobject_classifier_in_dfl_full_comp_cat_from_finlim_univ
      (subobject_classifier_in_dfl_full_comp_cat_to_finlim_univ c)
    =
    c.
Proof.
  use type_in_comp_cat_univ_eq.
  - exact (dfl_full_comp_cat_tm_to_mor_to_tm_univ
             _
             (type_in_comp_cat_univ_code c)).
  - simpl.
    refine (!(id_right _) @ _).
    rewrite !assoc'.
    do 2 apply maponpaths.
    use z_iso_inv_on_left.
    rewrite id_left.
    apply idpath.
Qed.

Proposition subobject_classifier_in_dfl_full_comp_cat_weq_finlim_univ_right
            {C : dfl_full_comp_cat_with_univ}
            (Ω : fiberwise_cat_property
                   subobject_classifier_local_property
                   (dfl_full_comp_cat_with_univ_types C))
            (c : subobject_classifier_in_cat_univ
                   (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                   (local_property_in_dfl_comp_cat _ _ Ω))
  : subobject_classifier_in_dfl_full_comp_cat_to_finlim_univ
      (subobject_classifier_in_dfl_full_comp_cat_from_finlim_univ c)
    =
    c.
Proof.
  use type_in_cat_univ_eq.
  - apply dfl_full_comp_cat_mor_to_tm_to_mor_univ.
  - simpl.
    refine (!_).
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply z_iso_after_z_iso_inv.
    }
    rewrite id_right.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      exact (dfl_full_comp_cat_cat_el_map_el_eq
               (C := dfl_full_comp_cat_with_univ_types C)
               _ _
               (dfl_full_comp_cat_mor_to_tm_to_mor_univ
                  (dfl_full_comp_cat_univ_ob C)
                  (type_in_cat_univ_code c))).
    }
    use (maponpaths (λ z, comprehension_functor_mor _ z)).
    apply (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C)).
Qed.

Definition subobject_classifier_in_dfl_full_comp_cat_weq_finlim_univ
           {C : dfl_full_comp_cat_with_univ}
           (Ω : fiberwise_cat_property
                  subobject_classifier_local_property
                  (dfl_full_comp_cat_with_univ_types C))
  : subobject_classifier_in_comp_cat_univ C Ω
    ≃
    subobject_classifier_in_cat_univ
      (C := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
      (local_property_in_dfl_comp_cat _ _ Ω).
Proof.
  use weq_iso.
  - exact subobject_classifier_in_dfl_full_comp_cat_to_finlim_univ.
  - exact subobject_classifier_in_dfl_full_comp_cat_from_finlim_univ.
  - exact (subobject_classifier_in_dfl_full_comp_cat_weq_finlim_univ_left Ω).
  - exact (subobject_classifier_in_dfl_full_comp_cat_weq_finlim_univ_right Ω).
Defined.
