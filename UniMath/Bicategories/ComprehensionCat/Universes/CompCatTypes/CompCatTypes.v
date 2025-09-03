(**

 Types formers in universes of coomprehension categories

 We defined when a comprehension category is equipped with a universe type, and we constructed
 a biequivalence between the bicategory of univalent DFL full comprehension categories with a
 universe type and the bicategory of univalent categories with finite limits and a universe
 type. Our next goal is to extended this biequivalence to cover universes that are closed under
 certain type formers as well. In this file, we define when a universe in a comprehension
 category is closed under type formers. We consider various type formers, and a complete list
 is given under the table of contents of this file.

 There are several design decisions in this file. First, to express that a universe has a code
 for a certain type former, we assume that the comprehension category supports that type former
 and we say that we have codes whose associated type is isomorphic to the given type former.
 For instance, to say that we have codes for the propositional truncation, we assume that
 the comprehension category is fiberwise a regular category (and that substitution preserves
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
 6. Codes for propositional resizing
 7. Codes for extensional identity types
 8. Codes for the propositional truncation
 9. Codes for binary sum types
 10. Codes for ∑-types

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
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.
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

  (** * 6. Codes for propositional resizing *)
  Definition resizing_in_comp_cat_univ
    : UU
    := ∏ (Γ : dfl_full_comp_cat_with_univ_types C)
         (A : ty Γ)
         (HA : is_hprop_ty A),
       ∑ (resize : tm Γ (dfl_full_comp_cat_univ Γ))
         (f : z_iso (Γ & comp_cat_univ_el el resize) (Γ & A)),
       f · π _ = π _.

  Proposition isaset_resizing_in_comp_cat_univ
      : isaset resizing_in_comp_cat_univ.
  Proof.
    do 3 (use impred_isaset ; intro).
    use isaset_total2.
    - apply isaset_comp_cat_tm.
    - intro.
      use isaset_total2.
      + apply isaset_z_iso.
      + intro.
        apply isasetaprop.
        apply homset_property.
  Qed.

  Definition make_resizing_in_comp_cat_univ
             (resize : ∏ (Γ : dfl_full_comp_cat_with_univ_types C)
                         (A : ty Γ)
                         (HA : is_hprop_ty A),
                       tm Γ (dfl_full_comp_cat_univ Γ))
             (f : ∏ (Γ : dfl_full_comp_cat_with_univ_types C)
                    (A : ty Γ)
                    (HA : is_hprop_ty A),
                  z_iso (Γ & comp_cat_univ_el el (resize Γ A HA)) (Γ & A))
             (p : ∏ (Γ : dfl_full_comp_cat_with_univ_types C)
                    (A : ty Γ)
                    (HA : is_hprop_ty A),
                  f Γ A HA · π _ = π _)
    : resizing_in_comp_cat_univ
    := λ Γ A HA, resize Γ A HA ,, f Γ A HA ,, p Γ A HA.

  Definition resizing_in_comp_cat_univ_code
             (resize : resizing_in_comp_cat_univ)
             {Γ : dfl_full_comp_cat_with_univ_types C}
             (A : ty Γ)
             (HA : is_hprop_ty A)
    : tm Γ (dfl_full_comp_cat_univ Γ)
    := pr1 (resize Γ A HA).

  Definition resizing_in_comp_cat_univ_z_iso
             (resize : resizing_in_comp_cat_univ)
             {Γ : dfl_full_comp_cat_with_univ_types C}
             (A : ty Γ)
             (HA : is_hprop_ty A)
    : z_iso
        (Γ & comp_cat_univ_el el (resizing_in_comp_cat_univ_code resize A HA))
        (Γ & A)
    := pr12 (resize Γ A HA).

  Proposition resizing_in_comp_cat_univ_comm
              (resize : resizing_in_comp_cat_univ)
              {Γ : dfl_full_comp_cat_with_univ_types C}
              (A : ty Γ)
              (HA : is_hprop_ty A)
    : resizing_in_comp_cat_univ_z_iso resize A HA · π _ = π _.
  Proof.
    exact (pr22 (resize Γ A HA)).
  Defined.

  Definition resizing_in_comp_cat_univ_z_iso_fiber
             (resize : resizing_in_comp_cat_univ)
             {Γ : dfl_full_comp_cat_with_univ_types C}
             (A : ty Γ)
             (HA : is_hprop_ty A)
    : z_iso
        (C := fiber_category _ _)
        (comp_cat_univ_el el (resizing_in_comp_cat_univ_code resize A HA))
        A.
  Proof.
    use cod_iso_to_type_iso.
    - exact (resizing_in_comp_cat_univ_z_iso resize A HA).
    - exact (resizing_in_comp_cat_univ_comm resize A HA).
  Defined.

  Lemma resizing_in_comp_cat_univ_code_on_eq
        (resize : resizing_in_comp_cat_univ)
        {Γ : C}
        {A B : ty Γ}
        (p : A = B)
        (HA : is_hprop_ty A)
        (HB : is_hprop_ty B)
    : (resizing_in_comp_cat_univ_code resize A HA : _ --> _)
      =
      resizing_in_comp_cat_univ_code resize B HB.
  Proof.
    induction p.
    assert (HA = HB) as ->.
    {
      apply isaprop_is_hprop_ty.
    }
    apply idpath.
  Qed.

  Proposition resizing_in_comp_cat_univ_code_on_z_iso_fib
              (resize : resizing_in_comp_cat_univ)
              {Γ : C}
              {A B : ty Γ}
              (p : z_iso (C := fiber_category _ _) A B)
              (HA : is_hprop_ty A)
              (HB : is_hprop_ty B)
    : (resizing_in_comp_cat_univ_code resize A HA : _ --> _)
      =
      resizing_in_comp_cat_univ_code resize B HB.
  Proof.
    use resizing_in_comp_cat_univ_code_on_eq.
    use (isotoid _ _ p).
    use is_univalent_fiber.
    apply disp_univalent_category_is_univalent_disp.
  Qed.

  Proposition resizing_in_comp_cat_univ_code_on_z_iso
              (resize : resizing_in_comp_cat_univ)
              {Γ : C}
              {A B : ty Γ}
              (f : z_iso (Γ & A) (Γ & B))
              (p : f · π _ = π _)
              (HA : is_hprop_ty A)
              (HB : is_hprop_ty B)
    : (resizing_in_comp_cat_univ_code resize A HA : _ --> _)
      =
      resizing_in_comp_cat_univ_code resize B HB.
  Proof.
    use resizing_in_comp_cat_univ_code_on_z_iso_fib.
    exact (cod_iso_to_type_iso f p).
  Qed.

  Proposition resizing_in_comp_cat_univ_eq
              {resize₁ resize₂ : resizing_in_comp_cat_univ}
              (p : ∏ (Γ : dfl_full_comp_cat_with_univ_types C)
                     (A : ty Γ)
                     (HA : is_hprop_ty A),
                   resizing_in_comp_cat_univ_code resize₁ A HA
                   =
                   resizing_in_comp_cat_univ_code resize₂ A HA)
      : resize₁ = resize₂.
  Proof.
    use funextsec ; intro Γ.
    use funextsec ; intro A.
    use funextsec ; intro HA.
    use total2_paths_f.
    - exact (p Γ A HA).
    - use subtypePath.
      {
        intro.
        apply homset_property.
      }
      rewrite pr1_transportf.
      use z_iso_eq.
      etrans.
      {
        apply (pr1_transportf
                 (P := λ (x : tm Γ (dfl_full_comp_cat_univ Γ))
                         (f : Γ & comp_cat_univ_el el x --> _),
                    is_z_isomorphism _)).
      }
      etrans.
      {
        exact (transportf_comp_cat_univ_el el (p Γ A HA) (pr112 (resize₁ Γ A HA))).
      }
      use (MonicisMonic _ (hprop_ty_to_monic HA)).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply resizing_in_comp_cat_univ_comm.
      }
      etrans.
      {
        apply comp_cat_comp_mor_comm.
      }
      refine (!_).
      apply resizing_in_comp_cat_univ_comm.
  Qed.

  Definition resizing_in_comp_cat_univ_is_stable
             (resize : resizing_in_comp_cat_univ)
    : UU
    := ∏ (Γ Δ : dfl_full_comp_cat_with_univ_types C)
         (s : Γ --> Δ)
         (A : ty Δ)
         (HA : is_hprop_ty A)
         (HAs := is_hprop_ty_subst s HA),
       resizing_in_comp_cat_univ_code resize A HA [[ s ]]tm
       ↑ sub_dfl_comp_cat_univ s
       =
       resizing_in_comp_cat_univ_code resize _ HAs.

  Proposition isaprop_resizing_in_comp_cat_univ_is_stable
              (resize : resizing_in_comp_cat_univ)
    : isaprop (resizing_in_comp_cat_univ_is_stable resize).
  Proof.
    do 5 (use impred ; intro).
    apply isaset_comp_cat_tm.
  Qed.

  Definition stable_resizing_in_comp_cat_univ
    : UU
    := ∑ (resize : resizing_in_comp_cat_univ),
       resizing_in_comp_cat_univ_is_stable resize.

  Definition make_stable_resizing_in_comp_cat_univ
             (resize : resizing_in_comp_cat_univ)
             (H : resizing_in_comp_cat_univ_is_stable resize)
    : stable_resizing_in_comp_cat_univ
    := resize ,, H.

  Proposition isaset_stable_resizing_in_comp_cat_univ
    : isaset stable_resizing_in_comp_cat_univ.
  Proof.
    use isaset_total2.
    - exact isaset_resizing_in_comp_cat_univ.
    - intro x.
      apply isasetaprop.
      apply isaprop_resizing_in_comp_cat_univ_is_stable.
  Qed.

  Coercion stable_resizing_in_comp_cat_univ_to_codes
           (resize : stable_resizing_in_comp_cat_univ)
    : resizing_in_comp_cat_univ
    := pr1 resize.

  Proposition stable_resizing_in_comp_cat_univ_code_stable
              (resize : stable_resizing_in_comp_cat_univ)
              {Γ Δ : dfl_full_comp_cat_with_univ_types C}
              (s : Γ --> Δ)
              (A : ty Δ)
              (HA : is_hprop_ty A)
              (HAs := is_hprop_ty_subst s HA)
    : resizing_in_comp_cat_univ_code resize A HA [[ s ]]tm
      ↑ sub_dfl_comp_cat_univ s
      =
      resizing_in_comp_cat_univ_code resize _ HAs.
  Proof.
    exact (pr2 resize Γ Δ s A HA).
  Defined.

  Proposition stable_resizing_in_comp_cat_univ_code_stable_mor
              (resize : stable_resizing_in_comp_cat_univ)
              {Γ Δ : dfl_full_comp_cat_with_univ_types C}
              (s : Γ --> Δ)
              (A : ty Δ)
              (HA : is_hprop_ty A)
              (HAs := is_hprop_ty_subst s HA)
    : (resizing_in_comp_cat_univ_code resize _ HAs : _ --> _)
      =
      resizing_in_comp_cat_univ_code resize A HA [[ s ]]tm
      ↑ sub_dfl_comp_cat_univ s.
  Proof.
    refine (!_).
    exact (maponpaths pr1 (stable_resizing_in_comp_cat_univ_code_stable resize s A HA)).
  Qed.

  Proposition stable_resizing_in_comp_cat_univ_code_stable_mor'
              (resize : stable_resizing_in_comp_cat_univ)
              {Γ Δ : dfl_full_comp_cat_with_univ_types C}
              (s : Γ --> Δ)
              (A : ty Δ)
              (HA : is_hprop_ty A)
              (HAs := is_hprop_ty_subst s HA)
    : s
      · resizing_in_comp_cat_univ_code resize A HA
      · comprehension_functor_mor
          (comp_cat_comprehension C)
          (cleaving_of_types _ _ _ _ _)
      =
      resizing_in_comp_cat_univ_code resize _ HAs
      · PullbackPr1 (comp_cat_pullback _ _).
  Proof.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply stable_resizing_in_comp_cat_univ_code_stable_mor.
    }
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    apply subst_comp_cat_tm_pr1.
  Qed.

  Proposition stable_resizing_in_comp_cat_univ_eq
              {resize₁ resize₂ : stable_resizing_in_comp_cat_univ}
              (p : ∏ (Γ : dfl_full_comp_cat_with_univ_types C)
                     (A : ty Γ)
                     (HA : is_hprop_ty A),
                   resizing_in_comp_cat_univ_code resize₁ A HA
                   =
                   resizing_in_comp_cat_univ_code resize₂ A HA)
      : resize₁ = resize₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_resizing_in_comp_cat_univ_is_stable.
    }
    use resizing_in_comp_cat_univ_eq.
    exact p.
  Qed.

  (** * 7. Codes for extensional identity types *)
  Definition ext_id_in_comp_cat_univ
    : UU
    := ∏ (Γ : dfl_full_comp_cat_with_univ_types C)
         (a : tm Γ (dfl_full_comp_cat_univ Γ))
         (t₁ t₂ : tm Γ (comp_cat_univ_el el a)),
       ∑ (eq : tm Γ (dfl_full_comp_cat_univ Γ))
         (f : z_iso
                (Γ & comp_cat_univ_el el eq)
                (Γ & dfl_ext_identity_type t₁ t₂)),
       f · π _ = π _.

  Proposition isaset_ext_id_in_comp_cat_univ
      : isaset ext_id_in_comp_cat_univ.
  Proof.
    do 4 (use impred_isaset ; intro).
    use isaset_total2.
    - apply isaset_comp_cat_tm.
    - intro.
      use isaset_total2.
      + apply isaset_z_iso.
      + intro.
        apply isasetaprop.
        apply homset_property.
  Qed.

  Definition make_ext_id_in_comp_cat_univ
             (eq : ∏ (Γ : C)
                     (a : tm Γ (dfl_full_comp_cat_univ Γ))
                     (t₁ t₂ : tm Γ (comp_cat_univ_el el a)),
                  tm Γ (dfl_full_comp_cat_univ Γ))
             (f : ∏ (Γ : dfl_full_comp_cat_with_univ_types C)
                    (a : tm Γ (dfl_full_comp_cat_univ Γ))
                    (t₁ t₂ : tm Γ (comp_cat_univ_el el a)),
                  z_iso
                    (Γ & comp_cat_univ_el el (eq Γ a t₁ t₂))
                    (Γ & dfl_ext_identity_type t₁ t₂))
             (p : ∏ (Γ : C)
                    (a : tm Γ (dfl_full_comp_cat_univ Γ))
                    (t₁ t₂ : tm Γ (comp_cat_univ_el el a)),
                  f Γ a t₁ t₂ · π _ = π _)
    : ext_id_in_comp_cat_univ
    := λ Γ a t₁ t₂, eq Γ a t₁ t₂ ,, f Γ a t₁ t₂ ,, p Γ a t₁ t₂.

  Definition ext_id_in_comp_cat_univ_code
             (eq : ext_id_in_comp_cat_univ)
             {Γ : C}
             {a : tm Γ (dfl_full_comp_cat_univ Γ)}
             (t₁ t₂ : tm Γ (comp_cat_univ_el el a))
    : tm Γ (dfl_full_comp_cat_univ Γ)
    := pr1 (eq Γ a t₁ t₂).

  Definition ext_id_in_comp_cat_univ_z_iso
             (eq : ext_id_in_comp_cat_univ)
             {Γ : dfl_full_comp_cat_with_univ_types C}
             {a : tm Γ (dfl_full_comp_cat_univ Γ)}
             (t₁ t₂ : tm Γ (comp_cat_univ_el el a))
    : z_iso
        (Γ & comp_cat_univ_el el (ext_id_in_comp_cat_univ_code eq t₁ t₂))
        (Γ & dfl_ext_identity_type t₁ t₂)
    := pr12 (eq Γ a t₁ t₂).

  Proposition ext_id_in_comp_cat_univ_comm
              (eq : ext_id_in_comp_cat_univ)
              {Γ : C}
              {a : tm Γ (dfl_full_comp_cat_univ Γ)}
              (t₁ t₂ : tm Γ (comp_cat_univ_el el a))
    : ext_id_in_comp_cat_univ_z_iso eq t₁ t₂ · π _ = π _.
  Proof.
    exact (pr22 (eq Γ a t₁ t₂)).
  Defined.

  Definition ext_id_in_comp_cat_univ_z_iso_fiber
             (eq : ext_id_in_comp_cat_univ)
             {Γ : dfl_full_comp_cat_with_univ_types C}
             {a : tm Γ (dfl_full_comp_cat_univ Γ)}
             (t₁ t₂ : tm Γ (comp_cat_univ_el el a))
    : z_iso
        (C := fiber_category _ _)
        (comp_cat_univ_el el (ext_id_in_comp_cat_univ_code eq t₁ t₂))
        (dfl_ext_identity_type t₁ t₂).
  Proof.
    use cod_iso_to_type_iso.
    - exact (ext_id_in_comp_cat_univ_z_iso eq t₁ t₂).
    - exact (ext_id_in_comp_cat_univ_comm eq t₁ t₂).
  Defined.

  Proposition ext_id_in_comp_cat_univ_code_on_eq
              (eq : ext_id_in_comp_cat_univ)
              {Γ : dfl_full_comp_cat_with_univ_types C}
              {a a' : tm Γ (dfl_full_comp_cat_univ Γ)}
              {t₁ t₂ : tm Γ (comp_cat_univ_el el a)}
              {t₁' t₂' : tm Γ (comp_cat_univ_el el a')}
              (p : a = a')
              (q : t₁ ↑ comp_cat_el_map_on_eq el p = t₁')
              (r : t₂ ↑ comp_cat_el_map_on_eq el p = t₂')
    : ext_id_in_comp_cat_univ_code eq t₁ t₂
      =
      ext_id_in_comp_cat_univ_code eq t₁' t₂'.
  Proof.
    induction p.
    cbn in q, r.
    rewrite id_coerce_comp_cat_tm in q, r.
    induction q, r.
    apply idpath.
  Qed.

  Proposition ext_id_in_comp_cat_univ_code_on_eq'
              (eq : ext_id_in_comp_cat_univ)
              {Γ : dfl_full_comp_cat_with_univ_types C}
              {a a' : tm Γ (dfl_full_comp_cat_univ Γ)}
              {t₁ t₂ : tm Γ (comp_cat_univ_el el a)}
              {t₁' t₂' : tm Γ (comp_cat_univ_el el a')}
              (p : a = a')
              (q : t₁ ↑ comp_cat_el_map_on_eq el p = t₁')
              (r : t₂ ↑ comp_cat_el_map_on_eq el p = t₂')
    : (ext_id_in_comp_cat_univ_code eq t₁ t₂ : _ --> _)
      =
      ext_id_in_comp_cat_univ_code eq t₁' t₂'.
  Proof.
    exact (maponpaths pr1 (ext_id_in_comp_cat_univ_code_on_eq eq p q r)).
  Qed.

  Proposition ext_id_in_comp_cat_univ_eq
              {eq₁ eq₂ : ext_id_in_comp_cat_univ}
              (p : ∏ (Γ : C)
                     (a : tm Γ (dfl_full_comp_cat_univ Γ))
                     (t₁ t₂ : tm Γ (comp_cat_univ_el el a)),
                   ext_id_in_comp_cat_univ_code eq₁ t₁ t₂
                   =
                   ext_id_in_comp_cat_univ_code eq₂ t₁ t₂)
    : eq₁ = eq₂.
  Proof.
    use funextsec ; intro Γ.
    use funextsec ; intro a.
    use funextsec ; intro t₁.
    use funextsec ; intro t₂.
    use total2_paths_f.
    - exact (p Γ a t₁ t₂).
    - use subtypePath.
      {
        intro.
        apply homset_property.
      }
      rewrite pr1_transportf.
      use z_iso_eq.
      etrans.
      {
        apply (pr1_transportf
                 (P := λ (x : tm Γ (dfl_full_comp_cat_univ Γ))
                         (f : Γ & comp_cat_univ_el el x --> _),
                    is_z_isomorphism _)).
      }
      etrans.
      {
        exact (transportf_comp_cat_univ_el el (p Γ a t₁ t₂) _).
      }
      use (hprop_ty_to_mono_ty (is_hprop_ty_dfl_ext_identity_type t₁ t₂)).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply ext_id_in_comp_cat_univ_comm.
      }
      rewrite comp_cat_comp_mor_comm.
      refine (!_).
      apply ext_id_in_comp_cat_univ_comm.
  Qed.

  Definition ext_id_in_comp_cat_univ_is_stable
             (eq : ext_id_in_comp_cat_univ)
    : UU
    := ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (a : tm Δ (dfl_full_comp_cat_univ Δ))
         (t₁ t₂ : tm Δ (comp_cat_univ_el el a)),
       ext_id_in_comp_cat_univ_code eq t₁ t₂ [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
       =
       ext_id_in_comp_cat_univ_code
         eq
         (t₁ [[ s ]]tm ↑ comp_cat_univ_el_stable_mor el s a)
         (t₂ [[ s ]]tm ↑ comp_cat_univ_el_stable_mor el s a).

  Proposition isaprop_ext_id_in_comp_cat_univ_is_stable
              (eq : ext_id_in_comp_cat_univ)
    : isaprop (ext_id_in_comp_cat_univ_is_stable eq).
  Proof.
    do 6 (use impred ; intro).
    apply isaset_comp_cat_tm.
  Qed.

  Definition stable_ext_id_in_comp_cat_univ
    : UU
    := ∑ (eq : ext_id_in_comp_cat_univ),
       ext_id_in_comp_cat_univ_is_stable eq.

  Definition make_stable_ext_id_in_comp_cat_univ
             (eq : ext_id_in_comp_cat_univ)
             (H : ext_id_in_comp_cat_univ_is_stable eq)
    : stable_ext_id_in_comp_cat_univ
    := eq ,, H.

  Proposition isaset_stable_ext_id_in_comp_cat_univ
    : isaset stable_ext_id_in_comp_cat_univ.
  Proof.
    use isaset_total2.
    - exact isaset_ext_id_in_comp_cat_univ.
    - intro x.
      apply isasetaprop.
      apply isaprop_ext_id_in_comp_cat_univ_is_stable.
  Qed.

  Coercion stable_ext_id_in_comp_cat_univ_to_codes
           (eq : stable_ext_id_in_comp_cat_univ)
    : ext_id_in_comp_cat_univ
    := pr1 eq.

  Proposition stable_ext_id_in_comp_cat_univ_code_stable
              (eq : stable_ext_id_in_comp_cat_univ)
              {Γ Δ : C}
              (s : Γ --> Δ)
              {a : tm Δ (dfl_full_comp_cat_univ Δ)}
              (t₁ t₂ : tm Δ (comp_cat_univ_el el a))
    : ext_id_in_comp_cat_univ_code eq t₁ t₂ [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
      =
      ext_id_in_comp_cat_univ_code
        eq
        (t₁ [[ s ]]tm ↑ comp_cat_univ_el_stable_mor el s a)
        (t₂ [[ s ]]tm ↑ comp_cat_univ_el_stable_mor el s a).
  Proof.
    exact (pr2 eq Γ Δ s a t₁ t₂).
  Defined.

  Proposition stable_ext_id_in_comp_cat_univ_code_stable_mor
              (eq : stable_ext_id_in_comp_cat_univ)
              {Γ Δ : C}
              (s : Γ --> Δ)
              {a : tm Δ (dfl_full_comp_cat_univ Δ)}
              (t₁ t₂ : tm Δ (comp_cat_univ_el el a))
    : s
      · ext_id_in_comp_cat_univ_code eq t₁ t₂
      · comprehension_functor_mor
          (comp_cat_comprehension C)
          (cleaving_of_types _ _ _ _ _)
      =
      ext_id_in_comp_cat_univ_code
        eq
        (t₁ [[ s ]]tm ↑ comp_cat_univ_el_stable_mor el s a)
        (t₂ [[ s ]]tm ↑ comp_cat_univ_el_stable_mor el s a)
      · PullbackPr1 (comp_cat_pullback _ _).
  Proof.
    pose (stable_ext_id_in_comp_cat_univ_code_stable eq s t₁ t₂) as p.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (maponpaths pr1 (!p)).
    }
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    apply subst_comp_cat_tm_pr1.
  Qed.

  Proposition stable_ext_id_in_comp_cat_univ_eq
              {eq₁ eq₂ : stable_ext_id_in_comp_cat_univ}
              (p : ∏ (Γ : C)
                     (a : tm Γ (dfl_full_comp_cat_univ Γ))
                     (t₁ t₂ : tm Γ (comp_cat_univ_el el a)),
                   ext_id_in_comp_cat_univ_code eq₁ t₁ t₂
                   =
                   ext_id_in_comp_cat_univ_code eq₂ t₁ t₂)
      : eq₁ = eq₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_ext_id_in_comp_cat_univ_is_stable.
    }
    use ext_id_in_comp_cat_univ_eq.
    exact p.
  Qed.

  (** * 8. Codes for the propositional truncation *)
  Section TruncationCode.
    Context (HC : fiberwise_cat_property
                    regular_local_property
                    (dfl_full_comp_cat_with_univ_types C)).

    Definition truncation_in_comp_cat_univ
      : UU
      := ∏ (Γ : C)
           (a : tm Γ (dfl_full_comp_cat_univ Γ))
           (A := comp_cat_univ_el el a),
         ∑ (trunc : tm Γ (dfl_full_comp_cat_univ Γ))
           (f : z_iso
                  (Γ & comp_cat_univ_el el trunc)
                  (Γ & regular_local_property_trunc HC A)),
         f · π _ = π _.

    Proposition isaset_truncation_in_comp_cat_univ
      : isaset truncation_in_comp_cat_univ.
    Proof.
      do 2 (use impred_isaset ; intro).
      use isaset_total2.
      - apply isaset_comp_cat_tm.
      - intro.
        use isaset_total2.
        + apply isaset_z_iso.
        + intro.
          apply isasetaprop.
          apply homset_property.
    Qed.

    Definition make_truncation_in_comp_cat_univ
               (trunc : ∏ (Γ : C)
                          (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                       tm Γ (dfl_full_comp_cat_univ Γ))
               (f : ∏ (Γ : C)
                      (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                    z_iso
                      (Γ & comp_cat_univ_el el (trunc Γ a))
                      (Γ & regular_local_property_trunc
                             HC
                             (comp_cat_univ_el el a)))
               (p : ∏ (Γ : C)
                      (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                    f Γ a · π _ = π _)
    : truncation_in_comp_cat_univ
    := λ Γ a, trunc Γ a ,, f Γ a ,, p Γ a.

    Definition truncation_in_comp_cat_univ_code
               (trunc : truncation_in_comp_cat_univ)
               {Γ : C}
               (a : tm Γ (dfl_full_comp_cat_univ Γ))
      : tm Γ (dfl_full_comp_cat_univ Γ)
      := pr1 (trunc Γ a).

    Definition truncation_in_comp_cat_univ_z_iso
               (trunc : truncation_in_comp_cat_univ)
               {Γ : C}
               (a : tm Γ (dfl_full_comp_cat_univ Γ))
      : z_iso
          (Γ & comp_cat_univ_el el (truncation_in_comp_cat_univ_code trunc a))
          (Γ & regular_local_property_trunc
                 HC
                 (comp_cat_univ_el el a))
      := pr12 (trunc Γ a).

    Proposition truncation_in_comp_cat_univ_comm
                (trunc : truncation_in_comp_cat_univ)
                {Γ : C}
                (a : tm Γ (dfl_full_comp_cat_univ Γ))
      : truncation_in_comp_cat_univ_z_iso trunc a · π _ = π _.
    Proof.
      exact (pr22 (trunc Γ a)).
    Defined.

    Definition truncation_in_comp_cat_univ_z_iso_fiber
               (trunc : truncation_in_comp_cat_univ)
               {Γ : C}
               (a : tm Γ (dfl_full_comp_cat_univ Γ))
      : z_iso
          (C := fiber_category _ _)
          (comp_cat_univ_el el (truncation_in_comp_cat_univ_code trunc a))
          (regular_local_property_trunc
             HC
             (comp_cat_univ_el el a)).
    Proof.
      use cod_iso_to_type_iso.
      - exact (truncation_in_comp_cat_univ_z_iso trunc a).
      - exact (truncation_in_comp_cat_univ_comm trunc a).
    Defined.

    Proposition trunc_in_comp_cat_univ_eq
                {trunc₁ trunc₂ : truncation_in_comp_cat_univ}
                (p : ∏ (Γ : C)
                       (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                     truncation_in_comp_cat_univ_code trunc₁ a
                     =
                     truncation_in_comp_cat_univ_code trunc₂ a)
      : trunc₁ = trunc₂.
    Proof.
      use funextsec ; intro Γ.
      use funextsec ; intro a.
      use total2_paths_f.
      - exact (p Γ a).
      - use subtypePath.
        {
          intro.
          apply homset_property.
        }
        rewrite pr1_transportf.
        use z_iso_eq.
        etrans.
        {
          apply (pr1_transportf
                   (P := λ (x : tm Γ (dfl_full_comp_cat_univ Γ))
                           (f : Γ & comp_cat_univ_el el x --> _),
                      is_z_isomorphism _)).
        }
        etrans.
        {
          exact (transportf_comp_cat_univ_el el (p Γ a) _).
        }
        use (hprop_ty_to_mono_ty (is_hprop_ty_trunc HC (comp_cat_univ_el el a))).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          exact (truncation_in_comp_cat_univ_comm trunc₁ a).
        }
        rewrite comp_cat_comp_mor_comm.
        refine (!_).
        exact (truncation_in_comp_cat_univ_comm trunc₂ a).
    Qed.

    Proposition truncation_in_comp_cat_univ_code_eq
                (trunc : truncation_in_comp_cat_univ)
                {Γ : C}
                {a₁ a₂ : tm Γ (dfl_full_comp_cat_univ Γ)}
                (p : a₁ = a₂)
      : (truncation_in_comp_cat_univ_code trunc a₁ : _ --> _)
        =
        truncation_in_comp_cat_univ_code trunc a₂.
    Proof.
      induction p.
      apply idpath.
    Qed.

    Definition trunc_in_comp_cat_univ_is_stable
               (trunc : truncation_in_comp_cat_univ)
      : UU
      := ∏ (Γ Δ : C)
           (s : Γ --> Δ)
           (a : tm Δ (dfl_full_comp_cat_univ Δ)),
         truncation_in_comp_cat_univ_code trunc a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
         =
         truncation_in_comp_cat_univ_code trunc (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s).

    Proposition isaprop_trunc_in_comp_cat_univ_is_stable
                (trunc : truncation_in_comp_cat_univ)
      : isaprop (trunc_in_comp_cat_univ_is_stable trunc).
    Proof.
      do 4 (use impred ; intro).
      apply isaset_comp_cat_tm.
    Qed.

    Definition stable_truncation_in_comp_cat_univ
      : UU
      := ∑ (trunc : truncation_in_comp_cat_univ),
         trunc_in_comp_cat_univ_is_stable trunc.

    Definition make_stable_truncation_in_comp_cat_univ
               (trunc : truncation_in_comp_cat_univ)
               (H : trunc_in_comp_cat_univ_is_stable trunc)
      : stable_truncation_in_comp_cat_univ
      := trunc ,, H.

    Proposition isaset_stable_truncation_in_comp_cat_univ
      : isaset stable_truncation_in_comp_cat_univ.
    Proof.
      use isaset_total2.
      - exact isaset_truncation_in_comp_cat_univ.
      - intro x.
        apply isasetaprop.
        apply isaprop_trunc_in_comp_cat_univ_is_stable.
    Qed.

    Coercion stable_truncation_in_comp_cat_univ_to_codes
             (trunc : stable_truncation_in_comp_cat_univ)
      : truncation_in_comp_cat_univ
      := pr1 trunc.

    Proposition stable_truncation_in_comp_cat_univ_code_stable
                (trunc : stable_truncation_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a : tm Δ (dfl_full_comp_cat_univ Δ))
      : truncation_in_comp_cat_univ_code trunc a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
        =
        truncation_in_comp_cat_univ_code trunc (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s).
    Proof.
      exact (pr2 trunc Γ Δ s a).
    Defined.

    Proposition stable_truncation_in_comp_cat_univ_code_stable_mor
                (trunc : stable_truncation_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a : tm Δ (dfl_full_comp_cat_univ Δ))
      : s
        · truncation_in_comp_cat_univ_code trunc a
        · comprehension_functor_mor
            (comp_cat_comprehension C)
            (cleaving_of_types _ _ _ _ _)
        =
        truncation_in_comp_cat_univ_code trunc
          (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        · PullbackPr1 (comp_cat_pullback _ _).
    Proof.
      pose (maponpaths pr1 (stable_truncation_in_comp_cat_univ_code_stable trunc s a)) as p.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (!p).
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply subst_comp_cat_tm_pr1.
    Qed.

    Proposition stable_truncation_in_comp_cat_univ_eq
                {trunc₁ trunc₂ : stable_truncation_in_comp_cat_univ}
                (p : ∏ (Γ : C)
                       (a : tm Γ (dfl_full_comp_cat_univ Γ)),
                     truncation_in_comp_cat_univ_code trunc₁ a
                     =
                     truncation_in_comp_cat_univ_code trunc₂ a)
      : trunc₁ = trunc₂.
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_trunc_in_comp_cat_univ_is_stable.
      }
      use trunc_in_comp_cat_univ_eq.
      exact p.
    Qed.
  End TruncationCode.

  (** * 9. Codes for binary sum types *)
  Section SumCode.
    Context (HC : fiberwise_cat_property
                    stable_bincoproducts_local_property
                    (dfl_full_comp_cat_with_univ_types C)).

    Definition sum_in_comp_cat_univ
      : UU
      := ∏ (Γ : C)
           (a b : tm Γ (dfl_full_comp_cat_univ Γ))
           (A := comp_cat_univ_el el a)
           (B := comp_cat_univ_el el b),
         ∑ (sum : tm Γ (dfl_full_comp_cat_univ Γ))
           (f : z_iso
                  (Γ & coprod_local_property_sum HC A B)
                  (Γ & comp_cat_univ_el el sum)),
         f · π _ = π _.

    Proposition isaset_sum_in_comp_cat_univ
      : isaset sum_in_comp_cat_univ.
    Proof.
      do 3 (use impred_isaset ; intro).
      use isaset_total2.
      - apply isaset_comp_cat_tm.
      - intro.
        use isaset_total2.
        + apply isaset_z_iso.
        + intro.
          apply isasetaprop.
          apply homset_property.
    Qed.

    Definition make_sum_in_comp_cat_univ
               (sum : ∏ (Γ : C)
                        (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                      tm Γ (dfl_full_comp_cat_univ Γ))
               (f : ∏ (Γ : C)
                      (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                    z_iso
                      (Γ & coprod_local_property_sum
                             HC
                             (comp_cat_univ_el el a)
                             (comp_cat_univ_el el b))
                      (Γ & comp_cat_univ_el el (sum Γ a b)))
               (p : ∏ (Γ : C)
                      (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                    f Γ a b · π _ = π _)
    : sum_in_comp_cat_univ
    := λ Γ a b, sum Γ a b ,, f Γ a b ,, p Γ a b.

    Definition sum_in_comp_cat_univ_code
               (sum : sum_in_comp_cat_univ)
               {Γ : C}
               (a b : tm Γ (dfl_full_comp_cat_univ Γ))
      : tm Γ (dfl_full_comp_cat_univ Γ)
      := pr1 (sum Γ a b).

    Definition sum_in_comp_cat_univ_z_iso
               (sum : sum_in_comp_cat_univ)
               {Γ : C}
               (a b : tm Γ (dfl_full_comp_cat_univ Γ))
      : z_iso
          (Γ & coprod_local_property_sum
                 HC
                 (comp_cat_univ_el el a)
                 (comp_cat_univ_el el b))
          (Γ & comp_cat_univ_el el (sum_in_comp_cat_univ_code sum a b))
      := pr12 (sum Γ a b).

    Proposition sum_in_comp_cat_univ_comm
                (sum : sum_in_comp_cat_univ)
                {Γ : C}
                (a b : tm Γ (dfl_full_comp_cat_univ Γ))
      : sum_in_comp_cat_univ_z_iso sum a b · π _ = π _.
    Proof.
      exact (pr22 (sum Γ a b)).
    Defined.

    Definition sum_in_comp_cat_univ_z_iso_fiber
               (sum : sum_in_comp_cat_univ)
               {Γ : C}
               (a b : tm Γ (dfl_full_comp_cat_univ Γ))
      : z_iso
          (C := fiber_category _ _)
          (coprod_local_property_sum
             HC
             (comp_cat_univ_el el a)
             (comp_cat_univ_el el b))
          (comp_cat_univ_el el (sum_in_comp_cat_univ_code sum a b)).
    Proof.
      use cod_iso_to_type_iso.
      - exact (sum_in_comp_cat_univ_z_iso sum a b).
      - exact (sum_in_comp_cat_univ_comm sum a b).
    Defined.

    Proposition sum_in_comp_cat_univ_code_eq
                (sum : sum_in_comp_cat_univ)
                {Γ : C}
                {a a' b b' : tm Γ (dfl_full_comp_cat_univ Γ)}
                (p : a = a')
                (q : b = b')
      : sum_in_comp_cat_univ_code sum a b
        =
        sum_in_comp_cat_univ_code sum a' b'.
    Proof.
      induction p, q.
      apply idpath.
    Qed.

    Proposition sum_in_comp_cat_univ_z_iso_eq
                (sum : sum_in_comp_cat_univ)
                {Γ : C}
                {a a' b b' : tm Γ (dfl_full_comp_cat_univ Γ)}
                (p : a = a')
                (q : b = b')
      : (sum_in_comp_cat_univ_z_iso sum a b : _ --> _)
        =
        comp_cat_comp_mor
          (BinCoproductOfArrows
             _
             (coprod_local_property_bincoproduct
                HC
                (comp_cat_univ_el el a)
                (comp_cat_univ_el el b))
             _
             (comp_cat_el_map_on_eq el p)
             (comp_cat_el_map_on_eq el q))
        · sum_in_comp_cat_univ_z_iso sum a' b'
        · comp_cat_comp_mor
            (comp_cat_el_map_on_eq
               el
               (!(sum_in_comp_cat_univ_code_eq sum p q))).
    Proof.
      induction p, q ; simpl.
      rewrite BinCoproduct_of_identities.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        apply comp_cat_comp_mor_id.
      }
      rewrite id_left.
      refine (_ @ id_right _).
      apply maponpaths.
      refine (_ @ comp_cat_comp_mor_id _).
      apply maponpaths.
      exact (comp_cat_el_map_on_idpath el _).
    Qed.

    Proposition sum_in_comp_cat_univ_eq
                {sum₁ sum₂ : sum_in_comp_cat_univ}
                (p : ∏ (Γ : C)
                       (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                     sum_in_comp_cat_univ_code sum₁ a b
                     =
                     sum_in_comp_cat_univ_code sum₂ a b)
                (q : ∏ (Γ : C)
                       (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                     sum_in_comp_cat_univ_z_iso sum₁ a b
                     · comp_cat_comp_mor (comp_cat_el_map_on_eq el (p Γ a b))
                     =
                     sum_in_comp_cat_univ_z_iso sum₂ a b)
      : sum₁ = sum₂.
    Proof.
      use funextsec ; intro Γ.
      use funextsec ; intro a.
      use funextsec ; intro b.
      use total2_paths_f.
      - exact (p Γ a b).
      - use subtypePath.
        {
          intro.
          apply homset_property.
        }
        rewrite pr1_transportf.
        use z_iso_eq.
        etrans.
        {
          apply (pr1_transportf
                   (P := λ (x : tm Γ (dfl_full_comp_cat_univ Γ))
                           (f : Γ & coprod_local_property_sum HC _ _
                                -->
                                Γ & comp_cat_univ_el el x),
                      is_z_isomorphism _)).
        }
        etrans.
        {
          exact (transportf_comp_cat_univ_el' el (p Γ a b) _).
        }
        exact (q Γ a b).
    Qed.

    Definition sum_in_comp_cat_univ_is_stable
               (sum : sum_in_comp_cat_univ)
      : UU
      := ∏ (Γ Δ : C)
           (s : Γ --> Δ)
           (a b : tm Δ (dfl_full_comp_cat_univ Δ)),
         ∑ (p : sum_in_comp_cat_univ_code sum a b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
                =
                sum_in_comp_cat_univ_code sum
                  (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
                  (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)),
         sum_in_comp_cat_univ_z_iso
           sum
           (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
           (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
         · comp_cat_comp_mor
             (comp_cat_el_map_on_eq el (!p)
              · inv_from_z_iso (comp_cat_univ_el_stable el s _))
         · comp_cat_extend_over _ s
         =
         comp_cat_comp_mor_over
           _
           (coprod_local_property_sum_functor
              HC
              (inv_from_z_iso (comp_cat_univ_el_stable el s a))
              (inv_from_z_iso (comp_cat_univ_el_stable el s b))
            · inv_from_z_iso (coprod_local_property_subst_z_iso HC s _ _))
         · sum_in_comp_cat_univ_z_iso sum a b.

    Proposition isaprop_sum_in_comp_cat_univ_is_stable
                (sum : sum_in_comp_cat_univ)
      : isaprop (sum_in_comp_cat_univ_is_stable sum).
    Proof.
      do 5 (use impred ; intro).
      use isaproptotal2.
      - intro.
        apply homset_property.
      - intros.
        apply isaset_comp_cat_tm.
    Qed.

    Definition stable_sum_in_comp_cat_univ
      : UU
      := ∑ (sum : sum_in_comp_cat_univ),
         sum_in_comp_cat_univ_is_stable sum.

    Definition make_stable_sum_in_comp_cat_univ
               (sum : sum_in_comp_cat_univ)
               (H : sum_in_comp_cat_univ_is_stable sum)
      : stable_sum_in_comp_cat_univ
      := sum ,, H.

    Proposition isaset_stable_sum_in_comp_cat_univ
      : isaset stable_sum_in_comp_cat_univ.
    Proof.
      use isaset_total2.
      - exact isaset_sum_in_comp_cat_univ.
      - intro x.
        apply isasetaprop.
        apply isaprop_sum_in_comp_cat_univ_is_stable.
    Qed.

    Coercion stable_sum_in_comp_cat_univ_to_codes
             (sum : stable_sum_in_comp_cat_univ)
      : sum_in_comp_cat_univ
      := pr1 sum.

    Proposition stable_sum_in_comp_cat_univ_code_stable
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : sum_in_comp_cat_univ_code sum a b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
        =
        sum_in_comp_cat_univ_code sum
          (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
          (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s).
    Proof.
      exact (pr1 (pr2 sum Γ Δ s a b)).
    Defined.

    Proposition stable_sum_in_comp_cat_univ_code_stable_mor
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : s
        · sum_in_comp_cat_univ_code sum a b
        · comprehension_functor_mor
            (comp_cat_comprehension C)
            (cleaving_of_types _ _ _ _ _)
        =
        sum_in_comp_cat_univ_code
          sum
          (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
          (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        · PullbackPr1 (comp_cat_pullback _ _).
    Proof.
      pose (maponpaths pr1 (stable_sum_in_comp_cat_univ_code_stable sum s a b)) as p.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (!p).
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply subst_comp_cat_tm_pr1.
    Qed.

    Proposition stable_sum_in_comp_cat_univ_z_iso_stable
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : sum_in_comp_cat_univ_z_iso
           sum
           (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
           (b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        · comp_cat_comp_mor
            (comp_cat_el_map_on_eq el (!(stable_sum_in_comp_cat_univ_code_stable sum s a b))
             · inv_from_z_iso (comp_cat_univ_el_stable el s _))
        · comp_cat_extend_over _ s
        =
        comp_cat_comp_mor_over
          _
          (coprod_local_property_sum_functor
             HC
             (inv_from_z_iso (comp_cat_univ_el_stable el s a))
             (inv_from_z_iso (comp_cat_univ_el_stable el s b))
           · inv_from_z_iso (coprod_local_property_subst_z_iso HC s _ _))
        · sum_in_comp_cat_univ_z_iso sum a b.
    Proof.
      exact (pr2 (pr2 sum Γ Δ s a b)).
    Defined.

    Proposition stable_sum_in_comp_cat_univ_z_iso_stable_in1
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : comp_cat_comp_mor (inv_from_z_iso (comp_cat_univ_el_stable el s a))
        · comprehension_functor_mor
            (comp_cat_comprehension
               (dfl_full_comp_cat_with_univ_types C))
            (comp_cat_subst (comp_cat_univ_el el a) s
             ;; BinCoproductIn1
                  (coprod_local_property_bincoproduct
                     HC
                     (comp_cat_univ_el el a)
                     (comp_cat_univ_el el b)))
        · sum_in_comp_cat_univ_z_iso sum a b
        =
        comp_cat_comp_mor (BinCoproductIn1 (coprod_local_property_bincoproduct HC _ _))
        · comp_cat_comp_mor_over
            _
            (coprod_local_property_sum_functor
               HC
               (inv_from_z_iso (comp_cat_univ_el_stable el s a))
               (inv_from_z_iso (comp_cat_univ_el_stable el s b))
             · inv_from_z_iso (coprod_local_property_subst_z_iso HC s _ _))
        · sum_in_comp_cat_univ_z_iso sum a b.
    Proof.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!(comp_cat_comp_mor_comp _ _) @ _).
        apply maponpaths.
        etrans.
        {
          refine (assoc (C := fiber_category _ _) _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn1Commutes.
        }
        refine (assoc' (C := fiber_category _ _) _ _ _ @ _).
        apply maponpaths.
        apply BinCoproductIn1Commutes.
      }
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply comp_cat_comp_mor_comp.
        }
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply cartesian_factorisation_commutes.
        }
        apply comprehension_functor_mor_transportf.
      }
      apply idpath.
    Qed.

    Proposition stable_sum_in_comp_cat_univ_z_iso_stable_in2
                (sum : stable_sum_in_comp_cat_univ)
                {Γ Δ : C}
                (s : Γ --> Δ)
                (a b : tm Δ (dfl_full_comp_cat_univ Δ))
      : comp_cat_comp_mor (inv_from_z_iso (comp_cat_univ_el_stable el s b))
        · comprehension_functor_mor
            (comp_cat_comprehension
               (dfl_full_comp_cat_with_univ_types C))
            (comp_cat_subst (comp_cat_univ_el el b) s
             ;; BinCoproductIn2
                  (coprod_local_property_bincoproduct
                     HC
                     (comp_cat_univ_el el a)
                     (comp_cat_univ_el el b)))
        · sum_in_comp_cat_univ_z_iso sum a b
        =
        comp_cat_comp_mor (BinCoproductIn2 (coprod_local_property_bincoproduct HC _ _))
        · comp_cat_comp_mor_over
            _
            (coprod_local_property_sum_functor
               HC
               (inv_from_z_iso (comp_cat_univ_el_stable el s a))
               (inv_from_z_iso (comp_cat_univ_el_stable el s b))
             · inv_from_z_iso (coprod_local_property_subst_z_iso HC s _ _))
        · sum_in_comp_cat_univ_z_iso sum a b.
    Proof.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (!(comp_cat_comp_mor_comp _ _) @ _).
        apply maponpaths.
        etrans.
        {
          refine (assoc (C := fiber_category _ _) _ _ _ @ _).
          apply maponpaths_2.
          apply BinCoproductIn2Commutes.
        }
        refine (assoc' (C := fiber_category _ _) _ _ _ @ _).
        apply maponpaths.
        apply BinCoproductIn2Commutes.
      }
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply comp_cat_comp_mor_comp.
        }
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          exact (!(comprehension_functor_mor_comp _ _ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply cartesian_factorisation_commutes.
        }
        apply comprehension_functor_mor_transportf.
      }
      apply idpath.
    Qed.

    Proposition stable_sum_in_comp_cat_univ_eq
                {sum₁ sum₂ : stable_sum_in_comp_cat_univ}
                (p : ∏ (Γ : C)
                       (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                     sum_in_comp_cat_univ_code sum₁ a b
                     =
                     sum_in_comp_cat_univ_code sum₂ a b)
                (q : ∏ (Γ : C)
                       (a b : tm Γ (dfl_full_comp_cat_univ Γ)),
                     sum_in_comp_cat_univ_z_iso sum₁ a b
                     · comp_cat_comp_mor (comp_cat_el_map_on_eq el (p Γ a b))
                     =
                     sum_in_comp_cat_univ_z_iso sum₂ a b)
      : sum₁ = sum₂.
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_sum_in_comp_cat_univ_is_stable.
      }
      use sum_in_comp_cat_univ_eq.
      - exact p.
      - exact q.
    Qed.
  End SumCode.

  (** * 10. Codes for ∑-types *)
  Definition sigma_in_comp_cat_univ
    : UU
    := ∏ (Γ : C)
         (a : tm Γ (dfl_full_comp_cat_univ Γ))
         (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
       ∑ (sig : tm Γ (dfl_full_comp_cat_univ Γ))
         (f : z_iso
                (Γ & comp_cat_univ_el el sig)
                (Γ & comp_cat_univ_el el a & comp_cat_univ_el el b)),
       f · π _ · π _ = π _.

  Proposition isaset_sigma_in_comp_cat_univ
      : isaset sigma_in_comp_cat_univ.
  Proof.
    do 3 (use impred_isaset ; intro).
    use isaset_total2.
    - apply isaset_comp_cat_tm.
    - intro.
      use isaset_total2.
      + apply isaset_z_iso.
      + intro.
        apply isasetaprop.
        apply homset_property.
  Qed.

  Definition make_sigma_in_comp_cat_univ
             (sig : ∏ (Γ : C)
                      (a : tm Γ (dfl_full_comp_cat_univ Γ))
                      (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                    tm Γ (dfl_full_comp_cat_univ Γ))
             (f : ∏ (Γ : C)
                    (a : tm Γ (dfl_full_comp_cat_univ Γ))
                    (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                  z_iso
                    (Γ & comp_cat_univ_el el (sig Γ a b))
                    (Γ & comp_cat_univ_el el a & comp_cat_univ_el el b))
             (p : ∏ (Γ : C)
                    (a : tm Γ (dfl_full_comp_cat_univ Γ))
                    (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                  f Γ a b · π _ · π _ = π _)
    : sigma_in_comp_cat_univ
    := λ Γ a b, sig Γ a b ,, f Γ a b ,, p Γ a b.

  Definition sigma_in_comp_cat_univ_code
             (sig : sigma_in_comp_cat_univ)
             {Γ : C}
             (a : tm Γ (dfl_full_comp_cat_univ Γ))
             (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : tm Γ (dfl_full_comp_cat_univ Γ)
    := pr1 (sig Γ a b).

  Definition sigma_in_comp_cat_univ_z_iso
             (sig : sigma_in_comp_cat_univ)
             {Γ : C}
             (a : tm Γ (dfl_full_comp_cat_univ Γ))
             (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : z_iso
        (Γ & comp_cat_univ_el el (sigma_in_comp_cat_univ_code sig a b))
        (Γ & comp_cat_univ_el el a & comp_cat_univ_el el b)
    := pr12 (sig Γ a b).

  Proposition sigma_in_comp_cat_univ_comm
              (sig : sigma_in_comp_cat_univ)
              {Γ : C}
              (a : tm Γ (dfl_full_comp_cat_univ Γ))
              (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : sigma_in_comp_cat_univ_z_iso sig a b · π _ · π _ = π _.
  Proof.
    exact (pr22 (sig Γ a b)).
  Defined.

  Definition sigma_in_comp_cat_univ_z_iso_fiber
             (sig : sigma_in_comp_cat_univ)
             {Γ : C}
             (a : tm Γ (dfl_full_comp_cat_univ Γ))
             (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : z_iso
        (C := fiber_category _ _)
        (comp_cat_univ_el el (sigma_in_comp_cat_univ_code sig a b))
        (dfl_sigma_type
           (C := dfl_full_comp_cat_with_univ_types C)
           (comp_cat_univ_el el a)
           (comp_cat_univ_el el b)).
  Proof.
    use cod_iso_to_type_iso.
    - exact (z_iso_comp
               (sigma_in_comp_cat_univ_z_iso sig a b)
               (dfl_sigma_type_strong _ _)).
    - abstract
        (simpl ;
         rewrite !assoc' ;
         etrans ;
         [ apply maponpaths ;
           apply (dependent_sum_map_eq
                    (strong_dependent_sum_dfl_full_comp_cat
                       (dfl_full_comp_cat_with_univ_types C)))
         | ] ;
         rewrite !assoc ;
         exact (sigma_in_comp_cat_univ_comm sig a b)).
  Defined.

  Proposition sigma_in_comp_cat_univ_code_on_eq
              (sig : sigma_in_comp_cat_univ)
              {Γ : C}
              {a a' : tm Γ (dfl_full_comp_cat_univ Γ)}
              (p : a = a')
              {b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)}
              {b' : tm (Γ & comp_cat_univ_el el a') (dfl_full_comp_cat_univ _)}
              (q : comp_cat_comp_mor (comp_cat_el_map_on_eq el p)
                   · b'
                   =
                   b
                   · comp_cat_comp_mor_over_sub
                       (comp_cat_el_map_on_eq el p)
                       (sub_dfl_comp_cat_univ_inv (C := C) _))
    : sigma_in_comp_cat_univ_code sig a b
      =
      sigma_in_comp_cat_univ_code sig a' b'.
  Proof.
    induction p.
    enough (b = b') as ->.
    {
      apply idpath.
    }
    use eq_comp_cat_tm.
    refine (_ @ !q @ _).
    - refine (!(id_right _) @ _).
      apply maponpaths.
      refine (!_).
      use sub_dfl_comp_cat_univ_inv_on_id.
      apply idpath.
    - refine (_ @ id_left _).
      apply maponpaths_2.
      apply comp_cat_comp_mor_id.
  Qed.

  Proposition sigma_in_comp_cat_univ_code_on_eq'
              (sig : sigma_in_comp_cat_univ)
              {Γ : C}
              {a a' : tm Γ (dfl_full_comp_cat_univ Γ)}
              (p : a = a')
              {b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)}
              {b' : tm (Γ & comp_cat_univ_el el a') (dfl_full_comp_cat_univ _)}
              (q : comp_cat_comp_mor (comp_cat_el_map_on_eq el p)
                   · b'
                   =
                   b
                   · comp_cat_comp_mor_over_sub
                       (comp_cat_el_map_on_eq el p)
                       (sub_dfl_comp_cat_univ_inv (C := C) _))
    : (sigma_in_comp_cat_univ_code sig a b : _ --> _)
      =
      sigma_in_comp_cat_univ_code sig a' b'.
  Proof.
    exact (maponpaths pr1 (sigma_in_comp_cat_univ_code_on_eq sig p q)).
  Qed.

  Proposition sigma_in_comp_cat_univ_z_iso_on_eq
              {sig : sigma_in_comp_cat_univ}
              {Γ : C}
              {a a' : tm Γ (dfl_full_comp_cat_univ Γ)}
              (p : a = a')
              {b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)}
              {b' : tm (Γ & comp_cat_univ_el el a') (dfl_full_comp_cat_univ _)}
              (q : comp_cat_comp_mor (comp_cat_el_map_on_eq el p)
                   · b'
                   =
                   b
                   · comp_cat_comp_mor_over_sub
                       (comp_cat_el_map_on_eq el p)
                       (sub_dfl_comp_cat_univ_inv (C := C) _))
    : sigma_in_comp_cat_univ_z_iso sig a b
      · comp_cat_comp_mor_over_sub
          (comp_cat_el_map_on_eq el p)
          (comp_cat_el_map_on_eq
             el
             (dfl_full_comp_cat_with_univ_dep_ty_eq p q)
           · inv_from_z_iso (comp_cat_univ_el_stable el _ b'))
      =
      comp_cat_comp_mor
        (comp_cat_el_map_on_eq
           el
           (sigma_in_comp_cat_univ_code_on_eq sig p q))
      · sigma_in_comp_cat_univ_z_iso sig a' b'.
  Proof.
    induction p ; simpl.
    refine (!_).
    assert (b = b') as r.
    {
      use eq_comp_cat_tm.
      refine (_ @ !q @ _).
      - refine (!(id_right _) @ _).
        apply maponpaths.
        refine (!_).
        use sub_dfl_comp_cat_univ_inv_on_id.
        apply idpath.
      - refine (_ @ id_left _).
        apply maponpaths_2.
        apply comp_cat_comp_mor_id.
    }
    induction r.
    etrans.
    {
      apply maponpaths_2.
      refine (_ @ comp_cat_comp_mor_id _).
      apply maponpaths.
      exact (comp_cat_el_map_on_idpath el _).
    }
    rewrite id_left.
    refine (!(id_right _) @ _).
    apply maponpaths.
    refine (!_).
    refine (!(comprehension_functor_mor_comp _ _ _) @ _).
    cbn.
    rewrite mor_disp_transportf_postwhisker.
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      refine (comp_cat_univ_el_stable_id_coh_inv_alt el _ _ _).
      refine (!_).
      apply comp_cat_comp_mor_id.
    }
    cbn -[id_subst_ty eq_subst_ty].
    rewrite mor_disp_transportf_postwhisker.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite !comprehension_functor_mor_transportf.
    rewrite !assoc_disp_var.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !comprehension_functor_mor_transportf.
    etrans.
    {
      do 4 apply maponpaths.
      apply subst_ty_eq_disp_iso_comm.
    }
    rewrite !mor_disp_transportf_prewhisker.
    rewrite !comprehension_functor_mor_transportf.
    etrans.
    {
      do 3 apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    unfold transportb.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite comprehension_functor_mor_transportf.
    rewrite id_right_disp.
    unfold transportb.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      apply maponpaths.
      exact (comp_cat_el_map_on_disp_concat el _ _).
    }
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      apply maponpaths.
      exact (comp_cat_el_map_on_idpath el _).
    }
    apply comprehension_functor_mor_id.
  Qed.

  Proposition sigma_in_comp_cat_univ_z_iso_on_eq'
              {sig : sigma_in_comp_cat_univ}
              {Γ : C}
              {a a' : tm Γ (dfl_full_comp_cat_univ Γ)}
              (p : a = a')
              {b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)}
              {b' : tm (Γ & comp_cat_univ_el el a') (dfl_full_comp_cat_univ _)}
              (q : comp_cat_comp_mor (comp_cat_el_map_on_eq el p)
                   · b'
                   =
                   b
                   · comp_cat_comp_mor_over_sub
                       (comp_cat_el_map_on_eq el p)
                       (sub_dfl_comp_cat_univ_inv (C := C) _))
    : comp_cat_comp_mor
        (comp_cat_el_map_on_eq
           el
           (!(sigma_in_comp_cat_univ_code_on_eq sig p q)))
      · sigma_in_comp_cat_univ_z_iso sig a b
      · comp_cat_comp_mor_over_sub
          (comp_cat_el_map_on_eq el p)
          (comp_cat_el_map_on_eq
             el
             (dfl_full_comp_cat_with_univ_dep_ty_eq p q)
           · inv_from_z_iso (comp_cat_univ_el_stable el _ b'))
      =
      sigma_in_comp_cat_univ_z_iso sig a' b'.
  Proof.
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      exact (sigma_in_comp_cat_univ_z_iso_on_eq p q).
    }
    rewrite assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!(comp_cat_comp_mor_comp _ _) @ _ @ comp_cat_comp_mor_id _).
      apply maponpaths.
      refine (!(comp_cat_el_map_on_concat el _ _) @ _).
      apply (comp_cat_el_map_on_idpath el).
    }
    apply id_left.
  Qed.

  Proposition sigma_in_comp_cat_univ_eq
              {sig₁ sig₂ : sigma_in_comp_cat_univ}
              (p : ∏ (Γ : C)
                     (a : tm Γ (dfl_full_comp_cat_univ Γ))
                     (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                   sigma_in_comp_cat_univ_code sig₁ a b
                   =
                   sigma_in_comp_cat_univ_code sig₂ a b)
              (q : ∏ (Γ : C)
                     (a : tm Γ (dfl_full_comp_cat_univ Γ))
                     (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                   comp_cat_comp_mor (comp_cat_el_map_on_eq el (!(p Γ a b)))
                   · sigma_in_comp_cat_univ_z_iso sig₁ a b
                   =
                   sigma_in_comp_cat_univ_z_iso sig₂ a b)
      : sig₁ = sig₂.
  Proof.
    use funextsec ; intro Γ.
    use funextsec ; intro a.
    use funextsec ; intro b.
    use total2_paths_f.
    - exact (p Γ a b).
    - use subtypePath.
      {
        intro.
        apply homset_property.
      }
      rewrite pr1_transportf.
      use z_iso_eq.
      etrans.
      {
        apply (pr1_transportf
                 (P := λ (x : tm Γ (dfl_full_comp_cat_univ Γ))
                         (f : Γ & comp_cat_univ_el el x --> _),
                    is_z_isomorphism _)).
      }
      etrans.
      {
        exact (transportf_comp_cat_univ_el el _ _).
      }
      exact (q Γ a b).
  Qed.

  Definition sigma_in_comp_cat_univ_is_stable
             (sig : sigma_in_comp_cat_univ)
    : UU
    := ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (a : tm Δ (dfl_full_comp_cat_univ _))
         (b : tm (Δ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
       ∑ (p : sigma_in_comp_cat_univ_code sig a b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
              =
              sigma_in_comp_cat_univ_code sig
                (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
                (b [[ extend_sub_univ el s a ]]tm ↑ sub_dfl_comp_cat_univ _)),
       sigma_in_comp_cat_univ_z_iso sig _ _
       · comp_cat_comp_mor_over_sub
           (comp_cat_univ_el_stable_inv el _ _)
           (comp_cat_univ_el_stable_inv el _ _ · comp_subst_ty_inv _ _ _)
       · comp_cat_extend_over _ (comp_cat_extend_over _ s)
       =
       comp_cat_comp_mor_over
         _
         (comp_cat_el_map_on_eq el (!p)
          · comp_cat_univ_el_stable_inv el s _)
       · sigma_in_comp_cat_univ_z_iso sig a b.

  Proposition isaprop_sigma_in_comp_cat_univ_is_stable
              (sig : sigma_in_comp_cat_univ)
    : isaprop (sigma_in_comp_cat_univ_is_stable sig).
  Proof.
    do 5 (use impred ; intro).
    use isaproptotal2.
    - intro.
      apply homset_property.
    - intros.
      apply isaset_comp_cat_tm.
  Qed.

  Definition stable_sigma_in_comp_cat_univ
    : UU
    := ∑ (sig : sigma_in_comp_cat_univ),
       sigma_in_comp_cat_univ_is_stable sig.

  Definition make_stable_sigma_in_comp_cat_univ
             (sig : sigma_in_comp_cat_univ)
             (H : sigma_in_comp_cat_univ_is_stable sig)
    : stable_sigma_in_comp_cat_univ
    := sig ,, H.

  Proposition isaset_stable_sigma_in_comp_cat_univ
    : isaset stable_sigma_in_comp_cat_univ.
  Proof.
    use isaset_total2.
    - exact isaset_sigma_in_comp_cat_univ.
    - intro x.
      apply isasetaprop.
      apply isaprop_sigma_in_comp_cat_univ_is_stable.
  Qed.

  Coercion stable_sigma_in_comp_cat_univ_to_codes
           (sig : stable_sigma_in_comp_cat_univ)
    : sigma_in_comp_cat_univ
    := pr1 sig.

  Proposition stable_sigma_in_comp_cat_univ_code_stable
              (sig : stable_sigma_in_comp_cat_univ)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : tm Δ (dfl_full_comp_cat_univ _))
              (b : tm (Δ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : sigma_in_comp_cat_univ_code sig a b [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
      =
      sigma_in_comp_cat_univ_code sig
        (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        (b [[ extend_sub_univ el s a ]]tm ↑ sub_dfl_comp_cat_univ _).
  Proof.
    exact (pr1 (pr2 sig Γ Δ s a b)).
  Defined.

  Proposition stable_sigma_in_comp_cat_univ_code_stable_mor
              (sig : stable_sigma_in_comp_cat_univ)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : tm Δ (dfl_full_comp_cat_univ _))
              (b : tm (Δ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : s
      · sigma_in_comp_cat_univ_code sig a b
      · comprehension_functor_mor
          (comp_cat_comprehension C)
          (cleaving_of_types _ _ _ _ _)
      =
      sigma_in_comp_cat_univ_code sig
        (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
        (b [[ extend_sub_univ el s a ]]tm ↑ sub_dfl_comp_cat_univ _)
      · PullbackPr1 (comp_cat_pullback _ _).
  Proof.
    pose (maponpaths pr1 (stable_sigma_in_comp_cat_univ_code_stable sig s a b)) as p.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!p).
    }
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    apply subst_comp_cat_tm_pr1.
  Qed.

  Proposition stable_sigma_in_comp_cat_univ_z_iso_stable
              (sig : stable_sigma_in_comp_cat_univ)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : tm Δ (dfl_full_comp_cat_univ _))
              (b : tm (Δ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _))
    : sigma_in_comp_cat_univ_z_iso sig _ _
     · comp_cat_comp_mor_over_sub
         (comp_cat_univ_el_stable_inv el _ _)
         (comp_cat_univ_el_stable_inv el _ _ · comp_subst_ty_inv _ _ _)
     · comp_cat_extend_over _ (comp_cat_extend_over _ s)
     =
     comp_cat_comp_mor_over
       _
       (comp_cat_el_map_on_eq el (!(stable_sigma_in_comp_cat_univ_code_stable sig s a b))
        · comp_cat_univ_el_stable_inv el s _)
     · sigma_in_comp_cat_univ_z_iso sig a b.
  Proof.
    exact (pr2 (pr2 sig Γ Δ s a b)).
  Defined.

  Proposition stable_sigma_in_comp_cat_univ_eq
              {sig₁ sig₂ : stable_sigma_in_comp_cat_univ}
              (p : ∏ (Γ : C)
                     (a : tm Γ (dfl_full_comp_cat_univ Γ))
                     (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                   sigma_in_comp_cat_univ_code sig₁ a b
                   =
                   sigma_in_comp_cat_univ_code sig₂ a b)
              (q : ∏ (Γ : C)
                     (a : tm Γ (dfl_full_comp_cat_univ Γ))
                     (b : tm (Γ & comp_cat_univ_el el a) (dfl_full_comp_cat_univ _)),
                   comp_cat_comp_mor (comp_cat_el_map_on_eq el (!(p Γ a b)))
                   · sigma_in_comp_cat_univ_z_iso sig₁ a b
                   =
                   sigma_in_comp_cat_univ_z_iso sig₂ a b)
      : sig₁ = sig₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_sigma_in_comp_cat_univ_is_stable.
    }
    use sigma_in_comp_cat_univ_eq.
    - exact p.
    - exact q.
  Qed.
End TypesInCompCatUniv.

Arguments type_in_comp_cat_univ {C} A.
Arguments type_in_comp_cat_univ_code {C A} a.
Arguments type_in_comp_cat_univ_z_iso {C A} a.
Arguments type_in_comp_cat_univ_z_iso_fiber {C A} a.

Arguments resizing_in_comp_cat_univ_code {C} resize {Γ} A HA.
Arguments resizing_in_comp_cat_univ_z_iso {C} resize {Γ} A HA.
Arguments resizing_in_comp_cat_univ_comm {C} resize {Γ} A HA.
Arguments resizing_in_comp_cat_univ_z_iso_fiber {C} resize {Γ} A HA.
Arguments stable_resizing_in_comp_cat_univ_code_stable {C} resize {Γ Δ} s A HA.
Arguments resizing_in_comp_cat_univ_code_on_eq {C} resize {Γ A B} p HA HB.
Arguments resizing_in_comp_cat_univ_code_on_z_iso_fib {C} resize {Γ A B} p HA HB.
Arguments resizing_in_comp_cat_univ_code_on_z_iso {C} resize {Γ A B} f p HA HB.
Arguments stable_resizing_in_comp_cat_univ_code_stable_mor {C} resize {Γ Δ} s A HA.
Arguments stable_resizing_in_comp_cat_univ_code_stable_mor' {C} resize {Γ Δ} s A HA.

Arguments ext_id_in_comp_cat_univ_code {C} eq {Γ a} t₁ t₂.
Arguments ext_id_in_comp_cat_univ_z_iso {C} eq {Γ a} t₁ t₂.
Arguments ext_id_in_comp_cat_univ_comm {C} eq {Γ a} t₁ t₂.
Arguments ext_id_in_comp_cat_univ_z_iso_fiber {C} eq {Γ a} t₁ t₂.
Arguments stable_ext_id_in_comp_cat_univ_code_stable {C} eq {Γ Δ} s {a} t₁ t₂.
Arguments stable_ext_id_in_comp_cat_univ_code_stable_mor {C} eq {Γ Δ} s {a} t₁ t₂.
Arguments ext_id_in_comp_cat_univ_code_on_eq {C} eq {Γ a a'} {t₁ t₂ t₁' t₂'} p q r.
Arguments ext_id_in_comp_cat_univ_code_on_eq' {C} eq {Γ a a'} {t₁ t₂ t₁' t₂'} p q r.

Arguments truncation_in_comp_cat_univ_code {C} HC trunc {Γ} a.
Arguments truncation_in_comp_cat_univ_z_iso {C} HC trunc {Γ} a.
Arguments truncation_in_comp_cat_univ_comm {C} HC trunc {Γ} a.
Arguments truncation_in_comp_cat_univ_z_iso_fiber {C} HC trunc {Γ} a.
Arguments stable_truncation_in_comp_cat_univ_code_stable {C} HC trunc {Γ Δ} s a.

Arguments sum_in_comp_cat_univ_code {C} HC sum {Γ} a b.
Arguments sum_in_comp_cat_univ_z_iso {C} HC sum {Γ} a b.
Arguments sum_in_comp_cat_univ_comm {C} HC sum {Γ} a b.
Arguments sum_in_comp_cat_univ_z_iso_fiber {C} HC sum {Γ} a b.
Arguments stable_sum_in_comp_cat_univ_code_stable {C} HC sum {Γ Δ} s a b.
Arguments stable_sum_in_comp_cat_univ_z_iso_stable {C} HC sum {Γ Δ} s a b.

Arguments sigma_in_comp_cat_univ_code {C} sig {Γ} a b.
Arguments sigma_in_comp_cat_univ_z_iso {C} sig {Γ} a b.
Arguments sigma_in_comp_cat_univ_comm {C} sig {Γ} a b.
Arguments sigma_in_comp_cat_univ_z_iso_fiber {C} sig {Γ} a b.
Arguments stable_sigma_in_comp_cat_univ_code_stable {C} sig {Γ Δ} s a b.
Arguments stable_sigma_in_comp_cat_univ_z_iso_stable {C} sig {Γ Δ} s a b.
