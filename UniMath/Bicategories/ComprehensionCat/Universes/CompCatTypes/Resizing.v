(**

 Resizing in comprehension categories

 We defined when a comprehension category is equipped with a universe type, and we constructed
 a biequivalence between the bicategory of univalent DFL full comprehension categories with a
 universe type and the bicategory of univalent categories with finite limits and a universe
 type. Our next goal is to extended this biequivalence to cover universes that are closed under
 certain type formers as well. We consider various type formers, and these are given in various
 files. In this file, we consider codes for propositional resizing. We use the same ideas for
 each type former, and these are explained in the file `Constant.v`

 Contents
 1. Codes for propositional resizing
 2. Accessors and builders
 3. Stability

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
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
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.HPropMono.
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

  (** * 1. Codes for propositional resizing *)
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

  (** * 2. Accessors and builders *)
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

  (** * 3. Stability *)
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
End TypesInCompCatUniv.

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
