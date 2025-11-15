(**

 Extensional identity types in comprehension categories

 We defined when a comprehension category is equipped with a universe type, and we constructed
 a biequivalence between the bicategory of univalent DFL full comprehension categories with a
 universe type and the bicategory of univalent categories with finite limits and a universe
 type. Our next goal is to extended this biequivalence to cover universes that are closed under
 certain type formers as well. We consider various type formers, and these are given in various
 files. In this file, we consider codes for extensional identity types. We use the same ideas
 for each type former, and these are explained in the file `Constant.v`

 Contents
 1. Codes for extensional identity types
 2. Accessors and builders
 3. Stability

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
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

  (** * 1. Codes for extensional identity types *)
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

  (** * 2. Accessors and builders *)
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

  (** * 3. Stability *)
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

End TypesInCompCatUniv.

Arguments ext_id_in_comp_cat_univ_code {C} eq {Γ a} t₁ t₂.
Arguments ext_id_in_comp_cat_univ_z_iso {C} eq {Γ a} t₁ t₂.
Arguments ext_id_in_comp_cat_univ_comm {C} eq {Γ a} t₁ t₂.
Arguments ext_id_in_comp_cat_univ_z_iso_fiber {C} eq {Γ a} t₁ t₂.
Arguments stable_ext_id_in_comp_cat_univ_code_stable {C} eq {Γ Δ} s {a} t₁ t₂.
Arguments stable_ext_id_in_comp_cat_univ_code_stable_mor {C} eq {Γ Δ} s {a} t₁ t₂.
Arguments ext_id_in_comp_cat_univ_code_on_eq {C} eq {Γ a a'} {t₁ t₂ t₁' t₂'} p q r.
Arguments ext_id_in_comp_cat_univ_code_on_eq' {C} eq {Γ a a'} {t₁ t₂ t₁' t₂'} p q r.
