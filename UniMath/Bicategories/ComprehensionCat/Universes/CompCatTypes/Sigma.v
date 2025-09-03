(**

 ∑-types in comprehension categories

 We defined when a comprehension category is equipped with a universe type, and we constructed
 a biequivalence between the bicategory of univalent DFL full comprehension categories with a
 universe type and the bicategory of univalent categories with finite limits and a universe
 type. Our next goal is to extended this biequivalence to cover universes that are closed under
 certain type formers as well. We consider various type formers, and these are given in various
 files. In this file, we consider codes for ∑-types. We use the same ideas for each type former,
 and these are explained in the file `Constant.v`

 Contents
 1. Codes for ∑-types
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

  (** * 1. Codes for ∑-types *)
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

  (** * 2. Accessors and builders *)
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

  (** * 3. Stability *)
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

Arguments sigma_in_comp_cat_univ_code {C} sig {Γ} a b.
Arguments sigma_in_comp_cat_univ_z_iso {C} sig {Γ} a b.
Arguments sigma_in_comp_cat_univ_comm {C} sig {Γ} a b.
Arguments sigma_in_comp_cat_univ_z_iso_fiber {C} sig {Γ} a b.
Arguments stable_sigma_in_comp_cat_univ_code_stable {C} sig {Γ Δ} s a b.
Arguments stable_sigma_in_comp_cat_univ_z_iso_stable {C} sig {Γ Δ} s a b.
