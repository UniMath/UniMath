(**

 Constructions of codes for extensional identity types in universes

 We have defined what it means for a universe in a category with finite limits and for a
 universe in a comprehension category to support extensional identity types. Our goal is to
 connect these two notions. To do so, we use the biequivalence between categories with finite
 limits and a universe and DFL full comprehension categories with a universe. Specifically, we
 showed that if `C` is a comprehension category with a universe `u`, then its category of
 contexts also has a universe. We construct an equivalence between the type that expresses
 that `C` supports extensional identity types and the type that the universe in the category of
 contexts supports extensional identity types. There are some calculational challenges in this
 development, and we comment on them in this file.

 Contents
 1. Preliminary material
 2. Construction of codes in the category of contexts
 3. Construction of codes in the comprehension category
 4. Equivalence

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionEso.
Require Import UniMath.Bicategories.ComprehensionCat.ComprehensionPreservation.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.FinLimToCompCatLemmas.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatTypes.Identity.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Identity.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

(** 1. Preliminary material *)

(**
   One of the goals in this file, is to show that a universe in a comprehension category
   supports extensional identity types if the universe in its category of contexts does so.
   This requires us to construct suitable sections from terms. More specifically, we are
   given a type in the universe and a term of that type, and we construct a section. This
   section is exactly what can be used to construct the desired identity types. We do this
   in [stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_code].
 *)
Definition dfl_full_comp_cat_with_univ_to_section
           {C : dfl_full_comp_cat_with_univ}
           {Γ : C}
           {a : tm Γ (dfl_full_comp_cat_univ Γ)}
           (t : tm Γ (comp_cat_univ_el (dfl_full_comp_cat_el C) a))
  : section_of_mor
      (cat_el_map_mor
         (univ_cat_cat_stable_el_map
            (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
         (dfl_full_comp_cat_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) a)).
Proof.
  use make_section_of_mor.
  - refine (pr1 t · comp_cat_comp_mor (comp_cat_el_map_on_eq (dfl_full_comp_cat_el C) _)).
    apply (!dfl_full_comp_cat_tm_to_mor_to_tm_univ _ a).
  - abstract
      (refine (assoc' _ _ _ @ _) ;
       etrans ;
       [ apply maponpaths ;
         apply comp_cat_comp_mor_comm
       | ] ;
       apply comp_cat_tm_eq).
Defined.

(**
   The following lemmas will be useful in the remainder of this file. They express
   how certain operations on terms interact with the previously mentioned construction
   of sections from terms.
 *)
Proposition dfl_full_comp_cat_tm_to_mor_on_section
            {C : dfl_full_comp_cat_with_univ}
            {Γ : C}
            {a : tm Γ (dfl_full_comp_cat_univ Γ)}
            (t : tm Γ (comp_cat_univ_el (dfl_full_comp_cat_el C) a))
  : dfl_full_comp_cat_tm_to_mor
      (C := dfl_full_comp_cat_with_univ_types C)
      (dfl_full_comp_cat_with_univ_to_section t)
    =
    dfl_full_comp_cat_tm_to_mor t
    · comp_cat_el_map_on_eq_iso
        (dfl_full_comp_cat_el C)
        (!(dfl_full_comp_cat_tm_to_mor_to_tm_univ _ a)).
Proof.
  use (invmaponpathsweq (dfl_full_comp_cat_tm_weq_mor _)).
  etrans.
  {
    apply dfl_full_comp_cat_tm_to_mor_to_tm.
  }
  use eq_section_of_mor.
  simpl.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    apply comprehension_functor_mor_comp.
  }
  rewrite !assoc.
  apply maponpaths_2.
  exact (maponpaths pr1 (dfl_full_comp_cat_tm_to_mor_to_tm t)).
Qed.

Proposition dfl_full_comp_cat_tm_to_mor_on_section'
            {C : dfl_full_comp_cat_with_univ}
            {Γ : C}
            {a : tm Γ (dfl_full_comp_cat_univ Γ)}
            (t : tm Γ (comp_cat_univ_el (dfl_full_comp_cat_el C) a))
  : dfl_full_comp_cat_tm_to_mor t
    =
    dfl_full_comp_cat_tm_to_mor
      (C := dfl_full_comp_cat_with_univ_types C)
      (dfl_full_comp_cat_with_univ_to_section t)
    · comp_cat_el_map_on_eq_iso
        (dfl_full_comp_cat_el C)
        (dfl_full_comp_cat_tm_to_mor_to_tm_univ _ a).
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply dfl_full_comp_cat_tm_to_mor_on_section.
  }
  rewrite assoc'.
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply (comp_cat_el_map_on_concat (dfl_full_comp_cat_el C)).
  }
  etrans.
  {
    apply maponpaths.
    apply (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C)).
  }
  apply id_right.
Qed.

Proposition dfl_full_comp_cat_with_univ_to_section_subst
            {C : dfl_full_comp_cat_with_univ}
            {Γ Δ : C}
            (s : Γ --> Δ)
            {a : tm Δ (dfl_full_comp_cat_univ Δ)}
            (t : tm Δ (comp_cat_univ_el (dfl_full_comp_cat_el C) a))
  : pr1 (dfl_full_comp_cat_with_univ_to_section t [[ s ]]tm)
    =
    t [[ s ]]tm
    · comp_cat_comp_mor
        (coerce_subst_ty
           s
           (comp_cat_el_map_on_eq
              (dfl_full_comp_cat_el C)
              (!(dfl_full_comp_cat_tm_to_mor_to_tm_univ _ a)))).
Proof.
  use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback _ _))).
  - etrans.
    {
      apply PullbackArrow_PullbackPr1.
    }
    refine (!_).
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      refine (_ @ comprehension_functor_mor_comp _ _ _).
      refine (!_).
      apply maponpaths.
      apply cartesian_factorisation_commutes.
    }
    rewrite comprehension_functor_mor_transportf.
    rewrite comprehension_functor_mor_comp.
    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply subst_comp_cat_tm_pr1.
    }
    refine (assoc' _ _ _ @ _).
    apply idpath.
  - etrans.
    {
      apply PullbackArrow_PullbackPr2.
    }
    refine (!_).
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      apply comp_cat_comp_mor_comm.
    }
    apply comp_cat_tm_eq.
Qed.

Proposition dfl_full_comp_cat_with_univ_to_section_subst_cat_univ_tm
            {C : dfl_full_comp_cat_with_univ}
            {Γ Δ : C}
            (s : Γ --> Δ)
            {a : tm Δ (dfl_full_comp_cat_univ Δ)}
            (t : tm Δ (comp_cat_univ_el (dfl_full_comp_cat_el C) a))
  : dfl_full_comp_cat_with_univ_to_section
      (C := C)
      (t [[ s ]]tm ↑ comp_cat_univ_el_stable_mor (dfl_full_comp_cat_el C) s a)
    · cat_el_map_el_eq
        (univ_cat_cat_stable_el_map (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
        (dfl_full_comp_cat_tm_to_mor_univ_subst s a)
    =
    subst_cat_univ_tm
      (univ_cat_cat_stable_el_map (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)) s
      (dfl_full_comp_cat_tm_to_mor_univ (dfl_full_comp_cat_univ_ob C) a)
      (dfl_full_comp_cat_with_univ_to_section t).
Proof.
  refine (_ @ maponpaths pr1 (subst_cat_univ_tm_dfl_full_comp_cat_to_finlim s _ _)).
  refine (assoc' _ _ _ @ _ @ assoc _ _ _).
  refine (assoc' _ _ _ @ _).
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    exact (dfl_full_comp_cat_with_univ_to_section_subst s t).
  }
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply comprehension_functor_mor_comp.
  }
  refine (!(comprehension_functor_mor_comp _ _ _) @ _).
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    apply (dfl_full_comp_cat_cat_el_map_el_eq
             (C := dfl_full_comp_cat_with_univ_types C)).
  }
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply comprehension_functor_mor_comp.
  }
  refine (!(comprehension_functor_mor_comp _ _ _) @ _).
  refine (!_).
  etrans.
  {
    rewrite assoc_disp.
    unfold transportb.
    rewrite comprehension_functor_mor_transportf.
    apply maponpaths.
    apply maponpaths_2.
    refine (!_).
    exact (comp_cat_univ_el_stable_natural_disp (dfl_full_comp_cat_el C) _ _).
  }
  rewrite assoc_disp_var.
  rewrite comprehension_functor_mor_transportf.
  etrans.
  {
    do 2 apply maponpaths.
    exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
  }
  rewrite mor_disp_transportf_prewhisker.
  rewrite comprehension_functor_mor_transportf.
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    exact (comp_cat_el_map_on_disp_concat (dfl_full_comp_cat_el C) _ _).
  }
  rewrite mor_disp_transportf_prewhisker.
  rewrite comprehension_functor_mor_transportf.
  do 2 apply maponpaths.
  apply (eq_comp_cat_el_map_on_eq (dfl_full_comp_cat_el C)).
Qed.

Section ExtId.
  Context {C : dfl_full_comp_cat_with_univ}.

  Let Cu : univ_cat_with_finlim_universe
    := dfl_full_comp_cat_with_univ_to_univ_cat_finlim C.

  (** * 2. Construction of codes in the category of contexts *)
  Section Code.
    Context (eq : stable_ext_id_in_comp_cat_univ C)
            {Γ : dfl_full_comp_cat_with_univ_to_univ_cat_finlim C}
            {a : Γ
                 -->
                 univ_cat_universe (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)}
            (t₁ t₂ : section_of_mor
                       (cat_el_map_mor
                          (univ_cat_cat_stable_el_map
                             (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
                          a)).

    Definition ext_id_in_dfl_full_comp_cat_to_finlim_univ_code
      : Γ
        -->
        univ_cat_universe (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C).
    Proof.
      use (dfl_full_comp_cat_tm_to_mor_univ
             (C := dfl_full_comp_cat_with_univ_types C)).
      exact (ext_id_in_comp_cat_univ_code eq t₁ t₂).
    Defined.

    Definition ext_id_in_dfl_full_comp_cat_to_finlim_univ_z_iso
      : z_iso
          (cat_el_map_el
             (dfl_full_comp_cat_to_finlim_el_map
                (dfl_full_comp_cat_univ_ob C)
                (dfl_full_comp_cat_el C))
             ext_id_in_dfl_full_comp_cat_to_finlim_univ_code)
          (equalizers_univ_cat_with_finlim
             (dfl_full_comp_cat_to_finlim (dfl_full_comp_cat_with_univ_types C))
             Γ
             (cat_el_map_el
                (dfl_full_comp_cat_to_finlim_el_map (dfl_full_comp_cat_univ_ob C)
                   (dfl_full_comp_cat_el C))
                a)
             t₁ t₂).
    Proof.
      refine (z_iso_comp
                (z_iso_comp _ (ext_id_in_comp_cat_univ_z_iso eq t₁ t₂)) _).
      - use comp_cat_comp_fiber_z_iso.
        use (comp_cat_el_map_on_eq_iso (dfl_full_comp_cat_el C)).
        apply (dfl_full_comp_cat_tm_to_mor_to_tm_univ
                 (dfl_full_comp_cat_univ_ob C)).
      - apply comprehension_preserves_ext_id_z_iso.
    Defined.

    Proposition ext_id_in_dfl_full_comp_cat_to_finlim_univ_comm
      : ext_id_in_dfl_full_comp_cat_to_finlim_univ_z_iso
        · EqualizerArrow
            (equalizers_univ_cat_with_finlim
               (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
               Γ
               (cat_el_map_el
                  (univ_cat_cat_stable_el_map
                     (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
                  a)
               t₁ t₂)
        =
        cat_el_map_mor
          (univ_cat_cat_stable_el_map
             (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
          (ext_id_in_dfl_full_comp_cat_to_finlim_univ_code).
    Proof.
      do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        apply comprehension_preserves_ext_id_z_iso_comm.
      }
      etrans.
      {
        apply maponpaths.
        apply ext_id_in_comp_cat_univ_comm.
      }
      etrans.
      {
        apply comprehension_functor_mor_comm.
      }
      apply id_right.
    Qed.
  End Code.

  Definition ext_id_in_dfl_full_comp_cat_to_finlim_univ
             (eq : stable_ext_id_in_comp_cat_univ C)
    : cat_univ_codes_ext_id (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C).
  Proof.
    use make_cat_univ_codes_ext_id.
    - intros Γ a t₁ t₂.
      exact (ext_id_in_dfl_full_comp_cat_to_finlim_univ_code eq t₁ t₂).
    - intros Γ a t₁ t₂.
      exact (ext_id_in_dfl_full_comp_cat_to_finlim_univ_z_iso eq t₁ t₂).
    - intros Γ a t₁ t₂.
      exact (ext_id_in_dfl_full_comp_cat_to_finlim_univ_comm eq t₁ t₂).
  Defined.

  Proposition ext_id_in_dfl_full_comp_cat_to_finlim_univ_is_stable
              (eq : stable_ext_id_in_comp_cat_univ C)
    : is_stable_cat_univ_codes_ext_id
        (ext_id_in_dfl_full_comp_cat_to_finlim_univ eq).
  Proof.
    intros Γ Δ s a t₁ t₂.
    refine (assoc _ _ _ @ _).
    etrans.
    {
      exact (stable_ext_id_in_comp_cat_univ_code_stable_mor eq s t₁ t₂).
    }
    refine (maponpaths (λ z, z · _) _).
    use ext_id_in_comp_cat_univ_code_on_eq'.
    - exact (dfl_full_comp_cat_mor_to_sub_tm (dfl_full_comp_cat_univ_ob C) s a).
    - exact (subst_cat_univ_tm_dfl_full_comp_cat_to_finlim s a t₁).
    - exact (subst_cat_univ_tm_dfl_full_comp_cat_to_finlim s a t₂).
  Qed.

  Definition stable_ext_id_in_dfl_full_comp_cat_to_finlim_univ
              (eq : stable_ext_id_in_comp_cat_univ C)
    : cat_univ_stable_codes_ext_id
        (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C).
  Proof.
    use make_cat_univ_stable_codes_ext_id.
    - exact (ext_id_in_dfl_full_comp_cat_to_finlim_univ eq).
    - exact (ext_id_in_dfl_full_comp_cat_to_finlim_univ_is_stable eq).
  Defined.

  (** * 3. Construction of codes in the comprehension category *)
  Section Code.
    Context (eq : cat_univ_stable_codes_ext_id
                    (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
            {Γ : C}
            {a : tm Γ (dfl_full_comp_cat_univ Γ)}
            (t₁ t₂ : tm Γ (comp_cat_univ_el (dfl_full_comp_cat_el C) a)).

    Definition stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_code
      : tm Γ (dfl_full_comp_cat_univ Γ).
    Proof.
      use (dfl_full_comp_cat_mor_to_tm_univ
             (C := dfl_full_comp_cat_with_univ_types C)).
      exact (cat_univ_ext_id eq
               (dfl_full_comp_cat_with_univ_to_section t₁)
               (dfl_full_comp_cat_with_univ_to_section t₂)).
    Defined.

    (**
       We need to show that the code gives a type isomorphic to the identity of `t₁`
       and `t₂`. For that, we need the following isomorphism.
     *)
    Definition dfl_ext_identity_section_mor
      : dfl_ext_identity
          (C := dfl_full_comp_cat_with_univ_types C)
          (dfl_full_comp_cat_with_univ_to_section t₁)
          (dfl_full_comp_cat_with_univ_to_section t₂)
        -->
        dfl_ext_identity t₁ t₂.
    Proof.
      use EqualizerIn.
      - exact (EqualizerArrow _).
      - abstract
          (rewrite (dfl_full_comp_cat_tm_to_mor_on_section' t₁) ;
           rewrite (dfl_full_comp_cat_tm_to_mor_on_section' t₂) ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply EqualizerEqAr).
    Defined.

    Definition dfl_ext_identity_section_inv
      : dfl_ext_identity t₁ t₂
        -->
        dfl_ext_identity
          (C := dfl_full_comp_cat_with_univ_types C)
          (dfl_full_comp_cat_with_univ_to_section t₁)
          (dfl_full_comp_cat_with_univ_to_section t₂).
    Proof.
      use EqualizerIn.
      - exact (EqualizerArrow _).
      - abstract
          (rewrite (dfl_full_comp_cat_tm_to_mor_on_section t₁) ;
           rewrite (dfl_full_comp_cat_tm_to_mor_on_section t₂) ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           apply EqualizerEqAr).
    Defined.

    Proposition dfl_ext_identity_section_iso_inverses
      : is_inverse_in_precat
          dfl_ext_identity_section_mor
          dfl_ext_identity_section_inv.
    Proof.
      split.
      - use EqualizerInsEq.
        unfold dfl_ext_identity_section_mor, dfl_ext_identity_section_inv.
        rewrite !assoc'.
        rewrite !EqualizerCommutes.
        rewrite id_left.
        apply idpath.
      - use EqualizerInsEq.
        unfold dfl_ext_identity_section_mor, dfl_ext_identity_section_inv.
        rewrite !assoc'.
        rewrite !EqualizerCommutes.
        rewrite id_left.
        apply idpath.
    Qed.

    Definition dfl_ext_identity_section_iso
      : z_iso
          (dfl_ext_identity
             (C := dfl_full_comp_cat_with_univ_types C)
             (dfl_full_comp_cat_with_univ_to_section t₁)
             (dfl_full_comp_cat_with_univ_to_section t₂))
          (dfl_ext_identity t₁ t₂).
    Proof.
      use make_z_iso.
      - exact dfl_ext_identity_section_mor.
      - exact dfl_ext_identity_section_inv.
      - exact dfl_ext_identity_section_iso_inverses.
    Defined.

    Definition stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_z_iso
      : z_iso
          (Γ & comp_cat_univ_el
                 (dfl_full_comp_cat_el C)
                 stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_code)
          (Γ & dfl_ext_identity_type t₁ t₂).
    Proof.
      refine (z_iso_comp
                (cat_univ_ext_id_z_iso
                   eq
                   (dfl_full_comp_cat_with_univ_to_section t₁)
                   (dfl_full_comp_cat_with_univ_to_section t₂))
                _).
      refine (z_iso_comp
                (z_iso_inv
                   (comprehension_preserves_ext_id_z_iso
                      (C := dfl_full_comp_cat_with_univ_types C)
                      (equalizers_univ_cat_with_finlim
                         (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C)
                         Γ
                         (cat_el_map_el
                            (univ_cat_cat_stable_el_map
                               (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
                            (dfl_full_comp_cat_tm_to_mor_univ
                               (dfl_full_comp_cat_univ_ob C) a))
                         (dfl_full_comp_cat_with_univ_to_section t₁)
                         (dfl_full_comp_cat_with_univ_to_section t₂))))
                _).
      use comp_cat_comp_fiber_z_iso.
      exact dfl_ext_identity_section_iso.
    Defined.

    Proposition stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_comm
      : stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_z_iso · π _
        =
        π _.
    Proof.
      unfold stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_z_iso.
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        apply comp_cat_comp_mor_comm.
      }
      etrans.
      {
        apply maponpaths.
        exact (comprehension_preserves_ext_id_z_iso_inv_comm
                 (C := dfl_full_comp_cat_with_univ_types C)
                 (dfl_full_comp_cat_with_univ_to_section t₁)
                 (dfl_full_comp_cat_with_univ_to_section t₂)
                 _).
      }
      exact (cat_univ_ext_id_comm
               eq
               (dfl_full_comp_cat_with_univ_to_section t₁)
               (dfl_full_comp_cat_with_univ_to_section t₂)).
    Qed.
  End Code.

  Definition stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_codes
             (eq : cat_univ_stable_codes_ext_id
                     (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
    : ext_id_in_comp_cat_univ C.
  Proof.
    use make_ext_id_in_comp_cat_univ.
    - exact (λ Γ a t₁ t₂,
             stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_code eq t₁ t₂).
    - exact (λ Γ a t₁ t₂,
             stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_z_iso eq t₁ t₂).
    - exact (λ Γ a t₁ t₂,
             stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_comm eq t₁ t₂).
  Defined.

  Proposition stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_stable
              (eq : cat_univ_stable_codes_ext_id
                      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
    : ext_id_in_comp_cat_univ_is_stable
        C
        (stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_codes eq).
  Proof.
    intros Γ Δ s a t₁ t₂.
    use dfl_full_comp_cat_univ_tm_eq ; simpl.
    etrans.
    {
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (comp_cat_comp_mor_sub_dfl_comp_cat_univ C s).
      }
      simpl.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply PullbackArrow_PullbackPr1.
      }
      rewrite !assoc'.
      apply maponpaths.
      exact (PullbackArrow_PullbackPr1
               (comp_cat_pullback
                  (dfl_full_comp_cat_univ_ob C)
                  _)
               _
               _
               _
               _).
    }
    refine (cat_univ_stable_codes_ext_id_stable eq s _ _ @ _).
    refine (!_).
    etrans.
    {
      exact (PullbackArrow_PullbackPr1
               (comp_cat_pullback
                  (dfl_full_comp_cat_univ_ob C)
                  _)
               _
               _
               _
               _).
    }
    use cat_univ_ext_id_eq.
    - exact (dfl_full_comp_cat_tm_to_mor_univ_subst s a).
    - exact (dfl_full_comp_cat_with_univ_to_section_subst_cat_univ_tm s t₁).
    - exact (dfl_full_comp_cat_with_univ_to_section_subst_cat_univ_tm s t₂).
  Qed.

  Definition stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ
             (eq : cat_univ_stable_codes_ext_id
                     (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
    : stable_ext_id_in_comp_cat_univ C.
  Proof.
    use make_stable_ext_id_in_comp_cat_univ.
    - exact (stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_codes eq).
    - exact (stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ_stable eq).
  Defined.

  (** * 4. Equivalence *)
  Proposition stable_ext_id_in_dfl_full_comp_cat_weq_finlim_univ_left
              (eq : stable_ext_id_in_comp_cat_univ C)
    : stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ
        (stable_ext_id_in_dfl_full_comp_cat_to_finlim_univ eq)
      =
      eq.
  Proof.
    use stable_ext_id_in_comp_cat_univ_eq.
    intros Γ a t₁ t₂.
    etrans.
    {
      exact (dfl_full_comp_cat_tm_to_mor_to_tm_univ
               _
               (ext_id_in_comp_cat_univ_code eq _ _)).
    }
    use ext_id_in_comp_cat_univ_code_on_eq.
    - exact (dfl_full_comp_cat_tm_to_mor_to_tm_univ _ a).
    - use eq_comp_cat_tm ; simpl.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      refine (!(comp_cat_comp_mor_comp _ _) @ _).
      refine (_ @ comp_cat_comp_mor_id _).
      apply maponpaths.
      refine (!(comp_cat_el_map_on_concat (dfl_full_comp_cat_el C) _ _) @ _).
      apply (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C)).
    - use eq_comp_cat_tm ; simpl.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      refine (!(comp_cat_comp_mor_comp _ _) @ _).
      refine (_ @ comp_cat_comp_mor_id _).
      apply maponpaths.
      refine (!(comp_cat_el_map_on_concat (dfl_full_comp_cat_el C) _ _) @ _).
      apply (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C)).
  Qed.

  Proposition stable_ext_id_in_dfl_full_comp_cat_weq_finlim_univ_right
              (eq : cat_univ_stable_codes_ext_id
                      (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C))
    : stable_ext_id_in_dfl_full_comp_cat_to_finlim_univ
        (stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ eq)
      =
      eq.
  Proof.
    use cat_univ_stable_codes_ext_id_eq.
    intros Γ a t₁ t₂.
    etrans.
    {
      apply dfl_full_comp_cat_mor_to_tm_to_mor_univ.
    }
    use cat_univ_ext_id_eq.
    - apply dfl_full_comp_cat_mor_to_tm_to_mor_univ.
    - refine (assoc' _ _ _ @ _ @ id_right _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply dfl_full_comp_cat_cat_el_map_el_eq.
      }
      refine (!(comp_cat_comp_mor_comp _ _) @ _).
      refine (_ @ comp_cat_comp_mor_id _).
      apply maponpaths.
      refine (!(comp_cat_el_map_on_concat (dfl_full_comp_cat_el C) _ _) @ _).
      apply (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C)).
    - refine (assoc' _ _ _ @ _ @ id_right _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply dfl_full_comp_cat_cat_el_map_el_eq.
      }
      refine (!(comp_cat_comp_mor_comp _ _) @ _).
      refine (_ @ comp_cat_comp_mor_id _).
      apply maponpaths.
      refine (!(comp_cat_el_map_on_concat (dfl_full_comp_cat_el C) _ _) @ _).
      apply (comp_cat_el_map_on_idpath (dfl_full_comp_cat_el C)).
  Qed.

  Definition stable_ext_id_in_dfl_full_comp_cat_weq_finlim_univ
    : stable_ext_id_in_comp_cat_univ C
      ≃
      cat_univ_stable_codes_ext_id
        (dfl_full_comp_cat_with_univ_to_univ_cat_finlim C).
  Proof.
    use weq_iso.
    - exact stable_ext_id_in_dfl_full_comp_cat_to_finlim_univ.
    - exact stable_ext_id_in_dfl_full_comp_cat_from_finlim_univ.
    - exact stable_ext_id_in_dfl_full_comp_cat_weq_finlim_univ_left.
    - exact stable_ext_id_in_dfl_full_comp_cat_weq_finlim_univ_right.
  Defined.
End ExtId.
