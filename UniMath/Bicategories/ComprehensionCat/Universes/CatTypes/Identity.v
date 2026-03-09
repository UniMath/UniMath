(**

 Codes for identity types in a universe of a category

 A universe is said to be closed under identity types if the identity type of any two terms
 in a type in that universe also is in the universe.  In this file, we develop the basic theory
 of universes that are closed under identity types. Specifically, we define when a universe
 supports codes for identity types and we define suitable stability condition. In addition, we
 define when a functor preserves such codes, and we show that the identity preserves codes for
 identity types and that the composition of functors that preseves codes for identity types,
 also preserve such codes. As a result, one can for suitable bicategories of categories with
 finite limits and a universe that has codes for identity types. Finally, we prove the lemma
 that is necessary to show that this bicategory is univalent.

 In the work on algebraic set theory, systems of small maps are used. Saying that the universe
 is closed under identity types, correspond to an axiom saying that a system of small maps is
 closed under equalizers. However, such an axiom is commonly not present in developments of
 algebraic set theory (see "A brief introduction to algebraic set theory" by Awodey or
 "Algebraic Set Theory" by Joyal and Moerdijk). This is because they assume a stronger axiom,
 namely that any monomorphism is contained in the universe, which corresponds to propositional
 resizing. However, in predicative developments of algebraic set theory (see By van den Berg
 and Moerdijk) one does not assume that every monomorphism is small (i.e., one does not assume
 propositional resizing). Van den Berg and Moerdijk assume another axiom, namely that all
 diagonals `Δ : X --> X × X` are small. Note that this is equivalent to saying that every
 equalizer is small. We slightly weaken this axiom by only requiring diagonals of small types
 to be small.

 References:
 - "Algebraic Set Theory" by Joyal and Moerdijk
 - "A brief introduction to algebraic set theory" by Awodey
 - "Aspects of predicative algebraic set theory. I. Exact completion" by Van den Berg and
   Moerdijk

 Contents
 1. Codes for identity types
 2. Stability
 3. Preservation
 4. Preservation by identity and composition
 5. Univalence condition

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.

Local Open Scope cat.

Section ExtIdInCatWithUniv.
  Context {C : univ_cat_with_finlim_universe}.

  Let el : cat_stable_el_map_coherent C := univ_cat_cat_stable_el_map C.

  (** * 1. Codes for identity types *)
  Definition cat_univ_codes_ext_id
    : UU
    := ∏ (Γ : C)
         (a : Γ --> univ_cat_universe C)
         (t₁ t₂ : section_of_mor (cat_el_map_mor el a)),
       ∑ (eq : Γ --> univ_cat_universe C)
         (f : z_iso (cat_el_map_el el eq) (equalizers_univ_cat_with_finlim C _ _ t₁ t₂)),
       f · EqualizerArrow (equalizers_univ_cat_with_finlim C _ _ t₁ t₂)
       =
       cat_el_map_mor el eq.

  Proposition isaset_cat_univ_codes_ext_id
    : isaset cat_univ_codes_ext_id.
  Proof.
    use impred_isaset ; intros Γ.
    use impred_isaset ; intros a.
    use impred_isaset ; intros t₁.
    use impred_isaset ; intros t₂.
    use isaset_total2.
    - apply homset_property.
    - intros eq.
      use isaset_total2.
      + apply isaset_z_iso.
      + intro f.
        apply isasetaprop.
        apply homset_property.
  Qed.

  Definition make_cat_univ_codes_ext_id
             (eq : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (t₁ t₂ : section_of_mor (cat_el_map_mor el a)),
                   Γ --> univ_cat_universe C)
             (f : ∏ (Γ : C)
                    (a : Γ --> univ_cat_universe C)
                    (t₁ t₂ : section_of_mor (cat_el_map_mor el a)),
                  z_iso
                    (cat_el_map_el el (eq Γ a t₁ t₂))
                    (equalizers_univ_cat_with_finlim C _ _ t₁ t₂))
             (p : ∏ (Γ : C)
                    (a : Γ --> univ_cat_universe C)
                    (t₁ t₂ : section_of_mor (cat_el_map_mor el a)),
                  f Γ a t₁ t₂
                  · EqualizerArrow (equalizers_univ_cat_with_finlim C _ _ t₁ t₂)
                  =
                  cat_el_map_mor el (eq Γ a t₁ t₂))
    : cat_univ_codes_ext_id
    := λ Γ a t₁ t₂, eq Γ a t₁ t₂ ,, f Γ a t₁ t₂ ,, p Γ a t₁ t₂.

  Definition cat_univ_ext_id
             (eq : cat_univ_codes_ext_id)
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (t₁ t₂ : section_of_mor (cat_el_map_mor el a))
    : Γ --> univ_cat_universe C
    := pr1 (eq Γ a t₁ t₂).

  Definition cat_univ_ext_id_z_iso
             (eq : cat_univ_codes_ext_id)
             {Γ : C}
             {a : Γ --> univ_cat_universe C}
             (t₁ t₂ : section_of_mor (cat_el_map_mor el a))
    : z_iso
        (cat_el_map_el el (cat_univ_ext_id eq t₁ t₂))
        (equalizers_univ_cat_with_finlim C _ _ t₁ t₂)
    := pr12 (eq Γ a t₁ t₂).

  Proposition cat_univ_ext_id_comm
              (eq : cat_univ_codes_ext_id)
              {Γ : C}
              {a : Γ --> univ_cat_universe C}
              (t₁ t₂ : section_of_mor (cat_el_map_mor el a))
    : cat_univ_ext_id_z_iso eq t₁ t₂
      · EqualizerArrow (equalizers_univ_cat_with_finlim C _ _ t₁ t₂)
      =
      cat_el_map_mor el (cat_univ_ext_id eq t₁ t₂).
  Proof.
    exact (pr22 (eq Γ a t₁ t₂)).
  Defined.

  Proposition cat_univ_codes_ext_id_eq
              {eq₁ eq₂ : cat_univ_codes_ext_id}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (t₁ t₂ : section_of_mor (cat_el_map_mor el a)),
                   cat_univ_ext_id eq₁ t₁ t₂
                   =
                   cat_univ_ext_id eq₂ t₁ t₂)
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
      unfold z_iso.
      use z_iso_eq.
      etrans.
      {
        apply (pr1_transportf (P := λ x (f : cat_el_map_el el x --> _), is_z_isomorphism _)).
      }
      rewrite transportf_cat_el_map_el.
      use EqualizerArrowisMonic.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply cat_univ_ext_id_comm.
      }
      rewrite cat_el_map_mor_eq.
      refine (!_).
      apply cat_univ_ext_id_comm.
  Qed.

  Proposition cat_univ_ext_id_eq
              (eq : cat_univ_codes_ext_id)
              {Γ : C}
              {a a' : Γ --> univ_cat_universe C}
              {t₁ t₂ : section_of_mor (cat_el_map_mor el a)}
              {t₁' t₂' : section_of_mor (cat_el_map_mor el a')}
              (p : a = a')
              (q : t₁ · cat_el_map_el_eq el p = t₁')
              (r : t₂ · cat_el_map_el_eq el p = t₂')
    : cat_univ_ext_id eq t₁ t₂ = cat_univ_ext_id eq t₁' t₂'.
  Proof.
    induction p ; cbn ; cbn in q, r.
    rewrite id_right in q, r.
    assert (t₁ = t₁') as ->.
    {
      use eq_section_of_mor.
      exact q.
    }
    assert (t₂ = t₂') as ->.
    {
      use eq_section_of_mor.
      exact r.
    }
    apply idpath.
  Qed.

  Definition equalizers_univ_cat_with_finlim_eq_mor
             {Γ : C}
             {a a' : Γ --> univ_cat_universe C}
             {t₁ t₂ : section_of_mor (cat_el_map_mor el a)}
             {t₁' t₂' : section_of_mor (cat_el_map_mor el a')}
             (p : a = a')
             (q : t₁ · cat_el_map_el_eq el p = t₁')
             (r : t₂ · cat_el_map_el_eq el p = t₂')
    : equalizers_univ_cat_with_finlim C Γ (cat_el_map_el el a) t₁ t₂
      -->
      equalizers_univ_cat_with_finlim C Γ (cat_el_map_el el a') t₁' t₂'.
  Proof.
    use EqualizerIn.
    - apply EqualizerArrow.
    - abstract
        (induction p ; cbn in q, r ;
         rewrite id_right in q, r ;
         assert (t₁ = t₁') as -> ; [ use eq_section_of_mor ; exact q | ] ;
         assert (t₂ = t₂') as -> ; [ use eq_section_of_mor ; exact r | ] ;
         apply EqualizerEqAr).
  Defined.

  (** * 2. Stability *)
  Definition is_stable_cat_univ_codes_ext_id
             (eq : cat_univ_codes_ext_id)
    : UU
    := ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (a : Δ --> univ_cat_universe C)
         (t₁ t₂ : section_of_mor (cat_el_map_mor el a)),
       s · cat_univ_ext_id eq t₁ t₂
       =
       cat_univ_ext_id
         eq
         (subst_cat_univ_tm el s a t₁)
         (subst_cat_univ_tm el s a t₂).

  Proposition isaprop_is_stable_cat_univ_codes_ext_id
              (eq : cat_univ_codes_ext_id)
    : isaprop (is_stable_cat_univ_codes_ext_id eq).
  Proof.
    repeat (use impred ; intro).
    apply homset_property.
  Qed.

  Definition cat_univ_stable_codes_ext_id
    : UU
    := ∑ (eq : cat_univ_codes_ext_id),
       is_stable_cat_univ_codes_ext_id eq.

  Definition make_cat_univ_stable_codes_ext_id
             (eq : cat_univ_codes_ext_id)
             (H : is_stable_cat_univ_codes_ext_id eq)
    : cat_univ_stable_codes_ext_id
    := eq ,, H.

  Coercion cat_univ_stable_codes_ext_id_to_codes
           (eq : cat_univ_stable_codes_ext_id)
    : cat_univ_codes_ext_id
    := pr1 eq.

  Proposition cat_univ_stable_codes_ext_id_stable
              (eq : cat_univ_stable_codes_ext_id)
              {Γ Δ : C}
              (s : Γ --> Δ)
              {a : Δ --> univ_cat_universe C}
              (t₁ t₂ : section_of_mor (cat_el_map_mor el a))
    : s · cat_univ_ext_id eq t₁ t₂
      =
      cat_univ_ext_id
        eq
        (subst_cat_univ_tm el s a t₁)
        (subst_cat_univ_tm el s a t₂).
  Proof.
    exact (pr2 eq Γ Δ s a t₁ t₂).
  Defined.

  Proposition cat_univ_stable_codes_ext_id_eq
              {eq₁ eq₂ : cat_univ_stable_codes_ext_id}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (t₁ t₂ : section_of_mor (cat_el_map_mor el a)),
                   cat_univ_ext_id eq₁ t₁ t₂
                   =
                   cat_univ_ext_id eq₂ t₁ t₂)
    : eq₁ = eq₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_stable_cat_univ_codes_ext_id.
    }
    use cat_univ_codes_ext_id_eq.
    exact p.
  Qed.

  Proposition isaset_cat_univ_stable_codes_ext_id
    : isaset cat_univ_stable_codes_ext_id.
  Proof.
    use isaset_total2.
    - exact isaset_cat_univ_codes_ext_id.
    - intro.
      apply isasetaprop.
      apply isaprop_is_stable_cat_univ_codes_ext_id.
  Qed.
End ExtIdInCatWithUniv.

Arguments cat_univ_codes_ext_id C : clear implicits.
Arguments isaset_cat_univ_codes_ext_id C : clear implicits.
Arguments cat_univ_stable_codes_ext_id C : clear implicits.

Section PreservationIdCodes.
  Context {C₁ C₂ : univ_cat_with_finlim_universe}
          (eq₁ : cat_univ_stable_codes_ext_id C₁)
          (eq₂ : cat_univ_stable_codes_ext_id C₂)
          (F : functor_finlim_universe C₁ C₂).

  Let el₁ : cat_stable_el_map_coherent C₁ := univ_cat_cat_stable_el_map C₁.
  Let el₂ : cat_stable_el_map_coherent C₂ := univ_cat_cat_stable_el_map C₂.

  Let Fel : functor_preserves_el
              (univ_cat_cat_stable_el_map C₁)
              (univ_cat_cat_stable_el_map C₂)
              F
    := functor_finlim_universe_preserves_el F.

  (** * 3. Preservation *)
  Definition functor_preserves_stable_codes_ext_id
    : UU
    := ∏ (Γ : C₁)
         (a : Γ --> univ_cat_universe C₁)
         (t₁ t₂ : section_of_mor (cat_el_map_mor el₁ a)),
       #F(cat_univ_ext_id eq₁ t₁ t₂) · functor_on_universe F
       =
       cat_univ_ext_id
         eq₂
         (functor_finlim_on_universe_tm Fel t₁)
         (functor_finlim_on_universe_tm Fel t₂).

  Proposition isaprop_functor_preserves_stable_codes_ext_id
    : isaprop functor_preserves_stable_codes_ext_id.
  Proof.
    repeat (use impred ; intro).
    apply homset_property.
  Qed.

  Proposition functor_preserves_stable_codes_ext_id_on_code
              (p : functor_preserves_stable_codes_ext_id)
              {Γ : C₁}
              {a : Γ --> univ_cat_universe C₁}
              (t₁ t₂ : section_of_mor (cat_el_map_mor el₁ a))
    : #F(cat_univ_ext_id eq₁ t₁ t₂) · functor_on_universe F
      =
      cat_univ_ext_id
        eq₂
        (functor_finlim_on_universe_tm Fel t₁)
        (functor_finlim_on_universe_tm Fel t₂).
  Proof.
    exact (p Γ a t₁ t₂).
  Defined.
End PreservationIdCodes.

Arguments functor_preserves_stable_codes_ext_id_on_code
  {C₁ C₂ eq₁ eq₂ F} p {Γ a} t₁ t₂.

(** * 4. Preservation by identity and composition *)
Proposition identity_preserves_stable_codes_ext_id
            {C : univ_cat_with_finlim_universe}
            (eq : cat_univ_stable_codes_ext_id C)
  : functor_preserves_stable_codes_ext_id eq eq (identity _).
Proof.
  intros Γ a t₁ t₂ ; simpl.
  rewrite id_right.
  use cat_univ_ext_id_eq.
  - exact (!(id_right _)).
  - apply idpath.
  - apply idpath.
Qed.

Proposition comp_preserves_stable_codes_ext_id
            {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
            {eq₁ : cat_univ_stable_codes_ext_id C₁}
            {eq₂ : cat_univ_stable_codes_ext_id C₂}
            {eq₃ : cat_univ_stable_codes_ext_id C₃}
            {F : functor_finlim_universe C₁ C₂}
            (Fc : functor_preserves_stable_codes_ext_id eq₁ eq₂ F)
            {G : functor_finlim_universe C₂ C₃}
            (Gc : functor_preserves_stable_codes_ext_id eq₂ eq₃ G)
  : functor_preserves_stable_codes_ext_id eq₁ eq₃ (F · G).
Proof.
  intros Γ a t₁ t₂ ; simpl.
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    rewrite <- functor_comp.
    apply maponpaths.
    apply (functor_preserves_stable_codes_ext_id_on_code Fc).
  }
  etrans.
  {
    apply (functor_preserves_stable_codes_ext_id_on_code Gc).
  }
  use cat_univ_ext_id_eq.
  - rewrite !functor_comp.
    rewrite !assoc'.
    apply idpath.
  - simpl.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply functor_comp.
    }
    do 2 refine (assoc' _ _ _ @ _).
    do 3 apply maponpaths.
    apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C₃)).
  - simpl.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply functor_comp.
    }
    do 2 refine (assoc' _ _ _ @ _).
    do 3 apply maponpaths.
    apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C₃)).
Qed.

(** * 5. Univalence condition *)
Proposition cat_univ_stable_codes_ext_id_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {eq₁ eq₂ : cat_univ_stable_codes_ext_id C}
            (Fc : functor_preserves_stable_codes_ext_id eq₁ eq₂ (identity _))
  : eq₁ = eq₂.
Proof.
  use cat_univ_stable_codes_ext_id_eq.
  intros Γ a t₁ t₂.
  refine (_ @ functor_preserves_stable_codes_ext_id_on_code Fc t₁ t₂ @ _).
  {
    refine (!_).
    apply id_right.
  }
  use cat_univ_ext_id_eq.
  + exact (id_right _).
  + cbn.
    rewrite assoc'.
    rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
    refine (_ @ id_right _).
    apply maponpaths.
    apply (cat_el_map_el_eq_id (univ_cat_cat_stable_el_map C)).
  + cbn.
    rewrite assoc'.
    rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
    refine (_ @ id_right _).
    apply maponpaths.
    apply (cat_el_map_el_eq_id (univ_cat_cat_stable_el_map C)).
Qed.
