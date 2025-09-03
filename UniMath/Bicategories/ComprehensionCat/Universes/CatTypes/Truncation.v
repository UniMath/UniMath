(**

 Codes for truncations in a universe of a category

 A universe is said to be closed under truncation types if the proposition truncation of any
 type in that universe   also is in that universe. In this file, we develop the basic theory
 of universes that are closed under truncations . Specifically, we define when a universe
 supports codes for truncations  and we define suitable stability condition. In addition, we
 define when a functor preserves such codes, and we show that the identity preserves codes for
 truncations and that the composition of functors that preseves codes for truncations, also
 preserve such codes. As a result, one can for suitable bicategories of categories with finite
 limits and a universe that has codes for truncations. Finally, we prove the lemma that is
 necessary to show that this bicategory is univalent.

 In the work on algebraic set theory, systems of small maps are used, and usually there is no
 axiom that explicitly says that the universe contains codes for truncations. This is because
 that axiom can be derived from other axioms. Concretely, it is frequently assumed that the
 universe contains all monomorphisms (e.g., in "A brief introduction to algebraic set theory"
 by Awodey or "Algebraic Set Theory" by Joyal and Moerdijk) meaning that every proposition,
 in particular the propositional truncation, is in the universe. In addition, one usually
 assumes, also in predicative developments, that the universe is closed under quotients, and
 that also allows us to show that the universe contains codes for truncations. However, this
 axiom is still sensible in settings where we do not assume all quotients to exists and thus
 settings where we do not assume that the universe is closed under quotients (see "Propositions
 as [types]" by Awodey and Bauer). In such a setting, one uses extensional type theory with
 the usual type formers and the propositional truncation.

 References:
 - "Algebraic Set Theory" by Joyal and Moerdijk
 - "A brief introduction to algebraic set theory" by Awodey
 - "Aspects of predicative algebraic set theory. I. Exact completion" by Van den Berg and
   Moerdijk
 - "Propositions as [types]" by Awodey and Bauer

 Contents
 1. Codes for truncations
 2. Stability
 3. Preservation
 4. Preservation by identity and composition
 5. Univalence condition

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpiFacts.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.

Local Open Scope cat.

Section TruncInCatWithUniv.
  Context {C : univ_cat_with_finlim_universe}
          {HC : is_regular_category C}.

  Let el : cat_stable_el_map_coherent C := univ_cat_cat_stable_el_map C.

  (** * 1. Codes for truncations *)
  Definition cat_univ_codes_trunc
    : UU
    := ∏ (Γ : C)
         (a : Γ --> univ_cat_universe C),
       ∑ (ta : Γ --> univ_cat_universe C)
         (f : z_iso
                (cat_el_map_el el ta)
                (regular_category_im HC (cat_el_map_mor el a))),
       f · regular_category_im_Monic HC (cat_el_map_mor el a)
       =
       cat_el_map_mor el ta.

  Proposition isaset_cat_univ_codes_trunc
    : isaset cat_univ_codes_trunc.
  Proof.
    use impred_isaset ; intros Γ.
    use impred_isaset ; intros a.
    use isaset_total2.
    - apply homset_property.
    - intros ta.
      use isaset_total2.
      + apply isaset_z_iso.
      + intro f.
        apply isasetaprop.
        apply homset_property.
  Qed.

  Definition make_cat_univ_codes_trunc
             (ta : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C),
                   Γ --> univ_cat_universe C)
             (f : ∏ (Γ : C)
                    (a : Γ --> univ_cat_universe C),
                  z_iso
                    (cat_el_map_el el (ta Γ a))
                    (regular_category_im HC (cat_el_map_mor el a)))
             (p : ∏ (Γ : C)
                    (a : Γ --> univ_cat_universe C),
                  f Γ a
                  · regular_category_im_Monic HC (cat_el_map_mor el a)
                  =
                  cat_el_map_mor el (ta Γ a))
    : cat_univ_codes_trunc
    := λ Γ a, ta Γ a ,, f Γ a ,, p Γ a.

  Definition cat_univ_trunc_code
             (ta : cat_univ_codes_trunc)
             {Γ : C}
             (a : Γ --> univ_cat_universe C)
    : Γ --> univ_cat_universe C
    := pr1 (ta Γ a).

  Definition cat_univ_trunc_z_iso
             (ta : cat_univ_codes_trunc)
             {Γ : C}
             (a : Γ --> univ_cat_universe C)
    : z_iso
        (cat_el_map_el el (cat_univ_trunc_code ta a))
        (regular_category_im HC (cat_el_map_mor el a))
    := pr12 (ta Γ a).

  Proposition cat_univ_trunc_comm
              (ta : cat_univ_codes_trunc)
              {Γ : C}
              (a : Γ --> univ_cat_universe C)
    : cat_univ_trunc_z_iso ta a
      · regular_category_im_Monic HC (cat_el_map_mor el a)
      =
      cat_el_map_mor el _.
  Proof.
    exact (pr22 (ta Γ a)).
  Defined.

  Proposition cat_univ_codes_trunc_eq
              {ta₁ ta₂ : cat_univ_codes_trunc}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C),
                   cat_univ_trunc_code ta₁ a
                   =
                   cat_univ_trunc_code ta₂ a)
    : ta₁ = ta₂.
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
      unfold z_iso.
      use z_iso_eq.
      etrans.
      {
        apply (pr1_transportf (P := λ x (f : cat_el_map_el el x --> _), is_z_isomorphism _)).
      }
      rewrite transportf_cat_el_map_el.
      use (MonicisMonic _ (regular_category_im_Monic HC (cat_el_map_mor el a))).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply cat_univ_trunc_comm.
      }
      rewrite cat_el_map_mor_eq.
      refine (!_).
      apply cat_univ_trunc_comm.
  Qed.

  Proposition cat_univ_trunc_code_eq
              (ta : cat_univ_codes_trunc)
              {Γ : C}
              {a a' : Γ --> univ_cat_universe C}
              (p : a = a')
    : cat_univ_trunc_code ta a = cat_univ_trunc_code ta a'.
  Proof.
    induction p.
    apply idpath.
  Qed.

  (** * 2. Stability *)
  Definition is_stable_cat_univ_trunc
             (ta : cat_univ_codes_trunc)
    : UU
    := ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (a : Δ --> univ_cat_universe C),
       s · cat_univ_trunc_code ta a
       =
       cat_univ_trunc_code ta (s · a).

  Proposition isaprop_is_stable_cat_univ_trunc
              (ta : cat_univ_codes_trunc)
    : isaprop (is_stable_cat_univ_trunc ta).
  Proof.
    repeat (use impred ; intro).
    apply homset_property.
  Qed.

  Definition cat_univ_stable_codes_trunc
    : UU
    := ∑ (ta : cat_univ_codes_trunc),
       is_stable_cat_univ_trunc ta.

  Definition make_cat_univ_stable_codes_trunc
             (ta : cat_univ_codes_trunc)
             (H : is_stable_cat_univ_trunc ta)
    : cat_univ_stable_codes_trunc
    := ta ,, H.

  Coercion cat_univ_stable_codes_trunc_to_codes
           (ta : cat_univ_stable_codes_trunc)
    : cat_univ_codes_trunc
    := pr1 ta.

  Proposition cat_univ_stable_codes_trunc_stable
              (ta : cat_univ_stable_codes_trunc)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : Δ --> univ_cat_universe C)
    : s · cat_univ_trunc_code ta a
      =
      cat_univ_trunc_code ta (s · a).
  Proof.
    exact (pr2 ta Γ Δ s a).
  Defined.

  Proposition cat_univ_stable_codes_trunc_eq
              {ta₁ ta₂ : cat_univ_stable_codes_trunc}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C),
                   cat_univ_trunc_code ta₁ a
                   =
                   cat_univ_trunc_code ta₂ a)
    : ta₁ = ta₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_stable_cat_univ_trunc.
    }
    use cat_univ_codes_trunc_eq.
    exact p.
  Qed.

  Proposition isaset_cat_univ_stable_codes_trunc
    : isaset cat_univ_stable_codes_trunc.
  Proof.
    use isaset_total2.
    - exact isaset_cat_univ_codes_trunc.
    - intro.
      apply isasetaprop.
      apply isaprop_is_stable_cat_univ_trunc.
  Qed.
End TruncInCatWithUniv.

Arguments cat_univ_codes_trunc {C} HC.
Arguments cat_univ_stable_codes_trunc {C} HC.

Section PreservationTruncCodes.
  Context {C₁ C₂ : univ_cat_with_finlim_universe}
          (HC₁ : is_regular_category C₁)
          (HC₂ : is_regular_category C₂)
          (ta₁ : cat_univ_stable_codes_trunc HC₁)
          (ta₂ : cat_univ_stable_codes_trunc HC₂)
          {F : functor_finlim_universe C₁ C₂}.

  Let el₁ : cat_stable_el_map_coherent C₁ := univ_cat_cat_stable_el_map C₁.
  Let el₂ : cat_stable_el_map_coherent C₂ := univ_cat_cat_stable_el_map C₂.

  Let Fel : functor_preserves_el
              (univ_cat_cat_stable_el_map C₁)
              (univ_cat_cat_stable_el_map C₂)
              F
    := functor_finlim_universe_preserves_el F.

  (** * 3. Preservation *)
  Definition functor_preserves_stable_trunc
    : UU
    := ∏ (Γ : C₁)
         (a : Γ --> univ_cat_universe C₁),
       #F(cat_univ_trunc_code ta₁ a) · functor_on_universe F
       =
       cat_univ_trunc_code ta₂ (#F a · functor_on_universe F).

  Proposition isaprop_functor_preserves_stable_trunc
    : isaprop functor_preserves_stable_trunc.
  Proof.
    repeat (use impred ; intro).
    apply homset_property.
  Qed.

  Proposition functor_preserves_stable_trunc_on_code
              (p : functor_preserves_stable_trunc)
              {Γ : C₁}
              (a : Γ --> univ_cat_universe C₁)
    : #F(cat_univ_trunc_code ta₁ a) · functor_on_universe F
      =
      cat_univ_trunc_code ta₂ (#F a · functor_on_universe F).
  Proof.
    exact (p Γ a).
  Defined.
End PreservationTruncCodes.

Arguments functor_preserves_stable_trunc
  {C₁ C₂ HC₁ HC₂} ta₁ ta₂ F.
Arguments functor_preserves_stable_trunc_on_code
  {C₁ C₂ HC₁ HC₂ ta₁ ta₂ F} p {Γ} a.

(** * 4. Preservation by identity and composition *)
Proposition id_preserves_stable_trunc
            {C : univ_cat_with_finlim_universe}
            (HC : is_regular_category C)
            (ta : cat_univ_stable_codes_trunc HC)
  : functor_preserves_stable_trunc ta ta (identity _).
Proof.
  intros Γ a ; cbn.
  rewrite id_right.
  use cat_univ_trunc_code_eq.
  rewrite id_right.
  apply idpath.
Qed.

Proposition comp_preserves_stable_trunc
            {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
            {HC₁ : is_regular_category C₁}
            {HC₂ : is_regular_category C₂}
            {HC₃ : is_regular_category C₃}
            {ta₁ : cat_univ_stable_codes_trunc HC₁}
            {ta₂ : cat_univ_stable_codes_trunc HC₂}
            {ta₃ : cat_univ_stable_codes_trunc HC₃}
            {F : functor_finlim_universe C₁ C₂}
            (Fc : functor_preserves_stable_trunc ta₁ ta₂ F)
            {G : functor_finlim_universe C₂ C₃}
            (Gc : functor_preserves_stable_trunc ta₂ ta₃ G)
  : functor_preserves_stable_trunc ta₁ ta₃ (F · G).
Proof.
  intros Γ a ; cbn.
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    rewrite <- functor_comp.
    apply maponpaths.
    apply (functor_preserves_stable_trunc_on_code Fc).
  }
  etrans.
  {
    apply (functor_preserves_stable_trunc_on_code Gc).
  }
  use cat_univ_trunc_code_eq.
  rewrite !functor_comp.
  rewrite !assoc'.
  apply idpath.
Qed.

(** * 5. Univalence condition *)
Proposition cat_univ_stable_trunc_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {HC : is_regular_category C}
            {ta₁ ta₂ : cat_univ_stable_codes_trunc HC}
            (Fc : functor_preserves_stable_trunc ta₁ ta₂ (identity _))
  : ta₁ = ta₂.
Proof.
  use cat_univ_stable_codes_trunc_eq.
  intros Γ a.
  pose (functor_preserves_stable_trunc_on_code Fc a) as p.
  cbn in p.
  rewrite id_right in p.
  refine (p @ _).
  use cat_univ_trunc_code_eq.
  apply id_right.
Qed.
