(**

 Universes in categories that are closed under propositional resizing

 A universe is said to be closed under propositional resizing if there is a code in that
 universe for every type that is a proposition (i.e., every two inhabitants are equal).
 In this file, we define when a universe in a category is closed under propositional
 resizing.

 The main idea behind our development is that types which are propositions, can be
 characterized as types whose projection map is a monomorphism, which holds generally in
 extensional type theory. Hence, if we are looking at comprehension categories arising
 from categories with finite limits, propositions in a context `Γ` are the same as
 monomorphisms into `Γ`. We can thus formulate propositional resizing in a convenient way
 for universes in categories, namely there is a code for every monomorphism in the
 category.

 Note that this axiom appears frequently in the context of algebraic set theory (see, for
 instance, "Algebraic Set Theory" by Joyal and Moerdijk or "A brief introduction to algebraic
 set theory" by Awodey). In that context, one works with categories that are, among others,
 equipped with a class of small maps and classifying object for them. The classifying object
 represents the universe type and the map that associated to each code an actual type, and
 small maps represent those types for which there is a code. If one uses algebraic set theory
 to construct models of IZF (i.e., intuitionistic Zermelo-Fraenkel set theory, which is
 impredicative), then one assumes that all monomorphisms are small. Concretely, this means
 that for every monomorphism there is a code in the universe, which corresponds to the axiom
 of propositional resizing. In the context of set theory, propositional resizing gives us
 the full separation axiom rather than one restricted to bounded formulas.

 References:
 - "Algebraic Set Theory" by Joyal and Moerdijk
 - "A brief introduction to algebraic set theory" by Awodey

 Contents
 1. Codes for resizing
 2. Stability
 3. Preservation
 4. Preservation by identity and composition
 5. Univalence condition

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.

Local Open Scope cat.

Section ResizingInCatWithUniv.
  Context {C : univ_cat_with_finlim_universe}.

  Let el : cat_stable_el_map_coherent C := univ_cat_cat_stable_el_map C.

  (** * 1. Codes for resizing *)
  Definition cat_univ_codes_resizing
    : UU
    := ∏ (Γ A : C)
         (m : Monic C A Γ),
       ∑ (a : Γ --> univ_cat_universe C)
         (f : z_iso (cat_el_map_el el a) A),
       f · m = cat_el_map_mor el _.

  Definition make_cat_univ_codes_resizing
             (a : ∏ (Γ A : C)
                    (m : Monic C A Γ),
                  Γ --> univ_cat_universe C)
             (f : ∏ (Γ A : C)
                    (m : Monic C A Γ),
                  z_iso (cat_el_map_el el (a Γ A m)) A)
             (p : ∏ (Γ A : C)
                    (m : Monic C A Γ),
                  f Γ A m · m = cat_el_map_mor el _)
    : cat_univ_codes_resizing
    := λ Γ A m, a Γ A m ,, f Γ A m ,, p Γ A m.

  Proposition isaset_cat_univ_codes_resizing
    : isaset cat_univ_codes_resizing.
  Proof.
    use impred_isaset ; intros Γ.
    use impred_isaset ; intros A.
    use impred_isaset ; intros m.
    use isaset_total2.
    - apply homset_property.
    - intros a.
      use isaset_total2.
      + apply isaset_z_iso.
      + intro f.
        apply isasetaprop.
        apply homset_property.
  Qed.

  Definition cat_univ_resize_monic
             (resize : cat_univ_codes_resizing)
             {Γ A : C}
             (m : Monic C A Γ)
    : Γ --> univ_cat_universe C
    := pr1 (resize Γ A m).

  Definition cat_univ_resize_z_iso
             (resize : cat_univ_codes_resizing)
             {Γ A : C}
             (m : Monic C A Γ)
    : z_iso (cat_el_map_el el (cat_univ_resize_monic resize m)) A
    := pr12 (resize Γ A m).

  Proposition cat_univ_resize_z_iso_comm
              (resize : cat_univ_codes_resizing)
              {Γ A : C}
              (m : Monic C A Γ)
    : cat_univ_resize_z_iso resize m · m = cat_el_map_mor el _.
  Proof.
    exact (pr22 (resize Γ A m)).
  Defined.

  Proposition cat_univ_codes_resizing_eq
              {resize₁ resize₂ : cat_univ_codes_resizing}
              (p : ∏ (Γ A : C)
                     (m : Monic C A Γ),
                   cat_univ_resize_monic resize₁ m
                   =
                   cat_univ_resize_monic resize₂ m)
    : resize₁ = resize₂.
  Proof.
    use funextsec ; intro Γ.
    use funextsec ; intro A.
    use funextsec ; intro m.
    use total2_paths_f.
    - exact (p Γ A m).
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
      use (MonicisMonic _ m).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply cat_univ_resize_z_iso_comm.
      }
      rewrite cat_el_map_mor_eq.
      refine (!_).
      apply cat_univ_resize_z_iso_comm.
  Qed.

  Proposition cat_univ_resize_monic_eq
              (resize : cat_univ_codes_resizing)
              {Γ A : C}
              {m m' : Monic C A Γ}
              (p : (m : A --> Γ) = m')
    : cat_univ_resize_monic resize m = cat_univ_resize_monic resize m'.
  Proof.
    assert (m = m') as ->.
    {
      use subtypePath ; [ intro ; apply isapropisMonic | ].
      exact p.
    }
    apply idpath.
  Qed.

  Proposition cat_univ_resize_monic_eq_on_z_iso_help
              (resize : cat_univ_codes_resizing)
              {Γ A A' : C}
              {m : Monic C A Γ}
              {m' : Monic C A' Γ}
              (f : A = A')
              (p : idtoiso f · m' = m)
    : cat_univ_resize_monic resize m = cat_univ_resize_monic resize m'.
  Proof.
    induction f.
    use cat_univ_resize_monic_eq.
    refine (!p @ _).
    apply id_left.
  Qed.

  Proposition cat_univ_resize_monic_eq_on_z_iso
              (resize : cat_univ_codes_resizing)
              {Γ A A' : C}
              {m : Monic C A Γ}
              {m' : Monic C A' Γ}
              (f : z_iso A A')
              (p : f · m' = m)
    : cat_univ_resize_monic resize m = cat_univ_resize_monic resize m'.
  Proof.
    use cat_univ_resize_monic_eq_on_z_iso_help.
    - refine (isotoid _ _ f).
      apply univalent_category_is_univalent.
    - rewrite idtoiso_isotoid.
      exact p.
  Qed.

  (** * 2. Stability *)
  Definition is_stable_cat_univ_codes_resizing
             (resize : cat_univ_codes_resizing)
    : UU
    := ∏ (Γ Δ A : C)
         (s : Γ --> Δ)
         (m : Monic C A Δ),
       s · cat_univ_resize_monic resize m
       =
       cat_univ_resize_monic
         resize
         (pullback_pr2_monic
            _ _
            (pullbacks_univ_cat_with_finlim C _ _ _ m s)).

  Proposition isaprop_is_stable_cat_univ_codes_resizing
              (resize : cat_univ_codes_resizing)
    : isaprop (is_stable_cat_univ_codes_resizing resize).
  Proof.
    repeat (use impred ; intro).
    apply homset_property.
  Qed.

  Definition cat_univ_stable_codes_resizing
    : UU
    := ∑ (resize : cat_univ_codes_resizing),
       is_stable_cat_univ_codes_resizing resize.

  Definition make_cat_univ_stable_codes_resizing
             (resize : cat_univ_codes_resizing)
             (H : is_stable_cat_univ_codes_resizing resize)
    : cat_univ_stable_codes_resizing
    := resize ,, H.

  Coercion cat_univ_stable_codes_resizing_to_codes
           (resize : cat_univ_stable_codes_resizing)
    : cat_univ_codes_resizing
    := pr1 resize.

  Proposition cat_univ_resize_monic_stable
              (resize : cat_univ_stable_codes_resizing)
              {Γ Δ A : C}
              (s : Γ --> Δ)
              (m : Monic C A Δ)
    : s · cat_univ_resize_monic resize m
      =
      cat_univ_resize_monic resize
        (pullback_pr2_monic
           _ _
           (pullbacks_univ_cat_with_finlim C _ _ _ m s)).
  Proof.
    exact (pr2 resize Γ Δ A s m).
  Defined.

  Proposition cat_univ_stable_codes_resizing_eq
              {resize₁ resize₂ : cat_univ_stable_codes_resizing}
              (p : ∏ (Γ A : C)
                     (m : Monic C A Γ),
                   cat_univ_resize_monic resize₁ m
                   =
                   cat_univ_resize_monic resize₂ m)
    : resize₁ = resize₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_stable_cat_univ_codes_resizing.
    }
    use cat_univ_codes_resizing_eq.
    exact p.
  Qed.

  Proposition isaset_cat_univ_stable_codes_resizing
    : isaset cat_univ_stable_codes_resizing.
  Proof.
    use isaset_total2.
    - exact isaset_cat_univ_codes_resizing.
    - intro resize.
      apply isasetaprop.
      apply isaprop_is_stable_cat_univ_codes_resizing.
  Qed.
End ResizingInCatWithUniv.

Arguments cat_univ_codes_resizing C : clear implicits.
Arguments isaset_cat_univ_codes_resizing C : clear implicits.
Arguments cat_univ_stable_codes_resizing C : clear implicits.

Section PreservationResizingCodes.
  Context {C₁ C₂ : univ_cat_with_finlim_universe}
          (resize₁ : cat_univ_stable_codes_resizing C₁)
          (resize₂ : cat_univ_stable_codes_resizing C₂)
          (F : functor_finlim_universe C₁ C₂).

  Let el₁ : cat_stable_el_map_coherent C₁ := univ_cat_cat_stable_el_map C₁.
  Let el₂ : cat_stable_el_map_coherent C₂ := univ_cat_cat_stable_el_map C₂.

  Let Fel : functor_preserves_el
              (univ_cat_cat_stable_el_map C₁)
              (univ_cat_cat_stable_el_map C₂)
              F
    := functor_finlim_universe_preserves_el F.

  (** * 3. Preservation *)
  Definition functor_preserves_stable_resizing_codes
    : UU
    := ∏ (Γ A : C₁)
         (m : Monic C₁ A Γ),
       #F(cat_univ_resize_monic resize₁ m) · functor_on_universe F
       =
       cat_univ_resize_monic
         resize₂
         (functor_preserves_pb_on_monic (functor_finlim_preserves_pullback F) m).

  Proposition isaprop_functor_preserves_stable_resizing_codes
    : isaprop functor_preserves_stable_resizing_codes.
  Proof.
    repeat (use impred ; intro).
    apply homset_property.
  Qed.

  Proposition functor_preserves_stable_resizing_codes_on_code
              (p : functor_preserves_stable_resizing_codes)
              {Γ A : C₁}
              (m : Monic C₁ A Γ)
    : #F(cat_univ_resize_monic resize₁ m) · functor_on_universe F
      =
      cat_univ_resize_monic
        resize₂
        (functor_preserves_pb_on_monic (functor_finlim_preserves_pullback F) m).
  Proof.
    exact (p Γ A m).
  Defined.
End PreservationResizingCodes.

Arguments functor_preserves_stable_resizing_codes_on_code
  {C₁ C₂ resize₁ resize₂ F} p {Γ A} m.

(** * 4. Preservation by identity and composition *)
Proposition identity_preserves_resizing_codes
            {C : univ_cat_with_finlim_universe}
            (resize : cat_univ_stable_codes_resizing C)
  : functor_preserves_stable_resizing_codes
      resize
      resize
      (identity _).
Proof.
  intros Γ A m ; cbn.
  rewrite id_right.
  use cat_univ_resize_monic_eq.
  apply idpath.
Qed.

Proposition comp_preserves_resizing_codes
            {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
            {resize₁ : cat_univ_stable_codes_resizing C₁}
            {resize₂ : cat_univ_stable_codes_resizing C₂}
            {resize₃ : cat_univ_stable_codes_resizing C₃}
            {F : functor_finlim_universe C₁ C₂}
            (Fc : functor_preserves_stable_resizing_codes resize₁ resize₂ F)
            {G : functor_finlim_universe C₂ C₃}
            (Gc : functor_preserves_stable_resizing_codes resize₂ resize₃ G)
  : functor_preserves_stable_resizing_codes
      resize₁
      resize₃
      (F · G).
Proof.
  intros Γ A m ; cbn.
  rewrite !assoc.
  etrans.
  {
    apply maponpaths_2.
    rewrite <- functor_comp.
    apply maponpaths.
    apply (functor_preserves_stable_resizing_codes_on_code Fc).
  }
  etrans.
  {
    apply (functor_preserves_stable_resizing_codes_on_code Gc).
  }
  use cat_univ_resize_monic_eq ; cbn.
  apply idpath.
Qed.

(** * 5. Univalence condition *)
Proposition cat_univ_stable_codes_resizing_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {resize₁ resize₂ : cat_univ_stable_codes_resizing C}
            (Fc : functor_preserves_stable_resizing_codes resize₁ resize₂ (identity _))
  : resize₁ = resize₂.
Proof.
  use cat_univ_stable_codes_resizing_eq.
  intros Γ A m.
  refine (_ @ functor_preserves_stable_resizing_codes_on_code Fc m @ _).
  {
    exact (!(id_right _)).
  }
  use cat_univ_resize_monic_eq ; cbn.
  apply idpath.
Qed.
