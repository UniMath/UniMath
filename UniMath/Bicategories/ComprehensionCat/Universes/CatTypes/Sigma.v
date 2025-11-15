(**

 Codes for ∑-types in a universe of a category

 A universe is said to be closed under ∑-types if the dependent sum of any two types in that
 universe also is in that universe. In this file, we develop the basic theory of universes
 that are closed under ∑-types. Specifically, we define when a universe supports codes
 for ∑-types and we define suitable stability condition. In addition, we define when a
 functor preserves such codes, and we show that the identity preserves codes for ∑-types
 and that the composition of functors that preseves codes for ∑-types, also preserve such
 codes. As a result, one can for suitable bicategories of categories with finite limits and
 a universe that has codes for dependent sum types. Finally, we prove the lemma that is
 necessary to show that this bicategory is univalent.

 In the work on algebraic set theory, systems of small maps are used, and one of their axioms
 is that they are closed under composition (see "A brief introduction to algebraic set theory"
 by Awodey or "Algebraic Set Theory" by Joyal and Moerdijk). This axiom corresponds to the
 universe being closed under ∑-types, since ∑-types in categories with finite limits are
 given by composition

 References:
 - "Algebraic Set Theory" by Joyal and Moerdijk
 - "A brief introduction to algebraic set theory" by Awodey

 Contents
 1. Codes for ∑-types
 2. Stability
 3. Preservation
 4. Preservation by identity and composition
 5. Univalence condition

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.

Local Open Scope cat.

Section SigmaInCatWithUniv.
  Context {C : univ_cat_with_finlim_universe}.

  Let el : cat_stable_el_map_coherent C := univ_cat_cat_stable_el_map C.

  (** * 1. Codes for ∑-types *)
  Definition cat_univ_codes_sigma
    : UU
    := ∏ (Γ : C)
         (a : Γ --> univ_cat_universe C)
         (b : cat_el_map_el el a --> univ_cat_universe C),
       ∑ (t : Γ --> univ_cat_universe C)
         (f : z_iso
                (cat_el_map_el el t)
                (cat_el_map_el el b)),
       cat_el_map_mor el t
       =
       f
       · cat_el_map_mor el b
       · cat_el_map_mor el a.

  Proposition isaset_cat_univ_codes_sigma
    : isaset cat_univ_codes_sigma.
  Proof.
    use impred_isaset ; intros Γ.
    use impred_isaset ; intros a.
    use impred_isaset ; intros b.
    use isaset_total2.
    - apply homset_property.
    - intros s.
      use isaset_total2.
      + apply isaset_z_iso.
      + intro f.
        apply isasetaprop.
        apply homset_property.
  Qed.

  Definition make_cat_univ_codes_sigma
             (t : ∏ (Γ : C)
                    (a : Γ --> univ_cat_universe C)
                    (b : cat_el_map_el el a --> univ_cat_universe C),
                  Γ --> univ_cat_universe C)
             (f : ∏ (Γ : C)
                    (a : Γ --> univ_cat_universe C)
                    (b : cat_el_map_el el a --> univ_cat_universe C),
                  z_iso
                    (cat_el_map_el el (t Γ a b))
                    (cat_el_map_el el b))
             (p : ∏ (Γ : C)
                    (a : Γ --> univ_cat_universe C)
                    (b : cat_el_map_el el a --> univ_cat_universe C),
                  cat_el_map_mor el (t Γ a b)
                  =
                  f Γ a b
                  · cat_el_map_mor el b
                  · cat_el_map_mor el a)
    : cat_univ_codes_sigma
    := λ Γ a b, t Γ a b ,, f Γ a b ,, p Γ a b.

  Definition cat_univ_codes_sigma_ty
             (Σ : cat_univ_codes_sigma)
             {Γ : C}
             (a : Γ --> univ_cat_universe C)
             (b : cat_el_map_el el a --> univ_cat_universe C)
    : Γ --> univ_cat_universe C
    := pr1 (Σ Γ a b).

  Definition cat_univ_codes_sigma_iso
             (Σ : cat_univ_codes_sigma)
             {Γ : C}
             (a : Γ --> univ_cat_universe C)
             (b : cat_el_map_el el a --> univ_cat_universe C)
    : z_iso
        (cat_el_map_el el (cat_univ_codes_sigma_ty Σ a b))
        (cat_el_map_el el b)
    := pr12 (Σ Γ a b).

  Proposition cat_univ_codes_sigma_comm
              (Σ : cat_univ_codes_sigma)
              {Γ : C}
              (a : Γ --> univ_cat_universe C)
              (b : cat_el_map_el el a --> univ_cat_universe C)
    : cat_el_map_mor el (cat_univ_codes_sigma_ty Σ a b)
      =
      cat_univ_codes_sigma_iso Σ a b
      · cat_el_map_mor el b
      · cat_el_map_mor el a.
  Proof.
    exact (pr22 (Σ Γ a b)).
  Defined.

  Proposition cat_univ_codes_sigma_eq
              {Σ₁ Σ₂ : cat_univ_codes_sigma}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (b : cat_el_map_el el a --> univ_cat_universe C),
                   cat_univ_codes_sigma_ty Σ₁ a b
                   =
                   cat_univ_codes_sigma_ty Σ₂ a b)
              (q : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (b : cat_el_map_el el a --> univ_cat_universe C),
                   cat_el_map_el_eq el (!(p Γ a b))
                   · cat_univ_codes_sigma_iso Σ₁ a b
                   =
                   cat_univ_codes_sigma_iso Σ₂ a b)
    : Σ₁ = Σ₂.
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
      unfold z_iso.
      use z_iso_eq.
      etrans.
      {
        apply (pr1_transportf (P := λ x (f : cat_el_map_el el x --> _), is_z_isomorphism _)).
      }
      rewrite transportf_cat_el_map_el.
      exact (q Γ a b).
  Qed.

  Proposition cat_univ_codes_sigma_ty_eq
              (Σ : cat_univ_codes_sigma)
              {Γ : C}
              {a a' : Γ --> univ_cat_universe C}
              (p : a = a')
              {b : cat_el_map_el el a --> univ_cat_universe C}
              {b' : cat_el_map_el el a' --> univ_cat_universe C}
              (q : b = cat_el_map_el_eq el p · b')
    : cat_univ_codes_sigma_ty Σ a b
      =
      cat_univ_codes_sigma_ty Σ a' b'.
  Proof.
    induction p.
    cbn in q.
    rewrite id_left in q.
    induction q.
    apply idpath.
  Qed.

  Proposition cat_univ_codes_sigma_z_iso_eq_lem
              (Σ : cat_univ_codes_sigma)
              {Γ : C}
              {a : Γ --> univ_cat_universe C}
              {b : cat_el_map_el el a --> univ_cat_universe C}
              {b' : cat_el_map_el el a --> univ_cat_universe C}
              (q : b = b')
              (r : cat_univ_codes_sigma_ty Σ a b = cat_univ_codes_sigma_ty Σ a b')
    : cat_el_map_el_eq el r · cat_univ_codes_sigma_iso Σ a b'
      =
      cat_univ_codes_sigma_iso Σ a b · cat_el_map_el_eq el q.
  Proof.
    induction q.
    assert (r = idpath _) as ->.
    {
      apply homset_property.
    }
    cbn.
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  Proposition cat_univ_codes_sigma_z_iso_eq
              (Σ : cat_univ_codes_sigma)
              {Γ : C}
              {a a' : Γ --> univ_cat_universe C}
              (p : a = a')
              {b : cat_el_map_el el a --> univ_cat_universe C}
              {b' : cat_el_map_el el a' --> univ_cat_universe C}
              (q : b = cat_el_map_el_eq el p · b')
    : cat_el_map_el_eq el (cat_univ_codes_sigma_ty_eq Σ p q)
      · cat_univ_codes_sigma_iso Σ a' b'
      =
      cat_univ_codes_sigma_iso Σ a b
      · cat_el_map_el_eq el q
      · cat_el_map_pb_mor el _ _.
  Proof.
    induction p.
    etrans.
    {
      use cat_univ_codes_sigma_z_iso_eq_lem.
      refine (q @ _).
      apply id_left.
    }
    rewrite !assoc'.
    apply maponpaths.
    cbn.
    rewrite (cat_el_map_pb_mor_id (univ_cat_cat_stable_el_map C)).
    rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
    apply idpath.
  Qed.

  Proposition cat_univ_codes_sigma_z_iso_eq'
              (Σ : cat_univ_codes_sigma)
              {Γ : C}
              {a a' : Γ --> univ_cat_universe C}
              (p : a = a')
              {b : cat_el_map_el el a --> univ_cat_universe C}
              {b' : cat_el_map_el el a' --> univ_cat_universe C}
              (q : b = cat_el_map_el_eq el p · b')
    : (cat_univ_codes_sigma_iso Σ a' b' : _ --> _)
      =
      cat_el_map_el_eq el (!(cat_univ_codes_sigma_ty_eq Σ p q))
      · cat_univ_codes_sigma_iso Σ a b
      · cat_el_map_el_eq el q
      · cat_el_map_pb_mor el _ _.
  Proof.
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      refine (!_).
      apply cat_univ_codes_sigma_z_iso_eq.
    }
    rewrite !assoc.
    rewrite cat_el_map_el_eq_comp.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply cat_el_map_el_eq_id.
  Qed.

  (** * 2. Stability *)
  Definition is_stable_cat_univ_codes_sigma
             (Σ : cat_univ_codes_sigma)
    : UU
    := ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (a : Δ --> univ_cat_universe C)
         (b : cat_el_map_el el a --> univ_cat_universe C),
       ∑ (p : s · cat_univ_codes_sigma_ty Σ a b
              =
              cat_univ_codes_sigma_ty Σ (s · a) (cat_el_map_pb_mor el s a · b)),
       cat_el_map_pb_mor _ _ _ · cat_univ_codes_sigma_iso Σ a b
       =
       cat_el_map_el_eq el p
       · cat_univ_codes_sigma_iso Σ (s · a) (cat_el_map_pb_mor el s a · b)
       · cat_el_map_pb_mor _ _ _.

  Proposition isaprop_is_stable_cat_univ_codes_sigma
              (Σ : cat_univ_codes_sigma)
    : isaprop (is_stable_cat_univ_codes_sigma Σ).
  Proof.
    repeat (use impred ; intro).
    use isaproptotal2.
    - intro.
      apply homset_property.
    - intros.
      apply homset_property.
  Qed.

  Definition cat_univ_stable_codes_sigma
    : UU
    := ∑ (Σ : cat_univ_codes_sigma),
       is_stable_cat_univ_codes_sigma Σ.

  Proposition isaset_cat_univ_stable_codes_sigma
    : isaset cat_univ_stable_codes_sigma.
  Proof.
    use isaset_total2.
    - exact isaset_cat_univ_codes_sigma.
    - intro.
      apply isasetaprop.
      apply isaprop_is_stable_cat_univ_codes_sigma.
  Qed.

  Definition make_cat_univ_stable_codes_sigma
             (Σ : cat_univ_codes_sigma)
             (H : is_stable_cat_univ_codes_sigma Σ)
    : cat_univ_stable_codes_sigma
    := Σ ,, H.

  Coercion cat_univ_stable_codes_sigma_to_codes
           (Σ : cat_univ_stable_codes_sigma)
    : cat_univ_codes_sigma
    := pr1 Σ.

  Proposition cat_univ_stable_codes_sigma_stable
              (Σ : cat_univ_stable_codes_sigma)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : Δ --> univ_cat_universe C)
              (b : cat_el_map_el el a --> univ_cat_universe C)
    : s · cat_univ_codes_sigma_ty Σ a b
      =
      cat_univ_codes_sigma_ty Σ (s · a) (cat_el_map_pb_mor el s a · b).
  Proof.
    exact (pr1 (pr2 Σ Γ Δ s a b)).
  Defined.

  Proposition cat_univ_stable_codes_sigma_z_iso_stable
              (Σ : cat_univ_stable_codes_sigma)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a : Δ --> univ_cat_universe C)
              (b : cat_el_map_el el a --> univ_cat_universe C)
    : cat_el_map_pb_mor _ _ _ · cat_univ_codes_sigma_iso Σ a b
      =
      cat_el_map_el_eq el (cat_univ_stable_codes_sigma_stable Σ s a b)
      · cat_univ_codes_sigma_iso Σ (s · a) (cat_el_map_pb_mor el s a · b)
      · cat_el_map_pb_mor _ _ _.
  Proof.
    exact (pr2 (pr2 Σ Γ Δ s a b)).
  Defined.

  Proposition cat_univ_stable_codes_sigma_eq
              {Σ₁ Σ₂ : cat_univ_stable_codes_sigma}
              (p : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (b : cat_el_map_el el a --> univ_cat_universe C),
                   cat_univ_codes_sigma_ty Σ₁ a b
                   =
                   cat_univ_codes_sigma_ty Σ₂ a b)
              (q : ∏ (Γ : C)
                     (a : Γ --> univ_cat_universe C)
                     (b : cat_el_map_el el a --> univ_cat_universe C),
                   cat_el_map_el_eq el (!(p Γ a b))
                   · cat_univ_codes_sigma_iso Σ₁ a b
                   =
                   cat_univ_codes_sigma_iso Σ₂ a b)
    : Σ₁ = Σ₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_stable_cat_univ_codes_sigma.
    }
    use cat_univ_codes_sigma_eq.
    - exact p.
    - exact q.
  Qed.
End SigmaInCatWithUniv.

Arguments cat_univ_codes_sigma C : clear implicits.
Arguments cat_univ_stable_codes_sigma C : clear implicits.

Section PreservationSigmaCodes.
  Context {C₁ C₂ : univ_cat_with_finlim_universe}
          (Σ₁ : cat_univ_stable_codes_sigma C₁)
          (Σ₂ : cat_univ_stable_codes_sigma C₂)
          {F : functor_finlim_universe C₁ C₂}.

  Let el₁ : cat_stable_el_map_coherent C₁ := univ_cat_cat_stable_el_map C₁.
  Let el₂ : cat_stable_el_map_coherent C₂ := univ_cat_cat_stable_el_map C₂.

  Let Fel : functor_preserves_el
              (univ_cat_cat_stable_el_map C₁)
              (univ_cat_cat_stable_el_map C₂)
              F
    := functor_finlim_universe_preserves_el F.

  (** * 3. Preservation *)
  Definition functor_preserves_stable_codes_sigma_ty
    : UU
    := ∏ (Γ : C₁)
         (a : Γ --> univ_cat_universe C₁)
         (b : cat_el_map_el el₁ a --> univ_cat_universe C₁),
       #F (cat_univ_codes_sigma_ty Σ₁ a b) · functor_on_universe F
       =
       cat_univ_codes_sigma_ty
         Σ₂
         (#F a · functor_on_universe F)
         (inv_from_z_iso (functor_el_map_iso Fel a)
          · #F b
          · functor_on_universe F).

  Definition functor_preserves_stable_codes_sigma_z_iso
             (p : functor_preserves_stable_codes_sigma_ty)
    : UU
    := ∏ (Γ : C₁)
         (a : Γ --> univ_cat_universe C₁)
         (b : cat_el_map_el el₁ a --> univ_cat_universe C₁),
       #F(cat_univ_codes_sigma_iso Σ₁ a b)
       · functor_el_map_iso Fel _
       =
       functor_el_map_iso Fel _
       · cat_el_map_el_eq el₂ (p Γ a b)
       · cat_univ_codes_sigma_iso
           Σ₂
           (#F a · functor_on_universe F)
           (inv_from_z_iso (functor_el_map_iso Fel a)
            · #F b
            · functor_on_universe F)
       · cat_el_map_el_eq el₂ (assoc' _ _ _)
       · cat_el_map_pb_mor el₂ _ _.

  Definition functor_preserves_stable_codes_sigma
    : UU
    := ∑ (p : functor_preserves_stable_codes_sigma_ty),
       functor_preserves_stable_codes_sigma_z_iso p.

  Proposition isaprop_functor_preserves_stable_codes_sigma
    : isaprop functor_preserves_stable_codes_sigma.
  Proof.
    use isaproptotal2.
    - intro.
      repeat (use impred ; intro).
      apply homset_property.
    - intros.
      repeat (use funextsec ; intro).
      apply homset_property.
  Qed.

  Definition make_functor_preserves_stable_codes_sigma
             (p : functor_preserves_stable_codes_sigma_ty)
             (q : functor_preserves_stable_codes_sigma_z_iso p)
    : functor_preserves_stable_codes_sigma
    := p ,, q.

  Proposition functor_preserves_stable_codes_sigma_on_code
              (p : functor_preserves_stable_codes_sigma)
              {Γ : C₁}
              (a : Γ --> univ_cat_universe C₁)
              (b : cat_el_map_el el₁ a --> univ_cat_universe C₁)
    : #F (cat_univ_codes_sigma_ty Σ₁ a b) · functor_on_universe F
      =
      cat_univ_codes_sigma_ty
        Σ₂
        (#F a · functor_on_universe F)
        (inv_from_z_iso (functor_el_map_iso Fel a)
         · #F b
         · functor_on_universe F).
  Proof.
    exact (pr1 p Γ a b).
  Defined.

  Proposition functor_preserves_stable_codes_sigmas_on_z_iso
              (p : functor_preserves_stable_codes_sigma)
              {Γ : C₁}
              (a : Γ --> univ_cat_universe C₁)
              (b : cat_el_map_el el₁ a --> univ_cat_universe C₁)
    : #F(cat_univ_codes_sigma_iso Σ₁ a b)
      · functor_el_map_iso Fel _
      =
      functor_el_map_iso Fel _
      · cat_el_map_el_eq el₂ (functor_preserves_stable_codes_sigma_on_code p a b)
      · cat_univ_codes_sigma_iso
          Σ₂
          (#F a · functor_on_universe F)
          (inv_from_z_iso (functor_el_map_iso Fel a)
           · #F b
           · functor_on_universe F)
      · cat_el_map_el_eq el₂ (assoc' _ _ _)
      · cat_el_map_pb_mor el₂ _ _.
  Proof.
    exact (pr2 p Γ a b).
  Defined.
End PreservationSigmaCodes.

Arguments functor_preserves_stable_codes_sigma
  {C₁ C₂} Σ₁ Σ₂ F.
Arguments functor_preserves_stable_codes_sigma_ty
  {C₁ C₂} Σ₁ Σ₂ F.
Arguments functor_preserves_stable_codes_sigma_z_iso
  {C₁ C₂ Σ₁ Σ₂ F} p.
Arguments functor_preserves_stable_codes_sigma_on_code
  {C₁ C₂ Σ₁ Σ₂ F} p {Γ} a b.
Arguments functor_preserves_stable_codes_sigmas_on_z_iso
  {C₁ C₂ Σ₁ Σ₂ F} p {Γ} a b.

(** * 4. Preservation by identity and composition *)
Proposition identity_preserves_stable_codes_sigma_ty
            {C : univ_cat_with_finlim_universe}
            (Σ : cat_univ_stable_codes_sigma C)
  : functor_preserves_stable_codes_sigma_ty Σ Σ (identity _).
Proof.
  intros Γ a b ; cbn.
  refine (id_right _ @ _).
  use cat_univ_codes_sigma_ty_eq.
  - rewrite id_right.
    apply idpath.
  - refine (!_).
    etrans.
    {
      apply maponpaths.
      apply id_right.
    }
    refine (assoc _ _ _ @ _).
    rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply cat_el_map_el_eq_id.
Qed.

Proposition identity_preserves_stable_codes_sigma_z_iso
            {C : univ_cat_with_finlim_universe}
            (Σ : cat_univ_stable_codes_sigma C)
  : functor_preserves_stable_codes_sigma_z_iso
      (identity_preserves_stable_codes_sigma_ty Σ).
Proof.
  intros Γ a b ; cbn.
  etrans.
  {
    apply maponpaths_2.
    use (cat_univ_codes_sigma_z_iso_eq' Σ (id_right _) (id_right _)).
  }
  do 3 refine (assoc' _ _ _ @ _).
  etrans.
  {
    do 3 apply maponpaths.
    refine (!_).
    use cat_el_map_pb_mor_eq.
    apply maponpaths.
    exact (!(id_right _)).
  }
  do 3 refine (assoc _ _ _ @ _).
  apply maponpaths_2.
  refine (assoc' _ _ _ @ _).
  rewrite !(cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
  use maponpaths_compose.
  - apply maponpaths_2.
    apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C)).
  - apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C)).
Qed.

Proposition identity_preserves_stable_codes_sigma
            {C : univ_cat_with_finlim_universe}
            (Σ : cat_univ_stable_codes_sigma C)
  : functor_preserves_stable_codes_sigma Σ Σ (identity _).
Proof.
  use make_functor_preserves_stable_codes_sigma.
  - exact (identity_preserves_stable_codes_sigma_ty Σ).
  - exact (identity_preserves_stable_codes_sigma_z_iso Σ).
Qed.

(**
   This reduces the memory consumption in the next section
 *)
Unset Kernel Term Sharing.

Section CompPreservation.
  Context {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
          {Σ₁ : cat_univ_stable_codes_sigma C₁}
          {Σ₂ : cat_univ_stable_codes_sigma C₂}
          {Σ₃ : cat_univ_stable_codes_sigma C₃}
          {F : functor_finlim_universe C₁ C₂}
          (Fc : functor_preserves_stable_codes_sigma Σ₁ Σ₂ F)
          {G : functor_finlim_universe C₂ C₃}
          (Gc : functor_preserves_stable_codes_sigma Σ₂ Σ₃ G).

  Proposition comp_preserves_stable_codes_sigma_ty
    : functor_preserves_stable_codes_sigma_ty Σ₁ Σ₃ (F · G).
  Proof.
    intros Γ a b ; cbn.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      apply (functor_preserves_stable_codes_sigma_on_code Fc).
    }
    etrans.
    {
      apply (functor_preserves_stable_codes_sigma_on_code Gc).
    }
    use cat_univ_codes_sigma_ty_eq.
    - rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    - etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        refine (functor_comp _ _ _ @ _).
        apply maponpaths_2.
        apply functor_comp.
      }
      rewrite !assoc.
      do 4 apply maponpaths_2.
      refine (!(id_left _) @ _).
      apply maponpaths_2.
      rewrite (cat_el_map_el_eq_inv (univ_cat_cat_stable_el_map C₃)).
      rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C₃)).
      refine (!_).
      apply cat_el_map_el_eq_id.
  Qed.

  Proposition comp_preserves_stable_codes_sigma_z_iso
    : functor_preserves_stable_codes_sigma_z_iso
        comp_preserves_stable_codes_sigma_ty.
  Proof.
    intros Γ a b.
    do 2 refine (assoc _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!(functor_comp G _ _) @ _).
      apply maponpaths.
      apply (functor_preserves_stable_codes_sigmas_on_z_iso Fc).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (functor_comp G _ _ @ _).
      apply maponpaths_2.
      refine (functor_comp G _ _ @ _).
      apply maponpaths_2.
      refine (functor_comp G _ _ @ _).
      apply maponpaths_2.
      apply (functor_comp G).
    }
    do 5 refine (assoc' _ _ _ @ _).
    do 4 refine (_ @ assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      do 3 apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply (functor_preserves_el_path (functor_finlim_universe_preserves_el G)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply functor_el_map_iso_eq_alt.
    }
    etrans.
    {
      apply maponpaths.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply (functor_preserves_stable_codes_sigmas_on_z_iso Gc).
    }
    etrans.
    {
      do 8 (refine (assoc _ _ _ @ _) ; apply maponpaths_2).
      apply functor_el_map_iso_eq_alt.
    }
    do 8 refine (assoc' _ _ _ @ _).
    refine (_ @ assoc _ _ _).
    apply maponpaths.
    do 5 refine (assoc _ _ _ @ _).
    do 3 refine (_ @ assoc' _ _ _).
    rewrite !cat_el_map_el_eq_comp.
    do 2 refine (_ @ assoc _ _ _).
    use z_iso_inv_to_left.
    etrans.
    {
      apply maponpaths_2.
      apply cat_el_map_el_eq_inv.
    }
    do 3 refine (assoc _ _ _ @ _).
    assert (#G(#F a) · (#G (functor_on_universe F) · functor_on_universe G)
            =
            #G(#F a · functor_on_universe F) · functor_on_universe G)
      as q₁.
    {
      rewrite !functor_comp.
      rewrite !assoc'.
      apply idpath.
    }
    etrans.
    {
      do 3 apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      rewrite cat_el_map_el_eq_comp.
      simple refine  (_ @ cat_univ_codes_sigma_z_iso_eq _ _ _).
      - apply maponpaths_2.
        apply cat_el_map_el_eq_eq.
      - exact q₁.
      - cbn.
        rewrite !assoc.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (_ @ assoc' _ _ _).
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (functor_comp G _ _ @ _).
          apply maponpaths_2.
          apply functor_comp.
        }
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        do 2 apply maponpaths_2.
        rewrite (cat_el_map_el_eq_inv (univ_cat_cat_stable_el_map C₃)).
        apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C₃)).
    }
    do 7 refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_pb_mor_comp.
    }
    refine (!_).
    etrans.
    {
      do 6 apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      apply maponpaths.
      refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      apply (functor_comp G).
    }
    etrans.
    {
      do 4 apply maponpaths.
      do 2 refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      rewrite !cat_el_map_el_eq_comp.
      apply idpath.
    }
    do 4 refine (assoc _ _ _ @ _).
    refine (_ @ assoc' _ _ _).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      refine (assoc _ _ _ @ _).
      rewrite cat_el_map_el_eq_comp.
      apply maponpaths.
      apply cat_el_map_pb_mor_comp.
    }
    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (assoc _ _ _ @ _).
      rewrite cat_el_map_el_eq_comp.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      apply maponpaths.
      do 2 refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      refine (functor_comp _ _ _ @ _).
      apply maponpaths_2.
      apply (functor_comp G).
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      rewrite cat_el_map_el_eq_comp.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      do 2 refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      refine (functor_comp _ _ _ @ _).
      apply maponpaths_2.
      apply (functor_comp G).
    }
    refine (assoc _ _ _ @ _).
    rewrite cat_el_map_el_eq_comp.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (cat_el_map_pb_mor_subst_eq _ _ _).
      refine (cat_el_map_el_eq_inv _ _ @ _).
      apply cat_el_map_el_eq_eq.
    }
    refine (assoc _ _ _ @ _).
    rewrite cat_el_map_el_eq_comp.
    apply maponpaths_2.
    apply cat_el_map_el_eq_eq.
  Qed.

  Proposition comp_preserves_stable_codes_sigma
    : functor_preserves_stable_codes_sigma Σ₁ Σ₃ (F · G).
  Proof.
    use make_functor_preserves_stable_codes_sigma.
    - exact comp_preserves_stable_codes_sigma_ty.
    - exact comp_preserves_stable_codes_sigma_z_iso.
  Qed.
End CompPreservation.

(** * 5. Univalence condition *)
Proposition sigma_univ_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            {Σ₁ Σ₂ : cat_univ_stable_codes_sigma C}
            (Fc : functor_preserves_stable_codes_sigma Σ₁ Σ₂ (identity _))
  : Σ₁ = Σ₂.
Proof.
  use cat_univ_stable_codes_sigma_eq.
  - intros Γ a b.
    pose (functor_preserves_stable_codes_sigma_on_code Fc a b) as p.
    simpl in p.
    refine (!(id_right _) @ _).
    refine (p @ _).
    use cat_univ_codes_sigma_ty_eq ; cbn.
    + apply id_right.
    + apply id_right.
  - intros Γ a b.
    pose (functor_preserves_stable_codes_sigmas_on_z_iso Fc a b) as p.
    simpl in p.
    etrans.
    {
      apply maponpaths.
      refine (_ @ maponpaths
                    (λ z, z · cat_el_map_el_eq
                                (univ_cat_cat_stable_el_map C)
                                (id_right _))
                    p).
      rewrite !assoc'.
      rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (cat_el_map_el_eq_id (univ_cat_cat_stable_el_map C)).
      }
      apply id_right.
    }
    cbn.
    refine (assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2 ; refine (assoc _ _ _ @ _).
      apply maponpaths_2 ; refine (assoc _ _ _ @ _).
      apply maponpaths_2 ; refine (assoc _ _ _ @ _).
      apply maponpaths_2 ; refine (assoc _ _ _ @ _).
      rewrite !(cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
      apply idpath.
    }
    refine (!_).
    refine (cat_univ_codes_sigma_z_iso_eq' Σ₂ (id_right _) (id_right _) @ _).
    do 2 refine (assoc' _ _ _ @ _).
    do 3 refine (_ @ assoc _ _ _).
    use maponpaths_compose.
    {
      apply cat_el_map_el_eq_eq.
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      use cat_el_map_pb_mor_eq.
      refine (assoc _ _ _ @ _).
      apply id_right.
    }
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
    apply cat_el_map_el_eq_eq.
Qed.
