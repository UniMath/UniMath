(**

 Codes for sum types in a universe of a category

 A universe is said to be closed under sum types if the binary sum of any two types in that
 universe also is in that universe. In this file, we develop the basic theory of universes
 that are closed under sum types. Specifically, we define when a universe supports codes
 for sum types and we define suitable stability condition. In addition, we define when a
 functor preserves such codes, and we show that the identity preserves codes for sum types
 and that the composition of functors that preseves codes for sum types, also preserve such
 codes. As a result, one can for suitable bicategories of categories with finite limits and
 a universe that has codes for binary sum types. Finally, we prove the lemma that is
 necessary to show that this bicategory is univalent.

 In the literature, various axioms are given that express that the universe is closed under
 sum types. Our approach follows "A brief introduction to algebraic set theory" by Awodey.
 Awodey's work is based on systems of small maps, which, intuitively represent the
 inhabitants of the universe. Awodey requires the following closure axiom: if both
 `f : A --> Γ` and `g : B --> Γ` are small, then so is `[f , g] : A + B --> Γ`. A different
 axiom is given in "Algebraic Set Theory" by Joyal and Moerdijk. While they also work with
 systems of small maps, they require a slightly different axiom: if `f : A --> Γ` and
 `g : B --> Δ` are small, then so is `f + g : A + B --> Γ + Δ`. The reason why we follow
 Awodey's development, is because it corresponds to what is usually required in Martin-Löf
 type theory.

 References:
 - "Algebraic Set Theory" by Joyal and Moerdijk
 - "A brief introduction to algebraic set theory" by Awodey

 Contents
 1. Codes for sum types
 2. Stability
 3. Preservation
 4. Preservation by identity and composition
 5. Univalence condition

                                                                                           *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.

Local Open Scope cat.

Section SumsInCatWithUniv.
  Context {C : univ_cat_with_finlim_universe}
          {BC : BinCoproducts C}.

  Let el : cat_stable_el_map_coherent C := univ_cat_cat_stable_el_map C.

  (** * 1. Codes for sum types *)
  Definition cat_univ_codes_sums
    : UU
    := ∏ (Γ : C)
         (a b : Γ --> univ_cat_universe C),
       ∑ (s : Γ --> univ_cat_universe C)
         (f : z_iso
                (BC (cat_el_map_el el a) (cat_el_map_el el b))
                (cat_el_map_el el s)),
       BinCoproductArrow _ (cat_el_map_mor el a) (cat_el_map_mor el b)
       =
       f · cat_el_map_mor el s.

  Proposition isaset_cat_univ_codes_sums
    : isaset cat_univ_codes_sums.
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

  Definition make_cat_univ_codes_sums
             (s : ∏ (Γ : C)
                    (a b : Γ --> univ_cat_universe C),
                  Γ --> univ_cat_universe C)
             (f : ∏ (Γ : C)
                    (a b : Γ --> univ_cat_universe C),
                  z_iso
                    (BC (cat_el_map_el el a) (cat_el_map_el el b))
                    (cat_el_map_el el (s Γ a b)))
             (p : ∏ (Γ : C)
                    (a b : Γ --> univ_cat_universe C),
                  BinCoproductArrow _ (cat_el_map_mor el a) (cat_el_map_mor el b)
                  =
                  f Γ a b · cat_el_map_mor el (s Γ a b))
    : cat_univ_codes_sums
    := λ Γ a b, s Γ a b ,, f Γ a b ,, p Γ a b.

  Definition cat_univ_codes_sums_sum
             (sum : cat_univ_codes_sums)
             {Γ : C}
             (a b : Γ --> univ_cat_universe C)
    : Γ --> univ_cat_universe C
    := pr1 (sum Γ a b).

  Definition cat_univ_codes_sums_z_iso
             (sum : cat_univ_codes_sums)
             {Γ : C}
             (a b : Γ --> univ_cat_universe C)
    : z_iso
        (BC (cat_el_map_el el a) (cat_el_map_el el b))
        (cat_el_map_el el (cat_univ_codes_sums_sum sum a b))
    := pr12 (sum Γ a b).

  Proposition cat_univ_codes_sums_sum_comm
              (sum : cat_univ_codes_sums)
              {Γ : C}
              (a b : Γ --> univ_cat_universe C)
    : BinCoproductArrow _ (cat_el_map_mor el a) (cat_el_map_mor el b)
      =
      cat_univ_codes_sums_z_iso sum a b
      · cat_el_map_mor el _.
  Proof.
    exact (pr22 (sum Γ a b)).
  Defined.

  Proposition cat_univ_codes_sums_sum_in1
              (sum : cat_univ_codes_sums)
              {Γ : C}
              (a b : Γ --> univ_cat_universe C)
    : cat_el_map_mor el a
      =
      BinCoproductIn1 _
      · cat_univ_codes_sums_z_iso sum a b
      · cat_el_map_mor el _.
  Proof.
    refine (!_).
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply cat_univ_codes_sums_sum_comm.
    }
    rewrite BinCoproductIn1Commutes.
    apply idpath.
  Qed.

  Proposition cat_univ_codes_sums_sum_in2
              (sum : cat_univ_codes_sums)
              {Γ : C}
              (a b : Γ --> univ_cat_universe C)
    : cat_el_map_mor el b
      =
      BinCoproductIn2 _
      · cat_univ_codes_sums_z_iso sum a b
      · cat_el_map_mor el _.
  Proof.
    refine (!_).
    rewrite assoc'.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply cat_univ_codes_sums_sum_comm.
    }
    rewrite BinCoproductIn2Commutes.
    apply idpath.
  Qed.

  Proposition cat_univ_codes_sums_eq
              {sum₁ sum₂ : cat_univ_codes_sums}
              (p : ∏ (Γ : C)
                     (a b : Γ --> univ_cat_universe C),
                   cat_univ_codes_sums_sum sum₁ a b
                   =
                   cat_univ_codes_sums_sum sum₂ a b)
              (q : ∏ (Γ : C)
                     (a b : Γ --> univ_cat_universe C),
                   cat_univ_codes_sums_z_iso sum₁ a b · cat_el_map_el_eq el (p Γ a b)
                   =
                   cat_univ_codes_sums_z_iso sum₂ a b)
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
      unfold z_iso.
      use z_iso_eq.
      etrans.
      {
        apply (pr1_transportf (P := λ x (f : _ --> cat_el_map_el el x), is_z_isomorphism _)).
      }
      rewrite transportf_cat_el_map_el'.
      exact (q Γ a b).
  Qed.

  Proposition cat_univ_codes_sums_sum_eq
              (sum : cat_univ_codes_sums)
              {Γ : C}
              {a a' b b' : Γ --> univ_cat_universe C}
              (p : a = a')
              (q : b = b')
    : cat_univ_codes_sums_sum sum a b
      =
      cat_univ_codes_sums_sum sum a' b'.
  Proof.
    induction p, q.
    apply idpath.
  Qed.

  Proposition cat_univ_codes_sums_z_iso_eq
              (sum : cat_univ_codes_sums)
              {Γ : C}
              {a a' b b' : Γ --> univ_cat_universe C}
              (p : a = a')
              (q : b = b')
    : (cat_univ_codes_sums_z_iso sum a b : _ --> _)
      =
      BinCoproductOfArrows _ _ _ (cat_el_map_el_eq el p) (cat_el_map_el_eq el q)
      · cat_univ_codes_sums_z_iso sum a' b'
      · cat_el_map_el_eq el (!(cat_univ_codes_sums_sum_eq sum p q)).
  Proof.
    induction p, q ; cbn.
    rewrite BinCoproduct_of_identities.
    rewrite id_left.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (cat_el_map_el_eq_id (univ_cat_cat_stable_el_map C)).
    }
    apply id_right.
  Qed.

  (** * 2. Stability *)
  Definition is_stable_cat_univ_codes_sums
             (sum : cat_univ_codes_sums)
    : UU
    := ∏ (Γ Δ : C)
         (s : Γ --> Δ)
         (a b : Δ --> univ_cat_universe C),
       ∑ (p : s · cat_univ_codes_sums_sum sum a b
              =
              cat_univ_codes_sums_sum sum (s · a) (s · b)),
       BinCoproductOfArrows _ _ _ (cat_el_map_pb_mor el s a) (cat_el_map_pb_mor el s b)
       · cat_univ_codes_sums_z_iso sum a b
       =
       cat_univ_codes_sums_z_iso sum (s · a) (s · b)
       · cat_el_map_el_eq el (!p)
       · cat_el_map_pb_mor el s (cat_univ_codes_sums_sum sum a b).

  Proposition isaprop_is_stable_cat_univ_codes_sums
              (sum : cat_univ_codes_sums)
    : isaprop (is_stable_cat_univ_codes_sums sum).
  Proof.
    repeat (use impred ; intro).
    use isaproptotal2.
    - intro.
      apply homset_property.
    - intros.
      apply homset_property.
  Qed.

  Definition cat_univ_stable_codes_sums
    : UU
    := ∑ (sum : cat_univ_codes_sums),
       is_stable_cat_univ_codes_sums sum.

  Proposition isaset_cat_univ_stable_codes_sums
    : isaset cat_univ_stable_codes_sums.
  Proof.
    use isaset_total2.
    - exact isaset_cat_univ_codes_sums.
    - intro.
      apply isasetaprop.
      apply isaprop_is_stable_cat_univ_codes_sums.
  Qed.

  Definition make_cat_univ_stable_codes_sums
             (sum : cat_univ_codes_sums)
             (H : is_stable_cat_univ_codes_sums sum)
    : cat_univ_stable_codes_sums
    := sum ,, H.

  Coercion cat_univ_stable_codes_sums_to_codes
           (sum : cat_univ_stable_codes_sums)
    : cat_univ_codes_sums
    := pr1 sum.

  Proposition cat_univ_codes_sums_sum_stable
              (sum : cat_univ_stable_codes_sums)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a b : Δ --> univ_cat_universe C)
    : s · cat_univ_codes_sums_sum sum a b
      =
      cat_univ_codes_sums_sum sum (s · a) (s · b).
  Proof.
    exact (pr1 (pr2 sum Γ Δ s a b)).
  Defined.

  Proposition cat_univ_codes_sums_z_iso_stable
              (sum : cat_univ_stable_codes_sums)
              {Γ Δ : C}
              (s : Γ --> Δ)
              (a b : Δ --> univ_cat_universe C)
    : BinCoproductOfArrows
        _ _ _
        (cat_el_map_pb_mor el s a)
        (cat_el_map_pb_mor el s b)
      · cat_univ_codes_sums_z_iso sum a b
      =
      cat_univ_codes_sums_z_iso sum (s · a) (s · b)
      · cat_el_map_el_eq el (!(cat_univ_codes_sums_sum_stable sum s a b))
      · cat_el_map_pb_mor el s (cat_univ_codes_sums_sum sum a b).
  Proof.
    exact (pr2 (pr2 sum Γ Δ s a b)).
  Defined.

  Proposition cat_univ_stable_codes_sums_eq
              {sum₁ sum₂ : cat_univ_stable_codes_sums}
              (p : ∏ (Γ : C)
                     (a b : Γ --> univ_cat_universe C),
                   cat_univ_codes_sums_sum sum₁ a b
                   =
                   cat_univ_codes_sums_sum sum₂ a b)
              (q : ∏ (Γ : C)
                     (a b : Γ --> univ_cat_universe C),
                   cat_univ_codes_sums_z_iso sum₁ a b · cat_el_map_el_eq el (p Γ a b)
                   =
                   cat_univ_codes_sums_z_iso sum₂ a b)
    : sum₁ = sum₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_is_stable_cat_univ_codes_sums.
    }
    use cat_univ_codes_sums_eq.
    - exact p.
    - exact q.
  Qed.
End SumsInCatWithUniv.

Arguments cat_univ_codes_sums {C} BC.
Arguments cat_univ_stable_codes_sums {C} BC.

Section PreservationSumCodes.
  Context {C₁ C₂ : univ_cat_with_finlim_universe}
          {BC₁ : BinCoproducts C₁}
          {BC₂ : BinCoproducts C₂}
          (sum₁ : cat_univ_stable_codes_sums BC₁)
          (sum₂ : cat_univ_stable_codes_sums BC₂)
          {F : functor_finlim_universe C₁ C₂}
          (HF : preserves_bincoproduct F).

  Let el₁ : cat_stable_el_map_coherent C₁ := univ_cat_cat_stable_el_map C₁.
  Let el₂ : cat_stable_el_map_coherent C₂ := univ_cat_cat_stable_el_map C₂.

  Let Fel : functor_preserves_el
              (univ_cat_cat_stable_el_map C₁)
              (univ_cat_cat_stable_el_map C₂)
              F
    := functor_finlim_universe_preserves_el F.

  (** * 3. Preservation *)
  Definition functor_preserves_stable_codes_sums_sum
    : UU
    := ∏ (Γ : C₁)
         (a b : Γ --> univ_cat_universe C₁),
       #F(cat_univ_codes_sums_sum sum₁ a b) · functor_on_universe F
       =
       cat_univ_codes_sums_sum
         sum₂
         (#F a · functor_on_universe F)
         (#F b · functor_on_universe F).

  Definition functor_preserves_univ_coprod
             {Γ : C₁}
             (a b : Γ --> univ_cat_universe C₁)
    : F (BC₁ (cat_el_map_el el₁ a) (cat_el_map_el el₁ b))
      -->
      BC₂ (cat_el_map_el el₂ (# F a · functor_on_universe F))
          (cat_el_map_el el₂ (# F b · functor_on_universe F)).
  Proof.
    use (BinCoproductArrow (preserves_bincoproduct_to_bincoproduct F HF _)).
    - refine (_ · BinCoproductIn1 _).
      apply (functor_el_map_iso Fel).
    - refine (_ · BinCoproductIn2 _).
      apply (functor_el_map_iso Fel).
  Defined.

  Definition functor_preserves_stable_codes_sums_z_iso
             (p : functor_preserves_stable_codes_sums_sum)
    : UU
    := ∏ (Γ : C₁)
         (a b : Γ --> univ_cat_universe C₁),
       #F(cat_univ_codes_sums_z_iso sum₁ a b)
       · functor_el_map_iso Fel _
       =
       functor_preserves_univ_coprod a b
       · cat_univ_codes_sums_z_iso sum₂ _ _
       · cat_el_map_el_eq el₂ (!(p Γ a b)).

  Definition functor_preserves_stable_codes_sums
    : UU
    := ∑ (p : functor_preserves_stable_codes_sums_sum),
       functor_preserves_stable_codes_sums_z_iso p.

  Proposition isaprop_functor_preserves_stable_codes_sums_sum
    : isaprop functor_preserves_stable_codes_sums.
  Proof.
    use isaproptotal2.
    - intro.
      repeat (use impred ; intro).
      apply homset_property.
    - intros.
      repeat (use funextsec ; intro).
      apply homset_property.
  Qed.

  Definition make_functor_preserves_stable_codes_sums
             (p : functor_preserves_stable_codes_sums_sum)
             (q : functor_preserves_stable_codes_sums_z_iso p)
    : functor_preserves_stable_codes_sums
    := p ,, q.

  Proposition functor_preserves_stable_codes_sums_on_code
              (p : functor_preserves_stable_codes_sums)
              {Γ : C₁}
              (a b : Γ --> univ_cat_universe C₁)
    : #F(cat_univ_codes_sums_sum sum₁ a b) · functor_on_universe F
      =
      cat_univ_codes_sums_sum
        sum₂
        (#F a · functor_on_universe F)
        (#F b · functor_on_universe F).
  Proof.
    exact (pr1 p Γ a b).
  Defined.

  Proposition functor_preserves_stable_codes_sums_on_z_iso
              (p : functor_preserves_stable_codes_sums)
              {Γ : C₁}
              (a b : Γ --> univ_cat_universe C₁)
    : #F(cat_univ_codes_sums_z_iso sum₁ a b)
      · functor_el_map_iso Fel _
      =
      functor_preserves_univ_coprod a b
      · cat_univ_codes_sums_z_iso sum₂ _ _
      · cat_el_map_el_eq el₂ (!(functor_preserves_stable_codes_sums_on_code p a b)).
  Proof.
    exact (pr2 p Γ a b).
  Defined.
End PreservationSumCodes.

Arguments functor_preserves_stable_codes_sums
  {C₁ C₂ BC₁ BC₂} sum₁ sum₂ F HF.
Arguments functor_preserves_stable_codes_sums_sum
  {C₁ C₂ BC₁ BC₂} sum₁ sum₂ F.
Arguments functor_preserves_stable_codes_sums_z_iso
  {C₁ C₂ BC₁ BC₂} {sum₁ sum₂} F HF p.
Arguments functor_preserves_stable_codes_sums_on_code
  {C₁ C₂ BC₁ BC₂ sum₁ sum₂ F HF} p {Γ} a b.
Arguments functor_preserves_stable_codes_sums_on_z_iso
  {C₁ C₂ BC₁ BC₂ sum₁ sum₂ F HF} p {Γ} a b.

(** * 4. Preservation by identity and composition *)
Proposition identity_preserves_stable_codes_sums_sum
            {C : univ_cat_with_finlim_universe}
            (BC : BinCoproducts C)
            (sum : cat_univ_stable_codes_sums BC)
  : functor_preserves_stable_codes_sums_sum sum sum (id₁ C).
Proof.
  intros Γ a b ; cbn.
  rewrite id_right.
  use cat_univ_codes_sums_sum_eq.
  - rewrite id_right.
    apply idpath.
  - rewrite id_right.
    apply idpath.
Qed.

Proposition identity_preserves_stable_codes_sums_z_iso
            {C : univ_cat_with_finlim_universe}
            (BC : BinCoproducts C)
            (sum : cat_univ_stable_codes_sums BC)
  : functor_preserves_stable_codes_sums_z_iso
      (identity C)
      (identity_preserves_bincoproduct C)
      (identity_preserves_stable_codes_sums_sum BC sum).
Proof.
  intros Γ a b ; cbn.
  etrans.
  {
    apply maponpaths_2.
    exact (cat_univ_codes_sums_z_iso_eq sum (!(id_right _)) (!(id_right _))).
  }
  rewrite !assoc'.
  rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
  rewrite !assoc.
  apply maponpaths.
  apply cat_el_map_el_eq_eq.
Qed.

Proposition identity_preserves_stable_codes_sums
            {C : univ_cat_with_finlim_universe}
            (BC : BinCoproducts C)
            (sum : cat_univ_stable_codes_sums BC)
  : functor_preserves_stable_codes_sums
      sum
      sum
      (identity _)
      (identity_preserves_bincoproduct _).
Proof.
  use make_functor_preserves_stable_codes_sums.
  - exact (identity_preserves_stable_codes_sums_sum BC sum).
  - exact (identity_preserves_stable_codes_sums_z_iso BC sum).
Qed.

Section CompPreservation.
  Context {C₁ C₂ C₃ : univ_cat_with_finlim_universe}
          {BC₁ : BinCoproducts C₁}
          {BC₂ : BinCoproducts C₂}
          {BC₃ : BinCoproducts C₃}
          {sum₁ : cat_univ_stable_codes_sums BC₁}
          {sum₂ : cat_univ_stable_codes_sums BC₂}
          {sum₃ : cat_univ_stable_codes_sums BC₃}
          {F : functor_finlim_universe C₁ C₂}
          {HF : preserves_bincoproduct F}
          (Fc : functor_preserves_stable_codes_sums sum₁ sum₂ F HF)
          {G : functor_finlim_universe C₂ C₃}
          {HG : preserves_bincoproduct G}
          (Gc : functor_preserves_stable_codes_sums sum₂ sum₃ G HG).

  Proposition comp_preserves_stable_codes_sums_sum
    : functor_preserves_stable_codes_sums_sum sum₁ sum₃ (F · G).
  Proof.
    intros Γ a b ; cbn.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      apply (functor_preserves_stable_codes_sums_on_code Fc).
    }
    etrans.
    {
      apply (functor_preserves_stable_codes_sums_on_code Gc).
    }
    use cat_univ_codes_sums_sum_eq ; cbn.
    - rewrite !functor_comp.
      rewrite !assoc'.
      apply idpath.
    - rewrite !functor_comp.
      rewrite !assoc'.
      apply idpath.
  Qed.

  Proposition comp_preserves_stable_codes_sums_z_iso
    : functor_preserves_stable_codes_sums_z_iso
        (F · G)
        (composition_preserves_bincoproduct HF HG)
        comp_preserves_stable_codes_sums_sum.
  Proof.
    intros Γ a b.
    do 2 refine (assoc _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!(functor_comp G _ _) @ _).
      apply maponpaths.
      apply (functor_preserves_stable_codes_sums_on_z_iso Fc).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (functor_comp G _ _ @ _).
      apply maponpaths_2.
      apply (functor_comp G).
    }
    etrans.
    {
      apply maponpaths_2.
      do 2 refine (assoc' _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply functor_el_map_iso_eq_alt.
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply (functor_preserves_stable_codes_sums_on_z_iso Gc).
    }
    refine (assoc' _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      rewrite cat_el_map_el_eq_comp.
      refine (assoc' _ _ _ @ _).
      rewrite cat_el_map_el_eq_comp.
      apply idpath.
    }
    refine (assoc _ _ _ @ _).
    assert (#G(#F a · functor_on_universe F) · functor_on_universe G
            =
            #G(#F a) · (#G (functor_on_universe F) · functor_on_universe G))
      as q₁.
    {
      rewrite !functor_comp.
      rewrite !assoc'.
      apply idpath.
    }
    assert (#G(#F b · functor_on_universe F) · functor_on_universe G
            =
            #G(#F b) · (#G (functor_on_universe F) · functor_on_universe G))
      as q₂.
    {
      rewrite !functor_comp.
      rewrite !assoc'.
      apply idpath.
    }
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      exact (cat_univ_codes_sums_z_iso_eq sum₃ q₁ q₂).
    }
    rewrite !assoc'.
    rewrite cat_el_map_el_eq_comp.
    do 3 refine (assoc _ _ _ @ _).
    refine (_ @ assoc' _ _ _).
    use maponpaths_compose.
    - apply maponpaths_2.
      use (BinCoproductArrowsEq
             _ _ _
             (preserves_bincoproduct_to_bincoproduct
                _
                (composition_preserves_bincoproduct HF HG)
                (BC₁ (cat_el_map_el _ a) (cat_el_map_el _ b)))).
      + refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(functor_comp G _ _) @ _).
          apply maponpaths.
          apply (BinCoproductIn1Commutes
                   _ _ _
                   (preserves_bincoproduct_to_bincoproduct
                      F HF
                      (BC₁ (cat_el_map_el _ a) (cat_el_map_el _ b)))).
        }
        simpl.
        etrans.
        {
          simpl.
          do 2 apply maponpaths_2.
          apply functor_comp.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply (BinCoproductIn1Commutes
                   _ _ _
                   (preserves_bincoproduct_to_bincoproduct
                      G HG
                      (BC₂ (cat_el_map_el _ (# F a · functor_on_universe F))
                           (cat_el_map_el _ (# F b · functor_on_universe F))))).
        }
        simpl.
        etrans.
        {
          apply maponpaths.
          refine (assoc' _ _ _ @ _).
          rewrite BinCoproductOfArrowsIn1.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          apply BinCoproductIn1Commutes.
        }
        simpl.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        apply maponpaths_2.
        apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C₃)).
      + refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (!(functor_comp G _ _) @ _).
          apply maponpaths.
          apply (BinCoproductIn2Commutes
                   _ _ _
                   (preserves_bincoproduct_to_bincoproduct
                      F HF
                      (BC₁ (cat_el_map_el _ a) (cat_el_map_el _ b)))).
        }
        simpl.
        etrans.
        {
          simpl.
          do 2 apply maponpaths_2.
          apply functor_comp.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply (BinCoproductIn2Commutes
                   _ _ _
                   (preserves_bincoproduct_to_bincoproduct
                      G HG
                      (BC₂ (cat_el_map_el _ (# F a · functor_on_universe F))
                           (cat_el_map_el _ (# F b · functor_on_universe F))))).
        }
        simpl.
        etrans.
        {
          apply maponpaths.
          refine (assoc' _ _ _ @ _).
          rewrite BinCoproductOfArrowsIn2.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          apply BinCoproductIn2Commutes.
        }
        simpl.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        apply maponpaths_2.
        apply (cat_el_map_el_eq_eq (univ_cat_cat_stable_el_map C₃)).
    - apply cat_el_map_el_eq_eq.
  Qed.

  Proposition comp_preserves_stable_codes_sums
    : functor_preserves_stable_codes_sums
        sum₁
        sum₃
        (F · G)
        (composition_preserves_bincoproduct HF HG).
  Proof.
    use make_functor_preserves_stable_codes_sums.
    - exact comp_preserves_stable_codes_sums_sum.
    - exact comp_preserves_stable_codes_sums_z_iso.
  Qed.
End CompPreservation.

(** * 5. Univalence condition *)
Proposition cat_univ_stable_codes_sums_univalence_lemma
            {C : univ_cat_with_finlim_universe}
            (BC : BinCoproducts C)
            {sum₁ sum₂ : cat_univ_stable_codes_sums BC}
            (Fc : functor_preserves_stable_codes_sums
                     sum₁
                     sum₂
                     (identity _)
                     (identity_preserves_bincoproduct C))
  : sum₁ = sum₂.
Proof.
  use cat_univ_stable_codes_sums_eq.
  - intros Γ a b.
    pose (functor_preserves_stable_codes_sums_on_code Fc a b) as p.
    simpl in p.
    refine (!(id_right _) @ _).
    refine (p @ _).
    use cat_univ_codes_sums_sum_eq ; cbn.
    + apply id_right.
    + apply id_right.
  - intros Γ a b.
    pose (functor_preserves_stable_codes_sums_on_z_iso Fc a b) as p.
    simpl in p.
    etrans.
    {
      apply maponpaths_2.
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
    etrans.
    {
      do 3 apply maponpaths_2.
      apply maponpaths.
      exact (cat_univ_codes_sums_z_iso_eq sum₂ (id_right _) (id_right _)).
    }
    rewrite !assoc'.
    rewrite !cat_el_map_el_eq_comp.
    etrans.
    {
      do 3 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
      }
      etrans.
      {
        apply (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
      }
      apply (cat_el_map_el_eq_id (univ_cat_cat_stable_el_map C)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply id_right.
    }
    refine (_ @ id_left _).
    rewrite assoc.
    apply maponpaths_2.
    use BinCoproductArrowsEq.
    + refine (_ @ !(id_right _)).
      rewrite assoc.
      etrans.
      {
        apply maponpaths_2.
        apply BinCoproductIn1Commutes.
      }
      simpl.
      rewrite assoc'.
      rewrite BinCoproductOfArrowsIn1.
      rewrite !assoc.
      rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply (cat_el_map_el_eq_id (univ_cat_cat_stable_el_map C)).
    + refine (_ @ !(id_right _)).
      rewrite assoc.
      etrans.
      {
        apply maponpaths_2.
        apply BinCoproductIn2Commutes.
      }
      simpl.
      rewrite assoc'.
      rewrite BinCoproductOfArrowsIn2.
      rewrite !assoc.
      rewrite (cat_el_map_el_eq_comp (univ_cat_cat_stable_el_map C)).
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply (cat_el_map_el_eq_id (univ_cat_cat_stable_el_map C)).
Qed.
