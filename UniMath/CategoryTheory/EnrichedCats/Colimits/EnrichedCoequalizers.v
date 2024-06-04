(*****************************************************************

 Coequalizers in enriched categories

 In this file, we define coequalizers in enriched categories. In
 addition, we show that they give rise to coequalizers in the
 underlying categories, and we show several properties of them.

 One way to formulate the universal property of coequalizers, is
 by expressing them as a natural bijection between two homsets.
 A morphism from the coequalizer of `f : x --> y` and
 `g : x --> y` to some `z` is the same a morphism `y --> z` that
 makes a certain diagram commute. For enriched categories, we
 formulate this universal property in the monoidal category `V`.

 Contents
 1. Cones of enriched coequalizers
 2. Coequalizers in an enriched category
 3. Being an coequalizer is a proposition
 4. Coequalizers in the underlying category
 5. Builders for coequalizers
 6. Coequalizers are closed under iso
 7. Enriched categories with products

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.

Import MonoidalNotations.
Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedCoequalizer.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          {x y : C}
          (f g : x --> y).

  (**
   1. Cones of enriched coequalizers
   *)
  Definition enriched_coequalizer_cocone
    : UU
    := ∑ (a : C)
         (p : I_{V} --> E ⦃ y , a ⦄),
       f · enriched_to_arr E p = g · enriched_to_arr E p.

  #[reversible] Coercion ob_enriched_coequalizer_cocone
           (a : enriched_coequalizer_cocone)
    : C
    := pr1 a.

  Definition enriched_coequalizer_cocone_in
             (a : enriched_coequalizer_cocone)
    : y --> a
    := enriched_to_arr E (pr12 a).

  Definition enriched_coequalizer_cocone_eq
             (a : enriched_coequalizer_cocone)
    : f · enriched_coequalizer_cocone_in a
      =
      g · enriched_coequalizer_cocone_in a
    := pr22 a.

  Definition make_enriched_coequalizer_cocone
             (a : C)
             (p : I_{V} --> E ⦃ y , a ⦄)
             (q : f · enriched_to_arr E p = g · enriched_to_arr E p)
    : enriched_coequalizer_cocone
    := a ,, p ,, q.

  Proposition precomp_eq_from_coequalizer_cocone
              (a : enriched_coequalizer_cocone)
              (w : C)
    : precomp_arr E w (enriched_coequalizer_cocone_in a) · precomp_arr E w f
      =
      precomp_arr E w (enriched_coequalizer_cocone_in a) · precomp_arr E w g.
  Proof.
    rewrite <- !precomp_arr_comp.
    apply maponpaths.
    apply enriched_coequalizer_cocone_eq.
  Qed.

  (**
   2. Coequalizers in an enriched category
   *)
  Definition is_coequalizer_enriched
             (a : enriched_coequalizer_cocone)
    : UU
    := ∏ (w : C),
       isEqualizer
         (precomp_arr E w f)
         (precomp_arr E w g)
         (precomp_arr E w (enriched_coequalizer_cocone_in a))
         (precomp_eq_from_coequalizer_cocone a w).

  Definition is_coequalizer_enriched_to_Equalizer
             {a : enriched_coequalizer_cocone}
             (Ha : is_coequalizer_enriched a)
             (w : C)
    : Equalizer
        (precomp_arr E w f)
        (precomp_arr E w g).
  Proof.
    use make_Equalizer.
    - exact (E ⦃ a , w ⦄).
    - exact (precomp_arr E w (enriched_coequalizer_cocone_in a)).
    - exact (precomp_eq_from_coequalizer_cocone a w).
    - exact (Ha w).
  Defined.

  Definition coequalizer_enriched
    : UU
    := ∑ (a : enriched_coequalizer_cocone),
       is_coequalizer_enriched a.

  #[reversible=no] Coercion cocone_of_coequalizer_enriched
           (a : coequalizer_enriched)
    : enriched_coequalizer_cocone
    := pr1 a.

  #[reversible=no] Coercion coequalizer_enriched_is_coequalizer
           (a : coequalizer_enriched)
    : is_coequalizer_enriched a
    := pr2 a.

  (**
   3. Being an coequalizer is a proposition
   *)
  Proposition isaprop_is_coequalizer_enriched
              (a : enriched_coequalizer_cocone)
    : isaprop (is_coequalizer_enriched a).
  Proof.
    use impred ; intro.
    apply isaprop_isEqualizer.
  Qed.

  (**
   4. Coequalizers in the underlying category
   *)
  Section InUnderlying.
    Context {a : enriched_coequalizer_cocone}
            (Ha : is_coequalizer_enriched a).

    Definition underlying_Coequalizer_arr
               {w : C}
               (h : y --> w)
               (q : f · h = g · h)
      : a --> w.
    Proof.
      use (enriched_to_arr E).
      use (EqualizerIn (is_coequalizer_enriched_to_Equalizer Ha w)).
      - exact (enriched_from_arr E h).
      - abstract
          (rewrite !enriched_from_arr_precomp ;
           rewrite q ;
           apply idpath).
    Defined.

    Proposition underlying_Coequalizer_arr_in
                {w : C}
                (h : y --> w)
                (q : f · h = g · h)
      : enriched_coequalizer_cocone_in a · underlying_Coequalizer_arr h q = h.
    Proof.
      unfold underlying_Coequalizer_arr, enriched_coequalizer_cocone_in.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      rewrite enriched_from_arr_comp.
      rewrite !enriched_from_to_arr.
      refine (_ @ EqualizerCommutes
                    (is_coequalizer_enriched_to_Equalizer Ha w)
                    I_{V}
                    (enriched_from_arr E h)
                    _).
      rewrite tensor_split'.
      rewrite !assoc.
      rewrite mon_linvunitor_I_mon_rinvunitor_I.
      rewrite <- tensor_rinvunitor.
      cbn.
      unfold precomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      do 3 apply maponpaths.
      refine (!_).
      apply enriched_from_to_arr.
    Qed.

    Proposition underlying_Coequalizer_arr_eq
                {w : C}
                {h₁ h₂ : a --> w}
                (q : enriched_coequalizer_cocone_in a · h₁
                     =
                     enriched_coequalizer_cocone_in a · h₂)
      : h₁ = h₂.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use (EqualizerInsEq (is_coequalizer_enriched_to_Equalizer Ha w)).
      cbn.
      unfold precomp_arr.
      rewrite !assoc.
      rewrite !tensor_rinvunitor.
      rewrite !assoc'.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite <- !tensor_split'.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_to_arr E _ _))) ; cbn.
      rewrite !assoc.
      rewrite mon_rinvunitor_I_mon_linvunitor_I.
      rewrite <- !(enriched_to_arr_comp E).
      exact q.
    Qed.

    Definition underlying_Coequalizer
      : Coequalizer f g.
    Proof.
      use make_Coequalizer.
      - exact a.
      - exact (enriched_coequalizer_cocone_in a).
      - exact (enriched_coequalizer_cocone_eq a).
      - intros w h q.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros φ₁ φ₂ ;
             use subtypePath ; [ intro ; apply homset_property | ] ;
             exact (underlying_Coequalizer_arr_eq (pr2 φ₁ @ !(pr2 φ₂)))).
        + exact (underlying_Coequalizer_arr h q ,, underlying_Coequalizer_arr_in h q).
    Defined.
  End InUnderlying.

  (**
   5. Builders for coequalizers
   *)
  Definition make_is_coequalizer_enriched
             (a : enriched_coequalizer_cocone)
             (eq_arr_eq : ∏ (w : C)
                            (v : V)
                            (h₁ h₂ : v --> E ⦃ a , w ⦄)
                            (q : h₁ · precomp_arr E w (enriched_coequalizer_cocone_in a)
                                 =
                                 h₂ · precomp_arr E w (enriched_coequalizer_cocone_in a)),
                          h₁ = h₂)
             (eq_in : ∏ (w : C)
                        (v : V)
                        (h : v --> E ⦃ y , w ⦄)
                        (q : h · precomp_arr E w f = h · precomp_arr E w g),
                      v --> E ⦃ a , w ⦄)
             (eq_in_eq : ∏ (w : C)
                           (v : V)
                           (h : v --> E ⦃ y , w ⦄)
                           (q : h · precomp_arr E w f = h · precomp_arr E w g),
                         eq_in w v h q
                         · precomp_arr E w (enriched_coequalizer_cocone_in a)
                         =
                         h)
    : is_coequalizer_enriched a.
  Proof.
    intro w.
    use make_isEqualizer.
    intros v h q.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         exact (eq_arr_eq w v _ _ (pr2 φ₁ @ !(pr2 φ₂)))).
    - exact (eq_in w v h q,, eq_in_eq w v h q).
  Defined.

  Definition coequalizer_enriched_to_equalizer
             (EqV : Equalizers V)
             (a : enriched_coequalizer_cocone)
             (w : C)
    : E ⦃ a , w ⦄ --> EqV (E ⦃ y , w ⦄) _ (precomp_arr E w f) (precomp_arr E w g).
  Proof.
    use EqualizerIn.
    - exact (precomp_arr E w (enriched_coequalizer_cocone_in a)).
    - exact (precomp_eq_from_coequalizer_cocone a w).
  Defined.

  Definition make_is_coequalizer_enriched_from_z_iso
             (EqV : Equalizers V)
             (a : enriched_coequalizer_cocone)
             (Ha : ∏ (w : C),
                   is_z_isomorphism (coequalizer_enriched_to_equalizer EqV a w))
    : is_coequalizer_enriched a.
  Proof.
    intro w.
    use (isEqualizer_z_iso
           (pr22 (EqV _ _ (precomp_arr E w f) (precomp_arr E w g)))
           (_ ,, Ha w)).
    abstract
      (unfold coequalizer_enriched_to_equalizer ; cbn ;
       refine (!_) ;
       apply EqualizerCommutes).
  Defined.

  Section CoequalizersFromUnderlying.
    Context (EqV : Equalizers V)
            (a : enriched_coequalizer_cocone)
            (eq_a : isCoequalizer
                      f g
                      (enriched_coequalizer_cocone_in a)
                      (enriched_coequalizer_cocone_eq a))
            (w : C).

    Definition coequalizer_enriched_from_underlying_map
               (h : I_{V} --> EqV _ _ (precomp_arr E w f) (precomp_arr E w g))
      : I_{V} --> E ⦃ a , w ⦄.
    Proof.
      use enriched_from_arr.
      use (CoequalizerOut (make_Coequalizer _ _ _ _ eq_a)).
      - exact (enriched_to_arr E (h · EqualizerArrow _)).
      - abstract
          (use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn ;
           rewrite !enriched_from_arr_comp ;
           rewrite !enriched_from_to_arr ;
           rewrite tensor_split' ;
           rewrite !assoc ;
           rewrite !mon_linvunitor_I_mon_rinvunitor_I ;
           rewrite <- !tensor_rinvunitor ;
           rewrite !assoc' ;
           rewrite !(maponpaths (λ z, _ · (_ · z)) (assoc _ _ _)) ;
           refine (maponpaths
                     (λ z, _ · z)
                     (EqualizerEqAr
                        (EqV _ _ (precomp_arr E w f) (precomp_arr E w g)))
                   @ _) ;
           refine (!_) ;
           rewrite tensor_split' ;
           rewrite !assoc ;
           rewrite <- tensor_rinvunitor ;
           rewrite !assoc' ;
           do 2 apply maponpaths ;
           unfold precomp_arr ;
           rewrite !assoc' ;
           apply idpath).
    Defined.

    Proposition coequalizer_enriched_from_underlying_map_inv₁
                (h : I_{V} --> E ⦃ a , w ⦄)
      : coequalizer_enriched_from_underlying_map
          (h · coequalizer_enriched_to_equalizer EqV a w)
        =
        h.
    Proof.
      unfold coequalizer_enriched_from_underlying_map.
      refine (_ @ enriched_from_to_arr E h).
      apply maponpaths.
      use (isCoequalizerOutsEq eq_a).
      etrans.
      {
        apply (CoequalizerCommutes (make_Coequalizer _ _ _ _ eq_a)).
      }
      unfold enriched_coequalizer_cocone_in.
      rewrite (enriched_to_arr_comp E).
      apply maponpaths.
      rewrite tensor_split'.
      rewrite !assoc.
      rewrite mon_linvunitor_I_mon_rinvunitor_I.
      rewrite <- tensor_rinvunitor.
      rewrite enriched_from_to_arr.
      rewrite !assoc'.
      apply maponpaths.
      unfold coequalizer_enriched_to_equalizer.
      rewrite EqualizerCommutes.
      rewrite !assoc.
      apply idpath.
    Qed.

    Proposition coequalizer_enriched_from_underlying_map_inv₂
                (h : I_{V} --> EqV _ _ (precomp_arr E w f) (precomp_arr E w g))
      : coequalizer_enriched_from_underlying_map h
        · coequalizer_enriched_to_equalizer EqV a w
        =
        h.
    Proof.
      unfold coequalizer_enriched_from_underlying_map.
      use (isEqualizerInsEq (pr22 (EqV _ _ _ _))).
      unfold coequalizer_enriched_to_equalizer.
      rewrite !assoc'.
      rewrite EqualizerCommutes.
      rewrite enriched_from_arr_precomp.
      refine (_ @ enriched_from_to_arr E _).
      apply maponpaths.
      apply (CoequalizerCommutes (make_Coequalizer _ _ _ _ eq_a)).
    Qed.
  End CoequalizersFromUnderlying.

  Definition make_is_coequalizer_enriched_from_underlying
             (EqV : Equalizers V)
             (a : enriched_coequalizer_cocone)
             (eq_a : isCoequalizer
                       f g
                       (enriched_coequalizer_cocone_in a)
                       (enriched_coequalizer_cocone_eq a))
             (HV : conservative_moncat V)
    : is_coequalizer_enriched a.
  Proof.
    use (make_is_coequalizer_enriched_from_z_iso EqV).
    intros w.
    use HV.
    use isweq_iso.
    - exact (coequalizer_enriched_from_underlying_map EqV a eq_a w).
    - exact (coequalizer_enriched_from_underlying_map_inv₁ EqV a eq_a w).
    - exact (coequalizer_enriched_from_underlying_map_inv₂ EqV a eq_a w).
  Defined.

  (**
   6. Coequalizers are closed under iso
   *)
  Section CoequalizerIso.
    Context (a : enriched_coequalizer_cocone)
            (Ha : is_coequalizer_enriched a)
            (b : C)
            (h : z_iso a b).

    Definition enriched_coequalizer_cocone_from_iso
      : enriched_coequalizer_cocone.
    Proof.
      refine (make_enriched_coequalizer_cocone
                b
                (enriched_from_arr E (enriched_coequalizer_cocone_in a · h))
                _).
      abstract
        (rewrite !enriched_to_from_arr ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         exact (enriched_coequalizer_cocone_eq a)).
    Defined.

    Definition is_coequalizer_enriched_from_iso
      : is_coequalizer_enriched enriched_coequalizer_cocone_from_iso.
    Proof.
      intros w.
      use (isEqualizer_z_iso (Ha w)).
      - exact (precomp_arr_z_iso E w h).
      - abstract
          (cbn ;
           rewrite <- precomp_arr_comp ;
           apply maponpaths ;
           unfold enriched_coequalizer_cocone_from_iso ; cbn ;
           unfold  enriched_coequalizer_cocone_in ; cbn ;
           rewrite enriched_to_from_arr ;
           apply idpath).
    Defined.
  End CoequalizerIso.

  (**
   7. Coequalizers are isomorphic
   *)
  Definition map_between_coequalizer_enriched
             {a b : enriched_coequalizer_cocone}
             (Ha : is_coequalizer_enriched a)
             (Hb : is_coequalizer_enriched b)
    : a --> b
    := underlying_Coequalizer_arr
         Ha
         (enriched_coequalizer_cocone_in b)
         (enriched_coequalizer_cocone_eq b).

  Lemma iso_between_coequalizer_enriched_inv
        {a b : enriched_coequalizer_cocone}
        (Ha : is_coequalizer_enriched a)
        (Hb : is_coequalizer_enriched b)
    : map_between_coequalizer_enriched Ha Hb · map_between_coequalizer_enriched Hb Ha
      =
      identity _.
  Proof.
    unfold map_between_coequalizer_enriched.
    use (underlying_Coequalizer_arr_eq Ha).
    rewrite !assoc.
    rewrite !underlying_Coequalizer_arr_in.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition iso_between_coequalizer_enriched
             {a b : enriched_coequalizer_cocone}
             (Ha : is_coequalizer_enriched a)
             (Hb : is_coequalizer_enriched b)
    : z_iso a b.
  Proof.
    use make_z_iso.
    - exact (map_between_coequalizer_enriched Ha Hb).
    - exact (map_between_coequalizer_enriched Hb Ha).
    - split.
      + apply iso_between_coequalizer_enriched_inv.
      + apply iso_between_coequalizer_enriched_inv.
  Defined.
End EnrichedCoequalizer.

(**
 7. Enriched categories with products
 *)
Definition enrichment_coequalizers
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : UU
  := ∏ (x y : C) (f g : x --> y),
     ∑ (a : enriched_coequalizer_cocone E f g),
     is_coequalizer_enriched E f g a.

Proposition isaprop_enrichment_coequalizers
            {V : monoidal_cat}
            {C : category}
            (HC : is_univalent C)
            (E : enrichment C V)
  : isaprop (enrichment_coequalizers E).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use funextsec ; intro x.
  use funextsec ; intro y.
  use funextsec ; intro f.
  use funextsec ; intro g.
  use subtypePath.
  {
    intro.
    apply isaprop_is_coequalizer_enriched.
  }
  use total2_paths_f.
  - use (isotoid _ HC).
    use iso_between_coequalizer_enriched.
    + exact (pr2 (φ₁ x y f g)).
    + exact (pr2 (φ₂ x y f g)).
  - use subtypePath.
    {
      intro.
      apply homset_property.
    }
    rewrite pr1_transportf.
    rewrite transportf_enriched_arr_r.
    rewrite idtoiso_isotoid.
    cbn.
    refine (_ @ enriched_from_to_arr E _).
    apply maponpaths.
    unfold map_between_coequalizer_enriched ; cbn.
    apply underlying_Coequalizer_arr_in.
Qed.

Definition cat_with_enrichment_coequalizers
           (V : monoidal_cat)
  : UU
  := ∑ (C : cat_with_enrichment V), enrichment_coequalizers C.

#[reversible=no] Coercion cat_with_enrichment_coequalizers_to_cat_with_enrichment
         {V : monoidal_cat}
         (C : cat_with_enrichment_coequalizers V)
  : cat_with_enrichment V
  := pr1 C.

Definition coequalizers_of_cat_with_enrichment_coequalizers
           {V : monoidal_cat}
           (C : cat_with_enrichment_coequalizers V)
  : enrichment_coequalizers C
  := pr2 C.
