(*****************************************************************

 Enriched equalizers

 We define the notion of equalizers in the enriched setting. To
 do so, we formulate the universal property for equalizers in
 arbitrary monoidal categories rather than just set. Whereas cones
 for cones we can use the same definition, we need to reformulate
 the universal property to take the enrichment into account. The
 idea here is the same as for terminal objects and for binary
 products.

 Content
 1. Cones of enriched equalizers
 2. Equalizers in an enriched category
 3. Being an equalizer is a proposition
 4. Equalizers in the underlying category
 5. Builders for equalizers
 6. Equalizers are closed under iso
 7. Equalizers are isomorphic
 8. Enriched categories with equalizers

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

Import MonoidalNotations.
Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedEqualizer.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          {x y : C}
          (f g : x --> y).

  (**
   1. Cones of enriched equalizers
   *)
  Definition enriched_equalizer_cone
    : UU
    := ∑ (a : C)
         (p : I_{V} --> E ⦃ a , x ⦄),
       enriched_to_arr E p · f = enriched_to_arr E p · g.

  #[reversible] Coercion ob_enriched_equalizer_cone
           (a : enriched_equalizer_cone)
    : C
    := pr1 a.

  Definition enriched_equalizer_cone_pr
             (a : enriched_equalizer_cone)
    : a --> x
    := enriched_to_arr E (pr12 a).

  Definition enriched_equalizer_cone_eq
             (a : enriched_equalizer_cone)
    : enriched_equalizer_cone_pr a · f
      =
      enriched_equalizer_cone_pr a · g
    := pr22 a.

  Definition make_enriched_equalizer_cone
             (a : C)
             (p : I_{V} --> E ⦃ a , x ⦄)
             (q : enriched_to_arr E p · f = enriched_to_arr E p · g)
    : enriched_equalizer_cone
    := a ,, p ,, q.

  Proposition postcomp_eq_from_equalizer_cone
              (a : enriched_equalizer_cone)
              (w : C)
    : postcomp_arr E w (enriched_equalizer_cone_pr a) · postcomp_arr E w f
      =
      postcomp_arr E w (enriched_equalizer_cone_pr a) · postcomp_arr E w g.
  Proof.
    rewrite <- !postcomp_arr_comp.
    apply maponpaths.
    apply enriched_equalizer_cone_eq.
  Qed.

  (**
   2. Equalizers in an enriched category
   *)
  Definition is_equalizer_enriched
             (a : enriched_equalizer_cone)
    : UU
    := ∏ (w : C),
       isEqualizer
         (postcomp_arr E w f)
         (postcomp_arr E w g)
         (postcomp_arr E w (enriched_equalizer_cone_pr a))
         (postcomp_eq_from_equalizer_cone a w).

  Definition is_equalizer_enriched_to_Equalizer
             {a : enriched_equalizer_cone}
             (Ha : is_equalizer_enriched a)
             (w : C)
    : Equalizer
        (postcomp_arr E w f)
        (postcomp_arr E w g).
  Proof.
    use make_Equalizer.
    - exact (E ⦃ w , a ⦄).
    - exact (postcomp_arr E w (enriched_equalizer_cone_pr a)).
    - exact (postcomp_eq_from_equalizer_cone a w).
    - exact (Ha w).
  Defined.

  Definition equalizer_enriched
    : UU
    := ∑ (a : enriched_equalizer_cone),
       is_equalizer_enriched a.

  #[reversible=no] Coercion cone_of_equalizer_enriched
           (a : equalizer_enriched)
    : enriched_equalizer_cone
    := pr1 a.

  #[reversible=no] Coercion equalizer_enriched_is_equalizer
           (a : equalizer_enriched)
    : is_equalizer_enriched a
    := pr2 a.

  (**
   3. Being an equalizer is a proposition
   *)
  Proposition isaprop_is_equalizer_enriched
              (a : enriched_equalizer_cone)
    : isaprop (is_equalizer_enriched a).
  Proof.
    use impred ; intro.
    apply isaprop_isEqualizer.
  Qed.

  (**
   4. Equalizers in the underlying category
   *)
  Section InUnderlying.
    Context {a : enriched_equalizer_cone}
            (Ha : is_equalizer_enriched a).

    Definition underlying_Equalizer_arr
               {w : C}
               (h : w --> x)
               (q : h · f = h · g)
      : w --> a.
    Proof.
      use (enriched_to_arr E).
      use (EqualizerIn (is_equalizer_enriched_to_Equalizer Ha w)).
      - exact (enriched_from_arr E h).
      - abstract
          (rewrite !enriched_from_arr_postcomp ;
           rewrite q ;
           apply idpath).
    Defined.

    Proposition underlying_Equalizer_arr_pr
                {w : C}
                (h : w --> x)
                (q : h · f = h · g)
      : underlying_Equalizer_arr h q · enriched_equalizer_cone_pr a = h.
    Proof.
      unfold underlying_Equalizer_arr, enriched_equalizer_cone_pr.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      rewrite enriched_from_arr_comp.
      rewrite !enriched_from_to_arr.
      rewrite tensor_split.
      rewrite !assoc.
      rewrite <- tensor_linvunitor.
      rewrite !assoc'.
      refine (maponpaths (λ z, _ · z) _
              @ EqualizerCommutes
                  (is_equalizer_enriched_to_Equalizer Ha w)
                  I_{V}
                  (enriched_from_arr E h)
                  _).
      cbn ; unfold postcomp_arr.
      rewrite !assoc'.
      apply maponpaths.
      do 2 apply maponpaths_2.
      refine (!_).
      apply enriched_from_to_arr.
    Qed.

    Proposition underlying_Equalizer_arr_eq
                {w : C}
                {h₁ h₂ : w --> a}
                (q : h₁ · enriched_equalizer_cone_pr a = h₂ · enriched_equalizer_cone_pr a)
      : h₁ = h₂.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use (EqualizerInsEq (is_equalizer_enriched_to_Equalizer Ha w)).
      cbn.
      unfold postcomp_arr.
      rewrite !assoc.
      rewrite !tensor_linvunitor.
      rewrite !assoc'.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite <- !tensor_split.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_to_arr E _ _))) ; cbn.
      rewrite !assoc.
      rewrite <- !(enriched_to_arr_comp E).
      exact q.
    Qed.

    Definition underlying_Equalizer
      : Equalizer f g.
    Proof.
      use make_Equalizer.
      - exact a.
      - exact (enriched_equalizer_cone_pr a).
      - exact (enriched_equalizer_cone_eq a).
      - intros w h q.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros φ₁ φ₂ ;
             use subtypePath ; [ intro ; apply homset_property | ] ;
             exact (underlying_Equalizer_arr_eq (pr2 φ₁ @ !(pr2 φ₂)))).
        + exact (underlying_Equalizer_arr h q ,, underlying_Equalizer_arr_pr h q).
    Defined.
  End InUnderlying.

  (**
   5. Builders for equalizers
   *)
  Definition make_is_equalizer_enriched
             (a : enriched_equalizer_cone)
             (eq_arr_eq : ∏ (w : C)
                            (v : V)
                            (h₁ h₂ : v --> E ⦃ w, a ⦄)
                            (q : h₁ · postcomp_arr E w (enriched_equalizer_cone_pr a)
                                 =
                                 h₂ · postcomp_arr E w (enriched_equalizer_cone_pr a)),
                          h₁ = h₂)
             (eq_in : ∏ (w : C)
                        (v : V)
                        (h : v --> E ⦃ w, x ⦄)
                        (q : h · postcomp_arr E w f = h · postcomp_arr E w g),
                      v --> E ⦃ w, a ⦄)
             (eq_in_eq : ∏ (w : C)
                           (v : V)
                           (h : v --> E ⦃ w, x ⦄)
                           (q : h · postcomp_arr E w f = h · postcomp_arr E w g),
                         eq_in w v h q
                         · postcomp_arr E w (enriched_equalizer_cone_pr a)
                         =
                         h)
    : is_equalizer_enriched a.
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

  Definition equalizer_enriched_to_equalizer
             (EqV : Equalizers V)
             (a : enriched_equalizer_cone)
             (w : C)
    : E ⦃ w , a ⦄ --> EqV (E ⦃ w, x ⦄) _ (postcomp_arr E w f) (postcomp_arr E w g).
  Proof.
    use EqualizerIn.
    - exact (postcomp_arr E w (enriched_equalizer_cone_pr a)).
    - exact (postcomp_eq_from_equalizer_cone a w).
  Defined.

  Definition make_is_equalizer_enriched_from_z_iso
             (EqV : Equalizers V)
             (a : enriched_equalizer_cone)
             (Ha : ∏ (w : C),
                   is_z_isomorphism (equalizer_enriched_to_equalizer EqV a w))
    : is_equalizer_enriched a.
  Proof.
    intro w.
    use (isEqualizer_z_iso
           (pr22 (EqV (E ⦃ w, x ⦄) (E ⦃ w, y ⦄) (postcomp_arr E w f) (postcomp_arr E w g)))
           (_ ,, Ha w)).
    abstract
      (unfold equalizer_enriched_to_equalizer ; cbn ;
       refine (!_) ;
       apply EqualizerCommutes).
  Defined.

  Section EqualizersFromUnderlying.
    Context (EqV : Equalizers V)
            (a : enriched_equalizer_cone)
            (eq_a : isEqualizer
                      f g
                      (enriched_equalizer_cone_pr a)
                      (enriched_equalizer_cone_eq a))
            (w : C).

    Definition equalizer_enriched_from_underlying_map
               (h : I_{ V} --> EqV _ _ (postcomp_arr E w f) (postcomp_arr E w g))
      : I_{ V} --> E ⦃ w, a ⦄.
    Proof.
      use enriched_from_arr.
      use (EqualizerIn (make_Equalizer _ _ _ _ eq_a)).
      - exact (enriched_to_arr E (h · EqualizerArrow _)).
      - abstract
          (use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn ;
           rewrite !enriched_from_arr_comp ;
           rewrite !enriched_from_to_arr ;
           rewrite tensor_split ;
           rewrite !assoc ;
           rewrite <- tensor_linvunitor ;
           rewrite !assoc' ;
           rewrite !(maponpaths (λ z, _ · (_ · z)) (assoc _ _ _)) ;
           refine (maponpaths
                     (λ z, _ · z)
                     (EqualizerEqAr
                        (EqV _ _ (postcomp_arr E w f) (postcomp_arr E w g)))
                   @ _) ;
           refine (!_) ;
           rewrite tensor_split ;
           rewrite !assoc ;
           rewrite <- tensor_linvunitor ;
           rewrite !assoc' ;
           do 2 apply maponpaths ;
           unfold postcomp_arr ;
           rewrite !assoc' ;
           apply idpath).
    Defined.

    Proposition equalizer_enriched_from_underlying_map_inv₁
                (h : I_{ V} --> E ⦃ w, a ⦄)
      : equalizer_enriched_from_underlying_map (h · equalizer_enriched_to_equalizer EqV a w)
        =
        h.
    Proof.
      unfold equalizer_enriched_from_underlying_map.
      refine (_ @ enriched_from_to_arr E h).
      apply maponpaths.
      use (isEqualizerInsEq eq_a).
      etrans.
      {
        apply (EqualizerCommutes (make_Equalizer _ _ _ _ eq_a)).
      }
      unfold enriched_equalizer_cone_pr.
      rewrite (enriched_to_arr_comp E).
      apply maponpaths.
      rewrite tensor_split.
      rewrite !assoc.
      rewrite <- tensor_linvunitor.
      rewrite enriched_from_to_arr.
      rewrite !assoc'.
      apply maponpaths.
      unfold equalizer_enriched_to_equalizer.
      rewrite EqualizerCommutes.
      rewrite !assoc.
      apply idpath.
    Qed.

    Proposition equalizer_enriched_from_underlying_map_inv₂
                (h : I_{ V} --> EqV _ _ (postcomp_arr E w f) (postcomp_arr E w g))
      : equalizer_enriched_from_underlying_map h
        · equalizer_enriched_to_equalizer EqV a w
        =
        h.
    Proof.
      unfold equalizer_enriched_from_underlying_map.
      use (isEqualizerInsEq (pr22 (EqV _ _ _ _))).
      unfold equalizer_enriched_to_equalizer.
      rewrite !assoc'.
      rewrite EqualizerCommutes.
      rewrite enriched_from_arr_postcomp.
      refine (_ @ enriched_from_to_arr E _).
      apply maponpaths.
      apply (EqualizerCommutes (make_Equalizer _ _ _ _ eq_a)).
    Qed.
  End EqualizersFromUnderlying.

  Definition make_is_equalizer_enriched_from_underlying
             (EqV : Equalizers V)
             (a : enriched_equalizer_cone)
             (eq_a : isEqualizer
                       f g
                       (enriched_equalizer_cone_pr a)
                       (enriched_equalizer_cone_eq a))
             (HV : conservative_moncat V)
    : is_equalizer_enriched a.
  Proof.
    use (make_is_equalizer_enriched_from_z_iso EqV).
    intros w.
    use HV.
    use isweq_iso.
    - exact (equalizer_enriched_from_underlying_map EqV a eq_a w).
    - exact (equalizer_enriched_from_underlying_map_inv₁ EqV a eq_a w).
    - exact (equalizer_enriched_from_underlying_map_inv₂ EqV a eq_a w).
  Defined.

  (**
   6. Equalizers are closed under iso
   *)
  Section EqualizerIso.
    Context (a : enriched_equalizer_cone)
            (Ha : is_equalizer_enriched a)
            (b : C)
            (h : z_iso b a).

    Definition enriched_equalizer_cone_from_iso
      : enriched_equalizer_cone.
    Proof.
      refine (make_enriched_equalizer_cone
                b
                (enriched_from_arr E (h · enriched_equalizer_cone_pr a))
                _).
      abstract
        (rewrite !enriched_to_from_arr ;
         rewrite !assoc' ;
         apply maponpaths ;
         exact (enriched_equalizer_cone_eq a)).
    Defined.

    Definition is_equalizer_enriched_from_iso
      : is_equalizer_enriched enriched_equalizer_cone_from_iso.
    Proof.
      intros w.
      use (isEqualizer_z_iso (Ha w)).
      - exact (postcomp_arr_z_iso E w h).
      - abstract
          (cbn ;
           rewrite <- postcomp_arr_comp ;
           apply maponpaths ;
           unfold enriched_equalizer_cone_from_iso ; cbn ;
           unfold  enriched_equalizer_cone_pr ; cbn ;
           rewrite enriched_to_from_arr ;
           apply idpath).
    Defined.
  End EqualizerIso.

  (**
   7. Equalizers are isomorphic
   *)
  Definition map_between_equalizer_enriched
             {a b : enriched_equalizer_cone}
             (Ha : is_equalizer_enriched a)
             (Hb : is_equalizer_enriched b)
    : a --> b
    := underlying_Equalizer_arr
         Hb
         (enriched_equalizer_cone_pr a)
         (enriched_equalizer_cone_eq a).

  Lemma iso_between_equalizer_enriched_inv
        {a b : enriched_equalizer_cone}
        (Ha : is_equalizer_enriched a)
        (Hb : is_equalizer_enriched b)
    : map_between_equalizer_enriched Ha Hb · map_between_equalizer_enriched Hb Ha
      =
      identity _.
  Proof.
    unfold map_between_equalizer_enriched.
    use (underlying_Equalizer_arr_eq Ha).
    rewrite !assoc'.
    rewrite !underlying_Equalizer_arr_pr.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition iso_between_equalizer_enriched
             {a b : enriched_equalizer_cone}
             (Ha : is_equalizer_enriched a)
             (Hb : is_equalizer_enriched b)
    : z_iso a b.
  Proof.
    use make_z_iso.
    - exact (map_between_equalizer_enriched Ha Hb).
    - exact (map_between_equalizer_enriched Hb Ha).
    - split.
      + apply iso_between_equalizer_enriched_inv.
      + apply iso_between_equalizer_enriched_inv.
  Defined.
End EnrichedEqualizer.

(**
 8. Enriched categories with equalizers
 *)
Definition enrichment_equalizers
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : UU
  := ∏ (x y : C) (f g : x --> y),
     ∑ (a : enriched_equalizer_cone E f g),
     is_equalizer_enriched E f g a.

Proposition isaprop_enrichment_equalizers
            {V : monoidal_cat}
            {C : category}
            (HC : is_univalent C)
            (E : enrichment C V)
  : isaprop (enrichment_equalizers E).
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
    apply isaprop_is_equalizer_enriched.
  }
  use total2_paths_f.
  - use (isotoid _ HC).
    use iso_between_equalizer_enriched.
    + exact (pr2 (φ₁ x y f g)).
    + exact (pr2 (φ₂ x y f g)).
  - use subtypePath.
    {
      intro.
      apply homset_property.
    }
    rewrite pr1_transportf.
    rewrite transportf_enriched_arr_l.
    rewrite idtoiso_inv.
    rewrite idtoiso_isotoid.
    cbn.
    refine (_ @ enriched_from_to_arr E _).
    apply maponpaths.
    unfold map_between_equalizer_enriched ; cbn.
    apply underlying_Equalizer_arr_pr.
Qed.

Definition cat_with_enrichment_equalizers
           (V : monoidal_cat)
  : UU
  := ∑ (C : cat_with_enrichment V), enrichment_equalizers C.

#[reversible=no] Coercion cat_with_enrichment_equalizers_to_cat_with_enrichment
         {V : monoidal_cat}
         (C : cat_with_enrichment_equalizers V)
  : cat_with_enrichment V
  := pr1 C.

Definition equalizers_of_cat_with_enrichment_equalizers
           {V : monoidal_cat}
           (C : cat_with_enrichment_equalizers V)
  : enrichment_equalizers C
  := pr2 C.
