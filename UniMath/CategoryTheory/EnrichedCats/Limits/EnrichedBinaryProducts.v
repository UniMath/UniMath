(*****************************************************************

 Enriched binary products

 In this file, we define binary products in the enriched setting.
 For ordinary categories, we can formulate the universal property
 of products via hom-sets. More specifically, the product `a × b`
 of `a` and `b` satisfies the following universal property: for
 every `z`, we have a natural isomorphism from `z --> a × b` to
 `(z --> a) × (z --> b)`. From this natural isomorphism, we can
 deduce that a cone for the product consists of an object `z`
 together with projections `z --> a` and `z --> b`, and that
 to give a map `z --> a × b`, it suffices to give `z --> a` and
 `z --> b`.

 To define enriched products, we formulate this universal property
 in monoidal categories. More specifically, we say that the hom
 object `z --> a × b` is the product of `z --> a` and `z --> b`.

 Content
 1. Cones of enriched products
 2. Binary products in an enriched category
 3. Being a binary product is a proposition
 4. Binary products in the underlying category
 5. Builders for binary products
 6. Products are closed under iso
 7. Products are isomorphic
 8. Enriched categories with products

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.Limits.BinProducts.

Import MonoidalNotations.
Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedProducts.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          (x y : C).

  (**
   1. Cones of enriched binary products
   *)
  Definition enriched_binary_prod_cone
    : UU
    := ∑ (a : C),
       I_{V} --> E ⦃ a , x ⦄
       ×
       I_{V} --> E ⦃ a , y ⦄.

  #[reversible=no] Coercion ob_enriched_binary_prod_cone
           (a : enriched_binary_prod_cone)
    : C
    := pr1 a.

  Definition enriched_prod_cone_pr1
             (a : enriched_binary_prod_cone)
    : a --> x
    := enriched_to_arr E (pr12 a).

  Definition enriched_prod_cone_pr2
             (a : enriched_binary_prod_cone)
    : a --> y
    := enriched_to_arr E (pr22 a).

  Definition make_enriched_binary_prod_cone
             (a : C)
             (p₁ : I_{V} --> E ⦃ a , x ⦄)
             (p₂ : I_{V} --> E ⦃ a , y ⦄)
    : enriched_binary_prod_cone
    := a ,, p₁ ,, p₂.

  (**
   2. Binary products in an enriched category
   *)
  Definition is_binary_prod_enriched
             (a : enriched_binary_prod_cone)
    : UU
    := ∏ (w : C),
       isBinProduct
         V
         (E ⦃ w , x ⦄)
         (E ⦃ w , y ⦄)
         (E ⦃ w , a ⦄)
         (postcomp_arr E w (enriched_prod_cone_pr1 a))
         (postcomp_arr E w (enriched_prod_cone_pr2 a)).

  Definition is_binary_prod_enriched_to_BinProduct
             {a : enriched_binary_prod_cone}
             (Ha : is_binary_prod_enriched a)
             (w : C)
    : BinProduct
        V
        (E ⦃ w , x ⦄)
        (E ⦃ w , y ⦄).
  Proof.
    use make_BinProduct.
    - exact (E ⦃ w , a ⦄).
    - exact (postcomp_arr E w (enriched_prod_cone_pr1 a)).
    - exact (postcomp_arr E w (enriched_prod_cone_pr2 a)).
    - exact (Ha w).
  Defined.

  Definition binary_prod_enriched
    : UU
    := ∑ (a : enriched_binary_prod_cone),
       is_binary_prod_enriched a.

  #[reversible=no] Coercion cone_of_binary_prod_enriched
           (a : binary_prod_enriched)
    : enriched_binary_prod_cone
    := pr1 a.

  #[reversible=no] Coercion binary_prod_enriched_is_prod
           (a : binary_prod_enriched)
    : is_binary_prod_enriched a
    := pr2 a.

  (**
   3. Being a binary product is a proposition
   *)
  Proposition isaprop_is_binary_prod_enriched
              (a : enriched_binary_prod_cone)
    : isaprop (is_binary_prod_enriched a).
  Proof.
    use impred ; intro.
    apply isaprop_isBinProduct.
  Qed.

  (**
   4. Binary products in the underlying category
   *)
  Section InUnderlying.
    Context {a : enriched_binary_prod_cone}
            (Ha : is_binary_prod_enriched a).

    Definition is_binary_prod_enriched_arrow
               {w : C}
               (f : w --> x)
               (g : w --> y)
      : w --> a.
    Proof.
      refine (enriched_to_arr E _).
      use (BinProductArrow _ (is_binary_prod_enriched_to_BinProduct Ha w)).
      - exact (enriched_from_arr E f).
      - exact (enriched_from_arr E g).
    Defined.

    Proposition is_binary_prod_enriched_arrow_pr1
                {w : C}
                (f : w --> x)
                (g : w --> y)
      : is_binary_prod_enriched_arrow f g · enriched_prod_cone_pr1 a
        =
        f.
    Proof.
      unfold is_binary_prod_enriched_arrow, enriched_prod_cone_pr1.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      refine (_ @ BinProductPr1Commutes
                    _ _ _
                    (is_binary_prod_enriched_to_BinProduct Ha w)
                    _
                    (enriched_from_arr E f)
                    (enriched_from_arr E g)).
      cbn.
      unfold postcomp_arr, enriched_prod_cone_pr1.
      rewrite enriched_from_arr_comp.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_split.
      rewrite !enriched_from_to_arr.
      apply idpath.
    Qed.

    Proposition is_binary_prod_enriched_arrow_pr2
                {w : C}
                (f : w --> x)
                (g : w --> y)
      : is_binary_prod_enriched_arrow f g · enriched_prod_cone_pr2 a
        =
        g.
    Proof.
      unfold is_binary_prod_enriched_arrow, enriched_prod_cone_pr2.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      refine (_ @ BinProductPr2Commutes
                    _ _ _
                    (is_binary_prod_enriched_to_BinProduct Ha w)
                    _
                    (enriched_from_arr E f)
                    (enriched_from_arr E g)).
      cbn.
      unfold postcomp_arr, enriched_prod_cone_pr2.
      rewrite enriched_from_arr_comp.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_split.
      rewrite !enriched_from_to_arr.
      apply idpath.
    Qed.

    Proposition is_binary_prod_enriched_arrow_eq
                {w : C}
                {f g : w --> a}
                (q₁ : f · enriched_prod_cone_pr1 a = g · enriched_prod_cone_pr1 a)
                (q₂ : f · enriched_prod_cone_pr2 a = g · enriched_prod_cone_pr2 a)
      : f = g.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use (BinProductArrowsEq
               _ _ _
               (is_binary_prod_enriched_to_BinProduct Ha w)).
      - cbn.
        unfold postcomp_arr.
        rewrite !assoc.
        rewrite !tensor_linvunitor.
        rewrite !assoc'.
        rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
        rewrite <- !tensor_split.
        use (invmaponpathsweq (make_weq _ (isweq_enriched_to_arr E _ _))) ; cbn.
        rewrite !assoc.
        rewrite <- !(enriched_to_arr_comp E).
        exact q₁.
      - cbn.
        unfold postcomp_arr.
        rewrite !assoc.
        rewrite !tensor_linvunitor.
        rewrite !assoc'.
        rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
        rewrite <- !tensor_split.
        use (invmaponpathsweq (make_weq _ (isweq_enriched_to_arr E _ _))) ; cbn.
        rewrite !assoc.
        rewrite <- !(enriched_to_arr_comp E).
        exact q₂.
    Qed.

    Definition underlying_BinProduct
      : BinProduct C x y.
    Proof.
      use make_BinProduct.
      - exact a.
      - exact (enriched_prod_cone_pr1 a).
      - exact (enriched_prod_cone_pr2 a).
      - intros w f g.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros φ₁ φ₂ ;
             use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
             exact (is_binary_prod_enriched_arrow_eq
                      (pr12 φ₁ @ !(pr12 φ₂))
                      (pr22 φ₁ @ !(pr22 φ₂)))).
        + exact (is_binary_prod_enriched_arrow f g
                 ,,
                 is_binary_prod_enriched_arrow_pr1 f g
                 ,,
                 is_binary_prod_enriched_arrow_pr2 f g).
    Defined.
  End InUnderlying.

  (**
   5. Builders for binary products
   *)
  Definition make_is_binary_prod_enriched
             (a : enriched_binary_prod_cone)
             (pair : ∏ (w : C) (v : V)
                       (f : v --> E ⦃ w, x ⦄)
                       (g : v --> E ⦃ w, y ⦄),
                     v --> E ⦃ w , a ⦄)
             (pair_pr1 : ∏ (w : C) (v : V)
                           (f : v --> E ⦃ w, x ⦄)
                           (g : v --> E ⦃ w, y ⦄),
                         pair w v f g · postcomp_arr E w (enriched_prod_cone_pr1 a)
                         =
                         f)
             (pair_pr2 : ∏ (w : C) (v : V)
                           (f : v --> E ⦃ w, x ⦄)
                           (g : v --> E ⦃ w, y ⦄),
                         pair w v f g · postcomp_arr E w (enriched_prod_cone_pr2 a)
                         =
                         g)
             (pair_eq : ∏ (w : C) (v : V)
                          (φ₁ φ₂ : v --> E ⦃ w , a ⦄)
                          (q₁ : φ₁ · postcomp_arr E w (enriched_prod_cone_pr1 a)
                                =
                                φ₂ · postcomp_arr E w (enriched_prod_cone_pr1 a))
                          (q₂ : φ₁ · postcomp_arr E w (enriched_prod_cone_pr2 a)
                                =
                                φ₂ · postcomp_arr E w (enriched_prod_cone_pr2 a)),
                        φ₁ = φ₂)
    : is_binary_prod_enriched a.
  Proof.
    intro w.
    use make_isBinProduct.
    intros v f g.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         exact (pair_eq
                  w v
                  (pr1 φ₁) (pr1 φ₂)
                  (pr12 φ₁ @ !(pr12 φ₂)) (pr22 φ₁ @ !(pr22 φ₂)))).
    - simple refine (_ ,, _ ,, _).
      + exact (pair w v f g).
      + exact (pair_pr1 w v f g).
      + exact (pair_pr2 w v f g).
  Defined.

  Definition binary_prod_enriched_to_prod
             (BPV : BinProducts V)
             (a : enriched_binary_prod_cone)
             (w : C)
    : E ⦃ w, a ⦄ --> BPV (E ⦃ w, x ⦄) (E ⦃ w, y ⦄).
  Proof.
    use BinProductArrow.
    - exact (postcomp_arr E w (enriched_prod_cone_pr1 a)).
    - exact (postcomp_arr E w (enriched_prod_cone_pr2 a)).
  Defined.

  Definition make_is_binary_prod_enriched_from_z_iso
             (BPV : BinProducts V)
             (a : enriched_binary_prod_cone)
             (Ha : ∏ (w : C),
                   is_z_isomorphism (binary_prod_enriched_to_prod BPV a w))
    : is_binary_prod_enriched a.
  Proof.
    intro w.
    use (isBinProduct_z_iso (pr2 (BPV (E ⦃ w, x ⦄) (E ⦃ w, y ⦄))) (_ ,, Ha w) _).
    - abstract
        (unfold binary_prod_enriched_to_prod ; cbn ;
         refine (!_) ;
         apply BinProductPr1Commutes).
    - abstract
        (unfold binary_prod_enriched_to_prod ; cbn ;
         refine (!_) ;
         apply BinProductPr2Commutes).
  Defined.

  Section BinaryProductFromUnderlying.
    Context (BPV : BinProducts V)
            (a : enriched_binary_prod_cone)
            (prod : isBinProduct
                      C
                      x y
                      a
                      (enriched_prod_cone_pr1 a)
                      (enriched_prod_cone_pr2 a))
            (w : C).

    Definition prod_from_underlying_arr_map
               (f : I_{V} --> BPV (E ⦃ w , x ⦄) (E ⦃ w, y ⦄))
      : I_{V} --> E ⦃ w, a ⦄.
    Proof.
      apply enriched_from_arr.
      use (BinProductArrow _ (make_BinProduct _ _ _ _ _ _ prod)).
      - exact (enriched_to_arr E (f · BinProductPr1 _ _)).
      - exact (enriched_to_arr E (f · BinProductPr2 _ _)).
    Defined.

    Proposition prod_from_underlying_arr_map_eq₁
                (f : I_{V} --> E ⦃ w, a ⦄)
      : prod_from_underlying_arr_map (f · binary_prod_enriched_to_prod BPV a w)
        =
        f.
    Proof.
      unfold prod_from_underlying_arr_map.
      refine (_ @ enriched_from_to_arr E f).
      apply maponpaths.
      use (BinProductArrowsEq
             _ _ _
             (make_BinProduct C x y a _ _ prod)).
      - unfold binary_prod_enriched_to_prod.
        rewrite !assoc'.
        rewrite !BinProductPr1Commutes ; cbn.
        rewrite (enriched_to_arr_comp E).
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc.
        rewrite <- tensor_linvunitor.
        rewrite !assoc'.
        rewrite enriched_from_to_arr.
        apply maponpaths.
        rewrite !assoc.
        apply idpath.
      - unfold binary_prod_enriched_to_prod.
        rewrite !assoc'.
        rewrite !BinProductPr2Commutes ; cbn.
        rewrite (enriched_to_arr_comp E).
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc.
        rewrite <- tensor_linvunitor.
        rewrite !assoc'.
        rewrite enriched_from_to_arr.
        apply maponpaths.
        rewrite !assoc.
        apply idpath.
    Qed.

    Proposition prod_from_underlying_arr_map_eq₂
                (f : I_{V} --> BPV (E ⦃ w, x ⦄) (E ⦃ w, y ⦄))
      : prod_from_underlying_arr_map f · binary_prod_enriched_to_prod BPV a w = f.
    Proof.
      unfold prod_from_underlying_arr_map.
      use (BinProductArrowsEq
             _ _ _
             (BPV (E ⦃ w, x ⦄) (E ⦃ w, y ⦄))).
      - unfold binary_prod_enriched_to_prod.
        rewrite !assoc'.
        rewrite !BinProductPr1Commutes.
        rewrite enriched_from_arr_postcomp.
        refine (_ @ enriched_from_to_arr E _).
        apply maponpaths.
        apply (BinProductPr1Commutes _ _ _ (make_BinProduct C x y a _ _ prod)).
      - unfold binary_prod_enriched_to_prod.
        rewrite !assoc'.
        rewrite !BinProductPr2Commutes.
        rewrite enriched_from_arr_postcomp.
        refine (_ @ enriched_from_to_arr E _).
        apply maponpaths.
        apply (BinProductPr2Commutes _ _ _ (make_BinProduct C x y a _ _ prod)).
    Qed.
  End BinaryProductFromUnderlying.

  Definition make_is_binary_prod_enriched_from_underlying
             (BPV : BinProducts V)
             (a : enriched_binary_prod_cone)
             (prod : isBinProduct
                       C
                       x y
                       a
                       (enriched_prod_cone_pr1 a)
                       (enriched_prod_cone_pr2 a))
             (HV : conservative_moncat V)
    : is_binary_prod_enriched a.
  Proof.
    use (make_is_binary_prod_enriched_from_z_iso BPV).
    intros w.
    use HV.
    use isweq_iso.
    - exact (prod_from_underlying_arr_map BPV a prod w).
    - exact (prod_from_underlying_arr_map_eq₁ BPV a prod w).
    - exact (prod_from_underlying_arr_map_eq₂ BPV a prod w).
  Defined.

  (**
   6. Products are closed under iso
   *)
  Section ProdIso.
    Context (a : enriched_binary_prod_cone)
            (Ha : is_binary_prod_enriched a)
            (b : C)
            (f : z_iso b a).

    Definition enriched_binary_prod_cone_from_iso
      : enriched_binary_prod_cone
      := make_enriched_binary_prod_cone
           b
           (enriched_from_arr E (f · enriched_prod_cone_pr1 a))
           (enriched_from_arr E (f · enriched_prod_cone_pr2 a)).

    Definition is_binary_prod_enriched_from_iso
      : is_binary_prod_enriched enriched_binary_prod_cone_from_iso.
    Proof.
      intros w.
      use (isBinProduct_z_iso (Ha w)).
      - exact (postcomp_arr_z_iso E w f).
      - abstract
          (cbn ;
           rewrite <- postcomp_arr_comp ;
           apply maponpaths ;
           unfold enriched_binary_prod_cone_from_iso ; cbn ;
           unfold  enriched_prod_cone_pr1 ; cbn ;
           rewrite enriched_to_from_arr ;
           apply idpath).
      - abstract
          (cbn ;
           rewrite <- postcomp_arr_comp ;
           apply maponpaths ;
           unfold enriched_binary_prod_cone_from_iso ; cbn ;
           unfold  enriched_prod_cone_pr2 ; cbn ;
           rewrite enriched_to_from_arr ;
           apply idpath).
    Defined.
  End ProdIso.

  (**
   7. Products are isomorphic
   *)
  Definition map_between_product_enriched
             {a b : enriched_binary_prod_cone}
             (Ha : is_binary_prod_enriched a)
             (Hb : is_binary_prod_enriched b)
    : a --> b
    := is_binary_prod_enriched_arrow
         Hb
         (enriched_prod_cone_pr1 a)
         (enriched_prod_cone_pr2 a).

  Lemma iso_between_product_enriched_inv
        {a b : enriched_binary_prod_cone}
        (Ha : is_binary_prod_enriched a)
        (Hb : is_binary_prod_enriched b)
    : map_between_product_enriched Ha Hb · map_between_product_enriched Hb Ha
      =
      identity _.
  Proof.
    unfold map_between_product_enriched.
    use (is_binary_prod_enriched_arrow_eq Ha).
    - rewrite !assoc'.
      rewrite !is_binary_prod_enriched_arrow_pr1.
      rewrite id_left.
      apply idpath.
    - rewrite !assoc'.
      rewrite !is_binary_prod_enriched_arrow_pr2.
      rewrite id_left.
      apply idpath.
  Qed.

  Definition iso_between_product_enriched
             {a b : enriched_binary_prod_cone}
             (Ha : is_binary_prod_enriched a)
             (Hb : is_binary_prod_enriched b)
    : z_iso a b.
  Proof.
    use make_z_iso.
    - exact (map_between_product_enriched Ha Hb).
    - exact (map_between_product_enriched Hb Ha).
    - split.
      + apply iso_between_product_enriched_inv.
      + apply iso_between_product_enriched_inv.
  Defined.
End EnrichedProducts.

(**
 8. Enriched categories with products
 *)
Definition enrichment_binary_prod
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : UU
  := ∏ (x y : C),
     ∑ (a : enriched_binary_prod_cone E x y),
     is_binary_prod_enriched E x y a.

Proposition isaprop_enrichment_binary_prod
            {V : monoidal_cat}
            {C : category}
            (HC : is_univalent C)
            (E : enrichment C V)
  : isaprop (enrichment_binary_prod E).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use funextsec ; intro x.
  use funextsec ; intro y.
  use subtypePath.
  {
    intro.
    apply isaprop_is_binary_prod_enriched.
  }
  use total2_paths_f.
  - use (isotoid _ HC).
    use iso_between_product_enriched.
    + exact (pr2 (φ₁ x y)).
    + exact (pr2 (φ₂ x y)).
  - rewrite transportf_dirprod.
    use pathsdirprod.
    + rewrite transportf_enriched_arr_l.
      rewrite idtoiso_inv.
      rewrite idtoiso_isotoid.
      cbn.
      refine (_ @ enriched_from_to_arr E _).
      apply maponpaths.
      unfold map_between_product_enriched ; cbn.
      apply is_binary_prod_enriched_arrow_pr1.
    + rewrite transportf_enriched_arr_l.
      rewrite idtoiso_inv.
      rewrite idtoiso_isotoid.
      cbn.
      refine (_ @ enriched_from_to_arr E _).
      apply maponpaths.
      unfold map_between_product_enriched ; cbn.
      apply is_binary_prod_enriched_arrow_pr2.
Qed.

Definition cat_with_enrichment_binary_prod
           (V : monoidal_cat)
  : UU
  := ∑ (C : cat_with_enrichment V), enrichment_binary_prod C.

#[reversible=no] Coercion cat_with_enrichment_binary_prod_to_cat_with_enrichment
         {V : monoidal_cat}
         (C : cat_with_enrichment_binary_prod V)
  : cat_with_enrichment V
  := pr1 C.

Definition binary_prod_of_cat_with_enrichment
           {V : monoidal_cat}
           (C : cat_with_enrichment_binary_prod V)
  : enrichment_binary_prod C
  := pr2 C.
