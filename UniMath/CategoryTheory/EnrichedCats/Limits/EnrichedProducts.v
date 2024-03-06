(*****************************************************************

 Type indexed enriched products

 In this file, we define the type indexed products in enriched
 categories. The definition foollows the same ideas as the
 definition for enriched binary, and the only difference is that
 we index the product by a type.

 Content
 1. Cones of enriched products
 2. Products in an enriched category
 3. Being a product is a proposition
 4. Products in the underlying category
 5. Builders for products
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
Require Import UniMath.CategoryTheory.Limits.Products.

Import MonoidalNotations.
Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedProducts.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          {J : UU}
          (D : J → C).

  (**
   1. Cones of enriched products
   *)
  Definition enriched_prod_cone
    : UU
    := ∑ (a : C), ∏ (j : J), I_{V} --> E ⦃ a , D j ⦄.

  #[reversible] Coercion ob_enriched_prod_cone
           (a : enriched_prod_cone)
    : C
    := pr1 a.

  Definition enriched_prod_cone_pr
             (a : enriched_prod_cone)
             (j : J)
    : a --> D j
    := enriched_to_arr E (pr2 a j).

  Definition make_enriched_prod_cone
             (a : C)
             (p : ∏ (j : J), I_{V} --> E ⦃ a , D j ⦄)
    : enriched_prod_cone
    := a ,, p.

  (**
   2. Products in an enriched category
   *)
  Definition is_prod_enriched
             (a : enriched_prod_cone)
    : UU
    := ∏ (w : C),
       isProduct
         J V
         (λ j, E ⦃ w , D j ⦄)
         (E ⦃ w , a ⦄)
         (λ j, postcomp_arr E w (enriched_prod_cone_pr a j)).

  Definition is_prod_enriched_to_Product
             {a : enriched_prod_cone}
             (Ha : is_prod_enriched a)
             (w : C)
    : Product
        J V
        (λ j, E ⦃ w , D j ⦄).
  Proof.
    use make_Product.
    - exact (E ⦃ w , a ⦄).
    - exact (λ j, postcomp_arr E w (enriched_prod_cone_pr a j)).
    - exact (Ha w).
  Defined.

  Definition prod_enriched
    : UU
    := ∑ (a : enriched_prod_cone),
       is_prod_enriched a.

  #[reversible=no] Coercion cone_of_prod_enriched
           (a : prod_enriched)
    : enriched_prod_cone
    := pr1 a.

  #[reversible=no] Coercion prod_enriched_is_prod
           (a : prod_enriched)
    : is_prod_enriched a
    := pr2 a.

  (**
   3. Being a product is a proposition
   *)
  Proposition isaprop_is_prod_enriched
              (a : enriched_prod_cone)
    : isaprop (is_prod_enriched a).
  Proof.
    repeat (use impred ; intro).
    apply isapropiscontr.
  Qed.

  (**
   4. Products in the underlying category
   *)
  Section InUnderlying.
    Context {a : enriched_prod_cone}
            (Ha : is_prod_enriched a).

    Definition is_prod_enriched_arrow
               {w : C}
               (f : ∏ (j : J), w --> D j)
      : w --> a.
    Proof.
      refine (enriched_to_arr E _).
      use (ProductArrow _ _ (is_prod_enriched_to_Product Ha w)).
      exact (λ j, enriched_from_arr E (f j)).
    Defined.

    Proposition is_prod_enriched_arrow_pr
                {w : C}
                (f : ∏ (j : J), w --> D j)
                (j : J)
      : is_prod_enriched_arrow f · enriched_prod_cone_pr a j
        =
        f j.
    Proof.
      unfold is_prod_enriched_arrow, enriched_prod_cone_pr.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      refine (_ @ ProductPrCommutes
                    _ _ _
                    (is_prod_enriched_to_Product Ha w)
                    _
                    (λ j, enriched_from_arr E (f j))
                    j).
      cbn.
      unfold postcomp_arr, enriched_prod_cone_pr.
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

    Proposition is_prod_enriched_arrow_eq
                {w : C}
                {f g : w --> a}
                (q : ∏ (j : J),
                     f · enriched_prod_cone_pr a j
                     =
                     g · enriched_prod_cone_pr a j)
      : f = g.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use (ProductArrow_eq
               _ _ _
               (is_prod_enriched_to_Product Ha w)).
      intro j.
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
      exact (q j).
    Qed.

    Definition underlying_Product
      : Product J C D.
    Proof.
      use make_Product.
      - exact a.
      - exact (enriched_prod_cone_pr a).
      - intros w f.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros φ₁ φ₂ ;
             use subtypePath ; [ intro ; use impred ; intro ; apply homset_property | ] ;
             exact (is_prod_enriched_arrow_eq
                      (λ j, pr2 φ₁ j @ !(pr2 φ₂ j)))).
        + exact (is_prod_enriched_arrow f
                 ,,
                 is_prod_enriched_arrow_pr f).
    Defined.
  End InUnderlying.

  (**
   5. Builders for products
   *)
  Definition make_is_prod_enriched
             (a : enriched_prod_cone)
             (pair : ∏ (w : C) (v : V)
                       (f : ∏ (j : J), v --> E ⦃ w , D j ⦄),
                     v --> E ⦃ w , a ⦄)
             (pair_pr : ∏ (w : C) (v : V)
                          (f : ∏ (j : J), v --> E ⦃ w , D j ⦄)
                          (j : J),
                        pair w v f · postcomp_arr E w (enriched_prod_cone_pr a j)
                        =
                          f j)
             (pair_eq : ∏ (w : C) (v : V)
                          (φ₁ φ₂ : v --> E ⦃ w , a ⦄)
                          (q : ∏ (j : J),
                           φ₁ · postcomp_arr E w (enriched_prod_cone_pr a j)
                           =
                           φ₂ · postcomp_arr E w (enriched_prod_cone_pr a j)),
                        φ₁ = φ₂)
    : is_prod_enriched a.
  Proof.
    intro w.
    use make_isProduct.
    { apply homset_property. }
    intros v f.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; use impred ; intro ; apply homset_property | ] ;
         exact (pair_eq
                  w v
                  (pr1 φ₁) (pr1 φ₂)
                  (λ j, pr2 φ₁ j @ !(pr2 φ₂ j)))).
    - simple refine (_ ,, _).
      + exact (pair w v f).
      + exact (pair_pr w v f).
  Defined.

  Definition prod_enriched_to_prod
             (PV : Products J V)
             (a : enriched_prod_cone)
             (w : C)
    : E ⦃ w, a ⦄ --> PV (λ j, E ⦃ w, D j ⦄).
  Proof.
    use ProductArrow.
    exact (λ j, postcomp_arr E w (enriched_prod_cone_pr a j)).
  Defined.

  Definition make_is_prod_enriched_from_z_iso
             (PV : Products J V)
             (a : enriched_prod_cone)
             (Ha : ∏ (w : C),
                   is_z_isomorphism (prod_enriched_to_prod PV a w))
    : is_prod_enriched a.
  Proof.
    intro w.
    use (isProduct_z_iso _ _ _ _ (pr2 (PV (λ j, E ⦃ w , D j ⦄)))).
    - exact (z_iso_inv (_ ,, Ha w)).
    - abstract
        (intro j ;
         unfold prod_enriched_to_prod ; cbn ;
         refine (!_) ;
         apply (ProductPrCommutes _ _ _ (PV (λ j, E ⦃ w , D j ⦄)))).
  Defined.

  Section ProductFromUnderlying.
    Context (PV : Products J V)
            (a : enriched_prod_cone)
            (prod : isProduct J C D a (enriched_prod_cone_pr a))
            (w : C).

    Definition prod_from_underlying_arr_map
               (f : I_{V} --> PV (λ j, E ⦃ w , D j ⦄))
      : I_{V} --> E ⦃ w, a ⦄.
    Proof.
      apply enriched_from_arr.
      use (ProductArrow _ _ (make_Product _ _ _ _ _ prod)).
      intro j.
      exact (enriched_to_arr E (f · ProductPr _ _ _ j)).
    Defined.

    Proposition prod_from_underlying_arr_map_eq₁
                (f : I_{V} --> E ⦃ w, a ⦄)
      : prod_from_underlying_arr_map (f · prod_enriched_to_prod PV a w)
        =
        f.
    Proof.
      unfold prod_from_underlying_arr_map.
      refine (_ @ enriched_from_to_arr E f).
      apply maponpaths.
      use (ProductArrow_eq
             _ _ _
             (make_Product _ _ _ _ _ prod)).
      unfold prod_enriched_to_prod.
      intro j.
      rewrite ProductPrCommutes ; cbn.
      rewrite (enriched_to_arr_comp E).
      apply maponpaths.
      rewrite tensor_split.
      rewrite !assoc.
      rewrite <- tensor_linvunitor.
      rewrite !assoc'.
      rewrite enriched_from_to_arr.
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply (ProductPrCommutes _ _ _ (PV (λ k, E ⦃ w , D k ⦄)) _ _ j).
      }
      apply idpath.
    Qed.

    Proposition prod_from_underlying_arr_map_eq₂
                (f : I_{V} --> PV (λ j, E ⦃ w , D j ⦄))
      : prod_from_underlying_arr_map f · prod_enriched_to_prod PV a w = f.
    Proof.
      unfold prod_from_underlying_arr_map.
      use (ProductArrow_eq
             _ _ _
             (PV (λ j, E ⦃ w, D j ⦄))).
      unfold prod_enriched_to_prod.
      intro j.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (ProductPrCommutes _ _ _ (PV (λ k, E ⦃ w , D k ⦄)) _ _ j).
      }
      rewrite enriched_from_arr_postcomp.
      refine (_ @ enriched_from_to_arr E _).
      apply maponpaths.
      apply (ProductPrCommutes _ _ _ (make_Product _ _ _ _ _ prod)).
    Qed.
  End ProductFromUnderlying.

  Definition make_is_prod_enriched_from_underlying
             (PV : Products J V)
             (a : enriched_prod_cone)
             (prod : isProduct
                       J C D
                       a
                       (enriched_prod_cone_pr a))
             (HV : conservative_moncat V)
    : is_prod_enriched a.
  Proof.
    use (make_is_prod_enriched_from_z_iso PV).
    intros w.
    use HV.
    use isweq_iso.
    - exact (prod_from_underlying_arr_map PV a prod w).
    - exact (prod_from_underlying_arr_map_eq₁ PV a prod w).
    - exact (prod_from_underlying_arr_map_eq₂ PV a prod w).
  Defined.

  (**
   6. Products are closed under iso
   *)
  Section ProdIso.
    Context (a : enriched_prod_cone)
            (Ha : is_prod_enriched a)
            (b : C)
            (f : z_iso b a).

    Definition enriched_prod_cone_from_iso
      : enriched_prod_cone
      := make_enriched_prod_cone
           b
           (λ j, enriched_from_arr E (f · enriched_prod_cone_pr a j)).

    Definition is_prod_enriched_from_iso
      : is_prod_enriched enriched_prod_cone_from_iso.
    Proof.
      intros w.
      use (isProduct_z_iso _ _ _ _ (Ha w)).
      - exact (postcomp_arr_z_iso E w (z_iso_inv f)).
      - abstract
          (intro j ;
           cbn ;
           rewrite <- postcomp_arr_comp ;
           apply maponpaths ;
           unfold enriched_prod_cone_from_iso ; cbn ;
           unfold  enriched_prod_cone_pr ; cbn ;
           rewrite enriched_to_from_arr ;
           apply idpath).
    Defined.
  End ProdIso.

  (**
   7. Products are isomorphic
   *)
  Definition map_between_product_enriched
             {a b : enriched_prod_cone}
             (Ha : is_prod_enriched a)
             (Hb : is_prod_enriched b)
    : a --> b
    := is_prod_enriched_arrow
         Hb
         (enriched_prod_cone_pr a).

  Lemma iso_between_product_enriched_inv
        {a b : enriched_prod_cone}
        (Ha : is_prod_enriched a)
        (Hb : is_prod_enriched b)
    : map_between_product_enriched Ha Hb · map_between_product_enriched Hb Ha
      =
      identity _.
  Proof.
    unfold map_between_product_enriched.
    use (is_prod_enriched_arrow_eq Ha).
    intro j.
    rewrite !assoc'.
    rewrite !is_prod_enriched_arrow_pr.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition iso_between_product_enriched
             {a b : enriched_prod_cone}
             (Ha : is_prod_enriched a)
             (Hb : is_prod_enriched b)
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
Definition enrichment_prod
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
           (J : UU)
  : UU
  := ∏ (D : J → C),
     ∑ (a : enriched_prod_cone E D),
     is_prod_enriched E D a.

Proposition isaprop_enrichment_prod
            {V : monoidal_cat}
            {C : category}
            (HC : is_univalent C)
            (E : enrichment C V)
            (J : UU)
  : isaprop (enrichment_prod E J).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use funextsec ; intro D.
  use subtypePath.
  {
    intro.
    apply isaprop_is_prod_enriched.
  }
  use total2_paths_f.
  - use (isotoid _ HC).
    use iso_between_product_enriched.
    + exact (pr2 (φ₁ D)).
    + exact (pr2 (φ₂ D)).
  - rewrite transportf_sec_constant.
    use funextsec.
    intro j.
    rewrite transportf_enriched_arr_l.
    rewrite idtoiso_inv.
    rewrite idtoiso_isotoid.
    cbn.
    refine (_ @ enriched_from_to_arr E _).
    apply maponpaths.
    unfold map_between_product_enriched ; cbn.
    etrans.
    {
      apply is_prod_enriched_arrow_pr.
    }
    apply idpath.
Qed.

Definition cat_with_enrichment_product
           (V : monoidal_cat)
           (J : UU)
  : UU
  := ∑ (C : cat_with_enrichment V), enrichment_prod C J.

#[reversible=no] Coercion cat_with_enrichment_product_to_cat_with_enrichment
         {V : monoidal_cat}
         {J : UU}
         (C : cat_with_enrichment_product V J)
  : cat_with_enrichment V
  := pr1 C.

Definition products_of_cat_with_enrichment
           {V : monoidal_cat}
           {J : UU}
           (C : cat_with_enrichment_product V J)
  : enrichment_prod C J
  := pr2 C.
