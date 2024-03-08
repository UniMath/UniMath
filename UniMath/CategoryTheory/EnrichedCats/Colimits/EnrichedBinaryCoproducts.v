(*****************************************************************

 Coproducts in enriched categories

 In this file, we define the notion of coproducts for enriched
 categories. The idea is the same as for initial objects: we need
 to express the universal property in the arbitrary monoidal
 categories instead of just set.

 Let `x` and `y` be objects of a category `C` enriched over `V`.
 The coproduct `x + y` satisfies the following universal property:
 for every `z`, the hom object `C ⟦ x + y , z ⟧` is the product
 of the hom objects `C ⟦ x , z ⟧` and `C ⟦ y , z ⟧`.

 Contents
 1. Cocones of enriched coproducts
 2. Binary products in an enriched category
 3. Being a binary coproduct is a proposition
 4. Binary products in the underlying category
 5. Builders for binary coproducts
 6. Coproducts are closed under iso
 7. Coproducts are isomorphic
 8. Enriched categories with coproducts

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
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.

Import MonoidalNotations.
Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedCoproducts.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          (x y : C).

  (**
   1. Cocones of enriched coproducts
   *)
  Definition enriched_binary_coprod_cocone
    : UU
    := ∑ (a : C),
       I_{V} --> E ⦃ x , a ⦄
       ×
       I_{V} --> E ⦃ y , a ⦄.

  #[reversible=no] Coercion ob_enriched_binary_coprod_cocone
           (a : enriched_binary_coprod_cocone)
    : C
    := pr1 a.

  Definition enriched_coprod_cocone_in1
             (a : enriched_binary_coprod_cocone)
    : x --> a
    := enriched_to_arr E (pr12 a).

  Definition enriched_coprod_cocone_in2
             (a : enriched_binary_coprod_cocone)
    : y --> a
    := enriched_to_arr E (pr22 a).

  Definition make_enriched_binary_coprod_cocone
             (a : C)
             (p₁ : I_{V} --> E ⦃ x , a ⦄)
             (p₂ : I_{V} --> E ⦃ y , a ⦄)
    : enriched_binary_coprod_cocone
    := a ,, p₁ ,, p₂.

  (**
   2. Binary products in an enriched category
   *)
  Definition is_binary_coprod_enriched
             (a : enriched_binary_coprod_cocone)
    : UU
    := ∏ (w : C),
       isBinProduct
         V
         (E ⦃ x , w ⦄)
         (E ⦃ y , w ⦄)
         (E ⦃ a , w ⦄)
         (precomp_arr E w (enriched_coprod_cocone_in1 a))
         (precomp_arr E w (enriched_coprod_cocone_in2 a)).

  Definition is_binary_coprod_enriched_to_BinProduct
             {a : enriched_binary_coprod_cocone}
             (Ha : is_binary_coprod_enriched a)
             (w : C)
    : BinProduct
        V
        (E ⦃ x , w ⦄)
        (E ⦃ y , w ⦄).
  Proof.
    use make_BinProduct.
    - exact (E ⦃ a , w ⦄).
    - exact (precomp_arr E w (enriched_coprod_cocone_in1 a)).
    - exact (precomp_arr E w (enriched_coprod_cocone_in2 a)).
    - exact (Ha w).
  Defined.

  Definition binary_coprod_enriched
    : UU
    := ∑ (a : enriched_binary_coprod_cocone),
       is_binary_coprod_enriched a.

  #[reversible=no] Coercion cone_of_binary_coprod_enriched
           (a : binary_coprod_enriched)
    : enriched_binary_coprod_cocone
    := pr1 a.

  #[reversible=no] Coercion binary_coprod_enriched_is_coprod
           (a : binary_coprod_enriched)
    : is_binary_coprod_enriched a
    := pr2 a.

  (**
   3. Being a binary coproduct is a proposition
   *)
  Proposition isaprop_is_binary_coprod_enriched
              (a : enriched_binary_coprod_cocone)
    : isaprop (is_binary_coprod_enriched a).
  Proof.
    use impred ; intro.
    apply isaprop_isBinProduct.
  Qed.

  (**
   4. Binary products in the underlying category
   *)
  Section InUnderlying.
    Context {a : enriched_binary_coprod_cocone}
            (Ha : is_binary_coprod_enriched a).

    Definition is_binary_coprod_enriched_arrow
               {w : C}
               (f : x --> w)
               (g : y --> w)
      : a --> w.
    Proof.
      refine (enriched_to_arr E _).
      use (BinProductArrow _ (is_binary_coprod_enriched_to_BinProduct Ha w)).
      - exact (enriched_from_arr E f).
      - exact (enriched_from_arr E g).
    Defined.

    Proposition is_binary_coprod_enriched_arrow_in1
                {w : C}
                (f : x --> w)
                (g : y --> w)
      : enriched_coprod_cocone_in1 a · is_binary_coprod_enriched_arrow f g
        =
        f.
    Proof.
      unfold is_binary_coprod_enriched_arrow, enriched_coprod_cocone_in1.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      refine (_ @ BinProductPr1Commutes
                    _ _ _
                    (is_binary_coprod_enriched_to_BinProduct Ha w)
                    _
                    (enriched_from_arr E f)
                    (enriched_from_arr E g)).
      cbn.
      unfold precomp_arr, enriched_coprod_cocone_in1.
      rewrite enriched_from_arr_comp.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !enriched_from_to_arr.
      rewrite tensor_rinvunitor.
      rewrite mon_linvunitor_I_mon_rinvunitor_I.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_split'.
      apply idpath.
    Qed.

    Proposition is_binary_coprod_enriched_arrow_in2
                {w : C}
                (f : x --> w)
                (g : y --> w)
      : enriched_coprod_cocone_in2 a · is_binary_coprod_enriched_arrow f g
        =
        g.
    Proof.
      unfold is_binary_coprod_enriched_arrow, enriched_coprod_cocone_in2.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      refine (_ @ BinProductPr2Commutes
                    _ _ _
                    (is_binary_coprod_enriched_to_BinProduct Ha w)
                    _
                    (enriched_from_arr E f)
                    (enriched_from_arr E g)).
      cbn.
      unfold precomp_arr, enriched_coprod_cocone_in2.
      rewrite enriched_from_arr_comp.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !enriched_from_to_arr.
      rewrite tensor_rinvunitor.
      rewrite mon_linvunitor_I_mon_rinvunitor_I.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_split'.
      apply idpath.
    Qed.

    Proposition is_binary_coprod_enriched_arrow_eq
                {w : C}
                {f g : a --> w}
                (q₁ : enriched_coprod_cocone_in1 a · f = enriched_coprod_cocone_in1 a · g)
                (q₂ : enriched_coprod_cocone_in2 a · f = enriched_coprod_cocone_in2 a · g)
      : f = g.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use (BinProductArrowsEq
               _ _ _
               (is_binary_coprod_enriched_to_BinProduct Ha w)).
      - cbn.
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
        exact q₁.
      - cbn.
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
        exact q₂.
    Qed.

    Definition underlying_BinCoproduct
      : BinCoproduct x y.
    Proof.
      use make_BinCoproduct.
      - exact a.
      - exact (enriched_coprod_cocone_in1 a).
      - exact (enriched_coprod_cocone_in2 a).
      - intros w f g.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros φ₁ φ₂ ;
             use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
             exact (is_binary_coprod_enriched_arrow_eq
                      (pr12 φ₁ @ !(pr12 φ₂))
                      (pr22 φ₁ @ !(pr22 φ₂)))).
        + exact (is_binary_coprod_enriched_arrow f g
                 ,,
                 is_binary_coprod_enriched_arrow_in1 f g
                 ,,
                 is_binary_coprod_enriched_arrow_in2 f g).
    Defined.
  End InUnderlying.

  (**
   5. Builders for binary coproducts
   *)
  Definition make_is_binary_coprod_enriched
             (a : enriched_binary_coprod_cocone)
             (sum : ∏ (w : C) (v : V)
                      (f : v --> E ⦃ x , w ⦄)
                      (g : v --> E ⦃ y , w ⦄),
                    v --> E ⦃ a , w ⦄)
             (sum_in1 : ∏ (w : C) (v : V)
                          (f : v --> E ⦃ x , w ⦄)
                          (g : v --> E ⦃ y , w ⦄),
                         sum w v f g · precomp_arr E w (enriched_coprod_cocone_in1 a)
                         =
                         f)
             (sum_in2 : ∏ (w : C) (v : V)
                          (f : v --> E ⦃ x , w ⦄)
                          (g : v --> E ⦃ y , w ⦄),
                         sum w v f g · precomp_arr E w (enriched_coprod_cocone_in2 a)
                         =
                         g)
             (sum_eq : ∏ (w : C) (v : V)
                         (φ₁ φ₂ : v --> E ⦃ a , w ⦄)
                         (q₁ : φ₁ · precomp_arr E w (enriched_coprod_cocone_in1 a)
                               =
                               φ₂ · precomp_arr E w (enriched_coprod_cocone_in1 a))
                         (q₂ : φ₁ · precomp_arr E w (enriched_coprod_cocone_in2 a)
                               =
                               φ₂ · precomp_arr E w (enriched_coprod_cocone_in2 a)),
                        φ₁ = φ₂)
    : is_binary_coprod_enriched a.
  Proof.
    intro w.
    use make_isBinProduct.
    intros v f g.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         exact (sum_eq
                  w v
                  (pr1 φ₁) (pr1 φ₂)
                  (pr12 φ₁ @ !(pr12 φ₂)) (pr22 φ₁ @ !(pr22 φ₂)))).
    - simple refine (_ ,, _ ,, _).
      + exact (sum w v f g).
      + exact (sum_in1 w v f g).
      + exact (sum_in2 w v f g).
  Defined.

  Definition binary_coprod_enriched_to_coprod
             (BPV : BinProducts V)
             (a : enriched_binary_coprod_cocone)
             (w : C)
    : E ⦃ a , w ⦄ --> BPV (E ⦃ x , w ⦄) (E ⦃ y , w ⦄).
  Proof.
    use BinProductArrow.
    - exact (precomp_arr E w (enriched_coprod_cocone_in1 a)).
    - exact (precomp_arr E w (enriched_coprod_cocone_in2 a)).
  Defined.

  Definition make_is_binary_coprod_enriched_from_z_iso
             (BPV : BinProducts V)
             (a : enriched_binary_coprod_cocone)
             (Ha : ∏ (w : C),
                   is_z_isomorphism (binary_coprod_enriched_to_coprod BPV a w))
    : is_binary_coprod_enriched a.
  Proof.
    intro w.
    use (isBinProduct_z_iso (pr2 (BPV (E ⦃ x , w ⦄) (E ⦃ y , w ⦄))) (_ ,, Ha w) _).
    - abstract
        (unfold binary_coprod_enriched_to_coprod ; cbn ;
         refine (!_) ;
         apply BinProductPr1Commutes).
    - abstract
        (unfold binary_coprod_enriched_to_coprod ; cbn ;
         refine (!_) ;
         apply BinProductPr2Commutes).
  Defined.

  Section BinaryCoproductFromUnderlying.
    Context (BPV : BinProducts V)
            (a : enriched_binary_coprod_cocone)
            (coprod : isBinCoproduct
                        C
                        x y
                        a
                        (enriched_coprod_cocone_in1 a)
                        (enriched_coprod_cocone_in2 a))
            (w : C).

    Definition coprod_from_underlying_arr_map
               (f : I_{V} --> BPV (E ⦃ x , w ⦄) (E ⦃ y , w ⦄))
      : I_{V} --> E ⦃ a , w ⦄.
    Proof.
      apply enriched_from_arr.
      use (BinCoproductArrow (make_BinCoproduct _ _ _ _ _ _ coprod)).
      - exact (enriched_to_arr E (f · BinProductPr1 _ _)).
      - exact (enriched_to_arr E (f · BinProductPr2 _ _)).
    Defined.

    Proposition coprod_from_underlying_arr_map_eq₁
                (f : I_{V} --> E ⦃ a , w ⦄)
      : coprod_from_underlying_arr_map (f · binary_coprod_enriched_to_coprod BPV a w)
        =
        f.
    Proof.
      unfold coprod_from_underlying_arr_map.
      refine (_ @ enriched_from_to_arr E f).
      apply maponpaths.
      use (BinCoproductArrowsEq
             _ _ _
             (make_BinCoproduct C x y a _ _ coprod)).
      - unfold binary_coprod_enriched_to_coprod.
        rewrite !assoc'.
        rewrite !BinProductPr1Commutes.
        rewrite !BinCoproductIn1Commutes ; cbn.
        rewrite (enriched_to_arr_comp E).
        apply maponpaths.
        unfold precomp_arr.
        rewrite !assoc.
        rewrite tensor_rinvunitor.
        rewrite mon_linvunitor_I_mon_rinvunitor_I.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite enriched_from_to_arr.
        rewrite <- tensor_split'.
        apply idpath.
      - unfold binary_coprod_enriched_to_coprod.
        rewrite !assoc'.
        rewrite !BinProductPr2Commutes.
        rewrite !BinCoproductIn2Commutes ; cbn.
        rewrite (enriched_to_arr_comp E).
        apply maponpaths.
        unfold precomp_arr.
        rewrite !assoc.
        rewrite tensor_rinvunitor.
        rewrite mon_linvunitor_I_mon_rinvunitor_I.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite enriched_from_to_arr.
        rewrite <- tensor_split'.
        apply idpath.
    Qed.

    Proposition coprod_from_underlying_arr_map_eq₂
                (f : I_{V} --> BPV (E ⦃ x , w ⦄) (E ⦃ y , w ⦄))
      : coprod_from_underlying_arr_map f · binary_coprod_enriched_to_coprod BPV a w = f.
    Proof.
      unfold coprod_from_underlying_arr_map.
      use (BinProductArrowsEq
             _ _ _
             (BPV (E ⦃ x , w ⦄) (E ⦃ y , w ⦄))).
      - unfold binary_coprod_enriched_to_coprod.
        rewrite !assoc'.
        rewrite !BinProductPr1Commutes.
        rewrite enriched_from_arr_precomp.
        refine (_ @ enriched_from_to_arr E _).
        apply maponpaths.
        apply (BinCoproductIn1Commutes _ _ _ (make_BinCoproduct C x y a _ _ coprod)).
      - unfold binary_coprod_enriched_to_coprod.
        rewrite !assoc'.
        rewrite !BinProductPr2Commutes.
        rewrite enriched_from_arr_precomp.
        refine (_ @ enriched_from_to_arr E _).
        apply maponpaths.
        apply (BinCoproductIn2Commutes _ _ _ (make_BinCoproduct C x y a _ _ coprod)).
    Qed.
  End BinaryCoproductFromUnderlying.

  Definition make_is_binary_coprod_enriched_from_underlying
             (BPV : BinProducts V)
             (a : enriched_binary_coprod_cocone)
             (prod : isBinCoproduct
                       C
                       x y
                       a
                       (enriched_coprod_cocone_in1 a)
                       (enriched_coprod_cocone_in2 a))
             (HV : conservative_moncat V)
    : is_binary_coprod_enriched a.
  Proof.
    use (make_is_binary_coprod_enriched_from_z_iso BPV).
    intros w.
    use HV.
    use isweq_iso.
    - exact (coprod_from_underlying_arr_map BPV a prod w).
    - exact (coprod_from_underlying_arr_map_eq₁ BPV a prod w).
    - exact (coprod_from_underlying_arr_map_eq₂ BPV a prod w).
  Defined.

  (**
   6. Coproducts are closed under iso
   *)
  Section CoprodIso.
    Context (a : enriched_binary_coprod_cocone)
            (Ha : is_binary_coprod_enriched a)
            (b : C)
            (f : z_iso a b).

    Definition enriched_binary_prod_cone_from_iso
      : enriched_binary_coprod_cocone
      := make_enriched_binary_coprod_cocone
           b
           (enriched_from_arr E (enriched_coprod_cocone_in1 a · f))
           (enriched_from_arr E (enriched_coprod_cocone_in2 a · f)).

    Definition is_binary_coprod_enriched_from_iso
      : is_binary_coprod_enriched enriched_binary_prod_cone_from_iso.
    Proof.
      intros w.
      use (isBinProduct_z_iso (Ha w)).
      - exact (precomp_arr_z_iso E w f).
      - abstract
          (cbn ;
           rewrite <- precomp_arr_comp ;
           apply maponpaths ;
           unfold enriched_binary_prod_cone_from_iso ; cbn ;
           unfold enriched_coprod_cocone_in1 ; cbn ;
           rewrite enriched_to_from_arr ;
           apply idpath).
      - abstract
          (cbn ;
           rewrite <- precomp_arr_comp ;
           apply maponpaths ;
           unfold enriched_binary_prod_cone_from_iso ; cbn ;
           unfold enriched_coprod_cocone_in2 ; cbn ;
           rewrite enriched_to_from_arr ;
           apply idpath).
    Defined.
  End CoprodIso.

  (**
   7. Coproducts are isomorphic
   *)
  Definition map_between_coproduct_enriched
             {a b : enriched_binary_coprod_cocone}
             (Ha : is_binary_coprod_enriched a)
             (Hb : is_binary_coprod_enriched b)
    : a --> b
    := is_binary_coprod_enriched_arrow
         Ha
         (enriched_coprod_cocone_in1 b)
         (enriched_coprod_cocone_in2 b).

  Lemma iso_between_coproduct_enriched_inv
        {a b : enriched_binary_coprod_cocone}
        (Ha : is_binary_coprod_enriched a)
        (Hb : is_binary_coprod_enriched b)
    : map_between_coproduct_enriched Ha Hb · map_between_coproduct_enriched Hb Ha
      =
      identity _.
  Proof.
    unfold map_between_coproduct_enriched.
    use (is_binary_coprod_enriched_arrow_eq Ha).
    - rewrite !assoc.
      rewrite !is_binary_coprod_enriched_arrow_in1.
      rewrite id_right.
      apply idpath.
    - rewrite !assoc.
      rewrite !is_binary_coprod_enriched_arrow_in2.
      rewrite id_right.
      apply idpath.
  Qed.

  Definition iso_between_coproduct_enriched
             {a b : enriched_binary_coprod_cocone}
             (Ha : is_binary_coprod_enriched a)
             (Hb : is_binary_coprod_enriched b)
    : z_iso a b.
  Proof.
    use make_z_iso.
    - exact (map_between_coproduct_enriched Ha Hb).
    - exact (map_between_coproduct_enriched Hb Ha).
    - split.
      + apply iso_between_coproduct_enriched_inv.
      + apply iso_between_coproduct_enriched_inv.
  Defined.
End EnrichedCoproducts.

(**
 8. Enriched categories with coproducts
 *)
Definition enrichment_binary_coprod
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
  : UU
  := ∏ (x y : C),
     ∑ (a : enriched_binary_coprod_cocone E x y),
     is_binary_coprod_enriched E x y a.

Proposition isaprop_enrichment_binary_coprod
            {V : monoidal_cat}
            {C : category}
            (HC : is_univalent C)
            (E : enrichment C V)
  : isaprop (enrichment_binary_coprod E).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use funextsec ; intro x.
  use funextsec ; intro y.
  use subtypePath.
  {
    intro.
    apply isaprop_is_binary_coprod_enriched.
  }
  use total2_paths_f.
  - use (isotoid _ HC).
    use iso_between_coproduct_enriched.
    + exact (pr2 (φ₁ x y)).
    + exact (pr2 (φ₂ x y)).
  - rewrite transportf_dirprod.
    use pathsdirprod.
    + rewrite transportf_enriched_arr_r.
      rewrite idtoiso_isotoid.
      cbn.
      refine (_ @ enriched_from_to_arr E _).
      apply maponpaths.
      unfold map_between_coproduct_enriched ; cbn.
      apply is_binary_coprod_enriched_arrow_in1.
    + rewrite transportf_enriched_arr_r.
      rewrite idtoiso_isotoid.
      cbn.
      refine (_ @ enriched_from_to_arr E _).
      apply maponpaths.
      unfold map_between_coproduct_enriched ; cbn.
      apply is_binary_coprod_enriched_arrow_in2.
Qed.

Definition cat_with_enrichment_coproduct
           (V : monoidal_cat)
  : UU
  := ∑ (C : cat_with_enrichment V), enrichment_binary_coprod C.

#[reversible=no] Coercion cat_with_enrichment_coproduct_to_cat_with_enrichment
         {V : monoidal_cat}
         (C : cat_with_enrichment_coproduct V)
  : cat_with_enrichment V
  := pr1 C.

Definition coproducts_of_cat_with_enrichment
           {V : monoidal_cat}
           (C : cat_with_enrichment_coproduct V)
  : enrichment_binary_coprod C
  := pr2 C.
