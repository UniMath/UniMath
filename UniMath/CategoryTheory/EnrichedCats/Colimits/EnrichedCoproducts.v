(*****************************************************************

 Type indexed enriched coproducts

 In this file, we define type indexed coproducts for enriched
 categories. The ideas are similar as for binary coproducts; the
 only difference being that instead of having two summands, the
 summands are indexed by a type.

 Content
 1. Cocones of enriched coproducts
 2. Coproducts in an enriched category
 3. Being a coproduct is a proposition
 4. Coproducts in the underlying category
 5. Builders for coproducts
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
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Coproducts.

Import MonoidalNotations.
Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedCoproducts.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          {J : UU}
          (D : J → C).

  (**
   1. Cocones of enriched coproducts
   *)
  Definition enriched_coprod_cocone
    : UU
    := ∑ (a : C), ∏ (j : J), I_{V} --> E ⦃ D j , a ⦄.

  #[reversible] Coercion ob_enriched_coprod_cocone
           (a : enriched_coprod_cocone)
    : C
    := pr1 a.

  Definition enriched_coprod_cocone_in
             (a : enriched_coprod_cocone)
             (j : J)
    : D j --> a
    := enriched_to_arr E (pr2 a j).

  Definition make_enriched_coprod_cocone
             (a : C)
             (p : ∏ (j : J), I_{V} --> E ⦃ D j , a ⦄)
    : enriched_coprod_cocone
    := a ,, p.

  (**
   2. Coproducts in an enriched category
   *)
  Definition is_coprod_enriched
             (a : enriched_coprod_cocone)
    : UU
    := ∏ (w : C),
       isProduct
         J V
         (λ j, E ⦃ D j , w ⦄)
         (E ⦃ a , w ⦄)
         (λ j, precomp_arr E w (enriched_coprod_cocone_in a j)).

  Definition is_coprod_enriched_to_Product
             {a : enriched_coprod_cocone}
             (Ha : is_coprod_enriched a)
             (w : C)
    : Product
        J V
        (λ j, E ⦃ D j , w ⦄).
  Proof.
    use make_Product.
    - exact (E ⦃ a , w ⦄).
    - exact (λ j, precomp_arr E w (enriched_coprod_cocone_in a j)).
    - exact (Ha w).
  Defined.

  Definition coprod_enriched
    : UU
    := ∑ (a : enriched_coprod_cocone),
       is_coprod_enriched a.

  #[reversible=no] Coercion cocone_of_coprod_enriched
           (a : coprod_enriched)
    : enriched_coprod_cocone
    := pr1 a.

  #[reversible=no] Coercion coprod_enriched_is_coprod
           (a : coprod_enriched)
    : is_coprod_enriched a
    := pr2 a.

  (**
   3. Being a coproduct is a proposition
   *)
  Proposition isaprop_is_coprod_enriched
              (a : enriched_coprod_cocone)
    : isaprop (is_coprod_enriched a).
  Proof.
    repeat (use impred ; intro).
    apply isapropiscontr.
  Qed.

  (**
   4. Coproducts in the underlying category
   *)
  Section InUnderlying.
    Context {a : enriched_coprod_cocone}
            (Ha : is_coprod_enriched a).

    Definition is_coprod_enriched_arrow
               {w : C}
               (f : ∏ (j : J), D j --> w)
      : a --> w.
    Proof.
      refine (enriched_to_arr E _).
      use (ProductArrow _ _ (is_coprod_enriched_to_Product Ha w)).
      exact (λ j, enriched_from_arr E (f j)).
    Defined.

    Proposition is_coprod_enriched_arrow_in
                {w : C}
                (f : ∏ (j : J), D j --> w)
                (j : J)
      : enriched_coprod_cocone_in a j · is_coprod_enriched_arrow f
        =
        f j.
    Proof.
      unfold is_coprod_enriched_arrow, enriched_coprod_cocone_in.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      refine (_ @ ProductPrCommutes
                    _ _ _
                    (is_coprod_enriched_to_Product Ha w)
                    _
                    (λ j, enriched_from_arr E (f j))
                    j).
      cbn.
      unfold precomp_arr, enriched_coprod_cocone_in.
      rewrite enriched_from_arr_comp.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_rinvunitor.
      rewrite !assoc'.
      rewrite mon_linvunitor_I_mon_rinvunitor_I.
      apply maponpaths.
      rewrite <- tensor_split'.
      rewrite !enriched_from_to_arr.
      apply idpath.
    Qed.

    Proposition is_coprod_enriched_arrow_eq
                {w : C}
                {f g : a --> w}
                (q : ∏ (j : J),
                     enriched_coprod_cocone_in a j · f
                     =
                     enriched_coprod_cocone_in a j · g)
      : f = g.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use (ProductArrow_eq
               _ _ _
               (is_coprod_enriched_to_Product Ha w)).
      intro j.
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
      exact (q j).
    Qed.

    Definition underlying_Coproduct
      : Coproduct J C D.
    Proof.
      use make_Coproduct.
      - exact a.
      - exact (enriched_coprod_cocone_in a).
      - intros w f.
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros φ₁ φ₂ ;
             use subtypePath ; [ intro ; use impred ; intro ; apply homset_property | ] ;
             exact (is_coprod_enriched_arrow_eq
                      (λ j, pr2 φ₁ j @ !(pr2 φ₂ j)))).
        + exact (is_coprod_enriched_arrow f
                 ,,
                 is_coprod_enriched_arrow_in f).
    Defined.
  End InUnderlying.

  (**
   5. Builders for coproducts
   *)
  Definition make_is_coprod_enriched
             (a : enriched_coprod_cocone)
             (sum : ∏ (w : C) (v : V)
                      (f : ∏ (j : J), v --> E ⦃ D j , w ⦄),
                     v --> E ⦃ a , w ⦄)
             (in_sum : ∏ (w : C) (v : V)
                         (f : ∏ (j : J), v --> E ⦃ D j , w ⦄)
                         (j : J),
                       sum w v f · precomp_arr E w (enriched_coprod_cocone_in a j)
                       =
                       f j)
             (sum_eq : ∏ (w : C) (v : V)
                         (φ₁ φ₂ : v --> E ⦃ a , w ⦄)
                         (q : ∏ (j : J),
                          φ₁ · precomp_arr E w (enriched_coprod_cocone_in a j)
                          =
                          φ₂ · precomp_arr E w (enriched_coprod_cocone_in a j)),
                       φ₁ = φ₂)
    : is_coprod_enriched a.
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
         exact (sum_eq
                  w v
                  (pr1 φ₁) (pr1 φ₂)
                  (λ j, pr2 φ₁ j @ !(pr2 φ₂ j)))).
    - simple refine (_ ,, _).
      + exact (sum w v f).
      + exact (in_sum w v f).
  Defined.

  Definition coprod_enriched_to_prod
             (PV : Products J V)
             (a : enriched_coprod_cocone)
             (w : C)
    : E ⦃ a , w ⦄ --> PV (λ j, E ⦃ D j , w ⦄).
  Proof.
    use ProductArrow.
    exact (λ j, precomp_arr E w (enriched_coprod_cocone_in a j)).
  Defined.

  Definition make_is_coprod_enriched_from_z_iso
             (PV : Products J V)
             (a : enriched_coprod_cocone)
             (Ha : ∏ (w : C),
                   is_z_isomorphism (coprod_enriched_to_prod PV a w))
    : is_coprod_enriched a.
  Proof.
    intro w.
    use (isProduct_z_iso _ _ _ _ (pr2 (PV (λ j, E ⦃ D j , w ⦄)))).
    - exact (z_iso_inv (_ ,, Ha w)).
    - abstract
        (intro j ;
         unfold coprod_enriched_to_prod ; cbn ;
         refine (!_) ;
         apply (ProductPrCommutes _ _ _ (PV (λ j, E ⦃ D j , w ⦄)))).
  Defined.

  Section CoproductFromUnderlying.
    Context (PV : Products J V)
            (a : enriched_coprod_cocone)
            (coprod : isCoproduct J C D a (enriched_coprod_cocone_in a))
            (w : C).

    Definition coprod_from_underlying_arr_map
               (f : I_{V} --> PV (λ j, E ⦃ D j , w ⦄))
      : I_{V} --> E ⦃ a , w ⦄.
    Proof.
      apply enriched_from_arr.
      use (CoproductArrow _ _ (make_Coproduct _ _ _ _ _ coprod)).
      intro j.
      exact (enriched_to_arr E (f · ProductPr _ _ _ j)).
    Defined.

    Proposition coprod_from_underlying_arr_map_eq₁
                (f : I_{V} --> E ⦃ a , w ⦄)
      : coprod_from_underlying_arr_map (f · coprod_enriched_to_prod PV a w)
        =
        f.
    Proof.
      unfold coprod_from_underlying_arr_map.
      refine (_ @ enriched_from_to_arr E f).
      apply maponpaths.
      use (CoproductArrow_eq
             _ _ _
             (make_Coproduct _ _ _ _ _ coprod)).
      unfold coprod_enriched_to_prod.
      intro j.
      rewrite CoproductInCommutes ; cbn.
      rewrite (enriched_to_arr_comp E).
      apply maponpaths.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (ProductPrCommutes _ _ _ (PV (λ k, E ⦃ D k , w ⦄)) _ _ j).
      }
      unfold precomp_arr.
      rewrite !assoc.
      rewrite tensor_rinvunitor.
      rewrite mon_linvunitor_I_mon_rinvunitor_I.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split'.
      rewrite enriched_from_to_arr.
      apply idpath.
    Qed.

    Proposition coprod_from_underlying_arr_map_eq₂
                (f : I_{V} --> PV (λ j, E ⦃ D j , w ⦄))
      : coprod_from_underlying_arr_map f · coprod_enriched_to_prod PV a w
        =
        f.
    Proof.
      unfold coprod_from_underlying_arr_map.
      use (ProductArrow_eq
             _ _ _
             (PV (λ j, E ⦃ D j , w ⦄))).
      unfold coprod_enriched_to_prod.
      intro j.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (ProductPrCommutes _ _ _ (PV (λ k, E ⦃ D k , w ⦄)) _ _ j).
      }
      rewrite enriched_from_arr_precomp.
      refine (_ @ enriched_from_to_arr E _).
      apply maponpaths.
      apply (CoproductInCommutes _ _ _ (make_Coproduct _ _ _ _ _ coprod)).
    Qed.
  End CoproductFromUnderlying.

  Definition make_is_coprod_enriched_from_underlying
             (PV : Products J V)
             (a : enriched_coprod_cocone)
             (prod : isCoproduct
                       J C D
                       a
                       (enriched_coprod_cocone_in a))
             (HV : conservative_moncat V)
    : is_coprod_enriched a.
  Proof.
    use (make_is_coprod_enriched_from_z_iso PV).
    intros w.
    use HV.
    use isweq_iso.
    - exact (coprod_from_underlying_arr_map PV a prod w).
    - exact (coprod_from_underlying_arr_map_eq₁ PV a prod w).
    - exact (coprod_from_underlying_arr_map_eq₂ PV a prod w).
  Defined.

  (**
   6. Coproducts are closed under iso
   *)
  Section CoprodIso.
    Context (a : enriched_coprod_cocone)
            (Ha : is_coprod_enriched a)
            (b : C)
            (f : z_iso b a).

    Definition enriched_coprod_cocone_from_iso
      : enriched_coprod_cocone
      := make_enriched_coprod_cocone
           b
           (λ j, enriched_from_arr E (enriched_coprod_cocone_in a j · inv_from_z_iso f)).

    Definition is_coprod_enriched_from_iso
      : is_coprod_enriched enriched_coprod_cocone_from_iso.
    Proof.
      intros w.
      use (isProduct_z_iso _ _ _ _ (Ha w)).
      - exact (precomp_arr_z_iso E w f).
      - abstract
          (intro j ;
           cbn ;
           rewrite <- precomp_arr_comp ;
           apply maponpaths ;
           unfold enriched_coprod_cocone_from_iso ; cbn ;
           unfold  enriched_coprod_cocone_in ; cbn ;
           rewrite enriched_to_from_arr ;
           apply idpath).
    Defined.
  End CoprodIso.

  (**
   7. Coproducts are isomorphic
   *)
  Definition map_between_coproduct_enriched
             {a b : enriched_coprod_cocone}
             (Ha : is_coprod_enriched a)
             (Hb : is_coprod_enriched b)
    : b --> a
    := is_coprod_enriched_arrow
         Hb
         (enriched_coprod_cocone_in a).

  Lemma iso_between_coproduct_enriched_inv
        {a b : enriched_coprod_cocone}
        (Ha : is_coprod_enriched a)
        (Hb : is_coprod_enriched b)
    : map_between_coproduct_enriched Ha Hb · map_between_coproduct_enriched Hb Ha
      =
      identity _.
  Proof.
    unfold map_between_coproduct_enriched.
    use (is_coprod_enriched_arrow_eq Hb).
    intro j.
    rewrite !assoc.
    rewrite !is_coprod_enriched_arrow_in.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition iso_between_coproduct_enriched
             {a b : enriched_coprod_cocone}
             (Ha : is_coprod_enriched a)
             (Hb : is_coprod_enriched b)
    : z_iso a b.
  Proof.
    use make_z_iso.
    - exact (map_between_coproduct_enriched Hb Ha).
    - exact (map_between_coproduct_enriched Ha Hb).
    - split.
      + apply iso_between_coproduct_enriched_inv.
      + apply iso_between_coproduct_enriched_inv.
  Defined.
End EnrichedCoproducts.

(**
 8. Enriched categories with coproducts
 *)
Definition enrichment_coprod
           {V : monoidal_cat}
           {C : category}
           (E : enrichment C V)
           (J : UU)
  : UU
  := ∏ (D : J → C),
     ∑ (a : enriched_coprod_cocone E D),
     is_coprod_enriched E D a.

Proposition isaprop_enrichment_coprod
            {V : monoidal_cat}
            {C : category}
            (HC : is_univalent C)
            (E : enrichment C V)
            (J : UU)
  : isaprop (enrichment_coprod E J).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use funextsec ; intro D.
  use subtypePath.
  {
    intro.
    apply isaprop_is_coprod_enriched.
  }
  use total2_paths_f.
  - use (isotoid _ HC).
    use iso_between_coproduct_enriched.
    + exact (pr2 (φ₁ D)).
    + exact (pr2 (φ₂ D)).
  - rewrite transportf_sec_constant.
    use funextsec.
    intro j.
    rewrite transportf_enriched_arr_r.
    rewrite idtoiso_isotoid.
    cbn.
    refine (_ @ enriched_from_to_arr E _).
    apply maponpaths.
    unfold map_between_coproduct_enriched ; cbn.
    etrans.
    {
      apply is_coprod_enriched_arrow_in.
    }
    apply idpath.
Qed.

Definition cat_with_enrichment_coproduct
           (V : monoidal_cat)
           (J : UU)
  : UU
  := ∑ (C : cat_with_enrichment V), enrichment_coprod C J.

#[reversible=no] Coercion cat_with_enrichment_coproduct_to_cat_with_enrichment
         {V : monoidal_cat}
         {J : UU}
         (C : cat_with_enrichment_coproduct V J)
  : cat_with_enrichment V
  := pr1 C.

Definition coproducts_of_cat_with_enrichment
           {V : monoidal_cat}
           {J : UU}
           (C : cat_with_enrichment_coproduct V J)
  : enrichment_coprod C J
  := pr2 C.
