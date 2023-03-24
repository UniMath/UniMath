(*****************************************************************

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.

Import MonoidalNotations.
Local Open Scope cat.
Local Open Scope moncat.

Opaque sym_mon_braiding.

Section EnrichedCopowers.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V)
          (v : V)
          (x : C).

  (**
   1. Cones of copowers
   *)
  Definition copower_cocone
    : UU
    := ∑ (a : C), v --> E ⦃ x , a ⦄.

  Coercion ob_copower_cocone
           (a : copower_cocone)
    : C
    := pr1 a.

  Definition copower_cocone_mor
             (a : copower_cocone)
    : v --> E ⦃ x , a ⦄
    := pr2 a.

  Definition make_copower_cocone
             (a : C)
             (f : v --> E ⦃ x , a ⦄)
    : copower_cocone
    := a ,, f.

  (**
   2. Copowers in an enriched category
   *)
  Definition is_copower_enriched_map
             (a : copower_cocone)
             (w : C)
    : E ⦃ a , w ⦄ --> v ⊸ (E ⦃ x , w ⦄)
    := internal_lam
         (identity _ #⊗ copower_cocone_mor a
          · enriched_comp E  _ _ _).

  Definition is_copower_enriched
             (a : copower_cocone)
    : UU
    := ∏ (w : C),
       is_z_isomorphism (is_copower_enriched_map a w).

  Definition is_copower_enriched_iso
             {a : copower_cocone}
             (Ha : is_copower_enriched a)
             (w : C)
    : z_iso (E ⦃ a , w ⦄) (v ⊸ (E ⦃ x , w ⦄))
    := _ ,, Ha w.

  (**
   3. Being aco power is a proposition
   *)
  Proposition isaprop_is_copower_enriched
              (a : copower_cocone)
    : isaprop (is_copower_enriched a).
  Proof.
    use impred ; intro.
    apply isaprop_is_z_isomorphism.
  Qed.

  (**
   4. Accessors for copowers
   *)
  Section Accessors.
    Context {a : copower_cocone}
            (Ha : is_copower_enriched a).

    Definition mor_to_copower
               {w : V}
               {b : C}
               (f : w --> v ⊸ (E ⦃ x , b ⦄))
      : w --> E ⦃ a , b ⦄
      := f · inv_from_z_iso (is_copower_enriched_iso Ha b).

    Proposition mor_to_copower_commutes
                {w : V}
                {b : C}
                (f : w --> v ⊸ (E ⦃ x , b ⦄))
      : mor_to_copower f · is_copower_enriched_map a b
        =
        f.
    Proof.
      unfold mor_to_copower.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      apply z_iso_after_z_iso_inv.
    Qed.

    Proposition mor_to_copower_eq
                {w : V}
                {b : C}
                {f g : w --> E ⦃ a , b ⦄}
                (p : f · is_copower_enriched_map a b
                     =
                     g · is_copower_enriched_map a b)
      : f = g.
    Proof.
      use (cancel_z_iso _ _ (is_copower_enriched_iso Ha _)).
      exact p.
    Qed.

    Definition arr_to_copower
               {b : C}
               (f : I_{V} --> v ⊸ (E ⦃ x , b ⦄))
      : a --> b
      := enriched_to_arr E (mor_to_copower f).

    Proposition arr_to_copower_commutes
                {b : C}
                (f : I_{V} --> v ⊸ (E ⦃ x , b ⦄))
      : enriched_from_arr E (arr_to_copower f) · is_copower_enriched_map a b
        =
        f.
    Proof.
      unfold arr_to_copower.
      rewrite enriched_from_to_arr.
      apply mor_to_copower_commutes.
    Qed.

    Proposition arr_to_copower_eq
                {b : C}
                {f g : a --> b}
                (p : enriched_from_arr E f · is_copower_enriched_map a b
                     =
                     enriched_from_arr E g · is_copower_enriched_map a b)
      : f = g.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use mor_to_copower_eq.
      exact p.
    Qed.
  End Accessors.

  (**
   5. Builders for copowers
   *)
  Definition make_is_copower_enriched
             (a : copower_cocone)
             (p_map : ∏ (w : C), v ⊸ (E ⦃ x , w ⦄) --> E ⦃ a , w ⦄)
             (H₁ : ∏ (w : C), is_copower_enriched_map a w · p_map w = identity _)
             (H₂ : ∏ (w : C), p_map w · is_copower_enriched_map a w = identity _)
    : is_copower_enriched a.
  Proof.
    intro w.
    use make_is_z_isomorphism.
    - exact (p_map w).
    - split.
      + exact (H₁ w).
      + exact (H₂ w).
  Defined.

  (**
   6. Copowers are closed under iso
   *)
  Section CopowerIso.
    Context (a : copower_cocone)
            (Ha : is_copower_enriched a)
            (b : C)
            (f : z_iso a b).

    Definition copower_cocone_from_iso
      : copower_cocone.
    Proof.
      use make_copower_cocone.
      - exact b.
      - exact (copower_cocone_mor a · postcomp_arr E x f).
    Defined.

    Definition is_copower_enriched_from_iso
      : is_copower_enriched copower_cocone_from_iso.
    Proof.
      intros w.
      refine (transportf
                is_z_isomorphism
                _
                (is_z_iso_comp_of_is_z_isos _ _ (precomp_arr_is_z_iso E w _ (pr2 f)) (Ha w))).
      unfold precomp_arr, is_copower_enriched_map.
      cbn.
      use internal_funext.
      intros z h.
      rewrite !tensor_comp_r_id_r.
      refine (!_).
      etrans.
      {
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite !internal_beta.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        apply maponpaths.
        rewrite enrichment_assoc.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite <- tensor_id_id.
        rewrite !assoc'.
        rewrite tensor_lassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_lassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite <- mon_inv_triangle.
        apply idpath.
      }
      rewrite <- !tensor_comp_id_l.
      apply maponpaths.
      rewrite !assoc'.
      apply maponpaths.
      unfold postcomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- !tensor_split.
      rewrite <- !tensor_split'.
      apply idpath.
    Qed.
  End CopowerIso.
End EnrichedCopowers.

(**
 6. Enriched categories with copowers
 *)
Definition enrichment_copower
           {V : sym_mon_closed_cat}
           {C : category}
           (E : enrichment C V)
  : UU
  := ∏ (v : V) (x : C),
     ∑ (e : copower_cocone E v x),
     is_copower_enriched E v x e.

Definition cat_with_enrichment_copower
           (V : sym_mon_closed_cat)
  : UU
  := ∑ (C : cat_with_enrichment V), enrichment_copower C.

Coercion cat_with_enrichment_copower_to_cat_with_enrichment
         {V : sym_mon_closed_cat}
         (C : cat_with_enrichment_copower V)
  : cat_with_enrichment V
  := pr1 C.

Definition copowers_of_cat_with_enrichment
           {V : sym_mon_closed_cat}
           (C : cat_with_enrichment_copower V)
  : enrichment_copower C
  := pr2 C.
