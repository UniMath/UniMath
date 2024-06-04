(*****************************************************************

 Powers in enriched categories

 Let `C` be a category enriched over `V`. If we have an object
 `x : C` and an object `v : V`, then the power `v ⋔ x` informally
 represents a `v`-indexed product of `x`. More precisely, the
 power satisfies the following universal property

   z --> v ⋔ x ≅ v ⊸ (z --> x)

 where `⊸` denotes the internal hom of `V`. If we look at
 categories enriched over sets, then the power is indeed such a
 product.

 Content
 1. Cones of powers
 2. Powers in an enriched category
 3. Being a power is a proposition
 4. Accessors for powers
 5. Builders for powers
 6. Powers are closed under iso
 7. Enriched categories with powers

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

Section EnrichedPowers.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V)
          (v : V)
          (x : C).

  (**
   1. Cones of powers
   *)
  Definition power_cone
    : UU
    := ∑ (a : C), v --> E ⦃ a , x ⦄.

  #[reversible=no] Coercion ob_power_cone
           (a : power_cone)
    : C
    := pr1 a.

  Definition power_cone_mor
             (a : power_cone)
    : v --> E ⦃ a , x ⦄
    := pr2 a.

  Definition make_power_cone
             (a : C)
             (f : v --> E ⦃ a , x ⦄)
    : power_cone
    := a ,, f.

  (**
   2. Powers in an enriched category
   *)
  Definition is_power_enriched_map
             (a : power_cone)
             (w : C)
    : E ⦃ w , a ⦄ --> v ⊸ (E ⦃ w , x ⦄)
    := internal_lam
         (identity _ #⊗ power_cone_mor a
          · sym_mon_braiding V _ _
          · enriched_comp E w a x).

  Definition is_power_enriched
             (a : power_cone)
    : UU
    := ∏ (w : C),
       is_z_isomorphism (is_power_enriched_map a w).

  Definition is_power_enriched_iso
             {a : power_cone}
             (Ha : is_power_enriched a)
             (w : C)
    : z_iso (E ⦃ w , a ⦄) (v ⊸ (E ⦃ w , x ⦄))
    := _ ,, Ha w.

  (**
   3. Being a power is a proposition
   *)
  Proposition isaprop_is_power_enriched
              (a : power_cone)
    : isaprop (is_power_enriched a).
  Proof.
    use impred ; intro.
    apply isaprop_is_z_isomorphism.
  Qed.

  (**
   4. Accessors for powers
   *)
  Section Accessors.
    Context {a : power_cone}
            (Ha : is_power_enriched a).

    Definition mor_to_power
               {w : V}
               {b : C}
               (f : w --> v ⊸ (E ⦃ b, x ⦄))
      : w --> E ⦃ b , a ⦄
      := f · inv_from_z_iso (is_power_enriched_iso Ha b).

    Proposition mor_to_power_commutes
                {w : V}
                {b : C}
                (f : w --> v ⊸ (E ⦃ b, x ⦄))
      : mor_to_power f · is_power_enriched_map a b
        =
        f.
    Proof.
      unfold mor_to_power.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      apply z_iso_after_z_iso_inv.
    Qed.

    Proposition mor_to_power_eq
                {w : V}
                {b : C}
                {f g : w --> E ⦃ b , a ⦄}
                (p : f · is_power_enriched_map a b
                     =
                     g · is_power_enriched_map a b)
      : f = g.
    Proof.
      use (cancel_z_iso _ _ (is_power_enriched_iso Ha _)).
      exact p.
    Qed.

    Definition arr_to_power
               {b : C}
               (f : I_{V} --> v ⊸ (E ⦃ b, x ⦄))
      : b --> a
      := enriched_to_arr E (mor_to_power f).

    Proposition arr_to_power_commutes
                {b : C}
                (f : I_{V} --> v ⊸ (E ⦃ b, x ⦄))
      : enriched_from_arr E (arr_to_power f) · is_power_enriched_map a b
        =
        f.
    Proof.
      unfold arr_to_power.
      rewrite enriched_from_to_arr.
      apply mor_to_power_commutes.
    Qed.

    Proposition arr_to_power_eq
                {b : C}
                {f g : b --> a}
                (p : enriched_from_arr E f · is_power_enriched_map a b
                     =
                     enriched_from_arr E g · is_power_enriched_map a b)
      : f = g.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use mor_to_power_eq.
      exact p.
    Qed.
  End Accessors.

  (**
   5. Builders for powers
   *)
  Definition make_is_power_enriched
             (a : power_cone)
             (p_map : ∏ (w : C), v ⊸ (E ⦃ w, x ⦄) --> E ⦃ w, a ⦄)
             (H₁ : ∏ (w : C), is_power_enriched_map a w · p_map w = identity _)
             (H₂ : ∏ (w : C), p_map w · is_power_enriched_map a w = identity _)
    : is_power_enriched a.
  Proof.
    intro w.
    use make_is_z_isomorphism.
    - exact (p_map w).
    - split.
      + exact (H₁ w).
      + exact (H₂ w).
  Defined.

  (**
   6. Powers are closed under iso
   *)
  Section PowerIso.
    Context (a : power_cone)
            (Ha : is_power_enriched a)
            (b : C)
            (f : z_iso b a).

    Definition power_cone_from_iso
      : power_cone.
    Proof.
      use make_power_cone.
      - exact b.
      - exact (power_cone_mor a · precomp_arr E x f).
    Defined.

    Definition is_power_enriched_from_iso
      : is_power_enriched power_cone_from_iso.
    Proof.
      intros w.
      refine (transportf
                is_z_isomorphism
                _
                (is_z_iso_comp_of_is_z_isos _ _ (postcomp_arr_is_z_iso E w _ (pr2 f)) (Ha w))).
      unfold postcomp_arr, is_power_enriched_map.
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
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite enrichment_assoc'.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        apply idpath.
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_id_id.
        rewrite tensor_rassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_rassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite tensor_split'.
        rewrite mon_inv_triangle.
        rewrite !assoc'.
        rewrite mon_lassociator_rassociator.
        rewrite id_right.
        apply idpath.
      }
      rewrite <- !tensor_comp_id_r.
      apply maponpaths_2.
      rewrite !assoc'.
      apply maponpaths.
      unfold precomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_rinvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_split.
      rewrite <- tensor_split'.
      apply idpath.
    Qed.
  End PowerIso.
End EnrichedPowers.

(**
 7. Enriched categories with powers
 *)
Definition enrichment_power
           {V : sym_mon_closed_cat}
           {C : category}
           (E : enrichment C V)
  : UU
  := ∏ (v : V) (x : C),
     ∑ (e : power_cone E v x),
     is_power_enriched E v x e.

Definition cat_with_enrichment_power
           (V : sym_mon_closed_cat)
  : UU
  := ∑ (C : cat_with_enrichment V), enrichment_power C.

#[reversible=no] Coercion cat_with_enrichment_power_to_cat_with_enrichment
         {V : sym_mon_closed_cat}
         (C : cat_with_enrichment_power V)
  : cat_with_enrichment V
  := pr1 C.

Definition powers_of_cat_with_enrichment
           {V : sym_mon_closed_cat}
           (C : cat_with_enrichment_power V)
  : enrichment_power C
  := pr2 C.
