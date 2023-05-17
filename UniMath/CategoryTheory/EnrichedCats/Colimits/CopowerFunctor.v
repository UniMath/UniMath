(**********************************************************************

 Functoriality of copowers

 In this file, we show that the copower is functorial. In addition, we
 prove various useful lemmas.

 Contents
 1. Action on objects
 2. Precomposition with copower functions
 3. Action on morphisms
 4. Enriched action on morphisms
 5. Functoriality
 6. Copowers on morphism objects

 **********************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.

Import MonoidalNotations.
Local Open Scope moncat.
Local Open Scope cat.

Section CopowerFunctor.
  Context {V : sym_mon_closed_cat}
          {C : category}
          {EC : enrichment C V}
          (copowC : enrichment_copower EC).

  (**
   1. Action on objects
   *)
  Definition copow_ob
             (v : V)
             (r : C)
    : C
    := pr1 (copowC v r).

  Definition mor_of_copow_ob
             (v : V)
             (r : C)
    : v --> EC ⦃ r , copow_ob v r ⦄
    := copower_cocone_mor _ _ _ (pr1 (copowC v r)).

  (**
   2. Precomposition with copower functions
   *)
  Proposition arr_to_copower_precomp
              {v : V}
              {x y r : C}
              (f : I_{ V} --> v ⊸ (EC ⦃ r , x ⦄))
              (g : x --> y)
    : arr_to_copower _ _ _ (pr2 (copowC v r)) f · g
      =
      arr_to_copower
        _ _ _
        (pr2 (copowC v r))
        (f · internal_postcomp _ (postcomp_arr EC r g)).
  Proof.
    use arr_to_copower_eq.
    {
      exact (pr2 (copowC v r)).
    }
    refine (!_).
    etrans.
    {
      apply arr_to_copower_commutes.
    }
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_postcomp, is_copower_enriched_map.
    rewrite !internal_beta.
    rewrite tensor_split.
    refine (!_).
    etrans.
    {
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite tensor_comp_l_id_l.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite enriched_from_arr_comp.
    rewrite !assoc.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite enrichment_assoc.
    unfold postcomp_arr.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      do 4 apply maponpaths_2.
      exact (!(arr_to_copower_commutes EC _ _ (pr2 (copowC v r)) f)).
    }
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      unfold is_copower_enriched_map.
      rewrite internal_beta.
      apply idpath.
    }
    rewrite !assoc.
    rewrite <- tensor_split'.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_lassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite mon_linvunitor_triangle.
      rewrite tensor_linvunitor.
      apply idpath.
    }
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc'.
      rewrite tensor_comp_l_id_r.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite <- !tensor_comp_mor.
    rewrite id_left, !id_right.
    apply idpath.
  Qed.

  (**
   3. Action on morphisms
   *)
  Definition copow_mor
             {v₁ v₂ : V}
             (f : v₁ --> v₂)
             (r : C)
    : copow_ob v₁ r --> copow_ob v₂ r.
  Proof.
    use arr_to_copower.
    {
      exact (pr2 (copowC v₁ r)).
    }
    exact (internal_lam (mon_lunitor _ · f · mor_of_copow_ob v₂ r)).
  Defined.

  Proposition copow_mor_commute
              {v₁ v₂ : V}
              (f : v₁ --> v₂)
              (r : C)
    : enriched_from_arr EC (copow_mor f r) · is_copower_enriched_map EC v₁ r _ _
      =
      internal_lam (mon_lunitor _ · f · mor_of_copow_ob v₂ r).
  Proof.
    apply arr_to_copower_commutes.
  Qed.

  (**
   4. Enriched action on morphisms
   *)
  Definition copow_enriched_mor
             (v₁ v₂ : V)
             (r : C)
    : v₁ ⊸ v₂ --> EC ⦃ copow_ob v₁ r , copow_ob v₂ r ⦄.
  Proof.
    use mor_to_copower.
    {
      exact (pr2 (copowC v₁ r)).
    }
    use internal_postcomp.
    apply mor_of_copow_ob.
  Defined.

  Proposition copow_enriched_mor_commute
              (v₁ v₂ : V)
              (r : C)
    : (copow_enriched_mor v₁ v₂ r · is_copower_enriched_map EC v₁ r _ _) #⊗ identity v₁
      · internal_eval v₁ _
      =
      internal_eval v₁ v₂ · mor_of_copow_ob v₂ r.
  Proof.
    pose (maponpaths
            (λ z, z #⊗ identity _ · internal_eval _ _)
            (mor_to_copower_commutes
               EC
               v₁ r
               (pr2 (copowC v₁ r))
               (internal_postcomp _ (mor_of_copow_ob v₂ r))))
      as p.
    cbn in p.
    unfold internal_postcomp in p.
    rewrite !internal_beta in p.
    exact p.
  Qed.

  (**
   5. Functoriality
   *)
  Proposition copow_id_mor
              (v : V)
              (r : C)
    : copow_mor (identity v) r = identity _.
  Proof.
    use arr_to_copower_eq.
    {
      exact (pr2 (copowC v r)).
    }
    refine (copow_mor_commute (identity v) r @ _).
    rewrite enriched_from_arr_id.
    unfold is_copower_enriched_map.
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite !internal_beta.
    rewrite id_left.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite <- enrichment_id_left.
    rewrite tensor_lunitor.
    apply idpath.
  Qed.

  Proposition copow_comp_mor
              {v₁ v₂ v₃ : V}
              (f : v₁ --> v₂)
              (g : v₂ --> v₃)
              (r : C)
    : copow_mor (f · g) r
      =
      copow_mor f r · copow_mor g r.
  Proof.
    use arr_to_copower_eq.
    {
      exact (pr2 (copowC v₁ r)).
    }
    refine (copow_mor_commute (f · g) r @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply arr_to_copower_precomp.
    }
    etrans.
    {
      apply arr_to_copower_commutes.
    }
    use internal_funext.
    intros a h.
    rewrite !tensor_comp_r_id_r.
    rewrite tensor_split.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    unfold internal_postcomp.
    rewrite !internal_beta.
    rewrite !assoc.
    rewrite !internal_beta.
    rewrite !assoc'.
    do 2 apply maponpaths.
    pose (maponpaths
            (λ z, z #⊗ identity _ · internal_eval _ _)
            (copow_mor_commute g r))
      as p.
    cbn in p.
    rewrite !tensor_comp_r_id_r in p.
    rewrite !assoc' in p.
    unfold is_copower_enriched_map in p.
    rewrite !internal_beta in p.
    rewrite !assoc in p.
    rewrite <- tensor_split' in p.
    refine (!(id_left _) @ _).
    rewrite <- mon_linvunitor_lunitor.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      exact (!p).
    }
    unfold postcomp_arr.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite tensor_linvunitor.
    rewrite !assoc'.
    apply maponpaths.
    rewrite <- tensor_split.
    apply idpath.
  Qed.

  (**
   6. Copowers on morphism objects
   *)
  Definition copow_on_enriched_mor
             (r₁ r₂ : C)
    : copow_ob (EC ⦃ r₁ , r₂ ⦄) r₁ --> r₂.
  Proof.
    use arr_to_copower.
    {
      exact (pr2 (copowC _ _)).
    }
    exact (internal_from_arr (identity _)).
  Defined.

  Proposition copow_on_enriched_mor_commute
              (r₁ r₂ : C)
    : (enriched_from_arr EC (copow_on_enriched_mor r₁ r₂)
       · is_copower_enriched_map EC _ _ _ _) #⊗ identity _
      · internal_eval _ _
      =
      mon_lunitor _.
  Proof.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply arr_to_copower_commutes.
    }
    unfold internal_from_arr.
    rewrite internal_beta.
    apply id_right.
  Qed.

  Proposition precomp_copow_on_enriched_mor_commute
              (x r₁ r₂ : C)
    : (precomp_arr EC x (copow_on_enriched_mor r₁ r₂)
       · is_copower_enriched_map EC _ _ _ _) #⊗ identity _
      · internal_eval _ _
      =
      enriched_comp EC r₁ r₂ x.
  Proof.
    rewrite !tensor_comp_r_id_r.
    unfold is_copower_enriched_map.
    rewrite !assoc'.
    rewrite internal_beta.
    rewrite !assoc.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    unfold precomp_arr.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite enrichment_assoc.
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite tensor_lassociator.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- mon_inv_triangle.
      apply idpath.
    }
    rewrite <- !tensor_comp_id_l.
    rewrite <- tensor_id_id.
    apply maponpaths.
    rewrite tensor_linvunitor.
    refine (_ @ mon_linvunitor_lunitor _).
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ copow_on_enriched_mor_commute _ _).
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold is_copower_enriched_map.
    rewrite internal_beta.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_split.
    rewrite <- tensor_split'.
    apply idpath.
  Qed.
End CopowerFunctor.
