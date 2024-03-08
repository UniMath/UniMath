(*****************************************************************

 Limits in enriched categories

 In this file, we define the notion of limit in enriched
 categories. Note that these limits refer to weighted limits
 rather than so-called conical limits, because the former is
 actually the correct notion of limit in this setting.

 Contents
 1. Cones of enriched limits
 2. Limits in an enriched category
 3. Being a limit is a proposition
 4. Instances of limits
 4.1. Powers as limits
 4.2. Conical limits as limits

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Limits.Ends.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedConicalLimits.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedPowers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.
Opaque sym_mon_braiding.

Section EnrichedLimit.
  Context {V : sym_mon_closed_cat}
          {I C : category}
          (E : enrichment C V)
          (D : I ⟶ C)
          (W : I ⟶ V).

  (**
   1. Cones of enriched limits
   *)
  Definition enriched_lim_cone
    : UU
    := ∑ (a : C),
       ∑ (fs : ∏ (i : I), W i --> E ⦃ a , D i ⦄),
       ∏ (i j : I)
         (f : i --> j),
       fs i · postcomp_arr E a (#D f)
       =
       #W f · fs j.

  #[reversible=no] Coercion ob_enriched_lim_cone
           (a : enriched_lim_cone)
    : C
    := pr1 a.

  Definition enriched_lim_cone_pr
             (a : enriched_lim_cone)
             (i : I)
    : W i --> E ⦃ a , D i ⦄
    := pr12 a i.

  Proposition enriched_lim_cone_commute
              (a : enriched_lim_cone)
              {i j : I}
              (f : i --> j)
    : enriched_lim_cone_pr a i · postcomp_arr E a (#D f)
      =
      #W f · enriched_lim_cone_pr a j.
  Proof.
    exact (pr22 a i j f).
  Qed.

  Definition make_enriched_lim_cone
             (a : C)
             (fs : ∏ (i : I), W i --> E ⦃ a , D i ⦄)
             (eqs : ∏ (i j : I)
                      (f : i --> j),
                    fs i · postcomp_arr E a (#D f)
                    =
                    #W f · fs j)
    : enriched_lim_cone
    := a ,, fs ,, eqs.

  (**
   2. Limits in an enriched category
   *)
  Definition weighted_hom_data
             (w : C)
    : functor_data (category_binproduct (I^opp) I) V.
  Proof.
    use make_functor_data.
    - exact (λ i, W (pr1 i) ⊸ (E ⦃ w , D (pr2 i) ⦄)).
    - exact (λ i j k,
             internal_pre_post_comp
               (#W (pr1 k))
               (postcomp_arr E w (#D (pr2 k)))).
  Defined.

  Proposition weighted_hom_is_functor
              (w : C)
    : is_functor (weighted_hom_data w).
  Proof.
    split.
    - intro i ; cbn.
      rewrite !functor_id.
      rewrite postcomp_arr_id.
      rewrite internal_pre_post_comp_id.
      apply idpath.
    - intros i j k f g ; cbn.
      rewrite !functor_comp.
      rewrite !postcomp_arr_comp.
      rewrite internal_pre_post_comp_comp.
      apply idpath.
  Qed.

  Definition weighted_hom
             (w : C)
    : category_binproduct (I^opp) I ⟶ V.
  Proof.
    use make_functor.
    - exact (weighted_hom_data w).
    - exact (weighted_hom_is_functor w).
  Defined.

  Definition is_lim_enriched_wedge_data
             (a : enriched_lim_cone)
             (w : C)
    : wedge_data (weighted_hom w).
  Proof.
    use make_wedge_data.
    - exact (E ⦃ w , a ⦄).
    - exact (λ i,
             internal_lam
               (identity _ #⊗ enriched_lim_cone_pr a i
                · sym_mon_braiding _ _ _
                · enriched_comp E _ _ _)).
  Defined.

  Proposition is_lim_enriched_is_wedge
              (a : enriched_lim_cone)
              (w : C)
    : is_wedge (weighted_hom w) (is_lim_enriched_wedge_data a w).
  Proof.
    intros i j g ; cbn -[sym_mon_braiding].
    rewrite !functor_id.
    rewrite postcomp_arr_id.
    use internal_funext.
    intros z h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_pre_post_comp.
    rewrite !internal_beta.
    rewrite !tensor_id_id.
    rewrite id_left, id_right.
    rewrite !assoc.
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    rewrite internal_beta.
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    rewrite tensor_sym_mon_braiding.
    rewrite !assoc'.
    rewrite enriched_comp_postcomp_arr.
    rewrite !(maponpaths (λ z, _ · (_ · z)) (assoc _ _ _)).
    rewrite <- tensor_comp_id_r.
    rewrite enriched_lim_cone_commute.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    rewrite <- tensor_sym_mon_braiding.
    rewrite !assoc.
    refine (!_).
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    rewrite tensor_split.
    rewrite tensor_comp_id_l.
    rewrite !assoc'.
    apply maponpaths.
    rewrite internal_beta.
    rewrite tensor_split.
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite !assoc.
    rewrite tensor_sym_mon_braiding.
    apply idpath.
  Qed.

  Definition is_lim_enriched_wedge
             (a : enriched_lim_cone)
             (w : C)
    : wedge (weighted_hom w).
  Proof.
    use make_wedge.
    - exact (is_lim_enriched_wedge_data a w).
    - exact (is_lim_enriched_is_wedge a w).
  Defined.

  Definition is_lim_enriched
             (a : enriched_lim_cone)
    : UU
    := ∏ (w : C),
       is_end (weighted_hom w) (is_lim_enriched_wedge a w).

  Definition lim_enriched
    : UU
    := ∑ (a : enriched_lim_cone),
       is_lim_enriched a.

  #[reversible=no] Coercion cone_of_lim_enriched
           (a : lim_enriched)
    : enriched_lim_cone
    := pr1 a.

  Definition enriched_lim_cone_is_lim
             (a : lim_enriched)
    : is_lim_enriched a
    := pr2 a.

  (**
   3. Being a limit is a proposition
   *)
  Proposition isaprop_is_lim_enriched
              (a : enriched_lim_cone)
    : isaprop (is_lim_enriched a).
  Proof.
    repeat (use impred ; intro).
    apply isapropiscontr.
  Qed.
End EnrichedLimit.

(**
 4. Instances of limits
 *)

(**
 4.1. Powers as limits
 *)
Section LimitToPower.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V)
          (v : V)
          (x : C).

  Let I : category := unit_category.
  Let D : I ⟶ C := constant_functor _ _ x.
  Let W : I ⟶ V := constant_functor _ _ v.

  Context (a : lim_enriched E D W).

  Definition power_from_lim_cone
    : power_cone E v x.
  Proof.
    use make_power_cone.
    - exact a.
    - exact (enriched_lim_cone_pr _ _ _ a tt).
  Defined.

  Section PowerUMP.
    Context (w : C).

    Definition power_from_lim_wedge_data
      : wedge_data (weighted_hom E D W w).
    Proof.
      use make_wedge_data ; cbn.
      - exact (v ⊸ (E ⦃ w, x ⦄)).
      - exact (λ _, identity _).
    Defined.

    Proposition power_from_lim_is_wedge
      : is_wedge (weighted_hom E D W w) power_from_lim_wedge_data.
    Proof.
      intros i j k.
      apply idpath.
    Qed.

    Definition power_from_lim_wedge
      : wedge (weighted_hom E D W w).
    Proof.
      use make_wedge.
      - exact power_from_lim_wedge_data.
      - exact power_from_lim_is_wedge.
    Defined.

    Proposition power_from_lim_wedge_inv_1
      : is_power_enriched_map E v x power_from_lim_cone w
        · mor_to_end
            (weighted_hom E D W w)
            (enriched_lim_cone_is_lim E _ _ a w)
            power_from_lim_wedge
        =
        identity _.
    Proof.
      use (mor_to_end_eq _ (pr2 a w)).
      intro i.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (mor_to_end_comm _ (pr2 a w) power_from_lim_wedge i).
      }
      refine (id_right _ @ _ @ !(id_left _)).
      use internal_funext.
      intros z h.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold is_power_enriched_map.
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply internal_beta.
      }
      rewrite !assoc.
      induction i.
      apply idpath.
    Qed.

    Proposition power_from_lim_wedge_inv_2
      : mor_to_end (weighted_hom E D W w) (pr2 a w) power_from_lim_wedge
        · is_power_enriched_map E v x power_from_lim_cone w
        =
        identity _.
    Proof.
      exact (mor_to_end_comm (weighted_hom E D W w) (pr2 a w) power_from_lim_wedge tt).
    Qed.
  End PowerUMP.

  Definition is_power_enriched_from_lim_cone
    : is_power_enriched _ _ _ power_from_lim_cone.
  Proof.
    use make_is_power_enriched.
    - exact (λ w, mor_to_end _ (pr2 a w) (power_from_lim_wedge w)).
    - exact power_from_lim_wedge_inv_1.
    - exact power_from_lim_wedge_inv_2.
  Defined.
End LimitToPower.

(**
 4.2. Conical limits as limits
 *)
Section LimitToConical.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V)
          {I : category}
          (D : I ⟶ C).

  Let W : I ⟶ V := constant_functor _ _ I_{V}.

  Context (a : lim_enriched E D W).

  Definition enriched_weighted_to_conical_cone
    : enriched_conical_lim_cone D.
  Proof.
    use make_enriched_conical_lim_cone.
    - exact a.
    - exact (λ i, enriched_to_arr E (enriched_lim_cone_pr _ _ _ a i)).
    - abstract
        (intros i j f ; cbn ;
         use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn ;
         rewrite enriched_from_to_arr ;
         pose (enriched_lim_cone_commute _ _ _ a f) as p ;
         cbn in p ;
         rewrite id_left in p ;
         rewrite <- p ;
         rewrite enriched_from_arr_comp ;
         rewrite enriched_from_to_arr ;
         rewrite tensor_split ;
         rewrite !assoc ;
         rewrite <- tensor_linvunitor ;
         rewrite !assoc' ;
         apply maponpaths ;
         rewrite !assoc ;
         apply idpath).
  Defined.

  Section ConicalLimUMP.
    Context {w : C}
            (v : V)
            (fs : ∏ (i : I), v --> E ⦃ w, D i ⦄)
            (ps : ∏ (i j : I) (k : i --> j), fs i · postcomp_arr E w (#D k) = fs j).

    Proposition enriched_weighted_to_conical_is_conical_lim_unique
      : isaprop
          (∑ (g : v --> E ⦃ w, a ⦄),
           ∏ (i : I),
           g · postcomp_arr E w (enriched_to_arr E (enriched_lim_cone_pr E D W a i))
           =
           fs i).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        use impred ; intro.
        apply homset_property.
      }
      use (mor_to_end_eq _ (pr2 a w)).
      intros i ; cbn.
      use internal_funext.
      intros z h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite !internal_beta.
      rewrite !assoc.
      rewrite <- !tensor_comp_mor.
      rewrite !id_right.
      rewrite !tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !tensor_comp_r_id_l.
      rewrite !assoc'.
      apply maponpaths.
      pose (p := maponpaths (λ z, mon_lunitor _ · z) (pr2 φ₁ i @ !(pr2 φ₂ i))).
      cbn in p.
      unfold postcomp_arr in p.
      rewrite !enriched_from_to_arr in p.
      rewrite !assoc' in p.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)) in p.
      rewrite !tensor_linvunitor in p.
      rewrite !assoc in p.
      rewrite !mon_lunitor_linvunitor in p.
      rewrite !id_left in p.
      rewrite <- !tensor_split in p.
      exact p.
    Qed.

    Definition enriched_weighted_to_conical_is_conical_lim_wedge_data
      : wedge_data (weighted_hom E D W w).
    Proof.
      use make_wedge_data.
      - exact v.
      - exact (λ i, internal_lam (mon_runitor _ · fs i)).
    Defined.

    Proposition enriched_weighted_to_conical_is_conical_lim_is_wedge
      : is_wedge
          (weighted_hom E D W w)
          enriched_weighted_to_conical_is_conical_lim_wedge_data.
    Proof.
      intros i j f ; cbn.
      use internal_funext.
      intros z h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_pre_post_comp.
      rewrite !internal_beta.
      rewrite functor_id.
      rewrite postcomp_arr_id.
      rewrite id_right.
      rewrite !tensor_id_id.
      rewrite !id_left.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite internal_beta.
      rewrite !assoc'.
      do 2 apply maponpaths.
      refine (!_).
      apply ps.
    Qed.

    Definition enriched_weighted_to_conical_is_conical_lim_wedge
      : wedge (weighted_hom E D W w).
    Proof.
      use make_wedge.
      - exact enriched_weighted_to_conical_is_conical_lim_wedge_data.
      - exact enriched_weighted_to_conical_is_conical_lim_is_wedge.
    Defined.

    Definition enriched_weighted_to_conical_is_conical_lim_mor
      : v --> E ⦃ w, a ⦄
      := mor_to_end
           _
           (pr2 a w)
           enriched_weighted_to_conical_is_conical_lim_wedge.

    Proposition enriched_weighted_to_conical_is_conical_lim_mor_eq
                (i : I)
      : enriched_weighted_to_conical_is_conical_lim_mor
        · postcomp_arr E w (enriched_to_arr E (enriched_lim_cone_pr E D W a i))
        =
        fs i.
    Proof.
      pose (maponpaths
              (λ z, z #⊗ identity _ · internal_eval _ _)
              (mor_to_end_comm
                 _
                 (pr2 a w)
                 enriched_weighted_to_conical_is_conical_lim_wedge
                 i))
        as p.
      cbn in p.
      rewrite tensor_comp_id_r in p.
      rewrite !assoc' in p.
      rewrite !internal_beta in p.
      rewrite !assoc in p.
      rewrite <- tensor_split' in p.
      rewrite tensor_sym_mon_braiding in p.
      refine (_ @ id_left _).
      rewrite <- mon_rinvunitor_runitor.
      rewrite !assoc'.
      rewrite <- p.
      unfold postcomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_linvunitor.
      rewrite sym_mon_braiding_rinvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_split.
      rewrite enriched_from_to_arr.
      apply idpath.
    Qed.
  End ConicalLimUMP.

  Definition enriched_weighted_to_conical_is_conical_lim
    : is_conical_lim_enriched E D enriched_weighted_to_conical_cone.
  Proof.
    intros w v cc.
    use iscontraprop1.
    - exact (enriched_weighted_to_conical_is_conical_lim_unique v (pr1 cc)).
    - refine (enriched_weighted_to_conical_is_conical_lim_mor v (pr1 cc) (pr2 cc)
              ,,
              _).
      intros i.
      exact (enriched_weighted_to_conical_is_conical_lim_mor_eq v (pr1 cc) (pr2 cc) i).
  Defined.
End LimitToConical.
