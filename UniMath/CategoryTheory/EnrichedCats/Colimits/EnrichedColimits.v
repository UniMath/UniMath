(*****************************************************************

 Colimits in enriched categories

 In this file, we define the notion of colimit in enriched
 categories. Note that these limits refer to weighted colimits
 rather than so-called conical colimits, because the former is
 actually the correct notion of colimit in this setting.

 Contents
 1. Cocones of enriched colimits
 2. Colimits in an enriched category
 3. Being a colimit is a proposition
 4. Instances of colimits
 4.1. Copowers as colimits
 4.2. Conical colimits as colimits

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
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedConicalColimits.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.
Opaque sym_mon_braiding.

Section EnrichedColimit.
  Context {V : sym_mon_closed_cat}
          {I C : category}
          (E : enrichment C V)
          (D : I ⟶ C)
          (W : I^opp ⟶ V).

  (**
   1. Coones of enriched colimits
   *)
  Definition enriched_colim_cocone
    : UU
    := ∑ (a : C),
       ∑ (fs : ∏ (i : I), W i --> E ⦃ D i , a ⦄),
       ∏ (i j : I)
         (f : j --> i),
       fs i · precomp_arr E a (#D f)
       =
       #W f · fs j.

  #[reversible=no] Coercion ob_enriched_colim_cocone
           (a : enriched_colim_cocone)
    : C
    := pr1 a.

  Definition enriched_colim_cocone_in
             (a : enriched_colim_cocone)
             (i : I)
    : W i --> E ⦃ D i , a ⦄
    := pr12 a i.

  Proposition enriched_colim_cocone_commute
              (a : enriched_colim_cocone)
              {i j : I}
              (f : j --> i)
    : enriched_colim_cocone_in a i · precomp_arr E a (#D f)
      =
      #W f · enriched_colim_cocone_in a j.
  Proof.
    exact (pr22 a i j f).
  Qed.

  Definition make_enriched_colim_cocone
             (a : C)
             (fs : ∏ (i : I), W i --> E ⦃ D i , a ⦄)
             (eqs : ∏ (i j : I)
                      (f : j --> i),
                    fs i · precomp_arr E a (#D f)
                    =
                    #W f · fs j)
    : enriched_colim_cocone
    := a ,, fs ,, eqs.

  (**
   2. Colimits in an enriched category
   *)
  Definition weighted_hom_co_data
             (w : C)
    : functor_data (category_binproduct (I^opp) I) V.
  Proof.
    use make_functor_data.
    - exact (λ i, W (pr2 i) ⊸ (E ⦃ D (pr1 i) , w ⦄)).
    - exact (λ i j k,
             internal_pre_post_comp
               (#W (pr2 k))
               (precomp_arr E w (#D (pr1 k)))).
  Defined.

  Proposition weighted_hom_co_is_functor
              (w : C)
    : is_functor (weighted_hom_co_data w).
  Proof.
    split.
    - intro i ; cbn.
      rewrite !functor_id.
      rewrite precomp_arr_id.
      rewrite (functor_id W).
      rewrite internal_pre_post_comp_id.
      apply idpath.
    - intros i j k f g ; cbn.
      refine (_ @ internal_pre_post_comp_comp _ _ _ _).
      rewrite !functor_comp.
      rewrite !precomp_arr_comp.
      pose (functor_comp W (pr2 g) (pr2 f)) as p.
      cbn in p.
      rewrite p.
      apply idpath.
  Qed.

  Definition weighted_hom_co
             (w : C)
    : category_binproduct (I^opp) I ⟶ V.
  Proof.
    use make_functor.
    - exact (weighted_hom_co_data w).
    - exact (weighted_hom_co_is_functor w).
  Defined.

  Definition is_colim_enriched_wedge_data
             (a : enriched_colim_cocone)
             (w : C)
    : wedge_data (weighted_hom_co w).
  Proof.
    use make_wedge_data.
    - exact (E ⦃ a , w ⦄).
    - exact (λ i,
             internal_lam
               (identity _ #⊗ enriched_colim_cocone_in a i
                · enriched_comp E _ _ _)).
  Defined.

  Proposition is_colim_enriched_is_wedge
              (a : enriched_colim_cocone)
              (w : C)
    : is_wedge (weighted_hom_co w) (is_colim_enriched_wedge_data a w).
  Proof.
    intros i j g ; cbn.
    rewrite !functor_id.
    rewrite (functor_id W).
    rewrite precomp_arr_id.
    use internal_funext.
    intros z h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_pre_post_comp.
    rewrite !internal_beta.
    rewrite !tensor_id_id.
    rewrite id_left, id_right.
    rewrite !assoc.
    rewrite <- tensor_comp_mor.
    rewrite id_right.
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite internal_beta.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    rewrite internal_beta.
    rewrite tensor_comp_id_l.
    rewrite !assoc'.
    apply maponpaths.
    rewrite enriched_comp_precomp_arr.
    rewrite !assoc.
    rewrite <- !tensor_comp_id_l.
    apply maponpaths_2.
    apply maponpaths.
    apply enriched_colim_cocone_commute.
  Qed.

  Definition is_colim_enriched_wedge
             (a : enriched_colim_cocone)
             (w : C)
    : wedge (weighted_hom_co w).
  Proof.
    use make_wedge.
    - exact (is_colim_enriched_wedge_data a w).
    - exact (is_colim_enriched_is_wedge a w).
  Defined.

  Definition is_colim_enriched
             (a : enriched_colim_cocone)
    : UU
    := ∏ (w : C),
       is_end (weighted_hom_co w) (is_colim_enriched_wedge a w).

  Definition colim_enriched
    : UU
    := ∑ (a : enriched_colim_cocone),
       is_colim_enriched a.

  #[reversible=no] Coercion cocone_of_colim_enriched
           (a : colim_enriched)
    : enriched_colim_cocone
    := pr1 a.

  Definition enriched_colim_cocone_is_colim
             (a : colim_enriched)
    : is_colim_enriched a
    := pr2 a.

  (**
   3. Being a colimit is a proposition
   *)
  Proposition isaprop_is_colim_enriched
              (a : enriched_colim_cocone)
    : isaprop (is_colim_enriched a).
  Proof.
    repeat (use impred ; intro).
    apply isapropiscontr.
  Qed.
End EnrichedColimit.

(**
 4. Instances of colimits
 *)

(**
 4.1. Copowers as colimits
 *)
Section ColimitToCopower.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V)
          (v : V)
          (x : C).

  Let I : category := unit_category.
  Let D : I ⟶ C := constant_functor _ _ x.
  Let W : I^opp ⟶ V := constant_functor _ _ v.

  Context (a : colim_enriched E D W).

  Definition copower_from_colim_cocone
    : copower_cocone E v x.
  Proof.
    use make_copower_cocone.
    - exact a.
    - exact (enriched_colim_cocone_in _ _ _ a tt).
  Defined.

  Section CopowerUMP.
    Context (w : C).

    Definition copower_from_colim_wedge_data
      : wedge_data (weighted_hom_co E D W w).
    Proof.
      use make_wedge_data ; cbn.
      - exact (v ⊸ (E ⦃ x , w ⦄)).
      - exact (λ _, identity _).
    Defined.

    Proposition copower_from_colim_is_wedge
      : is_wedge (weighted_hom_co E D W w) copower_from_colim_wedge_data.
    Proof.
      intros i j k.
      apply idpath.
    Qed.

    Definition copower_from_colim_wedge
      : wedge (weighted_hom_co E D W w).
    Proof.
      use make_wedge.
      - exact copower_from_colim_wedge_data.
      - exact copower_from_colim_is_wedge.
    Defined.

    Proposition copower_from_colim_wedge_inv_1
      : is_copower_enriched_map E v x copower_from_colim_cocone w
        · mor_to_end (weighted_hom_co E D W w) (pr2 a w) copower_from_colim_wedge
        =
        identity _.
    Proof.
      use (mor_to_end_eq _ (pr2 a w)).
      intro i.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (mor_to_end_comm _ (pr2 a w) copower_from_colim_wedge i).
      }
      refine (id_right _ @ _ @ !(id_left _)).
      use internal_funext.
      intros z h.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold is_copower_enriched_map.
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply internal_beta.
      }
      induction i.
      apply idpath.
    Qed.

    Proposition copower_from_colim_wedge_inv_2
      : mor_to_end (weighted_hom_co E D W w) (pr2 a w) copower_from_colim_wedge
        · is_copower_enriched_map E v x copower_from_colim_cocone w
        =
        identity _.
    Proof.
      exact (mor_to_end_comm (weighted_hom_co E D W w) (pr2 a w) copower_from_colim_wedge tt).
    Qed.
  End CopowerUMP.

  Definition is_copower_enriched_from_colim_cone
    : is_copower_enriched _ _ _ copower_from_colim_cocone.
  Proof.
    use make_is_copower_enriched.
    - exact (λ w, mor_to_end _ (pr2 a w) (copower_from_colim_wedge w)).
    - exact copower_from_colim_wedge_inv_1.
    - exact copower_from_colim_wedge_inv_2.
  Defined.
End ColimitToCopower.

(**
 4.2. Conical limits as limits
 *)
Section ColimitToConical.
  Context {V : sym_mon_closed_cat}
          {C : category}
          (E : enrichment C V)
          {I : category}
          (D : I ⟶ C).

  Let W : I^opp ⟶ V := constant_functor _ _ I_{V}.

  Context (a : colim_enriched E D W).

  Definition enriched_weighted_to_conical_cocone
    : enriched_conical_colim_cocone D.
  Proof.
    use make_enriched_conical_colim_cocone.
    - exact a.
    - exact (λ i, enriched_to_arr E (enriched_colim_cocone_in _ _ _ a i)).
    - abstract
        (intros i j f ; cbn ;
         use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn ;
         rewrite enriched_from_to_arr ;
         pose (enriched_colim_cocone_commute _ _ _ a f) as p ;
         cbn in p ;
         rewrite id_left in p ;
         rewrite <- p ;
         rewrite enriched_from_arr_comp ;
         rewrite enriched_from_to_arr ;
         rewrite tensor_split ;
         rewrite !assoc ;
         rewrite <- tensor_linvunitor ;
         unfold precomp_arr ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         rewrite tensor_rinvunitor ;
         rewrite tensor_linvunitor ;
         rewrite mon_rinvunitor_I_mon_linvunitor_I ;
         rewrite !assoc' ;
         apply maponpaths ;
         rewrite <- tensor_split ;
         rewrite <- tensor_split' ;
         apply idpath).
  Defined.

  Section ConicalColimUMP.
    Context {w : C}
            (v : V)
            (fs : ∏ (i : I), v --> E ⦃ D i , w ⦄)
            (ps : ∏ (i j : I) (k : j --> i), fs i · precomp_arr E w (#D k) = fs j).

    Proposition enriched_weighted_to_conical_is_conical_colim_unique
      : isaprop
          (∑ (g : v --> E ⦃ a , w ⦄),
           ∏ (i : I),
           g · precomp_arr E w (enriched_to_arr E (enriched_colim_cocone_in E D W a i))
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
      rewrite !tensor_comp_l_id_l.
      rewrite !assoc'.
      apply maponpaths.
      pose (p := maponpaths (λ z, mon_runitor _ · z) (pr2 φ₁ i @ !(pr2 φ₂ i))).
      cbn in p.
      unfold precomp_arr in p.
      rewrite !enriched_from_to_arr in p.
      rewrite !assoc' in p.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)) in p.
      rewrite !tensor_rinvunitor in p.
      rewrite !assoc in p.
      rewrite !mon_runitor_rinvunitor in p.
      rewrite !id_left in p.
      rewrite <- !tensor_split' in p.
      exact p.
    Qed.

    Definition enriched_weighted_to_conical_is_conical_colim_wedge_data
      : wedge_data (weighted_hom_co E D W w).
    Proof.
      use make_wedge_data.
      - exact v.
      - exact (λ i, internal_lam (mon_runitor _ · fs i)).
    Defined.

    Proposition enriched_weighted_to_conical_is_conical_colim_is_wedge
      : is_wedge
          (weighted_hom_co E D W w)
          enriched_weighted_to_conical_is_conical_colim_wedge_data.
    Proof.
      intros i j f ; cbn.
      use internal_funext.
      intros z h.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_pre_post_comp.
      rewrite !internal_beta.
      rewrite functor_id.
      rewrite precomp_arr_id.
      rewrite id_right.
      rewrite !tensor_id_id.
      rewrite !id_left.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite internal_beta.
      rewrite !assoc'.
      do 2 apply maponpaths.
      apply ps.
    Qed.

    Definition enriched_weighted_to_conical_is_conical_colim_wedge
      : wedge (weighted_hom_co E D W w).
    Proof.
      use make_wedge.
      - exact enriched_weighted_to_conical_is_conical_colim_wedge_data.
      - exact enriched_weighted_to_conical_is_conical_colim_is_wedge.
    Defined.

    Definition enriched_weighted_to_conical_is_conical_colim_mor
      : v --> E ⦃ a , w ⦄
      := mor_to_end
           _
           (pr2 a w)
           enriched_weighted_to_conical_is_conical_colim_wedge.

    Proposition enriched_weighted_to_conical_is_conical_colim_mor_eq
                (i : I)
      : enriched_weighted_to_conical_is_conical_colim_mor
        · precomp_arr E w (enriched_to_arr E (enriched_colim_cocone_in E D W a i))
        =
        fs i.
    Proof.
      pose (maponpaths
              (λ z, z #⊗ identity _ · internal_eval _ _)
              (mor_to_end_comm
                 _
                 (pr2 a w)
                 enriched_weighted_to_conical_is_conical_colim_wedge
                 i))
        as p.
      cbn in p.
      rewrite tensor_comp_id_r in p.
      rewrite !assoc' in p.
      rewrite !internal_beta in p.
      rewrite !assoc in p.
      rewrite <- tensor_split' in p.
      refine (_ @ id_left _).
      rewrite <- mon_rinvunitor_runitor.
      rewrite !assoc'.
      rewrite <- p.
      unfold precomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_rinvunitor.
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- tensor_split'.
      rewrite enriched_from_to_arr.
      apply idpath.
    Qed.
  End ConicalColimUMP.

  Definition enriched_weighted_to_conical_is_conical_colim
    : is_conical_colim_enriched E D enriched_weighted_to_conical_cocone.
  Proof.
    intros w v cc.
    use iscontraprop1.
    - exact (enriched_weighted_to_conical_is_conical_colim_unique v (pr1 cc)).
    - refine (enriched_weighted_to_conical_is_conical_colim_mor v (pr1 cc) (pr2 cc)
              ,,
              _).
      intros i.
      exact (enriched_weighted_to_conical_is_conical_colim_mor_eq v (pr1 cc) (pr2 cc) i).
  Defined.
End ColimitToConical.
