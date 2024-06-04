(*****************************************************************

 Enriched conical limits

 We define conical limits for enriched categories. A conical
 limit is the limit of a functor to the underlying category
 of an enriched category. Note that in ordinary category theory,
 these limits are called limits rather than conical limits.
 The reason for that, is that the 'right' notion of limit in
 enriched category is that of a weighted limit. The power is
 an example of a limit that is not conical.

 In addition, we show that conical limits can be constructed
 from type-indexed products and equalizers. We use a similar
 construction as the one used to construct limits from
 products and equalizers in ordinary category theory.

 Content
 1. Cones of enriched conical limits
 2. Conical limits in an enriched category
 3. Being a conical limit is a proposition
 4. Accessors for conical limits
 5. Conical limits are isomorphic
 6. Construction of conical limits

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedEqualizers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section EnrichedConicalLimit.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          {I : category}
          (D : I ⟶ C).

  (**
   1. Cones of enriched conical limits
   *)
  Definition enriched_conical_lim_cone
    : UU
    := ∑ (a : C),
       ∑ (ps : ∏ (i : I), a --> D i),
       ∏ (i j : I) (f : i --> j),
       ps i · #D f = ps j.

  #[reversible=no] Coercion ob_enriched_conical_lim_cone
           (a : enriched_conical_lim_cone)
    : C
    := pr1 a.

  Definition enriched_conical_lim_cone_pr
             (a : enriched_conical_lim_cone)
             (i : I)
    : a --> D i
    := pr12 a i.

  Proposition enriched_conical_lim_cone_commute
              (a : enriched_conical_lim_cone)
              {i j : I}
              (f : i --> j)
    : enriched_conical_lim_cone_pr a i · #D f
      =
      enriched_conical_lim_cone_pr a j.
  Proof.
    exact (pr22 a i j f).
  Qed.

  Definition make_enriched_conical_lim_cone
             (a : C)
             (ps : ∏ (i : I), a --> D i)
             (eqs : ∏ (i j : I)
                      (f : i --> j),
                    ps i · #D f = ps j)
    : enriched_conical_lim_cone
    := a ,, ps ,, eqs.

  (**
   2. Conical limits in an enriched category
   *)
  Definition is_conical_lim_enriched_diagram
             (a : enriched_conical_lim_cone)
             (w : C)
    : diagram I V.
  Proof.
    use make_diagram.
    - exact (λ i, E ⦃ w , D i ⦄).
    - exact (λ i j f, postcomp_arr E w (#D f)).
  Defined.

  Definition is_conical_lim_enriched_cone
             (a : enriched_conical_lim_cone)
             (w : C)
    : cone (is_conical_lim_enriched_diagram a w) (E ⦃ w, a ⦄).
  Proof.
    use make_cone.
    - exact (λ i, postcomp_arr E w (enriched_conical_lim_cone_pr a i)).
    - abstract
        (intros i j f ; cbn ;
         rewrite <- postcomp_arr_comp ;
         rewrite enriched_conical_lim_cone_commute ;
         apply idpath).
  Defined.

  Definition is_conical_lim_enriched
             (a : enriched_conical_lim_cone)
    : UU
    := ∏ (w : C),
       isLimCone
         (is_conical_lim_enriched_diagram a w)
         (E ⦃ w , a ⦄)
         (is_conical_lim_enriched_cone a w).

  Definition is_conical_lim_enriched_to_Lim
             {a : enriched_conical_lim_cone}
             (Ha : is_conical_lim_enriched a)
             (w : C)
    : LimCone (is_conical_lim_enriched_diagram a w).
  Proof.
    use make_LimCone.
    - exact (E ⦃ w , a ⦄).
    - exact (is_conical_lim_enriched_cone a w).
    - exact (Ha w).
  Defined.

  Definition conical_lim_enriched
    : UU
    := ∑ (a : enriched_conical_lim_cone),
       is_conical_lim_enriched a.

  #[reversible=no] Coercion cone_of_conical_lim_enriched
           (a : conical_lim_enriched)
    : enriched_conical_lim_cone
    := pr1 a.

  #[reversible=no] Coercion enriched_conical_lim_cone_is_conical_lim
           (a : conical_lim_enriched)
    : is_conical_lim_enriched a
    := pr2 a.

  (**
   3. Being a conical limit is a proposition
   *)
  Proposition isaprop_is_conical_lim_enriched
              (a : enriched_conical_lim_cone)
    : isaprop (is_conical_lim_enriched a).
  Proof.
    repeat (use impred ; intro).
    apply isapropiscontr.
  Qed.

  (**
   4. Accessors for conical limits
   *)
  Section ConicalLimAccessors.
    Context (a : conical_lim_enriched).

    Definition is_conical_lim_enriched_arrow
               (w : C)
               (gs : ∏ (i : I), w --> D i)
               (qs : ∏ (i j : I)
                       (f : i --> j),
                     gs i · # D f = gs j)
      : w --> a.
    Proof.
      refine (enriched_to_arr E _).
      use (limArrow (make_LimCone _ _ _ (pr2 a w))).
      simple refine (_ ,, _).
      - exact (λ i, enriched_from_arr E (gs i)).
      - abstract
          (intros i j f ; cbn ;
           rewrite enriched_from_arr_postcomp ;
           apply maponpaths ;
           exact (qs i j f)).
    Defined.

    Proposition is_conical_lim_enriched_map_pr
                (w : C)
                (gs : ∏ (i : I), w --> D i)
                (qs : ∏ (i j : I)
                        (f : i --> j),
                      gs i · # D f = gs j)
                (i : I)
      : is_conical_lim_enriched_arrow w gs qs · enriched_conical_lim_cone_pr a i
        =
        gs i.
    Proof.
      unfold is_conical_lim_enriched_arrow, enriched_conical_lim_cone_pr.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      rewrite enriched_from_arr_comp.
      rewrite !enriched_from_to_arr.
      rewrite tensor_split.
      rewrite !assoc.
      rewrite <- tensor_linvunitor.
      etrans.
      {
        rewrite !assoc'.
        rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
        apply (limArrowCommutes
                 (make_LimCone _ _ _ (pr2 a w))).
      }
      cbn.
      apply idpath.
    Qed.

    Proposition is_conical_lim_enriched_arrow_eq
                {w : C}
                {f g : w --> a}
                (q : ∏ (i : I),
                     f · enriched_conical_lim_cone_pr a i
                     =
                     g · enriched_conical_lim_cone_pr a i)
      : f = g.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use (arr_to_LimCone_eq (is_conical_lim_enriched_to_Lim (pr2 a) w)).
      intro i ; cbn.
      rewrite !enriched_from_arr_postcomp.
      rewrite q.
      apply idpath.
    Qed.
  End ConicalLimAccessors.

  (**
   5. Conical limits are isomorphic
   *)
  Definition map_between_conical_lim_enriched
             (a b : conical_lim_enriched)
    : a --> b.
  Proof.
    use (is_conical_lim_enriched_arrow b).
    - exact (enriched_conical_lim_cone_pr a).
    - exact (λ _ _ f, enriched_conical_lim_cone_commute a f).
  Defined.

  Lemma iso_between_conical_lim_enriched_inv
        (a b : conical_lim_enriched)
    : map_between_conical_lim_enriched a b · map_between_conical_lim_enriched b a
      =
      identity _.
  Proof.
    unfold map_between_conical_lim_enriched.
    use (is_conical_lim_enriched_arrow_eq a).
    intro j.
    rewrite !assoc'.
    rewrite !is_conical_lim_enriched_map_pr.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition iso_between_conical_lim_enriched
             (a b : conical_lim_enriched)
    : z_iso a b.
  Proof.
    use make_z_iso.
    - exact (map_between_conical_lim_enriched a b).
    - exact (map_between_conical_lim_enriched b a).
    - split.
      + apply iso_between_conical_lim_enriched_inv.
      + apply iso_between_conical_lim_enriched_inv.
  Defined.

  Proposition isaprop_conical_lim_enriched
              (HC : is_univalent C)
    : isaprop (conical_lim_enriched).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isaprop_is_conical_lim_enriched.
    }
    use total2_paths_f.
    - use (isotoid _ HC).
      apply iso_between_conical_lim_enriched.
    - use subtypePath.
      {
        intro.
        repeat (use impred ; intro).
        apply homset_property.
      }
      rewrite pr1_transportf.
      rewrite transportf_sec_constant.
      use funextsec.
      intro j.
      rewrite transportf_isotoid.
      use z_iso_inv_on_right ; cbn.
      refine (!_).
      apply is_conical_lim_enriched_map_pr.
  Qed.
End EnrichedConicalLimit.

(**
 6. Construction of conical limits
 *)
Section ConstructionOfConicalLimit.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          {I : category}
          (D : I ⟶ C)
          (PE : ∏ (J : UU), enrichment_prod E J)
          (EE : enrichment_equalizers E).

  Let prod_src : C := pr1 (PE I D).
  Let is_prod_src : is_prod_enriched E D prod_src := pr2 (PE I D).

  Let prod_tar : C
    := pr1 (PE (∑ (x : I) (y : I), x --> y) (λ z, D (pr12 z))).
  Let is_prod_tar : is_prod_enriched E _ prod_tar
    := pr2 (PE (∑ (x : I) (y : I), x --> y) (λ z, D (pr12 z))).

  Local Definition enriched_conical_lim_from_prod_equalizers_l
    : prod_src --> prod_tar
    := is_prod_enriched_arrow _ _ is_prod_tar (λ j, enriched_prod_cone_pr _ _ _ (pr12 j)).

  Let f : prod_src --> prod_tar := enriched_conical_lim_from_prod_equalizers_l.

  Local Proposition enriched_conical_lim_from_prod_equalizers_l_pr
                    {i j : I}
                    (k : i --> j)
    : f · enriched_prod_cone_pr _ _ _ (i ,, j ,, k)
      =
      enriched_prod_cone_pr _ _ _ j.
  Proof.
    exact (is_prod_enriched_arrow_pr
             _ _
             is_prod_tar
             (λ j, enriched_prod_cone_pr _ _ _ (pr12 j))
             (i ,, j ,, k)).
  Qed.

  Local Definition enriched_conical_lim_from_prod_equalizers_r
    : prod_src --> prod_tar
    := is_prod_enriched_arrow
         _ _
         is_prod_tar
         (λ j, enriched_prod_cone_pr _ _ _ (pr1 j) · #D (pr22 j)).

  Let g : prod_src --> prod_tar := enriched_conical_lim_from_prod_equalizers_r.

  Local Proposition enriched_conical_lim_from_prod_equalizers_r_pr
                    {i j : I}
                    (k : i --> j)
    : g · enriched_prod_cone_pr _ _ _ (i ,, j ,, k)
      =
      enriched_prod_cone_pr _ _ _ i · #D k.
  Proof.
    exact (is_prod_enriched_arrow_pr
             _ _
             is_prod_tar
             _
             (i ,, j ,, k)).
  Qed.

  Definition enriched_conical_lim_ob_from_prod_equalizers
    : C
    := pr1 (EE _ _ f g).

  Let lim : C := enriched_conical_lim_ob_from_prod_equalizers.

  Definition enriched_conical_lim_ob_from_prod_equalizers_is_equalizer
    : is_equalizer_enriched E f g lim
    := pr2 (EE _ _ f g).

  Definition enriched_conical_lim_pr_from_prod_equalizers
             (i : I)
    : lim --> D i
    := enriched_equalizer_cone_pr _ _ _ (pr1 (EE _ _ f g))
       · enriched_prod_cone_pr _ _ _ i.

  Proposition enriched_conical_lim_eq_from_prod_equalizers
              {i j : I}
              (k : i --> j)
    : enriched_conical_lim_pr_from_prod_equalizers i · # D k
      =
      enriched_conical_lim_pr_from_prod_equalizers j.
  Proof.
    unfold enriched_conical_lim_pr_from_prod_equalizers.
    rewrite !assoc'.
    rewrite <- enriched_conical_lim_from_prod_equalizers_r_pr.
    rewrite <- (enriched_conical_lim_from_prod_equalizers_l_pr k).
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    exact (enriched_equalizer_cone_eq _ _ _ (pr1 (EE _ _ f g))).
  Qed.

  Definition enriched_conical_lim_from_prod_equalizers_cone
    : enriched_conical_lim_cone D.
  Proof.
    use make_enriched_conical_lim_cone.
    - exact lim.
    - exact enriched_conical_lim_pr_from_prod_equalizers.
    - exact (λ i j k, enriched_conical_lim_eq_from_prod_equalizers k).
  Defined.

  Section EnrichedConicalLimUMP.
    Context (w : C)
            (v : V)
            (fs : ∏ (i : I), v --> E ⦃ w, D i ⦄)
            (qs : ∏ (i j : I) (k : i --> j), fs i · postcomp_arr E w (# D k) = fs j).

    Proposition enriched_conical_lim_from_prod_equalizers_unique
      : isaprop
          (∑ (φ : v --> E ⦃ w, lim ⦄),
           ∏ (i : I),
           φ · postcomp_arr E w (enriched_conical_lim_pr_from_prod_equalizers i)
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
      use (EqualizerInsEq
             (is_equalizer_enriched_to_Equalizer
                _ _ _
                enriched_conical_lim_ob_from_prod_equalizers_is_equalizer
                w)).
      use (ProductArrow_eq
             _ _ _
             (is_prod_enriched_to_Product
                _ _
                is_prod_src
                w)).
      intro i ; cbn.
      rewrite !assoc'.
      rewrite <- !postcomp_arr_comp.
      exact (pr2 φ₁ i @ !(pr2 φ₂ i)).
    Qed.

    Definition enriched_conical_lim_from_prod_equalizers_mor
      : v --> E ⦃ w , lim ⦄.
    Proof.
      use (EqualizerIn
             (is_equalizer_enriched_to_Equalizer
                _ _ _
                enriched_conical_lim_ob_from_prod_equalizers_is_equalizer
                w)).
      - exact (ProductArrow
                 _ _
                 (is_prod_enriched_to_Product
                    _ _
                    is_prod_src
                    w)
                 fs).
      - abstract
          (use (ProductArrow_eq
                  _ _ _
                  (is_prod_enriched_to_Product
                     _ _
                     is_prod_tar
                     w)) ;
           intros ijk ; cbn ;
           pose (ProductPrCommutes
                   I V _
                   (is_prod_enriched_to_Product E D is_prod_src w)
                   _
                   fs)
             as p ;
           cbn in p ;
           rewrite !assoc' ;
           rewrite <- !postcomp_arr_comp ;
           rewrite enriched_conical_lim_from_prod_equalizers_l_pr ;
           rewrite enriched_conical_lim_from_prod_equalizers_r_pr ;
           rewrite postcomp_arr_comp ;
           rewrite !assoc ;
           rewrite !p ;
           refine (!_) ;
           apply qs).
    Defined.

    Proposition enriched_conical_lim_from_prod_equalizers_commute
                (i : I)
      : enriched_conical_lim_from_prod_equalizers_mor
        · postcomp_arr E w (enriched_conical_lim_pr_from_prod_equalizers i)
        =
        fs i.
    Proof.
      unfold enriched_conical_lim_from_prod_equalizers_mor.
      unfold enriched_conical_lim_pr_from_prod_equalizers.
      rewrite postcomp_arr_comp.
      rewrite !assoc.
      rewrite (EqualizerCommutes
                 (is_equalizer_enriched_to_Equalizer E f g
                    enriched_conical_lim_ob_from_prod_equalizers_is_equalizer w)).
      rewrite (ProductPrCommutes
                 _ _ _
                 (is_prod_enriched_to_Product E D is_prod_src w)).
      apply idpath.
    Qed.
  End EnrichedConicalLimUMP.

  Definition enriched_conical_lim_from_prod_equalizers_is_lim
    : is_conical_lim_enriched
        E D
        enriched_conical_lim_from_prod_equalizers_cone.
  Proof.
    intros w v cc ; cbn.
    use iscontraprop1.
    - exact (enriched_conical_lim_from_prod_equalizers_unique w v (pr1 cc)).
    - simple refine (_ ,, _).
      + exact (enriched_conical_lim_from_prod_equalizers_mor _ _ (pr1 cc) (pr2 cc)).
      + exact (enriched_conical_lim_from_prod_equalizers_commute _ _ (pr1 cc) (pr2 cc)).
  Defined.

  Definition enriched_conical_lim_from_prod_equalizers
    : conical_lim_enriched E D
    := enriched_conical_lim_from_prod_equalizers_cone
       ,,
       enriched_conical_lim_from_prod_equalizers_is_lim.
End ConstructionOfConicalLimit.
