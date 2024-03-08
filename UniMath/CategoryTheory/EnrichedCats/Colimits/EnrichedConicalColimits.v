(*****************************************************************

 Enriched conical colimits

 We define conical colimits for enriched categories. A conical
 colimit is the colimit of a functor to the underlying category
 of an enriched category. Note that in ordinary category theory,
 these colimits are called colimits rather than conical colimits.
 The reason for that, is that the 'right' notion of colimit in
 enriched category is that of a weighted colimit. The copower is
 an example of a colimit that is not conical.

 In addition, we show that conical colimits can be constructed
 from type-indexed coproducts and coequalizers. We use a similar
 construction as the one used to construct colimits from
 coproducts and coequalizers in ordinary category theory.

 Content
 1. Cocones of enriched conical colimits
 2. Conical colimits in an enriched category
 3. Being a conical colimit is a proposition
 4. Accessors for conical colimits
 5. Conical colimits are isomorphic
 6. Construction of conical colimits

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoequalizers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section EnrichedConicalColimit.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          {I : category}
          (D : I ⟶ C).

  (**
   1. Cocones of enriched conical colimits
   *)
  Definition enriched_conical_colim_cocone
    : UU
    := ∑ (a : C),
       ∑ (ps : ∏ (i : I), D i --> a),
       ∏ (i j : I) (f : i --> j),
       #D f · ps j = ps i.

  #[reversible=no] Coercion ob_enriched_conical_colim_cocone
           (a : enriched_conical_colim_cocone)
    : C
    := pr1 a.

  Definition enriched_conical_colim_cocone_in
             (a : enriched_conical_colim_cocone)
             (i : I)
    : D i --> a
    := pr12 a i.

  Proposition enriched_enriched_conical_colim_cocone_commute
              (a : enriched_conical_colim_cocone)
              {i j : I}
              (f : i --> j)
    : #D f · enriched_conical_colim_cocone_in a j
      =
      enriched_conical_colim_cocone_in a i.
  Proof.
    exact (pr22 a i j f).
  Qed.

  Definition make_enriched_conical_colim_cocone
             (a : C)
             (ps : ∏ (i : I), D i --> a)
             (eqs : ∏ (i j : I)
                      (f : i --> j),
                    #D f · ps j = ps i)
    : enriched_conical_colim_cocone
    := a ,, ps ,, eqs.

  (**
   2. Conical colimits in an enriched category
   *)
  Definition is_conical_colim_enriched_diagram
             (a : enriched_conical_colim_cocone)
             (w : C)
    : diagram (I^opp) V.
  Proof.
    use make_diagram.
    - exact (λ i, E ⦃ D i , w ⦄).
    - exact (λ i j f, precomp_arr E w (#D f)).
  Defined.

  Definition is_conical_colim_enriched_cone
             (a : enriched_conical_colim_cocone)
             (w : C)
    : cone (is_conical_colim_enriched_diagram a w) (E ⦃ a , w ⦄).
  Proof.
    use make_cone.
    - exact (λ i, precomp_arr E w (enriched_conical_colim_cocone_in a i)).
    - abstract
        (intros i j f ; cbn ;
         rewrite <- precomp_arr_comp ;
         rewrite enriched_enriched_conical_colim_cocone_commute ;
         apply idpath).
  Defined.

  Definition is_conical_colim_enriched
             (a : enriched_conical_colim_cocone)
    : UU
    := ∏ (w : C),
       isLimCone
         (is_conical_colim_enriched_diagram a w)
         (E ⦃ a , w ⦄)
         (is_conical_colim_enriched_cone a w).

  Definition is_conical_colim_enriched_to_Lim
             {a : enriched_conical_colim_cocone}
             (Ha : is_conical_colim_enriched a)
             (w : C)
    : LimCone (is_conical_colim_enriched_diagram a w).
  Proof.
    use make_LimCone.
    - exact (E ⦃ a , w ⦄).
    - exact (is_conical_colim_enriched_cone a w).
    - exact (Ha w).
  Defined.

  Definition conical_colim_enriched
    : UU
    := ∑ (a : enriched_conical_colim_cocone),
       is_conical_colim_enriched a.

  #[reversible=no] Coercion cocone_of_enriched_conical_colim_cocone
           (a : conical_colim_enriched)
    : enriched_conical_colim_cocone
    := pr1 a.

  #[reversible=no] Coercion conical_colim_enriched_is_conical_colim
           (a : conical_colim_enriched)
    : is_conical_colim_enriched a
    := pr2 a.

  (**
   3. Being a conical colimit is a proposition
   *)
  Proposition isaprop_is_conical_colim_enriched
              (a : enriched_conical_colim_cocone)
    : isaprop (is_conical_colim_enriched a).
  Proof.
    repeat (use impred ; intro).
    apply isapropiscontr.
  Qed.

  (**
   4. Accessors for conical colimits
   *)
  Section ConicalColimAccessors.
    Context (a : conical_colim_enriched).

    Definition is_conical_colim_enriched_arrow
               (w : C)
               (gs : ∏ (i : I), D i --> w)
               (qs : ∏ (i j : I)
                       (f : i --> j),
                     # D f · gs j = gs i)
      : a --> w.
    Proof.
      refine (enriched_to_arr E _).
      use (limArrow (make_LimCone _ _ _ (pr2 a w))).
      simple refine (_ ,, _).
      - exact (λ i, enriched_from_arr E (gs i)).
      - abstract
          (intros i j f ; cbn ;
           rewrite enriched_from_arr_precomp ;
           apply maponpaths ;
           exact (qs j i f)).
    Defined.

    Proposition is_conical_colim_enriched_map_in
                (w : C)
                (gs : ∏ (i : I), D i --> w)
                (qs : ∏ (i j : I)
                        (f : i --> j),
                      # D f · gs j = gs i)
                (i : I)
      : enriched_conical_colim_cocone_in a i · is_conical_colim_enriched_arrow w gs qs
        =
        gs i.
    Proof.
      unfold is_conical_colim_enriched_arrow, enriched_conical_colim_cocone_in.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      rewrite enriched_from_arr_comp.
      rewrite !enriched_from_to_arr.
      rewrite tensor_split'.
      rewrite !assoc.
      rewrite mon_linvunitor_I_mon_rinvunitor_I.
      rewrite <- tensor_rinvunitor.
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

    Proposition is_conical_colim_enriched_arrow_eq
                {w : C}
                {f g : a --> w}
                (q : ∏ (i : I),
                     enriched_conical_colim_cocone_in a i · f
                     =
                     enriched_conical_colim_cocone_in a i · g)
      : f = g.
    Proof.
      refine (!(enriched_to_from_arr E _) @ _ @ enriched_to_from_arr E _).
      apply maponpaths.
      use (arr_to_LimCone_eq (is_conical_colim_enriched_to_Lim (pr2 a) w)).
      intro i ; cbn.
      rewrite !enriched_from_arr_precomp.
      rewrite q.
      apply idpath.
    Qed.
  End ConicalColimAccessors.

  (**
   5. Conical colimits are isomorphic
   *)
  Definition map_between_conical_colim_enriched
             (a b : conical_colim_enriched)
    : a --> b.
  Proof.
    use (is_conical_colim_enriched_arrow a).
    - exact (enriched_conical_colim_cocone_in b).
    - exact (λ _ _ f, enriched_enriched_conical_colim_cocone_commute b f).
  Defined.

  Lemma iso_between_conical_colim_enriched_inv
        (a b : conical_colim_enriched)
    : map_between_conical_colim_enriched a b · map_between_conical_colim_enriched b a
      =
      identity _.
  Proof.
    unfold map_between_conical_colim_enriched.
    use (is_conical_colim_enriched_arrow_eq a).
    intro j.
    rewrite !assoc.
    rewrite !is_conical_colim_enriched_map_in.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition iso_between_conical_colim_enriched
             (a b : conical_colim_enriched)
    : z_iso a b.
  Proof.
    use make_z_iso.
    - exact (map_between_conical_colim_enriched a b).
    - exact (map_between_conical_colim_enriched b a).
    - split.
      + apply iso_between_conical_colim_enriched_inv.
      + apply iso_between_conical_colim_enriched_inv.
  Defined.

  Proposition isaprop_conical_colim_enriched
              (HC : is_univalent C)
    : isaprop (conical_colim_enriched).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isaprop_is_conical_colim_enriched.
    }
    use total2_paths_f.
    - use (isotoid _ HC).
      apply iso_between_conical_colim_enriched.
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
      rewrite transportf_isotoid'.
      apply is_conical_colim_enriched_map_in.
  Qed.
End EnrichedConicalColimit.

(**
 6. Construction of conical colimits
 *)
Section ConstructionOfConicalColimit.
  Context {V : monoidal_cat}
          {C : category}
          (E : enrichment C V)
          {I' : category}
          (D : I' ⟶ C)
          (PE : ∏ (J : UU), enrichment_coprod E J)
          (EE : enrichment_coequalizers E).

  Let I : category := I'^opp.

  Let coprod_src : C
    := pr1 (PE (∑ (x : I) (y : I), x --> y) (λ z, D (pr12 z))).
  Let is_coprod_src : is_coprod_enriched E _ coprod_src
    := pr2 (PE (∑ (x : I) (y : I), x --> y) (λ z, D (pr12 z))).

  Let coprod_tar : C := pr1 (PE I D).
  Let is_coprod_tar : is_coprod_enriched E D coprod_tar := pr2 (PE I D).

  Local Definition enriched_conical_colim_from_coprod_coequalizers_l
    : coprod_src --> coprod_tar
    := is_coprod_enriched_arrow
         _
         _
         is_coprod_src
         (λ j, enriched_coprod_cocone_in _ _ _ (pr12 j)).

  Let f : coprod_src --> coprod_tar := enriched_conical_colim_from_coprod_coequalizers_l.

  Local Proposition enriched_conical_colim_from_coprod_coequalizers_l_in
                    {i j : I}
                    (k : i --> j)
    : enriched_coprod_cocone_in _ _ _ (i ,, j ,, k) · f
      =
      enriched_coprod_cocone_in _ _ _ j.
  Proof.
    exact (is_coprod_enriched_arrow_in
             _ _
             is_coprod_src
             _
             (i ,, j ,, k)).
  Qed.

  Local Definition enriched_conical_colim_from_coprod_coequalizers_r
    : coprod_src --> coprod_tar
    := is_coprod_enriched_arrow
         _
         _
         is_coprod_src
         (λ j, #D (pr22 j) · enriched_coprod_cocone_in _ _ _ (pr1 j)).

  Let g : coprod_src --> coprod_tar := enriched_conical_colim_from_coprod_coequalizers_r.

  Local Proposition enriched_conical_colim_from_coprod_coequalizers_r_in
                    {i j : I}
                    (k : i --> j)
    : enriched_coprod_cocone_in _ _ _ (i ,, j ,, k) · g
      =
      #D k · enriched_coprod_cocone_in _ _ _ i.
  Proof.
    exact (is_coprod_enriched_arrow_in
             _ _
             is_coprod_src
             _
             (i ,, j ,, k)).
  Qed.

  Definition enriched_conical_colim_ob_from_coprod_coequalizers
    : C
    := pr1 (EE _ _ f g).

  Let colim : C := enriched_conical_colim_ob_from_coprod_coequalizers.

  Definition enriched_conical_colim_ob_from_coprod_coequalizers_is_coequalizer
    : is_coequalizer_enriched E f g colim
    := pr2 (EE _ _ f g).

  Definition enriched_conical_colim_in_from_coprod_coequalizers
             (i : I)
    : D i --> colim
    := enriched_coprod_cocone_in _ _ _ i
       · enriched_coequalizer_cocone_in _ _ _ (pr1 (EE _ _ f g)).

  Proposition enriched_conical_colim_eq_from_coprod_coequalizers
              {i j : I}
              (k : i --> j)
    : # D k · enriched_conical_colim_in_from_coprod_coequalizers i
      =
      enriched_conical_colim_in_from_coprod_coequalizers j.
  Proof.
    unfold enriched_conical_colim_in_from_coprod_coequalizers.
    rewrite !assoc.
    rewrite <- enriched_conical_colim_from_coprod_coequalizers_r_in.
    rewrite <- (enriched_conical_colim_from_coprod_coequalizers_l_in k).
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    exact (enriched_coequalizer_cocone_eq _ _ _ (pr1 (EE _ _ f g))).
  Qed.

  Definition enriched_conical_colim_from_coprod_coequalizers_cocone
    : enriched_conical_colim_cocone D.
  Proof.
    use make_enriched_conical_colim_cocone.
    - exact colim.
    - exact enriched_conical_colim_in_from_coprod_coequalizers.
    - exact (λ i j k, enriched_conical_colim_eq_from_coprod_coequalizers k).
  Defined.

  Section EnrichedConicalColimUMP.
    Context (w : C)
            (v : V)
            (fs : ∏ (i : I), v --> E ⦃ D i , w ⦄)
            (qs : ∏ (i j : I) (k : i --> j), fs i · precomp_arr E w (# D k) = fs j).

    Proposition enriched_conical_colim_from_coprod_coequalizers_unique
      : isaprop
          (∑ (φ : v --> E ⦃ colim , w ⦄),
           ∏ (i : I),
           φ · precomp_arr E w (enriched_conical_colim_in_from_coprod_coequalizers i)
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
             (is_coequalizer_enriched_to_Equalizer
                _ _ _
                enriched_conical_colim_ob_from_coprod_coequalizers_is_coequalizer
                w)).
      use (ProductArrow_eq
             _ _ _
             (is_coprod_enriched_to_Product
                _ _
                is_coprod_tar
                w)).
      intro i ; cbn.
      rewrite !assoc'.
      rewrite <- !precomp_arr_comp.
      exact (pr2 φ₁ i @ !(pr2 φ₂ i)).
    Qed.

    Definition enriched_conical_colim_from_coprod_coequalizers_mor
      : v --> E ⦃ colim , w ⦄.
    Proof.
      use (EqualizerIn
             (is_coequalizer_enriched_to_Equalizer
                _ _ _
                enriched_conical_colim_ob_from_coprod_coequalizers_is_coequalizer
                w)).
      - exact (ProductArrow
                 _ _
                 (is_coprod_enriched_to_Product
                    _ _
                    is_coprod_tar
                    w)
                 fs).
      - abstract
          (use (ProductArrow_eq
                  _ _ _
                  (is_coprod_enriched_to_Product
                     _ _
                     is_coprod_src
                     w)) ;
           intros ijk ; cbn ;
           pose (ProductPrCommutes
                   I V _
                   (is_coprod_enriched_to_Product E D is_coprod_tar w)
                   _
                   fs)
             as p ;
           cbn in p ;
           rewrite !assoc' ;
           rewrite <- !precomp_arr_comp ;
           rewrite enriched_conical_colim_from_coprod_coequalizers_l_in ;
           rewrite enriched_conical_colim_from_coprod_coequalizers_r_in ;
           rewrite precomp_arr_comp ;
           rewrite !assoc ;
           rewrite !p ;
           refine (!_) ;
           apply qs).
    Defined.

    Proposition enriched_conical_colim_from_coprod_coequalizers_commute
                (i : I)
      : enriched_conical_colim_from_coprod_coequalizers_mor
        · precomp_arr E w (enriched_conical_colim_in_from_coprod_coequalizers i)
        =
        fs i.
    Proof.
      unfold enriched_conical_colim_from_coprod_coequalizers_mor.
      unfold enriched_conical_colim_in_from_coprod_coequalizers.
      rewrite precomp_arr_comp.
      rewrite !assoc.
      rewrite (EqualizerCommutes
                 (is_coequalizer_enriched_to_Equalizer E f g
                    enriched_conical_colim_ob_from_coprod_coequalizers_is_coequalizer w)).
      rewrite (ProductPrCommutes
                 _ _ _
                 (is_coprod_enriched_to_Product E D is_coprod_tar w)).
      apply idpath.
    Qed.
  End EnrichedConicalColimUMP.

  Definition enriched_conical_colim_from_coprod_coequalizers_is_colim
    : is_conical_colim_enriched
        E D
        enriched_conical_colim_from_coprod_coequalizers_cocone.
  Proof.
    intros w v cc ; cbn.
    use iscontraprop1.
    - exact (enriched_conical_colim_from_coprod_coequalizers_unique w v (pr1 cc)).
    - simple refine (_ ,, _).
      + exact (enriched_conical_colim_from_coprod_coequalizers_mor _ _ (pr1 cc) (pr2 cc)).
      + exact (enriched_conical_colim_from_coprod_coequalizers_commute _ _ (pr1 cc) (pr2 cc)).
  Defined.

  Definition enriched_conical_colim_from_coprod_coequalizers
    : conical_colim_enriched E D
    := enriched_conical_colim_from_coprod_coequalizers_cocone
       ,,
       enriched_conical_colim_from_coprod_coequalizers_is_colim.
End ConstructionOfConicalColimit.
