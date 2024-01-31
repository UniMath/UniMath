From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac Batch Debug.
(*****************************************************************

 Colimits in self enriched categories

 We construct colimits in self enriched categories. Copowers in
 the self enriched category come from the tensor in the monoidal
 category.

 To show how the construction of colimits works, we show how to
 construct an initial object in the self-enriched category Suppose
 that `V` is a symmetric monoidal closed category and let `x` be
 an initial object in `V`. We want to show that `x` also is an
 initial object in the enriched sense. This means that for all
 objects `y`, we must show that `x ⊸ y` is terminal in `V`. So,
 we must show that for every `w` the type `w --> x ⊸ y` is
 contractible.

 Since `⊸` is right adjoint to `⊗`, the types `w --> x ⊸ y` and
 `w ⊗ x --> y` are equivalent. As such, it suffices to show that
 `w ⊗ x --> y` is contractible. This is equivalent to `w ⊗ x`
 being an initial object, so it suffices to show that `w ⊗ x` is
 initial. Since `V` is monoidal closed, we know that the functor
 `x ↦ w ⊗ x` is a left adjoint, and thus it preserves initial
 objects. Since `x` is initial, we also get that `w ⊗ x` is
 initial, so we conclude that `V` has an initial object in the
 enriched sense.

 Contents
 1. Initial objects
 2. Binary coproducts
 3. Coequalizers
 4. Copowers
 5. Type indexed coproducts

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedInitial.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedBinaryCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCoequalizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Colimits.EnrichedCopowers.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section SelfEnrichmentColimits.
  Context (V : sym_mon_closed_cat).

  (**
   1. Initial objects
   *)
  Definition self_enrichment_initial
             (v : Initial V)
    : initial_enriched (self_enrichment V).
  Proof.
    refine (pr1 v ,, _).
    intros x y ; cbn.
    use (iscontrweqb (internal_hom_equiv _ _ _)).
    exact (left_adjoint_preserves_initial
             _
             (sym_mon_closed_left_tensor_left_adjoint V y)
             _
             (pr2 v)
             x).
  Defined.

  (**
   2. Binary coproducts
   *)
  Section SelfEnrichedCoproduct.
    Context {x y : V}
            (c : BinCoproduct x y).

    Let ι₁ : I_{V} --> x ⊸ c
      := enriched_from_arr
           (self_enrichment V)
           (BinCoproductIn1 c).

    Let ι₂ : I_{V} --> y ⊸ c
      := enriched_from_arr
           (self_enrichment V)
           (BinCoproductIn2 c).

    Definition make_self_enriched_binary_coprod_cocone
      : enriched_binary_coprod_cocone (self_enrichment V) x y.
    Proof.
      use make_enriched_binary_coprod_cocone.
      - exact c.
      - exact ι₁.
      - exact ι₂.
    Defined.

    Definition self_enriched_is_binary_coprod_paths_weq
               {w z : V}
               (f : z --> x ⊸ w)
               (g : z --> y ⊸ w)
               (fg : z --> c ⊸ w)
      : (fg · precomp_arr (self_enrichment V) w (internal_to_arr ι₁) = f
         ×
         fg · precomp_arr (self_enrichment V) w (internal_to_arr ι₂) = g)
        ≃
        (identity z #⊗ BinCoproductIn1 c · (fg #⊗ identity c · internal_eval c w)
         =
         f #⊗ identity x · internal_eval x w)
        ×
        (identity z #⊗ BinCoproductIn2 c · (fg #⊗ identity c · internal_eval c w)
         =
         g #⊗ identity y · internal_eval y w).
    Proof.
      use weqimplimpl.
      - intros pq.
        split.
        + rewrite !assoc.
          rewrite <- tensor_split.
          pose (p := pr1 pq) ; cbn in p.
          rewrite self_enrichment_precomp in p.
          rewrite <- p.
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite <- tensor_split'.
          apply maponpaths_2.
          apply maponpaths.
          rewrite internal_to_from_arr.
          apply idpath.
        + rewrite !assoc.
          rewrite <- tensor_split.
          pose (p := pr2 pq) ; cbn in p.
          rewrite self_enrichment_precomp in p.
          rewrite <- p.
          rewrite tensor_comp_r_id_r.
          rewrite !assoc'.
          rewrite internal_beta.
          rewrite !assoc.
          rewrite <- tensor_split'.
          apply maponpaths_2.
          apply maponpaths.
          rewrite internal_to_from_arr.
          apply idpath.
      - intros pq.
        split.
        + pose (p := pr1 pq).
          rewrite !assoc in p.
          rewrite <- tensor_split in p.
          use internal_funext.
          intros a h.
          rewrite tensor_comp_r_id_r.
          rewrite self_enrichment_precomp.
          rewrite !assoc'.
          rewrite internal_beta.
          rewrite (tensor_split f h).
          rewrite !assoc'.
          rewrite <- p.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite <- !tensor_comp_mor.
          rewrite id_left, id_right.
          do 2 apply maponpaths.
          cbn.
          apply internal_to_from_arr.
        + pose (p := pr2 pq) ; cbn in p.
          rewrite !assoc in p.
          rewrite <- tensor_split in p.
          use internal_funext.
          intros a h.
          rewrite tensor_comp_r_id_r.
          rewrite self_enrichment_precomp.
          rewrite !assoc'.
          rewrite internal_beta.
          rewrite (tensor_split g h).
          rewrite !assoc'.
          rewrite <- p.
          rewrite !assoc.
          apply maponpaths_2.
          rewrite <- !tensor_comp_mor.
          rewrite id_left, id_right.
          do 2 apply maponpaths.
          cbn.
          apply internal_to_from_arr.
      - apply isapropdirprod ; apply homset_property.
      - apply isapropdirprod ; apply homset_property.
    Qed.

    Definition self_enriched_is_binary_coprod_weq
               {w z : V}
               (f : z --> x ⊸ w)
               (g : z --> y ⊸ w)
      : (∑ (fg : z --> c ⊸ w),
         fg · precomp_arr (self_enrichment V) w (internal_to_arr ι₁) = f
         ×
         fg · precomp_arr (self_enrichment V) w (internal_to_arr ι₂) = g)
        ≃
        (∑ (fg : z ⊗ c --> w),
         identity z #⊗ BinCoproductIn1 c · fg = f #⊗ identity x · internal_eval x w
         ×
         identity z #⊗ BinCoproductIn2 c · fg = g #⊗ identity y · internal_eval y w).
    Proof.
      use weqtotal2.
      - exact (internal_hom_equiv z c w).
      - exact (self_enriched_is_binary_coprod_paths_weq f g).
    Defined.

    Definition self_enriched_is_binary_coprod
      : is_binary_coprod_enriched
          (self_enrichment V)
          x y
          make_self_enriched_binary_coprod_cocone.
    Proof.
      intros w z f g.
      use (iscontrweqb (self_enriched_is_binary_coprod_weq f g)).
      apply (left_adjoint_preserves_bincoproduct
               _
               (sym_mon_closed_left_tensor_left_adjoint V z)
               _ _ _ _ _
               (pr2 c)).
    Defined.
  End SelfEnrichedCoproduct.

  Definition self_enrichment_binary_coproducts
             (coprodV : BinCoproducts V)
    : enrichment_binary_coprod (self_enrichment V)
    := λ x y,
       make_self_enriched_binary_coprod_cocone (coprodV x y)
       ,,
       self_enriched_is_binary_coprod (coprodV x y).

  (**
   3. Coequalizers
   *)
  Section SelfEnrichmentCoequalizer.
    Context {x y : V}
            {f g : x --> y}
            (c : Coequalizer f g).

    Let e : y --> c := CoequalizerArrow c.

    Definition make_self_enriched_coequalizer_cocone
      : enriched_coequalizer_cocone (self_enrichment V) f g.
    Proof.
      use make_enriched_coequalizer_cocone.
      - exact c.
      - exact (enriched_from_arr (self_enrichment V) e).
      - abstract
          (cbn ;
           rewrite !internal_to_from_arr ;
           exact (CoequalizerEqAr c)).
    Defined.

    Definition self_enriched_is_coequalizer_path_weq
               {w z : V}
               (h : z --> y ⊸ w)
               (φ : z --> c ⊸ w)
      : (φ · precomp_arr (self_enrichment V) w (internal_to_arr (internal_from_arr e))
         =
         h)
        ≃
        (identity z #⊗ CoequalizerArrow c · (φ #⊗ identity c · internal_eval c w)
         =
         h #⊗ identity y · internal_eval y w).
    Proof.
      use weqimplimpl.
      - intro p.
        rewrite self_enrichment_precomp in p.
        rewrite <- p.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite internal_beta.
        rewrite internal_to_from_arr.
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite <- tensor_split'.
        apply idpath.
      - intro p.
        use internal_funext.
        intros a k.
        rewrite !assoc in p.
        rewrite <- tensor_split in p.
        rewrite self_enrichment_precomp.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        rewrite internal_beta.
        rewrite internal_to_from_arr.
        rewrite (tensor_split h k).
        rewrite !assoc'.
        rewrite <- p.
        rewrite !assoc.
        rewrite <- !tensor_comp_mor.
        rewrite id_right.
        rewrite id_left.
        apply idpath.
      - apply homset_property.
      - apply homset_property.
    Qed.

    Definition self_enriched_is_coequalizer_weq
               {w z : V}
               (h : z --> y ⊸ w)
               (r : h · precomp_arr (self_enrichment V) w f
                    =
                    h · precomp_arr (self_enrichment V) w g)
      : (∑ (φ : z --> c ⊸ w),
         φ · precomp_arr (self_enrichment V) w (internal_to_arr (internal_from_arr e)) = h)
        ≃
        (∑ (φ : z ⊗ c --> w),
         identity z #⊗ CoequalizerArrow c · φ = h #⊗ identity _ · internal_eval y w).
    Proof.
      use weqtotal2.
      - exact (internal_hom_equiv z c w).
      - exact (self_enriched_is_coequalizer_path_weq h).
    Defined.

    Definition make_self_enriched_is_coequalizer
      : is_coequalizer_enriched
          (self_enrichment V)
          f g
          make_self_enriched_coequalizer_cocone.
    Proof.
      intros w z h r.
      use (iscontrweqb (self_enriched_is_coequalizer_weq h r)).
      refine (left_adjoint_preserves_coequalizer
                _
                (sym_mon_closed_left_tensor_left_adjoint V z)
                _ _ _ _ _ _ _ _
                (pr22 c)
                _ _ _).
      - cbn.
        rewrite <- !tensor_comp_id_l.
        apply maponpaths.
        apply CoequalizerEqAr.
      - abstract
          (cbn ;
           pose (maponpaths (λ z, z #⊗ identity _ · internal_eval _ _) r)
             as r' ;
           cbn in r' ;
           rewrite !self_enrichment_precomp in r' ;
           rewrite !tensor_comp_id_r in r' ;
           rewrite !assoc' in r' ;
           rewrite !internal_beta in r' ;
           rewrite !assoc in r' ;
           rewrite <- !tensor_split' in r' ;
           rewrite !assoc ;
           rewrite <- !tensor_split ;
           exact r').
    Defined.
  End SelfEnrichmentCoequalizer.

  Definition self_enrichment_coequalizers
             (coeqV : Coequalizers V)
    : enrichment_coequalizers (self_enrichment V)
    := λ x y f g,
       make_self_enriched_coequalizer_cocone (coeqV x y f g)
       ,,
       make_self_enriched_is_coequalizer (coeqV x y f g).

  (**
   4. Copowers
   *)
  Section SelfEnrichmentCopower.
    Context (v₁ v₂ : V).

    Definition self_enrichment_copower_cocone
      : copower_cocone (self_enrichment V) v₁ v₂.
    Proof.
      use make_copower_cocone.
      - exact (v₁ ⊗ v₂).
      - exact (internal_pair v₁ v₂).
    Defined.

    Proposition self_enrichment_is_copower_eq_1
                (w : V)
      : is_copower_enriched_map
          (self_enrichment V)
          v₁ v₂
          self_enrichment_copower_cocone
          w
        · internal_uncurry v₁ v₂ w
        =
        identity _.
    Proof.
      cbn.
      use internal_funext.
      intros a h.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_uncurry.
      rewrite internal_beta.
      unfold is_copower_enriched_map.
      rewrite tensor_split.
      rewrite <- tensor_id_id.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite internal_beta ; cbn.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        unfold internal_comp.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        unfold internal_pair.
        rewrite internal_beta.
        rewrite tensor_id_id.
        apply id_left.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite mon_rassociator_lassociator.
      apply id_right.
    Qed.

    Proposition self_enrichment_is_copower_eq_2
                (w : V)
      : internal_uncurry v₁ v₂ w
        · is_copower_enriched_map
            (self_enrichment V)
            v₁ v₂
            self_enrichment_copower_cocone
            w
        =
        identity _.
    Proof.
      use internal_funext ; cbn.
      intros a₁ h₁.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold is_copower_enriched_map ; cbn.
      rewrite internal_beta.
      use internal_funext ; cbn.
      intros a₂ h₂.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite internal_beta.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        unfold internal_pair.
        rewrite internal_beta.
        rewrite tensor_id_id.
        apply id_left.
      }
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite tensor_split.
        rewrite !assoc'.
        unfold internal_uncurry.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply idpath.
      }
      rewrite !assoc.
      rewrite mon_lassociator_rassociator.
      rewrite id_left.
      apply idpath.
    Qed.

    Definition self_enrichment_is_copower
      : is_copower_enriched
          (self_enrichment V)
          v₁ v₂
          self_enrichment_copower_cocone.
    Proof.
      use make_is_copower_enriched.
      - exact (λ w, internal_uncurry v₁ v₂ w).
      - exact self_enrichment_is_copower_eq_1.
      - exact self_enrichment_is_copower_eq_2.
    Defined.
  End SelfEnrichmentCopower.

  Definition self_enrichment_copowers
    : enrichment_copower (self_enrichment V)
    := λ v₁ v₂,
       self_enrichment_copower_cocone v₁ v₂
       ,,
       self_enrichment_is_copower v₁ v₂.

  (**
   5. Type indexed coproducts
   *)
  Section SelfEnrichmentTypeCoproduct.
    Context {J : UU}
            {D : J → V}
            (coprod : Coproduct J V D).

    Let ι : ∏ (j : J), I_{V} --> D j ⊸ coprod
      := λ j,
         enriched_from_arr
           (self_enrichment V)
           (CoproductIn _ _ coprod j).

    Definition self_enriched_coprod_cocone
      : enriched_coprod_cocone (self_enrichment V) D.
    Proof.
      use make_enriched_coprod_cocone.
      - exact coprod.
      - exact ι.
    Defined.

    Definition self_enriched_is_coprod_weq_path
               {w z : V}
               (f : ∏ (j : J), z --> D j ⊸ w)
               (fs : z --> coprod ⊸ w)
               (j : J)
      : (fs · precomp_arr
                (self_enrichment V)
                w
                (internal_to_arr (internal_from_arr (CoproductIn J V coprod j)))
         =
         f j)
        ≃
        (identity z #⊗ CoproductIn J V coprod j
         · (fs #⊗ identity coprod · internal_eval coprod w)
         =
         f j #⊗ identity (D j) · internal_eval (D j) w).
    Proof.
      rewrite internal_to_from_arr.
      rewrite self_enrichment_precomp.
      rewrite !assoc.
      rewrite <- tensor_split.
      use weqimplimpl.
      - intro p.
        pose (maponpaths (λ z, z #⊗ identity _ · internal_eval _ _) p) as q.
        cbn in q.
        rewrite tensor_comp_id_r in q.
        rewrite !assoc' in q.
        rewrite internal_beta in q.
        rewrite !assoc in q.
        rewrite <- tensor_split' in q.
        exact q.
      - intro p.
        use internal_funext.
        intros a h.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite (tensor_split fs h).
        rewrite (tensor_split (f j) h).
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split'.
        exact p.
      - apply homset_property.
      - apply homset_property.
    Qed.

    Definition self_enriched_is_coprod_weq
               {w z : V}
               (f : ∏ (j : J), z --> D j ⊸ w)
      : (∑ (fs : z --> coprod ⊸ w),
         ∏ (j : J),
         fs · precomp_arr (self_enrichment V) w (internal_to_arr (ι j)) = f j)
        ≃
        (∑ (fs : z ⊗ coprod --> w),
         ∏ (j : J),
         identity z #⊗ CoproductIn _ _ coprod j · fs
         =
         f j #⊗ identity _ · internal_eval (D j) w).
    Proof.
      use weqtotal2.
      - exact (internal_hom_equiv z coprod w).
      - intro fs ; cbn -[ι].
        use weqonsecfibers.
        intro j.
        apply self_enriched_is_coprod_weq_path.
    Defined.

    Definition self_enriched_is_coprod
      : is_coprod_enriched (self_enrichment V) D self_enriched_coprod_cocone.
    Proof.
      intros w z f.
      use (iscontrweqb (self_enriched_is_coprod_weq f)).
      apply (left_adjoint_preserves_coproduct
               _
               (sym_mon_closed_left_tensor_left_adjoint V z)
                _ _ _ _
               (pr2 coprod)).
    Defined.
  End SelfEnrichmentTypeCoproduct.

  Definition self_enrichment_coprod
             (J : UU)
             (HV : Coproducts J V)
    : enrichment_coprod (self_enrichment V) J
    := λ D,
       self_enriched_coprod_cocone (HV D)
       ,,
       self_enriched_is_coprod (HV D).
End SelfEnrichmentColimits.
