(**********************************************************************

 The enriched Kleisli category

 In this file we define an enrichment of the Kleisli category (that is
 not guaranteed to be univalent). There are a couple of interesting
 aspects to this construction.
 - The data is given in [Kleisli_cat_monad_enrichment_data]. Most of
   the data corresponds directly to what one would expect from the
   Kleisli category. The hom object is given by the hom object from
   `E` but instantiated with the correct arguments, and the identity
   is given by the unit.
 - For composition in the enrichment, `postcomp_arr` is used. This
   significantly simplifies the usage of the obtained enrichment.
 - To prove the category laws in the enriched setting, one essentially
   follows the same proof strategy as for the ordinary case.

 In addition, we look at the universal property of the Kleisli category.
 We give a mapping property to construct functors from the Kleisli
 category ([functor_from_kleisli_cat_enrichment]), and we give a mapping
 property for natural transformations
 ([nat_trans_from_kleisli_cat_monad_enrichment]).

 Contents
 1. Data of the enrichment
 2. The laws of the enrichment
 3. The enrichment
 4. Enriched functors from the Kleisli category
 5. Natural transformations from the Kleisli category

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedKleisli.
  Context {V : monoidal_cat}
          {C : category}
          {E : enrichment C V}
          {M : Monad C}
          (EM : monad_enrichment E M).

  (** * 1. Data of the enrichment *)
  Definition Kleisli_cat_monad_enrichment_data
    : enrichment_data (Kleisli_cat_monad M) V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, E ⦃ x , M y ⦄).
    - exact (λ x, enriched_from_arr E (η M x)).
    - exact (λ x y z,
             endo_of_monad_enrichment EM y (M z) #⊗ identity _
             · enriched_comp E x (M y) (M(M z))
             · postcomp_arr E x (μ M z)).
    - exact (λ x y f, enriched_from_arr E f).
    - exact (λ x y f, enriched_to_arr E f).
  Defined.

  (** * 2. The laws of the enrichment *)
  Definition Kleisli_cat_monad_enrichment_laws
    : enrichment_laws Kleisli_cat_monad_enrichment_data.
  Proof.
    repeat split.
    - intros x y ; cbn.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        rewrite enriched_comp_postcomp_arr.
        rewrite !assoc.
        rewrite <- !tensor_comp_id_r.
        rewrite <- functor_enrichment_from_arr.
        rewrite enriched_from_arr_postcomp.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply maponpaths.
          exact (@Monad_law2 _ M y).
        }
        rewrite enriched_from_arr_id.
        rewrite <- enrichment_id_left.
        apply idpath.
      }
      apply idpath.
    - intros x y ; cbn.
      rewrite <- enriched_id_precomp_arr.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        rewrite <- enriched_comp_precomp_arr.
        rewrite !assoc.
        rewrite <- enrichment_id_right.
        apply idpath.
      }
      rewrite !assoc.
      rewrite tensor_runitor.
      refine (_ @ id_right _).
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite (nat_trans_enrichment_to_comp (unit_of_monad_enrichment EM)) ; cbn.
      rewrite id_left.
      rewrite <- postcomp_arr_comp.
      refine (_ @ postcomp_arr_id _ _ _).
      apply maponpaths.
      exact (@Monad_law1 _ M y).
    - intros w x y z ; cbn.
      rewrite !assoc'.
      rewrite !enriched_comp_postcomp_arr.
      rewrite !assoc.
      rewrite <- !tensor_comp_id_r.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite functor_enrichment_comp.
        rewrite !assoc'.
        rewrite enriched_comp_postcomp_arr.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite enrichment_assoc.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite <- !tensor_comp_mor.
        rewrite !id_left, !id_right.
        rewrite tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        rewrite tensor_split'.
        rewrite tensor_comp_id_r.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        rewrite !assoc.
        rewrite <- functor_enrichment_postcomp_arr.
        rewrite !assoc'.
        rewrite <- postcomp_arr_comp.
        do 2 apply maponpaths.
        exact (@Monad_law3 _ M z).
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !tensor_comp_id_l.
      rewrite !tensor_comp_id_r.
      rewrite !tensor_comp_id_l.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_comp_id_l.
        rewrite !assoc'.
        rewrite enrichment_assoc'.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite <- precomp_postcomp_arr_assoc.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        rewrite enrichment_assoc.
        rewrite !assoc.
        rewrite tensor_lassociator.
        apply idpath.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite mon_rassociator_lassociator.
        rewrite id_right.
        apply idpath.
      }
      rewrite <- !tensor_comp_mor.
      rewrite tensor_id_id.
      rewrite !id_left, !id_right.
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite <- precomp_postcomp_arr.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (nat_trans_enrichment_to_comp (mu_of_monad_enrichment EM) y (M z)).
      }
      cbn.
      rewrite !assoc'.
      rewrite <- postcomp_arr_comp.
      apply idpath.
    - intros x y f ; cbn.
      apply enriched_to_from_arr.
    - intros x y f ; cbn.
      apply enriched_from_to_arr.
    - intros x ; cbn.
      apply enriched_to_from_arr.
    - intros x y z f g ; cbn.
      refine (!_).
      rewrite !assoc'.
      rewrite enriched_comp_postcomp_arr.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- !tensor_comp_mor.
        rewrite !id_right.
        rewrite <- functor_enrichment_from_arr.
        rewrite enriched_from_arr_postcomp.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- enriched_to_arr_comp.
      apply idpath.
  Qed.

  (** * 3. The enrichment *)
  Definition Kleisli_cat_monad_enrichment
    : enrichment (Kleisli_cat_monad M) V.
  Proof.
    simple refine (_ ,, _).
    - exact Kleisli_cat_monad_enrichment_data.
    - exact Kleisli_cat_monad_enrichment_laws.
  Defined.

  Proposition Kleisli_cat_enrichment_precomp_arr
              {x y : Kleisli_cat_monad M}
              (w : Kleisli_cat_monad M)
              (f : x --> y)
    : precomp_arr
        Kleisli_cat_monad_enrichment
        w
        f
      =
      EM y (M w)
      · postcomp_arr E _ (μ M w)
      · precomp_arr E _ f.
  Proof.
    unfold precomp_arr ; cbn.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_split.
      rewrite tensor_split'.
      apply idpath.
    }
    rewrite !assoc.
    rewrite tensor_rinvunitor.
    rewrite !tensor_comp_id_r.
    rewrite !assoc'.
    do 2 apply maponpaths.
    rewrite enriched_comp_postcomp_arr.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_split.
    rewrite <- tensor_split'.
    apply idpath.
  Qed.

  Proposition Kleisli_cat_enrichment_postcomp_arr
              {x y : Kleisli_cat_monad M}
              (w : Kleisli_cat_monad M)
              (f : x --> y)
    : postcomp_arr
        Kleisli_cat_monad_enrichment
        w
        f
      =
      postcomp_arr E w (#M f · μ M y).
  Proof.
    unfold postcomp_arr ; cbn.
    rewrite !assoc'.
    apply maponpaths.
    rewrite enriched_comp_postcomp_arr.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- !tensor_comp_id_r.
    apply maponpaths_2.
    rewrite <- functor_enrichment_from_arr.
    rewrite enriched_from_arr_postcomp.
    apply idpath.
  Qed.

  (** * 4. Enriched functors from the Kleisli category *)
  Definition Left_Kleisli_functor_enrichment_laws
    : @is_functor_enrichment
        _ _ _
        (Left_Kleisli_functor M)
        E
        Kleisli_cat_monad_enrichment
        (λ x y : C, postcomp_arr E x (η M y)).
  Proof.
    repeat split.
    - intro x.
      exact (enriched_id_postcomp_arr E (η M x)).
    - intros x y z ; cbn.
      rewrite !assoc'.
      rewrite !enriched_comp_postcomp_arr.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite tensor_split'.
        rewrite !assoc'.
        apply maponpaths.
        rewrite <- tensor_comp_id_r.
        rewrite <- tensor_split.
        rewrite tensor_split'.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc'.
        rewrite <- precomp_postcomp_arr_assoc.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite <- !tensor_comp_mor.
      rewrite !id_left.
      apply maponpaths_2.
      rewrite !assoc.
      rewrite <- functor_enrichment_postcomp_arr.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- postcomp_arr_comp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply Monad_law2.
        }
        rewrite postcomp_arr_id.
        apply id_left.
      }
      rewrite (nat_trans_enrichment_to_comp (unit_of_monad_enrichment EM)).
      apply id_left.
    - intros x y f ; cbn.
      rewrite enriched_from_arr_postcomp.
      apply idpath.
  Qed.

  Definition Left_Kleisli_functor_enrichment
    : functor_enrichment
        (Left_Kleisli_functor M)
        E
        Kleisli_cat_monad_enrichment.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, postcomp_arr E x (η M y)).
    - exact Left_Kleisli_functor_enrichment_laws.
  Defined.

  Proposition kleisli_monad_nat_trans_enrichment
    : nat_trans_enrichment
        (kleisli_monad_nat_trans M)
        (functor_comp_enrichment
           EM
           Left_Kleisli_functor_enrichment)
        Left_Kleisli_functor_enrichment.
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    rewrite Kleisli_cat_enrichment_precomp_arr, Kleisli_cat_enrichment_postcomp_arr.
    rewrite precomp_arr_id.
    rewrite id_right.
    rewrite functor_id.
    rewrite id_left.
    rewrite !assoc.
    rewrite <- functor_enrichment_postcomp_arr.
    rewrite !assoc'.
    rewrite <- !postcomp_arr_comp.
    do 2 apply maponpaths.
    refine (Monad_law2 _ @ !_).
    apply Monad_law1.
  Qed.

  Section FunctorFromKleisli.
    Context {C' : category}
            (E' : enrichment C' V)
            {F : C ⟶ C'}
            (EF : functor_enrichment F E E')
            {γ : M ∙ F ⟹ F}
            (Eγ : nat_trans_enrichment
                    γ
                    (functor_comp_enrichment EM EF)
                    EF)
            (p : ∏ (x : C), # F (η M x) · γ x = identity _)
            (q : ∏ (x : C), γ (M x) · γ x = # F (μ M x) · γ x).

    Definition functor_from_kleisli_cat_enrichment_data
      : functor_enrichment_data
          (functor_from_kleisli_cat_monad M F γ p q)
          Kleisli_cat_monad_enrichment
          E'
      := λ x y, EF x (M y) · postcomp_arr E' (F x) (γ y).

    Proposition functor_from_kleisli_cat_enrichment_laws
      : is_functor_enrichment functor_from_kleisli_cat_enrichment_data.
    Proof.
      repeat split.
      - intros x ; cbn.
        unfold functor_from_kleisli_cat_enrichment_data.
        rewrite !assoc.
        rewrite <- functor_enrichment_from_arr.
        rewrite enriched_from_arr_postcomp.
        etrans.
        {
          apply maponpaths.
          exact (p x).
        }
        rewrite enriched_from_arr_id.
        apply idpath.
      - intros x y z ; cbn.
        unfold functor_from_kleisli_cat_enrichment_data.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            rewrite <- functor_enrichment_postcomp_arr.
            rewrite !assoc'.
            rewrite <- postcomp_arr_comp.
            apply idpath.
          }
          rewrite !assoc.
          rewrite functor_enrichment_comp.
          rewrite !assoc'.
          rewrite enriched_comp_postcomp_arr.
          apply idpath.
        }
        etrans.
        {
          rewrite !assoc.
          rewrite <- !tensor_comp_mor.
          rewrite id_left, id_right.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          rewrite tensor_comp_l_id_r.
          rewrite !assoc'.
          rewrite <- precomp_postcomp_arr_assoc ; cbn.
          rewrite !assoc.
          rewrite <- !tensor_comp_mor.
          rewrite id_right.
          apply idpath.
        }
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- precomp_postcomp_arr.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (nat_trans_enrichment_to_comp Eγ y (M z)).
        }
        cbn.
        rewrite !assoc'.
        rewrite <- postcomp_arr_comp.
        do 3 apply maponpaths.
        apply q.
      - intros x y f ; cbn.
        unfold functor_from_kleisli_cat_enrichment_data.
        rewrite !assoc.
        rewrite <- functor_enrichment_from_arr.
        rewrite enriched_from_arr_postcomp.
        apply idpath.
    Qed.

    Definition functor_from_kleisli_cat_enrichment
      : functor_enrichment
          (functor_from_kleisli_cat_monad M F γ p q)
          Kleisli_cat_monad_enrichment
          E'
      := functor_from_kleisli_cat_enrichment_data
         ,,
         functor_from_kleisli_cat_enrichment_laws.

    Proposition functor_from_kleisli_cat_monad_nat_trans_enrichment
      : nat_trans_enrichment
          (functor_from_kleisli_cat_monad_nat_trans M F γ p q)
          (functor_comp_enrichment
             Left_Kleisli_functor_enrichment
             functor_from_kleisli_cat_enrichment)
          EF.
    Proof.
      use nat_trans_enrichment_via_comp.
      intros x y ; cbn.
      rewrite precomp_arr_id, postcomp_arr_id.
      rewrite !id_right.
      unfold functor_from_kleisli_cat_enrichment_data.
      rewrite !assoc.
      rewrite <- functor_enrichment_postcomp_arr.
      rewrite !assoc'.
      rewrite <- postcomp_arr_comp.
      refine (!(id_right _) @ !_).
      apply maponpaths.
      refine (_ @ postcomp_arr_id _ _ _).
      apply maponpaths.
      apply p.
    Qed.
  End FunctorFromKleisli.

  (** * 5. Natural transformations from the Kleisli category *)
  Proposition nat_trans_from_kleisli_cat_monad_enrichment
              {C' : category}
              (E' : enrichment C' V)
              {G₁ G₂ : Kleisli_cat_monad M ⟶ C'}
              (EG₁ : functor_enrichment G₁ Kleisli_cat_monad_enrichment E')
              (EG₂ : functor_enrichment G₂ Kleisli_cat_monad_enrichment E')
              {α : Left_Kleisli_functor M ∙ G₁ ⟹ Left_Kleisli_functor M ∙ G₂}
              (Eα : nat_trans_enrichment
                      α
                      (functor_comp_enrichment
                         Left_Kleisli_functor_enrichment
                         EG₁)
                      (functor_comp_enrichment
                         Left_Kleisli_functor_enrichment
                         EG₂))
              (p : ∏ (x : C),
                   # G₁ (kleisli_monad_nat_trans M x) · α x
                   =
                   α (M x) · # G₂ (kleisli_monad_nat_trans M x))
    : nat_trans_enrichment
        (nat_trans_from_kleisli_cat_monad M α p)
        EG₁
        EG₂.
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    pose (maponpaths
            (λ z, z · postcomp_arr _ _ (#G₂ (kleisli_monad_nat_trans M y)))
            (nat_trans_enrichment_to_comp Eα x _))
      as q ; cbn in q.
    refine (_ @ q @ _) ; clear q.
    - rewrite !assoc'.
      rewrite precomp_postcomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply (functor_enrichment_postcomp_arr EG₂).
      }
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      rewrite Kleisli_cat_enrichment_postcomp_arr.
      refine (!(postcomp_arr_comp E _ _) @ _ @ postcomp_arr_id _ _ _).
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (!(nat_trans_ax (η M) _ _ _)).
      }
      cbn.
      rewrite id_left.
      apply Monad_law1.
    - rewrite !assoc'.
      rewrite <- postcomp_arr_comp.
      etrans.
      {
        do 3 apply maponpaths.
        exact (!(p y)).
      }
      cbn.
      rewrite postcomp_arr_comp.
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (functor_enrichment_postcomp_arr EG₁).
      }
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      rewrite Kleisli_cat_enrichment_postcomp_arr.
      refine (!(postcomp_arr_comp E _ _) @ _ @ postcomp_arr_id _ _ _).
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (!(nat_trans_ax (η M) _ _ _)).
      }
      cbn.
      rewrite id_left.
      apply Monad_law1.
  Qed.
End EnrichedKleisli.
