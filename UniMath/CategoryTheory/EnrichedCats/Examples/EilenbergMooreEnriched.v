(**********************************************************************

 The enriched Eilenberg-Moore category

 In this file, we construct an enrichment for the Eilenberg-Moore
 category. To do so, we make use of the fact that we already
 constructed enrichments for the full subcategory and for the category
 of dialgebras. In addition, we construct the relevant functors and
 natural transformation to prove the universal property.

 Contents
 1. The enrichment of the Eilenberg-Moore category
 2. The cone
 3. The universal property

 **********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.categories.EilenbergMoore.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.DialgebraEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FullSubEnriched.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.terminal.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedEilenbergMoore.
  Context {V : monoidal_cat}
          (HV : Equalizers V)
          {C : category}
          {E : enrichment C V}
          {M : Monad C}
          (EM : monad_enrichment E M).

  (**
   1. The enrichment of the Eilenberg-Moore category
   *)
  Definition eilenberg_moore_enrichment
    : enrichment (eilenberg_moore_cat M) V.
  Proof.
    use fullsub_enrichment.
    use (dialgebra_enrichment _ HV).
    - exact E.
    - exact E.
    - exact EM.
    - exact (functor_id_enrichment E).
  Defined.

  (**
   2. The cone
   *)
  Definition eilenberg_moore_pr_enrichment
    : functor_enrichment
        (eilenberg_moore_pr M)
        eilenberg_moore_enrichment
        E.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _).
    - exact (λ x y, dialgebra_pr1_enrichment V HV _ _ (pr1 x) (pr1 y)).
    - abstract
        (intros x ; cbn ;
         apply dialgebra_enrichment_id_incl).
    - abstract
        (intros x y z ; cbn ;
         apply dialgebra_enrichment_comp_incl).
    - abstract
        (intros x y f ; cbn ;
         refine (!_) ;
         apply dialgebra_enrichment_from_arr_incl).
  Defined.

  Definition eilenberg_moore_nat_trans_enrichment
    : nat_trans_enrichment
        (eilenberg_moore_nat_trans M)
        (functor_comp_enrichment
           eilenberg_moore_pr_enrichment
           EM)
        (functor_comp_enrichment
           (functor_id_enrichment _)
           eilenberg_moore_pr_enrichment).
  Proof.
    intros x y.
    pose (dialgebra_nat_trans_enrichment
            V HV
            EM (functor_id_enrichment _)
            (pr1 x) (pr1 y)).
    refine (_ @ p).
    apply maponpaths_2.
    apply maponpaths.
    cbn.
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  (**
   3. The universal property
   *)
  Section EilenbergMooreUMP1.
    Context {C' : category}
            {E' : enrichment C' V}
            {F : C' ⟶ C}
            (FE  : functor_enrichment F E' E)
            (τ : F ∙ M ⟹ functor_identity _ ∙ F)
            (Eτ : nat_trans_enrichment
                    τ
                    (functor_comp_enrichment FE EM)
                    (functor_comp_enrichment
                       (functor_id_enrichment _)
                       FE))
            (τη : ∏ (x : C'), η M (F x) · τ x = identity _)
            (τμ : ∏ (x : C'), # M (τ x) · τ x = μ M (F x) · τ x).

    Definition functor_to_em_enrichment_mor_eq
               (x y : C')
      : FE x y · dialgebra_enrichment_mor_left V (functor_id_enrichment E) (τ x) (τ y)
        =
        FE x y · @dialgebra_enrichment_mor_right
                    _ _ _ _
                    (functor_identity C)
                    _ _
                    EM
                    (F x) (F y)
                    (τ x) (τ y).
    Proof.
      unfold dialgebra_enrichment_mor_left.
      unfold dialgebra_enrichment_mor_right.
      rewrite !assoc.
      rewrite tensor_rinvunitor.
      rewrite tensor_linvunitor.
      rewrite !assoc'.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_mor.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_mor.
      }
      refine (!_).
      rewrite !id_left, !id_right.
      rewrite !assoc.
      pose (p := Eτ x y).
      cbn in p.
      rewrite id_left in p.
      exact p.
    Qed.

    Definition functor_to_em_enrichment_mor
               (x y : C')
      : E' ⦃ x , y ⦄ --> dialgebra_enrichment_mor V HV EM (functor_id_enrichment E) (τ x) (τ y).
    Proof.
      use EqualizerIn.
      - exact (FE x y).
      - exact (functor_to_em_enrichment_mor_eq x y).
    Defined.

    Definition functor_to_em_enrichment_mor_incl
               (x y : C')
      : functor_to_em_enrichment_mor x y
        · dialgebra_enrichment_mor_incl _ _ _ _ _ _
        =
        FE x y.
    Proof.
      apply EqualizerCommutes.
    Qed.

    Definition functor_to_eilenberg_moore_cat_enrichment
      : functor_enrichment
          (functor_to_eilenberg_moore_cat M F τ τη τμ)
          E'
          eilenberg_moore_enrichment.
    Proof.
      simple refine (_ ,, _ ,, _ ,, _).
      - exact functor_to_em_enrichment_mor.
      - abstract
          (intros x ;
           use (dialgebra_enrichment_mor_eq_of_mor
                  V
                  HV
                  EM (functor_id_enrichment _)) ; cbn ;
           rewrite !assoc' ;
           rewrite functor_to_em_enrichment_mor_incl ;
           refine (_ @ !(dialgebra_enrichment_id_incl _ _ _ _ _)) ;
           apply (functor_enrichment_id FE)).
      - abstract
          (intros x y z ;
           use (dialgebra_enrichment_mor_eq_of_mor
                  V
                  HV
                  EM (functor_id_enrichment _)) ; cbn ;
           rewrite !assoc' ;
           rewrite functor_to_em_enrichment_mor_incl ;
           rewrite dialgebra_enrichment_comp_incl ;
           refine (functor_enrichment_comp FE x y z @ _) ;
           unfold dialgebra_enrichment_comp_mor ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           refine (_ @ tensor_comp_mor _ _ _ _) ;
           rewrite !functor_to_em_enrichment_mor_incl ;
           apply idpath).
      - abstract
          (intros x y f ;
           use (dialgebra_enrichment_mor_eq_of_mor
                  V
                  HV
                  EM (functor_id_enrichment _)) ; cbn ;
           rewrite !assoc' ;
           rewrite functor_to_em_enrichment_mor_incl ;
           refine (dialgebra_enrichment_from_arr_incl _ _ _ _ _ _ @ _) ;
           apply (functor_enrichment_from_arr FE)).
    Defined.

    Definition functor_to_eilenberg_moore_cat_pr_enrichment
      : nat_trans_enrichment
          (functor_to_eilenberg_moore_cat_pr M F τ τη τμ)
          (functor_comp_enrichment
             functor_to_eilenberg_moore_cat_enrichment
             eilenberg_moore_pr_enrichment)
          FE.
    Proof.
      intros x y ; cbn.
      rewrite functor_to_em_enrichment_mor_incl.
      rewrite !enriched_from_arr_id.
      etrans.
      {
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        rewrite tensor_runitor.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_rinvunitor_runitor.
        }
        apply id_left.
      }
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply mon_linvunitor_lunitor.
      }
      apply id_left.
    Qed.

    Definition functor_to_eilenberg_moore_cat_pr_enrichment_inv
      : nat_trans_enrichment
          (nat_z_iso_inv
             (functor_to_eilenberg_moore_cat_pr_nat_z_iso M F τ τη τμ))
          FE
          (functor_comp_enrichment
             functor_to_eilenberg_moore_cat_enrichment
             eilenberg_moore_pr_enrichment).
    Proof.
      intros x y ; cbn.
      rewrite functor_to_em_enrichment_mor_incl.
      rewrite !enriched_from_arr_id.
      etrans.
      {
        rewrite tensor_split'.
        rewrite !assoc'.
        rewrite <- enrichment_id_right.
        rewrite tensor_runitor.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_rinvunitor_runitor.
        }
        apply id_left.
      }
      refine (!_).
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite <- enrichment_id_left.
      rewrite tensor_lunitor.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply mon_linvunitor_lunitor.
      }
      apply id_left.
    Qed.
  End EilenbergMooreUMP1.

  Definition nat_trans_to_eilenberg_moore_cat_enrichment
             {C' : category}
             (E' : enrichment C' V)
             {F₁ F₂ : C' ⟶ eilenberg_moore_cat M}
             {FE₁ : functor_enrichment F₁ E' eilenberg_moore_enrichment}
             {FE₂ : functor_enrichment F₂ E' eilenberg_moore_enrichment}
             (τ : F₁ ∙ eilenberg_moore_pr M ⟹ F₂ ∙ eilenberg_moore_pr M)
             (Eτ : nat_trans_enrichment
                     τ
                     (functor_comp_enrichment FE₁ eilenberg_moore_pr_enrichment)
                     (functor_comp_enrichment FE₂ eilenberg_moore_pr_enrichment))
             (p : ∏ (x : C'),
                  mor_of_eilenberg_moore_ob (F₁ x) · τ x
                  =
                  # M (τ x) · mor_of_eilenberg_moore_ob (F₂ x))
    : nat_trans_enrichment
        (nat_trans_to_eilenberg_moore_cat M F₁ F₂ τ p)
        FE₁
        FE₂.
  Proof.
    intros x y ; cbn.
    use (dialgebra_enrichment_mor_eq_of_mor
           V
           HV
           EM (functor_id_enrichment _)).
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply dialgebra_enrichment_comp_incl.
    }
    unfold dialgebra_enrichment_comp_mor.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      do 2 apply maponpaths.
      apply dialgebra_enrichment_comp_incl.
    }
    unfold dialgebra_enrichment_comp_mor.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply tensor_comp_mor.
    }
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply dialgebra_enrichment_from_arr_incl.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply dialgebra_enrichment_from_arr_incl.
    }
    rewrite !assoc.
    exact (Eτ x y).
  Qed.
End EnrichedEilenbergMoore.
