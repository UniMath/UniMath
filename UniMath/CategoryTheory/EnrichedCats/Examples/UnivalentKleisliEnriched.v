(**********************************************************************

 The enriched univalent Kleisli category

 We construct an enrichment of the univalent Kleisli category. Note
 that since this category is defined as a subcategory of the
 Eilenberg-Moore category, we assume that the monoidal category over
 which we enrich, has equalizers.

 Contents
 1. Enrichment of the free algebra functor
 2. Enrichment of the univalent Kleisli category
 3. Functor to the Kleisli category
 4. Functor between the two different versions of the Kleisli category
 5. The functor is fully faithful

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
Require Import UniMath.CategoryTheory.categories.KleisliCategory.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.DialgebraEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.EilenbergMooreEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.FullSubEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.ImageEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.KleisliEnriched.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.
Require Import UniMath.CategoryTheory.limits.equalizers.

Local Open Scope cat.
Local Open Scope moncat.

Section EnrichedKleisli.
  Context {V : monoidal_cat}
          (HV : Equalizers V)
          {C : category}
          {E : enrichment C V}
          {M : Monad C}
          (EM : monad_enrichment E M).

  (**
   1. Enrichment of the free algebra functor
   *)
  Definition free_alg_enrichment_mor
             (x y : C)
    : E ⦃ x, y ⦄
      -->
      eilenberg_moore_enrichment HV EM ⦃ free_alg_em M x, free_alg_em M y ⦄.
  Proof.
    use EqualizerIn.
    - exact (EM x y).
    - abstract
        (cbn ;
         unfold dialgebra_enrichment_mor_left ;
         unfold dialgebra_enrichment_mor_right ;
         cbn ;
         rewrite id_left ;
         rewrite !assoc ;
         etrans ;
         [ do 2 apply maponpaths_2 ;
           apply tensor_rinvunitor
         | ] ;
         rewrite !assoc' ;
         etrans ;
         [ apply maponpaths ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           exact (!(tensor_split' _ _))
         | ] ;
         rewrite !assoc ;
         refine (mu_of_monad_enrichment EM x y @ _) ;
         apply maponpaths_2 ;
         cbn ;
         refine (!_) ;
         etrans ;
         [ apply maponpaths_2 ;
           apply tensor_linvunitor
         | ] ;
         rewrite !assoc' ;
         apply maponpaths ;
         refine (!_) ;
         apply tensor_split).
  Defined.

  Definition free_alg_enrichment_mor_incl
             (x y : C)
    : free_alg_enrichment_mor x y
      · dialgebra_enrichment_mor_incl V HV EM (functor_id_enrichment E) (μ M x) (μ M y)
      =
      EM x y.
  Proof.
    apply EqualizerCommutes.
  Qed.

  Definition free_alg_enrichment_laws
    : is_functor_enrichment free_alg_enrichment_mor.
  Proof.
    repeat split.
    - intro x.
      use (dialgebra_enrichment_mor_eq_of_mor
             V HV
             EM (functor_id_enrichment E)).
      rewrite !assoc'.
      rewrite free_alg_enrichment_mor_incl.
      refine (!_).
      etrans.
      {
        apply dialgebra_enrichment_id_incl.
      }
      refine (!_).
      apply functor_enrichment_id.
    - intros x y z.
      use (dialgebra_enrichment_mor_eq_of_mor
             V HV
             EM (functor_id_enrichment E)).
      rewrite !assoc'.
      rewrite free_alg_enrichment_mor_incl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply dialgebra_enrichment_comp_incl.
      }
      unfold dialgebra_enrichment_comp_mor.
      cbn.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_mor.
      }
      rewrite !free_alg_enrichment_mor_incl.
      refine (!_).
      apply functor_enrichment_comp.
    - intros x y f.
      use (dialgebra_enrichment_mor_eq_of_mor
             V HV
             EM (functor_id_enrichment E)).
      rewrite !assoc'.
      rewrite free_alg_enrichment_mor_incl.
      etrans.
      {
        apply dialgebra_enrichment_from_arr_incl.
      }
      apply functor_enrichment_from_arr.
  Qed.

  Definition free_alg_enrichment
    : functor_enrichment
        (free_alg_em M)
        E
        (eilenberg_moore_enrichment HV EM).
  Proof.
    simple refine (_ ,, _).
    - exact free_alg_enrichment_mor.
    - exact free_alg_enrichment_laws.
  Defined.

  (**
    2. Enrichment of the univalent Kleisli category
   *)
  Definition Kleisli_cat_enrichment
    : enrichment (kleisli_cat M) V.
  Proof.
    use image_enrichment.
    exact (eilenberg_moore_enrichment HV EM).
  Defined.

  (**
   3. Functor to the Kleisli category
   *)
  Definition kleisli_incl_enrichment
    : functor_enrichment
        (kleisli_incl M)
        E
        Kleisli_cat_enrichment.
  Proof.
    use image_proj_enrichment.
    exact free_alg_enrichment.
  Defined.

  (**
   4. Functor between the two different versions of the Kleisli category
   *)
  Definition functor_to_kleisli_cat_enrichment_mor
             (x y : C)
    : E ⦃ x, M y ⦄ --> E ⦃ M x, M y ⦄
    := mon_linvunitor _
       · enriched_from_arr E (μ M y) #⊗ EM x (M y)
       · enriched_comp E (M x) (M(M y)) (M y).

  Definition functor_to_kleisli_cat_enrichment_eq
             (x y : C)
    : functor_to_kleisli_cat_enrichment_mor x y
      · @dialgebra_enrichment_mor_left
           V C C
           M (functor_identity C)
           E E
           (functor_id_enrichment E)
           (M x) (M y)
           (μ M x) (μ M y)
      =
      functor_to_kleisli_cat_enrichment_mor x y
      · @dialgebra_enrichment_mor_right
           V C C
           M (functor_identity C)
           E E
           EM
           (M x) (M y)
           (μ M x) (μ M y).
  Proof.
    unfold dialgebra_enrichment_mor_left.
    unfold dialgebra_enrichment_mor_right.
    unfold functor_to_kleisli_cat_enrichment_mor.
    cbn.
    rewrite !id_left.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      do 3 apply maponpaths_2.
      apply (functor_enrichment_comp EM).
    }
    rewrite !assoc'.
    etrans.
    {
      do 3 apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply tensor_linvunitor.
      }
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply tensor_split.
        }
        apply tensor_split'.
      }
      rewrite !assoc'.
      apply maponpaths.
      apply enrichment_assoc'.
    }
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply tensor_rinvunitor.
      }
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply tensor_split'.
        }
        apply tensor_split.
      }
      rewrite !assoc'.
      apply maponpaths.
      apply enrichment_assoc.
    }
    apply maponpaths.
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        apply tensor_split'.
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      etrans.
      {
        do 4 apply maponpaths_2.
        apply tensor_rinvunitor.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            do 2 apply maponpaths_2.
            refine (!_).
            apply tensor_id_id.
          }
          apply tensor_lassociator.
        }
        rewrite !assoc.
        apply maponpaths_2.
        apply tensor_lassociator.
      }
      rewrite !assoc.
      etrans.
      {
        do 4 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply mon_rinvunitor_triangle.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply mon_rassociator_lassociator.
        }
        apply id_right.
      }
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply tensor_comp_id_l.
        }
        refine (!_).
        apply tensor_comp_id_l.
      }
      refine (!_).
      apply tensor_comp_id_l.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_mor.
      }
      rewrite id_left, id_right.
      rewrite !assoc.
      exact (mu_of_monad_enrichment EM x (M y)).
    }
    cbn.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_comp_id_l.
      }
      rewrite !assoc'.
      apply maponpaths.
      apply enrichment_assoc'.
    }
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      rewrite !assoc'.
      apply maponpaths.
      apply maponpaths_2.
      apply tensor_comp_id_l.
    }
    etrans.
    {
      rewrite !assoc.
      do 3 apply maponpaths_2.
      refine (!(tensor_split' _ _) @ _).
      apply tensor_split.
    }
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply mon_linvunitor_triangle.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (!(tensor_comp_mor _ _ _ _)).
      }
      refine (!(tensor_comp_mor _ _ _ _) @ _).
      rewrite id_right.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_linvunitor.
      }
      apply tensor_comp_mor.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths.
          refine (!_).
          apply tensor_id_id.
        }
        refine (!_).
        apply tensor_lassociator.
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_lassociator_rassociator.
        }
        apply id_left.
      }
      etrans.
      {
        apply maponpaths.
        refine (!(tensor_comp_mor _ _ _ _) @ _).
        rewrite id_left.
        apply idpath.
      }
      refine (!(tensor_comp_mor _ _ _ _) @ _).
      rewrite id_right.
      apply maponpaths_2.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(tensor_split _ _) @ _).
      apply idpath.
    }
    assert (enriched_from_arr E (μ M y) #⊗ (enriched_from_arr E (μ M y) · EM (M (M y)) (M y))
            · enriched_comp E (M (M (M y))) (M (M y)) (M y)
            =
            enriched_from_arr E (μ M y) #⊗ enriched_from_arr E (μ M (M y))
            · enriched_comp E (M (M (M y))) (M (M y)) (M y))
      as p.
    {
      pose (maponpaths
              (λ z, mon_lunitor _ · enriched_from_arr E z)
              (@Monad_law3 _ M y))
        as p.
      cbn in p.
      rewrite !enriched_from_arr_comp in p.
      rewrite (functor_enrichment_from_arr EM) in p.
      rewrite !assoc in p.
      refine (_ @ p @ _).
      - refine (!(id_left _) @ _).
        rewrite !assoc.
        do 2 apply maponpaths_2.
        refine (!_).
        apply mon_lunitor_linvunitor.
      - refine (_ @ id_left _).
        rewrite !assoc.
        do 2 apply maponpaths_2.
        apply mon_lunitor_linvunitor.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact p.
    }
    clear p.
    etrans.
    {
      apply maponpaths.
      apply tensor_comp_r_id_r.
    }
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply tensor_rassociator.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        refine (!_).
        apply tensor_id_id.
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_rassociator.
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (!(tensor_comp_mor _ _ _ _) @ _).
      rewrite id_left.
      etrans.
      {
        apply maponpaths_2.
        exact (!(tensor_split' _ _)).
      }
      apply tensor_comp_l_id_l.
    }
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply mon_inv_triangle.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply mon_lassociator_rassociator.
      }
      apply id_right.
    }
    etrans.
    {
      refine (!_).
      apply tensor_split'.
    }
    apply maponpaths_2.
    apply mon_rinvunitor_I_mon_linvunitor_I.
  Qed.

  Definition functor_to_kleisli_cat_enrichment_data
             (x y : C)
    :  E ⦃ x, M y ⦄
       -->
       dialgebra_enrichment_mor V HV EM (functor_id_enrichment E) (μ M x) (μ M y).
  Proof.
    use EqualizerIn.
    - exact (functor_to_kleisli_cat_enrichment_mor x y).
    - exact (functor_to_kleisli_cat_enrichment_eq x y).
  Defined.

  Definition functor_to_kleisli_cat_enrichment_data_incl
             (x y : C)
    : functor_to_kleisli_cat_enrichment_data x y
      · dialgebra_enrichment_mor_incl _ _ _ _ _ _
      =
      functor_to_kleisli_cat_enrichment_mor x y.
  Proof.
    apply EqualizerCommutes.
  Qed.

  Definition functor_to_kleisli_cat_enrichment_is_enrichment
    : @is_functor_enrichment
        _ _ _
        (functor_to_kleisli_cat M)
        (Kleisli_cat_monad_enrichment EM)
        Kleisli_cat_enrichment
        functor_to_kleisli_cat_enrichment_data.
  Proof.
    repeat split.
    - intros x ; cbn.
      use (dialgebra_enrichment_mor_eq_of_mor
             V HV
             EM (functor_id_enrichment E)).
      refine (!_).
      refine (dialgebra_enrichment_id_incl _ _ _ _ _ @ _).
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply functor_to_kleisli_cat_enrichment_data_incl.
      }
      unfold functor_to_kleisli_cat_enrichment_mor.
      rewrite <- enriched_from_arr_id.
      rewrite <- (@Monad_law2 _ M x).
      rewrite enriched_from_arr_comp ; cbn.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_linvunitor.
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (!(tensor_comp_mor _ _ _ _) @ _).
      rewrite id_left.
      apply maponpaths.
      rewrite <- (functor_enrichment_from_arr EM).
      apply idpath.
    - (**
       The proof for this goal is in essence that for all

         f : x --> M y
         g : y --> M z

       we have

       (#M f · μ M y) · (#M g · μ M z)
       =
       #M f · (μ M y · (#M g · μ M z))
       =
       #M f · ((μ M y · #M g) · μ M z)
       =
       #M f · ((#M (#M g) · μ M z) · μ M z)
       =
       #M f · (#M (#M g) · (μ M z · μ M z))
       =
       (#M f · #M (#M g)) · (μ M z · μ M z))
       =
       #M (f · #M g) · (μ M z · μ M z)
       =
       #M(f · #M g) · (#M (μ M z) · μ M z)
       =
       (#M(f · #M g) · #M (μ M z)) · μ M z
       =
       #M((f · #M g) · μ M z) · μ M z
       *)
      intros x y z ; cbn.
      use (dialgebra_enrichment_mor_eq_of_mor
             V HV
             EM (functor_id_enrichment E)).
      rewrite !assoc'.
      etrans.
      {
        do 5 apply maponpaths.
        apply functor_to_kleisli_cat_enrichment_data_incl.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply dialgebra_enrichment_comp_incl.
      }
      unfold dialgebra_enrichment_comp_mor.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        refine (!(tensor_comp_mor _ _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          apply functor_to_kleisli_cat_enrichment_data_incl.
        }
        apply maponpaths_2.
        apply functor_to_kleisli_cat_enrichment_data_incl.
      }
      unfold functor_to_kleisli_cat_enrichment_mor.
      rewrite !assoc'.
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc.
          apply tensor_comp_l_id_r.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc'.
      }
      rewrite !assoc'.
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite tensor_comp_mor.
          rewrite !assoc'.
          apply maponpaths.
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_split.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!(tensor_comp_id_r _ _) @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_split.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc.
      }
      cbn.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          do 3 apply maponpaths_2.
          etrans.
          {
            do 2 apply maponpaths_2.
            refine (!_).
            apply tensor_id_id.
          }
          apply tensor_lassociator.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc'.
          apply tensor_comp_id_r.
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(tensor_comp_mor _ _ _ _) @ _).
        rewrite id_right.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            refine (!_).
            apply tensor_id_id.
          }
          apply maponpaths_2.
          refine (!_).
          apply tensor_id_id.
        }
        apply tensor_lassociator.
      }
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply tensor_split'.
        }
        rewrite !assoc.
        apply tensor_split.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc.
          apply tensor_comp_id_r.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            refine (!_).
            apply tensor_id_id.
          }
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!(tensor_comp_mor _ _ _ _) @ _).
          rewrite id_left.
          rewrite !assoc.
          etrans.
          {
            do 2 apply maponpaths_2.
            apply tensor_lassociator.
          }
          rewrite !assoc'.
          apply tensor_split'.
        }
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_comp_r_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths.
          apply tensor_comp_id_r.
        }
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!(tensor_comp_mor _ _ _ _) @ _).
          rewrite id_left, id_right.
          apply idpath.
        }
        refine (!(tensor_comp_mor _ _ _ _) @ _).
        rewrite id_right.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply tensor_comp_id_l.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply tensor_comp_id_l.
        }
        etrans.
        {
          refine (!_).
          apply tensor_comp_id_l.
        }
        apply maponpaths.
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            apply maponpaths_2.
            exact (!(tensor_split' _ _)).
          }
          rewrite !assoc.
          apply maponpaths_2.
          exact (!(tensor_split' _ _)).
        }
        pose (maponpaths
                (λ z, mon_runitor _ · z)
                (mu_of_monad_enrichment EM y (M z))) as p.
        cbn in p.
        refine (_ @ p).
        refine (!_).
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply mon_runitor_rinvunitor.
        }
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc'.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply tensor_comp_id_l.
          }
          apply tensor_split.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!(tensor_comp_id_r _ _) @ _).
        rewrite !assoc'.
        apply maponpaths_2.
        apply maponpaths.
        apply enrichment_assoc'.
      }
      rewrite !assoc'.
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_id_r.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc.
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!(tensor_comp_mor _ _ _ _) @ _).
          rewrite id_right.
          rewrite id_left.
          rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths_2.
            apply maponpaths.
            rewrite assoc.
            apply maponpaths.
            apply tensor_comp_l_id_r.
          }
          etrans.
          {
            apply maponpaths_2.
            rewrite !assoc.
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths_2.
                apply tensor_comp_id_l.
              }
              rewrite !assoc'.
              apply maponpaths.
              apply tensor_rassociator.
            }
            rewrite !assoc'.
            do 2 apply maponpaths.
            etrans.
            {
              do 2 apply maponpaths_2.
              apply tensor_id_id.
            }
            refine (!(tensor_split _ _) @ _).
            apply tensor_split'.
          }
          rewrite !assoc.
          refine (tensor_comp_r_id_l _ _ _ @ _).
          apply idpath.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_lassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine ((!tensor_comp_id_l _ _) @ _).
        apply maponpaths.
        exact (!(functor_enrichment_comp EM x (M y) (M(M z)))).
      }
      refine (!_).
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_linvunitor.
        }
        rewrite assoc'.
        apply maponpaths.
        refine (!(tensor_comp_mor _ _ _ _) @ _).
        rewrite id_left.
        apply maponpaths.
        exact (functor_enrichment_comp EM x (M(M z)) (M z)).
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_l_id_r.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc'.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc'.
        do 5 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!(tensor_comp_mor _ _ _ _) @ _).
        rewrite id_right.
        etrans.
        {
          apply tensor_comp_r_id_l.
        }
        apply maponpaths.
        apply tensor_split'.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply tensor_comp_id_l.
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 5 apply maponpaths_2.
          apply tensor_linvunitor.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 4 apply maponpaths_2.
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply mon_linvunitor_triangle.
          }
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply mon_lassociator_rassociator.
          }
          apply id_right.
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!(tensor_split _ _) @ _).
        apply tensor_split'.
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply maponpaths_2.
            etrans.
            {
              do 2 apply maponpaths_2.
              apply tensor_comp_id_l.
            }
            rewrite !assoc'.
            apply tensor_comp_id_r.
          }
          rewrite !assoc.
          do 2 apply maponpaths_2.
          refine (!(tensor_comp_id_r _ _) @ _).
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply mon_runitor_triangle.
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply mon_lassociator_rassociator.
          }
          apply id_left.
        }
        rewrite !assoc.
        do 2 apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply mon_triangle.
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_rassociator_lassociator.
        }
        apply id_left.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        refine (!(tensor_split' _ _) @ _).
        apply tensor_split.
      }
      etrans.
      {
        rewrite !assoc.
        do 2 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!(tensor_comp_id_l _ _) @ _).
          etrans.
          {
            apply maponpaths.
            apply mon_linvunitor_lunitor.
          }
          apply tensor_id_id.
        }
        apply id_left.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_comp_id_r.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        apply mon_linvunitor_triangle.
      }
      etrans.
      {
        rewrite !assoc.
        do 5 apply maponpaths_2.
        refine (!(tensor_comp_id_r _ _) @ _).
        etrans.
        {
          apply maponpaths_2.
          apply tensor_linvunitor.
        }
        apply tensor_comp_id_r.
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc'.
          apply tensor_comp_id_r.
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(tensor_comp_id_r _ _) @ _).
        apply maponpaths_2.
        refine (!(tensor_split' _ _) @ _).
        refine (tensor_split _ _ @ _).
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply tensor_split.
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply tensor_linvunitor.
      }
      etrans.
      {
        do 4 apply maponpaths_2.
        rewrite !assoc'.
        apply tensor_comp_id_l.
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        apply tensor_comp_id_r.
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      assert (enriched_from_arr E (μ M z) #⊗ enriched_from_arr E (# M (μ M z))
              · enriched_comp E (M (M (M z))) (M (M z)) (M z)
              =
              enriched_from_arr E (μ M z) #⊗ enriched_from_arr E (μ M (M z))
              · enriched_comp E (M (M (M z))) (M (M z)) (M z))
        as p.
      {
        pose (p := maponpaths
                     (λ z, mon_lunitor _ · enriched_from_arr E z)
                     (@Monad_law3 _ M z)).
        cbn in p.
        rewrite !enriched_from_arr_comp in p.
        refine (_ @ p @ _).
        - rewrite !assoc.
          apply maponpaths_2.
          refine (!(id_left _) @ _).
          apply maponpaths_2.
          refine (!_).
          apply mon_lunitor_linvunitor.
        - rewrite !assoc.
          apply maponpaths_2.
          refine (_ @ id_left _).
          apply maponpaths_2.
          apply mon_lunitor_linvunitor.
      }
      etrans.
      {
        apply maponpaths_2.
        refine (!(tensor_comp_id_r _ _) @ _).
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              apply maponpaths.
              refine (!_).
              apply tensor_id_id.
            }
            apply tensor_rassociator.
          }
          rewrite !assoc'.
          apply maponpaths.
          exact (!(tensor_comp_id_r _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          rewrite !assoc.
          apply maponpaths_2.
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!(tensor_comp_id_r _ _) @ _).
        apply maponpaths_2.
        etrans.
        {
          rewrite !assoc.
          apply maponpaths_2.
          exact (!(tensor_split _ _)).
        }
        exact (!p).
      }
      clear p.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          exact (!(tensor_comp_id_r _ _)).
        }
        etrans.
        {
          do 2 apply maponpaths.
          exact (!(tensor_comp_id_r _ _)).
        }
        etrans.
        {
          apply maponpaths.
          exact (!(tensor_comp_id_r _ _)).
        }
        etrans.
        {
          do 2 apply maponpaths.
          exact (!(tensor_id_id _ _)).
        }
        refine (!_).
        apply tensor_lassociator.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply mon_inv_triangle.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply mon_lassociator_rassociator.
        }
        apply id_right.
      }
      refine (!(tensor_comp_id_r _ _) @ _).
      apply maponpaths_2.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply tensor_linvunitor.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths_2.
        apply mon_linvunitor_I_mon_rinvunitor_I.
      }
      apply maponpaths.
      refine (!(tensor_comp_mor _ _ _ _) @ _).
      rewrite id_left.
      apply maponpaths.
      refine (!_).
      apply (functor_enrichment_from_arr EM).
    - intros x y f ; cbn.
      use (dialgebra_enrichment_mor_eq_of_mor
             V HV
             EM (functor_id_enrichment E)).
      unfold bind.
      refine (dialgebra_enrichment_from_arr_incl _ _ _ _ _ _ @ _).
      rewrite !assoc'.
      refine (!_).
      etrans ;
        [ apply maponpaths ;
          apply functor_to_kleisli_cat_enrichment_data_incl
        | ].
      unfold functor_to_kleisli_cat_enrichment_mor.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply (@Monad_law2 _ M y).

        }
        apply id_right.
      }
      rewrite enriched_from_arr_comp.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply tensor_linvunitor.
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (!(tensor_comp_mor _ _ _ _) @ _).
      rewrite id_left.
      apply maponpaths.
      rewrite (functor_enrichment_from_arr EM).
      apply idpath.
  Qed.

  Definition functor_to_kleisli_cat_enrichment
    : functor_enrichment
        (functor_to_kleisli_cat M)
        (Kleisli_cat_monad_enrichment EM)
        Kleisli_cat_enrichment.
  Proof.
    simple refine (_ ,, _).
    - exact functor_to_kleisli_cat_enrichment_data.
    - exact functor_to_kleisli_cat_enrichment_is_enrichment.
  Defined.

  (**
   5. The functor is fully faithful
   *)
  Section FullyFaithfulToKleisli.
    Context (x y : C).

    Definition functor_to_kleisli_cat_enrichment_inv
      : Kleisli_cat_enrichment ⦃ functor_to_kleisli_cat M x, functor_to_kleisli_cat M y ⦄
        -->
        Kleisli_cat_monad_enrichment EM ⦃ x, y ⦄
      := dialgebra_enrichment_mor_incl _ _ _ _ _ _
         · mon_rinvunitor _
         · (identity _ #⊗ enriched_from_arr E (η M x))
         · enriched_comp E x (M x) (M y).

    Local Lemma functor_to_kleisli_cat_enrichment_inv_right
      : functor_to_kleisli_cat_enrichment_data x y
        · functor_to_kleisli_cat_enrichment_inv
        =
        identity _.
    Proof.
      unfold functor_to_kleisli_cat_enrichment_inv.
      cbn.
      rewrite !assoc.
      etrans.
      {
        do 3 apply maponpaths_2.
        apply functor_to_kleisli_cat_enrichment_data_incl.
      }
      unfold functor_to_kleisli_cat_enrichment_mor.
      (*
       We show that for all

         f : x --> M y

       we have

         η M x · (#M f · μ M y)
         =
         f
       *)
      rewrite !assoc'.
      (*
       η M x · (#M f · μ M y)
       =
       (η M x · #M f) · μ M y
       *)
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_rinvunitor.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!(tensor_split' _ _) @ _).
          apply tensor_split.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_lassociator.
        }
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply mon_rinvunitor_triangle.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply mon_rassociator_lassociator.
        }
        apply id_right.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply tensor_split'.
      }
      rewrite !assoc'.
      (*
       (η M x · #M f) · μ M y
       =
       (f · η M y) · μ M y
       *)
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          exact (!(tensor_comp_id_l _ _)).
        }
        etrans.
        {
          apply maponpaths.
          exact (!(tensor_comp_id_l _ _)).
        }
        refine (!(tensor_comp_id_l _ _) @ _).
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_rinvunitor.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          exact (!(tensor_split' _ _)).
        }
        rewrite !assoc.
        exact (unit_of_monad_enrichment EM x (M y)).
      }
      cbn.
      (*
       (f · η M y) · μ M y
       =
       f · (η M y · μ M y)
       *)
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc'.
      }
      (*
       f · (η M y · μ M y)
       =
       f · id
       *)
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              apply tensor_comp_id_l.
            }
            rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply tensor_rassociator.
            }
            rewrite !assoc.
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              apply mon_inv_triangle.
            }
            rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              apply mon_lassociator_rassociator.
            }
            apply id_right.
          }
          etrans.
          {
            apply maponpaths.
            exact (!(tensor_comp_id_r _ _)).
          }
          refine (!(tensor_comp_id_r _ _) @ _).
          apply maponpaths_2.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply tensor_rinvunitor.
          }
          rewrite mon_rinvunitor_I_mon_linvunitor_I.
          rewrite !assoc'.
          apply maponpaths.
          exact (!(tensor_split' _ _)).
        }
        refine (!(tensor_comp_id_r _ _) @ _).
        apply maponpaths_2.
        pose (p := maponpaths (enriched_from_arr E) (@Monad_law1 _ M y)).
        rewrite enriched_from_arr_id in p.
        rewrite enriched_from_arr_comp in p.
        cbn in p.
        exact p.
      }
      (*
       f · id = f
       *)
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_left.
      }
      apply mon_linvunitor_lunitor.
    Qed.

    Local Lemma functor_to_kleisli_cat_enrichment_inv_left
      : functor_to_kleisli_cat_enrichment_inv
        · functor_to_kleisli_cat_enrichment_data x y
        =
        identity _.
    Proof.
      use (dialgebra_enrichment_mor_eq_of_mor
             V HV
             EM (functor_id_enrichment E)).
      rewrite id_left.
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        apply functor_to_kleisli_cat_enrichment_data_incl.
      }
      unfold functor_to_kleisli_cat_enrichment_mor.
      unfold functor_to_kleisli_cat_enrichment_inv.
      cbn.
      rewrite !assoc'.
      pose (dialgebra_enrichment_mor_incl_eq
              V HV
              EM (functor_id_enrichment E)
              (μ M x) (μ M y))
        as p.
      unfold dialgebra_enrichment_mor_right in p.
      cbn in p.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          do 2 apply maponpaths_2.
          apply tensor_linvunitor.
        }
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          refine (!(tensor_comp_mor _ _ _ _) @ _).
          rewrite id_left.
          apply maponpaths.
          apply (functor_enrichment_comp EM).
        }
        etrans.
        {
          do 2 apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply mon_linvunitor_triangle.
          }
          rewrite !assoc'.
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply tensor_comp_l_id_r.
          }
          rewrite !assoc.
          apply maponpaths_2.
          refine (!_).
          apply tensor_lassociator.
        }
        rewrite !assoc'.
        etrans.
        {
          do 4 apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply enrichment_assoc'.
          }
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply mon_lassociator_rassociator.
          }
          apply id_left.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          exact (!(tensor_comp_mor _ _ _ _)).
        }
        rewrite id_right.
        etrans.
        {
          do 2 apply maponpaths.
          exact (!(tensor_comp_mor _ _ _ _)).
        }
        rewrite id_left.
        etrans.
        {
          apply maponpaths.
          exact (!(tensor_comp_mor _ _ _ _)).
        }
        rewrite id_left.
        etrans.
        {
          apply maponpaths.
          apply tensor_split'.
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply tensor_rinvunitor.
      }
      rewrite !assoc.
      etrans.
      {
        do 3 apply maponpaths_2.
        refine (_ @ !p).
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          apply tensor_linvunitor.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!_).
        apply tensor_split.
      }
      refine (_ @ id_right _).
      rewrite !assoc'.
      apply maponpaths.
      clear p.
      unfold dialgebra_enrichment_mor_left ; cbn.
      (*
       For all

         f : M x --> M y

       we have

         #M (η M x) · (μ M x · f)
         =
         f
       *)
      rewrite id_left.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_rinvunitor.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!(tensor_split' _ _) @ _).
          apply tensor_split.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc.
      }
      pose (p := maponpaths (enriched_from_arr E) (@Monad_law2 _ M x)).
      rewrite enriched_from_arr_id in p.
      rewrite enriched_from_arr_comp in p.
      rewrite (functor_enrichment_from_arr EM) in p.
      cbn in p.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(tensor_id_id _ _)).
        }
        apply tensor_lassociator.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        do 3 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply mon_rinvunitor_triangle.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply mon_rassociator_lassociator.
        }
        apply id_right.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(tensor_comp_id_l _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (!(tensor_comp_id_l _ _)).
        }
        refine (!(tensor_comp_id_l _ _) @ _).
        apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_rinvunitor.
        }
        rewrite mon_rinvunitor_I_mon_linvunitor_I.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          exact (!(tensor_split' _ _)).
        }
        rewrite !assoc.
        exact p.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_right.
      }
      apply mon_rinvunitor_runitor.
    Qed.
  End FullyFaithfulToKleisli.

  Definition fully_faithful_functor_to_kleisli_cat_enrichment
    : fully_faithful_enriched_functor functor_to_kleisli_cat_enrichment.
  Proof.
    intros x y.
    use make_is_z_isomorphism.
    - exact (functor_to_kleisli_cat_enrichment_inv x y).
    - split.
      + exact (functor_to_kleisli_cat_enrichment_inv_right x y).
      + exact (functor_to_kleisli_cat_enrichment_inv_left x y).
  Defined.
End EnrichedKleisli.
