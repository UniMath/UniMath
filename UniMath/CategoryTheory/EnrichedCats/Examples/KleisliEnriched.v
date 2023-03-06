(**********************************************************************

 The enriched Kleisli category

 In this file we define an enrichment of the Kleisli category (that is
 not guaranteed to be univalent).

 Contents
 1. Data of the enrichment
 2. The laws of the enrichment
 3. The enrichment

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
Require Import UniMath.CategoryTheory.MonoidalOld.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.KleisliCategory.

Local Open Scope cat.
Local Open Scope moncat.

Opaque mon_linvunitor mon_rinvunitor mon_rassociator.

Section EnrichedKleisli.
  Context {V : monoidal_cat}
          {C : category}
          {E : enrichment C V}
          {M : Monad C}
          (EM : monad_enrichment E M).

  (**
   1. Data of the enrichment
   *)
  Definition Kleisli_cat_monad_enrichment_data
    : enrichment_data (Kleisli_cat_monad M) V.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x y, E ⦃ x , M y ⦄).
    - exact (λ x, enriched_from_arr E (η M x)).
    - exact (λ x y z,
             endo_of_monad_enrichment EM y (M z) #⊗ identity _
             · enriched_comp E x (M y) (M(M z))
             · mon_linvunitor _
             · enriched_from_arr E (μ M z) #⊗ identity _
             · enriched_comp E x (M (M z)) (M z)).
    - exact (λ x y f, enriched_from_arr E (f · η M y)).
    - exact (λ x y f, enriched_to_arr E f).
  Defined.

  (**
   2. The laws of the enrichment
   *)
  Definition Kleisli_cat_monad_enrichment_laws
    : enrichment_laws Kleisli_cat_monad_enrichment_data.
  Proof.
    repeat split.
    - intros x y ; cbn.
      refine (enrichment_id_left _ _ _ @ _).
      etrans.
      {
        rewrite <- (enriched_from_arr_id E (M y)).
        rewrite <- (@Monad_law2 _ M y).
        rewrite enriched_from_arr_comp.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc.
        etrans.
        {
          do 4 apply maponpaths_2.
          refine (!_).
          apply tensor_comp_mor.
        }
        rewrite id_right.
        rewrite <- (functor_enrichment_from_arr EM).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          do 2 apply maponpaths_2.
          apply tensor_linvunitor.
        }
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply tensor_split.
          }
          rewrite tensor_split'.
          rewrite !assoc'.
          apply maponpaths.
          apply enrichment_assoc'.
        }
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        rewrite tensor_split.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        refine (!_).
        apply tensor_linvunitor.
      }
      rewrite !assoc'.
      rewrite tensor_comp_id_r.
      apply maponpaths.
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
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
      rewrite !assoc.
      etrans.
      {
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
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply tensor_comp_id_r.
      }
      refine (!(tensor_comp_id_r _ _) @ _).
      apply idpath.
    - intros x y ; cbn.
      rewrite !assoc'.
      refine (_ @ id_left _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply mon_runitor_rinvunitor.
      }
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          do 4 apply maponpaths_2.
          refine (!_).
          apply tensor_split.
        }
        rewrite !assoc.
        do 3 apply maponpaths_2.
        exact (unit_of_monad_enrichment EM x (M y)).
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_linvunitor.
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
        apply enrichment_assoc'.
      }
      rewrite !assoc'.
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
        etrans.
        {
          do 3 apply maponpaths_2.
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
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply mon_lassociator_rassociator.
        }
        apply id_left.
      }
      pose (maponpaths
              (enriched_from_arr E)
              (@Monad_law1 _ M y))
        as p.
      rewrite enriched_from_arr_id in p.
      rewrite enriched_from_arr_comp in p.
      refine (_ @ mon_linvunitor_lunitor _).
      apply maponpaths.
      refine (_ @ !(enrichment_id_left _ _ _)).
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply tensor_comp_id_r.
          }
          refine (!_).
          apply tensor_comp_id_r.
        }
        refine (!_).
        apply tensor_comp_id_r.
      }
      apply maponpaths_2.
      refine (_ @ p).
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        rewrite tensor_split.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply tensor_linvunitor.
    - intros w x y z ; cbn.
      (*
       The equation basically says that for all

         f : w --> M x
         g : x --> M y
         h : y --> M z

       we have

         (f · #M ((g · #M h) · μ M z)) · μ M z
         =
         ((f · #M g) · μ M y) · #M h · μ M z
       *)
      rewrite !assoc'.
      (*
       (f · #M ((g · #M h) · μ M z)) · μ M z
       =
       f · (#M ((g · #M h) · μ M z) · μ M z)
       *)
      etrans.
      {
        do 2 apply maponpaths.
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
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc'.
      }
      refine (!_).
      (*
       ((f · #M g) · μ M y) · #M h · μ M z
       =
       ((f · #M g) · μ M y) · (#M h · μ M z)
       *)
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
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc'.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        rewrite !assoc.
        apply maponpaths_2.
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
            apply maponpaths.
            exact (!(tensor_comp_id_r _ _)).
          }
          exact (!(tensor_comp_id_r _ _)).
        }
        refine (!(tensor_split) _ _ @ _).
        apply tensor_split'.
      }
      (*
       ((f · #M g) · μ M y) · (#M h · μ M z)
       =
       (f · #M g) · (μ M y · (#M h · μ M z))
       *)
      etrans.
      {
        rewrite !assoc'.
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc.
          apply tensor_comp_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          rewrite !assoc.
          apply maponpaths_2.
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc'.
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
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        rewrite !assoc.
        apply maponpaths_2.
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
          apply tensor_comp_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
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
      rewrite !assoc'.
      (*
       (f · #M g) · (μ M y · (#M h · μ M z))
       =
       f · (#M g · (μ M y · (#M h · μ M z)))
       *)
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (!(tensor_comp_id_r _ _)).
          }
          etrans.
          {
            apply maponpaths_2.
            exact (!(tensor_comp_id_r _ _)).
          }
          exact (!(tensor_comp_id_r _ _)).
        }
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
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        do 2 apply maponpaths.
        apply enrichment_assoc'.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      (*
       Simplify so that `w` does not occur in the equation
       *)
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        rewrite assoc.
        apply maponpaths_2.
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
        exact (!(tensor_comp_id_r _ _)).
      }
      refine (!_).
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (!(tensor_id_id _ _)).
        }
        apply tensor_rassociator.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        apply tensor_rassociator.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        do 3 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (!(tensor_id_id _ _)).
        }
        apply tensor_rassociator.
      }
      etrans.
      {
        rewrite !assoc.
        etrans.
        {
          do 4 apply maponpaths_2.
          apply mon_lassociator_rassociator.
        }
        rewrite id_left.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(tensor_comp_id_r _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (!(tensor_comp_id_r _ _)).
        }
        exact (!(tensor_comp_id_r _ _)).
      }
      apply maponpaths_2.
      clear w.
      (*
       We simplified the equation, and now we need to show that for all

         g : x --> M y
         h : y --> M z

       we have

         #M ((g · #M h) · μ M z) · μ M z
         =
         #M g · (μ M y · (#M h · μ M z))
       *)
      rewrite !assoc'.
      refine (!_).
      (*
         #M ((g · #M h) · μ M z) · μ M z
         =
         (#M (g · #M h) · #M (μ M z)) · μ M z
       *)
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        do 3 apply maponpaths_2.
        apply (functor_enrichment_comp EM).
      }
      rewrite !assoc'.
      (*
         (#M (g · #M h) · #M (μ M z)) · μ M z
         =
         #M (g · #M h) · (#M (μ M z) · μ M z)
       *)
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_linvunitor.
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
        apply enrichment_assoc'.
      }
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !assoc.
        do 2 apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        rewrite !assoc.
        apply maponpaths_2.
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
      (*
         #M (g · #M h) · (#M (μ M z) · μ M z)
         =
         (#M g · #M(#M h)) · (#M (μ M z) · μ M z)
       *)
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 6 apply maponpaths_2.
          apply tensor_linvunitor.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 5 apply maponpaths_2.
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        do 4 apply maponpaths_2.
        refine (!(tensor_comp_mor _ _ _ _) @ _).
        rewrite id_left.
        apply maponpaths.
        apply (functor_enrichment_comp EM).
      }
      (*
         (#M g · #M(#M h)) · (#M (μ M z) · μ M z)
         =
         #M g · (#M(#M h) · (#M (μ M z) · μ M z))
       *)
      etrans.
      {
        rewrite !assoc'.
        do 3 apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_l_id_r.
        }
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          rewrite !assoc.
          do 3 apply maponpaths_2.
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          rewrite !assoc.
          do 2 apply maponpaths_2.
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        etrans.
        {
          rewrite !assoc.
          apply maponpaths_2.
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc'.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        do 5 apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply tensor_split.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          refine (!(tensor_split' _ _) @ _).
          apply tensor_split.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply tensor_linvunitor.
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!(tensor_comp_mor _ _ _ _) @ _).
        rewrite id_left.
        apply tensor_split.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        refine (!(tensor_split' _ _) @ _).
        apply tensor_split.
      }
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply tensor_comp_id_r.
      }
      refine (!_).
      etrans.
      {
        do 6 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        exact (!(tensor_comp_id_r _ _)).
      }
      etrans.
      {
        do 5 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        exact (!(tensor_comp_id_r _ _)).
      }
      etrans.
      {
        do 4 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        exact (!(tensor_comp_id_r _ _)).
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        exact (!(tensor_comp_id_r _ _)).
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        exact (!(tensor_comp_id_r _ _)).
      }
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
        rewrite !assoc'.
        exact (!(tensor_comp_id_r _ _)).
      }
      etrans.
      {
        exact (!(tensor_comp_id_r _ _)).
      }
      apply maponpaths_2.
      clear x.
      (*
       We simplified the equation, and now we need to show that for all

         h : y --> M z

       we have

         μ M y · (#M h · μ M z)
         =
         #M(#M h) · (#M (μ M z) · μ M z)
       *)
      assert (enriched_from_arr E (μ M z) #⊗ enriched_from_arr E (# M (μ M z))
              · enriched_comp E (M (M (M z))) (M (M z)) (M z)
              =
              enriched_from_arr E (μ M z) #⊗ enriched_from_arr E (μ M (M z))
              · enriched_comp E (M (M (M z))) (M (M z)) (M z))
        as p.
      {
        refine (!(id_left _) @ _ @ id_left _).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply mon_lunitor_linvunitor.
        }
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          pose (p := maponpaths
                       (enriched_from_arr E)
                       (@Monad_law3 _ M z)).
          rewrite !enriched_from_arr_comp in p.
          cbn in p.
          rewrite !assoc.
          exact p.
        }
        rewrite !assoc.
        do 2 apply maponpaths_2.
        apply mon_lunitor_linvunitor.
      }
      rewrite (functor_enrichment_from_arr EM) in p.
      (**
         #M(#M h) · (#M (μ M z) · μ M z)
         =
         #M(#M h) · (μ M (M z) · μ M z)
       *)
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          do 3 apply maponpaths_2.
          exact (!(tensor_comp_id_r _ _)).
        }
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(tensor_comp_id_r _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (!(tensor_comp_id_r _ _)).
        }
        etrans.
        {
          exact (!(tensor_comp_id_r _ _)).
        }
        apply maponpaths_2.
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
          exact (!(tensor_split _ _)).
        }
        exact p.
      }
      clear p.
      (*
         #M(#M h) · (μ M (M z) · μ M z)
         =
         (#M(#M h) · μ M (M z)) · μ M z
       *)
      etrans.
      {
        do 2 apply maponpaths.
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
      refine (!_).
      (*
       μ M y · (#M h · μ M z)
       =
       (μ M y · #M h) · μ M z
       *)
      etrans.
      {
        do 3 apply maponpaths.
        apply enrichment_assoc.
      }
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        do 4 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_linvunitor.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_linvunitor.
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!(tensor_split _ _) @ _).
        apply tensor_split'.
      }
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply tensor_split'.
          }
          rewrite !assoc.
          apply maponpaths_2.
          rewrite mon_linvunitor_I_mon_rinvunitor_I.
          refine (!_).
          apply tensor_rinvunitor.
        }
        rewrite !assoc'.
        apply tensor_comp_id_r.
      }
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            rewrite !assoc.
            do 3 apply maponpaths_2.
            refine (!_).
            apply tensor_id_id.
          }
          etrans.
          {
            apply maponpaths_2.
            apply tensor_lassociator.
          }
          rewrite !assoc'.
          apply maponpaths.
          refine (!_).
          apply tensor_comp_id_l.
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          refine (!_).
          apply mon_rinvunitor_triangle.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply mon_rassociator_lassociator.
          }
          apply id_left.
        }
        exact (!(tensor_comp_id_l _ _)).
      }
      refine (!(tensor_comp_id_l _ _) @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_lassociator.
        }
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          exact (!(tensor_comp_id_l _ _)).
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_comp_id_r.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            rewrite !assoc.
            apply maponpaths_2.
            apply tensor_lassociator.
          }
          rewrite !assoc'.
          apply maponpaths.
          exact (!(tensor_comp_id_l _ _)).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply mon_inv_triangle.
        }
        exact (!(tensor_comp_id_l _ _)).
      }
      apply maponpaths.
      (*
       We simplified the equation, and now we need to show that for all

         h : y --> M z

       we have

         #M(#M h) · μ M (M z)
         =
         μ M y · #M h
       *)
      pose (p := mu_of_monad_enrichment EM y (M z)).
      cbn in p.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (!(tensor_split' _ _)).
      }
      rewrite !assoc.
      refine (!p @ _) ; clear p.
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply tensor_rinvunitor.
      }
      rewrite !assoc'.
      apply maponpaths.
      exact (!(tensor_split' _ _)).
    - intros x y f ; cbn.
      rewrite enriched_to_from_arr.
      etrans.
      {
        apply maponpaths.
        apply bind_η.
      }
      apply id_right.
    - intros x y f ; cbn.
      rewrite enriched_from_arr_comp.
      rewrite enriched_from_to_arr.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply bind_η.
        }
        apply enriched_from_arr_id.
      }
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
    - intros x ; cbn.
      rewrite enriched_to_from_arr.
      apply idpath.
    - intros x y z f g ; cbn.
      unfold bind.
      use (invmaponpathsweq (make_weq _ (isweq_enriched_from_arr E _ _))) ; cbn.
      rewrite enriched_from_to_arr.
      rewrite enriched_from_arr_comp.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_linvunitor.
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
        apply enrichment_assoc'.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
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
        etrans.
        {
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
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply mon_lassociator_rassociator.
        }
        apply id_left.
      }
      rewrite <- !tensor_comp_mor.
      rewrite !id_left.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply tensor_comp_mor.
      }
      etrans.
      {
        refine (!_).
        apply tensor_comp_mor.
      }
      rewrite !id_right.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (@Monad_law2 _ M y).
        }
        apply id_right.
      }
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply (@Monad_law2 _ M z).
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
      etrans.
      {
        refine (!_).
        apply tensor_comp_mor.
      }
      rewrite !id_left, id_right.
      apply maponpaths.
      rewrite (functor_enrichment_from_arr EM g).
      apply idpath.
  Qed.

  (**
   3. The enrichment
   *)
  Definition Kleisli_cat_monad_enrichment
    : enrichment (Kleisli_cat_monad M) V.
  Proof.
    simple refine (_ ,, _).
    - exact Kleisli_cat_monad_enrichment_data.
    - exact Kleisli_cat_monad_enrichment_laws.
  Defined.


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
    - cbn.
      intros x y z.
      etrans.
      {
        apply enriched_comp_postcomp_arr.
      }
      refine (!_).
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
        exact (!(tensor_split _ _)).
      }
      unfold postcomp_arr.
      etrans.
      {
        do 4 apply maponpaths_2.
        apply tensor_comp_l_id_r.
      }
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_linvunitor.
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
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_id_l.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply enrichment_assoc'.
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            do 2 apply maponpaths_2.
            apply tensor_id_id.
          }
          refine (!(tensor_split _ _) @ _).
          apply tensor_split'.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply enrichment_assoc'.
      }
      rewrite !assoc.
      refine (_ @ id_left _).
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          do 3 apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            refine (!(tensor_id_id _ _) @ _).
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
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
          rewrite !assoc.
          do 4 apply maponpaths_2.
          apply mon_lassociator_rassociator.
        }
        rewrite id_left.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(tensor_id_id _ _)).
          }
          apply tensor_rassociator.
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          do 2 apply maponpaths_2.
          apply tensor_rassociator.
        }
        rewrite !assoc.
        do 3 apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          exact (!(tensor_id_id _ _)).
        }
        apply tensor_rassociator.
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          refine (!_).
          apply tensor_comp_id_r.
        }
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply tensor_comp_id_r.
        }
        refine (!_).
        apply tensor_comp_id_r.
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply tensor_comp_l_id_l.
        }
        rewrite !assoc'.
        apply maponpaths.
        apply tensor_rassociator.
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply tensor_comp_id_r.
      }
      rewrite !assoc.
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
      refine (_ @ tensor_id_id _ _).
      apply maponpaths_2.
      rewrite !assoc'.
      pose (unit_of_monad_enrichment EM y (M z)).
      cbn in p.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          apply enrichment_assoc.
        }
        rewrite !assoc.
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc'.
          apply maponpaths.
          apply tensor_lassociator.
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply mon_linvunitor_triangle.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply tensor_id_id.
          }
          refine (!(tensor_split' _ _) @ _).
          apply tensor_split.
        }
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply tensor_linvunitor.
      }
      rewrite !assoc.
      etrans.
      {
        do 3 apply maponpaths_2.
        exact p.
      }
      clear p.
      pose (p := maponpaths (enriched_from_arr E) (@Monad_law1 _ M z)).
      rewrite enriched_from_arr_id in p.
      rewrite enriched_from_arr_comp in p.
      cbn in p.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
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
          refine (!(tensor_split _ _) @ _).
          apply tensor_comp_l_id_r.
        }
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply enrichment_assoc'.
        }
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply tensor_rassociator.
        }
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        refine (!_).
        apply tensor_comp_id_r.
      }
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
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        etrans.
        {
          refine (!_).
          apply tensor_comp_id_r.
        }
        rewrite !assoc.
        apply maponpaths_2.
        exact p.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply enrichment_id_left.
      }
      apply mon_linvunitor_lunitor.
    - cbn.
      intros x y f.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        exact (@η_bind _ M _ _ (η M y)).
      }
      refine (!_).
      apply enriched_from_arr_postcomp.
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
End EnrichedKleisli.
