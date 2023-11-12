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
         unfold dialgebra_enrichment_mor_left, dialgebra_enrichment_mor_right ; cbn ;
         rewrite id_left ;
         rewrite !assoc ;
         exact (nat_trans_enrichment_to_comp (mu_of_monad_enrichment EM) x y)).
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
  Definition kleisli_cat_enrichment
    : enrichment (kleisli_cat M) V.
  Proof.
    use image_enrichment.
    exact (eilenberg_moore_enrichment HV EM).
  Defined.

  Proposition kleisli_cat_enrichment_precomp_arr
              {x y : kleisli_cat M}
              (w : kleisli_cat M)
              (f : x --> y)
    : precomp_arr kleisli_cat_enrichment w f
      · dialgebra_enrichment_mor_incl _ _ _ _ _ _
      =
      dialgebra_enrichment_mor_incl _ _ _ _ _ _ · precomp_arr _ _ (pr111 f).
  Proof.
    apply eilenberg_moore_enrichment_precomp_arr.
  Qed.

  Proposition kleisli_cat_enrichment_postcomp_arr
              {x y : kleisli_cat M}
              (w : kleisli_cat M)
              (f : x --> y)
    : postcomp_arr kleisli_cat_enrichment w f
      · dialgebra_enrichment_mor_incl _ _ _ _ _ _
      =
      dialgebra_enrichment_mor_incl _ _ _ _ _ _ · postcomp_arr _ _ (pr111 f).
  Proof.
    apply eilenberg_moore_enrichment_postcomp_arr.
  Qed.

  (**
   3. Functor to the Kleisli category
   *)
  Definition kleisli_incl_enrichment
    : functor_enrichment
        (kleisli_incl M)
        E
        kleisli_cat_enrichment.
  Proof.
    use image_proj_enrichment.
    exact free_alg_enrichment.
  Defined.

  Proposition kleisli_nat_trans_enrichment
    : nat_trans_enrichment
        (kleisli_nat_trans M)
        (functor_comp_enrichment
           EM
           kleisli_incl_enrichment)
        kleisli_incl_enrichment.
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y ; cbn.
    use (dialgebra_enrichment_mor_eq_of_mor
           V
           HV
           EM (functor_id_enrichment _)).
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      exact (kleisli_cat_enrichment_precomp_arr
               (kleisli_incl M y)
               (kleisli_nat_trans M x)).
    }
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      apply free_alg_enrichment_mor_incl.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      exact (kleisli_cat_enrichment_postcomp_arr (kleisli_incl M (M x)) (kleisli_nat_trans M y)).
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply free_alg_enrichment_mor_incl.
    }
    cbn.
    rewrite !assoc.
    exact (!(nat_trans_enrichment_to_comp (mu_of_monad_enrichment EM) x y)).
  Qed.

  (**
   4. Functor between the two different versions of the Kleisli category
   *)
  Definition functor_to_kleisli_cat_enrichment_mor
             (x y : C)
    : E ⦃ x, M y ⦄ --> E ⦃ M x, M y ⦄
    := EM x (M y) · postcomp_arr E (M x) (μ M y).

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
    unfold dialgebra_enrichment_mor_left, dialgebra_enrichment_mor_right ; cbn.
    rewrite id_left.
    unfold functor_to_kleisli_cat_enrichment_mor.
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- functor_enrichment_postcomp_arr.
      cbn.
      rewrite !assoc'.
      rewrite <- postcomp_arr_comp.
      do 2 apply maponpaths.
      apply Monad_law3.
    }
    rewrite postcomp_arr_comp.
    rewrite !assoc'.
    rewrite <- precomp_postcomp_arr.
    rewrite !assoc.
    apply maponpaths_2.
    exact (!(nat_trans_enrichment_to_comp (mu_of_monad_enrichment EM) x (M y))).
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
        kleisli_cat_enrichment
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
      rewrite !assoc.
      rewrite <- functor_enrichment_from_arr.
      rewrite enriched_from_arr_postcomp.
      etrans.
      {
        apply maponpaths.
        exact (@Monad_law2 _ M x).
      }
      apply enriched_from_arr_id.
    - intros x y z ; cbn.
      use (dialgebra_enrichment_mor_eq_of_mor
             V HV
             EM (functor_id_enrichment E)).
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        apply functor_to_kleisli_cat_enrichment_data_incl.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply dialgebra_enrichment_comp_incl.
      }
      unfold dialgebra_enrichment_comp_mor, functor_to_kleisli_cat_enrichment_mor.
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- tensor_comp_mor.
        rewrite !functor_to_kleisli_cat_enrichment_data_incl.
        unfold functor_to_kleisli_cat_enrichment_mor.
        apply idpath.
      }
      etrans.
      {
        rewrite tensor_comp_l_id_r.
        rewrite !assoc'.
        rewrite <- precomp_postcomp_arr_assoc ; cbn.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        apply idpath.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- functor_enrichment_postcomp_arr.
        rewrite !assoc'.
        rewrite <- postcomp_arr_comp.
        apply idpath.
      }
      etrans.
      {
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
        rewrite <- !tensor_comp_mor.
        rewrite id_left, id_right.
        apply idpath.
      }
      do 2 apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths.
        apply Monad_law3.
      }
      rewrite postcomp_arr_comp.
      rewrite !assoc'.
      rewrite <- precomp_postcomp_arr.
      rewrite !assoc.
      apply maponpaths_2.
      exact (!(nat_trans_enrichment_to_comp (mu_of_monad_enrichment EM) y (M z))).
    - intros x y f ; cbn.
      use (dialgebra_enrichment_mor_eq_of_mor
             V HV
             EM (functor_id_enrichment E)).
      unfold bind.
      refine (dialgebra_enrichment_from_arr_incl _ _ _ _ _ _ @ _).
      rewrite !assoc'.
      rewrite functor_to_kleisli_cat_enrichment_data_incl.
      unfold functor_to_kleisli_cat_enrichment_mor.
      rewrite !assoc.
      rewrite <- functor_enrichment_from_arr.
      rewrite enriched_from_arr_postcomp.
      apply idpath.
  Qed.

  Definition functor_to_kleisli_cat_enrichment
    : functor_enrichment
        (functor_to_kleisli_cat M)
        (Kleisli_cat_monad_enrichment EM)
        kleisli_cat_enrichment.
  Proof.
    simple refine (_ ,, _).
    - exact functor_to_kleisli_cat_enrichment_data.
    - exact functor_to_kleisli_cat_enrichment_is_enrichment.
  Defined.

  Proposition functor_to_kleisli_incl_nat_trans_enrichment
    : nat_trans_enrichment
        (functor_to_kleisli_cat_incl_nat_trans M)
        kleisli_incl_enrichment
        (functor_comp_enrichment
           (Left_Kleisli_functor_enrichment EM)
           functor_to_kleisli_cat_enrichment).
  Proof.
    use nat_trans_enrichment_via_comp.
    intros x y.
    use (dialgebra_enrichment_mor_eq_of_mor
           V HV
           EM (functor_id_enrichment E)).
    rewrite !assoc'.
    rewrite kleisli_cat_enrichment_precomp_arr.
    rewrite kleisli_cat_enrichment_postcomp_arr.
    rewrite !assoc ; cbn.
    rewrite precomp_arr_id, postcomp_arr_id.
    rewrite !id_right.
    rewrite !assoc'.
    rewrite functor_to_kleisli_cat_enrichment_data_incl.
    rewrite free_alg_enrichment_mor_incl.
    unfold functor_to_kleisli_cat_enrichment_mor.
    rewrite !assoc.
    rewrite <- functor_enrichment_postcomp_arr.
    rewrite !assoc'.
    rewrite <- postcomp_arr_comp.
    etrans.
    {
      do 2 apply maponpaths.
      exact (@Monad_law2 _ M y).
    }
    rewrite postcomp_arr_id.
    apply id_right.
  Qed.

  (**
   5. The functor is fully faithful
   *)
  Section FullyFaithfulToKleisli.
    Context (x y : C).

    Definition functor_to_kleisli_cat_enrichment_inv
      : kleisli_cat_enrichment ⦃ functor_to_kleisli_cat M x, functor_to_kleisli_cat M y ⦄
        -->
        Kleisli_cat_monad_enrichment EM ⦃ x, y ⦄
      := dialgebra_enrichment_mor_incl _ _ _ _ _ _ · precomp_arr _ _ (η M x).

    Local Lemma functor_to_kleisli_cat_enrichment_inv_right
      : functor_to_kleisli_cat_enrichment_data x y
        · functor_to_kleisli_cat_enrichment_inv
        =
        identity _.
    Proof.
      unfold functor_to_kleisli_cat_enrichment_inv ; cbn.
      rewrite !assoc.
      rewrite functor_to_kleisli_cat_enrichment_data_incl.
      unfold functor_to_kleisli_cat_enrichment_mor.
      rewrite !assoc'.
      rewrite <- precomp_postcomp_arr.
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        exact (nat_trans_enrichment_to_comp (unit_of_monad_enrichment EM) _ _).
      }
      cbn.
      rewrite id_left.
      rewrite <- postcomp_arr_comp.
      refine (_ @ postcomp_arr_id _ _ _).
      apply maponpaths.
      apply Monad_law1.
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
      unfold functor_to_kleisli_cat_enrichment_mor, functor_to_kleisli_cat_enrichment_inv.
      cbn.
      refine (_ @ id_right _).
      rewrite !assoc'.
      pose (dialgebra_enrichment_mor_incl_eq
              V HV
              EM (functor_id_enrichment E)
              (μ M x) (μ M y))
        as p.
      unfold dialgebra_enrichment_mor_right in p.
      unfold dialgebra_enrichment_mor_left in p.
      cbn in p.
      rewrite id_left in p.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- functor_enrichment_precomp_arr.
        rewrite !assoc'.
        rewrite precomp_postcomp_arr.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        exact (!p).
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite <- precomp_arr_comp.
      refine (_ @ precomp_arr_id _ _ _).
      apply maponpaths.
      apply Monad_law2.
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
