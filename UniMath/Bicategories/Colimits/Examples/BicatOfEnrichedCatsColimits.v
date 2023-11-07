(******************************************************************************

 Colimits of enriched categories

 In this file, we collect results about colimits in the bicategory of enriched
 categories. Note that we only look at univalent enriched categories.

 The bicategory of enriched categories has Kleisli objects. In this construction,
 there is an interesting subtlety. Usually, one can construct enriched Kleili
 category without any additional assumption on `V`. This is done in the file
 `EnrichedCats.Examples.KleisliEnriched.v`. However, this construction does
 not give rise to a univalent category. As such, we do not get Kleisli objects
 in the bicategory of univalent enriched categories this way.

 Alteratively, one can construct the Kleisli category as a full subcategory of
 the Eilenberg-Moore category. This route is taken in the file
 `EnrichedCats.Examples.UnivalentKleisliEnriched`. However, for this construction,
 we need to make additional assumptions on `V`. To guarantee that the
 Eilenberg-Moore category is enriched, one needs to have equalizers in `V`,
 because those are used to formulate the commutativity requirement for morphisms
 in the Eilenberg-Moore category. This construction does give rise to a univalent
 enriched category, and this way, we can construct Kleisli objects in the
 bicategory of enriched categories.

 To prove the universal property of this construction, we use the universal
 property of the Rezk completion. The relevant functions are given in the file
 `EnrichedCats.Examples.UnivalentKleisliMapping.v`, and more explanation is
 given there. The main idea is:
 - We can establish the universal property for the ordinary non-univalent Kleisli
   category.
 - We have a weak equivalence from the non-univalent Kleisli category to the
   univalent Kleisli category. As such, the univalent Kleisli category is the
   Rezk completion of the non-univalent one.
 - Using this weak equivalence and the universal property of the Rezk completion,
   we obtain the universal property for the univalent Kleisli category.

 Note that in the file `RezkCompletion.EnrichedRezkCompletion.v`, there is a
 general construction for Rezk completions of enriched categories. This
 construction cannot be used here, because it raises the universe level, and
 thus the obtained category might not live in the bicategory that we are looking
 at. However, for the Kleisli category, we established that its Rezk completion
 does actually live in the relevant bicategory, because of the weak equivalence
 that we constructed between the two versions of the Kleisli category.

 Furthermore, for the Rezk completion in `RezkCompletion.EnrichedRezkCompletion.v`,
 we assume that `V` is a complete symmetric monoidal closed category, whereas
 in our construction, we only need equalizers.

 Contents
 1. Kleisli categories

 ******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.categories.KleisliCategory.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentMonad.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.UnivalentKleisliEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.UnivalentKleisliMapping.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInBicatOfEnrichedCats.
Require Import UniMath.Bicategories.Monads.Examples.MonadsInOp1Bicat.
Require Import UniMath.Bicategories.Colimits.KleisliObjects.

Local Open Scope cat.

Section ColimitsEnrichedCats.
  Context (V : monoidal_cat).

  (** * 1. Kleisli objects *)
  Section KleisliEnrichedCat.
    Context (HV : Equalizers V)
            (EM : mnd (op1_bicat (bicat_of_enriched_cats V))).

    Let C : univalent_category := pr1 (ob_of_mnd EM).
    Let E : enrichment C V := pr2 (ob_of_mnd EM).
    Let M : Monad C := Monad_from_mnd_enriched_cats _ (mnd_op1_to_mnd EM).
    Let EM' : monad_enrichment E M
      := Monad_enrichment_from_mnd_enriched_cats _ (mnd_op1_to_mnd EM).

    Definition bicat_of_enriched_cats_has_kleisli_cocone
      : kleisli_cocone EM.
    Proof.
      use make_kleisli_cocone.
      - exact (univalent_kleisli_cat M ,, kleisli_cat_enrichment HV EM').
      - exact (kleisli_incl M ,, kleisli_incl_enrichment HV EM').
      - exact (kleisli_nat_trans M ,, kleisli_nat_trans_enrichment HV EM').
      - abstract
          (use eq_enriched_nat_trans ;
           intro x ;
           use eq_mor_kleisli_cat ;
           exact (@Monad_law2 _ M x)).
      - abstract
          (use eq_enriched_nat_trans ;
           intro x ;
           use eq_mor_kleisli_cat ;
           cbn ;
           rewrite id_left ;
           apply (!(@Monad_law3 _ M x))).
    Defined.

    Definition bicat_of_enriched_cats_has_kleisli_ump_1
      : has_kleisli_ump_1 EM bicat_of_enriched_cats_has_kleisli_cocone.
    Proof.
      intro q.
      pose (F := mor_of_kleisli_cocone _ q).
      pose (γ := cell_of_kleisli_cocone _ q).
      pose (p₁ := from_eq_enriched_nat_trans (kleisli_cocone_unit _ q)).
      assert (p₂ : ∏ (x : C), pr11 γ (M x) · pr11 γ x = # (pr11 F) (μ M x) · pr11 γ x).
      {
        intro x.
        pose (p₂ := from_eq_enriched_nat_trans (kleisli_cocone_mult _ q) x).
        cbn in p₂.
        rewrite !id_left in p₂.
        exact p₂.
      }
      use make_kleisli_cocone_mor.
      - exact (enriched_functor_from_univalent_kleisli_cat
                 HV
                 EM'
                 _
                 (enriched_functor_enrichment F)
                 (enriched_nat_trans_enrichment _ γ)
                 p₁ p₂).
      - exact (enriched_functor_from_univalent_kleisli_cat_nat_trans
                 HV
                 EM'
                 _
                 (enriched_functor_enrichment F)
                 (enriched_nat_trans_enrichment _ γ)
                 p₁ p₂).
      - abstract
          (use eq_enriched_nat_trans ;
           intro x ;
           refine (_ @ maponpaths (λ z, z · _) (!(id_left _))) ;
           exact (enriched_functor_from_univalent_kleisli_cat_eq
                    HV
                    EM'
                    _
                    (enriched_functor_enrichment F)
                    (enriched_nat_trans_enrichment _ γ)
                    p₁ p₂
                    x)).
      - use make_is_invertible_2cell_enriched.
        apply enriched_functor_from_univalent_kleisli_cat_nat_trans_is_z_iso.
    Defined.

    Definition bicat_of_enriched_cats_has_kleisli_ump_2
      : has_kleisli_ump_2 EM bicat_of_enriched_cats_has_kleisli_cocone.
    Proof.
      intros C' G₁ G₂ α p.
      assert (p' : ∏ (x : C),
                 # (pr11 G₁) (kleisli_nat_trans M x) · pr11 α x
                 =
                 pr11 α (M x) · # (pr11 G₂) (kleisli_nat_trans M x)).
      {
        intro x.
        pose (q := from_eq_enriched_nat_trans p x).
        cbn in q.
        rewrite !id_left, !id_right in q.
        exact q.
      }
      use iscontraprop1.
      - abstract
          (use invproofirrelevance ;
           intros β₁ β₂ ;
           use subtypePath ; [ intro ; apply cellset_property | ] ;
           use eq_enriched_nat_trans ;
           exact (enriched_nat_trans_from_univalent_kleisli_cat_unique
                    HV EM'
                    _
                    α
                    (from_eq_enriched_nat_trans (pr2 β₁))
                    (from_eq_enriched_nat_trans (pr2 β₂)))).
      - simple refine (_ ,, _).
        + exact (enriched_nat_trans_from_univalent_kleisli_cat HV EM' _ α p').
        + abstract
            (use eq_enriched_nat_trans ;
             exact (pre_whisker_enriched_nat_trans_from_univalent_kleisli_cat
                      HV EM'
                      _
                      α
                      p')).
    Defined.
  End KleisliEnrichedCat.

  Definition bicat_of_enriched_cats_has_kleisli
             (HV : Equalizers V)
    : has_kleisli (bicat_of_enriched_cats V).
  Proof.
    intro m.
    simple refine (_ ,, _ ,, _).
    - exact (bicat_of_enriched_cats_has_kleisli_cocone HV m).
    - exact (bicat_of_enriched_cats_has_kleisli_ump_1 HV m).
    - exact (bicat_of_enriched_cats_has_kleisli_ump_2 HV m).
  Defined.
End ColimitsEnrichedCats.
