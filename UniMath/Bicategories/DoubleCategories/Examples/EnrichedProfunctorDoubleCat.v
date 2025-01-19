(*****************************************************************************************

 The double category of profunctors enriched over a quantale

 In this file, we define the double category of quantale enriched profunctors. Given a
 quantale `V`, we define this double category as follows:
 - Objects: `V`-enriched univalent categories
 - Vertical morphisms: `V`-enriched functors
 - Horizontal morphisms: `V`-enriched profunctors
 - Squares: transformations of profunctors

 The key thing to note about this construction is that we do actually require the objects
 to be univalent categories. This might seem strange at first, because we do not have a
 category of univalent categories. Here the quantale enrichment comes into play. Because
 the category is enriched over the quantale `V`, this univalent category can have at most
 a single morphism between any two objects. This is because morphisms from `x` to `y` in
 that category correspond to morphisms from the monoidal unit in `V` to some object in `V`.
 Since `V` is a poset, there can be at most one such morphism, and thus the same must hold
 for `C` as well. For the same reason, every univalent category enriched over a quantale
 also has a set of objects.

 For all constructions in this file we reuse what we already did for the Verity double
 bicategory of enriched profunctors.

 Content
 1. The 2-sided displayed category of quantale enriched profunctors
 2. Horizontal identities
 3. Horizontal composition
 4. The unitors and associators
 5. The double category of quantale enriched profunctors
 6. Companions and conjoints

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentFunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichmentTransformation.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Profunctor.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.QuantaleEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.StandardProfunctors.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorTransformations.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Invertible.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.ProfunctorSquares.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Coend.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.Composition.
Require Import UniMath.CategoryTheory.EnrichedCats.Profunctors.RepresentableLaws.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.EnrichedCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

Opaque sym_mon_braiding.

Section QuantaleEnriched.
  Context (V : quantale_cosmos).

  (** * 1. The 2-sided displayed category of quantale enriched profunctors *)
  Definition quantale_enriched_profunctor_twosided_disp_cat_ob_mor
    : twosided_disp_cat_ob_mor
        (cat_of_quantale_enriched_cat V)
        (cat_of_quantale_enriched_cat V).
  Proof.
    simple refine (_ ,, _).
    - exact (λ E₁ E₂,
             enriched_cat_to_enrichment _ E₁ ↛e enriched_cat_to_enrichment _ E₂).
    - exact (λ E₁ E₂ E₃ E₄ P Q F G,
             enriched_profunctor_square
               (enriched_functor_enrichment F)
               (enriched_functor_enrichment G)
               P Q).
  Defined.

  Definition quantale_enriched_profunctor_twosided_disp_cat_id_comp
    : twosided_disp_cat_id_comp
        quantale_enriched_profunctor_twosided_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ E₁ E₂ P, id_h_enriched_profunctor_square P).
    - exact (λ C₁ C₂ C₃ D₁ D₂ D₃ P₁ P₂ P₃ F₁ F₂ G₁ G₂ τ₁ τ₂,
             comp_h_enriched_profunctor_square τ₁ τ₂).
  Defined.

  Definition quantale_enriched_profunctor_twosided_disp_cat_data
    : twosided_disp_cat_data
        (cat_of_quantale_enriched_cat V)
        (cat_of_quantale_enriched_cat V).
  Proof.
    simple refine (_ ,, _).
    - exact quantale_enriched_profunctor_twosided_disp_cat_ob_mor.
    - exact quantale_enriched_profunctor_twosided_disp_cat_id_comp.
  Defined.

  Proposition quantale_enriched_profunctor_twosided_disp_cat_axioms
    : twosided_disp_cat_axioms
        quantale_enriched_profunctor_twosided_disp_cat_data.
  Proof.
    repeat split ; intro ; intros.
    - apply isaprop_quantale_enriched_profunctor_transformation.
    - apply isaprop_quantale_enriched_profunctor_transformation.
    - apply isaprop_quantale_enriched_profunctor_transformation.
    - apply isasetaprop.
      apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  Definition quantale_enriched_profunctor_twosided_disp_cat
    : twosided_disp_cat
        (cat_of_quantale_enriched_cat V)
        (cat_of_quantale_enriched_cat V).
  Proof.
    simple refine (_ ,, _).
    - exact quantale_enriched_profunctor_twosided_disp_cat_data.
    - exact quantale_enriched_profunctor_twosided_disp_cat_axioms.
  Defined.

  Proposition is_univalent_quantale_enriched_profunctor_twosided_disp_cat
    : is_univalent_twosided_disp_cat
        quantale_enriched_profunctor_twosided_disp_cat.
  Proof.
    intros C₁ C₂ C₃ C₄ p₁ p₂ P Q.
    induction p₁, p₂.
    use isweqimplimpl.
    - cbn.
      intro τ.
      use eq_profunctor_quantale_enrichment.
      intros y x.
      use (isotoid _ (is_univalent_quantale_cosmos V)).
      use make_z_iso.
      + exact (pr11 τ y x).
      + exact (pr112 τ y x).
      + split.
        * apply is_poset_category_quantale_cosmos.
        * apply is_poset_category_quantale_cosmos.
    - apply isaset_profunctor_quantale_enrichment.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_twosided_disp.
      + intros.
        apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  (** * 2. Horizontal identities *)
  Definition quantale_enriched_profunctor_hor_id_data
    : hor_id_data quantale_enriched_profunctor_twosided_disp_cat.
  Proof.
    use make_hor_id_data.
    - exact (λ E, identity_enriched_profunctor _).
    - exact (λ E₁ E₂ F, id_v_enriched_profunctor_square _).
  Defined.

  Proposition quantale_enriched_profunctor_hor_id_laws
    : hor_id_laws quantale_enriched_profunctor_hor_id_data.
  Proof.
    repeat split ; intro ; intros ; apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  Definition quantale_enriched_profunctor_hor_id
    : hor_id quantale_enriched_profunctor_twosided_disp_cat.
  Proof.
    use make_hor_id.
    - exact quantale_enriched_profunctor_hor_id_data.
    - exact quantale_enriched_profunctor_hor_id_laws.
  Defined.

  (** * 3. Horizontal composition *)
  Definition quantale_enriched_profunctor_hor_comp_data
    : hor_comp_data quantale_enriched_profunctor_twosided_disp_cat.
  Proof.
    use make_hor_comp_data.
    - exact (λ E₁ E₂ E₃ P Q, comp_enriched_profunctor P Q).
    - exact (λ E₁ E₂ E₃ E₄ E₅ E₆ F₁ F₂ F₃ P₁ P₂ Q₁ Q₂ τ θ,
             comp_v_enriched_profunctor_square τ θ).
  Defined.

  Proposition quantale_enriched_profunctor_hor_comp_laws
    : hor_comp_laws quantale_enriched_profunctor_hor_comp_data.
  Proof.
    repeat split ; intro ; intros ; apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  Definition quantale_enriched_profunctor_hor_comp
    : hor_comp quantale_enriched_profunctor_twosided_disp_cat.
  Proof.
    use make_hor_comp.
    - exact quantale_enriched_profunctor_hor_comp_data.
    - exact quantale_enriched_profunctor_hor_comp_laws.
  Defined.

  (** * 4. The unitors and associators *)
  Definition quantale_enriched_profunctor_double_cat_lunitor_data
    : double_lunitor_data
        quantale_enriched_profunctor_hor_id
        quantale_enriched_profunctor_hor_comp.
  Proof.
    intros E₁ E₂ P.
    use make_iso_twosided_disp.
    - use enriched_profunctor_transformation_to_square.
      exact (lunitor_enriched_profunctor P).
    - simple refine (_ ,, _ ,, _).
      + use enriched_profunctor_transformation_to_square.
        exact (linvunitor_enriched_profunctor P).
      + apply isaprop_quantale_enriched_profunctor_transformation.
      + apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  Proposition quantale_enriched_profunctor_double_cat_lunitor_laws
    : double_lunitor_laws
        quantale_enriched_profunctor_double_cat_lunitor_data.
  Proof.
    intro ; intros.
    apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  Definition quantale_enriched_profunctor_double_cat_lunitor
    : double_cat_lunitor
        quantale_enriched_profunctor_hor_id
        quantale_enriched_profunctor_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact quantale_enriched_profunctor_double_cat_lunitor_data.
    - exact quantale_enriched_profunctor_double_cat_lunitor_laws.
  Defined.

  Definition quantale_enriched_profunctor_double_cat_runitor_data
    : double_runitor_data
        quantale_enriched_profunctor_hor_id
        quantale_enriched_profunctor_hor_comp.
  Proof.
    intros E₁ E₂ P.
    use make_iso_twosided_disp.
    - use enriched_profunctor_transformation_to_square.
      exact (runitor_enriched_profunctor P).
    - simple refine (_ ,, _ ,, _).
      + use enriched_profunctor_transformation_to_square.
        exact (rinvunitor_enriched_profunctor P).
      + apply isaprop_quantale_enriched_profunctor_transformation.
      + apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  Proposition quantale_enriched_profunctor_double_cat_runitor_laws
    : double_runitor_laws
        quantale_enriched_profunctor_double_cat_runitor_data.
  Proof.
    intro ; intros.
    apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  Definition quantale_enriched_profunctor_double_cat_runitor
    : double_cat_runitor
        quantale_enriched_profunctor_hor_id
        quantale_enriched_profunctor_hor_comp.
  Proof.
    use make_double_runitor.
    - exact quantale_enriched_profunctor_double_cat_runitor_data.
    - exact quantale_enriched_profunctor_double_cat_runitor_laws.
  Defined.

  Definition quantale_enriched_profunctor_double_cat_associator_data
    : double_associator_data quantale_enriched_profunctor_hor_comp.
  Proof.
    intros E₁ E₂ E₃ E₄ P₁ P₂ P₃.
    use make_iso_twosided_disp.
    - use enriched_profunctor_transformation_to_square.
      exact (lassociator_enriched_profunctor P₁ P₂ P₃).
    - simple refine (_ ,, _ ,, _).
      + use enriched_profunctor_transformation_to_square.
        exact (rassociator_enriched_profunctor P₁ P₂ P₃).
      + apply isaprop_quantale_enriched_profunctor_transformation.
      + apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  Proposition quantale_enriched_profunctor_double_cat_associator_laws
    : double_associator_laws
        quantale_enriched_profunctor_double_cat_associator_data.
  Proof.
    intro ; intros.
    apply isaprop_quantale_enriched_profunctor_transformation.
  Qed.

  Definition quantale_enriched_profunctor_double_cat_associator
    : double_cat_associator quantale_enriched_profunctor_hor_comp.
  Proof.
    use make_double_associator.
    - exact quantale_enriched_profunctor_double_cat_associator_data.
    - exact quantale_enriched_profunctor_double_cat_associator_laws.
  Defined.

  (** * 5. The double category of quantale enriched profunctors *)
  Definition quantale_enriched_profunctor_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact (univalent_cat_of_quantale_enriched_cat V).
    - exact quantale_enriched_profunctor_twosided_disp_cat.
    - exact quantale_enriched_profunctor_hor_id.
    - exact quantale_enriched_profunctor_hor_comp.
    - exact quantale_enriched_profunctor_double_cat_lunitor.
    - exact quantale_enriched_profunctor_double_cat_runitor.
    - exact quantale_enriched_profunctor_double_cat_associator.
    - abstract
        (intro ; intros ;
         apply isaprop_quantale_enriched_profunctor_transformation).
    - abstract
        (intro ; intros ;
         apply isaprop_quantale_enriched_profunctor_transformation).
  Defined.

  Definition quantale_enriched_profunctor_univalent_double_cat
    : univalent_double_cat.
  Proof.
    use make_univalent_double_cat.
    - exact quantale_enriched_profunctor_double_cat.
    - split.
      + apply univalent_category_is_univalent.
      + exact is_univalent_quantale_enriched_profunctor_twosided_disp_cat.
  Defined.

  (** * 6. Companions and conjoints *)
  Definition all_companions_quantale_enriched_profunctor_double_cat
    : all_companions_double_cat
        quantale_enriched_profunctor_double_cat.
  Proof.
    refine (λ C₁ C₂ F,
            representable_enriched_profunctor_left (enriched_functor_enrichment F)
            ,,
            _).
    use make_double_cat_are_companions.
    - apply representable_enriched_profunctor_left_unit.
    - apply representable_enriched_profunctor_left_counit.
    - abstract
        (apply isaprop_quantale_enriched_profunctor_transformation).
    - abstract
        (apply isaprop_quantale_enriched_profunctor_transformation).
  Defined.

  Definition all_conjoints_quantale_enriched_profunctor_double_cat
    : all_conjoints_double_cat
        quantale_enriched_profunctor_double_cat.
  Proof.
    refine (λ C₁ C₂ F,
            representable_enriched_profunctor_right (enriched_functor_enrichment F)
            ,,
            _).
    use make_double_cat_are_conjoints.
    - apply representable_enriched_profunctor_right_unit.
    - apply representable_enriched_profunctor_right_counit.
    - abstract
        (apply isaprop_quantale_enriched_profunctor_transformation).
    - abstract
        (apply isaprop_quantale_enriched_profunctor_transformation).
  Defined.
End QuantaleEnriched.
