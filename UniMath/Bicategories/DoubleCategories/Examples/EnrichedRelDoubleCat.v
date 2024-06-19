(*************************************************************************************

 The double category of enriched relations

 Suppose that we have a quantale `V`. An enriched relation between sets `X` and `Y` is
 given by a map `X → Y → V`. This is a generalization of relations: instead of taking
 values in `hProp`, it takes values in `V`. In this file, we construct the univalent
 pseudo double category of enriched relations. This double category is defined as follows:
 - Objects: sets
 - Vertical morphisms: functions
 - Horizontal morphisms: enriched relations
 - Squares: given by the order relation on `V`
 Note that if we take `V` to be `hProp`, then we obtain the usual double category of
 functions and relations, and thus the double category that we define in this files,
 generalizes the double category of sets and relations. For a reference on quantale
 enriched relations, see the paper "A point-free perspective on lax extensions and
 predicate liftings" . However, in that paper, double categories are not used.

 It is also good to compare it to the double category of categories enriched over a
 quantale. That double category is defined as follows:
 - Objects: `V`-enriched categories
 - Vertical morphisms: `V`-enriched functors
 - Horizontal morphisms: `V`-enriched profunctors
 - Squares: given by enriched natural transformation
 If we instantiate this double category with `hProp`, then we acquire a different
 double category, namely the double category of partially ordered sets, monotone
 functions, and monotone relations. As such, the difference between these two double
 categories is that the objects in the category of enriched relations are only sets
 and do not have any other structure.

 All the relevant constructions and proofs to define this double category have been
 given in other files, so this file only collects these facts.

 References
 - "A point-free perspective on lax extensions and predicate liftings" by Goncharov,
   Hofmann, Nora, Schröder and Wild

 Content
 1. Horizontal identities
 2. Horizontal composition
 3. Unitors and associators
 4. The double category of enriched relations
 5. Companion pairs and conjoints

 *************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichedRelation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.EnrichedRels.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.SymmetricUnivalent.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.

Local Open Scope cat.
Local Open Scope double_cat.
Local Open Scope moncat.

Import MonoidalNotations.

Section EnrichedRelationDoubleCat.
  Context (V : quantale_cosmos).

  (** * 1. Horizontal identities *)
  Definition enriched_rel_double_cat_hor_id_data
    : hor_id_data (enriched_relation_twosided_disp_cat V).
  Proof.
    use make_hor_id_data.
    - intro X.
      exact (id_enriched_relation X).
    - intros X Y f.
      exact (id_h_enriched_relation_square f).
  Defined.

  Definition enriched_rel_double_cat_hor_id
    : hor_id (enriched_relation_twosided_disp_cat V).
  Proof.
    use make_hor_id.
    - exact enriched_rel_double_cat_hor_id_data.
    - abstract
        (split ; intro ; intros ; apply isaprop_enriched_relation_square).
  Defined.

  (** * 2. Horizontal composition *)
  Definition enriched_rel_double_cat_hor_comp_data
    : hor_comp_data (enriched_relation_twosided_disp_cat V).
  Proof.
    use make_hor_comp_data.
    - intros X Y Z R₁ R₂.
      exact (R₁ ·e R₂).
    - intros ? ? ? ? ? ? ? ? ? ? ? ? ? τ θ.
      exact (comp_h_enriched_relation_square τ θ).
  Defined.

  Definition enriched_rel_double_cat_hor_comp
    : hor_comp (enriched_relation_twosided_disp_cat V).
  Proof.
    use make_hor_comp.
    - exact enriched_rel_double_cat_hor_comp_data.
    - abstract
        (split ; intro ; intros ; apply isaprop_enriched_relation_square).
  Defined.

  (** * 3. Unitors and associators *)
  Definition enriched_rel_double_cat_lunitor_data
    : double_lunitor_data
        enriched_rel_double_cat_hor_id
        enriched_rel_double_cat_hor_comp.
  Proof.
    intros X Y R.
    use to_iso_enriched_relation_twosided_disp_cat.
    - exact (enriched_relation_lunitor R).
    - exact (enriched_relation_linvunitor R).
  Defined.

  Definition enriched_rel_double_cat_lunitor
    : double_cat_lunitor
        enriched_rel_double_cat_hor_id
        enriched_rel_double_cat_hor_comp.
  Proof.
    use make_double_lunitor.
    - exact enriched_rel_double_cat_lunitor_data.
    - abstract
        (intro ; intros ; apply isaprop_enriched_relation_square).
  Defined.

  Definition enriched_rel_double_cat_runitor_data
    : double_runitor_data
        enriched_rel_double_cat_hor_id
        enriched_rel_double_cat_hor_comp.
  Proof.
    intros X Y R.
    use to_iso_enriched_relation_twosided_disp_cat.
    - exact (enriched_relation_runitor R).
    - exact (enriched_relation_rinvunitor R).
  Defined.

  Definition enriched_rel_double_cat_runitor
    : double_cat_runitor
        enriched_rel_double_cat_hor_id
        enriched_rel_double_cat_hor_comp.
  Proof.
    use make_double_runitor.
    - exact enriched_rel_double_cat_runitor_data.
    - abstract
        (intro ; intros ; apply isaprop_enriched_relation_square).
  Defined.

  Definition enriched_rel_double_cat_associator_data
    : double_associator_data enriched_rel_double_cat_hor_comp.
  Proof.
    intros W X Y Z R₁ R₂ R₃.
    use to_iso_enriched_relation_twosided_disp_cat.
    - exact (enriched_relation_rassociator R₁ R₂ R₃).
    - exact (enriched_relation_lassociator R₁ R₂ R₃).
  Defined.

  Definition enriched_rel_double_cat_associator
    : double_cat_associator enriched_rel_double_cat_hor_comp.
  Proof.
    use make_double_associator.
    - exact enriched_rel_double_cat_associator_data.
    - abstract
        (intro ; intros ; apply isaprop_enriched_relation_square).
  Defined.

  (** * 4. The double category of enriched relations *)
  Definition enriched_rel_double_cat
    : double_cat.
  Proof.
    use make_double_cat.
    - exact SET.
    - exact (enriched_relation_twosided_disp_cat V).
    - exact enriched_rel_double_cat_hor_id.
    - exact enriched_rel_double_cat_hor_comp.
    - exact enriched_rel_double_cat_lunitor.
    - exact enriched_rel_double_cat_runitor.
    - exact enriched_rel_double_cat_associator.
    - abstract
        (intro ; intros ; apply isaprop_enriched_relation_square).
    - abstract
        (intro ; intros ; apply isaprop_enriched_relation_square).
  Defined.

  Definition enriched_rel_univalent_double_cat
    : univalent_double_cat.
  Proof.
    use make_univalent_double_cat.
    - exact enriched_rel_double_cat.
    - split.
      + exact is_univalent_HSET.
      + exact (is_univalent_enriched_relation_twosided_disp_cat V).
  Defined.

  Proposition is_flat_enriched_rel_double_cat
    : is_flat_double_cat enriched_rel_double_cat.
  Proof.
    intro ; intros.
    apply isaprop_enriched_relation_square.
  Qed.

  (** * 5. Companion pairs and conjoints *)
  Definition all_companions_enriched_rel
    : all_companions_double_cat enriched_rel_double_cat.
  Proof.
    refine (λ (X Y : hSet) (f : X → Y), _).
    simple refine (_ ,, _).
    - exact (companion_enriched_relation f).
    - use make_double_cat_are_companions' ; cbn.
      + apply companion_enriched_relation_left.
      + apply companion_enriched_relation_right.
      + abstract
          (apply isaprop_enriched_relation_square).
      + abstract
          (apply isaprop_enriched_relation_square).
  Defined.

  Definition all_conjoints_enriched_rel
    : all_conjoints_double_cat enriched_rel_double_cat.
  Proof.
    refine (λ (X Y : hSet) (f : X → Y), _).
    simple refine (_ ,, _).
    - exact (conjoint_enriched_relation f).
    - use make_double_cat_are_conjoints'.
      + apply conjoint_enriched_relation_left.
      + apply conjoint_enriched_relation_right.
      + abstract
          (apply isaprop_enriched_relation_square).
      + abstract
          (apply isaprop_enriched_relation_square).
  Defined.
End EnrichedRelationDoubleCat.
