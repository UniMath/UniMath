(******************************************************************************************

 Benabou cosmos

 In the theory of enriched categories, one often is interested in categories enriched over
 a monoidal category with sufficient structure. The reason for that is that structure on the
 category over which we enrich, allows us to do more sophisticated constructions.

 A key notion is given by the notion of a Benabou cosmos. A Benabou cosmos is given by a
 complete and cocomplete symmetric monoidal closed category. Let us understand why this
 notion is nice in the context of enriched category theory.
 - To construct the opposite of enriched categories, we assume that the category over which
   we enrich, is symmetric monoidal.
 - To construct Eilenberg-Moore categories of enriched monads, we assume that the category
   over which we enrich, has equalizers.
 - To construct the self-enriched category, we assume that the category over which we enrich,
   is symmetric monoidal closed.
 - To construct enriched functor categories, we assume that the category over which we enrich,
   is complete and symmetric monoidal closed.
 - To construct the composition of enriched profunctors, we assume that the category over
   which we enrich, is cocomplete.
 Note that from the last point, we see that to construct a double (bi)category of enriched
 categories and profunctors, we need to assume that we are enriched over a cocomplete
 monoidal category.

 A Benabou cosmos collects each of these assumptions and combines it all into one notion.

 References
 - "Elementary Cosmos I" by Street

 Contents
 1. Benabou cosmos
 2. Accessors

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coends.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

(** * 1. Benabou cosmos *)
Definition benabou_cosmos
  : UU
  := ∑ (V : sym_mon_closed_cat),
     (∏ (I : UU), Products I V)
     ×
     Equalizers V
     ×
     (∏ (I : UU), Coproducts I V)
     ×
     Coequalizers V.

(** * 2. Accessors *)
Coercion benabou_cosmos_to_sym_mon_closed_cat
         (V : benabou_cosmos)
  : sym_mon_closed_cat.
Proof.
  exact (pr1 V).
Defined.

Definition benabou_cosmos_products
           (V : benabou_cosmos)
           (I : UU)
  : Products I V
  := pr12 V I.

Definition benabou_cosmos_equalizers
           (V : benabou_cosmos)
  : Equalizers V
  := pr122 V.

Definition benabou_cosmos_coproducts
           (V : benabou_cosmos)
           (I : UU)
  : Coproducts I V
  := pr1 (pr222 V) I.

Definition benabou_cosmos_coequalizers
           (V : benabou_cosmos)
  : Coequalizers V
  := pr2 (pr222 V).

Definition benabou_cosmos_coends
           (V : benabou_cosmos)
           {C : category}
           (F : category_binproduct (C^opp) C ⟶ V)
  : coend_colimit F.
Proof.
  use construction_of_coends.
  - apply benabou_cosmos_coequalizers.
  - apply benabou_cosmos_coproducts.
  - apply benabou_cosmos_coproducts.
Defined.

#[global] Opaque benabou_cosmos_coends.
