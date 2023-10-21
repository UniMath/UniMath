(*****************************************************************************

 The factorization system of esos and ff morphisms

 In this file, we construct, in any bicategory, the factorization system of eso 1-cells and
 fully faithful 1-cells. In the file `Eso.v`, we defined `eso_ff_factorization`,
 which only expresses the existence of the factorization. Here we show that
 it actually gives rise to an orthogonal factorization system. We also
 instantiate this to 1-types and to univalent categories.

 Contents
 1. The eso-ff factorization system
 2. The eso-ff factorization system for 1-types
 3. The eso-ff factorization system for univalent categories

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Eso.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderInvertibles.
Require Import UniMath.Bicategories.Morphisms.Properties.EsoProperties.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInOneTypes.
Require Import UniMath.Bicategories.Morphisms.Examples.EsosInBicatOfUnivCats.
Require Import UniMath.Bicategories.OrthogonalFactorization.Orthogonality.
Require Import UniMath.Bicategories.OrthogonalFactorization.FactorizationSystem.

Local Open Scope cat.

(**
 1. The eso-ff factorization system
 *)
Definition eso_ff_orthogonal_factorization_system
           {B : bicat}
           (fact_B : eso_ff_factorization B)
           (HB_2_1 : is_univalent_2_1 B)
  : orthogonal_factorization_system B.
Proof.
  use make_orthogonal_factorization_system.
  - exact (λ x y f, is_eso f).
  - exact (λ x y f, fully_faithful_1cell f).
  - abstract
      (intros ;
       apply isaprop_is_eso ;
       exact HB_2_1).
  - abstract
      (intros ;
       apply isaprop_fully_faithful_1cell).
  - intros x y f.
    exact (fact_B x y f).
  - intros x y f g τ Hf ; cbn.
    use (invertible_is_eso HB_2_1 Hf τ).
    apply property_from_invertible_2cell.
  - intros x y f g τ Hf ; cbn.
    use (fully_faithful_invertible τ _ Hf).
    apply property_from_invertible_2cell.
  - intros b₁ b₂ c₁ c₂ e m He Hm.
    apply He.
    exact Hm.
Defined.

(**
 2. The eso-ff factorization system for 1-types
 *)
Definition eso_ff_orthogonal_factorization_system_one_types
  : orthogonal_factorization_system one_types.
Proof.
  use eso_ff_orthogonal_factorization_system.
  - exact eso_ff_factorization_one_types.
  - exact one_types_is_univalent_2_1.
Defined.

(**
 3. The eso-ff factorization system for univalent categories
 *)
Definition eso_ff_orthogonal_factorization_system_bicat_of_univ_cats
  : orthogonal_factorization_system bicat_of_univ_cats.
Proof.
  use eso_ff_orthogonal_factorization_system.
  - exact eso_ff_factorization_bicat_of_univ_cats.
  - exact univalent_cat_is_univalent_2_1.
Defined.
