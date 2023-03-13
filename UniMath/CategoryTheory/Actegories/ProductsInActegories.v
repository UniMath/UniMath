(** studies products in the categories on which is being acted in actegories

author: Ralph Matthes, 2023
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.ProductActegory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.binproducts.


Local Open Scope cat.

Import BifunctorNotations.

Section FixAMonoidalCategory.

  Context {V : category} (Mon_V : monoidal V). (** given the monoidal category that acts upon categories *)


Section BinaryProduct.

  Context {C : category} (BP : BinProducts C) (Act : actegory Mon_V C).

  Definition binprod_collector_data (v : V) (c d : C):
      v ⊗_{Act} (BP c d) --> BP (v ⊗_{Act} c) (v ⊗_{Act} d).
  Proof.
    apply BinProductArrow; apply leftwhiskering_on_morphisms; [apply BinProductPr1 | apply BinProductPr2 ].
  Defined.

  Definition binprod_functor_lineator_data:
    lineator_data Mon_V (actegory_binprod Mon_V Act Act) Act (binproduct_functor BP).
  Proof.
    intros v cd.
    exact (binprod_collector_data v (pr1 cd) (pr2 cd)).
  Defined.

 Lemma binprod_functor_lineator_laxlaws:
    lineator_laxlaws _ _ _ _ binprod_functor_lineator_data.
  Proof.
    red; repeat split.
    - red.
      intros v cd1 cd2 g.
      etrans.
      { apply precompWithBinProductArrow. }
      etrans.
      2: { apply pathsinv0, postcompWithBinProductArrow. }
      apply maponpaths_12.
      + etrans.
        { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
        etrans.
        2: { cbn. apply (functor_comp (leftwhiskering_functor Act v)). }
        apply maponpaths.
        etrans.
        { apply BinProductOfArrowsPr1. }
        apply idpath.
      + etrans.
        { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
        etrans.
        2: { cbn. apply (functor_comp (leftwhiskering_functor Act v)). }
        apply maponpaths.
        etrans.
        { apply BinProductOfArrowsPr2. }
        apply idpath.
    - red.
      intros v1 v2 cd f.
      etrans.
      { apply precompWithBinProductArrow. }
      etrans.
      2: { apply pathsinv0, postcompWithBinProductArrow. }
      apply maponpaths_12.
      + etrans.
        { apply (bifunctor_equalwhiskers Act). }
        apply idpath.
      + etrans.
        { apply (bifunctor_equalwhiskers Act). }
        apply idpath.
    - red.
      intros v w cd.
      etrans.
      { apply postcompWithBinProductArrow. }
      etrans.
      2: { apply pathsinv0, precompWithBinProductArrow. }
      apply maponpaths_12.
      + cbn.
        etrans.
        2: { rewrite assoc'.
             apply maponpaths.
             etrans.
             2: { apply (functor_comp (leftwhiskering_functor Act v)). }
             apply maponpaths.
             apply pathsinv0, BinProductPr1Commutes.
        }
        apply pathsinv0, actegory_actornatleft.
      + cbn.
        etrans.
        2: { rewrite assoc'.
             apply maponpaths.
             etrans.
             2: { apply (functor_comp (leftwhiskering_functor Act v)). }
             apply maponpaths.
             apply pathsinv0, BinProductPr2Commutes.
        }
        apply pathsinv0, actegory_actornatleft.
    - red.
      intro cd.
      etrans.
      { apply postcompWithBinProductArrow. }
      cbn.
      etrans.
      2: { apply pathsinv0, BinProductArrowEta. }
      apply maponpaths_12; apply actegory_unitornat.
  Qed.

  Definition binprod_functor_lax_lineator:
    lineator_lax Mon_V (actegory_binprod Mon_V Act Act) Act (binproduct_functor BP).
  Proof.
    exists binprod_functor_lineator_data.
    exact binprod_functor_lineator_laxlaws.
  Defined.

End BinaryProduct.

End FixAMonoidalCategory.
