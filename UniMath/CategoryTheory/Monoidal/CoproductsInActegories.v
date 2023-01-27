(** studies coproducts in the categories on which is being acted in actegories

author: Ralph Matthes, 2023
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.ProductActegory.
(* Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.coslicecat. *)
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
(* Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects. *)

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
Import ActegoryNotations.

Section FixAMonoidalCategory.

  Context {V : category} (Mon_V : monoidal V). (** given the monoidal category that acts upon categories *)


Section BinaryCoproduct.

  Context {C : category} (BCP : BinCoproducts C) (Act : actegory Mon_V C).

  Definition bincoprod_antidistributor_data (v : V) (c d : C) :
    BCP (v ⊗_{Act} c) (v ⊗_{Act} d) --> v ⊗_{Act} (BCP c d).
  Proof.
    use BinCoproductArrow; apply leftwhiskering_on_morphisms; [apply BinCoproductIn1 | apply BinCoproductIn2 ].
  Defined.

  Lemma bincoprod_antidistributor_nat_left (v : V) (x1 x2 : category_binproduct C C) (g : category_binproduct C C ⟦ x1, x2 ⟧) :
    bincoprod_antidistributor_data v (pr1 x1) (pr2 x1) · v ⊗^{Act}_{l} #(bincoproduct_functor BCP) g =
     #(bincoproduct_functor BCP) (v ⊗^{actegory_binprod Mon_V Act Act}_{l} g) · bincoprod_antidistributor_data v (pr1 x2) (pr2 x2).
  Proof.
    use BinCoproductArrowsEq.
    - etrans.
      { rewrite assoc.
        apply cancel_postcomposition.
        apply BinCoproductIn1Commutes. }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           cbn.
           apply pathsinv0,  BinCoproductOfArrowsIn1. }
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply pathsinv0, BinCoproductIn1Commutes. }
      etrans.
      { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
      etrans.
      2: { apply (functor_comp (leftwhiskering_functor Act v)). }
      apply maponpaths.
      apply BinCoproductOfArrowsIn1.
    - etrans.
      { rewrite assoc.
        apply cancel_postcomposition.
        apply BinCoproductIn2Commutes. }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           cbn.
           apply pathsinv0,  BinCoproductOfArrowsIn2. }
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply pathsinv0, BinCoproductIn2Commutes. }
      etrans.
      { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
      etrans.
      2: { apply (functor_comp (leftwhiskering_functor Act v)). }
      apply maponpaths.
      apply BinCoproductOfArrowsIn2.
  Qed.


  Definition bincoprod_distributor_data : UU := ∏ (v : V) (c d : C),
      v ⊗_{Act} (BCP c d) --> BCP (v ⊗_{Act} c) (v ⊗_{Act} d).

  Definition bincoprod_distributor_iso_law (δ : bincoprod_distributor_data) : UU :=
    ∏ (v : V) (c d : C), is_inverse_in_precat (δ v c d) (bincoprod_antidistributor_data v c d).

  Definition bincoprod_functor_lineator_data (δ : bincoprod_distributor_data) :
    lineator_data Mon_V (actegory_binprod Mon_V Act Act) Act (bincoproduct_functor BCP).
  Proof.
    intros v cd.
    exact (δ v (pr1 cd) (pr2 cd)).
  Defined.

  Definition bincoprod_functor_lineator_strongly (δ : bincoprod_distributor_data) (δisinverse : bincoprod_distributor_iso_law δ) :
    lineator_strongly _ _ _ _ (bincoprod_functor_lineator_data δ).
  Proof.
    intros v cd.
    exists (bincoprod_antidistributor_data v (pr1 cd) (pr2 cd)).
    apply δisinverse.
  Defined.

  Lemma bincoprod_functor_lineator_laxlaws (δ : bincoprod_distributor_data) (δisinverse : bincoprod_distributor_iso_law δ)  :
    lineator_laxlaws _ _ _ _ (bincoprod_functor_lineator_data δ).
  Proof.
    red; repeat split.
    - red.
      intros v x1 x2 g.
      apply (z_iso_inv_to_right _ _ _ _ (_,,bincoprod_functor_lineator_strongly δ δisinverse v _)).
      rewrite assoc'.
      apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly δ δisinverse v _)).
      apply bincoprod_antidistributor_nat_left.




      Abort.


End BinaryCoproduct.



End FixAMonoidalCategory.
