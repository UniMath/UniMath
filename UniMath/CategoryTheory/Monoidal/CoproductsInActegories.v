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

  Lemma bincoprod_antidistributor_nat_left (v : V) (cd1 cd2 : category_binproduct C C) (g : category_binproduct C C ⟦ cd1, cd2 ⟧) :
    bincoprod_antidistributor_data v (pr1 cd1) (pr2 cd1) · v ⊗^{Act}_{l} #(bincoproduct_functor BCP) g =
    #(bincoproduct_functor BCP) (v ⊗^{actegory_binprod Mon_V Act Act}_{l} g) · bincoprod_antidistributor_data v (pr1 cd2) (pr2 cd2).
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

  Lemma bincoprod_antidistributor_nat_right (v1 v2 : V) (cd : category_binproduct C C) (f : V ⟦ v1, v2 ⟧) :
    bincoprod_antidistributor_data v1 (pr1 cd) (pr2 cd) · f ⊗^{ Act}_{r} bincoproduct_functor BCP cd  =
    #(bincoproduct_functor BCP) (f ⊗^{ actegory_binprod Mon_V Act Act}_{r} cd) · bincoprod_antidistributor_data v2 (pr1 cd) (pr2 cd).
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
      apply pathsinv0, bifunctor_equalwhiskers.
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
      apply pathsinv0, bifunctor_equalwhiskers.
  Qed.

  Lemma bincoprod_antidistributor_pentagon_identity (v w : V) (cd : category_binproduct C C) :
    # (bincoproduct_functor BCP) aα^{actegory_binprod Mon_V Act Act}_{v, w, cd} ·
                                      bincoprod_antidistributor_data v (w ⊗_{Act} pr1 cd) (w ⊗_{ Act} pr2 cd) ·
                                      v ⊗^{Act}_{l} bincoprod_antidistributor_data w (pr1 cd) (pr2 cd) =
      bincoprod_antidistributor_data (v ⊗_{Mon_V} w) (pr1 cd) (pr2 cd)
        · aα^{Act}_{v, w, bincoproduct_functor BCP cd}.
  Proof.
    use BinCoproductArrowsEq.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        etrans.
        { apply cancel_postcomposition.
          apply BinCoproductOfArrowsIn1. }
        rewrite assoc'.
        apply maponpaths.
        apply BinCoproductIn1Commutes.
      }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply pathsinv0, BinCoproductIn1Commutes. }
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
      unfold bincoprod_antidistributor_data.
      rewrite BinCoproductIn1Commutes.
      etrans.
      2: { apply actegory_actornatleft. }
      apply idpath.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        etrans.
        { apply cancel_postcomposition.
          apply BinCoproductOfArrowsIn2. }
        rewrite assoc'.
        apply maponpaths.
        apply BinCoproductIn2Commutes.
      }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply pathsinv0, BinCoproductIn2Commutes. }
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
      unfold bincoprod_antidistributor_data.
      rewrite BinCoproductIn2Commutes.
      etrans.
      2: { apply actegory_actornatleft. }
      apply idpath.
  Qed.

  Lemma bincoprod_antidistributor_triangle_identity (cd : category_binproduct C C) :
    #(bincoproduct_functor BCP) au^{actegory_binprod Mon_V Act Act}_{cd} =
      bincoprod_antidistributor_data I_{Mon_V} (pr1 cd) (pr2 cd) · au^{Act}_{bincoproduct_functor BCP cd}.
  Proof.
    use BinCoproductArrowsEq.
    - etrans.
      { apply BinCoproductOfArrowsIn1. }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply pathsinv0, BinCoproductIn1Commutes. }
      etrans.
      2: { apply pathsinv0, actegory_unitornat. }
      apply idpath.
    - etrans.
      { apply BinCoproductOfArrowsIn2. }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply pathsinv0, BinCoproductIn2Commutes. }
      etrans.
      2: { apply pathsinv0, actegory_unitornat. }
      apply idpath.
  Qed.

  Definition bincoprod_associator_data (c d e : C) : BCP (BCP c d) e --> BCP c (BCP d e).
  Proof.
    use BinCoproductArrow.
    - use BinCoproductArrow.
      + apply BinCoproductIn1.
      + refine (_ · BinCoproductIn2 _).
        apply BinCoproductIn1.
    - refine (_ · BinCoproductIn2 _).
      apply BinCoproductIn2.
  Defined.

  Definition bincoprod_associatorinv_data (c d e : C) : BCP c (BCP d e) --> BCP (BCP c d) e.
  Proof.
    use BinCoproductArrow.
    - refine (_ · BinCoproductIn1 _).
      apply BinCoproductIn1.
    - use BinCoproductArrow.
      + refine (_ · BinCoproductIn1 _).
        apply BinCoproductIn2.
      + apply BinCoproductIn2.
  Defined.

  Lemma bincoprod_associator_inverses (c d e : C) :
    is_inverse_in_precat (bincoprod_associator_data c d e) (bincoprod_associatorinv_data c d e).
  Proof.
    split.
    + apply pathsinv0, BinCoproduct_endo_is_identity.
      * rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply BinCoproductIn1Commutes. }
        use BinCoproductArrowsEq.
        -- repeat rewrite assoc.
           etrans.
           { apply cancel_postcomposition.
             apply BinCoproductIn1Commutes. }
           etrans.
           { apply BinCoproductIn1Commutes. }
           apply idpath.
        -- repeat rewrite assoc.
           etrans.
           { apply cancel_postcomposition.
             apply BinCoproductIn2Commutes. }
           etrans.
           { rewrite assoc'.
             apply maponpaths.
             apply BinCoproductIn2Commutes. }
           apply BinCoproductIn1Commutes.
      * rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply BinCoproductIn2Commutes. }
        etrans.
        { rewrite assoc'.
          apply maponpaths.
          apply BinCoproductIn2Commutes. }
        apply BinCoproductIn2Commutes.
    + apply pathsinv0, BinCoproduct_endo_is_identity.
      * rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply BinCoproductIn1Commutes. }
        etrans.
        { rewrite assoc'.
          apply maponpaths.
          apply BinCoproductIn1Commutes. }
        apply BinCoproductIn1Commutes.
      * rewrite assoc.
        etrans.
        { apply cancel_postcomposition.
          apply BinCoproductIn2Commutes. }
        use BinCoproductArrowsEq.
        -- repeat rewrite assoc.
           etrans.
           { apply cancel_postcomposition.
             apply BinCoproductIn1Commutes. }
           etrans.
           { rewrite assoc'.
             apply maponpaths.
             apply BinCoproductIn1Commutes. }
           apply BinCoproductIn2Commutes.
        -- repeat rewrite assoc.
           etrans.
           { apply cancel_postcomposition.
             apply BinCoproductIn2Commutes. }
           etrans.
           { apply BinCoproductIn2Commutes. }
           apply idpath.
  Qed.


  Definition bincoprod_associator (c d e : C) : z_iso (BCP (BCP c d) e) (BCP c (BCP d e)) :=
    bincoprod_associator_data c d e,, bincoprod_associatorinv_data c d e,, bincoprod_associator_inverses c d e.

  Lemma bincoprod_antidistributor_commutes_with_associativity_of_coproduct (v : V) (c d e : C) :
    #(bincoproduct_functor BCP) (catbinprodmor (bincoprod_antidistributor_data v c d) (identity (v ⊗_{Act} e))) ·
      bincoprod_antidistributor_data v (BCP c d) e ·
      v ⊗^{Act}_{l} bincoprod_associator_data c d e =
    bincoprod_associator_data (v ⊗_{Act} c) (v ⊗_{Act} d) (v ⊗_{Act} e) ·
      #(bincoproduct_functor BCP) (catbinprodmor (identity (v ⊗_{Act} c)) (bincoprod_antidistributor_data v d e)) ·
      bincoprod_antidistributor_data v c (BCP d e).
  Proof.
    use BinCoproductArrowsEq.
    - etrans.
      { repeat rewrite assoc.
        do 2 apply cancel_postcomposition.
        apply BinCoproductOfArrowsIn1. }
      cbn.
      etrans.
      2: { repeat rewrite assoc.
           do 2 apply cancel_postcomposition.
           apply pathsinv0, BinCoproductIn1Commutes. }
      use BinCoproductArrowsEq.
      + etrans.
        { repeat rewrite assoc.
          do 3 apply cancel_postcomposition.
          apply BinCoproductIn1Commutes. }
        etrans.
        { apply cancel_postcomposition.
          rewrite assoc'.
          apply maponpaths.
          apply BinCoproductIn1Commutes. }
        etrans.
        2: { repeat rewrite assoc.
             do 2 apply cancel_postcomposition.
             apply pathsinv0, BinCoproductIn1Commutes. }
        etrans.
        2: { apply cancel_postcomposition.
             apply pathsinv0, BinCoproductOfArrowsIn1. }
        rewrite id_left.
        etrans.
        2: { apply pathsinv0, BinCoproductIn1Commutes. }
        etrans.
        { apply cancel_postcomposition.
          apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
        etrans.
        { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
        apply maponpaths.
        rewrite assoc'.
        unfold bincoprod_associator_data.
        do 2 rewrite BinCoproductIn1Commutes.
        apply idpath.
      + etrans.
        { repeat rewrite assoc.
          do 3 apply cancel_postcomposition.
          apply BinCoproductIn2Commutes. }
        etrans.
        { apply cancel_postcomposition.
          rewrite assoc'.
          apply maponpaths.
          apply BinCoproductIn1Commutes. }
        etrans.
        2: { repeat rewrite assoc.
             do 2 apply cancel_postcomposition.
             apply pathsinv0, BinCoproductIn2Commutes. }
        etrans.
        2: { apply cancel_postcomposition.
             rewrite assoc'.
             apply maponpaths.
             apply pathsinv0, BinCoproductOfArrowsIn2. }
        etrans.
        2: { repeat rewrite assoc.
             do 2 apply cancel_postcomposition.
             apply pathsinv0, BinCoproductIn1Commutes. }
        etrans.
        2: { rewrite assoc'.
             apply maponpaths.
             apply pathsinv0, BinCoproductIn2Commutes. }
        etrans.
        { apply cancel_postcomposition.
          apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
        etrans.
        { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
        etrans.
        2: { apply (functor_comp (leftwhiskering_functor Act v)). }
        apply maponpaths.
        rewrite assoc'.
        unfold bincoprod_associator_data.
        rewrite BinCoproductIn1Commutes.
        rewrite BinCoproductIn2Commutes.
        apply idpath.
    - etrans.
      { repeat rewrite assoc.
        do 2 apply cancel_postcomposition.
        apply BinCoproductOfArrowsIn2. }
      cbn.
      rewrite id_left.
      etrans.
      2: { repeat rewrite assoc.
           do 2 apply cancel_postcomposition.
           apply pathsinv0, BinCoproductIn2Commutes. }
      etrans.
      { apply cancel_postcomposition.
        apply BinCoproductIn2Commutes. }
      etrans.
      2: { apply cancel_postcomposition.
           rewrite assoc'.
           apply maponpaths.
           apply pathsinv0, BinCoproductOfArrowsIn2. }
      etrans.
      2: { repeat rewrite assoc.
           do 2 apply cancel_postcomposition.
           apply pathsinv0, BinCoproductIn2Commutes. }
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply pathsinv0, BinCoproductIn2Commutes. }
      etrans.
      { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
      etrans.
      2: { apply (functor_comp (leftwhiskering_functor Act v)). }
      apply maponpaths.
      apply BinCoproductIn2Commutes.
  Qed.


  (** axiomatize extra requirements *)

  Definition bincoprod_distributor_data : UU := ∏ (v : V) (c d : C),
      v ⊗_{Act} (BCP c d) --> BCP (v ⊗_{Act} c) (v ⊗_{Act} d).

  Identity Coercion bincoprod_distributor_data_funclass: bincoprod_distributor_data >-> Funclass.

  Definition bincoprod_distributor_iso_law (δ : bincoprod_distributor_data) : UU :=
    ∏ (v : V) (c d : C), is_inverse_in_precat (δ v c d) (bincoprod_antidistributor_data v c d).

  Definition bincoprod_functor_lineator_data (δ : bincoprod_distributor_data) :
    lineator_data Mon_V (actegory_binprod Mon_V Act Act) Act (bincoproduct_functor BCP).
  Proof.
    intros v cd.
    exact (δ v (pr1 cd) (pr2 cd)).
  Defined.

  Definition bincoprod_distributor : UU := ∑ δ : bincoprod_distributor_data, bincoprod_distributor_iso_law δ.

  Definition bincoprod_distributor_to_data (δ : bincoprod_distributor) : bincoprod_distributor_data := pr1 δ.
  Coercion bincoprod_distributor_to_data : bincoprod_distributor >-> bincoprod_distributor_data.

  Definition bincoprod_functor_lineator_strongly (δ : bincoprod_distributor) :
    lineator_strongly _ _ _ _ (bincoprod_functor_lineator_data δ).
  Proof.
    intros v cd.
    exists (bincoprod_antidistributor_data v (pr1 cd) (pr2 cd)).
    apply (pr2 δ).
  Defined.

  Lemma bincoprod_functor_lineator_laxlaws (δ : bincoprod_distributor) :
    lineator_laxlaws _ _ _ _ (bincoprod_functor_lineator_data δ).
  Proof.
    red; repeat split.
    - red.
      intros v cd1 cd2 g.
      apply (z_iso_inv_to_right _ _ _ _ (_,,bincoprod_functor_lineator_strongly δ v _)).
      rewrite assoc'.
      apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly δ v _)).
      apply bincoprod_antidistributor_nat_left.
    - red.
      intros v1 v2 cd f.
      apply (z_iso_inv_to_right _ _ _ _ (_,,bincoprod_functor_lineator_strongly δ _ _)).
      rewrite assoc'.
      apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly δ _ _)).
      apply bincoprod_antidistributor_nat_right.
    - red.
      intros v w cd.
      apply pathsinv0, (z_iso_inv_to_right _ _ _ _ (_,,bincoprod_functor_lineator_strongly δ _ _)).
      rewrite assoc'.
      apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly δ _ _)).
      rewrite assoc.
      apply (z_iso_inv_to_right _ _ _ _ (functor_on_z_iso (leftwhiskering_functor Act v)
                                           (_,,bincoprod_functor_lineator_strongly δ _ _))).
      apply pathsinv0, bincoprod_antidistributor_pentagon_identity.
    - red.
      intro cd.
      apply pathsinv0, (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly δ _ _)).
      apply pathsinv0, bincoprod_antidistributor_triangle_identity.
  Qed.

  Definition bincoprod_functor_lineator (δ : bincoprod_distributor) :
    lineator Mon_V (actegory_binprod Mon_V Act Act) Act (bincoproduct_functor BCP).
  Proof.
    use tpair.
    - exists (bincoprod_functor_lineator_data δ).
      exact (bincoprod_functor_lineator_laxlaws δ).
    - apply bincoprod_functor_lineator_strongly.
  Defined.

(* TODO: Lemma bincoprod_distributor_commutes_with_associativity_of_coproduct *)


End BinaryCoproduct.

End FixAMonoidalCategory.
