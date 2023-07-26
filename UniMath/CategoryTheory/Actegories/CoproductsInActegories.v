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
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.ProductActegory.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
(* Require Import UniMath.CategoryTheory.coslicecat. *)
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

  Definition actegory_bincoprod_antidistributor : ∏ (a : V) (c c' : C),
      BCP (leftwhiskering_functor Act a c) (leftwhiskering_functor Act a c') --> leftwhiskering_functor Act a (BCP c c')
    := bifunctor_bincoprod_antidistributor BCP BCP Act.

  Lemma actegory_bincoprod_antidistributor_nat_left (v : V) (cd1 cd2 : category_binproduct C C) (g : cd1 --> cd2) :
    actegory_bincoprod_antidistributor v (pr1 cd1) (pr2 cd1) · v ⊗^{Act}_{l} #(bincoproduct_functor BCP) g =
    #(bincoproduct_functor BCP) (v ⊗^{actegory_binprod Mon_V Act Act}_{l} g) · actegory_bincoprod_antidistributor v (pr1 cd2) (pr2 cd2).
  Proof.
    apply bincoprod_antidistributor_nat_left.
  Qed.

  Lemma actegory_bincoprod_antidistributor_nat_right (v1 v2 : V) (cd : category_binproduct C C) (f : v1 --> v2) :
    actegory_bincoprod_antidistributor v1 (pr1 cd) (pr2 cd) · f ⊗^{ Act}_{r} bincoproduct_functor BCP cd  =
    #(bincoproduct_functor BCP) (f ⊗^{ actegory_binprod Mon_V Act Act}_{r} cd) · actegory_bincoprod_antidistributor v2 (pr1 cd) (pr2 cd).
  Proof.
    apply bincoprod_antidistributor_nat_right.
  Qed.

  Lemma bincoprod_antidistributor_pentagon_identity (v w : V) (cd : category_binproduct C C) :
    # (bincoproduct_functor BCP) aα^{actegory_binprod Mon_V Act Act}_{v, w, cd} ·
                                      actegory_bincoprod_antidistributor v (w ⊗_{Act} pr1 cd) (w ⊗_{ Act} pr2 cd) ·
                                      v ⊗^{Act}_{l} actegory_bincoprod_antidistributor w (pr1 cd) (pr2 cd) =
      actegory_bincoprod_antidistributor (v ⊗_{Mon_V} w) (pr1 cd) (pr2 cd)
        · aα^{Act}_{v, w, bincoproduct_functor BCP cd}.
  Proof.
    etrans.
    { rewrite assoc'.
      apply postcompWithBinCoproductArrow. }
    etrans.
    2: { apply pathsinv0, postcompWithBinCoproductArrow. }
    apply maponpaths_12.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        rewrite assoc'.
        apply maponpaths.
        apply BinCoproductIn1Commutes. }
      etrans.
      2: { apply actegory_actornatleft. }
      rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
      apply maponpaths.
      apply BinCoproductIn1Commutes.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        rewrite assoc'.
        apply maponpaths.
        apply BinCoproductIn2Commutes. }
      etrans.
      2: { apply actegory_actornatleft. }
      rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
      apply maponpaths.
      apply BinCoproductIn2Commutes.
  Qed.

  Lemma bincoprod_antidistributor_triangle_identity (cd : category_binproduct C C) :
    #(bincoproduct_functor BCP) au^{actegory_binprod Mon_V Act Act}_{cd} =
      actegory_bincoprod_antidistributor I_{Mon_V} (pr1 cd) (pr2 cd) · au^{Act}_{bincoproduct_functor BCP cd}.
  Proof.
    etrans.
    2: { apply pathsinv0, postcompWithBinCoproductArrow. }
    cbn. unfold BinCoproductOfArrows.
    apply maponpaths_12; apply pathsinv0, actegory_unitornat.
  Qed.

  Lemma actegory_bincoprod_antidistributor_commutes_with_associativity_of_coproduct (v : V) (c d e : C) :
    #(bincoproduct_functor BCP) (catbinprodmor (actegory_bincoprod_antidistributor v c d) (identity (v ⊗_{Act} e))) ·
      actegory_bincoprod_antidistributor v (BCP c d) e ·
      v ⊗^{Act}_{l} bincoprod_associator_data BCP c d e =
    bincoprod_associator_data BCP (v ⊗_{Act} c) (v ⊗_{Act} d) (v ⊗_{Act} e) ·
      #(bincoproduct_functor BCP) (catbinprodmor (identity (v ⊗_{Act} c)) (actegory_bincoprod_antidistributor v d e)) ·
      actegory_bincoprod_antidistributor v c (BCP d e).
  Proof.
    apply bincoprod_antidistributor_commutes_with_associativity_of_coproduct.
  Qed.


  Definition actegory_bincoprod_distributor_data : UU := bifunctor_bincoprod_distributor_data BCP BCP Act.
  Identity Coercion actegory_bincoprod_distributor_data_coercion: actegory_bincoprod_distributor_data >-> bifunctor_bincoprod_distributor_data.

  Definition actegory_bincoprod_distributor_iso_law (δ : actegory_bincoprod_distributor_data) : UU :=
    bifunctor_bincoprod_distributor_iso_law BCP BCP Act δ.
  Definition actegory_bincoprod_distributor : UU := bifunctor_bincoprod_distributor BCP BCP Act.

  Definition actegory_bincoprod_distributor_to_data (δ : actegory_bincoprod_distributor) : actegory_bincoprod_distributor_data := pr1 δ.
  Coercion actegory_bincoprod_distributor_to_data : actegory_bincoprod_distributor >-> actegory_bincoprod_distributor_data.

  Definition bincoprod_functor_lineator_data (δ : actegory_bincoprod_distributor) :
    lineator_data Mon_V (actegory_binprod Mon_V Act Act) Act (bincoproduct_functor BCP).
  Proof.
    intros v cd.
    exact (δ v (pr1 cd) (pr2 cd)).
  Defined.

  Definition bincoprod_functor_lineator_strongly (δ : actegory_bincoprod_distributor) :
    lineator_strongly _ _ _ _ (bincoprod_functor_lineator_data δ).
  Proof.
    intros v cd.
    exists (actegory_bincoprod_antidistributor v (pr1 cd) (pr2 cd)).
    apply (pr2 δ v).
  Defined.

  Lemma bincoprod_functor_lineator_laxlaws (δ : actegory_bincoprod_distributor) :
    lineator_laxlaws _ _ _ _ (bincoprod_functor_lineator_data δ).
  Proof.
    red; repeat split.
    - red.
      intros v cd1 cd2 g.
      apply (z_iso_inv_to_right _ _ _ _ (_,,bincoprod_functor_lineator_strongly δ v _)).
      rewrite assoc'.
      apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly δ v _)).
      apply (bincoprod_antidistributor_nat_left _ _ Act).
    - red.
      intros v1 v2 cd f.
      apply (z_iso_inv_to_right _ _ _ _ (_,,bincoprod_functor_lineator_strongly δ _ _)).
      rewrite assoc'.
      apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly δ _ _)).
      apply (bincoprod_antidistributor_nat_right _ _ Act).
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

  Definition bincoprod_functor_lineator (δ : actegory_bincoprod_distributor) :
    lineator Mon_V (actegory_binprod Mon_V Act Act) Act (bincoproduct_functor BCP).
  Proof.
    use tpair.
    - exists (bincoprod_functor_lineator_data δ).
      exact (bincoprod_functor_lineator_laxlaws δ).
    - apply bincoprod_functor_lineator_strongly.
  Defined.


  Lemma bincoprod_distributor_commutes_with_associativity_of_coproduct (δ : actegory_bincoprod_distributor) (v : V) (c d e : C) :
    v ⊗^{Act}_{l} bincoprod_associator_data BCP c d e ·
      δ v c (BCP d e) ·
      #(bincoproduct_functor BCP) (catbinprodmor (identity (v ⊗_{Act} c)) (δ v d e)) =
    δ v (BCP c d) e ·
      #(bincoproduct_functor BCP) (catbinprodmor (δ v c d) (identity (v ⊗_{Act} e))) ·
      bincoprod_associator_data BCP (v ⊗_{Act} c) (v ⊗_{Act} d) (v ⊗_{Act} e).
  Proof.
    repeat rewrite assoc'.
    apply (z_iso_inv_to_left _ _ _ (_,,bincoprod_functor_lineator_strongly δ v (((BCP c d): C),, e))).
    repeat rewrite assoc.
    apply (z_iso_inv_to_right _ _ _ _ (functor_on_z_iso (functor_fix_fst_arg _ _ _
                                                           (bincoproduct_functor BCP) (v ⊗_{ Act} c))
                                         (_,,bincoprod_functor_lineator_strongly δ v (d,,e)))).
    apply (z_iso_inv_to_right _ _ _ _ (_,,bincoprod_functor_lineator_strongly δ v (c,,((BCP d e): C)))).
    repeat rewrite assoc'.
    apply (z_iso_inv_to_left _ _ _ (functor_on_z_iso (functor_fix_snd_arg _ _ _
                                                           (bincoproduct_functor BCP) (v ⊗_{ Act} e))
                                      (_,,bincoprod_functor_lineator_strongly δ v (c,,d)))).
    repeat rewrite assoc.
    apply actegory_bincoprod_antidistributor_commutes_with_associativity_of_coproduct.
  Qed.


End BinaryCoproduct.

Section Coproduct.

  Context {I : UU} {C : category} (CP : Coproducts I C) (Act : actegory Mon_V C).

  Definition actegory_coprod_antidistributor := bifunctor_coprod_antidistributor CP CP Act.

  Lemma actegory_coprod_antidistributor_nat_left (v : V)
    (cs1 cs2 : power_category I C) (g : cs1 --> cs2) :
    actegory_coprod_antidistributor v cs1 · v ⊗^{Act}_{l} #(coproduct_functor I CP) g =
      #(coproduct_functor I CP) (v ⊗^{actegory_power Mon_V I Act}_{l} g) ·
        actegory_coprod_antidistributor v cs2.
  Proof.
    apply coprod_antidistributor_nat_left.
  Qed.

  Lemma actegory_coprod_antidistributor_nat_right (v1 v2 : V)
    (cs : power_category I C) (f : v1 --> v2) :
    actegory_coprod_antidistributor v1 cs · f ⊗^{Act}_{r} coproduct_functor I CP cs  =
      #(coproduct_functor I CP) (f ⊗^{actegory_power Mon_V I Act}_{r} cs) ·
        actegory_coprod_antidistributor v2 cs.
  Proof.
    apply coprod_antidistributor_nat_right.
  Qed.

  Lemma coprod_antidistributor_pentagon_identity (v w : V) (cs : power_category I C) :
    # (coproduct_functor I CP) aα^{actegory_power Mon_V I Act}_{v, w, cs} ·
                                      actegory_coprod_antidistributor v (fun i => w ⊗_{Act} (cs i)) ·
                                      v ⊗^{Act}_{l} actegory_coprod_antidistributor w cs =
     actegory_coprod_antidistributor (v ⊗_{Mon_V} w) cs
        · aα^{Act}_{v, w, coproduct_functor I CP cs}.
  Proof.
    etrans.
    { rewrite assoc'.
      apply postcompWithCoproductArrow. }
    etrans.
    2: { apply pathsinv0, postcompWithCoproductArrow. }
    apply maponpaths; apply funextsec; intro i.
    etrans.
    { repeat rewrite assoc.
      apply cancel_postcomposition.
      rewrite assoc'.
      apply maponpaths.
      apply CoproductInCommutes. }
    etrans.
    2: { apply actegory_actornatleft. }
    rewrite assoc'.
    apply maponpaths.
    etrans.
    { apply pathsinv0, (functor_comp (leftwhiskering_functor Act v)). }
    apply maponpaths.
    apply CoproductInCommutes.
  Qed.

  Lemma coprod_antidistributor_triangle_identity (cs : power_category I C) :
    #(coproduct_functor I CP) au^{actegory_power Mon_V I Act}_{cs} =
      actegory_coprod_antidistributor I_{Mon_V} cs · au^{Act}_{coproduct_functor I CP cs}.
  Proof.
    etrans.
    2: { apply pathsinv0, postcompWithCoproductArrow. }
    cbn. unfold CoproductOfArrows.
    apply maponpaths, funextsec; intro i; apply pathsinv0, actegory_unitornat.
  Qed.

  Definition actegory_coprod_distributor_data : UU := bifunctor_coprod_distributor_data CP CP Act.
  Identity Coercion actegory_coprod_distributor_data_coercion:
    actegory_coprod_distributor_data >-> bifunctor_coprod_distributor_data.

  Definition actegory_coprod_distributor_iso_law (δ : actegory_coprod_distributor_data) : UU :=
    bifunctor_coprod_distributor_iso_law CP CP Act δ.
  Definition actegory_coprod_distributor : UU := bifunctor_coprod_distributor CP CP Act.

  Definition actegory_coprod_distributor_to_data (δ : actegory_coprod_distributor) :
    actegory_coprod_distributor_data := pr1 δ.
  Coercion actegory_coprod_distributor_to_data :
    actegory_coprod_distributor >-> actegory_coprod_distributor_data.

  Definition coprod_functor_lineator_data (δ : actegory_coprod_distributor_data) :
    lineator_data Mon_V (actegory_power Mon_V I Act) Act (coproduct_functor I CP).
  Proof.
    intros v cs.
    exact (δ v cs).
  Defined.

  Definition coprod_functor_lineator_strongly (δ : actegory_coprod_distributor) :
    lineator_strongly _ _ _ _ (coprod_functor_lineator_data δ).
  Proof.
    intros v cs.
    exists (actegory_coprod_antidistributor v cs).
    apply (pr2 δ).
  Defined.

  Lemma coprod_functor_lineator_laxlaws (δ : actegory_coprod_distributor) :
    lineator_laxlaws _ _ _ _ (coprod_functor_lineator_data δ).
  Proof.
    red; repeat split.
    - red.
      intros v cs1 cs2 g.
      apply (z_iso_inv_to_right _ _ _ _ (_,,coprod_functor_lineator_strongly δ v _)).
      rewrite assoc'.
      apply (z_iso_inv_to_left _ _ _ (_,,coprod_functor_lineator_strongly δ v _)).
      apply actegory_coprod_antidistributor_nat_left.
    - red.
      intros v1 v2 cs f.
      apply (z_iso_inv_to_right _ _ _ _ (_,,coprod_functor_lineator_strongly δ _ _)).
      rewrite assoc'.
      apply (z_iso_inv_to_left _ _ _ (_,,coprod_functor_lineator_strongly δ _ _)).
      apply actegory_coprod_antidistributor_nat_right.
    - red.
      intros v w cs.
      apply pathsinv0, (z_iso_inv_to_right _ _ _ _ (_,,coprod_functor_lineator_strongly δ _ _)).
      rewrite assoc'.
      apply (z_iso_inv_to_left _ _ _ (_,,coprod_functor_lineator_strongly δ _ _)).
      rewrite assoc.
      apply (z_iso_inv_to_right _ _ _ _ (functor_on_z_iso (leftwhiskering_functor Act v)
                                           (_,,coprod_functor_lineator_strongly δ _ _))).
      apply pathsinv0, coprod_antidistributor_pentagon_identity.
    - red.
      intro cs.
      apply pathsinv0, (z_iso_inv_to_left _ _ _ (_,,coprod_functor_lineator_strongly δ _ _)).
      apply pathsinv0, coprod_antidistributor_triangle_identity.
  Qed.

  Definition coprod_functor_lineator (δ : actegory_coprod_distributor) :
    lineator Mon_V (actegory_power Mon_V I Act) Act (coproduct_functor I CP).
  Proof.
    use tpair.
    - exists (coprod_functor_lineator_data δ).
      exact (coprod_functor_lineator_laxlaws δ).
    - apply coprod_functor_lineator_strongly.
  Defined.

End Coproduct.

End FixAMonoidalCategory.

Section TwoMonoidalCategories.

  Context {V : category} (Mon_V : monoidal V) {C : category} (Act : actegory Mon_V C)
    {W : category} (Mon_W : monoidal W)
    {F : W ⟶ V} (U : fmonoidal Mon_W Mon_V F).

  Let ActW : actegory Mon_W C := reindexed_actegory Mon_V Act Mon_W U.

Section BinaryCase.

  Context (BCP : BinCoproducts C) (δ : actegory_bincoprod_distributor Mon_V BCP Act).

  Definition reindexed_bincoprod_distributor_data : actegory_bincoprod_distributor_data Mon_W BCP ActW.
  Proof.
    intros w c c'.
    apply (δ (F w)).
  Defined.

  Lemma reindexed_bincoprod_distributor_law :
    actegory_bincoprod_distributor_iso_law _ _ _ reindexed_bincoprod_distributor_data.
  Proof.
    intros w c c'.
    split; unfold reindexed_bincoprod_distributor_data; apply (pr2 δ (F w)).
  Qed.

  Definition reindexed_bincoprod_distributor : actegory_bincoprod_distributor Mon_W BCP ActW :=
    _,,reindexed_bincoprod_distributor_law.

End BinaryCase.

Section IndexedCase.

  Context {I : UU} (CP : Coproducts I C) (δ : actegory_coprod_distributor Mon_V CP Act).

  Definition reindexed_coprod_distributor_data : actegory_coprod_distributor_data Mon_W CP ActW.
  Proof.
    intros w cs.
    apply (δ (F w)).
  Defined.

  Lemma reindexed_coprod_distributor_law :
    actegory_coprod_distributor_iso_law _ _ _ reindexed_coprod_distributor_data.
  Proof.
    intros w cs.
    split; unfold reindexed_coprod_distributor_data; apply (pr2 δ).
  Qed.

  Definition reindexed_coprod_distributor : actegory_coprod_distributor Mon_W CP ActW :=
    _,,reindexed_coprod_distributor_law.

End IndexedCase.

End TwoMonoidalCategories.
