(** Construction of actegory morphisms

Part Generalization of pointed distributivity laws to lifted distributivity laws in general monads
- definition
- construction of actegory morphism from it
- composition

Part Closure of the notion of actegory morphisms under
- the pointwise binary product of functors
- the pointwise binary coproduct of functors


author: Ralph Matthes 2022
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Actegories.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.Actegories.CoproductsInActegories.
Require Import UniMath.CategoryTheory.Actegories.ProductsInActegories.
Require Import UniMath.CategoryTheory.Actegories.ProductActegory.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
Import ActegoryNotations.

Section LiftedLineatorAndLiftedDistributivity.

  Context {V : category} (Mon_V : monoidal V)
          {W : category} (Mon_W : monoidal W)
          {F : W ⟶ V} (U : fmonoidal Mon_W Mon_V F).


Section LiftedLaxLineator.

  Context {C D : category} (ActC : actegory Mon_V C) (ActD : actegory Mon_V D).

Section OnFunctors.

  Context {H : functor C D} (ll : lineator_lax Mon_V ActC ActD H).

  Definition lifted_lax_lineator_data : lineator_data Mon_W (lifted_actegory Mon_V ActC Mon_W U)
                                                            (lifted_actegory Mon_V ActD Mon_W U) H.
  Proof.
    intros w c. exact (ll (F w) c).
  Defined.

  Lemma lifted_lax_lineator_laws : lineator_laxlaws Mon_W (lifted_actegory Mon_V ActC Mon_W U)
                                     (lifted_actegory Mon_V ActD Mon_W U) H lifted_lax_lineator_data.
  Proof.
    split4.
    - intro; intros. apply (lineator_linnatleft _ _ _ _ ll).
    - intro; intros. apply (lineator_linnatright _ _ _ _ ll).
    - intro; intros. cbn. unfold lifted_lax_lineator_data, lifted_actor_data.
      etrans.
      2: { repeat rewrite assoc'. apply maponpaths.
           rewrite assoc.
           apply (lineator_preservesactor _ _ _ _ ll). }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply pathsinv0, lineator_linnatright. }
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply functor_comp. }
      apply idpath.
    - intro; intros. cbn. unfold lifted_lax_lineator_data, lifted_action_unitor_data.
      etrans.
      2: { apply maponpaths.
           apply (lineator_preservesunitor _ _ _ _ ll). }
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           apply pathsinv0, lineator_linnatright. }
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply functor_comp. }
      apply idpath.
  Qed.

  Definition lifted_lax_lineator : lineator_lax Mon_W (lifted_actegory Mon_V ActC Mon_W U)
                                                      (lifted_actegory Mon_V ActD Mon_W U) H :=
    _,,lifted_lax_lineator_laws.

End OnFunctors.

Section OnNaturalTransformations.

  Context {H : functor C D} (Hl : lineator_lax Mon_V ActC ActD H)
    {K : functor C D} (Kl : lineator_lax Mon_V ActC ActD K)
    {ξ : H ⟹ K} (islntξ : is_linear_nat_trans Hl Kl ξ).

  Lemma preserves_linearity_lifted_lax_lineator :
    is_linear_nat_trans (lifted_lax_lineator Hl) (lifted_lax_lineator Kl) ξ.
  Proof.
    intros w c.
    apply islntξ.
  Qed.

End OnNaturalTransformations.

End LiftedLaxLineator.

Section LiftedDistributivity.

Section FixAnObject.

  Context {v0 : V}.

  Definition lifteddistributivity_data: UU := ∏ (w: W), F w ⊗_{Mon_V} v0 --> v0 ⊗_{Mon_V} F w.

  Identity Coercion lifteddistributivity_data_funclass: lifteddistributivity_data >-> Funclass.

Section δ_laws.

  Context (δ : lifteddistributivity_data).

  Definition lifteddistributivity_nat: UU := is_nat_trans (functor_composite F (rightwhiskering_functor Mon_V v0))
                                                           (functor_composite F (leftwhiskering_functor Mon_V v0)) δ.

  Definition lifteddistributivity_tensor_body (w w' : W): UU :=
    δ (w ⊗_{Mon_W} w') = pr1 (fmonoidal_preservestensorstrongly U w w') ⊗^{Mon_V}_{r} v0 · α_{Mon_V} _ _ _ ·
                           F w ⊗^{Mon_V}_{l} δ w' · αinv_{Mon_V} _ _ _ · δ w ⊗^{Mon_V}_{r} F w' ·
                           α_{Mon_V} _ _ _ · v0 ⊗^{Mon_V}_{l} fmonoidal_preservestensordata U w w'.

  Definition lifteddistributivity_tensor: UU := ∏ (w w' : W), lifteddistributivity_tensor_body w w'.

  Definition lifteddistributivity_unit: UU :=
    δ I_{Mon_W} = pr1 (fmonoidal_preservesunitstrongly U) ⊗^{Mon_V}_{r} v0 · lu_{Mon_V} v0 ·
                  ruinv_{Mon_V} v0 · v0 ⊗^{Mon_V}_{l} fmonoidal_preservesunit U.


End δ_laws.

Definition lifteddistributivity: UU := ∑ δ : lifteddistributivity_data,
      lifteddistributivity_nat δ × lifteddistributivity_tensor δ × lifteddistributivity_unit δ.

Definition lifteddistributivity_lddata (δ : lifteddistributivity): lifteddistributivity_data := pr1 δ.
Coercion lifteddistributivity_lddata : lifteddistributivity >-> lifteddistributivity_data.

Definition lifteddistributivity_ldnat (δ : lifteddistributivity): lifteddistributivity_nat δ := pr12 δ.
Definition lifteddistributivity_ldtensor (δ : lifteddistributivity): lifteddistributivity_tensor δ := pr122 δ.
Definition lifteddistributivity_ldunit (δ : lifteddistributivity): lifteddistributivity_unit δ := pr222 δ.



Section ActegoryMorphismFromLiftedDistributivity.

  Context (δ : lifteddistributivity) {C : category} (ActV : actegory Mon_V C).

  Local Definition FF: C ⟶ C := leftwhiskering_functor ActV v0.
  Local Definition ActW: actegory Mon_W C := lifted_actegory Mon_V ActV Mon_W U.

  Definition lineator_data_from_δ: lineator_data Mon_W ActW ActW FF.
  Proof.
    intros w x. unfold FF. cbn.
    exact (aαinv^{ActV}_{F w, v0, x} · δ w ⊗^{ActV}_{r} x · aα^{ActV}_{v0, F w, x}).
  Defined.

  Lemma lineator_laxlaws_from_δ: lineator_laxlaws Mon_W ActW ActW FF lineator_data_from_δ.
  Proof.
    assert (δ_nat := lifteddistributivity_ldnat δ).
    do 2 red in δ_nat. cbn in δ_nat.
    repeat split; red; intros; unfold lineator_data_from_δ; try unfold lifted_actor_data; try unfold lifted_action_unitor_data; cbn;
      try unfold lifted_actor_data; try unfold lifted_action_unitor_data; cbn.
    - etrans.
      { repeat rewrite assoc.
        do 2 apply cancel_postcomposition.
        apply actorinv_nat_leftwhisker. }
      etrans.
      2: { repeat rewrite assoc'.
           do 2 apply maponpaths.
           apply pathsinv0, actegory_actornatleft.
      }
      repeat rewrite assoc'.
      apply maponpaths.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0, (bifunctor_equalwhiskers ActV).
    - etrans.
      { repeat rewrite assoc.
        do 2 apply cancel_postcomposition.
        apply actorinv_nat_rightwhisker. }
      etrans.
      2: { repeat rewrite assoc'.
           do 2 apply maponpaths.
           apply pathsinv0, actegory_actornatleftright.
      }
      repeat rewrite assoc'.
      apply maponpaths.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      etrans.
      { apply pathsinv0, (functor_comp (rightwhiskering_functor ActV x)). }
      etrans.
      2: { apply (functor_comp (rightwhiskering_functor ActV x)). }
      apply maponpaths.
      apply δ_nat.
    - etrans.
      { apply maponpaths.
        apply (functor_comp (leftwhiskering_functor ActV v0)). }
      cbn.
      etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        repeat rewrite assoc'.
        do 2 apply maponpaths.
        apply actegory_actornatleftright.
      }
      etrans.
      { repeat rewrite assoc.
        do 2 apply cancel_postcomposition.
        repeat rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, (functor_comp (rightwhiskering_functor ActV x)).
      }
      cbn.
      etrans.
      { do 2 apply cancel_postcomposition.
        do 2 apply maponpaths.
        rewrite (lifteddistributivity_ldtensor δ).
        repeat rewrite assoc'.
        do 6 apply maponpaths.
        etrans.
        { apply pathsinv0, (functor_comp (leftwhiskering_functor Mon_V v0)). }
        apply (functor_id_id _ _ (leftwhiskering_functor Mon_V v0)).
        apply (pr2 (fmonoidal_preservestensorstrongly U v w)).
      }
      rewrite id_right.
      etrans.
      { do 2 apply cancel_postcomposition.
        etrans.
        { apply maponpaths.
          apply (functor_comp (rightwhiskering_functor ActV x)). }
        cbn.
        rewrite assoc.
        apply cancel_postcomposition.
        apply pathsinv0, actorinv_nat_rightwhisker.
      }
      repeat rewrite assoc'.
      apply maponpaths.
      (* the extra effort for having an abstract strong monoidal functor has now been accomplished *)
      apply (z_iso_inv_on_right _ _ _ (z_iso_from_actor_iso Mon_V ActV _ _ _)).
      etrans.
      { apply cancel_postcomposition.
        repeat rewrite assoc.
        apply (functor_comp (rightwhiskering_functor ActV x)). }
      cbn.
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        apply actegory_pentagonidentity.
      }
      repeat rewrite assoc.
      apply cancel_postcomposition.
      rewrite <- actegory_pentagonidentity.
      etrans.
      { apply cancel_postcomposition.
        repeat rewrite assoc'.
        apply (functor_comp (rightwhiskering_functor ActV x)). }
      cbn.
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      2: { apply maponpaths.
           etrans.
           2: { apply maponpaths.
                apply cancel_postcomposition.
                apply pathsinv0, (functor_comp (leftwhiskering_functor ActV (F v))). }
           cbn.
           repeat rewrite assoc.
           do 3 apply cancel_postcomposition.
           etrans.
           2: { apply (functor_comp (leftwhiskering_functor ActV (F v))). }
           apply pathsinv0, (functor_id_id _ _ (leftwhiskering_functor ActV (F v))).
           apply (pr1 (actegory_actorisolaw Mon_V ActV _ _ _)).
      }
      rewrite id_left.
      etrans.
      2: { apply maponpaths.
           rewrite assoc'.
           apply cancel_postcomposition.
           apply pathsinv0, (functor_comp (leftwhiskering_functor ActV (F v))).
      }
      cbn.
      etrans.
      2: { repeat rewrite assoc.
           do 3 apply cancel_postcomposition.
           apply pathsinv0, actegory_actornatleftright. }
      etrans.
      { apply cancel_postcomposition.
        apply (functor_comp (rightwhiskering_functor ActV x)). }
      cbn.
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply cancel_postcomposition.
        apply (functor_comp (rightwhiskering_functor ActV x)). }
      cbn.
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, actegory_actornatright. }
      repeat rewrite assoc.
      apply cancel_postcomposition.
      (* only a variant of the pentagon law with some inverses is missing here *)
      apply (z_iso_inv_on_left _ _ _ _ (z_iso_from_actor_iso Mon_V ActV _ _ _)).
      cbn.
      rewrite assoc'.
      rewrite <- actegory_pentagonidentity.
      etrans.
      2: { repeat rewrite assoc.
           do 2 apply cancel_postcomposition.
           etrans.
           2: { apply (functor_comp (rightwhiskering_functor ActV x)). }
           apply pathsinv0, (functor_id_id  _ _ (rightwhiskering_functor ActV x)).
           apply (pr2 (monoidal_associatorisolaw Mon_V _ _ _)).
      }
      rewrite id_left.
      apply idpath.
    - etrans.
      { apply maponpaths.
        apply (functor_comp (leftwhiskering_functor ActV v0)). }
      cbn.
      etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        repeat rewrite assoc'.
        do 2 apply maponpaths.
        apply actegory_actornatleftright.
      }
      etrans.
      { repeat rewrite assoc.
        do 2 apply cancel_postcomposition.
        repeat rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, (functor_comp (rightwhiskering_functor ActV x)).
      }
      cbn.
      etrans.
      { do 2 apply cancel_postcomposition.
        do 2 apply maponpaths.
        rewrite (lifteddistributivity_ldunit δ).
        repeat rewrite assoc'.
        do 3 apply maponpaths.
        etrans.
        { apply pathsinv0, (functor_comp (leftwhiskering_functor Mon_V v0)). }
        apply (functor_id_id _ _ (leftwhiskering_functor Mon_V v0)).
        apply (pr2 (fmonoidal_preservesunitstrongly U)).
      }
      rewrite id_right.
      etrans.
      { do 2 apply cancel_postcomposition.
        etrans.
        { apply maponpaths.
          apply (functor_comp (rightwhiskering_functor ActV x)). }
        cbn.
        rewrite assoc.
        apply cancel_postcomposition.
        apply pathsinv0, actorinv_nat_rightwhisker.
      }
      repeat rewrite assoc'.
      apply maponpaths.
      (* the extra effort for having an abstract strong monoidal functor has now been accomplished *)
      etrans.
      { repeat rewrite assoc'.
        do 2 apply maponpaths.
        apply actegory_triangleidentity. }
      etrans.
      { apply maponpaths.
        apply pathsinv0, (functor_comp (rightwhiskering_functor ActV x)). }
      cbn.
      rewrite assoc'.
      rewrite (pr2 (monoidal_rightunitorisolaw Mon_V v0)).
      rewrite id_right.
      rewrite <- actegory_triangleidentity'.
      rewrite assoc.
      rewrite (pr2 (actegory_actorisolaw Mon_V ActV _ _ _)).
      apply id_left.
  Qed.

  Definition liftedstrength_from_δ: liftedstrength Mon_V Mon_W U ActV ActV FF :=
    lineator_data_from_δ,,lineator_laxlaws_from_δ.

End ActegoryMorphismFromLiftedDistributivity.

End FixAnObject.

Arguments liftedstrength_from_δ _ _ {_} _.
Arguments lifteddistributivity _ : clear implicits.
Arguments lifteddistributivity_data _ : clear implicits.


  Definition unit_lifteddistributivity_data: lifteddistributivity_data I_{Mon_V}.
  Proof.
    intro w.
    exact (ru^{Mon_V}_{F w} · luinv^{Mon_V}_{F w}).
  Defined.

  Lemma unit_lifteddistributivity_nat: lifteddistributivity_nat unit_lifteddistributivity_data.
  Proof.
    intro; intros. unfold unit_lifteddistributivity_data.
    cbn.
    etrans.
    { rewrite assoc.
      apply cancel_postcomposition.
      apply monoidal_rightunitornat. }
    repeat rewrite assoc'.
    apply maponpaths.
    apply pathsinv0, monoidal_leftunitorinvnat.
  Qed.

  Lemma unit_lifteddistributivity_tensor: lifteddistributivity_tensor unit_lifteddistributivity_data.
  Proof.
    intro; intros. unfold lifteddistributivity_tensor_body, unit_lifteddistributivity_data.
    etrans.
    2: { do 2 apply cancel_postcomposition.
         etrans.
         2: { do 2 apply cancel_postcomposition.
              rewrite assoc'.
              do 2 apply maponpaths.
              apply pathsinv0, (functor_comp (leftwhiskering_functor Mon_V _)). }
         apply maponpaths.
         apply pathsinv0, (functor_comp (rightwhiskering_functor Mon_V _)).
    }
    cbn.
    etrans.
    2: { repeat rewrite assoc'.
         apply maponpaths.
         repeat rewrite assoc.
         do 6 apply cancel_postcomposition.
         apply pathsinv0, left_whisker_with_runitor. }
    etrans.
    2: { repeat rewrite assoc.
         do 4 apply cancel_postcomposition.
         repeat rewrite assoc'.
         do 2 apply maponpaths.
         apply pathsinv0, monoidal_triangle_identity_inv. }
    etrans.
    2: { repeat rewrite assoc'.
         do 2 apply maponpaths.
         repeat rewrite assoc.
         do 3 apply cancel_postcomposition.
         etrans.
         2: { apply (functor_comp (rightwhiskering_functor Mon_V _)). }
         apply maponpaths.
         apply pathsinv0, monoidal_rightunitorisolaw.
    }
    rewrite functor_id, id_left.
    etrans.
    2: { do 2 apply maponpaths.
         apply cancel_postcomposition.
         rewrite <- monoidal_triangle_identity'_inv.
         rewrite assoc'.
         apply maponpaths.
         apply pathsinv0, monoidal_associatorisolaw.
    }
    rewrite id_right.
    etrans.
    2: { repeat rewrite assoc'.
         do 2 apply maponpaths.
         apply pathsinv0, monoidal_leftunitorinvnat. }
    do 2 rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    2: { apply cancel_postcomposition.
         apply pathsinv0, monoidal_rightunitornat. }
    etrans.
    2: { rewrite assoc'.
         apply maponpaths.
         apply pathsinv0, fmonoidal_preservestensorstrongly.
    }
    apply pathsinv0, id_right.
  Qed.

  Lemma unit_lifteddistributivity_unit: lifteddistributivity_unit unit_lifteddistributivity_data.
  Proof.
    unfold lifteddistributivity_unit, unit_lifteddistributivity_data.
    etrans.
    2: { do 2 apply cancel_postcomposition.
         rewrite unitors_coincide_on_unit.
         apply pathsinv0, monoidal_rightunitornat. }
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    2: { apply maponpaths.
         rewrite <- unitorsinv_coincide_on_unit.
         apply pathsinv0, monoidal_leftunitorinvnat. }
    rewrite assoc.
    etrans.
    2: {apply cancel_postcomposition.
        apply pathsinv0, (pr22 (fmonoidal_preservesunitstrongly U)). }
    apply pathsinv0, id_left.
  Qed.

  Definition unit_lifteddistributivity: lifteddistributivity I_{Mon_V}.
  Proof.
    use tpair.
    - exact  unit_lifteddistributivity_data.
    - split3.
      + exact unit_lifteddistributivity_nat.
      + exact unit_lifteddistributivity_tensor.
      + exact unit_lifteddistributivity_unit.
  Defined.

Section CompositionOfLiftedDistributivities.

  Context (v1 v2 : V) (δ1 : lifteddistributivity v1) (δ2 : lifteddistributivity v2).

  Definition composedlifteddistributivity_data: lifteddistributivity_data (v1 ⊗_{Mon_V} v2).
  Proof.
    red; intros.
    exact (αinv_{Mon_V} _ _ _ · δ1 w ⊗^{Mon_V}_{r} v2 · α_{Mon_V} _ _ _
             · v1 ⊗^{Mon_V}_{l} δ2 w · αinv_{Mon_V} _ _ _).
  Defined.

  Lemma composedlifteddistributivity_nat: lifteddistributivity_nat composedlifteddistributivity_data.
  Proof.
    do 2 red; intros; unfold composedlifteddistributivity_data; cbn.
    assert (δ1_nat := lifteddistributivity_ldnat δ1).
    assert (δ2_nat := lifteddistributivity_ldnat δ2).
    do 2 red in δ1_nat, δ2_nat; cbn in δ1_nat, δ2_nat.
    etrans.
    { repeat rewrite assoc.
      do 4 apply cancel_postcomposition.
      apply monoidal_associatorinvnatright. }
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    { rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0, (functor_comp (rightwhiskering_functor Mon_V v2)). }
    cbn.
    rewrite δ1_nat.
    etrans.
    { rewrite assoc.
      do 2 apply cancel_postcomposition.
      apply (functor_comp (rightwhiskering_functor Mon_V v2)). }
    cbn.
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    2: { do 2 apply maponpaths.
         apply monoidal_associatorinvnatleft. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    2: { rewrite assoc'.
         apply maponpaths.
         apply (functor_comp (leftwhiskering_functor Mon_V v1)). }
    cbn.
    rewrite <- δ2_nat.
    etrans.
    2: { apply maponpaths.
         apply pathsinv0, (functor_comp (leftwhiskering_functor Mon_V v1)). }
    cbn.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    apply pathsinv0, monoidal_associatornatleftright.
  Qed.

  Lemma composedlifteddistributivity_tensor: lifteddistributivity_tensor composedlifteddistributivity_data.
  Proof.
    do 2 red; intros; unfold composedlifteddistributivity_data; cbn.
    rewrite (lifteddistributivity_ldtensor δ1).
    rewrite (lifteddistributivity_ldtensor δ2).
    etrans.
    { do 3 apply cancel_postcomposition.
      apply maponpaths.
      etrans.
      { apply (functor_comp (rightwhiskering_functor Mon_V v2)). }
      do 5 rewrite functor_comp.
      cbn.
      apply idpath.
    }
    etrans.
    { apply cancel_postcomposition.
      repeat rewrite assoc'.
      do 9 apply maponpaths.
      etrans.
      { apply (functor_comp (leftwhiskering_functor Mon_V v1)). }
      do 5 rewrite functor_comp.
      cbn.
      apply idpath.
    }
    etrans.
    { repeat rewrite assoc.
      do 15 apply cancel_postcomposition.
      apply pathsinv0, monoidal_associatorinvnatright. }
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    { do 14 apply maponpaths.
      apply monoidal_associatorinvnatleft. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    2: { do 3 apply cancel_postcomposition.
         apply maponpaths.
         etrans.
         2: { apply pathsinv0, (functor_comp (leftwhiskering_functor Mon_V (F w))). }
      do 3 rewrite functor_comp.
      cbn.
      apply idpath.
    }
    etrans.
    2: { apply cancel_postcomposition.
         repeat rewrite assoc'.
         do 7 apply maponpaths.
         etrans.
         2: { apply pathsinv0, (functor_comp (rightwhiskering_functor Mon_V (F w'))). }
      do 3 rewrite functor_comp.
      cbn.
      apply idpath.
    }
    etrans.
    { do 6 apply cancel_postcomposition.
      repeat rewrite assoc'.
      do 6 apply maponpaths.
      etrans.
      { apply maponpaths.
        apply monoidal_associatornatleftright. }
      rewrite assoc.
      apply cancel_postcomposition.
      etrans.
      { apply pathsinv0, (functor_comp (rightwhiskering_functor Mon_V v2)). }
      apply maponpaths.
      etrans.
      { apply pathsinv0, (functor_comp (leftwhiskering_functor Mon_V v1)). }
      apply (functor_id_id _ _ (leftwhiskering_functor Mon_V v1)).
      apply (pr2 (fmonoidal_preservestensorstrongly U w w')).
    }
    rewrite functor_id.
    rewrite id_left.
    etrans.
    { repeat rewrite assoc'. apply idpath. }
    apply (z_iso_inv_on_right _ _ _ (z_iso_from_associator_iso Mon_V _ _ _)).
    cbn.
    etrans.
    2: { repeat rewrite assoc.
         do 11 apply cancel_postcomposition.
         etrans.
         2: { apply cancel_postcomposition.
              apply monoidal_pentagonidentity. }
         repeat rewrite assoc'.
         do 2 apply maponpaths.
         etrans.
         2: { apply (functor_comp (leftwhiskering_functor Mon_V (F w))). }
         apply pathsinv0, (functor_id_id _ _ (leftwhiskering_functor Mon_V (F w))).
         apply (pr1 (monoidal_associatorisolaw Mon_V _ _ _)).
    }
    rewrite id_right.
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    2: { repeat rewrite assoc.
         do 10 apply cancel_postcomposition.
         apply pathsinv0, monoidal_associatornatleftright. }
    repeat rewrite assoc'.
    apply maponpaths.
    apply (z_iso_inv_on_right _ _ _ (functor_on_z_iso (rightwhiskering_functor Mon_V v2) (z_iso_from_associator_iso Mon_V _ _ _))).
    cbn.
    etrans.
    2: { repeat rewrite assoc.
         do 9 apply cancel_postcomposition.
         apply pathsinv0, monoidal_pentagonidentity. }
    etrans.
    { repeat rewrite assoc. apply idpath. }
    apply pathsinv0, (z_iso_inv_on_left _ _ _ _ (z_iso_from_associator_iso Mon_V _ _ _)).
    cbn.
    etrans.
    2: { repeat rewrite assoc'.
         do 9 apply maponpaths.
         etrans.
         2: { apply maponpaths.
              apply monoidal_pentagonidentity. }
         repeat rewrite assoc.
         do 2 apply cancel_postcomposition.
         etrans.
         2: { apply (functor_comp (rightwhiskering_functor Mon_V _)). }
         apply pathsinv0, (functor_id_id _ _ (rightwhiskering_functor Mon_V (F w'))).
         apply (pr2 (monoidal_associatorisolaw Mon_V _ _ _)).
    }
    rewrite id_left.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    { do 3 apply cancel_postcomposition.
      repeat rewrite assoc'.
      apply maponpaths.
      rewrite assoc.
      apply monoidal_pentagonidentity. }
    etrans.
    { repeat rewrite assoc.
      do 4 apply cancel_postcomposition.
      apply pathsinv0, monoidal_associatornatright. }
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    { apply maponpaths.
      repeat rewrite assoc.
      do 2 apply cancel_postcomposition.
      apply monoidal_associatornatleft. }
    etrans.
    { repeat rewrite assoc.
      do 3 apply cancel_postcomposition.
      apply (bifunctor_equalwhiskers Mon_V). }
    unfold functoronmorphisms2.
    etrans.
    2: { repeat rewrite assoc.
         do 7 apply cancel_postcomposition.
         apply pathsinv0, monoidal_associatornatleft. }
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    2: { repeat rewrite assoc.
         do 4 apply cancel_postcomposition.
         etrans.
         2: { repeat rewrite assoc'.
              apply maponpaths.
              rewrite assoc.
              apply pathsinv0, monoidal_pentagon_identity_inv. }
         rewrite assoc.
         apply cancel_postcomposition.
         apply pathsinv0, (pr1 (monoidal_associatorisolaw Mon_V _ _ _)).
    }
    rewrite id_left.
    etrans.
    2: { repeat rewrite assoc'.
         do 3 apply maponpaths.
         apply monoidal_associatornatleftright. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    repeat rewrite assoc'.
    apply pathsinv0, (z_iso_inv_on_right _ _ _ (z_iso_from_associator_iso Mon_V _ _ _)).
    cbn.
    etrans.
    2: { repeat rewrite assoc.
         do 2 apply cancel_postcomposition.
         apply pathsinv0, monoidal_associatornatright. }
    repeat rewrite assoc'.
    apply maponpaths.
    rewrite assoc.
    apply (z_iso_inv_on_left _ _ _ _ (functor_on_z_iso (leftwhiskering_functor Mon_V v1) (z_iso_from_associator_iso Mon_V _ _ _))).
    cbn.
    apply pathsinv0, monoidal_pentagonidentity.
  Qed.

  Lemma composedlifteddistributivity_unit: lifteddistributivity_unit composedlifteddistributivity_data.
  Proof.
    red; unfold composedlifteddistributivity_data; cbn.
    rewrite (lifteddistributivity_ldunit δ1).
    rewrite (lifteddistributivity_ldunit δ2).
    etrans.
    { do 3 apply cancel_postcomposition.
      apply maponpaths.
      etrans.
      { apply (functor_comp (rightwhiskering_functor Mon_V v2)). }
      do 2 rewrite functor_comp.
      cbn.
      apply idpath.
    }
    etrans.
    { apply cancel_postcomposition.
      repeat rewrite assoc'.
      do 6 apply maponpaths.
      etrans.
      { apply (functor_comp (leftwhiskering_functor Mon_V v1)). }
      do 2 rewrite functor_comp.
      cbn.
      apply idpath.
    }
    etrans.
    { repeat rewrite assoc.
      do 9 apply cancel_postcomposition.
      apply pathsinv0, monoidal_associatorinvnatright. }
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    { repeat rewrite assoc.
      do 8 apply cancel_postcomposition.
      rewrite <- monoidal_triangleidentity'.
      rewrite assoc.
      apply cancel_postcomposition.
      apply (pr2 (monoidal_associatorisolaw Mon_V _ _ _)).
    }
    rewrite id_left.
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    { do 6 apply maponpaths.
      apply monoidal_associatorinvnatleft. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    { do 4 apply cancel_postcomposition.
      rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, monoidal_associatornatleftright.
    }
    etrans.
    { do 3 apply cancel_postcomposition.
      repeat rewrite assoc'.
      do 2 apply maponpaths.
      etrans.
      { apply pathsinv0, (functor_comp (leftwhiskering_functor Mon_V v1)). }
      apply maponpaths.
      etrans.
      { apply pathsinv0, (functor_comp (rightwhiskering_functor Mon_V v2)). }
      apply (functor_id_id _ _ (rightwhiskering_functor Mon_V v2)).
      apply (pr2 (fmonoidal_preservesunitstrongly U)).
    }
    rewrite functor_id.
    rewrite id_right.
    etrans.
    { repeat rewrite assoc'.
      do 3 apply maponpaths.
      apply monoidal_triangle_identity''_inv. }
    etrans.
    { apply maponpaths.
      rewrite assoc.
      apply cancel_postcomposition.
      apply monoidal_triangleidentity. }
    rewrite assoc.
    etrans.
    { apply cancel_postcomposition.
      etrans.
      { apply pathsinv0, (functor_comp (rightwhiskering_functor Mon_V v2)). }
      apply (functor_id_id _ _ (rightwhiskering_functor Mon_V v2)).
      apply (monoidal_rightunitorisolaw Mon_V).
    }
    apply id_left.
  Qed.

  Definition composedlifteddistributivity: lifteddistributivity (v1 ⊗_{Mon_V} v2).
  Proof.
    exists composedlifteddistributivity_data.
    exact (composedlifteddistributivity_nat,,
           composedlifteddistributivity_tensor,,
           composedlifteddistributivity_unit).
  Defined.

End CompositionOfLiftedDistributivities.

End LiftedDistributivity.

End LiftedLineatorAndLiftedDistributivity.

Arguments lifteddistributivity {_} _ {_} _ {_} _ _.
Arguments lifteddistributivity_data {_} _ {_ _} _.

Section PointwiseOperationsOnLinearFunctors.

  Context {V : category} (Mon_V : monoidal V)
    {C D : category}
    (ActC : actegory Mon_V C) (ActD : actegory Mon_V D).

Section PointwiseBinaryOperationsOnLinearFunctors.

  Context {F1 F2 : functor C D}
    (ll1 : lineator_lax Mon_V ActC ActD F1)
    (ll2 : lineator_lax Mon_V ActC ActD F2).

Section PointwiseBinaryProductOfLinearFunctors.

  Context (BPD : BinProducts D).

  Let FF : functor C D := BinProduct_of_functors _ _ BPD F1 F2.
  Let FF' : functor C D := BinProduct_of_functors_alt BPD F1 F2.

  Definition lax_lineator_binprod_aux: lineator_lax Mon_V ActC ActD FF'.
  Proof.
    use comp_lineator_lax.
    - apply actegory_binprod; assumption.
    - apply actegory_binprod_delta_lineator.
    - use comp_lineator_lax.
      + apply actegory_binprod; assumption.
      + apply actegory_pair_functor_lineator; assumption.
      + apply binprod_functor_lax_lineator.
  Defined.

  Definition lax_lineator_binprod_indirect: lineator_lax Mon_V ActC ActD FF.
  Proof.
    unfold FF.
    rewrite <- BinProduct_of_functors_alt_eq_BinProduct_of_functors.
    apply lax_lineator_binprod_aux.
  Defined.

  Lemma lax_lineator_binprod_indirect_data_ok (v : V) (c : C):
    lax_lineator_binprod_indirect v c =
      binprod_collector_data Mon_V BPD ActD v (F1 c) (F2 c) ·
        BinProductOfArrows _ (BPD _ _) (BPD _ _) (ll1 v c) (ll2 v c).
  Proof.
    unfold lax_lineator_binprod_indirect.
  Abort.
  (* how could one use the equality proof? *)

  (** now an alternative concrete construction *)
  Definition lineator_data_binprod: lineator_data Mon_V ActC ActD FF.
  Proof.
    intros v c.
    exact (binprod_collector_data Mon_V BPD ActD v (F1 c) (F2 c) ·
        BinProductOfArrows _ (BPD _ _) (BPD _ _) (ll1 v c) (ll2 v c)).
  Defined.

  Let cll : lineator_lax Mon_V (actegory_binprod Mon_V ActD ActD) ActD (binproduct_functor BPD)
      := binprod_functor_lax_lineator Mon_V BPD ActD.

  Lemma lineator_laxlaws_binprod: lineator_laxlaws Mon_V ActC ActD FF lineator_data_binprod.
  Proof.
    repeat split; red; intros; unfold lineator_data_binprod.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        apply (lineator_linnatleft _ _ _ _ cll v (_,,_) (_,,_) (_,,_)). }
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply BinProductOfArrows_comp. }
      etrans.
      2: { apply pathsinv0, BinProductOfArrows_comp. }
      apply maponpaths_12; apply lineator_linnatleft.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        apply (lineator_linnatright _ _ _ _ cll v1 v2 (_,,_) f). }
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply BinProductOfArrows_comp. }
      etrans.
      2: { apply pathsinv0, BinProductOfArrows_comp. }
      apply maponpaths_12; apply lineator_linnatright.
    - etrans.
      { rewrite assoc'.
        apply maponpaths.
        etrans.
        { apply BinProductOfArrows_comp. }
        apply maponpaths_12; apply lineator_preservesactor.
      }
      etrans.
      { apply maponpaths.
        repeat rewrite assoc'.
        apply pathsinv0, BinProductOfArrows_comp. }
      etrans.
      { rewrite assoc.
        apply cancel_postcomposition.
        apply (lineator_preservesactor _ _ _ _ cll v w (_,,_)). }
      etrans.
      2: { apply cancel_postcomposition.
           apply maponpaths.
           apply pathsinv0, (functor_comp (leftwhiskering_functor ActD v)). }
      repeat rewrite assoc'.
      do 2 apply maponpaths.
      repeat rewrite assoc.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (lineator_linnatleft _ _ _ _ cll v (_,,_) (_,,_) (_,,_)). }
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: { apply pathsinv0, BinProductOfArrows_comp. }
      apply idpath.
    - etrans.
      2: { apply (lineator_preservesunitor _ _ _ _ cll (_,,_)). }
      rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply BinProductOfArrows_comp. }
      cbn.
      apply maponpaths_12; apply lineator_preservesunitor.
  Qed.

  Definition lax_lineator_binprod: lineator_lax Mon_V ActC ActD FF :=
    lineator_data_binprod,,lineator_laxlaws_binprod.

End PointwiseBinaryProductOfLinearFunctors.

Section PointwiseBinaryCoproductOfLinearFunctors.

  Context (BCD : BinCoproducts D) (δ : actegory_bincoprod_distributor Mon_V BCD ActD).

  Let FF : functor C D := BinCoproduct_of_functors _ _ BCD F1 F2.
  Let FF' : functor C D := BinCoproduct_of_functors_alt2 BCD F1 F2.

  Definition lax_lineator_bincoprod_aux : lineator_lax Mon_V ActC ActD FF'.
  Proof.
    use comp_lineator_lax.
    - apply actegory_binprod; assumption.
    - apply actegory_binprod_delta_lineator.
    - use comp_lineator_lax.
      + apply actegory_binprod; assumption.
      + apply actegory_pair_functor_lineator; assumption.
      + apply (bincoprod_functor_lineator Mon_V BCD ActD δ).
  Defined.

  Definition lax_lineator_bincoprod_indirect : lineator_lax Mon_V ActC ActD FF.
  Proof.
    unfold FF.
    rewrite <- BinCoproduct_of_functors_alt_eq_BinCoproduct_of_functors.
    apply lax_lineator_bincoprod_aux.
  Defined.

  Lemma lax_lineator_bincoprod_data_ok (v : V) (c : C) : lax_lineator_bincoprod_indirect v c =
    δ v (F1 c) (F2 c) · (BinCoproductOfArrows _ (BCD _ _) (BCD _ _) (ll1 v c) (ll2 v c)).
  Proof.
    unfold lax_lineator_bincoprod_indirect.
  Abort.
  (* how could one use the equality proof? *)

  (** now an alternative concrete construction *)
  Definition lineator_data_bincoprod: lineator_data Mon_V ActC ActD FF.
  Proof.
    intros v c.
    exact (δ v (F1 c) (F2 c) · (BinCoproductOfArrows _ (BCD _ _) (BCD _ _) (ll1 v c) (ll2 v c))).
  Defined.

  Let δll : lineator Mon_V (actegory_binprod Mon_V ActD ActD) ActD (bincoproduct_functor BCD)
      := bincoprod_functor_lineator Mon_V BCD ActD δ.

  Lemma lineator_laxlaws_bincoprod
    : lineator_laxlaws Mon_V ActC ActD FF lineator_data_bincoprod.
  Proof.
    repeat split; red; intros; unfold lineator_data_bincoprod.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        apply (lineator_linnatleft _ _ _ _ δll v (_,,_) (_,,_) (_,,_)). }
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply BinCoproductOfArrows_comp. }
      etrans.
      2: { apply pathsinv0, BinCoproductOfArrows_comp. }
      apply maponpaths_12; apply lineator_linnatleft.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        apply (lineator_linnatright _ _ _ _ δll v1 v2 (_,,_) f). }
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply BinCoproductOfArrows_comp. }
      etrans.
      2: { apply pathsinv0, BinCoproductOfArrows_comp. }
      apply maponpaths_12; apply lineator_linnatright.
    - etrans.
      { rewrite assoc'.
        apply maponpaths.
        etrans.
        { apply BinCoproductOfArrows_comp. }
        apply maponpaths_12; apply lineator_preservesactor.
      }
      etrans.
      { apply maponpaths.
        repeat rewrite assoc'.
        apply pathsinv0, BinCoproductOfArrows_comp. }
      etrans.
      { rewrite assoc.
        apply cancel_postcomposition.
        apply (lineator_preservesactor _ _ _ _ δll v w (_,,_)). }
      etrans.
      2: { apply cancel_postcomposition.
           apply maponpaths.
           apply pathsinv0, (functor_comp (leftwhiskering_functor ActD v)). }
      repeat rewrite assoc'.
      do 2 apply maponpaths.
      repeat rewrite assoc.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (lineator_linnatleft _ _ _ _ δll v (_,,_) (_,,_) (_,,_)). }
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: { apply pathsinv0, BinCoproductOfArrows_comp. }
      apply idpath.
    - etrans.
      2: { apply (lineator_preservesunitor _ _ _ _ δll (_,,_)). }
      rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply BinCoproductOfArrows_comp. }
      cbn.
      apply maponpaths_12; apply lineator_preservesunitor.
  Qed.

  Definition lax_lineator_bincoprod: lineator_lax Mon_V ActC ActD FF :=
    lineator_data_bincoprod,,lineator_laxlaws_bincoprod.

End PointwiseBinaryCoproductOfLinearFunctors.

End PointwiseBinaryOperationsOnLinearFunctors.

Section PointwiseCoproductOfLinearFunctors.

  Context {I : UU} {F : I -> functor C D}
    (ll : ∏ (i: I), lineator_lax Mon_V ActC ActD (F i))
    (CD : Coproducts I D) (δ : actegory_coprod_distributor Mon_V CD ActD).

  Let FF : functor C D := coproduct_of_functors _ _ _ CD F.
  Let FF' : functor C D := coproduct_of_functors_alt_old _ CD F.

  Definition lax_lineator_coprod_aux : lineator_lax Mon_V ActC ActD FF'.
  Proof.
    use comp_lineator_lax.
    - apply actegory_power; assumption.
    - apply actegory_prod_delta_lineator.
    - use comp_lineator_lax.
      + apply actegory_power; assumption.
      + apply actegory_family_functor_lineator; assumption.
      + apply (coprod_functor_lineator Mon_V CD ActD δ).
  Defined.

  Definition lax_lineator_coprod_indirect : lineator_lax Mon_V ActC ActD FF.
  Proof.
    unfold FF.
    rewrite <- coproduct_of_functors_alt_old_eq_coproduct_of_functors.
    apply lax_lineator_coprod_aux.
  Defined.

  Lemma lax_lineator_coprod_data_ok (v : V) (c : C) : lax_lineator_coprod_indirect v c =
    δ v (fun i => F i c) · (CoproductOfArrows I _ (CD _) (CD _) (fun i => ll i v c)).
  Proof.
    unfold lax_lineator_coprod_indirect.
  Abort.
  (* how could one use the equality proof? *)

  (** now an alternative concrete construction *)
  Definition lineator_data_coprod: lineator_data Mon_V ActC ActD FF.
  Proof.
    intros v c.
    exact (δ v (fun i => F i c) · (CoproductOfArrows I _ (CD _) (CD _) (fun i => ll i v c))).
  Defined.

  Let δll : lineator Mon_V (actegory_power Mon_V I ActD) ActD (coproduct_functor I CD)
      := coprod_functor_lineator Mon_V CD ActD δ.

  Lemma lineator_laxlaws_coprod
    : lineator_laxlaws Mon_V ActC ActD FF lineator_data_coprod.
  Proof.
    repeat split; red; intros; unfold lineator_data_coprod.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        apply (lineator_linnatleft _ _ _ _ δll v). }
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply CoproductOfArrows_comp. }
      etrans.
      2: { apply pathsinv0, CoproductOfArrows_comp. }
      apply maponpaths, funextsec; intro i; apply lineator_linnatleft.
    - etrans.
      { repeat rewrite assoc.
        apply cancel_postcomposition.
        apply (lineator_linnatright _ _ _ _ δll v1 v2 _ f). }
      repeat rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply CoproductOfArrows_comp. }
      etrans.
      2: { apply pathsinv0, CoproductOfArrows_comp. }
      apply maponpaths, funextsec; intro i; apply lineator_linnatright.
    - etrans.
      { rewrite assoc'.
        apply maponpaths.
        etrans.
        { apply CoproductOfArrows_comp. }
        cbn.
        apply maponpaths, funextsec; intro i; apply lineator_preservesactor.
      }
      etrans.
      { apply maponpaths.
        assert (aux : (fun i => aα^{ ActD }_{ v, w, F i x} · v ⊗^{ ActD}_{l} ll i w x · ll i v (w ⊗_{ ActC} x))
                      = (fun i => aα^{ ActD }_{ v, w, F i x} · (v ⊗^{ ActD}_{l} ll i w x · ll i v (w ⊗_{ ActC} x)))).
        { apply funextsec; intro i; apply assoc'. }
        rewrite aux.
        apply pathsinv0, CoproductOfArrows_comp. }
      etrans.
      { rewrite assoc.
        apply cancel_postcomposition.
        apply (lineator_preservesactor _ _ _ _ δll v w).
      }
      etrans.
      2: { apply cancel_postcomposition.
           apply maponpaths.
           apply pathsinv0, (functor_comp (leftwhiskering_functor ActD v)). }
      repeat rewrite assoc'.
      do 2 apply maponpaths.
      repeat rewrite assoc.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (lineator_linnatleft _ _ _ _ δll v). }
      rewrite assoc'.
      apply maponpaths.
      etrans.
      2: { apply pathsinv0, CoproductOfArrows_comp. }
      apply idpath.
    - etrans.
      2: { apply (lineator_preservesunitor _ _ _ _ δll). }
      rewrite assoc'.
      apply maponpaths.
      etrans.
      { apply CoproductOfArrows_comp. }
      cbn.
      apply maponpaths, funextsec; intro i; apply lineator_preservesunitor.
  Qed.

  Definition lax_lineator_coprod: lineator_lax Mon_V ActC ActD FF :=
    lineator_data_coprod,,lineator_laxlaws_coprod.

End PointwiseCoproductOfLinearFunctors.

End PointwiseOperationsOnLinearFunctors.
