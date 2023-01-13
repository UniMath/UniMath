(** Generalization of pointed distributivity laws to lifted distributivity laws in general monads

author: Ralph Matthes 2022
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.
Require Import UniMath.CategoryTheory.Monoidal.MorphismsOfActegories.
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
Import ActegoryNotations.

Section LiftedDistributivity.

  Context {V : category} (Mon_V : monoidal V)
          {W : category} (Mon_W : monoidal W)
          {F : W ⟶ V} (U : fmonoidal Mon_W Mon_V F)
          (v0 : V).

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
      apply pathsinv0, bifunctor_equalwhiskers.
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
    - admit.
    - admit.
  Admitted.


End ActegoryMorphismFromLiftedDistributivity.

End LiftedDistributivity.
