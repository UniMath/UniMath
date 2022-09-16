(**
  Construction of actegories:
  - the monoidal category acting on itself
  - lifting an action from the target of a strong monoidal functor to its source

Reconstructs the results from [UniMath.Bicategories.MonoidalCategories.ConstructionOfActions]
in the whiskered setting.

author: Ralph Matthes 2022
 *)


Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
Import ActegoryNotations.

Section A.

Context {V : category} (Mon_V : monoidal V).

Definition actegory_of_action_on_itself: actegory Mon_V V.
Proof.
  use tpair.
  - use make_actegory_data.
    + exact (monoidal_tensor Mon_V).
    + exact (lu_{Mon_V}).
    + exact (luinv_{Mon_V}).
    + exact (α_{Mon_V}).
    + exact (αinv_{Mon_V}).
  - split; [| split; [| split]].
    + apply monoidal_leftunitorlaw.
    + apply monoidal_associatorlaw.
    + apply monoidal_triangleidentity.
    + apply monoidal_pentagonidentity.
Defined.


Context {C : category} (Act : actegory Mon_V C)
  {W : category} (Mon_W : monoidal W).

Context {F : W ⟶ V} (U : fmonoidal Mon_W Mon_V F).

Definition lifted_action_data: bifunctor_data W C C.
Proof.
  use make_bifunctor_data.
  - intros w x. exact (F w ⊗_{Act} x).
  - intros w x x' f. exact (F w ⊗^{Act}_{l} f).
  - intros x w w' g. exact (#F g ⊗^{Act}_{r} x).
Defined.

Lemma lifted_action_data_is_bifunctor: is_bifunctor lifted_action_data.
Proof.
  repeat split; red; intros; cbn.
  - apply bifunctor_leftid.
  - rewrite functor_id. apply bifunctor_rightid.
  - apply bifunctor_leftcomp.
  - rewrite functor_comp. apply bifunctor_rightcomp.
  - apply bifunctor_equalwhiskers.
Qed.

Definition lifted_action: action(V:=W) C := lifted_action_data,,lifted_action_data_is_bifunctor.

Definition lifted_action_unitor_data : action_unitor_data Mon_W lifted_action.
Proof.
  intro x.
  exact (pr1 (fmonoidal_preservesunitstrongly U) ⊗^{Act}_{r} x · au^{Mon_V,Act}_{x}).
Defined.

Definition lifted_action_unitorinv_data : action_unitorinv_data Mon_W lifted_action.
Proof.
  intro x.
  exact (auinv^{Mon_V,Act}_{x} · fmonoidal_preservesunit U ⊗^{Act}_{r} x).
Defined.

Definition lifted_actor_data : actor_data Mon_W lifted_action.
Proof.
  intros v w x.
  exact (pr1 (fmonoidal_preservestensorstrongly U v w) ⊗^{Act}_{r} x · aα^{Mon_V,Act}_{F v,F w,x}).
Defined.

Definition lifted_actorinv_data : actorinv_data Mon_W lifted_action.
Proof.
  intros v w x.
  exact (aαinv^{Mon_V,Act}_{F v,F w,x} · fmonoidal_preservestensordata U v w ⊗^{Act}_{r} x).
Defined.

Definition lifted_actegory_data: actegory_data Mon_W C.
Proof.
  use make_actegory_data.
  - exact lifted_action.
  - exact lifted_action_unitor_data.
  - exact lifted_action_unitorinv_data.
  - exact lifted_actor_data.
  - exact lifted_actorinv_data.
Defined.

Lemma lifted_actegory_laws: actegory_laws Mon_W lifted_actegory_data.
Proof.
  split; [| split; [| split]]. (* splits into the 4 main goals *)
  - repeat split.
    + intros x y f. cbn. unfold lifted_action_unitor_data.
      admit.
    + cbn. unfold lifted_action_unitor_data.
      unfold lifted_action_unitorinv_data.
      etrans. {
        rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        exact (pr1 (actegory_unitorisolaw Mon_V Act x)).
      }
      rewrite id_left.
      refine (! bifunctor_rightcomp Act _ _ _ _ _ _ @ _).
      etrans. {
        apply maponpaths.
        exact (pr22 (fmonoidal_preservesunitstrongly U)).
      }
      apply (bifunctor_rightid Act).
    + cbn. unfold lifted_action_unitor_data.
      unfold lifted_action_unitorinv_data.
      etrans. {
        rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        refine (! bifunctor_rightcomp Act _ _ _ _ _ _ @ _).
        apply maponpaths.
        exact (pr12 (fmonoidal_preservesunitstrongly U)).
      }
      rewrite bifunctor_rightid.
      rewrite id_left.
      exact (pr2 (actegory_unitorisolaw Mon_V Act x)).
  - repeat split.
    + intros v w z z' h.
      cbn.
      unfold lifted_actor_data.
      admit.
    + admit.
    + admit.
    + cbn.
      unfold lifted_actor_data.
      unfold lifted_actorinv_data.
      etrans. {
        rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        exact (pr1 (actegory_actorisolaw Mon_V Act (F v) (F w) z)).
      }
      rewrite id_left.
      refine (! bifunctor_rightcomp Act _ _ _ _ _ _ @ _).
      etrans. {
        apply maponpaths.
        exact (pr22 (fmonoidal_preservestensorstrongly U v w)).
      }
      apply bifunctor_rightid.
    + cbn.
      unfold lifted_actor_data.
      unfold lifted_actorinv_data.
      etrans. {
        rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        apply maponpaths_2.
        refine (! bifunctor_rightcomp Act _ _ _ _ _ _ @ _).
        apply maponpaths.
        exact (pr12 (fmonoidal_preservestensorstrongly U v w)).
      }
      rewrite bifunctor_rightid.
      rewrite id_left.
      exact (pr2 (actegory_actorisolaw Mon_V Act (F v) (F w) z)).
  - intros v y.
    cbn.
    unfold lifted_actor_data.
    unfold lifted_action_unitor_data.
    rewrite assoc'.
    rewrite bifunctor_leftcomp.
    etrans. {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply (actegory_actornatleftright Mon_V Act).
    }
    rewrite assoc'.
    rewrite (actegory_triangleidentity Mon_V Act (F v) y).
    do 2 rewrite (! bifunctor_rightcomp _ _ _ _ _ _ _).
    apply maponpaths.
    rewrite (! fmonoidal_preservesrightunitality U v).
    etrans. {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc.
      apply maponpaths_2.
      rewrite (! bifunctor_leftcomp _ _ _ _ _ _ _).
      apply maponpaths.
      exact (pr22 (fmonoidal_preservesunitstrongly U)).
    }
    rewrite bifunctor_leftid.
    rewrite id_left.
    rewrite assoc.
    rewrite (pr22 (fmonoidal_preservestensorstrongly U v I_{Mon_W})).
    apply id_left.
  - intros w v v' z.
    cbn.
    unfold lifted_actor_data.

    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      exact (! actegory_actornatright Mon_V Act _ _ _ _ _).
    }

    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc'.
      apply maponpaths.
      exact (actegory_pentagonidentity Mon_V Act (F w) (F v) (F v') z).
    }

    rewrite bifunctor_leftcomp.
    rewrite assoc'.
    etrans. {
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply (actegory_actornatleftright Mon_V Act).
    }

    repeat (rewrite assoc).
    do 2 apply maponpaths_2.
    repeat (rewrite (! bifunctor_rightcomp Act _ _ _ _ _ _)).
    apply maponpaths.
    set (pα := fmonoidal_preservesassociativity U).
    apply (! preserves_associativity_of_inverse_preserves_tensor pα _ _ _ _).

      (* TODO: a lot of work (approx. 200loc) was needed in [UniMath.Bicategories.MonoidalCategories.ConstructionOfActions] *)

Admitted.

Definition lifted_actegory: actegory Mon_W C := lifted_actegory_data,,lifted_actegory_laws.

End A.
