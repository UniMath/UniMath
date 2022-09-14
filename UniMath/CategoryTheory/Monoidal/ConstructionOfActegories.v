(**
  Construction of actegories:
  - the monoidal category acting on itself
  - lifting an action from the target of a strong monoidal functor to its source

Reconstructs the results from [UniMath.Bicategories.MonoidalCategories.ConstructionOfActions]
in the whiskered setting.

author: Ralph Matthes 2022
 *)


Require Import UniMath.MoreFoundations.Notations.

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
    + exact (lu^{Mon_V}).
    + exact (luinv^{Mon_V}).
    + exact (α^{Mon_V}).
    + exact (αinv^{Mon_V}).
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

      (* TODO: a lot of work (approx. 200loc) was needed in [UniMath.Bicategories.MonoidalCategories.ConstructionOfActions] *)

Admitted.

Definition lifted_actegory: actegory Mon_W C := lifted_actegory_data,,lifted_actegory_laws.

End A.
