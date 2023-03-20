Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.

Definition finite_set_skeleton_precat : precategory.
Proof.
  use make_precategory.
  - use make_precategory_data.
    + use make_precategory_ob_mor.
      * exact nat.
      * intros m n.
        exact ((stn m) → (stn n)).
    + intros ?.
      exact (λ i, i).
    + intros ? ? ?.
      exact (λ f g, g ∘ f).
  - repeat split.
Defined.

Definition finite_set_skeleton_category : category.
Proof.
  use make_category.
  - exact finite_set_skeleton_precat.
  - intros ? ?.
    simpl.
    apply funspace_isaset.
    apply isasetstn.
Defined.