Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractCloneMorphisms.

Lemma id_is_morphism (C : abstract_clone_data) : is_abstract_clone_morphism (λ n (x : C n), x).
Proof.
  use make_is_abstract_clone_morphism.
  - repeat intro.
    apply maponpaths, funextfun.
    intro.
    apply idpath.
  - repeat intro.
    apply idpath.
Qed.

Definition id_morphism
  (C : abstract_clone_data)
  : abstract_clone_morphism C C
  := make_abstract_clone_morphism _ (id_is_morphism C).

Lemma comp_is_morphism
  {C C' C''}
  (f : abstract_clone_morphism C C')
  (g : abstract_clone_morphism C' C'')
  : is_abstract_clone_morphism (λ n, (g n ∘ f n)).
Proof.
  use make_is_abstract_clone_morphism.
  - repeat intro.
    simpl.
    rewrite (pr12 f), (pr12 g).
    apply maponpaths, funextfun.
    intro.
    apply idpath.
  - repeat intro.
    simpl.
    rewrite (pr22 f), (pr22 g).
    apply idpath.
Qed.

Definition comp_morphism
  {C C' C''}
  (f : abstract_clone_morphism C C')
  (g : abstract_clone_morphism C' C'')
  : abstract_clone_morphism C C''
  := make_abstract_clone_morphism _ (comp_is_morphism f g).

Definition abstract_clone_precategory_data : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact abstract_clone.
    + exact abstract_clone_morphism.
  - simpl.
    exact id_morphism.
  - simpl.
    intros ? ? ?.
    exact comp_morphism.
Defined.

Lemma abstract_clone_is_precategory : is_precategory abstract_clone_precategory_data.
Proof.
  use make_is_precategory;
    intros;
    apply abstract_clone_morphism_eq;
    intros;
    apply idpath.
Defined.

Definition abstract_clone_precategory
  : precategory
  := make_precategory abstract_clone_precategory_data abstract_clone_is_precategory.

Lemma abstract_clone_is_category : has_homsets abstract_clone_precategory.
Proof.
  unfold has_homsets.
  simpl.
  intros C C'.
  apply isaset_total2.
  - apply impred_isaset.
    intro n.
    apply funspace_isaset.
    simpl.
    apply (C' n).
  - intros.
    exact (isasetaprop (isaprop_is_abstract_clone_morphism _)).
Qed.

Definition abstract_clone_category
  : category
  := make_category abstract_clone_precategory abstract_clone_is_category.
