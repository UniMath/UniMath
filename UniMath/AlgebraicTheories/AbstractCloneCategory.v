Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.AlgebraicTheories.AlgebraicBase.
Require Import UniMath.AlgebraicTheories.AbstractClone.
Require Import UniMath.AlgebraicTheories.AbstractCloneMorphism.

Definition id_morphism_data (C : abstract_clone_data) : abstract_clone_morphism_data C C := λ _ x, x.

Lemma id_is_morphism (C : abstract_clone_data) : is_abstract_clone_morphism (id_morphism_data C).
Proof.
  use make_is_abstract_clone_morphism.
  - unfold id_morphism_data.
    repeat intro.
    apply maponpaths, funextfun.
    intro.
    apply idpath.
  - repeat intro.
    apply idpath.
Qed.

Definition comp_morphism_data {C C' C''} (f : abstract_clone_morphism_data C C') (g : abstract_clone_morphism_data C' C'') : abstract_clone_morphism_data C C'' := (λ n, (g n ∘ f n)).

Lemma comp_is_morphism {C C' C''} (f : abstract_clone_morphism C C') (g : abstract_clone_morphism C' C'') : is_abstract_clone_morphism (comp_morphism_data f g).
Proof.
  use make_is_abstract_clone_morphism.
  - unfold comp_morphism_data.
    repeat intro.
    simpl.
    rewrite (pr12 f), (pr12 g).
    apply maponpaths, funextfun.
    intro.
    apply idpath.
  - repeat intro.
    unfold comp_morphism_data.
    simpl.
    rewrite (pr22 f), (pr22 g).
    apply idpath.
Qed.

Definition abstract_clone_precategory_data : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact abstract_clone.
    + exact abstract_clone_morphism.
  - simpl.
    exact (λ C, make_abstract_clone_morphism (id_morphism_data C) (id_is_morphism C)).
  - simpl.
    intros C C' C'' f g.
    use (make_abstract_clone_morphism (comp_morphism_data f g) (comp_is_morphism f g)).
Defined.

Lemma abstract_clone_is_precategory : is_precategory abstract_clone_precategory_data.
Proof.
  use make_is_precategory;
    intros;
    apply abstract_clone_morphism_eq;
    intros;
    apply idpath.
Defined.

Definition abstract_clone_precategory : precategory := make_precategory abstract_clone_precategory_data abstract_clone_is_precategory.

Lemma abstract_clone_is_category : has_homsets abstract_clone_precategory.
Proof.
  unfold has_homsets.
  simpl.
  intros.
  apply isaset_total2.
  - apply impred_isaset.
    intro.
    apply funspace_isaset.
    simpl.
    apply (b t).
  - intros.
    exact (isasetaprop (isaprop_is_abstract_clone_morphism _)).
Qed.

Definition abstract_clone_category : category := make_category abstract_clone_precategory abstract_clone_is_category.
