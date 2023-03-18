Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryEquality.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.


Local Open Scope cat.

Definition daggercatiso (C D : dagger_category)
  : UU
  := ∑ i : catiso C D,
      is_dagger_functor C D i.

Definition daggercatiso_is_path_cat
           (C D : dagger_category)
  : C = D ≃ daggercatiso C D.
Proof.
  refine (_ ∘ total2_paths_equiv _ _ _)%weq.
  apply (weqbandf (catiso_is_path_cat (pr1 C) (pr1 D))).
  induction C as [C dagC].
  induction D as [D dagD].

  intro p.
  use weqimplimpl.
  - intro q.
    simpl in p ; induction p.
    cbn in q ; induction q.
    intros x y f ; apply idpath.
  - intro q.
    simpl in p ; induction p.
    simpl in q.
    apply dagger_equality.
    apply funextsec ; intro x.
    apply funextsec ; intro y.
    apply funextsec ; intro f.
    exact (q x y f).
  - apply isaset_dagger.
  - apply isaprop_is_dagger_functor.
Defined.
