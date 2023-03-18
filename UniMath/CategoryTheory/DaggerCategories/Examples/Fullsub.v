(* A full sub-category of a dagger category is again a dagger category. *)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.

Local Open Scope cat.

Section Fullsub.

  Context {C : category} (dag : dagger C) (P : ob C -> hProp).

  Let CP := full_sub_category C P.

  Definition full_sub_dagger_structure : dagger_structure CP
    := λ x y f, dag _ _ (pr1 f) ,, tt.

  Lemma full_sub_dagger_laws : dagger_laws full_sub_dagger_structure.
  Proof.
    repeat split ; (intro ; intros ; use subtypePath ; [intro ; apply isapropunit | ]).
    - apply dagger_to_law_id.
    - apply dagger_to_law_comp.
    - apply dagger_to_law_idemp.
  Qed.

  Definition full_sub_dagger : dagger CP
    := _ ,, full_sub_dagger_laws.

  Lemma inclusion_is_dagger_functor
    : is_dagger_functor full_sub_dagger dag
                        (sub_precategory_inclusion C (full_sub_precategory P)).
  Proof.
    intro ; intros ; apply idpath.
  Qed.

End Fullsub.
