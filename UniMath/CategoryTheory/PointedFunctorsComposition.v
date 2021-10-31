
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-  Definition of composition of pointed functors


************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Section def_ptd.

Variable C : category.

Definition ptd_composite (Z Z' : ptd_obj C) : category_Ptd C.
Proof.
  exists (functor_composite Z Z').
  apply (horcomp (ptd_pt _ Z) (ptd_pt _ Z')).
Defined.

Definition ptd_compose (Z Z' : ptd_obj C) : category_Ptd C.
Proof.
  exists (functor_compose _ _ _ (pr1 Z:[C, C]) (pr1 Z':[C, C])).
  apply (# (functorial_composition _ _ _) (((ptd_pt _ Z: [C, C]⟦functor_identity C,pr1 Z⟧) ,,
                                            (ptd_pt _ Z': [C, C]⟦functor_identity C,pr1 Z'⟧))
  : category_binproduct [C, C] [C, C] ⟦(functor_identity C,,functor_identity C),(pr1 Z,,pr1 Z')⟧)).
Defined.

Lemma ptd_composite_compose (Z Z' : ptd_obj C): ptd_composite Z Z' = ptd_compose Z Z'.
Proof.
  use total2_paths_f.
  - apply idpath.
  - cbn.
    rewrite (@horcomp_post_pre _ _ C).
    apply (nat_trans_eq (homset_property C)).
    intro c. apply idpath.
Qed.

End def_ptd.
