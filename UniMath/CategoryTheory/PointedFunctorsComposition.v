
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

Variable C : precategory.
Variable hs : has_homsets C.

Definition ptd_composite (Z Z' : ptd_obj C) : precategory_Ptd C hs.
Proof.
  exists (functor_composite Z Z').
  apply (horcomp (ptd_pt _ Z) (ptd_pt _ Z')).
Defined.

Definition ptd_compose (Z Z' : ptd_obj C) : precategory_Ptd C hs.
Proof.
  exists (functor_compose hs hs (pr1 Z:[C, C, hs]) (pr1 Z':[C, C, hs])).
  apply (# (functorial_composition hs hs) (((ptd_pt _ Z: [C, C, hs]⟦functor_identity C,pr1 Z⟧) ,,
                                            (ptd_pt _ Z': [C, C, hs]⟦functor_identity C,pr1 Z'⟧))
  : precategory_binproduct [C, C, hs] [C, C, hs] ⟦(functor_identity C,,functor_identity C),(pr1 Z,,pr1 Z')⟧)).
Defined.

Lemma ptd_composite_compose (Z Z' : ptd_obj C): ptd_composite Z Z' = ptd_compose Z Z'.
Proof.
  use total2_paths_f.
  - apply idpath.
  - cbn.
    rewrite (@horcomp_post_pre _ _ (C,,hs)).
    apply (nat_trans_eq hs).
    intro c. apply idpath.
Qed.

End def_ptd.
