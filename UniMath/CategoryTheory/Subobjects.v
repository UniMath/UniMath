(** * Subobjects *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.sub_precategories.

Require Import UniMath.CategoryTheory.limits.pullbacks.


(** * Definition of subobjects *)
Section def_subobjects.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition SubobjectsPrecategory (c : C) : UU :=
    slice_precat (subprecategory_of_monics C hs)
                 (subprecategory_of_monics_ob C hs c)
                 (has_homsets_subprecategory_of_monics C hs).

  (** Construction of a subobject from a monic *)
  Definition SubobjectsPrecategory_ob {c c' : C} (h : C⟦c', c⟧) (isM : isMonic h) :
    SubobjectsPrecategory c := tpair _ (subprecategory_of_monics_ob C hs c') (tpair _ h isM).

  Hypothesis hpb : @Pullbacks C.

  (** Given any subobject S of c and a morphism h : c' -> c, by taking then pullback of S by h we
      obtain a subobject of c'. *)
  Definition PullbackSubobject {c : C} (S : SubobjectsPrecategory c) {c' : C} (h : C⟦c', c⟧) :
    SubobjectsPrecategory c'.
  Proof.
    set (pb := hpb _ _ _ h (pr1 (pr2 S))).
    use SubobjectsPrecategory_ob.
    - exact pb.
    - exact (limits.pullbacks.PullbackPr1 pb).
    - use MonicPullbackisMonic'.
  Defined.

End def_subobjects.
