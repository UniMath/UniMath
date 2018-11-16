(** * Quotobjects *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnderCategories.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.Subcategory.Core.

Require Import UniMath.CategoryTheory.limits.pushouts.


(** * Definition of quotient objects *)
Section def_quotobjects.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition Quotobjectscategory (c : C) : UU :=
    Undercategory (subprecategory_of_epis C hs)
                     (has_homsets_subprecategory_of_epis C hs)
                     (subprecategory_of_epis_ob C hs c).

  (** Construction of a quotient object from an epi *)
  Definition Quotobjectscategory_ob {c c' : C} (h : C⟦c, c'⟧) (isE : isEpi h) :
    Quotobjectscategory c := tpair _ (subprecategory_of_epis_ob C hs c') (tpair _ h isE).

  Hypothesis hpo : @Pushouts C.

  (** Given any quotient object Q of c and a morphism h : c -> c', by taking then pushout of Q by h
      we obtain a quotient object of c'. *)
  Definition PushoutQuotobject {c : C} (Q : Quotobjectscategory c) {c' : C} (h : C⟦c, c'⟧) :
    Quotobjectscategory c'.
  Proof.
    set (po := hpo _ _ _ h (pr1 (pr2 Q))).
    use Quotobjectscategory_ob.
    - exact po.
    - exact (limits.pushouts.PushoutIn1 po).
    - use EpiPushoutisEpi'.
  Defined.

End def_quotobjects.
