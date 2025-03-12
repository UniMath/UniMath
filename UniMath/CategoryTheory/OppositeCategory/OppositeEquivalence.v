(**************************************************************************************************

  The Opposite Adjoint Equivalence

  An adjoint equivalence F between categories C and D gives an adjoint equivalence between D^opp and
  C^opp, which just repackages the data of F.

  Contents
  1. The opposite equivalence [adj_equivalence_of_cats_opposite] [adj_equiv_opposite]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.OppositeCategory.OppositeAdjunction.

Local Open Scope cat.

(* 1. The opposite equivalence *)

Section OppositeEquivalence.

  Context {C D : category}.

  Definition forms_equivalence_opposite
    {F : C ⟶ D}
    {G : D ⟶ C}
    {H1 : are_adjoints F G}
    (H2 : forms_equivalence H1)
    : forms_equivalence (are_adjoints_opposite H1).
  Proof.
    use make_forms_equivalence.
    - intro a.
      apply opp_is_z_isomorphism.
      exact (pr2 H2 a).
    - intro a.
      apply opp_is_z_isomorphism.
      apply (pr1 H2 a).
  Defined.

  Definition adj_equivalence_of_cats_opposite
    {F : C ⟶ D}
    (H : adj_equivalence_of_cats F)
    : adj_equivalence_of_cats (functor_op (right_functor H))
    := (functor_op F ,, _) ,,
      forms_equivalence_opposite (pr2 H).

  Definition adj_equiv_opposite
    (F : adj_equiv C D)
    : adj_equiv (D^opp) (C^opp)
    := _ ,, adj_equivalence_of_cats_opposite F.

End OppositeEquivalence.
