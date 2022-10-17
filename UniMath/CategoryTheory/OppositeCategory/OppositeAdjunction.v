Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.OppositeCategory.Core.

Section OppositeAdjunction.

  Context {C D : category} {F : functor C D} {G : functor D C}
          (a : are_adjoints F G).

  Local Definition a_adjunction : adjunction C D := make_adjunction _ (pr2 a).

  Definition adjunction_data_opposite : adjunction_data (opp_cat D) (opp_cat C).
  Proof.
    refine (functor_op G ,, functor_op F ,, _ ,, _).
    - exists (λ d, counit_from_are_adjoints a d).
      exact (λ d1 d2 f, ! pr2 (counit_from_are_adjoints a) d2 d1 f).
    - exists (λ d, unit_from_are_adjoints a d).
      exact (λ d1 d2 f, ! pr2 (unit_from_are_adjoints a) d2 d1 f).
  Defined.

  Definition form_adjunction'_opposite : form_adjunction' adjunction_data_opposite.
  Proof.
    exists (λ d, triangle_2_statement_from_adjunction a_adjunction d).
    exact (λ c, triangle_1_statement_from_adjunction a_adjunction c).
  Qed.

  Definition adjunction_opposite : adjunction (opp_cat D) (opp_cat C).
  Proof.
    exists adjunction_data_opposite.
    exact form_adjunction'_opposite.
  Defined.

  Definition are_adjoints_opposite : are_adjoints (functor_op G) (functor_op F)
    := are_adjoints_from_adjunction adjunction_opposite.

End OppositeAdjunction.

Lemma is_right_adjoint_opposite {C D : category} (F : functor C D)
  : is_left_adjoint F -> is_right_adjoint (functor_op F).
Proof.
  intro ila.
  set (adj := make_adjunction _ (pr22 ila)).
  exists (functor_op (pr121 adj)).
  exact (are_adjoints_opposite adj).
Defined.

Lemma is_right_adjoint_opposite' {C D : category} (F : functor C D)
  : is_left_adjoint (functor_op F) -> is_right_adjoint F.
Proof.
  intro ila.
  apply (is_right_adjoint_opposite (functor_op F) ila).
Defined.
