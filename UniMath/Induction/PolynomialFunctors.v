(** ** Polynomial functors

    Using the formalism of a polynomial functor, one can build any functor
    combining constant types, +, and ×, where the variable X is to the right
    of the arrow →.

    W-types are (up to isomorphism) initial algebras of polynomial functors,
    whereas M-types are final coalgebras.

    (Definition 2 in Ahrens, Capriotti, and Spadotti)

    Author: Langston Barrett (@siddharthist)
*)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.Type.Core.

Section PolynomialFunctors.

  Context (A : UU).
  Context (B : A → UU).

  Definition polynomial_functor_obj := fun (X : UU) => ∑ (a : A), B a → X.

  (** The action on arrows is defined by composition in the second projection. *)
  Definition polynomial_functor_arr {X Y : UU} (f : X → Y) :
    (polynomial_functor_obj X) → (polynomial_functor_obj Y) :=
    fun o => (pr1 o,, (f ∘ pr2 o)%functions).

  (** Polynomial functors aren't functors in the usual sense, since UU is an
      (∞,1)-category. However, they are functors in the sense of UniMath's
      definition. *)
  Definition polynomial_functor_data : functor_data type_precat type_precat :=
    functor_data_constr _ _
                        (polynomial_functor_obj : type_precat → type_precat)
                        (@polynomial_functor_arr).

  Lemma polynomial_functor_is_functor : is_functor polynomial_functor_data.
  Proof.
    split.
    - intro.
      reflexivity.
    - intros ? ? ? ? ?.
      reflexivity.
  Defined.

  Definition polynomial_functor : functor type_precat type_precat :=
    mk_functor polynomial_functor_data polynomial_functor_is_functor.

  (** An algebra with an uncurried structure map *)
  Definition polynomial_alg_uncurried : UU :=
    ∑ (X : ob type_precat), ∏ (a : A), (B a → X) → X.

  (** The uncurried and curried versions are equivalent *)
  Lemma polynomial_alg_uncurried_equiv :
    polynomial_alg_uncurried ≃ (algebra_ob polynomial_functor).
  Proof.
    apply (weq_iso (λ p, (pr1 p,, uncurry (pr2 p)))
                   (λ p, (pr1 p,, curry (pr2 p))));
      try reflexivity.
  Defined.

End PolynomialFunctors.
