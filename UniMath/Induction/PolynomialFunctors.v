From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
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
Require Import UniMath.Induction.FunctorAlgebras_legacy.
Require Import UniMath.Induction.FunctorCoalgebras_legacy.
Require Import UniMath.CategoryTheory.categories.Type.Core.

Section PolynomialFunctors.

  Context (A : UU).
  Context (B : A → UU).

  Definition polynomial_functor_obj := fun (X : UU) => ∑ (a : A), B a → X.

  (** The action on arrows is defined by composition in the second projection.
#+begin_src output

**Composition in the second projection defines the behavior of arrows in a polynomial functor.**

The definition of a polynomial functor for two types X and Y, denoted as `polynomial_functor_arr {X Y}`, takes a function `f : X → Y` as input and returns a new type that encodes the composition of `f` with a polynomial evaluation on an object of type Y. The resulting type is defined as follows:

`(pr1 o, (f ∘ pr2 o)%functions)`, where `o` is a polynomial functor object for type X and `(f ∘ pr2 o)%functions` represents the function obtained by composing `f` with the polynomial evaluation on the second projection of `o`.

The `pr1` and `pr2` functions are projections that extract the first and second elements from a tuple, respectively. The `%functions` operator represents a type that encodes functions that map elements in one type to elements in another type. In this case, it is used to specify the type of the output of `(f ∘ pr2 o)%functions`.

In summary, this definition states that when given a polynomial functor object for type X and a function `f : X → Y`, we can define a new type that encodes the composition of `f` with a polynomial evaluation on an object of type Y by composing `f` with the polynomial evaluation on the second projection of the input object and applying the `%functions` operator to specify the output type.
#+end_src

   *)
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
    make_functor polynomial_functor_data polynomial_functor_is_functor.

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
