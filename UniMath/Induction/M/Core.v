(** ** M-types

    The M-type associated to (A, B) is the final coalgebra of the associated
    polynomial functor.

    We can't use (1) the definition of [Terminal], because we can't use (2)
    that (co)algebras and their morphisms form a precategory, because this is
    only true when the base category has homsets, which [UU] doesn't.
    Therefore, we must redefine what it means to be a final coalgebra here
    without categorical language.

    (Definition 4 in Ahrens, Capriotti, and Spadotti)
    (IsFinal in HoTT/M-types)

    Author: Langston Barrett (@siddharthist)
  *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.Induction.PolynomialFunctors.

Section M.
  Context {A : UU} (B : A → UU).
  Local Notation F := (polynomial_functor A B). (* can be coerced to a function *)

  Definition is_prefinal (X : coalgebra F) :=
    ∏ (Y : coalgebra F), coalgebra_homo F Y X.

  Definition is_final (X : coalgebra F) :=
    ∏ (Y : coalgebra F), iscontr (coalgebra_homo F Y X).

  (** prop-IsFinal in HoTT/M-types *)
  Definition isaprop_is_final (X : coalgebra F) : isaprop (is_final X).
  Proof.
    apply impred.
    intro.
    apply isapropiscontr.
  Defined.

  Lemma is_prefinal_to_is_final (X : coalgebra F) :
    is_prefinal X -> (∏ Y, isaprop (coalgebra_homo F Y X)) -> is_final X.
  Proof.
    exact (λ is_pre is_prop Y, iscontraprop1 (is_prop Y) (is_pre Y)).
  Defined.

  Definition M := ∑ (X : coalgebra F), is_final X.
  Definition M_coalgebra : M → coalgebra F := pr1.
  Definition M_is_final : ∏ (m : M), is_final (pr1 m) := pr2.
  Coercion M_coalgebra : M >-> coalgebra.
End M.

Arguments isaprop_is_final {_ _} _.
Arguments is_prefinal {_ _} _.
Arguments is_final {_ _} _.
