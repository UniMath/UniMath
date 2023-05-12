Require Import UniMath.Foundations.PartD.
Require Import UniMath.Induction.FunctorAlgebras_legacy.
Require Import UniMath.Induction.PolynomialFunctors.

(** The W-type associated to (A, B) is the initial algebra of the associated
    polynomial functor. See the comment in Induction.M.Core as to why we
    can't use category-theoretic terminology. *)

Section W.
  Context {A : UU} (B : A → UU).
  Local Notation F := (polynomial_functor A B).

  (** The "recursion principle": there exists a morphism into any other
      algebra.

      (The first two rules in Proposition 5.8 in Awodey, Gambino, and Sojakova)
     *)
  Definition is_preinitial (X : algebra_ob F) :=
    ∏ (Y : algebra_ob F), algebra_mor F X Y.

  (** The "homotopy-initiality principle": there is exactly one morphism into
      any other algebra.

      (Definition 5.6 in Awodey, Gambino, and Sojakova)
   *)
  Definition is_initial (X : algebra_ob F) :=
    ∏ (Y : algebra_ob F), iscontr (algebra_mor F X Y).

  Definition isaprop_is_initial (X : algebra_ob F) : isaprop (is_initial X).
  Proof.
    apply impred.
    intro.
    apply isapropiscontr.
  Defined.

  Lemma is_preinitial_to_is_initial (X : algebra_ob F) :
    is_preinitial X -> (∏ Y, isaprop (algebra_mor F X Y)) -> is_initial X.
  Proof.
    exact (λ is_pre is_prop Y, iscontraprop1 (is_prop Y) (is_pre Y)).
  Defined.

  Definition W := ∑ (X : algebra_ob F), is_initial X.
  Definition W_algebra : W → algebra_ob F := pr1.
  Definition W_is_initial : ∏ (w : W), is_initial (pr1 w) := pr2.
  Coercion W_algebra : W >-> algebra_ob.
End W.

Arguments isaprop_is_initial {_ _} _.
Arguments is_preinitial {_ _} _.
Arguments is_initial {_ _} _.
