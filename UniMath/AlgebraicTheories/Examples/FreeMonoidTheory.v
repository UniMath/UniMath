(**************************************************************************************************

  The Free Monoid Theory

  One can construct an algebraic theory T by taking T(n) to be the free monoid on n generators. Then
  the type of algebras for this algebraic theory is equivalent to the type of monoids.

  Contents
  1. The definition of the algebraic theory [free_monoid_theory]
  2. The functor from monoids to algebras [monoid_to_algebra]
  3. Constructing a monoid from an algebra [free_monoid_theory_algebra_to_monoid]
  4. The equivalence of categories between algebras and monoids [monoid_algebra_equivalence]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Export UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Require Import UniMath.Algebra.IteratedBinaryOperations.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Categories.Monoid.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.Algebras.
Require Import UniMath.AlgebraicTheories.AlgebraCategoryCore.
Require Import UniMath.AlgebraicTheories.AlgebraCategory.
Require Import UniMath.AlgebraicTheories.AlgebraMorphisms.
Require Import UniMath.AlgebraicTheories.Examples.FreeObjectTheory.

Local Open Scope algebraic_theories.
Local Open Scope vec_scope.
Local Open Scope cat.

(** * 1. The definition of the algebraic theory *)

Definition free_monoid_theory
  : algebraic_theory
  := free_object_theory monoid_free_forgetful_adjunction.

(** * 2. The functor from monoids to algebras *)

Definition monoid_to_algebra
  : monoid_category ⟶ algebra_cat free_monoid_theory
  := free_object_algebra_functor monoid_free_forgetful_adjunction.

(** * 3. Constructing a monoid from an algebra *)

Definition op_el
  : free_monoid_theory 2
  := op
    (free_monoid_unit (X := stnset _) (make_stn 2 0 (idpath _)))
    (free_monoid_unit (X := stnset _) (make_stn 2 1 (idpath _))).

Definition unit_el
  : free_monoid_theory 0
  := unel _.

Definition free_monoid_theory_algebra_to_setwithbinop
  (A : algebra free_monoid_theory)
  : setwithbinop.
Proof.
  use make_setwithbinop.
  - exact A.
  - intros a b.
    exact (action op_el (weqvecfun _ [(a ; b)])).
Defined.

Local Lemma move_action_through_weqvecfun
  {A : algebra free_monoid_theory}
  {n : nat}
  {f g : free_monoid_theory n}
  (h : stn n → A)
  : weqvecfun _ [( action f h ; action g h )] = λ i, action (weqvecfun _  [(f ; g)] i) h.
Proof.
  now apply (invmaponpathsweq (invweq (weqvecfun _))).
Qed.

Lemma free_monoid_theory_algebra_to_setwithbinop_op_is_assoc
  (A : algebra free_monoid_theory)
  : isassoc (op (X := free_monoid_theory_algebra_to_setwithbinop A)).
Proof.
  intros a b c.
  pose (f := weqvecfun _ [(a ; b ; c)]).
  pose (Hf := λ i Hi, !(var_action _ (make_stn 3 i Hi) f)).
  cbn -[weqvecfun action].
  rewrite (Hf 0 (idpath true) : a = _),
    (Hf 1 (idpath true) : b = _),
    (Hf 2 (idpath true) : c = _).
  now do 4 rewrite (move_action_through_weqvecfun f), <- subst_action.
Qed.

Definition free_monoid_theory_algebra_to_unit (A : algebra free_monoid_theory)
  : A
  := action unit_el (weqvecfun _ [()]).

Lemma free_monoid_theory_algebra_to_isunit (A : algebra free_monoid_theory)
  : isunit
    (op (X := free_monoid_theory_algebra_to_setwithbinop A))
    (free_monoid_theory_algebra_to_unit A).
Proof.
  split;
    intro x;
    cbn -[weqvecfun action];
    now rewrite <- (var_action _ (make_stn 1 0 (idpath _)) (λ _, x)),
      <- (lift_constant_action 1 _ (λ _, x) : _ = free_monoid_theory_algebra_to_unit A),
      (move_action_through_weqvecfun (λ _, x)),
      <- subst_action.
Qed.

Definition free_monoid_theory_algebra_to_setwithbinop_op_is_unital
  (A : algebra free_monoid_theory)
  : isunital (op (X := free_monoid_theory_algebra_to_setwithbinop A))
  := _ ,, free_monoid_theory_algebra_to_isunit A.

Definition free_monoid_theory_algebra_to_setwithbinop_op_is_monoidop
  (A : algebra free_monoid_theory)
  : ismonoidop (op (X := free_monoid_theory_algebra_to_setwithbinop A))
  := free_monoid_theory_algebra_to_setwithbinop_op_is_assoc A ,,
    free_monoid_theory_algebra_to_setwithbinop_op_is_unital A.

Definition free_monoid_theory_algebra_to_monoid (A : algebra free_monoid_theory)
  : monoid
  := free_monoid_theory_algebra_to_setwithbinop A ,,
    free_monoid_theory_algebra_to_setwithbinop_op_is_monoidop A.

(** * 4. The equivalence *)

Definition fully_faithful_monoid_to_algebra
  : fully_faithful monoid_to_algebra.
Proof.
  intros M M'.
  use isweq_iso.
  - refine (λ (f : algebra_morphism _ _), _).
    exists f.
    abstract (
      use make_ismonoidfun;
      [ exact (λ m m', mor_action f op_el (weqvecfun _ [(m ; m')]))
      | exact (mor_action f unit_el (weqvecfun _ [()])) ]
    ).
  - abstract (
      intro f;
      apply subtypePath;
      [ intro;
        apply isapropdirprod;
        repeat (apply impred_isaprop; intro);
        apply setproperty
      | apply idpath ]
    ).
  - abstract (
      intro f;
      now apply algebra_morphism_eq
    ).
Defined.

Lemma mor_action_ax_identity
  (A : algebra free_monoid_theory)
  (n : nat)
  (f : free_monoid_theory n)
  (a : stn n → (monoid_to_algebra (free_monoid_theory_algebra_to_monoid A) : algebra _))
  : mor_action_ax (identity _) (idfun A)
    (@action free_monoid_theory
      (monoid_to_algebra (free_monoid_theory_algebra_to_monoid A) : algebra _))
    (@action free_monoid_theory A) n f a.
Proof.
  pose (A' := monoid_to_algebra (free_monoid_theory_algebra_to_monoid A) : algebra _).
  apply (list_ind (λ x, action (A := A') x a = action (A := A) x a)).
  - exact (!(lift_constant_action (A := A) _ (unel _) a)).
  - intros i xs Haction.
    refine (subst_action A' op_el (weqvecfun _ [(free_monoid_unit i ; xs)]) a @ !_).
    refine (subst_action A op_el (weqvecfun _ [(free_monoid_unit i ; xs)]) a @ !_).
    now rewrite <- (move_action_through_weqvecfun (A := A) a),
      <- Haction,
      (var_action A _ _ :
        action (free_monoid_unit i : free_monoid_theory n) _ = _).
Qed.

Definition monoid_algebra_equivalence
  : adj_equivalence_of_cats monoid_to_algebra.
Proof.
  apply rad_equivalence_of_cats.
  - apply monoid_category_is_univalent.
  - apply fully_faithful_monoid_to_algebra.
  - intro A.
    apply hinhpr.
    exists (free_monoid_theory_algebra_to_monoid A).
    use make_algebra_z_iso.
    + apply identity_z_iso.
    + apply mor_action_ax_identity.
Defined.
