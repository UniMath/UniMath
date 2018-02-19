(** ** Natural numbers

    The natural numbers are a motivating example of W-types, and one of the only
    W-types readily available in UniMath. We show that they are an initial
    algebra for a polynomial functor, and satisfy a few other properties.

    Author: Langston Barrett (@siddharthist)
 *)
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.Ktheory.Utilities.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.W.Core.
Require Import UniMath.Induction.W.Fibered.

Local Notation ℕ := nat.

(** The signature for the nat functor is (bool, [false ↦ empty; true ↦ unit])
    since the naturals have two constructors: one for zero and one for successor.
 *)
Definition nat_functor : functor type_precat type_precat :=
  polynomial_functor bool (bool_rect (λ _, UU) empty unit).

(** The functor deals with functions from ∅ and unit; these lemmas will come in
    handy in several proofs. *)
Lemma eqfromempty {X : UU} (f : empty -> X) : f = fromempty.
Proof. apply proofirrelevance, isapropifcontr, iscontrfunfromempty. Defined.

Lemma eta_unit {X : UU} (f : unit -> X) : f = λ _, f tt.
Proof. apply funextfun; intros ?; induction _; reflexivity. Defined.

(** The intuition is that an algebra X for this functor is given by a constant
    x : X and a function X → X. The following equivalence verifies this. *)
Definition nat_functor_equiv :
  ∏ {X : UU}, (X × (X → X)) ≃ (nat_functor X -> X).
Proof.
  intro X.
  use weq_iso.
  * intros dprodpair.
    intros pairfun.
    induction pairfun as [b bfun]; induction b.
    - exact (pr1 dprodpair).
    - exact (pr2 dprodpair (bfun tt)).
  * intro pairfun.
    exact (dirprodpair (pairfun (true,, fromempty))
                       (λ x, pairfun (false,, λ _, x))).
  * reflexivity.
  * intro Y.
    apply funextsec; intro y; induction y as [b bfun].
    induction b; cbn in *; apply (maponpaths Y).
    - (** There is a unique function out of the empty type *)
      apply subtypeEquality'; try reflexivity.
      apply isapropifcontr, iscontrfunfromempty.
    - apply maponpaths.
      apply funextfun; intro t; induction t; reflexivity.
Defined.

(** Using our equivalence, we can consisely define the algebra corresponding to
    ℕ. Any choice of zero results in an isomorphic algebra.
 *)
Definition nat_alg (n : ℕ) : algebra_ob nat_functor :=
  (ℕ,, nat_functor_equiv (dirprodpair n S)).

Definition nat_alg_z : algebra_ob nat_functor := nat_alg 0.

(** We may also define it directly. This will be judgmentally equal
    to [nat_alg_z]. *)
Example nat_alg' : algebra_ob nat_functor.
Proof.
  unfold algebra_ob, nat_functor; cbn; unfold polynomial_functor_obj; cbn.
  refine (ℕ,, λ pair, _).
  induction pair as [b rect].
  induction b; cbn in rect.
  - exact 0.
  - exact (S (rect tt)).
Defined.
Lemma nat_algs_eq : nat_alg_z = nat_alg'. Proof. reflexivity. Defined.

(** An algebra morphism between algebras for the nat functor is a
    function that respects all the relevant structure. *)
Definition mk_nat_functor_algebra_mor {X Y : algebra_ob nat_functor} :
  let X' := invmap nat_functor_equiv (pr2 X) in
  let Y' := invmap nat_functor_equiv (pr2 Y) in
  ∏ (f : pr1 X → pr1 Y),
    (f (pr1 X') = (pr1 Y')) × (f ∘ (pr2 X') = (pr2 Y') ∘ f)
  → is_algebra_mor _ X Y f.
Proof.
  intros X' Y' f.
  intro p.
  apply funextsec; intro pair.
  unfold compose, funcomp; cbn.
  induction pair as [b bfun]; induction b.
  + unfold polynomial_functor_arr, funcomp; cbn.
    rewrite (eqfromempty bfun).
    refine (pr1 p @ _).
    apply (maponpaths (pr2 Y)), maponpaths.
    symmetry; apply eqfromempty.
  + unfold polynomial_functor_arr, funcomp; cbn.
    rewrite (eta_unit bfun).
    exact (eqtohomot (pr2 p) (bfun tt)).
Defined.

(** Define the unique algebra morphism out of ℕ *)
Lemma nat_alg_is_preinitial : is_preinitial nat_alg_z.
Proof.
  intro X; pose (x := pr2 X).

  (** X has a "zero" and a "successor", just like ℕ, given by the algebra
      structure. We use these to define the unique morphism ℕ -> X
      by induction. *)
  pose (x0    := x (true,, fromempty)).
  pose (xsucc := (λ y, x (false,, λ _, y)) : pr1 X -> pr1 X).

  (** The recursor for ℕ gets an extra argument of type ℕ, which we don't pass
      to xsucc. Compare to [CategoryTheory.FunctorAlgebras.nat_ob_rec]. *)
  refine ((nat_rect _ x0 (λ _, xsucc)),, _).
  apply mk_nat_functor_algebra_mor; split; reflexivity.
Defined.

(** The first projection of the morphism out of ℕ (the actual function)
    is unique. *)
Lemma nat_alg_func_is_unique :
  ∏ X, ∏ (mor : algebra_mor _ nat_alg_z X), pr1 mor = pr1 (nat_alg_is_preinitial X).
Proof.
  intros X mor.
  induction X as [X x]; induction mor as [mor is_mor]; cbn in x.
  apply funextfun; intros n; induction n; cbn.
  - unfold is_algebra_mor in is_mor; cbn in is_mor.
    (** Use the condition that mor is an algebra morphism *)
    refine ((eqtohomot is_mor (true,, fromempty)) @ _).
    apply (maponpaths x).
    unfold polynomial_functor_arr; cbn.
    apply maponpaths.
    apply (eqfromempty _).
  - (** Use the condition that mor is an algebra morphism *)
    refine ((eqtohomot is_mor (false,, _)) @ _); cbn.
    apply (maponpaths x).
    unfold polynomial_functor_arr; cbn.
    apply maponpaths.
    apply funextsec; intros ttt; induction ttt.
    apply IHn.
Defined.

(** Define the section out of ℕ *)
Definition nat_alg_sec (X : fibered_alg nat_alg_z) : ∏ n : ℕ, pr1 X n.
Proof.
  pose (x := pr2 X).
  apply nat_rect.
  - exact (x (true,, fromempty) (empty_rect (pr1 X ∘ fromempty))).
  - intros ? fn.
    refine (x (false,, λ _, n) (λ b : unit, fn)).
Defined.

(** Prove it's really a section *)
Lemma nat_alg_is_preinitial_sec : is_preinitial_sec nat_alg_z.
Proof.
  intro E. pose (x := pr2 E).
  unfold is_preinitial, algebra_section.
  refine (nat_alg_sec E,, _).
  intros pair.
  induction pair as [b bfun]; cbn.
  induction b; cbn.
  - (* It would be nice to do this proof without `rewrite` *)
    rewrite (eqfromempty bfun).
    apply maponpaths, (proofirrelevancecontr (iscontrsecoverempty _)).
  - rewrite (eta_unit bfun). (* It would be nice to do this proof without `rewrite` *)
    apply maponpaths.
    reflexivity.
Defined.

(** Since fibered algebras are the "dependent version" of normal algebras,
    we need some kind of "dependent version" of the lemmas above.
 *)
Lemma sec_fromempty {X : UU} {Y : X -> UU}
      (f : ∅ -> X)
      (t : ∏ z : ∅, Y (f z)) : t = λ e, fromempty e.
Proof.
  apply funextsec; intros ?; induction _.
Defined.

(** A fibered algebra over ℕ consists of a family ℕ → UU, a point x0 : X 0,
    and a function from each X n to X (S n).
 *)
Definition fibered_algebra_nat :
  fibered_alg nat_alg_z ≃ ∑ (X : ∏ n : ℕ, UU), (X 0) × (∏ n, X n → X (S n)).
Proof.
  apply weqfibtototal; intro X; cbn in X.
  use weq_iso.
  - intro x.
    apply dirprodpair.
    + exact (x (true,, fromempty) (λ e, fromempty e)).
    + refine (λ n xn, _).
      unfold fibered_alg in x; cbn in x.
      apply (x (false,, λ _, n) (λ _, xn)).
  - intro x.
    unfold fibered_alg; cbn.
    intros pair from; induction pair as [b bfun].
    induction b; cbn in *.
    + exact (pr1 x).
    + exact (pr2 x (bfun tt) (from tt)).
  - cbn; intro g.
    apply funextsec; intro pair.
    induction pair as [b bfun].
    induction b; cbn; cbn in bfun.
    + apply funextsec; intro z.
      rewrite (sec_fromempty bfun z).
      rewrite (eqfromempty bfun).
      reflexivity.
    + rewrite (eta_unit bfun).
      apply funextsec; intro z.
      apply maponpaths.
      exact (!eta_unit z).
  - reflexivity.
Defined.
