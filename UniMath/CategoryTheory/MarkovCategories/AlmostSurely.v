(*********************************************
Almost-sure Equality

In this file, we define the notion almost-sure equality and prove basic lemmas about it.

Given a state p : I --> x, two morphisms f,g : x --> y are p-almost surely equal if the 
distributions p · ⟨id, f⟩ = p · ⟨id, g⟩ coincide. This abstract property captures and generalizes
almost-sure equality from probability theory, namely that the channels f(x) and g(x) are equal on the
support of p, i.e. all x with p(x) > 0.

Almost-sure equality is an equivalence relation, and many constructions such as 
conditionals and Bayesian inverses are only unique up to almost-sure equality.  
The category of probability spaces in `ProbabilitySpaces.v` is defined using
the quotient modulo almost-sure equality.

Some useful properties of almost-sure equality only hold when assuming further axioms such as causality. 
Those properties are proved in `InformationFlowAxioms.v`.

Table of Contents
1. Definition of Almost Sure Equality
2. Basic Lemmas 
3. Definition of Almost Sure Determinism

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics' 
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

(** * 1. Definition of Almost Sure Equality *)

Section DefAlmostSurely.
  Context {C : markov_category}.

  Definition equal_almost_surely {a x y : C} (p : a --> x) (f g : x --> y) : UU
    := p · ⟨identity _, f⟩ = p · ⟨identity _, g⟩.

  Proposition equal_almost_surely_r {a x y : C} (p : a --> x) (f g : x --> y) :
    equal_almost_surely p f g -> p · ⟨identity _, f⟩ = p · ⟨identity _, g⟩.
  Proof. 
    intros e. rewrite e. reflexivity.
  Qed.

  Proposition equal_almost_surely_l {a x y : C} (p : a --> x) (f g : x --> y) :
    equal_almost_surely p f g -> p · ⟨f, identity _⟩ = p · ⟨g, identity _⟩.
  Proof. 
    intros e.
    apply cancel_braiding.
    rewrite !assoc', !pairing_sym_mon_braiding.
    apply equal_almost_surely_r.
    assumption.
  Qed.
    
  Proposition make_equal_almost_surely_r {a x y : C} (p : a --> x) (f g : x --> y) :
    p · ⟨identity _, f⟩ = p · ⟨identity _, g⟩ -> equal_almost_surely p f g.
  Proof. 
    intros e.
    exact e.
  Qed.

  Proposition make_equal_almost_surely_l {a x y : C} (p : a --> x) (f g : x --> y) :
    p · ⟨f, identity _⟩ = p · ⟨g, identity _⟩ -> equal_almost_surely p f g.
  Proof. 
    intros e.
    apply cancel_braiding.
    rewrite !assoc', !pairing_sym_mon_braiding.
    assumption.
  Qed.

  Proposition isaprop_ase {a x y : C} (p : a --> x) (f g : x --> y) :
      isaprop (equal_almost_surely p f g).
  Proof. 
    apply homset_property.
  Qed.  

End DefAlmostSurely.

Arguments equal_almost_surely {C a x y} p f g /.
Notation "f =_{ p } g" := (equal_almost_surely p f g) (at level 70) : markov.

(** * 2. Basic Lemmas *)

Section PropertiesAlmostSurely.

  Context {C : markov_category}
          {a x : C}
          (p : a --> x).

  Proposition ase_refl {y : C} (f : x --> y) : f =_{p} f.
  Proof. 
    reflexivity.
  Qed.

  Proposition ase_symm {y : C} (f g : x --> y) :
    f =_{p} g -> g =_{p} f.
  Proof. 
    cbn.
    intros ->.
    reflexivity.
  Qed.

  Proposition ase_trans {y : C} (f g h : x --> y) :
    f =_{p} g -> g =_{p} h -> f =_{p} h.
  Proof.
    intros e1 e2.
    cbn in *.
    rewrite e1, e2.
    reflexivity.
  Qed.

  Proposition ase_from_eq {y : C} (f g : x --> y) : 
    f = g -> f =_{p} g.
  Proof.
    intros e.
    rewrite e.
    apply ase_refl.
  Qed.

  Proposition ase_postcomp {y z : C} (f1 f2 : x --> y) (h : y --> z) :
       f1 =_{p} f2 
    -> f1 · h =_{p} f2 · h.
  Proof.
    cbn.
    intros e.
    rewrite <- (id_left (identity x)).
    rewrite <- !pairing_tensor.
    rewrite !assoc.
    rewrite e.
    reflexivity.
  Qed.

  Proposition ase_precomp {y : C} (f g : x --> y) :
    f =_{p} g -> p · f = p · g.
  Proof.
    intros ase.
    rewrite <- (pairing_proj2 (identity _) f).
    rewrite <- (pairing_proj2 (identity _) g).
    rewrite !assoc.
    rewrite ase.
    reflexivity.
  Qed.    

End PropertiesAlmostSurely.

(** * 3. Definition of Almost Sure Determinism *)

Section AlmostSurelyDeterministic.
  Context {C : markov_category}.

  Definition is_deterministic_ase {a x y : C} (p : a --> x) (f : x --> y) : UU
   := f · copy y =_{p} copy x · f #⊗ f.

  Proposition deterministic_implies_determinstic_ase 
            {a x y : C} (p : a --> x) (f : x --> y) :
    is_deterministic f -> is_deterministic_ase p f.
  Proof.
    intros e.
    apply ase_from_eq.
    exact e.
  Qed.

End AlmostSurelyDeterministic.