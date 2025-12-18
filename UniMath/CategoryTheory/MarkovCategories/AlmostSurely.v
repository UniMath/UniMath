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
    apply pairing_flip.
    apply equal_almost_surely_r.
    assumption.
  Qed.

  Proposition equal_almost_surely_r2 {a x y z : C} (p : a --> x) (f g : x --> y) (h : x --> z) :
    equal_almost_surely p f g -> p · ⟨h, f⟩ = p · ⟨h, g⟩.
  Proof. 
    intros e.
    etrans. {
      rewrite pairing_split_l, assoc. 
      rewrite (equal_almost_surely_r p f g e).
      rewrite <- assoc, <- pairing_split_l.
      reflexivity.
    }
    reflexivity.
  Qed.

  Proposition equal_almost_surely_l2 {a x y z : C} (p : a --> x) (f g : x --> y) (h : x --> z) :
    equal_almost_surely p f g -> p · ⟨f, h⟩ = p · ⟨g, h⟩.
  Proof. 
    intros e.
    apply pairing_flip.
    apply equal_almost_surely_r2.
    assumption.
  Qed.

  Definition equal_almost_surely_composition {a x y : C} (p : a --> x) (f g : x --> y) :
    equal_almost_surely p f g -> (p · f) = (p · g).
  Proof.
    intros e.
    rewrite <- (pairing_proj1 f (identity _)).
    rewrite <- (pairing_proj1 g (identity _)).
    rewrite !assoc.
    rewrite (equal_almost_surely_l _ _ _ e).
    reflexivity.
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

  Proposition cancel_braiding_ase {y z : C} (f g : x --> y ⊗ z) :
    f · sym_mon_braiding _ y z =_{p} g · sym_mon_braiding _ y z -> f =_{p} g.
  Proof.
    intros ase.
    rewrite <- (id_right f), <- (id_right g).
    rewrite <- !sym_mon_braiding_inv, !assoc.
    apply ase_postcomp.
    exact ase.
  Qed.

  Proposition ase_pairing_l {y z : C} (f g : x --> y) (h : x --> z) :
    f =_{p} g -> ⟨f, h⟩ =_{p} ⟨g, h⟩.
  Proof.
    intros ase.
    apply make_equal_almost_surely_l.
    rewrite <- pairing_rassociator, assoc.
    rewrite (equal_almost_surely_l2 _ f g _ ase).
    rewrite <- assoc, pairing_rassociator.
    reflexivity.
  Qed.

  Proposition ase_pairing_r {y z : C} (f g : x --> y) (h : x --> z) :
    f =_{p} g -> ⟨h, f⟩ =_{p} ⟨h, g⟩.
  Proof.
    intros ase.
    apply cancel_braiding_ase.
    do 2 rewrite pairing_sym_mon_braiding.
    apply ase_pairing_l.
    exact ase.
  Qed.

End PropertiesAlmostSurely.

Section MiscellaneousLemmas.

  Proposition id_ase {C : markov_category} {x y : C} (f g : x --> y) :
    (f =_{identity x} g) -> f = g.
  Proof.
    intros ase.
    rewrite <- (pairing_proj1 f (identity x)), <- (pairing_proj1 g (identity x)).
    apply maponpaths_2.
    rewrite <- (id_left ⟨ f, identity x ⟩), <- (id_left ⟨ g, identity x ⟩).
    apply equal_almost_surely_l.
    exact ase.
  Qed. 

  Lemma copy_ase {C : markov_category} (x : C) : proj1 =_{copy x} proj2.
  Proof.
    apply make_equal_almost_surely_l.
    apply det_eta; try auto with autodet.
    - rewrite !assoc', !pairing_proj1.
      rewrite copy_proj1, copy_proj2.
      reflexivity.
    - rewrite !assoc', !pairing_proj2.
      reflexivity.
  Qed.

End MiscellaneousLemmas.

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

  Proposition is_deterministic_ase_stable {a x y : C} (p : a --> x) (f g : x --> y) :
    (f =_{p} g) -> is_deterministic_ase p f -> is_deterministic_ase p g.
  Proof. 
    intros ase df.
    unfold is_deterministic_ase.

    apply ase_trans with (f · copy y).
    { apply ase_postcomp. apply ase_symm. exact ase. }

    apply ase_trans with (copy x · f #⊗ f).
    { apply df.  }

    do 2 rewrite <- pairing_eq.

    apply ase_trans with (⟨ f, g ⟩).
    { apply ase_pairing_r. exact ase. }

    apply ase_pairing_l. exact ase.
  Qed.

  Proposition is_deterministic_ase_postcomp 
    {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z) 
    : is_deterministic_ase p f -> is_deterministic g -> is_deterministic_ase p (f · g).
  Proof.
    intros df dg.
    unfold is_deterministic_ase.
    rewrite assoc', dg.
    rewrite tensor_comp_mor, !assoc.
    apply ase_postcomp. 
    exact df.
  Qed.    

End AlmostSurelyDeterministic.

#[global] Opaque equal_almost_surely.