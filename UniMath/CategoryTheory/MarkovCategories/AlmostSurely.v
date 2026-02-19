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
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

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

  Proposition ase_pairing {y z : C} (f1 f2 : x --> y) (g1 g2 : x --> z) :
    f1 =_{p} f2 -> g1 =_{p} g2 -> ⟨f1, g1⟩ =_{p} ⟨f2, g2⟩.
  Proof.
    intros ase_f ase_g.
    apply ase_trans with (⟨f2, g1⟩).
    { apply ase_pairing_l; exact ase_f. }
    apply ase_pairing_r; exact ase_g.
  Qed.

End PropertiesAlmostSurely.

Section MiscellaneousLemmas.
  Context {C : markov_category}.

  Proposition id_ase {x y : C} (f g : x --> y) :
    (f =_{identity x} g) -> f = g.
  Proof.
    intros ase.
    rewrite <- (pairing_proj1 f (identity x)), <- (pairing_proj1 g (identity x)).
    apply maponpaths_2.
    rewrite <- (id_left ⟨ f, identity x ⟩), <- (id_left ⟨ g, identity x ⟩).
    apply equal_almost_surely_l.
    exact ase.
  Qed. 

  Lemma copy_ase (x : C) : proj1 =_{copy x} proj2.
  Proof.
    apply make_equal_almost_surely_l.
    apply det_eta; try auto with autodet.
    - rewrite !assoc', !pairing_proj1.
      rewrite copy_proj1, copy_proj2.
      reflexivity.
    - rewrite !assoc', !pairing_proj2.
      reflexivity.
  Qed.

  Proposition ase_tensor_split {a1 a2 x1 x2 y1 y2 : C} 
    {p1 : a1 --> x1} {p2 : a2 --> x2}
    {f1 : x1 --> y1} {f2 : x2 --> y2}
    {g1 : x1 --> y1} {g2 : x2 --> y2}
    : f1 =_{p1} g1 -> f2 =_{p2} g2 -> (f1 #⊗ f2) =_{p1 #⊗ p2} (g1 #⊗ g2).
  Proof.
    intros ase1 ase2.
    apply make_equal_almost_surely_r.
    rewrite <- !tensor_id_id.
    rewrite <- !pairing_inner_swap, !assoc.
    apply maponpaths_2.
    rewrite <- !tensor_comp_mor.
    apply maponpaths_12.
    - apply equal_almost_surely_r; exact ase1.
    - apply equal_almost_surely_r; exact ase2.
  Qed.

  Proposition cancel_z_iso_ase {a x y z : C}
      {p : a --> x} {f1 f2 : x --> y} (g : z_iso y z)
    : f1 · g =_{p} f2 · g -> f1 =_{p} f2.
  Proof.
    intros ase.
    assert(e1 : f1 = f1 · g · inv_from_z_iso g).
    { rewrite assoc', z_iso_inv_after_z_iso, id_right. reflexivity. }
    assert(e2 : f2 = f2 · g · inv_from_z_iso g).
    { rewrite assoc', z_iso_inv_after_z_iso, id_right. reflexivity. }
    rewrite e1, e2.
    apply ase_postcomp.
    exact ase.
  Qed.

End MiscellaneousLemmas.

#[global] Opaque equal_almost_surely.

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
    apply ase_pairing; exact ase.
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

  Proposition is_deterministic_ase_tensor 
      {a1 x1 y1 a2 x2 y2 : C} {p1 : a1 --> x1} {f1 : x1 --> y1}
      {p2 : a2 --> x2} {f2 : x2 --> y2} 
    :    is_deterministic_ase p1 f1 -> is_deterministic_ase p2 f2 
      -> is_deterministic_ase (p1 #⊗ p2) (f1 #⊗ f2).
  Proof.
    intros d1 d2.
    unfold is_deterministic_ase.
    use cancel_z_iso_ase.
    - exact ((y1 ⊗ y1) ⊗ (y2 ⊗ y2)).
    - exists (inner_swap _ _ _ _ _); apply inner_swap_is_z_isomorphism.
    - apply ase_trans with ((f1 · copy y1) #⊗ (f2 · copy y2)). {
        rewrite assoc', copy_tensor'.
        rewrite <- tensor_comp_mor.
        apply ase_refl.
      }

      rewrite assoc', <- naturality_inner_swap.
      rewrite assoc, copy_tensor'.
      rewrite <- tensor_comp_mor.

      apply ase_tensor_split.
      * exact d1.
      * exact d2.
  Qed.   

  Proposition is_deterministic_ase_pairing
      {a x y z : C} {p : a --> x} {f : x --> y} {g : x --> z} 
    :    is_deterministic_ase p f -> is_deterministic_ase p g 
      -> is_deterministic_ase p ⟨f,g⟩.
  Proof.
    intros d1 d2.
    unfold is_deterministic_ase.
    use cancel_z_iso_ase.
    - exact (y ⊗ y ⊗ (z ⊗ z)).
    - exists (inner_swap _ _ _ _ _); apply inner_swap_is_z_isomorphism.
    - apply ase_trans with (⟨f · copy y, g · copy z⟩). {
        apply ase_from_eq.
        rewrite assoc', copy_tensor'.
        rewrite pairing_tensor.
        reflexivity.
      }
      cbn.
      rewrite assoc'.
      rewrite pairing_inner_swap.
      rewrite copy_pairing.
      apply ase_pairing.
      * exact d1.
      * exact d2.
  Qed.

End AlmostSurelyDeterministic.
