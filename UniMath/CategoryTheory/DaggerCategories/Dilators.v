(*********************************************
Dilators

A dilation is a presentation of a map in a dagger category by a 
span of coisometries. A dilator is a terminal dilation. Dagger categories in which
every morphism has a dilator have a rich theory, generalizing aspects of 
allegories and regular categories. 

In this file, we develop the basic theory of dilations and dilators.

Table of Contents
1. Definition of dilatins and dilators


- Matthew Di Meglio - 'R*-categories: The Hilbert-space analogue of abelian categories'
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Isometry.

Local Open Scope cat.

(** * 1. Definition of dilatins and dilators *)
Section Dilators.
  Context (C : dagger_category).
  Local Notation "f †" := (C _ _ f).

  Definition dilation {x y : C} (f : x --> y) :=
    ∑ p : C, 
      ∑ (u : coisometry C p x) (v : coisometry C p y),
      u † · v = f.

  Definition dilation_map {x y : C} {f : x --> y} (d1 : dilation f) (d2 : dilation f) : UU.
  Proof.
    destruct d1 as (p & u1 & v1 & e1).
    destruct d2 as (q & u2 & v2 & e2).
    exact (∑ h : coisometry C p q, 
      (h · u2 = u1) × (h · v2 = v1)).
  Defined.

  Proposition dilation_map_eq {x y : C} {f : x --> y} {d e : dilation f} (h1 h2 : dilation_map d e)
    : pr1 h1 = pr1 h2 -> h1 = h2.
  Proof.
    intros p.
    use subtypePath.
    { intro. use isapropdirprod; use homset_property. }
    exact p.
  Qed.    

  Definition is_dilator {x y : C} {f : x --> y} (e : dilation f) : UU
    := ∏ d : dilation f, iscontr (dilation_map d e).

  Lemma isaprop_is_dilator {x y : C} {f : x --> y} {d : dilation f} 
    : isaprop (is_dilator d).
  Proof.
    apply impred.
    intro.
    apply isapropiscontr.
  Qed.

  Definition dilator {x y : C} (f : x --> y) : UU
    := ∑ d : dilation f, is_dilator d.

  Definition with_dilators : UU :=
    ∏ (x y : C) (f : x --> y), dilator f.

  Definition has_dilators : UU :=
    ∏ (x y : C) (f : x --> y), ∥dilator f∥.

  (* Example: dilations of the identity *)

  Definition dilation_id_id (x : C) : dilation (identity x).
  Proof.
    refine (x ,, coisometry_id C x ,, coisometry_id C x ,, _).
    cbn.
    rewrite dagger_to_law_id, id_left.
    reflexivity.
  Defined.

  (* If C has dilators, then [dilation_id_id] is one as well *)
  Lemma dilator_id_id (x : C) (dil : with_dilators) : is_dilator (dilation_id_id x).
  Proof.
    intros d.

    (* Find a dilator of the identity *)
    destruct (dil _ _ (identity x)) as ((q & [s sco] & [t tco] & ee) & is_dil).

    (* Factor the dilation (id,id) *)
    destruct (pr1 (is_dil (dilation_id_id x))) as (w & e1 & e2).

    (* Factor the dilation d*)
    destruct (pr1 (is_dil d)) as (h & f1 & f2).

    destruct d as (p & [u uco] & [v vco] & e); cbn in *.

    assert(eq1 : s = t). {
      refine (coisometry_epi _ w _ _ _).
      rewrite e2.
      exact e1.       
    } 
    
    assert(eq2 : u = v). { 
      rewrite <- f1, <- f2.
      rewrite eq1.
      reflexivity.
    }

    unfold dilation_map.
    cbn.
    rewrite eq2.
    use make_iscontr.
    - exists (v ,, vco).
      rewrite !id_right.
      split ; reflexivity.
    - intros [h2 [P Q]].
      use subtypePath.
      { intro. use isapropdirprod; use homset_property. }
      apply coisometry_eq.
      cbn.
      rewrite <- (id_right (pr1 h2)).
      exact P.
  Qed.  
       
End Dilators.