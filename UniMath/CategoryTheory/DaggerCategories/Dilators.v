(*********************************************
Dilators

A dilation is a presentation of a map in a dagger category by a 
span of coisometries. A dilator is a terminal dilation. Dagger categories in which
every morphism has a dilator have a rich theory, generalizing aspects of 
allegories and regular categories. 

In this file, we develop the basic theory of dilations and dilators.

Table of Contents
1. Definition of Dilations
2. Maps of Dilations
3. Definition of Dilators
4. Some Lemmas about Dilators


- Matthew Di Meglio: 'R*-categories: The Hilbert-space analogue of abelian categories'
- Matthew Di Meglio, Chris Heunen, Jean-Simon Pacaud Lemay, Paolo Perrone, Dario Stein:
  'Dagger categories of relations: the equivalence of dilatory dagger categories
                                   and epi-regular independence categories'
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Isometry.

Local Open Scope cat.

(** * 1. Definition of Dilations *)

Section Dilations.
  Context (C : dagger_category).

  Definition dilation {x y : C} (f : x --> y) :=
    ∑ r : C, 
      ∑ (u : coisometry C r x) (v : coisometry C r y),
      {u}_C^† · v = f.

  Definition make_dilation_from_coisometries {x y r : C}
    (f : x --> y) (u : coisometry C r x) (v : coisometry C r y) (eq : {u}_C^† · v = f) : dilation f.
  Proof.
    exact (r ,, u ,, v ,, eq).
  Defined.

  Definition make_dilation {x y r : C}
    (f : x --> y) (u : r --> x) (v : r --> y)
    (iso_u : is_coisometry C u) (iso_v : is_coisometry C v) (eq : {u}_C^† · v = f) : dilation f.
  Proof.
    simple refine (r ,, _ ,, _ ,, _).
    - use make_coisometry.
      * exact u.
      * exact iso_u.
    - use make_coisometry.
      * exact v.
      * exact iso_v.
    - abstract (exact eq).
  Defined.

  Coercion apex {x y : C} {f : x --> y} (d : dilation f) : C := pr1 d. 
  Definition left_leg {x y : C} {f : x --> y} (d : dilation f) : coisometry C (apex d) x := pr12 d.
  Definition right_leg {x y : C} {f : x --> y} (d : dilation f) : coisometry C (apex d) y := pr122 d.

  Proposition dilation_eq {x y : C} {f : x --> y} (d : dilation f) :
    {left_leg d}_C^† · right_leg d = f.
  Proof.
    exact (pr222 d).
  Qed.

End Dilations.

Arguments apex {C} {x y} {f}.
Arguments left_leg {C} {x y} {f}.
Arguments right_leg {C} {x y} {f}.

(** * 2. Maps of Dilations *)

Section DilationMaps.
  Context (C : dagger_category).

  Definition dilation_map {x y : C} {f : x --> y} (d : dilation C f) (e : dilation C f) : UU
    := ∑ h : coisometry C (apex d) (apex e), 
        (h · left_leg e = left_leg d) × (h · right_leg e = right_leg d).

  Coercion dilation_map_to_coisom 
      {x y : C} {f : x --> y} {d e : dilation C f} (h : dilation_map d e)
    : coisometry C d e := pr1 h.

  Definition make_dilation_map_from_coisometries
    {x y : C} {f : x --> y} {d : dilation C f} {e : dilation C f}
    (h : coisometry C d e)
    (eq_left : h · left_leg e = left_leg d)
    (eq_right : h · right_leg e = right_leg d)
    : dilation_map d e.
  Proof.
    exact (h ,, eq_left ,, eq_right).
  Defined.

  Definition make_dilation_map 
      {x y : C} {f : x --> y} {d : dilation C f} {e : dilation C f}
      (h : d --> e)
      (coiso_h : is_coisometry C h)
      (eq_left : h · left_leg e = left_leg d)
      (eq_right : h · right_leg e = right_leg d)
      : dilation_map d e.
  Proof.
    use make_dilation_map_from_coisometries.
    - use make_coisometry.
      * exact h.
      * exact coiso_h.
    - exact eq_left.
    - exact eq_right.
  Defined.

  (* Accessors *)

  Proposition dilation_map_eq_left 
      {x y : C} {f : x --> y} {d : dilation C f} {e : dilation C f} (h : dilation_map d e)
    : h · left_leg e = left_leg d.
  Proof.
    exact (pr12 h).
  Qed.

  Proposition dilation_map_eq_right 
      {x y : C} {f : x --> y} {d : dilation C f} {e : dilation C f} (h : dilation_map d e)
    : h · right_leg e = right_leg d.
  Proof.
    exact (pr22 h).
  Qed. 

  Proposition dilation_map_ext {x y : C} {f : x --> y} {d e : dilation C f} (h1 h2 : dilation_map d e)
    : pr1 h1 = pr1 h2 -> h1 = h2.
  Proof.
    intros p.
    use subtypePath.
    { intro. use isapropdirprod; use homset_property. }
    exact p.
  Qed.

End DilationMaps.

(** * 3. Definition of Dilators *)

Section Dilators.
  Context (C : dagger_category).

  (* A dilator is a terminal dilation *)

  Definition is_dilator {x y : C} {f : x --> y} (e : dilation C f) : UU
    := ∏ d : dilation C f, iscontr (dilation_map C d e).

  Lemma isaprop_is_dilator {x y : C} {f : x --> y} {d : dilation C f} 
    : isaprop (is_dilator d).
  Proof.
    apply impred.
    intro.
    apply isapropiscontr.
  Qed.

  Definition dilator {x y : C} (f : x --> y) : UU
    := ∑ d : dilation C f, is_dilator d.

  Definition with_dilators : UU :=
    ∏ (x y : C) (f : x --> y), dilator f.

  Definition has_dilators : UU :=
    ∏ (x y : C) (f : x --> y), ∥dilator f∥.

End Dilators.

(** * 4. Some Lemmas about Dilators *)

Section DilatorLemmas.
  Context (C : dagger_category).

  (* Example: the identity span is a dilation of the identity *)

  Definition dilation_id_id (x : C) : dilation C (identity x).
  Proof.
    refine (x ,, coisometry_id C x ,, coisometry_id C x ,, _).
    cbn.
    rewrite dagger_to_law_id, id_left.
    reflexivity.
  Defined.

  (* If C has dilators, then [dilation_id_id] is a dilator *)
  Lemma dilator_id_id (x : C) (dil : with_dilators C) : is_dilator C (dilation_id_id x).
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

    use make_iscontr. {
      exists (v ,, vco).
      rewrite !id_right.
      split.
      - rewrite eq2. reflexivity.
      - reflexivity. }
    
    intros [h2 [P Q]].
    use dilation_map_ext.
    apply coisometry_ext.
    cbn.
    rewrite <- eq2.
    rewrite <- (id_right (pr1 h2)).
    exact P.
  Qed.  
       
End DilatorLemmas.