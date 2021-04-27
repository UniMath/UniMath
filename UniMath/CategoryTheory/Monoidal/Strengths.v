(**
  Definition of tensorial strengths between actions over monoidal categories.

  Based on the definitions in the paper "Second-Order and Dependently-Sorted Abstract Syntax" by Marcelo Fiore.
**)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.Actions.

Local Open Scope cat.

Section A.

Context (Mon_V : monoidal_precat).

Let V := monoidal_precat_precat Mon_V.
Let I := monoidal_precat_unit Mon_V.
Let tensor := monoidal_precat_tensor Mon_V.
Notation "X ⊗ Y" := (tensor (X , Y)).

Section Strengths_Definition.

Context (actn actn' : action Mon_V).

Let A := pr1 actn.
Let odot := pr1 (pr2 actn).
Let ϱ := pr1 (pr2 (pr2 actn)).
Let χ := pr1 (pr2 (pr2 (pr2 actn))).
Let A' := pr1 actn'.
Let odot' := pr1 (pr2 actn').
Let ϱ' := pr1 (pr2 (pr2 actn')).

Let χ' := pr1 (pr2 (pr2 (pr2 actn'))).

Section Strengths_Natural_Transformation.

Context (F : A ⟶ A').

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (#odot (f #, g)) (at level 31).
Notation "X ⊙' Y" := (odot' (X , Y)) (at level 31).
Notation "f #⊙' g" := (#odot' (f #, g)) (at level 31).

Definition strength_dom : A ⊠ V ⟶ A' :=
  functor_composite (pair_functor F (functor_identity _)) odot'.

Lemma strength_dom_ok: functor_on_objects strength_dom = λ ax, F (ob1 ax) ⊙' (ob2 ax).
Proof.
  apply idpath.
Qed.

Definition strength_codom : A ⊠ V ⟶ A' :=
  functor_composite odot F.

Lemma strength_codom_ok: functor_on_objects strength_codom = λ ax, F (ob1 ax ⊙ ob2 ax).
Proof.
  apply idpath.
Qed.

Definition strength_nat : UU := nat_trans strength_dom strength_codom.

Definition strength_triangle_eq (ϛ : strength_nat) :=
  ∏ (a : A), (pr1 ϛ (a, I)) · (#F (pr1 ϱ a)) = pr1 ϱ' (F a).

Definition strength_pentagon_eq (ϛ : strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  (pr1 χ' ((F a, x), y)) · pr1 ϛ (a, x ⊗ y) =
  (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)) · (#F (pr1 χ ((a, x), y))).

(** the original notion in Fiore's LICS'08 paper *)
Definition strength_pentagon_eq_variant1 (ϛ : strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  pr1 ϛ (a, x ⊗ y) =
  (nat_iso_to_trans_inv χ' ((F a, x), y)) · (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)) · (#F (pr1 χ ((a, x), y))).

(** the notion that fits with the definition of relative strength in the TYPES'15 post-proceedings paper by Ahrens and Matthes *)
Definition strength_pentagon_eq_variant2 (ϛ : strength_nat): UU := ∏ (a : A), ∏ (x y : V),
  pr1 ϛ (a, x ⊗ y) · (#F (nat_iso_to_trans_inv χ ((a, x), y))) =
  (nat_iso_to_trans_inv χ' ((F a, x), y)) · (pr1 ϛ (a, x)) #⊙' (id y) · (pr1 ϛ (a ⊙ x, y)).


End Strengths_Natural_Transformation.

Definition strength (F : A ⟶ A'): UU := ∑ (ϛ : strength_nat F),
  (strength_triangle_eq F ϛ) × (strength_pentagon_eq F ϛ).

Definition strength_variant1 (F : A ⟶ A'): UU := ∑ (ϛ : strength_nat F),
  (strength_triangle_eq F ϛ) × (strength_pentagon_eq_variant1 F ϛ).

Definition strength_variant2 (F : A ⟶ A'): UU := ∑ (ϛ : strength_nat F),
  (strength_triangle_eq F ϛ) × (strength_pentagon_eq_variant2 F ϛ).


End Strengths_Definition.

(*
  The standard tensorial strength:
  F(A) ⊗ B --> F(A ⊗ B)
*)
Definition tensorial_strength := strength (tensorial_action Mon_V) (tensorial_action Mon_V).

End A.

Section B.
(** following the TYPES'15 post-proceedings paper by Ahrens and Matthes - will be identified as an instance of the previous *)

  Context (Mon_W Mon_V : monoidal_precat).

  Let V := monoidal_precat_precat Mon_V.
  Let timesV := monoidal_precat_tensor Mon_V.
  Let I := monoidal_precat_unit Mon_V.
  Let lambda := monoidal_precat_left_unitor Mon_V.
  Let alpha := monoidal_precat_associator Mon_V.

  Let W := monoidal_precat_precat Mon_W.
  Let timesW := monoidal_precat_tensor Mon_W.
  Let E := monoidal_precat_unit Mon_W.

  Context (U:strong_monoidal_functor Mon_W Mon_V).
  Let phiI := pr1 (pr2 (pr1 U)).
  Let phiIinv := inv_from_iso (make_iso phiI (pr1 (pr2 U))).
  Let phi := pr1 (pr2 (pr2 (pr1 U))).
  Let phiinv := nat_iso_to_trans_inv (make_nat_iso _ _ phi (pr2 (pr2 U))).

Section Relative_Strengths_Natural_Transformation.
  Context (F: functor V V).

  Notation "X ⊗V Y" := (timesV (X , Y)) (at level 31).
  Notation "X •W Y" := (timesW (X , Y)) (at level 31).

  Notation "f #⊗V g" := (#timesV (f #, g)) (at level 31).
  Notation "f #•W g" := (#timesW (f #, g)) (at level 31).

  Definition rel_strength_dom : W ⊠ V ⟶ V :=
    functor_composite (pair_functor U F) timesV.

  Lemma rel_strength_dom_ok: functor_on_objects rel_strength_dom = λ ax, U (ob1 ax) ⊗V  F (ob2 ax).
  Proof.
    apply idpath.
  Qed.

  Definition rel_strength_codom : W ⊠ V ⟶ V :=
  functor_composite (functor_composite (pair_functor U (functor_identity _)) timesV) F.

  Lemma rel_strength_codom_ok: functor_on_objects rel_strength_codom = λ ax, F (U (ob1 ax) ⊗V ob2 ax).
  Proof.
    apply idpath.
  Qed.

  Definition rel_strength_nat : UU := nat_trans rel_strength_dom rel_strength_codom.

  (** the following looks like a pentagon but is of the nature of a triangle equation *)
  Definition rel_strength_pentagon_eq (ϛ : rel_strength_nat) :=
    ∏ (v : V), (pr1 ϛ (E, v)) · (#F (phiIinv #⊗V (identity v))) · (#F (pr1 lambda v))  =
               (phiIinv #⊗V (identity (F v))) · (pr1 lambda (F v)).

  (** the following looks like a rectangle in the paper but is of the nature of a pentagon equation *)
  Definition rel_strength_rectangle_eq (ϛ : rel_strength_nat): UU := ∏ (w w' : W), ∏ (v : V),
  ( pr1 ϛ (w •W w', v) ) · (#F (phiinv (w, w') #⊗V (identity v))) · (#F (pr1 alpha ((U w, U w'), v))) =
  (phiinv (w, w') #⊗V (identity (F v))) · (pr1 alpha ((U w, U w'), F v)) ·
                                        ((identity (U w)) #⊗V pr1 ϛ (w', v)) · ( pr1 ϛ (w, U w' ⊗V v)).

End Relative_Strengths_Natural_Transformation.

Definition rel_strength (F : V ⟶ V): UU :=
  ∑ (ϛ : rel_strength_nat F), (rel_strength_pentagon_eq F ϛ) × (rel_strength_rectangle_eq F ϛ).


Section Relative_Strength_Is_A_Strength.

  Context (F: functor V V).
  Context (str: rel_strength F).

  Let ϛ := pr1 str.
  Let pentagon := pr1 (pr2 str).
  Let rectangle := pr2 (pr2 str).

(* TO BE CONTINUED *)


End Relative_Strength_Is_A_Strength.

End B.
