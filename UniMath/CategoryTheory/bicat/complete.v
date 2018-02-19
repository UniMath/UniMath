(* ========================================================================= *)
(* Check for completeness.                                                   *)
(* Every (pre)bicategory of UniMath.CategoryTheory.bicat  is a               *)
(* (pre)bicategory of UniMath.CategoryTheory.bicategories.                   *)
(* ========================================================================= *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.bicategories.prebicategory.

(*
Require Import UniMath.CategoryTheory.bicategories.whiskering.
 *)

Require Import UniMath.CategoryTheory.bicat.bicat.

Open Scope cat.
Open Scope bicategories.

Local Notation "C  'c×'  D" := (precategory_binproduct C D)
 (at level 75, right associativity).

Section Build_Bicategory.

Variable C : bicat.

Definition bicate_ob_hom : prebicategory_ob_hom.
Proof.
  exists C. exact (λ a b : C, hom a b).
Defined.

Definition bicate_id_comp : prebicategory_id_comp.
Proof.
  exists bicate_ob_hom; unfold bicate_ob_hom; simpl; split.
  - exact identity.
  - unfold hom_data, hom_ob_mor. simpl. intros a b c.
    apply hcomp_functor.
Defined.

Definition bicate_associator_fun {a b c d : bicate_id_comp}
           (x : C ⟦ a, b ⟧ × C ⟦ b, c ⟧ × C ⟦ c, d ⟧)
  : pr1 x · (pr12 x · pr22 x) ==> pr1 x · pr12 x · pr22 x
  := lassociator (pr1 x) (pr12 x) (pr22 x).

Lemma bicate_associator_fun_natural {a b c d : bicate_id_comp}
  : is_nat_trans
      (functor_composite
         (pair_functor (functor_identity (hom a b)) (compose_functor b c d))
         hcomp_functor)
      (functor_composite
         (precategory_binproduct_assoc (hom a b) (hom b c) (hom c d))
         (functor_composite
            (pair_functor (compose_functor a b c) (functor_identity (hom c d)))
            hcomp_functor)) bicate_associator_fun.
Proof.
  red; cbn. intros (f1, (f2, f3)) (g1, (g2, g3)).
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  intros (x1, (x2, x3)). simpl.
  unfold bicate_associator_fun. simpl.
  apply hcomp1_lassoc.
Defined.

Definition bicate_associator (a b c d : bicate_id_comp) : associator_trans_type a b c d.
Proof.
  exists bicate_associator_fun.
  exact bicate_associator_fun_natural.
Defined.

Lemma bicate_left_unitor (a b : bicate_id_comp) : left_unitor_trans_type a b.
Proof.
  unfold bicate_id_comp, left_unitor_trans_type. simpl. intros.
  red. cbn.
  unfold identity1
Defined.

Lemma bicate_right_unitor (a b : bicate_id_comp) : right_unitor_trans_type a b.
Proof.
  unfold bicate_id_comp, right_unitor_trans_type. simpl. intros.
Admitted.

Lemma bicate_trans :
  (∏ a b c d : bicate_id_comp, associator_trans_type a b c d) ×
  (∏ a b : bicate_id_comp, left_unitor_trans_type a b) ×
  (∏ a b : bicate_id_comp, right_unitor_trans_type a b).
Proof.
  repeat split.
  - exact bicate_associator.
  - exact bicate_left_unitor.
  - exact bicate_right_unitor.
Defined.

Definition bicate_data : prebicategory_data.
Proof.
  exists bicate_id_comp. exact bicate_trans.
Defined.

Definition associator_and_unitors_are_iso (C : prebicategory_data) : UU
  :=   (∏ (a b c d : C) (f : a -1-> b) (g : b -1-> c) (h : c -1-> d),
          is_iso (associator_2mor f g h))
     × (∏ (a b : C) (f : a -1-> b), is_iso (left_unitor_2mor f))
     × (∏ (a b : C) (g : a -1-> b), is_iso (right_unitor_2mor g)).

(* It suffices to check the pentagon/triangle axioms pointwise *)

Definition pentagon_axiom_type {C : prebicategory_data} {a b c d e : C}
     (k : a -1-> b) (h : b -1-> c) (g : c -1-> d) (f : d -1-> e)
  : UU
  :=
    (* Anticlockwise *)
    associator_2mor k h (g ;1; f) ;v; associator_2mor (k ;1; h) g f
    =
    (* Clockwise *)
        (identity k ;h; associator_2mor h g f)
    ;v; associator_2mor k (h ;1; g) f
    ;v; (associator_2mor k h g ;h; identity f).

Definition triangle_axiom_type {C : prebicategory_data} {a b c : C}
    (f : a -1-> b)
    (g : b -1-> c)
  : UU
  := identity f ;h; left_unitor_2mor g =
     associator_2mor f (identity1 b) g ;v; (right_unitor_2mor f ;h; identity g).

Definition prebicategory_coherence (C : prebicategory_data) : UU
  :=   (∏ (a b c d e : C) (k : a -1-> b) (h : b -1-> c) (g : c -1-> d) (f : d -1-> e),
          pentagon_axiom_type k h g f)
     × (∏ (a b c : C) (f : a -1-> b) (g : b -1-> c), triangle_axiom_type f g).

Definition is_prebicategory (C : prebicategory_data) : UU
  :=   has_2mor_sets C
     × associator_and_unitors_are_iso C
     × prebicategory_coherence C.

(* *********************************************************************************** *)
(** ** Final packing and projections. *)

Definition prebicategory : UU := total2 is_prebicategory.

Definition has_homcats (C : prebicategory) : UU
  := ∏ a b : C, is_univalent (a -1-> b).

Definition pentagon_axiom {C : prebicategory} {a b c d e: C}
    (k : a -1-> b) (h : b -1-> c) (g : c -1-> d) (f : d -1-> e)
  : pentagon_axiom_type k h g f
  := pr1 (pr2 (pr2 (pr2 C))) a b c d e k h g f.

Definition triangle_axiom {C : prebicategory} {a b c : C}
    (f : a -1-> b) (g : b -1-> c)
  : triangle_axiom_type f g
  := pr2 (pr2 (pr2 (pr2 C))) a b c f g.
*)