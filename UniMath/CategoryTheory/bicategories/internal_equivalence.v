Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.equivalences.

Require Import UniMath.CategoryTheory.bicategories.prebicategory.
Require Import UniMath.CategoryTheory.bicategories.whiskering.
Require Import UniMath.CategoryTheory.bicategories.notations.

Definition inv {C:precategory} {a b : C}
 (f : iso a b)
 := iso_inv_from_iso f.

(******************************************************************************)
(* Internal Equivalence *)

Definition is_int_equivalence {C : prebicategory} {a b : C}
  (f : a -1-> b)
  := total2 (fun g : b -1-> a => (iso (identity_1mor a) (f ;1; g))
                            × (iso (g ;1; f) (identity_1mor b))).

Definition int_equivalence {C : prebicategory}
  (a b : C)
  := total2 (fun f : a -1-> b => is_int_equivalence f).

Definition identity_int_equivalence {C : prebicategory}
  (a : C) : int_equivalence a a.
Proof.
  exists (identity_1mor a).
  exists (identity_1mor a).
  split.
  - exact (inv (left_unitor (identity_1mor a))).
  - exact (left_unitor (identity_1mor a)).
Defined.

Definition id_to_int_equivalence {C : prebicategory} (a b : C)
  : (a = b) -> int_equivalence a b.
Proof.
  intros p.
  induction p.
  exact (identity_int_equivalence a).
Defined.

(******************************************************************************)
(* Internal Adjoint Equivalence *)

Definition is_adj_int_equivalence {C : prebicategory} { a b : C }
  (f : a -1-> b)
  := total2 (fun g : b -1-> a =>
     total2 (fun etaeps : (iso (identity_1mor a) (f ;1; g)) × (iso (g ;1; f) (identity_1mor b)) =>
               let eta := pr1 etaeps in
               let eps := pr2 etaeps in
       (
             (inv (left_unitor f))
         ;v; (whisker_right eta f)
         ;v; (inv (associator _ _ _))
         ;v; (whisker_left f eps)
         ;v; (right_unitor _)
           = (identity f)
       ) × (
             (inv (right_unitor g))
         ;v; (whisker_left g eta)
         ;v; (associator _ _ _)
         ;v; (whisker_right eps g)
         ;v; (left_unitor _) = (identity g)
       )
     )).

Definition adj_int_equivalence {C : prebicategory}
  (a b : C)
  := total2 (fun f : a -1-> b => is_adj_int_equivalence f).

Local Definition identity_triangle1 {C : prebicategory}
  (a : C) :
      (inv (left_unitor (identity_1mor a)))
  ;v; (whisker_right (inv (left_unitor (identity_1mor a))) (identity_1mor a))
  ;v; (inv (associator _ _ _))
  ;v; (whisker_left (identity_1mor a) (right_unitor (identity_1mor a)))
  ;v; (right_unitor _)
    = (identity (identity_1mor a)).
Proof.
  apply iso_inv_to_right.
  rewrite id_left.
  rewrite <- !assoc.
  apply iso_inv_on_right.

  intermediate_path (identity (identity_1mor a ;1; identity_1mor a)).
    rewrite whisker_right_inv.
    apply iso_inv_on_right.
    apply iso_inv_on_right.
    rewrite id_right.
    simpl.
    unfold whisker_left.
    unfold whisker_right.
    rewrite <- left_unitor_id_is_right_unitor_id.
    rewrite (triangle_axiom (identity_1mor a) (identity_1mor a)).
    rewrite <- left_unitor_id_is_right_unitor_id.
    reflexivity.

  simpl.
  apply pathsinv0.
  rewrite left_unitor_id_is_right_unitor_id.

  apply (iso_inv_after_iso (right_unitor _)).
Defined.

Local Definition identity_triangle2 {C : prebicategory}
  (a : C) :
      (inv (right_unitor (identity_1mor a)))
  ;v; (whisker_left (identity_1mor a) (inv (left_unitor (identity_1mor a))))
  ;v; (associator _ _ _)
  ;v; (whisker_right (right_unitor (identity_1mor a)) (identity_1mor a))
  ;v; (left_unitor _)
    = (identity (identity_1mor a)).
Proof.
  rewrite <- (assoc _ _ (whisker_right _ _)).
  unfold whisker_right at 1.
  simpl.
  rewrite <- triangle_axiom.
  fold (whisker_left (identity_1mor a) (left_unitor_2mor (identity_1mor a))).
  rewrite <- (assoc _ _ (whisker_left _ _)).
  rewrite <- whisker_left_on_comp.

  set (W := iso_after_iso_inv (left_unitor (identity_1mor a))).
  simpl in W.
  rewrite W.
  clear W.

  fold (identity_2mor (identity_1mor a)).
  rewrite whisker_left_id_2mor.
  rewrite id_right.

  rewrite left_unitor_id_is_right_unitor_id.

  set (W := iso_after_iso_inv (right_unitor (identity_1mor a))).
  simpl in W.
  rewrite W.
  reflexivity.
Defined.

Definition identity_adj_int_equivalence {C : prebicategory}
  (a : C) : adj_int_equivalence a a.
Proof.
  exists (identity_1mor a).
  exists (identity_1mor a).
  use tpair.
  - exists (inv (left_unitor (identity_1mor a))).
    exact (right_unitor (identity_1mor a)).
  - split.
    + apply identity_triangle1.
    + apply identity_triangle2.
Defined.

Definition path_to_adj_int_equivalence {C : prebicategory}
  (a b : C) :
  a = b -> adj_int_equivalence a b.
Proof.
  intros p.
  induction p.
  exact (identity_adj_int_equivalence a).
Defined.
