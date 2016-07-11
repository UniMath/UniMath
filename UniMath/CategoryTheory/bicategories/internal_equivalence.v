Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductPrecategory.
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
  := total2 (fun g : b -1-> a => (iso (identity_1mor a) (f ;1; g)) × (iso (g ;1; f) (identity_1mor b))).

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
  rewrite whisker_right_inv.
  rewrite <- (assoc _ _ _ _ _ _ (inv_from_iso _)).
  simpl.

  set (W := iso_inv_of_iso_comp _ _ _ _ (associator
                                                 (identity_1mor a)
                                                 (identity_1mor a)
                                                 (identity_1mor a))
                                        (whisker_right_iso
                                                 (left_unitor
                                                 (identity_1mor a))
                                                 (identity_1mor a))).
  set (W' := maponpaths pr1 W).
  simpl in W'.
  unfold inv.
  rewrite <- W'.
  clear W W'.

  assert (W : (associator (identity_1mor a) (identity_1mor a) (identity_1mor a)
           ;i; whisker_right_iso (left_unitor (identity_1mor a)) (identity_1mor a)
             = whisker_left_iso (identity_1mor a) (left_unitor (identity_1mor a)))).
    apply eq_iso.
    simpl.
    apply pathsinv0.
    unfold whisker_left.
    unfold whisker_right.
    eapply pathscomp0.
    apply (triangle_axiom (identity_1mor a) (identity_1mor a)).
    rewrite left_unitor_id_is_right_unitor_id.
    reflexivity.
  rewrite W.
  clear W.

  rewrite <- left_unitor_id_is_right_unitor_id.
  rewrite <- whisker_left_inv.
  rewrite <- (assoc _ _ _ _ _ _ _ (whisker_left _ (left_unitor_2mor _))).
  rewrite <- whisker_left_on_comp.

  simpl.

  set (W := iso_after_iso_inv (left_unitor (identity_1mor a))).
  simpl in W.
  rewrite W.
  fold (identity_2mor (identity_1mor a)).
  rewrite whisker_left_id_2mor.
  rewrite id_right.
  rewrite W.
  reflexivity.
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
  rewrite <- (assoc _ _ _ _ _ _ (associator _ _ _)).
  unfold whisker_right at 1.
  simpl.
  rewrite <- triangle_axiom.
  fold (whisker_left (identity_1mor a) (left_unitor_2mor (identity_1mor a))).
  rewrite <- (assoc _ _ _ _ _ _  (whisker_left (identity_1mor a) (inv_from_iso _))).
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

Lemma precomp_with_identity_is_identity {C : prebicategory} (hc : has_homcats C) (a : C)
  : forall b : C, precomp_with_1mor (identity_1mor a) = functor_identity (a -1-> b).
Proof.
  intros b.
  set (abhs := pr2 (hc a b)).
  simpl in abhs.
  apply (functor_eq_from_functor_iso abhs (hc a b)).
  apply (functor_iso_from_pointwise_iso _ _ _ _ _ (precomp_with_identity_is_identity_trans a b)).
  exact (pr1 (pr2 (pr1 (pr2 (pr2 C)))) a b).
Defined.

Definition is_precomp_equiv {C : prebicategory_data} {a b : C} (f : a -1-> b) :=
  forall (c : C), adj_equivalence_of_precats (precomp_with_1mor f (c:=c)).

Definition precomp_equiv {C: prebicategory_data}(a b : C) := total2 (fun f : a -1-> b => is_precomp_equiv f).

(* TODO: This does not need homcategories  *)
(* Pending a proof that a functor naturally isomorphic to a lift
   adjoint is a left adjoint *)
Definition identity_precomp_equiv {C : prebicategory} (hc : has_homcats C) (a : C) :
  precomp_equiv a a.
Proof.
  unfold precomp_equiv.
  use tpair.
  - exact (identity_1mor a).
  - simpl.
    unfold is_precomp_equiv.
    intros b.
    rewrite (precomp_with_identity_is_identity hc a b).
    apply identity_functor_is_adj_equivalence.
Defined.

Definition idto_precomp_equiv {C : prebicategory} {a b : C} (hc : has_homcats C):
      a = b -> precomp_equiv a b.
Proof.
  intro H.
  destruct H.
  exact (identity_precomp_equiv hc a).
Defined.
