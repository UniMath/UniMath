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

Definition isaprop_has_homcats { C : prebicategory }
  : isaprop (has_homcats C).
Proof.
  apply impred.
  intro a.
  apply impred.
  intro b.
  apply (isaprop_is_category (a -1-> b)).
Qed.

Definition isaprop_is_bicategory { C : prebicategory }
  : isaprop (is_bicategory C).
Proof.
  apply isapropdirprod.
  - exact isaprop_has_homcats.
  - apply impred.
    intros a.
    apply impred.
    intros b.
    apply isapropisweq.
Qed.


(******************************************************************************)
(* Equivalence in a prebicategory via precomposition *)

Definition precomp_with_1mor {C : prebicategory_data} {a b : C} (f : a -1-> b) {c : C}
  : functor (b -1-> c) (a -1-> c)
  := functor_fix_fst_arg _ _ _ (compose_functor a b c) f.

Definition precomp_with_identity_is_identity_trans {C : prebicategory} (a : C)
  : forall b : C, nat_trans (precomp_with_1mor (identity_1mor a)) (functor_identity (a -1-> b)).
Proof.
  intros b.
  use tpair.
  - exact left_unitor.
  - exact (pr2 (pr1 (pr2 (pr2 (pr1 C))) a b)).
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
