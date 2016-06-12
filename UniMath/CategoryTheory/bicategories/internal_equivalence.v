Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.bicategories.prebicategory.

Local Notation "a -1-> b" := (homprecat a b)(at level 50).
Local Notation "f ;1; g" := (compose_1mor f g) (at level 50, format "f ;1; g", no associativity).
Local Notation "a -2-> b" := (precategory_morphisms a b)(at level 50).
Local Notation "alpha ;v; beta" := (compose alpha beta) (at level 50, format "alpha ;v; beta", no associativity).
Local Notation "alpha ;h; beta" := (compose_2mor_horizontal alpha beta) (at level 50, format "alpha ;h; beta").

(******************************************************************************)
(* Equivalence in a prebicategory *)

Definition is_internal_equivalence {C : prebicategory} {a b : C}
  (f : a -1-> b)
  := total2 (fun g : b -1-> a => (iso (f ;1; g) (identity_1mor a)) × (iso (g ;1; f) (identity_1mor b))).

Definition internal_equivalence {C : prebicategory}
  (a b : C)
  := total2 (fun f : a -1-> b => is_internal_equivalence f).

Definition identity_equivalence {C : prebicategory}
  (a : C) : internal_equivalence a a.
Proof.
  exists (identity_1mor a).
  exists (identity_1mor a).
  split.
  - exact (left_unitor (identity_1mor a)).
  - exact (left_unitor (identity_1mor a)).
Defined.

Definition id_to_internal_equivalence {C : prebicategory} (a b : C)
  : (a = b) -> internal_equivalence a b.
Proof.
  intros p.
  induction p.
  exact (identity_equivalence a).
Defined.

Definition has_homcats (C : prebicategory)
  := forall a b : C, is_category (a -1-> b).

Definition is_bicategory (C : prebicategory)
  := (has_homcats C) × (forall (a b : C), isweq (id_to_internal_equivalence a b)).

Definition bicategory := total2 (fun C : prebicategory => is_bicategory C).

(***)
(* Being a bicategory is a prop *)

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
