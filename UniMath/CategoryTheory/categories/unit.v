(** * Category of one element *)
(** ** Contents
- Precategory of one element [unit_Precategory]
- Category of one element [unit_category]
- Functor [functor_to_unit] from a precategory to [unit_precategory]
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.


Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.


(** * Precategory of one object and one arrow *)

Definition unit_precategory_data : precategory_data.
Proof.
  mkpair.
  - exists unit.
    exact (fun _ _ => unit).
  - mkpair; cbn.
    + intro; apply tt.
    + intros; apply tt.
Defined.

Definition unit_precategory_axioms : is_precategory unit_precategory_data.
Proof.
  repeat split; cbn.
  - intros ? ? f. induction f. apply idpath.
  - intros ? ? f. induction f. apply idpath.
Qed.

Definition unit_precategory : precategory := _ ,, unit_precategory_axioms.

Definition unit_Precategory : Precategory.
Proof.
  exists unit_precategory.
  abstract (
      intros a b; induction a; induction b;
      apply isasetunit).
Defined.

Definition is_category_unit : is_category unit_precategory.
Proof.
  split.
  - intros a b. induction a; induction b.
    use (gradth _ _ _ _ ).
    + intro. apply idpath.
    + cbn; intros;
      apply ifcontrthenunitl0.
    + intros; cbn.
      apply eq_iso.
      cbn. apply proofirrelevance.
      apply isapropunit.
  - apply (homset_property unit_Precategory).
Qed.

Definition unit_category : category := _ ,, is_category_unit.


Section functor.

Variable A : precategory.

Definition functor_to_unit_data : functor_data A unit_precategory.
Proof.
  exists (fun _ => tt).
  exact (fun _ _ _ => tt).
Defined.

Definition is_functor_to_unit : is_functor functor_to_unit_data.
Proof.
  split.
  - intro a. apply idpath.
  - intros a b c f g . apply idpath.
Qed.

Definition functor_to_unit : functor A _ := _ ,, is_functor_to_unit.

Lemma functor_to_unit_unique (F : functor A unit_precategory)
  : F = functor_to_unit.
Proof.
  apply functor_eq.
  - apply (homset_property unit_Precategory).
  - use total2_paths_f.
    + apply funextsec. intro. cbn.
      apply proofirrelevance.
      apply isapropunit.
    + do 3 (apply funextsec; intro).
      apply proofirrelevance.
      apply isapropunit.
Qed.

End functor.

(* *)