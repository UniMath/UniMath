Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.
Require Import RezkCompletion.yoneda.
(*Require Import RezkCompletion.functors_transformations.*)
Require Import RezkCompletion.limits.aux_lemmas_HoTT.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).
(*Local Notation "# F" := (functor_on_morphisms F)(at level 3).*)

Section bla.

Variable C : precategory.

Lemma C_op_op_eq_C_pr1_pr1_pr1 : pr1 (pr1 (pr1 (C^op^op))) == pr1 (pr1 (pr1 C)).
Proof.
  apply idpath.
Defined.

Lemma C_op_op_eq_C_pr1_pr1 : pr1 (pr1 (C^op^op)) == pr1 (pr1 C).
Proof.
  apply (total2_paths C_op_op_eq_C_pr1_pr1_pr1).
(*  rewrite transportf_idpath. *)
  simpl.
  apply funextfunax.
  intro x .
  apply funextfunax.
  intro y.
  apply idpath.
Defined.

Lemma C_op_op_eq_C_pr1 : pr1 (C^op^op) == pr1 C.
Proof.
  apply (total2_paths C_op_op_eq_C_pr1_pr1).
  unfold C_op_op_eq_C_pr1_pr1.
  rewrite transportf_dirprod.
  destruct C as [Cdata Cax].
  simpl.

Lemma

Lemma C_op_op_eq_C : C^op^op == C.

