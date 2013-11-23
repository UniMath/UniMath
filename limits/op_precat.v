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

Section pr1.

Variable C : precategory_ob_mor.

Lemma opp_opp_precat_ob_mor : pr1 (opp_precat_ob_mor (opp_precat_ob_mor C)) == pr1 C.
Proof.
  apply idpath.
Defined.

Lemma opp_opp_precat_ob_mor' : opp_precat_ob_mor (opp_precat_ob_mor C) == C.
Proof.
  apply (total2_paths opp_opp_precat_ob_mor).
  apply funextfunax.
  intro x.
  apply funextfunax.
  intro y.
  apply idpath.
Defined.

End pr1.


Section pr2.
Variable C : precategory_data.

Lemma helper : pr1 (opp_precat_data (opp_precat_data C)) == pr1 C.
Proof.
    change (pr1 (opp_precat_data (opp_precat_data C))) with
       (opp_precat_ob_mor (opp_precat_ob_mor (pr1 C))).
  apply opp_opp_precat_ob_mor'.
Defined.

Lemma bla : opp_precat_data (opp_precat_data C) == C.
Proof.
  apply (total2_paths helper).
(*  set (H:= opp_opp_precat_ob_mor' (pr1 C)).
  change (opp_precat_ob_mor (opp_precat_ob_mor (pr1 C))) with
       (pr1 (opp_precat_data (opp_precat_data C))) in H.
  apply (total2_paths H).
  unfold H. clear H.
*)
  unfold opp_precat_data.
  simpl.
  Check transportf_dirprod.
  set (H := transportf_dirprod precategory_ob_mor).
  set (H' := H (fun x => forall c : x, c --> c)
               (fun x => forall a b c : x, a --> b -> b --> c -> a --> c)).
  set (H'':= H' (opp_precat_data (opp_precat_data C)) C helper).
  simpl in *.
  
  rewrite H''.
  
  simpl in H'.
  rewrite H'.
  unfold helper.
  unfold opp_opp_precat_ob_mor'.
  Search (transportf _ (total2_paths)).
  simpl.
  rewrite (transportf_dirprod).
  destruct C as [Cobmor Cidcomp].
  simpl.
  Check transportf_dirprod.
  (
  rewrite (transportf_dirprod).
  destruct Cidcomp as [Cid Ccomp].
  simpl in *.
  rewrite (transportf_dirprod).
  unfold opp_opp_precat_ob_mor'.
  simpl.
  simpl in H.
  simpl.
  apply (total2_paths (opp_opp_precat_ob_mor' _ )).


  refine (total2_paths _ _ ).
  unfold precategory_ob_mor in C.

(*

unfold opp_precat_ob_mor. simpl.
  simpl.

*)

  apply (total2_paths (idpath _ )).
  apply idpath.


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

