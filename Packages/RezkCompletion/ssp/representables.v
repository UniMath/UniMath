(** **********************************************************

Benedikt Ahrens



************************************************************)


(** **********************************************************

Contents :  

  - representables


************************************************************)

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.

Require Import RezkCompletion.ssp.gen_precategories.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).
About precategory_morphisms.
Local Notation "'Hom' C" := (precategory_morphisms (C:=C))(at level 2).

Local Notation "f ;; g" := (compose f g)(at level 50).
Local Notation "C '^op'" := (opp_precat C) (at level 3).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

(** ** representable functors *)

(** a natural transformation alpha : F -> G : C -> UUcat is an iso if it is 
    a weak equivalence pointwise, i.e. naturality of the inverse *)

Section nat_iso_if_pointwise_weq.

Variable C : precategory.

Definition Hom_in_data (b : C) : functor_data C^op UUcat := 
  mkfunctor_data C^op UUcat 
             (fun a : C => Hom C a b)
             (fun a a' (f : Hom (C^op) a a') => 
                  fun h : Hom C a b => compose (C:=C) f h).

Lemma is_functor_Hom_in (b : C) : is_functor (Hom_in_data b).
Proof.
  repeat split; simpl.
  - intro a. apply funextfun.
    intro f; unfold identity. simpl.
    apply id_left.
  - intros a c d f g.
    apply funextfun; simpl; intro h;
    simpl. cbv beta.
    apply pathsinv0. apply assoc.
Qed.

Definition Hom_in (b : C) : functor C^op UUcat := 
   tpair _ _ (is_functor_Hom_in b).

Section postcompose_with_nat_trans.

Variables b c : C.
Variable g : Hom C b c.

Definition postcompose_with_is_nat_trans : is_nat_trans (Hom_in b) (Hom_in c)
      (fun a : C => fun h : Hom C a b => h ;; g).
Proof.
  unfold is_nat_trans.
  intros a a' f. simpl.
  apply funextfun.
  intro h.
  apply pathsinv0. 
  apply assoc.
Defined.  

Definition postcompose_nat_trans : nat_trans (Hom_in b) (Hom_in c) := 
   tpair _ _ postcompose_with_is_nat_trans.

End postcompose_with_nat_trans.

Section nat_trans_pointwise_weq.

Variables F G : functor C UUcat.
Variable alpha : nat_trans F G.
Hypothesis alpha_isweq : forall c, isweq (alpha c).

Definition alpha_inv_is_nat_trans : is_nat_trans G F
      (fun c : C => invmap (weqpair _ (alpha_isweq c))).
Proof.
  intros a a' f. 
  apply funextfun; intro x.
  apply (equal_transport_along_weq _ _ (weqpair _ (alpha_isweq _ ))); simpl.
  unfold compose; simpl.
  set (H := homotweqinvweq (weqpair (alpha a') (alpha_isweq a')) ).
  simpl in H. rewrite H.
  set (H' := nat_trans_ax _ _ alpha).
    unfold compose in H'. simpl in H'.
  set (H'':= fun_eq_fun_eq_pointwise _ _ _ _ (H' _ _ f)).
   rewrite H''.
  set (H''' := homotweqinvweq (weqpair (alpha a) (alpha_isweq a)) x).
    simpl in H'''.
  rewrite (H''' ).
  apply idpath.
Qed.
  



































