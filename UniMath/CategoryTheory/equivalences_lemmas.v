(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman
january 2013


************************************************************)


(** **********************************************************

Contents :  Definition of adjunction

	    Definition of equivalence of precategories

	    Equivalence of categories yields weak equivalence
            of object types

            A fully faithful and ess. surjective functor induces
            equivalence of precategories, if the source
            is a category.

************************************************************)


Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functor_categories.
Require Import RezkCompletion.equivalences.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
(*Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).*)
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).


Section from_equiv_to_fully_faithful.

Variables A B : precategory.
Variable F : functor A B.
Variable H : equivalence_of_precats F.

Local Definition G : functor B A := right_adjoint (pr1 H).
Local Definition eta := eta_pointwise_iso_from_equivalence H.
Local Definition eps := eps_pointwise_iso_from_equivalence H.

Definition inverse {a b} (g : F a --> F b) : a --> b :=
   eta a ;;  #G g ;; inv_from_iso (eta b).

Lemma inverse_is_inverse_1 a b (f : a --> b) :
    inverse (#F f) = f.
Proof.
  unfold inverse.
  set (H' := nat_trans_ax  (eta_from_left_adjoint (pr1 H))).
  simpl in H'; rewrite <- H'; clear H'; simpl in *.
  rewrite <- assoc.
  transitivity (f ;; identity _ ).
  apply maponpaths.
  set (H':=iso_inv_after_iso _ _ _ (eta b)).
  apply H'.
  rewrite id_right.
  apply idpath.
Qed.

Lemma triangle_id_inverse (a : A):
   iso_inv_from_iso (functor_on_iso _ _ F _ _ (eta a)) = eps (F a).
Proof.
  apply eq_iso. simpl.
  match goal with | [  |- ?x = ?y ] => transitivity (x ;; identity _ )end.
  apply pathsinv0, id_right.
  apply iso_inv_on_right.
  set (H':=triangle_id_left_ad _ _ _ (pr1 H) a).
  apply pathsinv0.
  apply H'.
Qed.

Lemma triangle_id_inverse' (a : A):
   inv_from_iso (functor_on_iso _ _ F _ _ (eta a)) = eps (F a).
Proof.
  apply (base_paths _ _ (triangle_id_inverse a)).
Qed.


Lemma inverse_is_inverse_2 a b (g : F a --> F b) :
    #F (inverse g) = g.
Proof.
  unfold inverse.
  repeat rewrite functor_comp.
  rewrite functor_on_inv_from_iso.
  simpl.
  rewrite triangle_id_inverse'.
  rewrite <- assoc.
  set (H':=nat_trans_ax  (eps_from_left_adjoint (pr1 H))).
  simpl in H'; rewrite H'; clear H'.
  rewrite assoc.
  set (H' := pathsinv0 (triangle_id_left_ad _ _ _ (pr1 H) a)).
  match goal with | [ |- ?f ;; ?g = ?h ] =>
        assert (H'' : identity _ = f) end.
  - simpl in *; apply H'.
  - rewrite <- H''. rewrite id_left. apply idpath.
Qed.


Lemma fully_faithful_from_equivalence : fully_faithful F.
Proof.
  unfold fully_faithful.
  intros a b.
  apply (gradth _ (@inverse a b)).
  - apply inverse_is_inverse_1.
  - apply inverse_is_inverse_2.
Qed.

End from_equiv_to_fully_faithful.
