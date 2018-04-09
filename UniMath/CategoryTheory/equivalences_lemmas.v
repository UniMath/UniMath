(** ** Lemmas about equivalences of categories

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)

Revised by: Marco Maggesi (November 2017), Langston Barrett (April 2018)

*)


(** ** Contents :

 - Fully faithful functor from an equivalence
 - Functor from an equivalence is essentially surjective
 - Composition of equivalences
*)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.


(** ** Fully faithful functor from an equivalence *)

Section from_equiv_to_fully_faithful.

Local Open Scope cat.

Variables A B : precategory.
Variable F : A ⟶ B.
Variable H : adj_equivalence_of_precats F.

Local Definition G : B ⟶ A := adj_equivalence_inv H.

Local Definition eta : ∏ a : A, iso a (G (F a))
  := unit_pointwise_iso_from_adj_equivalence H.

Local Definition eps : ∏ b : B, iso (F (G b)) b
  := counit_pointwise_iso_from_adj_equivalence H.

Definition inverse {a b} (g : B⟦F a, F b⟧) : A⟦a, b⟧
  := eta a · #G g · inv_from_iso (eta b).

Lemma inverse_is_inverse_1 a b (f : a --> b) : inverse (#F f) = f.
Proof.
  unfold inverse.
  set (H' := nat_trans_ax  (adjunit (pr1 H))).
  simpl in H'; rewrite <- H'; clear H'; simpl in *.
  rewrite <- assoc.
  intermediate_path (f · identity _).
  apply maponpaths.
  set (H' := iso_inv_after_iso (eta b)).
  apply H'.
  rewrite id_right.
  apply idpath.
Qed.

Lemma triangle_id_inverse (a : A)
  : iso_inv_from_iso (functor_on_iso F (eta a)) = eps (F a).
Proof.
  apply eq_iso. simpl.
  match goal with | [ |- ?x = ?y ] => transitivity (x · identity _) end.
  apply pathsinv0, id_right.
  apply iso_inv_on_right.
  set (H' := triangle_id_left_ad (pr2 (pr1 H)) a).
  apply pathsinv0.
  apply H'.
Qed.

Lemma triangle_id_inverse' (a : A)
  : inv_from_iso (functor_on_iso F (eta a)) = eps (F a).
Proof.
  apply (base_paths _ _ (triangle_id_inverse a)).
Qed.

Lemma inverse_is_inverse_2 a b (g : F a --> F b) : #F (inverse g) = g.
Proof.
  unfold inverse.
  repeat rewrite functor_comp.
  rewrite functor_on_inv_from_iso.
  simpl.
  rewrite triangle_id_inverse'.
  rewrite <- assoc.
  set (H' := nat_trans_ax  (adjcounit (pr1 H))).
  simpl in H'; rewrite H'; clear H'.
  rewrite assoc.
  set (H' := pathsinv0 (triangle_id_left_ad (pr2 (pr1 H)) a)).
  match goal with [|- ?f · ?g = ?h] => assert (H'' : identity _ = f) end.
  - simpl in *; apply H'.
  - rewrite <- H''. rewrite id_left. apply idpath.
Qed.

Lemma fully_faithful_from_equivalence : fully_faithful F.
Proof.
  unfold fully_faithful. intros a b.
  apply (isweq_iso _ (@inverse a b)).
  - apply inverse_is_inverse_1.
  - apply inverse_is_inverse_2.
Qed.

(** ** Functor from an equivalence is essentially surjective *)

Lemma functor_from_equivalence_is_essentially_surjective :
  essentially_surjective F.
Proof.
  unfold essentially_surjective.
  intros b; apply hinhpr.
  exists (G b).
  apply counit_pointwise_iso_from_adj_equivalence.
Defined.

End from_equiv_to_fully_faithful.

(** ** Composition of equivalences *)

(** There is probably a more general way to do this. We assume
    that C is univalent, and use the fact that a fully faithful, essentially
    surjective functor out of a univalent category is an equivalence. *)

Lemma compose_equivalences_univalent {C : univalent_category} (D E : precategory)
      (F : functor C D) (FE : adj_equivalence_of_precats F)
      (G : functor D E) (GE : adj_equivalence_of_precats G) :
  adj_equivalence_of_precats (functor_composite F G).
Proof.
  use rad_equivalence_of_precats.
  - apply univalent_category_is_univalent.
  - apply comp_ff_is_ff; apply fully_faithful_from_equivalence; assumption.
  - apply comp_essentially_surjective;
      apply functor_from_equivalence_is_essentially_surjective;
      assumption.
Defined.
