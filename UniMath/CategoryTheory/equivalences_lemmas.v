(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman
january 2013

Revised by Marco Maggesi, november 2017

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


Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.

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
  match goal with [|- ?x = ?y] => transitivity (x · identity _) end.
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
  apply (gradth _ (@inverse a b)).
  - apply inverse_is_inverse_1.
  - apply inverse_is_inverse_2.
Qed.

End from_equiv_to_fully_faithful.
