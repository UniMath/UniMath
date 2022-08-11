(** * Fully faithful functors and equivalences

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)
Revised by: Marco Maggesi (November 2017), Langston Barrett (April 2018)

*)


(** ** Contents :

 - Fully faithful functor from an equivalence
 - Functor from an equivalence is essentially surjective
 - Fully faithful essentially surjective functors preserve all [hProp]s on
   hom-types
*)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import UniMath.CategoryTheory.Equivalences.Core.

Local Open Scope cat.

(** ** Fully faithful functor from an equivalence *)

Section from_equiv_to_fully_faithful.

Variables A B : category.
Variable F : A ⟶ B.
Variable H : adj_equivalence_of_cats F.

Local Definition G : B ⟶ A := adj_equivalence_inv H.

Local Definition eta : ∏ a : A, z_iso a (G (F a))
  := unit_pointwise_z_iso_from_adj_equivalence H.

Local Definition eps : ∏ b : B, z_iso (F (G b)) b
  := counit_pointwise_z_iso_from_adj_equivalence H.

Definition inverse {a b} (g : B⟦F a, F b⟧) : A⟦a, b⟧
  := eta a · #G g · inv_from_z_iso (eta b).

Lemma inverse_is_inverse_1 a b (f : a --> b) : inverse (#F f) = f.
Proof.
  unfold inverse.
  set (H' := nat_trans_ax  (adjunit (pr1 H))).
  simpl in H'; rewrite <- H'; clear H'; simpl in *.
  rewrite <- assoc.
  intermediate_path (f · identity _).
  apply maponpaths.
  set (H' := z_iso_inv_after_z_iso (eta b)).
  apply H'.
  rewrite id_right.
  apply idpath.
Qed.

Lemma triangle_id_inverse (a : A)
  : z_iso_inv_from_z_iso (functor_on_z_iso F (eta a)) = eps (F a).
Proof.
  apply z_iso_eq. simpl.
  match goal with | [ |- ?x = ?y ] => transitivity (x · identity _) end.
  apply pathsinv0, id_right.
  apply z_iso_inv_on_right.
  set (H' := triangle_id_left_ad (pr2 (pr1 H)) a).
  apply pathsinv0.
  apply H'.
Qed.

Lemma triangle_id_inverse' (a : A)
  : inv_from_z_iso (functor_on_z_iso F (eta a)) = eps (F a).
Proof.
  apply (base_paths _ _ (triangle_id_inverse a)).
Qed.

Lemma inverse_is_inverse_2 a b (g : F a --> F b) : #F (inverse g) = g.
Proof.
  unfold inverse.
  repeat rewrite functor_comp.
  rewrite functor_on_inv_from_z_iso.
  simpl.
  rewrite triangle_id_inverse'.
  rewrite <- assoc.
  set (H' := nat_trans_ax (adjcounit (pr1 H))).
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
  apply counit_pointwise_z_iso_from_adj_equivalence.
Defined.

End from_equiv_to_fully_faithful.

(** ** Fully faithful essentially surjective functors preserve all [hProp]s on hom-types *)

Section HomtypeProperties.

  Context {C D : category} (F : functor C D).

  (** For every hom-type in D, there merely exists a hom-type in C to which
      it is equivalent. For split essentially surjective functors, this
      could be strengthened to an untruncated version. *)
  (* TODO: better name? *)
  Lemma ff_es_homtype_weq (FFF : fully_faithful F) (FES : essentially_surjective F) :
    (∏ d d' : ob D, ∥ ∑ c c' : ob C,  C⟦c, c'⟧ ≃ D⟦d, d'⟧ ∥).
  Proof.
    intros d d'.

    (** Obtain the c, c' for which F c ≅ d and F c' ≅ d'. *)
    apply (squash_to_prop (FES d)); [apply isapropishinh|]; intros c.
    apply (squash_to_prop (FES d')); [apply isapropishinh|]; intros c'.
    apply hinhpr.
    exists (pr1 c), (pr1 c').

    (** Homsets between isomorphic objects are equivalent. *)
    intermediate_weq (D ⟦ F (pr1 c), F (pr1 c') ⟧).
    - apply weq_from_fully_faithful; assumption.
    - intermediate_weq (D ⟦ F (pr1 c), d' ⟧).
      + eapply make_weq.
        apply z_iso_comp_left_isweq.
        Unshelve.
        exact (pr2 c').
      + eapply make_weq.
        apply z_iso_comp_right_weq.
        Unshelve.
        exact (z_iso_inv_from_is_z_iso (pr1 (pr2 c)) (pr2 (pr2 c))).
  Defined.

  Lemma ff_es_homtype_property (FFF : fully_faithful F)
        (FES : essentially_surjective F) (P : UU → hProp)
        (prop : ∏ a b : ob C, P (C⟦a, b⟧)) : (∏ a b : ob D, P (D⟦a, b⟧)).
  Proof.
    intros a b.
    apply (squash_to_prop (ff_es_homtype_weq FFF FES a b));
      [apply propproperty|]; intros H.
    use transportf.
    - exact (P (C⟦(pr1 H), (pr1 (pr2 H))⟧)).
    - apply maponpaths.
      apply weqtopaths.
      exact (pr2 (pr2 H)).
    - apply prop.
  Defined.

  (** Corollary: Equivalences preserve [hProp]s on hom-types. *)
  Corollary equivalence_homtype_property (E : adj_equivalence_of_cats F)
            (P : UU → hProp) (prop : ∏ a b : ob C, P (C⟦a, b⟧)) :
    (∏ a b : ob D, P (D⟦a, b⟧)).
  Proof.
    apply ff_es_homtype_property.
    - apply fully_faithful_from_equivalence; assumption.
    - apply functor_from_equivalence_is_essentially_surjective; assumption.
    - assumption.
  Defined.

  (** Corollary: Fully faithful essentially surjective functors preserve the
      property of having hom-sets. *)
  Corollary ff_es_preserves_homsets (FFF : fully_faithful F)
            (FES : essentially_surjective F) (hsC : has_homsets C) : has_homsets D.
  Proof.
    refine (ff_es_homtype_property FFF FES
              (λ t, make_hProp _ (isapropisaset t)) _).
    apply hsC.
  Defined.

  (** Other applications: ff/es functors preserve univalence, being a groupoid,
      merely having any type of (co)limits, etc. *)

End HomtypeProperties.
