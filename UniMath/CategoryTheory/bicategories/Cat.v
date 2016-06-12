Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.bicategories.prebicategory.

(******************************************************************************)
(* Lemmas for use in PreCat and Cat *)

Definition Catlike_associator ( a b c d : precategory ) (hsB : has_homsets b) (hsC : has_homsets c) (hsD : has_homsets d) :
   nat_trans
     (functor_composite
        (product_functor
           (functor_identity (functor_precategory a b hsB))
           (functorial_composition b c d hsC hsD))
        (functorial_composition a b d hsB hsD))
     (functor_composite
        (product_precategory_assoc (functor_precategory a b hsB)
           (functor_precategory b c hsC)
           (functor_precategory c d hsD))
        (functor_composite
           (product_functor
              (functorial_composition a b c hsB hsC)
              (functor_identity (functor_precategory c d hsD)))
           (functorial_composition a c d hsC hsD))).
Proof.
  use tpair.
  - intros x. (* Step 1: Give the components of the natural transformation *)
    simpl.
    exists (fun x => identity _).
    induction x as [x1 [x2 x3]].
    unfold is_nat_trans.
    intros oba oba' f.
    simpl.
    simpl in d, x1, x2, x3.
    refine (id_right d _ _ _ @ !(id_left d _ _ _)).
  - intros [x1 [x2 x3]].
    simpl in x1, x2, x3.
    intros [y1 [y2 y3]].
    intros [f1 [f2 f3]].
    apply nat_trans_eq. exact hsD.
    intros oba.
    simpl.
    simpl in d.
    rewrite (id_right d _ _ _).
    rewrite (id_left d  _ _ _).
    rewrite functor_comp.
    rewrite (assoc d).
    reflexivity.
Defined.

Definition Catlike_left_unitor (a b : precategory) (hsA : has_homsets a) (hsB : has_homsets b) :
  nat_trans
     (functor_composite
        (pair_functor
           (functor_composite (unit_functor (functor_precategory a b hsB))
              (ob_as_functor (C:= (functor_precategory a a hsA)) (functor_identity a)))
           (functor_identity (functor_precategory a b hsB)))
        (functorial_composition a a b hsA hsB))
     (functor_identity (functor_precategory a b hsB)).
Proof.
  unfold nat_trans.
  use tpair.
  - intros x.
    exists (fun x => identity _).
    intros oba oba' f.
    simpl.
    simpl in b.
    exact (id_right b _ _ _ @ !(id_left b _ _ _)).
  - intros x x' f.
    apply nat_trans_eq. exact hsB.
    intros oba.
    simpl.
    simpl in x, x'.
    simpl in a, b.
    rewrite (id_right b _ _ _).
    rewrite (id_left b _ _ _).
    rewrite functor_id.
    rewrite (id_right b _ _ _).
    reflexivity.
Defined.

Definition Catlike_right_unitor (a b : precategory) (hsB : has_homsets b) :
  nat_trans
     (functor_composite
        (pair_functor (functor_identity (functor_precategory a b hsB))
           (functor_composite (unit_functor (functor_precategory a b hsB))
              (ob_as_functor (C:= (functor_precategory b b hsB)) (functor_identity b))))
        (functorial_composition a b b hsB hsB)) (functor_identity (functor_precategory a b hsB)).
Proof.
  unfold nat_trans.
  use tpair.
  - intros x.
    exists (fun x => identity _).
    intros oba oba' f.
    simpl.
    simpl in b.
    exact (id_right b _ _ _ @ !(id_left b _ _ _)).
  - intros x x' f.
    apply nat_trans_eq. exact hsB.
    intros oba.
    simpl.
    simpl in x, x'.
    simpl in a, b.
    rewrite (id_right b _ _ _).
    rewrite (id_left b _ _ _).
    reflexivity.
Defined.

(******************************************************************************)
(* The prebicategory of precategories *)

Definition PreCat_1mor_2mor : prebicategory_ob_1mor_2mor.
Proof.
  exists hs_precategory.
  intros a b.
  exact (functor_precategory a b (hs_precategory_has_homsets b)).
Defined.

Definition PreCat_id_comp : prebicategory_id_comp.
Proof.
  exists PreCat_1mor_2mor.
  split.
  - simpl.
    exact functor_identity.
  - simpl.
    intros a b c.
    exact (functorial_composition a b c (hs_precategory_has_homsets b) (hs_precategory_has_homsets c)).
Defined.

Definition PreCat_data : prebicategory_data.
Proof.
  unfold prebicategory_data.
  exists PreCat_id_comp.
  repeat split.
  - intros.
    simpl in a,b,c,d.
    exact (Catlike_associator a b c d (hs_precategory_has_homsets b)
                                      (hs_precategory_has_homsets c)
                                      (hs_precategory_has_homsets d)).
  - intros.
    simpl in a, b.
    exact (Catlike_left_unitor a b (hs_precategory_has_homsets a)
                               (hs_precategory_has_homsets b)).
  - intros.
    simpl in a, b.
    exact (Catlike_right_unitor a b (hs_precategory_has_homsets b)).
Defined.

Definition PreCat_has_2mor_set : has_2mor_sets PreCat_data.
Proof.
  unfold has_2mor_sets.
  intros a b f g.
  apply isaset_nat_trans.
  exact (hs_precategory_has_homsets b).
Defined.

Definition PreCat_associator_and_unitors_are_iso : associator_and_unitors_are_iso PreCat_data.
Proof.
  unfold associator_and_unitors_are_iso.
  repeat split.
  - intros a b c d f g h.
    unfold associator.
    apply functor_iso_if_pointwise_iso.
    intros oba.
    simpl.
    unfold is_isomorphism. (* What is even the point of this *)
    simpl in d.
    apply (identity_is_iso d).
  - intros a b f.
    unfold left_unitor.
    apply functor_iso_if_pointwise_iso.
    intros oba.
    simpl.
    unfold is_isomorphism.
    simpl in b.
    apply (identity_is_iso b).
  - intros a b f.
    unfold right_unitor.
    apply functor_iso_if_pointwise_iso.
    intros oba.
    simpl.
    unfold is_isomorphism.
    simpl in b.
    apply (identity_is_iso b).
Defined.

Definition PreCat_coherence : prebicategory_coherence PreCat_data.
Proof.
  unfold prebicategory_coherence.
  split.
  - intros a b c d e k h g f.
    unfold pentagon_axiom.
    apply nat_trans_eq. exact (hs_precategory_has_homsets e).
    intros x.
    simpl.
    simpl in e.
    repeat rewrite functor_id.
    repeat rewrite (id_left e _ _ _).
    reflexivity.
  - intros a b c f g.
    unfold triangle_axiom.
    apply nat_trans_eq. exact (hs_precategory_has_homsets c).
    intros x.
    simpl.
    simpl in c.
    repeat rewrite functor_id.
    repeat rewrite (id_left c _ _ _).
    reflexivity.
Defined.

Definition PreCat : prebicategory.
Proof.
  use tpair.
  exact PreCat_data.
  unfold is_prebicategory.
  split.
  exact PreCat_has_2mor_set.
  split.
  exact PreCat_associator_and_unitors_are_iso.
  exact PreCat_coherence.
Defined.

(******************************************************************************)
(* The bicategory of categories *)

Definition Cat_1mor_2mor : prebicategory_ob_1mor_2mor.
Proof.
  exists category.
  intros a b.
  exact (functor_precategory a b (category_has_homsets b)).
Defined.

Definition Cat_id_comp : prebicategory_id_comp.
Proof.
  exists Cat_1mor_2mor.
  split.
  - simpl.
    exact functor_identity.
  - simpl.
    intros a b c.
    exact (functorial_composition a b c (category_has_homsets b) (category_has_homsets c)).
Defined.

Definition Cat_data : prebicategory_data.
Proof.
  unfold prebicategory_data.
  exists Cat_id_comp.
  repeat split.
  - intros.
    simpl in a,b,c,d.
    exact (Catlike_associator a b c d (category_has_homsets b)
                                      (category_has_homsets c)
                                      (category_has_homsets d)).
  - intros.
    simpl in a, b.
    exact (Catlike_left_unitor a b (category_has_homsets a)
                                   (category_has_homsets b)).
  - intros.
    simpl in a, b.
    exact (Catlike_right_unitor a b (category_has_homsets b)).
Defined.

Definition Cat_has_2mor_set : has_2mor_sets Cat_data.
Proof.
  unfold has_2mor_sets.
  intros a b f g.
  apply isaset_nat_trans.
  exact (category_has_homsets b).
Defined.

Definition Cat_associator_and_unitors_are_iso : associator_and_unitors_are_iso Cat_data.
Proof.
  unfold associator_and_unitors_are_iso.
  repeat split.
  - intros a b c d f g h.
    unfold associator.
    apply functor_iso_if_pointwise_iso.
    intros oba.
    simpl.
    unfold is_isomorphism. (* What is even the point of this *)
    simpl in d.
    apply (identity_is_iso d).
  - intros a b f.
    unfold left_unitor.
    apply functor_iso_if_pointwise_iso.
    intros oba.
    simpl.
    unfold is_isomorphism.
    simpl in b.
    apply (identity_is_iso b).
  - intros a b f.
    unfold right_unitor.
    apply functor_iso_if_pointwise_iso.
    intros oba.
    simpl.
    unfold is_isomorphism.
    simpl in b.
    apply (identity_is_iso b).
Defined.

Definition Cat_coherence : prebicategory_coherence Cat_data.
Proof.
  unfold prebicategory_coherence.
  split.
  - intros a b c d e k h g f.
    unfold pentagon_axiom.
    apply nat_trans_eq. exact (category_has_homsets e).
    intros x.
    simpl.
    simpl in e.
    repeat rewrite functor_id.
    repeat rewrite (id_left e _ _ _).
    reflexivity.
  - intros a b c f g.
    unfold triangle_axiom.
    apply nat_trans_eq. exact (category_has_homsets c).
    intros x.
    simpl.
    simpl in c.
    repeat rewrite functor_id.
    repeat rewrite (id_left c _ _ _).
    reflexivity.
Defined.

Definition Cat_prebicategory : prebicategory.
Proof.
  use tpair.
  exact Cat_data.
  unfold is_prebicategory.
  split.
  exact Cat_has_2mor_set.
  split.
  exact Cat_associator_and_unitors_are_iso.
  exact Cat_coherence.
Defined.

Definition Cat_has_homcats : has_homcats Cat_prebicategory.
Proof.
  unfold has_homcats.
  intros a b.
  apply is_category_functor_category.
Defined.

Definition Cat_is_lt2saturated (a b : Cat_prebicategory)
  : isweq (id_to_internal_equivalence a b).
Proof.

Admitted.

Definition Cat : bicategory.
Proof.
  exists Cat_prebicategory.
  split.
  - exact Cat_has_homcats.
  - exact Cat_is_lt2saturated.
Defined.
