(** **********************************************************

Mitchell Riley

June 2016

I am very grateful to Peter LeFanu Lumsdaine, whose unreleased
bicategories code strongly influenced the proofs in this file.

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.equivalences.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.bicategories.prebicategory.

(******************************************************************************)
(* Lemmas for use in PreCat and Cat *)

Definition Catlike_associator ( a b c d : precategory )
   (hsB : has_homsets b) (hsC : has_homsets c) (hsD : has_homsets d) :
   nat_trans
     (functor_composite
        (pair_functor
           (functor_identity (functor_precategory a b hsB))
           (functorial_composition b c d hsC hsD))
        (functorial_composition a b d hsB hsD))
     (functor_composite
        (precategory_binproduct_assoc (functor_precategory a b hsB)
           (functor_precategory b c hsC)
           (functor_precategory c d hsD))
        (functor_composite
           (pair_functor
              (functorial_composition a b c hsB hsC)
              (functor_identity (functor_precategory c d hsD)))
           (functorial_composition a c d hsC hsD))).
Proof.
  use tpair.
  - (* Step 1: Give the components of the natural transformation *)
    (* I.e., for every triple of functors
         F : a -> b
         G : b -> c
         H : c -> d,
       a natural transformation F (G H) -> (F G) H *)

    intros x.
    simpl.

    (* The component at x is just the identity, because composition of
       functions is associative for free. *)
    exists (λ x, identity _).

    (* Which is natural. *)
    intros oba oba' f.
    use (id_right _ @ !(id_left _)).

  - (* Step 2: Show the above is natural, so given
       f : F -> F', g : G -> G', h : H -> H', *)
    intros [F  [G  H]].
    intros [F' [G' H']].
    intros [f  [g  h]].
    (* Verify that
       (f, (g, h)) ∘ (assoc F' G' H') = (assoc F G H) ∘ ((f, g), h))
       as natural transformations. *)

    (* To show two natural transformations are equal, suffices to
       check components *)
    apply nat_trans_eq. exact hsD.
    intros oba.

    simpl.

    (* Now assoc is just identity *)
    rewrite id_right.
    rewrite id_left.

    (* And the order we do f, g, h doesn't matter *)
    rewrite functor_comp.
    rewrite assoc.
    reflexivity.
Defined.

Definition Catlike_associator_is_iso ( a b c d : precategory )
  (hsB : has_homsets b) (hsC : has_homsets c) (hsD : has_homsets d) :
  forall f g h, is_iso (Catlike_associator a b c d hsB hsC hsD
                    (precatbinprodpair f (precatbinprodpair g h))).
Proof.
  intros f g h.
  (* The components are all the identity, so this is easy *)
  apply functor_iso_if_pointwise_iso.
  intros oba.
  apply (identity_is_iso d).
Defined.

Definition Catlike_left_unitor (a b : precategory) (hsA : has_homsets a) (hsB : has_homsets b) :
  nat_trans
     (functor_composite
        (bindelta_pair_functor
           (functor_composite (unit_functor (functor_precategory a b hsB))
              (constant_functor unit_precategory (functor_precategory a a hsA) (functor_identity a)))
           (functor_identity (functor_precategory a b hsB)))
        (functorial_composition a a b hsA hsB))
     (functor_identity (functor_precategory a b hsB)).
Proof.
  use tpair.
  - (* Step 1: Give components.
       Again identity works, as function composition is unital for free *)
    intros x.
    exists (λ x, identity _).
    intros oba oba' f.
    exact (id_right _ @ !(id_left _)).

  - (* Step 2: Show the above is natural, so given f : F -> F' *)
    intros F F' f.
    (* Verify that
       (f, id) ∘ (left_unitor F') = (left_unitor F) ∘ f
       as natural transformations. *)

    (* Again just check components *)
    apply nat_trans_eq. exact hsB.
    intros oba.

    simpl.
    rewrite id_right.
    rewrite id_left.
    rewrite functor_id.
    rewrite id_right.
    reflexivity.
Defined.

Definition Catlike_left_unitor_is_iso (a b : precategory)
  (hsA : has_homsets a) (hsB : has_homsets b) :
  forall f, is_iso (Catlike_left_unitor a b hsA hsB f).
Proof.
  intros f.
  apply functor_iso_if_pointwise_iso.
  intros oba.
  apply (identity_is_iso b).
Defined.

Definition Catlike_right_unitor (a b : precategory) (hsB : has_homsets b) :
  nat_trans
     (functor_composite
        (bindelta_pair_functor (functor_identity (functor_precategory a b hsB))
           (functor_composite (unit_functor (functor_precategory a b hsB))
              (constant_functor unit_precategory (functor_precategory b b hsB) (functor_identity b))))
        (functorial_composition a b b hsB hsB))
     (functor_identity (functor_precategory a b hsB)).
Proof.
  use tpair. (* Same as above *)
  - intros x.
    exists (λ x, identity _).
    intros oba oba' f.
    exact (id_right _ @ !(id_left _)).

  - intros F F' f.
    apply nat_trans_eq. exact hsB.
    intros oba.

    simpl.
    rewrite (id_right _).
    rewrite (id_left _).
    reflexivity.
Defined.

Definition Catlike_right_unitor_is_iso (a b : precategory) (hsB : has_homsets b) :
  forall f, is_iso (Catlike_right_unitor a b hsB f).
Proof.
  intros f.
  apply functor_iso_if_pointwise_iso.
  intros oba.
  apply (identity_is_iso b).
Defined.

(* What a mess! *)
Definition Catlike_pentagon ( a b c d e : precategory )
  (hsB : has_homsets b) (hsC : has_homsets c) (hsD : has_homsets d)
  (hsE : has_homsets e) :
  forall k h g f,
  (Catlike_associator a b c e _ _ _)
     (precatbinprodpair k
        (precatbinprodpair h ((functorial_composition c d e hsD _) (dirprodpair g f)))) ·
   (Catlike_associator a c d e _ _ _)
     (precatbinprodpair ((functorial_composition a b c hsB hsC) (dirprodpair k h))
        (precatbinprodpair g f))
  = (functor_on_morphisms (functorial_composition a b e hsB hsE)
      (precatbinprodmor (identity k)
         ((Catlike_associator b c d e _ _ _) (precatbinprodpair h (precatbinprodpair g f)))) ·
    (Catlike_associator a b d e _ _ _)
      (precatbinprodpair k
         (precatbinprodpair ((functorial_composition b c d _ _) (dirprodpair h g)) f))) ·
   functor_on_morphisms (functorial_composition a d e _ _)
     (precatbinprodmor
        ((Catlike_associator a b c d _ _ _) (precatbinprodpair k (precatbinprodpair h g)))
        (identity f)).
Proof.
  intros k h g f.
  apply nat_trans_eq. exact hsE.

  intros oba.
  simpl.

  (* Everything boils down to the identity *)
  repeat rewrite functor_id.
  repeat rewrite (id_left _).
  reflexivity.
Defined.

Definition Catlike_triangle ( a b c : precategory )
  (hsB : has_homsets b) (hsC : has_homsets c) :
   forall f g, functor_on_morphisms (functorial_composition a b c _ _)
                               (precatbinprodmor (identity f) (Catlike_left_unitor b c _ hsC g))
   =
      (Catlike_associator a b b c hsB _ _
        (precatbinprodpair f (precatbinprodpair (functor_identity_as_ob b hsB) g)))
   · functor_on_morphisms (functorial_composition a b c _ _)
                           (precatbinprodmor (Catlike_right_unitor a b _ f) (identity g)).
Proof.
  intros f g.
  apply nat_trans_eq. exact hsC.
  intros oba.
  simpl.
  repeat rewrite functor_id.
  repeat rewrite (id_left _).
  reflexivity.
Defined.

(******************************************************************************)
(* The prebicategory of precategories *)

Definition PreCat_1mor_2mor : prebicategory_ob_1mor_2mor.
Proof.
  exists category.
  intros a b.
  exact (functor_precategory a b (homset_property b)).
Defined.

Definition PreCat_id_comp : prebicategory_id_comp.
Proof.
  exists PreCat_1mor_2mor.
  split.
  - simpl.
    exact functor_identity.
  - simpl.
    intros a b c.
    exact (functorial_composition a b c (homset_property b)
                                        (homset_property c)).
Defined.

Definition PreCat_data : prebicategory_data.
Proof.
  unfold prebicategory_data.
  exists PreCat_id_comp.
  repeat split.
  - intros.
    simpl in a,b,c,d.
    exact (Catlike_associator a b c d (homset_property b)
                                      (homset_property c)
                                      (homset_property d)).
  - intros.
    simpl in a, b.
    exact (Catlike_left_unitor a b (homset_property a)
                                   (homset_property b)).
  - intros.
    simpl in a, b.
    exact (Catlike_right_unitor a b (homset_property b)).
Defined.

Definition PreCat_has_2mor_set : has_2mor_sets PreCat_data.
Proof.
  unfold has_2mor_sets.
  intros a b f g.
  apply isaset_nat_trans.
  exact (homset_property b).
Defined.

Definition PreCat_associator_and_unitors_are_iso : associator_and_unitors_are_iso PreCat_data.
Proof.
  repeat split.
  - intros a b c d.
    apply Catlike_associator_is_iso.
  - intros a b.
    apply Catlike_left_unitor_is_iso.
  - intros a b.
    apply Catlike_right_unitor_is_iso.
Defined.

Definition PreCat_coherence : prebicategory_coherence PreCat_data.
Proof.
  unfold prebicategory_coherence.
  split.
  - intros a b c d e.
    apply Catlike_pentagon.
  - intros a b c.
    apply Catlike_triangle.
Defined.

Definition PreCat : prebicategory.
Proof.
  use tpair.
  exact PreCat_data.
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
  exists univalent_category.
  intros a b.
  exact (functor_precategory a b (univalent_category_has_homsets b)).
Defined.

Definition Cat_id_comp : prebicategory_id_comp.
Proof.
  exists Cat_1mor_2mor.
  split.
  - simpl.
    exact functor_identity.
  - simpl.
    intros a b c.
    exact (functorial_composition a b c (univalent_category_has_homsets b)
                                        (univalent_category_has_homsets c)).
Defined.

Definition Cat_data : prebicategory_data.
Proof.
  unfold prebicategory_data.
  exists Cat_id_comp.
  repeat split.
  - intros.
    simpl in a,b,c,d.
    exact (Catlike_associator a b c d (univalent_category_has_homsets b)
                                      (univalent_category_has_homsets c)
                                      (univalent_category_has_homsets d)).
  - intros.
    simpl in a, b.
    exact (Catlike_left_unitor a b (univalent_category_has_homsets a)
                                   (univalent_category_has_homsets b)).
  - intros.
    simpl in a, b.
    exact (Catlike_right_unitor a b (univalent_category_has_homsets b)).
Defined.

Definition Cat_has_2mor_set : has_2mor_sets Cat_data.
Proof.
  unfold has_2mor_sets.
  intros a b f g.
  apply isaset_nat_trans.
  exact (univalent_category_has_homsets b).
Defined.

Definition Cat_associator_and_unitors_are_iso : associator_and_unitors_are_iso Cat_data.
Proof.
  repeat split.
  - intros a b c d.
    apply Catlike_associator_is_iso.
  - intros a b.
    apply Catlike_left_unitor_is_iso.
  - intros a b.
    apply Catlike_right_unitor_is_iso.
Defined.

Definition Cat_coherence : prebicategory_coherence Cat_data.
Proof.
  split.
  - intros a b c d e.
    apply Catlike_pentagon.
  - intros a b c.
    apply Catlike_triangle.
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
  apply is_univalent_functor_category.
Defined.

(* TODO: "Should be easy" *)

(* Definition Cat_is_lt2saturated (a b : Cat_prebicategory) *)
(*   : isweq (id_to_internal_equivalence a b). *)
(* Proof. *)

(* Definition Cat : bicategory. *)
(* Proof. *)
(*   exists Cat_prebicategory. *)
(*   split. *)
(*   - exact Cat_has_homcats. *)
(*   - exact Cat_is_lt2saturated. *)
(* Defined. *)
