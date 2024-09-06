(**************************************************************************************************

  The precategory of types in a fixed universe does not have homsets

  In this file, we show that the precategory of types in a fixed universe does not have homsets.
  First of all, we show that bool is equal to itself in two distinct ways: the identity path, or the
  negation path. Therefore, UU is not a set. Because type_precat⟦unit, UU⟧ is equivalent to UU, this
  hom-type is also not a set. This shows that type_precat does not have homsets.

  Contents
  1. The proof that type_precat does not have homsets [type_no_homsets]

 **************************************************************************************************)
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.MoreFoundations.NoInjectivePairing.
Require Import UniMath.MoreFoundations.PartD.
Require Import UniMath.CategoryTheory.Categories.Type.Core.
Require Import UniMath.CategoryTheory.Core.Categories.

Definition bool_eq1 :
  bool = bool
  := weqtopaths (idweq _).

Definition bool_eq2 :
  bool = bool
  := weqtopaths negb_weq.

Lemma bool_eq_distinct :
  bool_eq1 != bool_eq2.
Proof.
  intro H.
  refine (transportf (λ t, bool_to_type (negb t)) (_ : false = true) tt).
  change true with (negb_weq false).
  change false with (idweq _ false).
  apply (maponpaths (λ (f : _ ≃ _), f _)).
  apply (invmaponpathsweq (invweq (univalence _ _))).
  exact H.
Qed.

(* These can be lifted to two distinct proofs for the constant bool function. *)

Definition const_bool
  (t : unit)
  : UU
  := bool.

Definition const_bool_eq1 : const_bool = const_bool :=
  invweq (weqtoforallpaths _ _ _) (λ _, bool_eq1).

Definition const_bool_eq2 : const_bool = const_bool :=
  invweq (weqtoforallpaths _ _ _) (λ _, bool_eq2).

Definition const_bool_eq_distinct :
  const_bool_eq1 != const_bool_eq2.
Proof.
  intros H.
  apply bool_eq_distinct.
  change bool_eq1 with ((λ _, bool_eq1) tt).
  change bool_eq2 with ((λ _, bool_eq2) tt).
  apply (maponpaths (λ x, x tt)).
  refine (invmaponpathsweq (invweq (weqtoforallpaths _ _ _)) _ _ _).
  exact H.
Qed.

(* Hence [UU] has no homsets. *)

Lemma type_no_homsets :
  ¬ has_homsets type_precat.
Proof.
  intros H.
  apply const_bool_eq_distinct.
  apply H.
Qed.
