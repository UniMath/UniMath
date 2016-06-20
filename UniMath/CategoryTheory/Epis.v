(* Definition of epi *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Section def_epi.

  Variable C : precategory.

  (** Definition and construction of isEpi. *)
  Definition isEpi {x y : C} (f : x --> y) :=
    forall (z : C) (g h : y --> z), f ;; g = f ;; h -> g = h.
  Definition mk_isEpi {x y : C} (f : x --> y) :
    (forall (z : C) (g h : y --> z), f ;; g = f ;; h -> g = h) -> isEpi f.
  Proof. intros X. unfold isEpi. apply X.  Defined.

  (** Definition and construction of Epi. *)
  Definition Epi (x y : C) : UU := Σ f : x --> y, isEpi f.
  Definition mk_Epi {x y : C} (f : x --> y) (H : isEpi f) :
    Epi x y := tpair _ f H.

  (** Gets the arrow out of Epi. *)
  Definition EpiArrow {x y : C} (E : Epi x y) : C⟦x, y⟧ := pr1 E.
  Coercion EpiArrow : Epi >-> precategory_morphisms.

  (** Isomorphism to isEpi and Epi. *)
  Lemma iso_isEpi {x y : C} (f : x --> y) (H : is_iso f) : isEpi f.
  Proof.
    apply mk_isEpi.
    intros z g h X.
    apply (pre_comp_with_iso_is_inj _ x _ _ f H).
    exact X.
  Defined.

  Lemma iso_Epi {x y : C} (f : x --> y) (H : is_iso f) : Epi x y.
  Proof. apply (mk_Epi f (iso_isEpi f H)). Defined.

  (** Identity to isEpi and Epi. *)
  Lemma identity_isEpi {x : C} : isEpi (identity x).
  Proof. apply (iso_isEpi (identity x) (identity_is_iso _ x)). Defined.

  Lemma identity_Epi {x : C} : Epi x x.
  Proof. exact (tpair _ (identity x) (identity_isEpi)). Defined.

  (** Composition of isEpis and Epis. *)
  Definition isEpi_comp {x y z : C} (f : x --> y) (g : y --> z) :
    isEpi f -> isEpi g -> isEpi (f ;; g).
  Proof.
    intros X X0. unfold isEpi. intros z0 g0 h X1.
    repeat rewrite <- assoc in X1. apply X in X1. apply X0 in X1. apply X1.
  Defined.

  Definition Epi_comp {x y z : C} (E1 : Epi x y) (E2 : Epi y z) :
    Epi x z := tpair _ (E1 ;; E2) (isEpi_comp E1 E2 (pr2 E1) (pr2 E2)).

  (** If precomposition of g with f is an epi, then g is an epi. *)
  Definition isEpi_precomp {x y z : C} (f : x --> y) (g : y --> z) :
    isEpi (f ;; g) -> isEpi g.
  Proof.
    intros X. intros w φ ψ H.
    apply (maponpaths (fun g' => f ;; g')) in H.
    repeat rewrite assoc in H.
    apply (X w _ _ H).
  Defined.

End def_epi.
