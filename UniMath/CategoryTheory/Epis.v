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
  Definition Epi (x y : C) := Σ f : x --> y, isEpi f.
  Definition mk_Epi {x y : C} (f : x --> y) (H : isEpi f) : Epi x y.
  Proof. apply (tpair _ f H). Defined.

  (** Gets the arrow out of Epi. *)
  Definition EpiArrow {x y : C} (M : Epi x y) := pr1 M.

  (** Identity to isEpi and Epi. *)
  Lemma id_isEpi {x : C} : isEpi (identity x).
  Proof.
    apply mk_isEpi.
    intros z g h H.
    rewrite <- id_left; apply pathsinv0; rewrite <- id_left; apply pathsinv0.
    exact H.
  Defined.

  Lemma id_Epi {x : C} : Epi x x.
  Proof. exact (tpair _ (identity x) (id_isEpi)). Defined.

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

  (** Composition of isEpis and Epis. *)
  Definition isEpi_comp {x y z : C} (f : x --> y) (g : y --> z) :
    isEpi f -> isEpi g -> isEpi (f ;; g).
  Proof.
    intros X X0. unfold isEpi. intros z0 g0 h X1.
    repeat rewrite <- assoc in X1. apply X in X1. apply X0 in X1. apply X1.
  Defined.

  Definition Epi_comp {x y z : C} (M1 : Epi x y) (M2 : Epi y z) :
    Epi x z := tpair _ (EpiArrow M1 ;; EpiArrow M2)
                       (isEpi_comp (EpiArrow M1) (EpiArrow M2)
                                     (pr2 M1) (pr2 M2)).

  (* This general result should be moved somewhere? *)
  Lemma precomp_with_eq {x y z : C} {f g : y --> z} (h : x --> y) :
    f = g -> h ;; f = h ;; g.
  Proof.
    intros X.
    rewrite X.
    apply idpath.
  Defined.

  (** If precomposition of g with f is an epi, then g is an epi. *)
  Definition isEpi_precomp {x y z : C} (f : x --> y) (g : y --> z) :
    isEpi (f ;; g) -> isEpi g.
  Proof.
    intros X. intros w φ ψ H.
    apply (precomp_with_eq f) in H.
    repeat rewrite assoc in H.
    apply (X w _ _ H).
  Defined.

End def_epi.
