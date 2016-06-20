(* Definition of monic *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Section def_monic.

  Variable C : precategory.

  (** Definition and construction of isMonic. *)
  Definition isMonic {y z : C} (f : y --> z) :=
    forall (x : C) (g h : x --> y), g ;; f = h ;; f -> g = h.
  Definition mk_isMonic {y z : C} (f : y --> z) :
    (forall (x : C) (g h : x --> y), g ;; f = h ;; f -> g = h) -> isMonic f.
  Proof. intros X. unfold isMonic. apply X.  Defined.

  (** Definition and construction of Monic. *)
  Definition Monic (y z : C) := Σ f : y --> z, isMonic f.
  Definition mk_Monic {y z : C} (f : y --> z) (H : isMonic f) : Monic y z.
  Proof. apply (tpair _ f H). Defined.

  (** Gets the arrow out of Monic. *)
  Definition MonicArrow {y z : C} (M : Monic y z) := pr1 M.

  (** Identity to isMonic and Monic. *)
  Lemma identity_isMonic {x : C} : isMonic (identity x).
  Proof.
    apply mk_isMonic.
    intros z g h H.
    rewrite <- id_right; apply pathsinv0; rewrite <- id_right; apply pathsinv0.
    exact H.
  Defined.

  Lemma identity_Monic {x : C} : Monic x x.
  Proof. exact (tpair _ (identity x) (identity_isMonic)). Defined.

  (** Isomorphism to isMonic and Monic. *)
  Lemma iso_isMonic {y x : C} (f : y --> x) (H : is_iso f) : isMonic f.
  Proof.
    apply mk_isMonic.
    intros z g h X.
    apply (post_comp_with_iso_is_inj _ y _ f H).
    exact X.
  Defined.

  Lemma iso_Monic {y x : C} (f : y --> x) (H : is_iso f) : Monic y x.
  Proof. apply (mk_Monic f (iso_isMonic f H)). Defined.

  (** Composition of isMonics and Monics. *)
  Definition isMonic_comp {x y z : C} (f : x --> y) (g : y --> z) :
    isMonic f -> isMonic g -> isMonic (f ;; g).
  Proof.
    intros X X0. apply mk_isMonic. intros x0 g0 h X1.
    repeat rewrite assoc in X1. apply X0 in X1. apply X in X1. apply X1.
  Defined.

  Definition Monic_comp {x y z : C} (M1 : Monic x y) (M2 : Monic y z) :
    Monic x z := tpair _ (MonicArrow M1 ;; MonicArrow M2)
                       (isMonic_comp (MonicArrow M1) (MonicArrow M2)
                                     (pr2 M1) (pr2 M2)).

  (* This general result should be moved somewhere? *)
  Lemma postcomp_with_eq {x y z : C} {f g : x --> y} (h : y --> z) :
    f = g -> f ;; h = g ;; h.
  Proof.
    intros X.
    rewrite X.
    apply idpath.
  Defined.

  (** If precomposition of g with f is a monic, then f is a monic. *)
  Definition isMonic_postcomp {x y z : C} (f : x --> y) (g : y --> z) :
    isMonic (f ;; g) -> isMonic f.
  Proof.
    intros X. intros w φ ψ H.
    apply (postcomp_with_eq g) in H.
    repeat rewrite <- assoc in H.
    apply (X w _ _ H).
  Defined.

End def_monic.
