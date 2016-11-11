(** * Monics *)
(** ** Contents
- Definitions of Monics
- Construction of the subcategory of Monics
- Construction of monics in functor categories
*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.sub_precategories.
Require Import UniMath.CategoryTheory.functor_categories.


(** * Definition of Monics *)
Section def_monic.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Definition and construction of isMonic. *)
  Definition isMonic {y z : C} (f : y --> z) : UU :=
    Π (x : C) (g h : x --> y), g ;; f = h ;; f -> g = h.

  Definition mk_isMonic {y z : C} (f : y --> z)
             (H : Π (x : C) (g h : x --> y), g ;; f = h ;; f -> g = h) : isMonic f := H.

  Lemma isapropisMonic {y z : C} (f : y --> z) : isaprop (isMonic f).
  Proof.
    apply impred_isaprop; intros t.
    apply impred_isaprop; intros g.
    apply impred_isaprop; intros h.
    apply impred_isaprop; intros H.
    apply hs.
  Qed.

  (** Definition and construction of Monic. *)
  Definition Monic (y z : C) : UU := Σ f : y --> z, isMonic f.

  Definition mk_Monic {y z : C} (f : y --> z) (H : isMonic f) : Monic y z := tpair _ f H.

  (** Gets the arrow out of Monic. *)
  Definition MonicArrow {y z : C} (M : Monic y z) : C⟦y, z⟧ := pr1 M.
  Coercion MonicArrow : Monic >-> precategory_morphisms.

  Definition MonicisMonic {y z : C} (M : Monic y z) : isMonic M := pr2 M.

  (** Isomorphism to isMonic and Monic. *)
  Lemma iso_isMonic {y x : C} (f : y --> x) (H : is_iso f) : isMonic f.
  Proof.
    apply mk_isMonic.
    intros z g h X.
    apply (post_comp_with_iso_is_inj _ y _ f H).
    exact X.
  Defined.

  Lemma iso_Monic {y x : C} (f : y --> x) (H : is_iso f) : Monic y x.
  Proof.
    apply (mk_Monic f (iso_isMonic f H)).
  Defined.

  (** Identity to isMonic and Monic. *)
  Lemma identity_isMonic {x : C} : isMonic (identity x).
  Proof.
    apply (iso_isMonic (identity x) (identity_is_iso _ x)).
  Defined.

  Lemma identity_Monic {x : C} : Monic x x.
  Proof.
    exact (tpair _ (identity x) (identity_isMonic)).
  Defined.

  (** Composition of isMonics and Monics. *)
  Definition isMonic_comp {x y z : C} (f : x --> y) (g : y --> z) :
    isMonic f -> isMonic g -> isMonic (f ;; g).
  Proof.
    intros X X0. apply mk_isMonic. intros x0 g0 h X1.
    repeat rewrite assoc in X1. apply X0 in X1. apply X in X1. apply X1.
  Defined.

  Definition Monic_comp {x y z : C} (M1 : Monic x y) (M2 : Monic y z) :
    Monic x z := tpair _ (M1 ;; M2) (isMonic_comp M1 M2 (pr2 M1) (pr2 M2)).

  (** If precomposition of g with f is a monic, then f is a monic. *)
  Definition isMonic_postcomp {x y z : C} (f : x --> y) (g : y --> z) :
    isMonic (f ;; g) -> isMonic f.
  Proof.
    intros X. intros w φ ψ H.
    apply (maponpaths (fun f' => f' ;; g)) in H.
    repeat rewrite <- assoc in H.
    apply (X w _ _ H).
  Defined.

End def_monic.
Arguments isMonic [C] [y] [z] _.


(** * Construction of the subcategory consisting of all monics. *)
Section monics_subcategory.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition hsubtypes_obs_isMonic : hsubtypes C := (fun c : C => hProppair _ isapropunit).

  Definition hsubtypes_mors_isMonic : Π (a b : C), hsubtypes (C⟦a, b⟧) :=
    (fun a b : C => (fun f : C⟦a, b⟧ => hProppair _ (isapropisMonic C hs f))).

  Definition subprecategory_of_monics : sub_precategories C.
  Proof.
    use tpair.
    split.
    - exact hsubtypes_obs_isMonic.
    - exact hsubtypes_mors_isMonic.
    - cbn. unfold is_sub_precategory. cbn.
      split.
      + intros a tt. exact (identity_isMonic C).
      + apply isMonic_comp.
  Defined.

  Definition has_homsets_subprecategory_of_monics : has_homsets subprecategory_of_monics.
  Proof.
    intros a b.
    apply is_set_sub_precategory_morphisms.
    exact hs.
  Qed.

  Definition subprecategory_of_monics_ob (c : C) : ob (subprecategory_of_monics) := tpair _ c tt.

  Definition subprecategory_of_monics_mor {c' c : C} (f : c' --> c) (isM : isMonic f) :
    subprecategory_of_monics⟦subprecategory_of_monics_ob c', subprecategory_of_monics_ob c⟧ :=
    tpair _ f isM.

End monics_subcategory.


(** * In functor categories monics can be constructed from pointwise monics *)
Section monics_functorcategories.

  Lemma is_nat_trans_monic_from_pointwise_monics (C D : precategory) (hs : has_homsets D)
        (F G : ob (functor_precategory C D hs)) (α : F --> G) (H : Π a : ob C, isMonic (pr1 α a)) :
    isMonic α.
  Proof.
    intros G' β η H'.
    use (nat_trans_eq hs).
    intros x.
    set (H'' := nat_trans_eq_pointwise H' x). cbn in H''.
    apply (H x) in H''.
    exact H''.
  Qed.

End monics_functorcategories.
