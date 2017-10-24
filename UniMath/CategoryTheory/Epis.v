(** * Epis *)
(** ** Contents
- Definition of Epis
- Construction of the subcategory of Epis
- Construction of Epis in functor categories

More proofs/definitions about epi can be found in EpiFacts
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.sub_precategories.
Require Import UniMath.CategoryTheory.functor_categories.

(** * Definition of Epis *)
Section def_epi.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Definition and construction of isEpi. *)
  Definition isEpi {x y : C} (f : x --> y) : UU :=
    ∏ (z : C) (g h : y --> z), f · g = f · h -> g = h.

  Definition mk_isEpi {x y : C} (f : x --> y)
             (H : ∏ (z : C) (g h : y --> z), f · g = f · h -> g = h) : isEpi f := H.

  Lemma isapropisEpi {y z : C} (f : y --> z) : isaprop (isEpi f).
  Proof.
    apply impred_isaprop; intros t.
    apply impred_isaprop; intros g.
    apply impred_isaprop; intros h.
    apply impred_isaprop; intros H.
    apply hs.
  Qed.

  (** Definition and construction of Epi. *)
  Definition Epi (x y : C) : UU := ∑ f : x --> y, isEpi f.
  Definition mk_Epi {x y : C} (f : x --> y) (H : isEpi f) :
    Epi x y := tpair _ f H.

  (** Gets the arrow out of Epi. *)
  Definition EpiArrow {x y : C} (E : Epi x y) : C⟦x, y⟧ := pr1 E.
  Coercion EpiArrow : Epi >-> precategory_morphisms.

  Definition EpiisEpi {x y : C} (E : Epi x y) : isEpi E := pr2 E.

  (** Isomorphism to isEpi and Epi. *)
  Lemma is_iso_isEpi {x y : C} (f : x --> y) (H : is_z_isomorphism f) : isEpi f.
  Proof.
    apply mk_isEpi.
    intros z g h X.
    apply (pre_comp_with_z_iso_is_inj H).
    exact X.
  Qed.

  Lemma is_iso_Epi {x y : C} (f : x --> y) (H : is_z_isomorphism f) : Epi x y.
  Proof.
    apply (mk_Epi f (is_iso_isEpi f H)).
  Defined.

  (** Identity to isEpi and Epi. *)
  Lemma identity_isEpi {x : C} : isEpi (identity x).
  Proof.
    apply (is_iso_isEpi (identity x) (is_z_isomorphism_identity x)).
  Defined.

  Lemma identity_Epi {x : C} : Epi x x.
  Proof.
    exact (tpair _ (identity x) (identity_isEpi)).
  Defined.

  (** Composition of isEpis and Epis. *)
  Definition isEpi_comp {x y z : C} (f : x --> y) (g : y --> z) :
    isEpi f -> isEpi g -> isEpi (f · g).
  Proof.
    intros X X0. unfold isEpi. intros z0 g0 h X1.
    repeat rewrite <- assoc in X1. apply X in X1. apply X0 in X1. apply X1.
  Qed.

  Definition Epi_comp {x y z : C} (E1 : Epi x y) (E2 : Epi y z) :
    Epi x z := tpair _ (E1 · E2) (isEpi_comp E1 E2 (pr2 E1) (pr2 E2)).

  (** If precomposition of g with f is an epi, then g is an epi. *)
  Definition isEpi_precomp {x y z : C} (f : x --> y) (g : y --> z) : isEpi (f · g) -> isEpi g.
  Proof.
    intros X. intros w φ ψ H.
    apply (maponpaths (fun g' => f · g')) in H.
    repeat rewrite assoc in H.
    apply (X w _ _ H).
  Defined.

  Lemma isEpi_path {x y : C} (f1 f2 : x --> y) (e : f1 = f2) (isE : isEpi f1) : isEpi f2.
  Proof.
    induction e. exact isE.
  Qed.

  (** Transport of isEpi *)
  Lemma transport_target_isEpi {x y z : C} (f : x --> y) (E : isEpi f) (e : y = z) :
    isEpi (transportf (precategory_morphisms x) e f).
  Proof.
    induction e. apply E.
  Qed.

  Lemma transport_source_isEpi {x y z : C} (f : y --> z) (E : isEpi f) (e : y = x) :
    isEpi (transportf (fun x' : ob C => precategory_morphisms x' z) e f).
  Proof.
    induction e. apply E.
  Qed.

End def_epi.
Arguments isEpi [C] [x] [y] _.


(** * Construction of the subcategory consisting of all epis. *)
Section epis_subcategory.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition hsubtype_obs_isEpi : hsubtype C := (fun c : C => hProppair _ isapropunit).

  Definition hsubtype_mors_isEpi : ∏ (a b : C), hsubtype (C⟦a, b⟧) :=
    (fun a b : C => (fun f : C⟦a, b⟧ => hProppair _ (isapropisEpi C hs f))).

  Definition subprecategory_of_epis : sub_precategories C.
  Proof.
    use tpair.
    split.
    - exact hsubtype_obs_isEpi.
    - exact hsubtype_mors_isEpi.
    - cbn. unfold is_sub_precategory. cbn.
      split.
      + intros a tt. exact (identity_isEpi C).
      + apply isEpi_comp.
  Defined.

  Definition has_homsets_subprecategory_of_epis : has_homsets subprecategory_of_epis.
  Proof.
    intros a b.
    apply is_set_sub_precategory_morphisms.
    exact hs.
  Qed.

  Definition subprecategory_of_epis_ob (c : C) : ob (subprecategory_of_epis) := tpair _ c tt.

End epis_subcategory.


(** * In functor categories epis can be constructed from pointwise epis *)
Section epis_functorcategories.

  Lemma is_nat_trans_epi_from_pointwise_epis (C D : precategory) (hs : has_homsets D)
        (F G : ob (functor_precategory C D hs)) (α : F --> G) (H : ∏ a : ob C, isEpi (pr1 α a)) :
    isEpi α.
  Proof.
    intros G' β η H'.
    use (nat_trans_eq hs).
    intros x.
    set (H'' := nat_trans_eq_pointwise H' x). cbn in H''.
    apply (H x) in H''.
    exact H''.
  Qed.

End epis_functorcategories.
