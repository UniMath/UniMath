Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.ModelCategories.Retract.

Declare Scope morcls.
Delimit Scope morcls with morcls.

Local Open Scope morcls.

Local Open Scope cat.

(* See UniMath/MoreFoundations/Subtypes.v *)

(* A subset in Coq is like (A : hSet) : A -> Prop *)
Definition morphism_class (C : category) : UU :=
    ∏ (X Y : C), hsubtype (X --> Y).

Lemma isasetmorphism_class {C : category} : isaset (morphism_class C).
Proof.
  change (isaset) with (isofhlevel 2).
  apply impred; intro x.
  apply impred; intro t.
  exact (isasethsubtype _).
Qed.

Definition morphism_class_set (C : category) : hSet :=
    make_hSet (morphism_class C) (isasetmorphism_class (C := C)).

Definition morphism_class_containedIn {C : category} : hrel (morphism_class_set C) :=
    λ S T, ∀ (X Y : C) (f : X --> Y), ((S _ _) f ⇒ (T _ _) f)%logic.

Notation "S ⊆ T" := (morphism_class_containedIn S T) (at level 70) : morcls.

(* Definition morphism_class_notContainedIn : hrel (morphism_class_set C) :=
    λ S T, ∃ (X Y : C) (f : X --> Y), ((S _ _) f × ¬(T _ _) f)%logic. *)

Lemma morphism_class_ext {C : category} {I J : morphism_class C}
  (h : ∏ x y (f : x --> y), ((I _ _) f <-> (J _ _) f)) : I = J.
Proof.
  do 3 (apply funextsec; intro).
  destruct ((h x x0 x1)) as [impl conv].

  (* in the statement we wish to prove that two hProps are equal,
     this boils down to univalence on hProps *)
  exact (hPropUnivalence _ _ impl conv).
Qed.

Lemma morphism_class_subset_antisymm {C : category} {I J : morphism_class C} (h : I ⊆ J) (h' : J ⊆ I) : I = J.
Proof.
  apply morphism_class_ext.
  intros x y f.
  split.
  - exact (h _ _ _).
  - exact (h' _ _ _).
Qed.

Definition morphism_class_intersection {C : category} (S T : morphism_class C) : morphism_class C :=
    λ X Y f, (S _ _ f) ∧ (T _ _ f).

Notation "S ∩ T" := (morphism_class_intersection S T) (at level 40, left associativity) : morcls.

(* Back to morphism_class.lean *)
Definition morphism_class_univ (C : category) : (morphism_class C) :=
    λ X Y f, htrue.

Definition morphism_class_isos (C : category) : (morphism_class C) :=
    λ X Y f, make_hProp (is_iso f) (isaprop_is_iso _ _ _).

Lemma iso_in_morphism_class_isos {C : category} {a b : C} (f : iso a b) : (morphism_class_isos C _ _ f).
Proof.
  exact (iso_is_iso f).
Qed.

(* No longer in lean files *)

Definition morphism_class_opp {C : category} (S : morphism_class C) : (morphism_class (op_cat C)) :=
    λ X Y f, (S _ _) (opp_mor f).

Definition morphism_class_rm_opp {C : category} (S : morphism_class (op_cat C)) : (morphism_class C) :=
    λ X Y f, (S _ _) (rm_opp_mor f).

Lemma morphism_class_opp_opp {C : category} (S : morphism_class C) :
    morphism_class_opp (morphism_class_opp S) = S.
Proof.
  trivial.
Qed.

Definition morphism_class_opp_equal {C : category} {S T : morphism_class C} (e : morphism_class_opp S = morphism_class_opp T) :
  S = T.
Proof.
  rewrite <- (morphism_class_opp_opp S).
  rewrite <- (morphism_class_opp_opp T).
  now rewrite e.
Qed.

Definition morphism_class_retract_closure
    {C : category} (S : morphism_class C) : morphism_class C :=
  λ x y (f : x --> y), ∃ x' y' (f' : x' --> y'), (S _ _ f') × (retract f' f).

Notation "S ^cl" := (morphism_class_retract_closure S) (at level 70) : morcls.

Definition morphism_class_retract_closed
    {C : category} (S : morphism_class C) : UU :=
  ∏ x y (f : x --> y) x' y' (f' : x' --> y'),
    (S _ _ f') × (retract f' f) -> (S _ _ f).

Lemma isaprop_morphism_class_retract_closed {C : category} (S : morphism_class C) :
  isaprop (morphism_class_retract_closed S).
Proof.
  do 7 (apply impred; intro).
  apply propproperty.
Qed.

Lemma in_morcls_retc_if_in_morcls {C : category} (S : morphism_class C)
    {a b} (f : a --> b) :
  (S _ _ f) -> (S^cl _ _ f).
Proof.
  intro H.

  apply hinhpr.
  exists _, _, f.
  exact (make_dirprod H (retract_self f)).
Qed.

Lemma morphism_class_retract_closed_impl_eq_cl {C : category} (S : morphism_class C) :
  morphism_class_retract_closed S -> S^cl = S.
Proof.
  intro H.
  apply morphism_class_subset_antisymm.
  - intros x y f Hf.
    simpl in Hf.
    use (hinhuniv _ Hf).
    clear Hf; intro Hf; destruct Hf as [x' [y' [f' Hf']]].
    apply (H _ _ f _ _ f' Hf').
  - intros x y f Hf.
    apply in_morcls_retc_if_in_morcls.
    exact Hf.
Qed.

Lemma morphism_class_retract_closed_if_eq_cl {C : category} (S : morphism_class C) :
    S^cl = S -> morphism_class_retract_closed S.
Proof.
  intro H.
  intros x y f x' y' f' Hf'.
  rewrite <- H.
  apply hinhpr.
  exists _, _, f'.
  exact Hf'.
Qed.

Lemma morphism_class_retract_closed_iff_eq_cl
    {C : category} (S : morphism_class C) :
  morphism_class_retract_closed S <-> S^cl = S.
Proof.
  split.
  - exact (morphism_class_retract_closed_impl_eq_cl S).
  - exact (morphism_class_retract_closed_if_eq_cl S).
Qed.

Lemma morcls_eq_impl_morcls_cl_eq {C : category} {S T : morphism_class C}
    (HT : morphism_class_retract_closed T) :
  S = T -> S^cl = T.
Proof.
  intro H.
  rewrite H.
  apply morphism_class_retract_closed_impl_eq_cl.
  exact HT.
Qed.