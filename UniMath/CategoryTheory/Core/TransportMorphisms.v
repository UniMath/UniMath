(** * Lemmas on transport of morphisms *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Local Open Scope cat.

(** *** Transport source and target of a morphism *)

Lemma transport_target_postcompose {C : precategory} {x y z w : ob C} (f : x --> y) (g : y --> z)
      (e : z = w) :
  transportf (precategory_morphisms x) e (f · g) = f · transportf (precategory_morphisms y) e g.
Proof.
  induction e. apply idpath.
Qed.

Lemma transport_source_precompose {C : precategory} {x y z w : ob C} (f : x --> y) (g : y --> z)
      (e : x = w) :
  transportf (λ x' : ob C, precategory_morphisms x' z) e (f · g) =
  transportf (λ x' : ob C, precategory_morphisms x' y) e f · g.
Proof.
  induction e. apply idpath.
Qed.

Lemma transport_compose {C : precategory} {x y z w : ob C} (f : x --> y) (g : z --> w) (e : y = z) :
  transportf (precategory_morphisms x) e f · g =
  f · transportf (λ x' : ob C, precategory_morphisms x' w) (! e) g.
Proof.
  induction e. apply idpath.
Qed.

Lemma transport_compose' {C : precategory} {x y z w : ob C} (f : x --> y) (g : y --> z) (e : y = w) :
  (transportf (precategory_morphisms x) e f)
    · (transportf (λ x' : ob C, precategory_morphisms x' z) e g) = f · g.
Proof.
  induction e. apply idpath.
Qed.

Lemma transport_target_path {C : precategory} {x y z : ob C} (f g : x --> y) (e : y = z) :
  transportf (precategory_morphisms x) e f = transportf (precategory_morphisms x) e g -> f = g.
Proof.
  induction e. intros H. apply H.
Qed.

Lemma transport_source_path {C : precategory} {x y z : ob C} (f g : y --> z) (e : y = x) :
  transportf (λ x' : ob C, precategory_morphisms x' z) e f =
  transportf (λ x' : ob C, precategory_morphisms x' z) e g -> f = g.
Proof.
  induction e. intros H. apply H.
Qed.

Lemma transport_source_target {X : UU} {C : precategory} {x y : X} (P : ∏ (x' : X), ob C)
      (P' : ∏ (x' : X), ob C) (f : ∏ (x' : X), (P x') --> (P' x')) (e : x = y) :
  transportf (λ (x' : X), (P x') --> (P' x')) e (f x) =
  transportf (λ (x' : X), precategory_morphisms (P x') (P' y)) e
             (transportf (precategory_morphisms (P x)) (maponpaths P' e) (f x)).
Proof.
  rewrite <- functtransportf. unfold pathsinv0. unfold paths_rect. induction e.
  apply idpath.
Qed.

Lemma transport_target_source {X : UU} {C : precategory} {x y : X} (P : ∏ (x' : X), ob C)
      (P' : ∏ (x' : X), ob C) (f : ∏ (x' : X), (P x') --> (P' x')) (e : x = y) :
  transportf (λ (x' : X), (P x') --> (P' x')) e (f x) =
  transportf (precategory_morphisms (P y)) (maponpaths P' e)
             (transportf (λ (x' : X), precategory_morphisms (P x') (P' x)) e (f x)).
Proof.
  rewrite <- functtransportf. unfold pathsinv0. unfold paths_rect. induction e.
  apply idpath.
Qed.

Lemma transport_source_target_comm {C : precategory} {x y x' y' : ob C} (f : x --> y) (e1 : x = x')
      (e2 : y = y') :
  transportf (λ (x'' : ob C), precategory_morphisms x'' y') e1
             (transportf (precategory_morphisms x) e2 f) =
  transportf (precategory_morphisms x') e2
             (transportf (λ (x'' : ob C), precategory_morphisms x'' y) e1 f).
Proof.
  induction e1. induction e2. apply idpath.
Qed.


(** *** Transport a morphism using funextfun *)

Definition transport_source_funextfun {X : UU} {C : precategory_ob_mor} (F F' : X -> ob C)
           (H : ∏ (x : X), F x = F' x) {x : X} (c : ob C) (f : F x --> c) :
  transportf (λ x0 : X → C, x0 x --> c) (funextfun F F' H) f =
  transportf (λ x0 : C, x0 --> c) (H x) f.
Proof.
  exact (@transportf_funextfun X (ob C) (λ x0 : C, x0 --> c) F F' H x f).
Qed.

Definition transport_target_funextfun {X : UU} {C : precategory_ob_mor} (F F' : X -> ob C)
           (H : ∏ (x : X), F x = F' x) {x : X} {c : ob C} (f : c --> F x)  :
  transportf (λ x0 : X → C, c --> x0 x) (funextfun F F' H) f =
  transportf (λ x0 : C, c --> x0) (H x) f.
Proof.
  use transportf_funextfun.
Qed.

Lemma transport_mor_funextfun {X : UU} {C : precategory_ob_mor} (F F' : X -> ob C)
           (H : ∏ (x : X), F x = F' x) {x1 x2 : X} (f : F x1 --> F x2) :
  transportf (λ x : X → C, x x1 --> x x2) (funextfun F F' H) f =
  transportf (λ x : X → C, F' x1 --> x x2)
             (funextfun F F' (λ x : X, H x))
             (transportf (λ x : X → C, x x1 --> F x2)
                         ((funextfun F F' (λ x : X, H x))) f).
Proof.
  induction (funextfun F F' (λ x : X, H x)).
  apply idpath.
Qed.

(** *** Transport of is_iso *)
Lemma transport_target_is_iso {C : precategory} {x y z : ob C} (f : x --> y) (H : is_iso f)
      (e : y = z) : is_iso (transportf (precategory_morphisms x) e f).
Proof.
  induction e. apply H.
Qed.

Lemma transport_source_is_iso {C : precategory} {x y z : ob C} (f : x --> y) (H : is_iso f)
      (e : x = z) : is_iso (transportf (λ x' : ob C, precategory_morphisms x' y) e f).
Proof.
  induction e. apply H.
Qed.

(** *** Induced precategories *)

Definition induced_precategory (M : precategory) {X:Type} (j : X -> ob M) : precategory.
Proof.
  use tpair.
  - use tpair.
    + exact (X,, λ a b, precategory_morphisms (j a) (j b)).
    + split;cbn.
      * exact (λ c, identity (j c)).
      * exact (λ a b c, @compose M (j a) (j b) (j c)).
  - repeat split; cbn.
    + exact (λ a b, @id_left M (j a) (j b)).
    + exact (λ a b, @id_right M (j a) (j b)).
    + exact (λ a b c d, @assoc M (j a) (j b) (j c) (j d)).
    + exact (λ a b c d, @assoc' M (j a) (j b) (j c) (j d)).
Defined.