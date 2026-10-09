(********************************************************************************

 Unital (Pre)magmoids

 Author: B. Szilvasy
 January 2026

 A unital (pre)magmoid is a (pre)category without associativity.  It
 may also be called a "non-associative category". This file defines
 unital magmoids, and provides definitions and lemmas for the
 important special cases when unital magmoids do associate.

 Contents:
 1. Linearity, thunkability and polarization (exposition)
 2. Unbundled definitions of unitality and associativity
 3. Definition of a unital (pre)magmoid
 3.1. Unital premagmoid
 3.2. Unital magmoid
 4. Definition of linearity, thunkability, and polarization
 5. Lemmas for working with linearity, thunkability and polarization

 ** Linearity, thunkability and polarization (exposition)

 Linearity, thunkability, and polarization are those properties of morphisms or
 objects that provide associatitivy of composition around them, in the following
 ways (described in diagram order):

 1. A *linear* morphism associates when it is on the *right*.
 2. A *thunkable* morphism associates when it is on the *left*.
 3. An *intermediate* morphisms associates when it is in the *middle*.
 4. A *negative* object is one where all *incoming* morphisms are *thunkable*.
 5. A *positive* object is one where all *outgoing* morphisms are *linear*.

 In pictorial form, given objects and morphisms as follows, composition
 associates if any one of the annotations holds:

 <<
                                  intermediate
                       thunkable ↓     ↓     ↓ linear
                                 f     g     h
                              A --> B --> C --> D
                           negative ↑     ↑ positive
 >>

 When any of those named properties can be proven, the lemmas named below can be
 used to reassociate, replacing the [*] with the property:

 - [assoc_*]  : f · (g · h) = (f · g) · h     ("to the left")
 - [assoc'_*] : (f · g) · h = f · (g · h)    ("to the right")

 Identities are both linear and thunkable, and composition preserves linearity.
 Indeed, a unital magmoid's submagmoid of linear morphisms is a category, and
 likewise for thunkable morphisms, but those definitions and more are in
 [PolarizedSubcategories.v].

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

Declare Scope unital_magmoid.
Delimit Scope unital_magmoid with unital_magmoid.
Local Open Scope unital_magmoid.

Section magmoid_defs.
  (** ** Unbundled definitions of unitality and associativity *)

  Definition unital_premagmoid_data := precategory_data.
  Identity Coercion Id_unital_premagmoid_data : unital_premagmoid_data >-> precategory_data.

  Definition is_unital_premagmoid (M : unital_premagmoid_data) : UU
    := ((∏ (a b : M) (f : a --> b), identity a · f = f)
          ×
          (∏ (a b : M) (f : a --> b), f · identity b = f)).
  Definition make_is_unital_premagmoid (M : unital_premagmoid_data)
    (H1 : ∏ (a b : M) (f : a --> b), identity a · f = f)
    (H2 : ∏ (a b : M) (f : a --> b), f · identity b = f)
    : is_unital_premagmoid M
    := H1,,H2.

  Definition isaprop_is_unital_premagmoid (M : unital_premagmoid_data) (hs : has_homsets M)
    : isaprop (is_unital_premagmoid M).
  Proof. apply isapropdirprod; do 3 (apply impred; intro); apply hs. Qed.

  Definition is_assoc_premagmoid (M : unital_premagmoid_data) : UU
    := ((∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
          ×
          (∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), (f · g) · h = f · (g · h))).
  Definition make_is_assoc_premagmoid (M : unital_premagmoid_data)
    (H1 : ∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
    (H2 : ∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), (f · g) · h = f · (g · h))
    : is_assoc_premagmoid M
    := H1,,H2.
  Definition make_is_one_assoc_premagmoid (M : unital_premagmoid_data)
    (H : ∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
    : is_assoc_premagmoid M
    := make_is_assoc_premagmoid M H (λ a b c d f g h, !H a b c d f g h).

  Definition isaprop_is_assoc_premagmoid (M : unital_premagmoid_data) (hs : has_homsets M)
    : isaprop (is_assoc_premagmoid M).
  Proof. apply isapropdirprod; do 7 (apply impred; intro); apply hs. Qed.

  (** ** Definition of a unital (pre)magmoid *)

  (** *** Unital premagmoid *)
  Definition unital_premagmoid : UU
    := total2 is_unital_premagmoid.
  Coercion unital_premagmoid_to_precategory_data (M : unital_premagmoid) : unital_premagmoid_data := pr1 M.
  Definition unital_premagmoid_is_unital (M : unital_premagmoid) : is_unital_premagmoid M := pr2 M.
  Definition make_unital_premagmoid
    (M : unital_premagmoid_data) (H : is_unital_premagmoid M) : unital_premagmoid
    := M,,H.

  Definition magmoid_id_left {M : unital_premagmoid} {a b : M} (f : a --> b)
    : identity a · f = f
    := pr1 (unital_premagmoid_is_unital M) a b f.
  Definition magmoid_id_right {M : unital_premagmoid} {a b : M} (f : a --> b)
    : f · identity b = f
    := pr2 (unital_premagmoid_is_unital M) a b f.

  (** *** Unital magmoid *)
  Definition unital_magmoid : UU
    := ∑ (M : unital_premagmoid), has_homsets M.
  Definition make_unital_magmoid
    (M : unital_premagmoid)
    (H : has_homsets M)
    : unital_magmoid
    := M,,H.
  Coercion unital_magmoid_to_unital_premagmoid (M : unital_magmoid) : unital_premagmoid := pr1 M.
  Definition unital_magmoid_has_homsets (M : unital_magmoid) : has_homsets M := pr2 M.

  Definition unital_magmoid_paths (N M : unital_magmoid)
    (data_eq : (N : precategory_data) = M)
    : N = M.
  Proof.
    apply subtypePath'.
    2: apply isaprop_has_homsets.
    apply subtypePath'.
    2: apply isaprop_is_unital_premagmoid, unital_magmoid_has_homsets.
    exact data_eq.
  Defined.

  Definition um_homset {M : unital_magmoid} (a b : M) : hSet
    := make_hSet (M⟦a, b⟧) (unital_magmoid_has_homsets M a b).

End magmoid_defs.

(** ** Definition of linearity, thunkability, and polarization *)

Section polarity_defs.

  Context {M : unital_premagmoid_data}.
  Hypothesis hs : has_homsets M.

  (** Linear, thunkable and intermediate *)

  Definition is_linear {a b : M} (f : a --> b) : UU
    := ∏ (c d : M) (g : c --> a) (h : d --> c),
      (h · g) · f = h · (g · f).
  Definition is_thunkable {a b : M} (f : b --> a) : UU
    := ∏ (c d : M) (g : a --> c) (h : c --> d),
      f · (g · h) = (f · g) · h.
  Definition is_intermediate {a b : M} (f : a --> b) : UU
    :=  ∏ (c d : M) (g : c --> a) (h : b --> d),
      g · (f · h) = (g · f) · h.

  Lemma isaprop_is_linear' {a b : M} (f : a --> b) : isaprop (is_linear f).
  Proof. do 4 (apply impred; intro); apply hs. Qed.
  Lemma isaprop_is_thunkable' {a b : M} (f : a --> b) : isaprop (is_thunkable f).
  Proof. do 4 (apply impred; intro); apply hs. Qed.
  Lemma isaprop_is_intermediate' {a b : M} (f : a --> b) : isaprop (is_intermediate f).
  Proof. do 4 (apply impred; intro); apply hs. Qed.

  (** Positive and negative *)

  Definition is_positive (a : M) : UU
    := ∏ (b : M) (f : a --> b), is_linear f.
  Definition is_negative (a : M) : UU
    := ∏ (b : M) (f : b --> a), is_thunkable f.

  Lemma isaprop_is_positive' (a : M) : isaprop (is_positive a).
  Proof. do 2 (apply impred; intro); apply isaprop_is_linear'. Qed.
  Lemma isaprop_is_negative' (a : M) : isaprop (is_negative a).
  Proof. do 2 (apply impred; intro); apply isaprop_is_thunkable'. Qed.

End polarity_defs.

(** ** Lemmas for working with linearity, thunkability and polarization *)

Section polarity_lemmas.
  Context {M : unital_premagmoid_data}.

  Definition is_linear_of_positive {a b : M} (f : a --> b)
    : is_positive a -> is_linear f := λ H, H _ f.
  Definition is_thunkable_of_negative {a b : M} (f : b --> a)
    : is_negative a -> is_thunkable f := λ H, H _ f.

  (** Lemmas for reassociating composition. *)

  Lemma assoc_linear {a b c d : M} (f : a --> b) (H : is_linear f)
    (g : c --> a) (h : d --> c) : h · (g · f) = (h · g) · f.
  Proof. apply pathsinv0, H. Defined.
  Lemma assoc'_linear {a b c d : M} (f : a --> b) (H : is_linear f)
    (g : c --> a) (h : d --> c)
    : (h · g) · f = h · (g · f).
  Proof. apply H. Defined.

  Lemma assoc_thunkable {a b c d : M} (f : b --> a) (H : is_thunkable f)
    (g : a --> c) (h : c --> d)
    : f · (g · h) = (f · g) · h.
  Proof. apply H. Defined.
  Lemma assoc'_thunkable {a b c d : M} (f : b --> a) (H : is_thunkable f)
    (g : a --> c) (h : c --> d)
    : (f · g) · h = f · (g · h).
  Proof. apply pathsinv0, H. Defined.

  Lemma assoc_positive {a b d : M} (c : M) (H : is_positive c)
    (f : a --> b) (g : b --> c) (h : c --> d)
    : f · (g · h) = (f · g) · h.
  Proof. apply assoc_linear, is_linear_of_positive, H. Defined.
  Lemma assoc'_positive {a b d : M} (c : M) (H : is_positive c)
    (f : a --> b) (g : b --> c) (h : c --> d)
    : (f · g) · h = f · (g · h).
  Proof. apply assoc'_linear, is_linear_of_positive, H. Defined.

  Lemma assoc_negative {a c d : M} (b : M) (H : is_negative b)
    (f : a --> b) (g : b --> c) (h : c --> d)
    : f · (g · h) = (f · g) · h.
  Proof. apply assoc_thunkable, is_thunkable_of_negative, H. Defined.
  Lemma assoc'_negative {a c d : M} (b : M) (H : is_negative b)
    (f : a --> b) (g : b --> c) (h : c --> d)
    : (f · g) · h = f · (g · h).
  Proof. apply assoc'_thunkable, is_thunkable_of_negative, H. Defined.

  Lemma assoc_intermediate {a b c d : M} (f : b --> c) (H : is_intermediate f)
    (g : a --> b) (h : c --> d)
    : g · (f · h) = (g · f) · h.
  Proof. apply H. Defined.
  Lemma assoc'_intermediate {a b c d : M} (f : b --> c) (H : is_intermediate f)
    (g : a --> b) (h : c --> d)
    : (g · f) · h = g · (f · h).
  Proof. apply pathsinv0, H. Defined.

  (** Linearity and thunkability are preserved under composition. *)
  Lemma is_linear_compose {a b c : M} (f : a --> b) (g : b --> c)
    : is_linear f -> is_linear g -> is_linear (f · g).
  Proof. intros Hf Hg d e h k. now rewrite <- Hg, <- Hg, Hf, Hg. Qed.
  Lemma is_thunkable_compose {a b c : M} (f : a --> b) (g : b --> c)
    : is_thunkable f -> is_thunkable g -> is_thunkable (f · g).
  Proof. intros Hf Hg d e h k. now rewrite <- Hf, <- Hf, Hg, Hf. Qed.

  (** Intermediate morphisms *)

  Lemma is_intermediate_of_positive {a b : M} (f : a --> b)
    : is_positive b -> is_intermediate f.
  Proof. intros H c d g h; apply assoc_positive, H. Qed.
  Lemma is_intermediate_of_negative {a b : M} (f : a --> b)
    : is_negative a -> is_intermediate f.
  Proof. intros H c d g h; apply assoc_negative, H. Qed.
  Lemma is_intermediate_compose {a b c : M} (f : a --> b) (g : b --> c)
    : is_intermediate f -> is_intermediate g -> is_intermediate (f · g).
  Proof. intros Hf Hg d e h k. now rewrite <- Hg, !Hf, Hg. Qed.

  Lemma is_negative_of_all_intermediate (a : M)
    (H : ∏ (b : M) (f : a --> b), is_intermediate f)
    : is_negative a.
  Proof.
    intros b f c d g h.
    apply assoc_intermediate, H.
  Qed.

  Lemma is_positive_of_all_intermediate (a : M)
    (H : ∏ (b : M) (f : a <-- b), is_intermediate f)
    : is_positive a.
  Proof.
    intros b f c d g h.
    apply assoc'_intermediate, H.
  Qed.

End polarity_lemmas.

Section polarity_lemmas.
  Context {M : unital_premagmoid}.

  (** Identities are linear and thunkable. *)
  Lemma is_linear_identity (a : M) : is_linear (identity a).
  Proof. intros b c g h. now do 2 rewrite magmoid_id_right. Defined.
  Lemma is_thunkable_identity (a : M) : is_thunkable (identity a).
  Proof. intros b c g h. now do 2 rewrite magmoid_id_left. Defined.
  Lemma is_intermediate_identity (a : M) : is_intermediate (identity a).
  Proof. intros b c g h. now rewrite magmoid_id_left, magmoid_id_right. Qed.

  (** Characterisations of [is_assoc_premagmoid] in a unital magmoid *)
  Lemma all_is_linear_iff_assoc
    : (∏ (a b : M) (f : a --> b), is_linear f) <-> is_assoc_premagmoid M.
  Proof.
    split; intro H.
    - apply make_is_one_assoc_premagmoid; intros.
      apply assoc_linear, H.
    - intros a b f c d g h. apply H.
  Defined.

  Lemma all_is_thunkable_iff_assoc
    : (∏ (a b : M) (f : a <-- b), is_thunkable f) <-> is_assoc_premagmoid M.
  Proof.
    split; intro H.
    - apply make_is_one_assoc_premagmoid; intros.
      apply assoc_thunkable, H.
    - intros a b f c d g h. apply H.
  Defined.

  Lemma all_is_positive_iff_assoc
    : (∏ (a : M), is_positive a) <-> is_assoc_premagmoid M.
  Proof.
    eapply logeq_trans; [|apply all_is_linear_iff_assoc].
    split; intro H; intros.
    - apply is_linear_of_positive, H.
    - intros b f.
      apply H.
  Defined.

  Lemma all_is_negative_iff_assoc
    : (∏ (a : M), is_negative a) <-> is_assoc_premagmoid M.
  Proof.
    eapply logeq_trans; [|apply all_is_thunkable_iff_assoc].
    split; intro H; intros.
    - apply is_thunkable_of_negative, H.
    - intros b f.
      apply H.
  Defined.

End polarity_lemmas.

Section polarity_lemmas.
  Context {M : unital_magmoid}.
  Let hs : has_homsets M := unital_magmoid_has_homsets M.

  Definition isaprop_is_linear {a b : M} (f : a --> b) : isaprop (is_linear f).
  Proof. apply isaprop_is_linear', hs. Defined.
  Definition isaprop_is_thunkable {a b : M} (f : a --> b) : isaprop (is_thunkable f).
  Proof. apply isaprop_is_thunkable', hs. Defined.
  Lemma isaprop_is_intermediate {a b : M} (f : a --> b) : isaprop (is_intermediate f).
  Proof. apply isaprop_is_intermediate', hs. Qed.

  Definition ish_linear {a b : M} : hsubtype (a --> b)
    := λ f, make_hProp (is_linear f) (isaprop_is_linear f).
  Definition ish_thunkable {a b : M} : hsubtype (a --> b)
    := λ f, make_hProp (is_thunkable f) (isaprop_is_thunkable f).
  Definition ish_intermediate {a b : M} : hsubtype (a --> b)
    := λ f, make_hProp (is_intermediate f) (isaprop_is_intermediate f).

  (** Positive objects *)
  Definition isaprop_is_positive (a : M) : isaprop (is_positive a).
  Proof. apply isaprop_is_positive', hs. Defined.
  Definition ish_positive : hsubtype M
    := λ a, make_hProp (is_positive a) (isaprop_is_positive a).

  (** Negative objects *)
  Definition isaprop_is_negative (a : M) : isaprop (is_negative a).
  Proof. apply isaprop_is_negative', hs. Defined.
  Definition ish_negative : hsubtype M
    := λ a, make_hProp (is_negative a) (isaprop_is_negative a).

End polarity_lemmas.
Notation "'^⊕'" := ish_positive : unital_magmoid.
Notation "'^⊖'" := ish_negative : unital_magmoid.
