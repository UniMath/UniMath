(********************************************************************************

 Submagmoids

 Author: B. Szilvasy
 September 2026

 Central to the study of unital magmoids are the (often associative) submagmoids
 obtained by restricting to a subset of the morphisms.  We define them in their
 full generality here.  The specific submagmoids obtained by requiring
 associativity may be found in [PolarizedSubcategories.v].

 Contents:
 1. Wide submagmoids
 1.1. Wide submagmoid definitions
 1.2. Wide submagmoid morphisms
 1.3. Sub-objects
 1.4. Intersection submagmoids
 1.5. Associative wide submagmoids
 2. Submagmoids to magmoids
 2.1. Wide submagmoid to magmoid
 2.2. Full submagmoid to magmoid
 2.3. Arbitrary submagmoids

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** Wide submagmoids *)

Section submagmoids.
  Context {M : unital_premagmoid_data}.
  Hypothesis hs : has_homsets M.

  (** *** Wide submagmoid definitions *)

  Definition wide_submagmoid_data : UU
    := ∏ (a b : M), hsubtype (a --> b).
  Identity Coercion Id_wide_submagmoid_data : wide_submagmoid_data >-> Funclass.
  Definition is_wide_submagmoid (P : wide_submagmoid_data) : hProp :=
    ((∀ (a : M), P _ _ (identity a)) ∧
       (∀ (a b c : M) (f : a --> b) (g : b --> c),
           P _ _ f ⇒ P _ _ g ⇒ P _ _ (f · g)))%logic.

  Definition make_is_wide_submagmoid
    (P : wide_submagmoid_data)
    (Hid : ∏ (a : M), P _ _ (identity a))
    (Hcomp : ∏ (a b c : M) (f : a --> b) (g : b --> c), P _ _ f -> P _ _ g -> P _ _ (f · g))
    : is_wide_submagmoid P
    := make_dirprod Hid Hcomp.

  Definition wide_submagmoid := total2 is_wide_submagmoid.
  Coercion wide_submagmoid_to_data (P : wide_submagmoid)
    : wide_submagmoid_data := pr1 P.
  Definition wide_submagmoid_is_wide_submagmoid (P : wide_submagmoid)
    : is_wide_submagmoid P := pr2 P.

  Definition make_wide_submagmoid
    (H : wide_submagmoid_data)
    (His : is_wide_submagmoid H)
    : wide_submagmoid
    := H,, His.

  Definition make_wide_submagmoid'
    (H : wide_submagmoid_data)
    (Hid : ∏ (a : M), H _ _ (identity a))
    (Hcomp : ∏ (a b c : M) (f : a --> b) (g : b --> c), H _ _ f -> H _ _ g -> H _ _ (f · g))
    : wide_submagmoid
    := make_wide_submagmoid H
         (make_is_wide_submagmoid H Hid Hcomp).

  Definition wide_submagmoid_identity_holds (P : wide_submagmoid) (a : M)
    : P a a (identity a)
    := pr1 (wide_submagmoid_is_wide_submagmoid P) a.
  Definition wide_submagmoid_compose_holds (P : wide_submagmoid)
    {a b c : M} (f : a --> b) (g : b --> c)
    (Hf : P a b f) (Hg : P b c g)
    : P a c (f · g)
    := pr2 (wide_submagmoid_is_wide_submagmoid P) a b c f g Hf Hg.

  (** *** Wide submagmoid morphisms *)

  Definition submm_mor (P : wide_submagmoid_data) (a b : M) : UU := P a b.
  Identity Coercion Id_submm_mor : submm_mor >-> carrier.
  Coercion submm_mor_mor {P : wide_submagmoid_data} {a b : M}
    (f : submm_mor P a b) : M⟦a, b⟧ := pr1carrier _ f.
  Definition submm_mor_property (P : wide_submagmoid_data) {a b : M}
    (f : submm_mor P a b) : P a b f := pr2 f.
  Definition make_submm_mor (P : wide_submagmoid_data) {a b : M}
    (f : a --> b) (H : P a b f)
    : submm_mor P a b
    := f,, H.

  Local Notation "a '-->{' P '}' b" :=
    (submm_mor P a b) (at level 55, format "a  -->{ P }  b") : unital_magmoid.

  Lemma isaset_submm_mor' (P : wide_submagmoid_data) (a b : M)
    : isaset (a -->{P} b).
  Proof.
    apply isaset_total2.
    - apply hs.
    - intro f; apply isasetaprop, propproperty.
  Qed.

  Definition isincl_submm_mor_mor (P : wide_submagmoid_data) (a b : M)
    : isincl (λ (f : a -->{P} b), submm_mor_mor f)
    := isinclpr1carrier (P a b).

  Definition issurjective_submm_mor_mor (P : wide_submagmoid_data) (a b : M)
    (H : ∏ (f : a --> b), P a b f)
    : issurjective (λ (f : a -->{P} b), submm_mor_mor f).
  Proof.
    intro f; apply hinhpr.
    exists (make_submm_mor P f (H f)).
    reflexivity.
  Defined.

  Definition isweq_submm_mor_mor (P : wide_submagmoid_data) (a b : M)
    (H : ∏ (f : a --> b), P a b f)
    : isweq (λ (f : a -->{P} b), submm_mor_mor f).
  Proof.
    apply isweqinclandsurj.
    - apply isincl_submm_mor_mor.
    - apply issurjective_submm_mor_mor, H.
  Defined.

  Definition submm_mor_eq {P : wide_submagmoid_data} {a b : M} (f g : a -->{P} b)
    : submm_mor_mor f = g ≃ f = g.
  Proof.
    apply invweq, Injectivity, isweqonpathsincl, isincl_submm_mor_mor.
  Qed.

  Definition weq_make_submm_mor (P : wide_submagmoid_data)
    (a b : M) (H : ∏ (f : a --> b), P a b f)
    : (a --> b) ≃ (a -->{P} b)
    := invweq (make_weq _ (isweq_submm_mor_mor P a b H)).

  Definition submm_identity (P : wide_submagmoid) (a : M) : a -->{P} a
    := make_submm_mor P (identity a) (wide_submagmoid_identity_holds P a).
  Definition submm_compose (P : wide_submagmoid)
    {a b c : M} (f : a -->{P} b) (g : b -->{P} c) : a -->{P} c
    := make_submm_mor P (f · g)
         (wide_submagmoid_compose_holds P f g
            (submm_mor_property P f) (submm_mor_property P g)).

  (** *** Sub-objects *)

  Definition sub_ob (M : precategory_ob_mor) (P : hsubtype M) : UU := carrier P.
  Identity Coercion Id_sub_ob : sub_ob >-> carrier.
  Coercion sub_ob_ob {M : precategory_ob_mor} {P : hsubtype M}
    (a : sub_ob M P) : ob M := pr1carrier _ a.
  Definition sub_ob_property {M : precategory_ob_mor} (P : hsubtype M)
    (a : sub_ob M P) : P a := pr2 a.
  Definition make_sub_ob {M : precategory_ob_mor} (P : hsubtype M)
    (a : M) (H : P a)
    : sub_ob M P
    := a,, H.

  (** *** Intersection submagmoids *)

  Definition submm_includes_at
    (P Q : wide_submagmoid_data) (a b : M)
    : UU := ∏ (f : a --> b), P a b f -> Q a b f.
  Definition make_submm_includes_at
    (P Q : wide_submagmoid_data) (a b : M)
    (H : ∏ (f : a -->{P} b), Q a b f)
    : submm_includes_at P Q a b
    := λ f Hf, H (f,, Hf).

  Definition submm_includes_in
    (R : hsubtype M)
    (P Q : wide_submagmoid_data)
    : UU := ∏ (a b : sub_ob M R), submm_includes_at P Q a b.

  Definition make_submm_includes_in
    (R : hsubtype M) (P Q : wide_submagmoid_data) (a b : M)
    (H : ∏ (a b : M) (f : a -->{P} b), Q a b f)
    : submm_includes_in R P Q
    := λ a b, make_submm_includes_at P Q a b (H a b).

  Definition submm_includes (P Q : wide_submagmoid_data)
    : UU := ∏ (a b : M), submm_includes_at P Q a b.

  Definition make_submm_includes
    (P Q : wide_submagmoid_data) (a b : M)
    (H : ∏ (a b : M) (f : a -->{P} b), Q a b f)
    : submm_includes P Q
    := λ a b, make_submm_includes_at P Q a b (H a b).

  Lemma weq_submm_includes_in_trivial (P Q : wide_submagmoid_data)
    : submm_includes P Q
        ≃ submm_includes_in (totalsubtype M) P Q.
  Proof.
    apply (weqcomp (weqonsecbase _ (weqtotalsubtype M))).
    apply weqonsecfibers; intro a.
    apply (weqonsecbase _ (weqtotalsubtype M)).
  Defined.

  Definition submm_mor_incl (P Q : wide_submagmoid_data)
    {a b : M} (H : submm_includes_at P Q a b)
    (f : a -->{P} b) : a -->{Q} b
    := make_submm_mor Q f (H f (submm_mor_property P f)).

  Lemma weq_hfiber_totalfun {X : UU} (P Q : X -> UU)
    (f : ∏ x : X, P x -> Q x)
    (x : X) (y : Q x)
    : hfiber (totalfun _ _ f) (x,, y) ≃ hfiber (f x) y.
  Proof.
    intermediate_weq (∑ xy, totalfun P Q f xy ╝ x,, y).
    { apply weqfibtototal; intro.
      apply total2_paths_equiv. }
    use weq_iso.
    - intros [[x' y'] [Hx' Hy']]; cbn in Hx', Hy'.
      induction Hx'; cbn in Hy'.
      exact (y',, Hy').
    - intros [y' Hy'].
      exists (x,, y').
      exists (idpath x).
      exact Hy'.
    - intros [[x' y'] [Hx' Hy']]; cbn in Hx', Hy'.
      induction Hx'; cbn in Hy'.
      reflexivity.
    - easy.
  Defined.

  Lemma isofhlevelf_totalfun (n : nat) {X : UU} (P Q : X -> UU)
    (f : ∏ x : X, P x -> Q x)
    (H : ∏ x, isofhlevelf n (f x))
    : isofhlevelf n (totalfun _ _ f).
  Proof.
    intros [x y].
    apply (isofhlevelweqb n (Y:=hfiber (f x) y)).
    - exact (weq_hfiber_totalfun P Q f x y).
    - exact (H x y).
  Defined.

  Theorem isincl_submm_mor_incl (P Q : wide_submagmoid_data)
    {a b : M} (H : submm_includes_at P Q a b)
    : isincl (submm_mor_incl P Q H).
  Proof.
    change (isincl (totalfun _ _ H)).
    apply isofhlevelf_totalfun; intro f.
    apply isofhlevelffromXY.
    - apply propproperty.
    - apply isofhlevelsnprop, propproperty.
  Qed.

  Lemma issurjective_submm_mor_incl (P Q : wide_submagmoid_data)
    {a b : M}
    (H : submm_includes_at P Q a b)
    (Hinv : submm_includes_at Q P a b)
    : issurjective (submm_mor_incl P Q H).
  Proof.
    intros f; apply hinhpr.
    use make_hfiber.
    - exact (submm_mor_incl _ _ Hinv f).
    - now apply submm_mor_eq.
  Defined.

  Theorem isweq_submm_mor_incl (P Q : wide_submagmoid_data)
    {a b : M}
    (H : submm_includes_at P Q a b)
    (Hinv : submm_includes_at Q P a b)
    : isweq (submm_mor_incl P Q H).
  Proof.
    apply isweqinclandsurj.
    - apply isincl_submm_mor_incl.
    - apply issurjective_submm_mor_incl, Hinv.
  Defined.

  Definition weq_submm_mor_incl {P Q : wide_submagmoid_data}
    {a b : M} (H : ∏ (f : a --> b), P a b f ≃ Q a b f)
    : (a -->{P} b) ≃ (a -->{Q} b).
  Proof.
    use make_weq.
    - apply submm_mor_incl.
      exact (λ f, H f).
    - apply isweq_submm_mor_incl.
      exact (λ f, invmap (H f)).
  Defined.

  Definition is_wide_submagmoid_intersection
    (P Q : wide_submagmoid)
    : is_wide_submagmoid (λ a b f, P a b f ∧ Q a b f).
  Proof.
    use make_is_wide_submagmoid.
    - intro a; split; apply wide_submagmoid_identity_holds.
    - intros a b c f g Hf Hg.
      induction Hf, Hg.
      split; now apply wide_submagmoid_compose_holds.
  Qed.

  Definition wide_submagmoid_intersection (P Q : wide_submagmoid)
    : wide_submagmoid
    := make_wide_submagmoid _ (is_wide_submagmoid_intersection P Q).

  Local Notation "P ∩ Q" := (wide_submagmoid_intersection P Q) : unital_magmoid.

  Definition submm_mor_to_left {P Q : wide_submagmoid} {a b : M}
    : (a -->{P ∩ Q} b) -> (a -->{P} b)
    := submm_mor_incl (P ∩ Q) P (λ _, pr1).

  Definition submm_mor_from_left {P Q : wide_submagmoid}
    {a b : M} (f : a -->{P} b) (H : Q a b f)
    : a -->{P ∩ Q} b.
  Proof.
    apply (make_submm_mor _ f); split.
    - apply submm_mor_property.
    - assumption.
  Defined.

  Lemma isweq_submm_mor_to_left {P Q : wide_submagmoid} (a b : M)
    (H : ∏ (f : a -->{P} b), Q a b f)
    : isweq (λ (f : a -->{P ∩ Q} b), submm_mor_to_left f).
  Proof.
    apply isweq_submm_mor_incl.
    intros f Hf; split.
    - exact Hf.
    - exact (H (f,, Hf)).
  Defined.

  Definition submm_mor_to_right {P Q : wide_submagmoid} {a b : M}
    : (a -->{P ∩ Q} b) -> (a -->{Q} b)
    := submm_mor_incl (P ∩ Q) Q (λ _, pr2).

  Definition submm_mor_from_right {P Q : wide_submagmoid}
    {a b : M} (f : a -->{Q} b) (H : P a b f)
    : a -->{P ∩ Q} b.
  Proof.
    apply (make_submm_mor _ f); split.
    - assumption.
    - apply submm_mor_property.
  Defined.

  Lemma isweq_submm_mor_to_right {P Q : wide_submagmoid} (a b : M)
    (H : ∏ (f : a -->{Q} b), P a b f)
    : isweq (λ (f : a -->{P ∩ Q} b), submm_mor_to_right f).
  Proof.
    apply isweq_submm_mor_incl.
    intros f Hf; split.
    - exact (H (f,, Hf)).
    - exact Hf.
  Defined.

  Definition trivial_submm : wide_submagmoid.
  Proof.
    use make_wide_submagmoid.
    - intros a b; exact (totalsubtype (M⟦a, b⟧)).
    - easy.
  Defined.

  (** *** Associative wide submagmoids *)

  Definition is_assoc_wide_submagmoid (P : wide_submagmoid_data) : UU
    := ∏ (a b c d : M) (f : a --> b) (g : b --> c) (h : c --> d),
      P _ _ f -> P _ _ g -> P _ _ h ->
      f · (g · h) = (f · g) · h.

  Lemma isaprop_is_assoc_wide_submagmoid' (P : wide_submagmoid_data)
    : isaprop (is_assoc_wide_submagmoid P).
  Proof.
    do 10 (apply impred; intro).
    apply hs.
  Qed.

  Definition wide_subcategory : UU
    := ∑ (P : wide_submagmoid), is_assoc_wide_submagmoid P.
  Coercion wide_subcategory_to_submagmoid (P : wide_subcategory)
    : wide_submagmoid := pr1 P.
  Definition wide_subcategory_is_assoc (P : wide_subcategory)
    : is_assoc_wide_submagmoid P := pr2 P.

  Definition make_wide_subcategory (P : wide_submagmoid)
    (H : is_assoc_wide_submagmoid P)
    : wide_subcategory
    := P,, H.

  Lemma is_assoc_wide_submagmoid_intersection_left
    (P Q : wide_submagmoid)
    (H : is_assoc_wide_submagmoid P)
    : is_assoc_wide_submagmoid (wide_submagmoid_intersection P Q).
  Proof.
    intros a b c d f g h Hf Hg Hh.
    apply H.
    - exact (pr1 Hf).
    - exact (pr1 Hg).
    - exact (pr1 Hh).
  Qed.

  Lemma is_assoc_wide_submagmoid_intersection_right
    (P Q : wide_submagmoid)
    (H : is_assoc_wide_submagmoid Q)
    : is_assoc_wide_submagmoid (wide_submagmoid_intersection P Q).
  Proof.
    intros a b c d f g h Hf Hg Hh.
    apply H.
    - exact (pr2 Hf).
    - exact (pr2 Hg).
    - exact (pr2 Hh).
  Qed.

End submagmoids.
Arguments wide_submagmoid_data _ : clear implicits.
Arguments wide_submagmoid _ : clear implicits.
Arguments wide_subcategory _ : clear implicits.

Lemma isaset_submm_mor {M : unital_magmoid}
  (P : wide_submagmoid_data M) (a b : M) : isaset (P a b).
Proof.
  apply isaset_submm_mor'.
  apply unital_magmoid_has_homsets.
Qed.

Lemma isaprop_is_assoc_wide_submagmoid {M : unital_magmoid}
  (P : wide_submagmoid_data M)
  : isaprop (is_assoc_wide_submagmoid P).
Proof.
  apply isaprop_is_assoc_wide_submagmoid'.
  apply unital_magmoid_has_homsets.
Qed.

Notation "a '-->{' P '}' b" :=
  (submm_mor P a b) (at level 55, format "a  -->{ P }  b") : unital_magmoid.
Notation "a '<--{' P '}' b" :=
  (submm_mor P b a) (at level 55, only parsing) : unital_magmoid.
Notation "M '∣' P '∣⟦' a ',' b '⟧'" :=
  (submm_mor (M:=M) P a b)
    (at level 49, right associativity,
      format "M ∣ P ∣⟦  a ,  b  ⟧") : unital_magmoid.
Notation "f '∘{' P '}' g" :=
  (submm_compose P g f) (at level 40, left associativity, format "f  ∘{ P }  g") : unital_magmoid.
Notation "f '·{' P '}' g" :=
  (submm_compose P f g) (at level 40, left associativity, format "f  ·{ P }  g") : unital_magmoid.

(** ** Submagmoids to magmoids *)

Section submagmoid_to_magmoid.
  (** *** Wide submagmoid to magmoid *)

  Definition wide_submagmoid_carrier_data
    (M : unital_premagmoid_data) (P : wide_submagmoid M)
    : unital_premagmoid_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact (ob M).
      + exact (λ a b, a -->{P} b).
    - apply submm_identity.
    - apply submm_compose.
  Defined.

  Definition wide_submagmoid_has_homsets
    (M : unital_magmoid) (P : wide_submagmoid M)
    : has_homsets (wide_submagmoid_carrier_data M P).
  Proof.
    intros a b; cbn.
    apply isaset_submm_mor', unital_magmoid_has_homsets.
  Defined.

  Definition wide_submagmoid_is_unital
    (M : unital_premagmoid) (P : wide_submagmoid M)
    : is_unital_premagmoid (wide_submagmoid_carrier_data M P).
  Proof.
    use make_is_unital_premagmoid.
    - intros a b f; apply submm_mor_eq, magmoid_id_left.
    - intros a b f; apply submm_mor_eq, magmoid_id_right.
  Defined.

  Definition wide_sub_premagmoid_carrier
    (M : unital_premagmoid) (P : wide_submagmoid M)
    : unital_premagmoid
    := make_unital_premagmoid _ (wide_submagmoid_is_unital M P).

  Definition wide_submagmoid_carrier
    (M : unital_magmoid) (P : wide_submagmoid M)
    : unital_magmoid
    := make_unital_magmoid (wide_sub_premagmoid_carrier M P)
         (wide_submagmoid_has_homsets M P).

  Definition wide_submagmoid_is_assoc_iff
    (M : unital_premagmoid_data) (P : wide_submagmoid M)
    : is_assoc_wide_submagmoid P
        <-> is_assoc_premagmoid (wide_submagmoid_carrier_data M P).
  Proof.
    split.
    - intros H; apply make_is_one_assoc_premagmoid; intros a b c d f g h.
      apply submm_mor_eq, H;
        apply submm_mor_property.
    - intros H; intros a b c d f g h Hf Hg Hh.
      exact (base_paths _ _ (pr1 H a b c d (f,,Hf) (g,,Hg) (h,,Hh))).
  Defined.

  Definition wide_subcategory_is_assoc_premagmoid
    (M : unital_premagmoid) (P : wide_subcategory M)
    : is_assoc_premagmoid (wide_submagmoid_carrier_data M P).
  Proof.
    apply wide_submagmoid_is_assoc_iff.
    apply wide_subcategory_is_assoc.
  Defined.

  Definition wide_subcategory_is_precategory
    (M : unital_premagmoid) (P : wide_subcategory M)
    : is_precategory (wide_submagmoid_carrier_data M P).
  Proof.
    split.
    - apply wide_submagmoid_is_unital.
    - apply wide_subcategory_is_assoc_premagmoid.
  Qed.

  Definition wide_sub_precategory_carrier
    (M : unital_premagmoid) (P : wide_subcategory M)
    : precategory
    := make_precategory _ (wide_subcategory_is_precategory M P).

  Definition wide_subcategory_carrier
    (M : unital_magmoid) (P : wide_subcategory M)
    : category
    := make_category (wide_sub_precategory_carrier M P)
         (wide_submagmoid_has_homsets M P).

  (** *** Full submagmoid to magmoid *)

  Definition full_unital_sub_premagmoid_data
    (M : unital_premagmoid_data) (P : hsubtype M)
    : unital_premagmoid_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact (sub_ob M P).
      + exact (@precategory_morphisms M).
    - cbn; intro a.
      exact (@identity M a).
    - cbn; intros a b c.
      exact (@compose M a b c).
  Defined.

  Definition full_unital_sub_premagmoid
    (M : unital_premagmoid) (P : hsubtype M)
    : unital_premagmoid.
  Proof.
    apply (make_unital_premagmoid (full_unital_sub_premagmoid_data M P)).
    split; cbn; intros a b.
    - exact (@magmoid_id_left M a b).
    - exact (@magmoid_id_right M a b).
  Defined.

  Definition full_unital_submagmoid_carrier
    (M : unital_magmoid) (P : hsubtype M)
    : unital_magmoid.
  Proof.
    apply (make_unital_magmoid (full_unital_sub_premagmoid M P)).
    red; cbn; intros a b.
    exact (unital_magmoid_has_homsets M a b).
  Defined.

  (** *** Arbitrary submagmoids *)

  Definition full_submagmoid_promote
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q : wide_submagmoid M)
    : wide_submagmoid (full_unital_sub_premagmoid_data M P).
  Proof.
    use make_wide_submagmoid.
    - intros a b; cbn in a, b.
      exact (Q a b).
    - use make_is_wide_submagmoid.
      + intro a; cbn in a.
        exact (wide_submagmoid_identity_holds Q a).
      + intros a b c f g; cbn in a, b, c, f, g.
        exact (wide_submagmoid_compose_holds Q f g).
  Defined.

  Definition full_subcategory_promote
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q : wide_subcategory M)
    : wide_subcategory (full_unital_sub_premagmoid_data M P).
  Proof.
    use make_wide_subcategory.
    - exact (full_submagmoid_promote M P Q).
    - red; cbn; intros a b c d.
      exact (wide_subcategory_is_assoc Q a b c d).
  Defined.

  Definition associative_submagmoid_carrier
    (M : unital_magmoid)
    (P : hsubtype M)
    (Q : wide_subcategory M)
    : category
    := wide_subcategory_carrier
         (full_unital_submagmoid_carrier M P)
         (full_subcategory_promote M P Q).

End submagmoid_to_magmoid.

Section submagmoid_to_magmoid_functors.

  (** Inclusion from submagmoid into the base *)

  Definition wide_submm_trivial_incl
    (M : unital_premagmoid_data) (P : wide_submagmoid M)
    : functor (wide_submagmoid_carrier_data M P) M.
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact (idfun M).
      + exact (@submm_mor_mor M P).
    - easy.
  Defined.

  Theorem faithful_wide_submm_trivial_incl
    (M : unital_premagmoid_data) (P : wide_submagmoid M)
    : faithful (wide_submm_trivial_incl M P).
  Proof.
    intros a b.
    apply isincl_submm_mor_mor.
  Qed.

  Lemma full_wide_submm_trivial_incl
    (M : unital_premagmoid_data) (P : wide_submagmoid M)
    (H : ∏ (a b : M) (f : a --> b), P a b f)
    : full (wide_submm_trivial_incl M P).
  Proof.
    intros a b f; apply hinhpr.
    exists (make_submm_mor P f (H a b f)).
    reflexivity.
  Qed.

  Theorem fully_faithful_wide_submm_trivial_incl
    (M : unital_premagmoid_data) (P : wide_submagmoid M)
    (H : ∏ (a b : M) (f : a --> b), P a b f)
    : fully_faithful (wide_submm_trivial_incl M P).
  Proof.
    apply full_and_faithful_implies_fully_faithful; split.
    - apply full_wide_submm_trivial_incl, H.
    - apply faithful_wide_submm_trivial_incl.
  Defined.

  Corollary is_catiso_wide_submm_trivial_incl
    (M : unital_premagmoid_data) (P : wide_submagmoid M)
    (H : ∏ (a b : M) (f : a --> b), P a b f)
    : is_catiso (wide_submm_trivial_incl M P).
  Proof.
    split.
    - apply fully_faithful_wide_submm_trivial_incl, H.
    - apply idisweq.
  Defined.

  (** Inclusion between submagmoids *)

  Definition wide_submm_incl
    (M : unital_premagmoid_data)
    (P Q : wide_submagmoid M)
    (H : submm_includes P Q)
    : functor (wide_submagmoid_carrier_data M P)
        (wide_submagmoid_carrier_data M Q).
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact (idfun M).
      + cbn; intros a b.
        exact (submm_mor_incl P Q (H a b)).
    - use make_is_functor.
      + intro a; cbn.
        now apply submm_mor_eq.
      + intros a b c f g; cbn.
        now apply submm_mor_eq.
  Defined.

  Lemma faithful_wide_submm_incl
    (M : unital_premagmoid_data)
    (P Q : wide_submagmoid M)
    (H : submm_includes P Q)
    : faithful (wide_submm_incl M P Q H).
  Proof.
    intros a b.
    apply isincl_submm_mor_incl.
  Qed.

  Theorem fully_faithful_wide_submm_incl
    (M : unital_premagmoid_data)
    (P Q : wide_submagmoid M)
    (H    : submm_includes P Q)
    (Hinv : submm_includes Q P)
    : fully_faithful (wide_submm_incl M P Q H).
  Proof.
    intros a b.
    apply isweq_submm_mor_incl, Hinv.
  Defined.

  Corollary is_catiso_wide_submm_incl
    (M : unital_premagmoid_data)
    (P Q : wide_submagmoid M)
    (H : submm_includes P Q)
    (Hinv : submm_includes Q P)
    : is_catiso (wide_submm_incl M P Q H).
  Proof.
    split.
    - apply fully_faithful_wide_submm_incl, Hinv.
    - apply idisweq.
  Defined.

  Definition wide_submm_incl_catiso
    (M : unital_premagmoid_data)
    (P Q : wide_submagmoid M)
    (H : submm_includes P Q)
    (Hinv : submm_includes Q P)
    : catiso (wide_submagmoid_carrier_data M P)
        (wide_submagmoid_carrier_data M Q)
    := _,, is_catiso_wide_submm_incl M P Q H Hinv.

  Definition trivial_submm_catiso
    (M : unital_premagmoid_data)
    : catiso (wide_submagmoid_carrier_data M trivial_submm) M.
  Proof.
    use tpair.
    - use make_functor.
      + use make_functor_data.
        * exact (idweq M).
        * intros a b.
          exact (weqtotalsubtype (M⟦a, b⟧)).
      + easy.
    - split.
      + intros a b; apply weqproperty.
      + intros a; apply weqproperty.
  Defined.

  (** Full submagmoid inclusions *)

  Definition full_submm_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    : functor (full_unital_sub_premagmoid_data M P) M.
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact sub_ob_ob.
      + intros a b; cbn in a, b.
        exact (idfun (M⟦a, b⟧)).
    - easy.
  Defined.

  Lemma fully_faithful_full_submm_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    : fully_faithful (full_submm_incl M P).
  Proof.
    intros a b.
    apply idisweq.
  Defined.

  Definition full_submm_into_other_incl
    (M : unital_premagmoid_data)
    (P Q : hsubtype M)
    (H : subtype_containedIn P Q)
    : functor (full_unital_sub_premagmoid_data M P)
        (full_unital_sub_premagmoid_data M Q).
  Proof.
    use make_functor.
    - use make_functor_data.
      + cbn; intro a.
        apply (make_sub_ob Q a).
        exact (H a (sub_ob_property P a)).
      + intros a b; cbn in a, b.
        exact (idfun (M⟦a, b⟧)).
    - easy.
  Defined.

  Lemma fully_faithful_full_submm_into_other_incl
    (M : unital_premagmoid_data)
    (P Q : hsubtype M)
    (H : subtype_containedIn P Q)
    : fully_faithful (full_submm_into_other_incl M P Q H).
  Proof.
    intros a b.
    apply idisweq.
  Defined.

  Lemma isweq_full_submm_into_other_incl
    (M : unital_premagmoid_data)
    (P Q : hsubtype M)
    (H : subtype_containedIn P Q)
    (Hinv : subtype_containedIn Q P)
    : isweq (full_submm_into_other_incl M P Q H).
  Proof.
    use weqhomot.
    - apply weqfibtototal; intro a.
      apply weqimplimpl.
      + apply (H a).
      + apply (Hinv a).
      + apply propproperty.
      + apply propproperty.
    - easy.
  Defined.

  Corollary is_catiso_full_submm_into_other_incl
    (M : unital_premagmoid_data)
    (P Q : hsubtype M)
    (H : subtype_containedIn P Q)
    (Hinv : subtype_containedIn Q P)
    : is_catiso (full_submm_into_other_incl M P Q H).
  Proof.
    split.
    - apply fully_faithful_full_submm_into_other_incl.
    - now apply isweq_full_submm_into_other_incl.
  Defined.

  (** Arbitrary submagmoid inclusions *)

  Definition submm_into_wide_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q : wide_submagmoid M)
    : functor
        (wide_submagmoid_carrier_data
           (full_unital_sub_premagmoid_data M P)
           (full_submagmoid_promote M P Q))
        (wide_submagmoid_carrier_data M Q).
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact sub_ob_ob.
      + intros a b; cbn in a, b.
        exact (idfun (M∣Q∣⟦a, b⟧)).
    - easy.
  Defined.

  Theorem fully_faithful_submm_into_wide_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q : wide_submagmoid M)
    : fully_faithful (submm_into_wide_incl M P Q).
  Proof.
    intros a b.
    apply idisweq.
  Defined.

  (** Note: this is not the most general form; [H] could be strengthened to take
      [sub_ob P] (but it would no longer factor through [wide_submm_incl]). *)
  Definition submm_into_other_wide_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q₁ Q₂ : wide_submagmoid M)
    (H : submm_includes Q₁ Q₂)
    : functor
        (wide_submagmoid_carrier_data
           (full_unital_sub_premagmoid_data M P)
           (full_submagmoid_promote M P Q₁))
        (wide_submagmoid_carrier_data M Q₂)
    := submm_into_wide_incl M P Q₁
         ∙ wide_submm_incl M Q₁ Q₂ H.

  Theorem faithful_submm_into_other_wide_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q₁ Q₂ : wide_submagmoid M)
    (H : submm_includes Q₁ Q₂)
    : faithful (submm_into_other_wide_incl M P Q₁ Q₂ H).
  Proof.
    apply comp_faithful_is_faithful.
    - apply fully_faithful_implies_full_and_faithful.
      apply fully_faithful_submm_into_wide_incl.
    - apply faithful_wide_submm_incl.
  Qed.

  Lemma full_submm_into_other_wide_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q₁ Q₂ : wide_submagmoid M)
    (H : submm_includes Q₁ Q₂)
    (Hinv : submm_includes_in P Q₂ Q₁)
    : full (submm_into_other_wide_incl M P Q₁ Q₂ H).
  Proof.
    intros a b; cbn in a, b.
    change (issurjective (submm_mor_incl Q₁ Q₂ (H a b))).
    apply issurjective_submm_mor_incl, Hinv.
  Defined.

  Theorem fully_faithful_submm_into_other_wide_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q₁ Q₂ : wide_submagmoid M)
    (H : submm_includes Q₁ Q₂)
    (Hinv : submm_includes_in P Q₂ Q₁)
    : fully_faithful (submm_into_other_wide_incl M P Q₁ Q₂ H).
  Proof.
    apply full_and_faithful_implies_fully_faithful; split.
    - apply full_submm_into_other_wide_incl, Hinv.
    - apply faithful_submm_into_other_wide_incl.
  Defined.

  Definition submm_trivial_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q : wide_submagmoid M)
    : functor
        (wide_submagmoid_carrier_data
           (full_unital_sub_premagmoid_data M P)
           (full_submagmoid_promote M P Q))
        M
    := submm_into_wide_incl M P Q
         ∙ wide_submm_trivial_incl M Q.

  Theorem faithful_submm_trivial_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q : wide_submagmoid M)
    : faithful (submm_trivial_incl M P Q).
  Proof.
    apply comp_faithful_is_faithful.
    - apply fully_faithful_implies_full_and_faithful.
      apply fully_faithful_submm_into_wide_incl.
    - apply faithful_wide_submm_trivial_incl.
  Defined.

  Lemma full_submm_trivial_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q : wide_submagmoid M)
    (H : ∏ (a b : sub_ob M P) (f : a --> b), Q a b f)
    : full (submm_trivial_incl M P Q).
  Proof.
    intros a b; cbn in a, b.
    change (issurjective (@submm_mor_mor M Q a b)).
    apply issurjective_submm_mor_mor, H.
  Defined.

  Theorem fully_faithful_submm_trivial_incl
    (M : unital_premagmoid_data)
    (P : hsubtype M)
    (Q : wide_submagmoid M)
    (H : ∏ (a b : sub_ob M P) (f : a --> b), Q a b f)
    : fully_faithful (submm_trivial_incl M P Q).
  Proof.
    apply full_and_faithful_implies_fully_faithful; split.
    - apply full_submm_trivial_incl, H.
    - apply faithful_submm_trivial_incl.
  Defined.

  (** Even more arbitrary submagmoid inclusions *)
  Definition submm_into_other_incl
    (M : unital_premagmoid_data)
    (P₁ P₂ : hsubtype M)
    (Q₁ Q₂ : wide_submagmoid M)
    (HP : subtype_containedIn P₁ P₂)
    (HQ : ∏ (a b : sub_ob M P₁),
        submm_includes_at Q₁ Q₂ a b)
    : functor
        (wide_submagmoid_carrier_data
           (full_unital_sub_premagmoid_data M P₁)
           (full_submagmoid_promote M P₁ Q₁))
        (wide_submagmoid_carrier_data
           (full_unital_sub_premagmoid_data M P₂)
           (full_submagmoid_promote M P₂ Q₂)).
  Proof.
    use make_functor.
    - use make_functor_data.
      + cbn; intro a.
        apply (make_sub_ob _ a).
        exact (HP a (sub_ob_property _ a)).
      + cbn; intros a b.
        exact (submm_mor_incl _ _ (HQ a b)).
    - split.
      + intro a; now apply submm_mor_eq.
      + intros a b c f g; now apply submm_mor_eq.
  Defined.

  Definition fully_faithful_submm_into_other_incl
    (M : unital_premagmoid_data)
    (P₁ P₂ : hsubtype M)
    (Q₁ Q₂ : wide_submagmoid M)
    (HP : subtype_containedIn P₁ P₂)
    (HQ : ∏ (a b : sub_ob M P₁),
        submm_includes_at Q₁ Q₂ a b)
    (HQinv : ∏ (a b : sub_ob M P₁),
        submm_includes_at Q₂ Q₁ a b)
    : fully_faithful (submm_into_other_incl M P₁ P₂ Q₁ Q₂ HP HQ).
  Proof.
    red; cbn; intros a b.
    change (isweq (totalfun _ _ (HQ a b))).
    apply (isofhlevelf_totalfun 0); intro f.
    apply isweqimplimpl.
    - apply (HQinv a b).
    - apply propproperty.
    - apply propproperty.
  Defined.

End submagmoid_to_magmoid_functors.
