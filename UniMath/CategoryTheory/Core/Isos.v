(** * Isomorphisms *)

(** ** Contents

  - isomorphisms: [iso], [isiso f := isweq (precomp_with f)]
  - Equivalence relation identifying isomorphic objects
  - Isomorphisms in a category [z_iso]
    - Definition: [is_z_iso f := ∑ g, ...]
    - Relationship between [z_iso] and [iso]
  - Properties of 0-isomorphisms
    - uniqueness of inverse, composition etc.
    - stability under composition
    - Analogue to [isweq_iso]: [is_iso_qinv]
 *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

(** A morphism [f: a --> b] in a precategory is an isomorphism [is_iso(f)],
    if for any [c: C], precomposition with [f] yields an equivalence
    (b --> c -> a --> c].
    Definition suggested by V. Voevodsky
*)

Definition precomp_with {C : precategory_data} {a b : C} (f : a --> b) {c : C} (g : b --> c): a --> c :=
   f · g.

Definition is_iso {C : precategory_data} {a b : C} (f : a --> b) :=
  ∏ c, isweq (precomp_with f (c:=c)).

Lemma isaprop_is_iso {C : precategory_data} (a b : C) (f : a --> b) : isaprop (is_iso f).
Proof.
  apply impred; intro.
  apply isapropisweq.
Qed.

Definition iso {C: precategory_data} (a b : C) := ∑ f : a --> b, is_iso f.
Definition morphism_from_iso {C : precategory_data} {a b : C} (f : iso a b) : a --> b := pr1 f.
Coercion morphism_from_iso : iso >-> precategory_morphisms.

Definition iso_is_iso {C : precategory_data} {a b : C} (f : iso a b) : is_iso f := pr2 f.

Definition make_iso {C : precategory_data} {a b : C} (f : a --> b) (fiso: is_iso f) : iso a b := (f,,fiso).

Definition inv_from_iso {C : precategory_data} {a b : C} (f : iso a b) : b --> a :=
   invmap (make_weq (precomp_with f) (pr2 f a)) (identity _ ).

Definition iso_inv_after_iso {C : precategory_data} {a b : C} (f: iso a b) :
   f · inv_from_iso f = identity _ .
Proof.
  set (T := homotweqinvweq (make_weq (precomp_with f) (pr2 f a ))).
  simpl in *.
  apply T.
Defined.

Definition iso_after_iso_inv {C : precategory} {a b : C} (f : iso a b) :
  inv_from_iso f · f = identity _ .
Proof.
  set (T := invmaponpathsweq (make_weq (precomp_with f) (pr2 f b))).
  apply T; clear T; simpl.
  unfold precomp_with.
  intermediate_path ((f · inv_from_iso f) · f).
  - apply assoc.
  - apply remove_id_left.
    + apply iso_inv_after_iso.
    + apply (!(id_right _ )).
Defined.

Definition is_iso_inv_from_iso {C : precategory} {a b : C} (f : iso a b) : is_iso (inv_from_iso f).
Proof.
  intro c.
  apply (isweq_iso _ (precomp_with f)).
  - intro g.
    unfold precomp_with.
    intermediate_path ((f · inv_from_iso f) · g).
    + apply assoc.
    + apply remove_id_left. apply iso_inv_after_iso. apply idpath.
  - intro g.
    unfold precomp_with.
    intermediate_path ((inv_from_iso f · f) · g).
    + apply assoc.
    + apply remove_id_left. apply iso_after_iso_inv. apply idpath.
Defined.

Definition iso_inv_from_iso {C : precategory} {a b : C} (f : iso a b) : iso b a :=
  tpair _ _ (is_iso_inv_from_iso f).

Lemma eq_iso {C: precategory_data} {a b : C} (f g : iso a b) : pr1 f = pr1 g -> f = g.
Proof.
  intro H.
  apply subtypePath.
  - intros t. apply isaprop_is_iso.
  - apply H.
Defined.

Lemma isaset_iso {C : precategory_data} (hs : has_homsets C) (a b : ob C) :
  isaset (iso a b).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  - apply hs.
  - intro f.
    apply isasetaprop.
    apply isaprop_is_iso.
Qed.

Lemma identity_is_iso (C : precategory) (a : ob C) : is_iso (identity a).
Proof.
  intros c.
  set (T := @isweqhomot (a --> c) (a --> c) (λ t, t) (precomp_with (identity a))).
  apply T.
  - intro g. apply pathsinv0. apply id_left.
  - apply idisweq.
Defined.

Definition identity_iso {C : precategory} (a : ob C) :
   iso a a := tpair _ _ (identity_is_iso C a).


Definition iso_inv_from_is_iso {C : precategory} {a b : ob C}
  (f : a --> b) (H : is_iso f) : iso b a :=
  iso_inv_from_iso (f,,H).

Lemma iso_inv_on_right {C : precategory} (a b c : ob C)
  (f : iso a  b) (g : b --> c) (h : a --> c) (H : h = f · g) :
     inv_from_iso f · h = g.
Proof.
  apply (invmaponpathsweq (make_weq (precomp_with f) (pr2 f c))).
  unfold precomp_with; simpl.
  intermediate_path ((f · inv_from_iso f) · h).
  - apply assoc.
  - apply remove_id_left.
    + apply iso_inv_after_iso.
    + assumption.
Defined.

Lemma iso_inv_on_left {C : precategory} (a b c : ob C)
  (f : a --> b) (g : iso b c) (h : a --> c) (H : h = f · g) :
     f = h · inv_from_iso g.
Proof.
  assert (H2 : h · inv_from_iso g =
                         (f · g) · inv_from_iso g).
    rewrite H. apply idpath.
  rewrite <- assoc in H2.
  rewrite iso_inv_after_iso in H2.
  rewrite id_right in H2.
  apply pathsinv0.
  assumption.
Qed.

Lemma iso_inv_to_left {C : precategory} (a b c : ob C)
  (f : iso a  b) (g : b --> c) (h : a --> c) :
    inv_from_iso f · h = g -> h = f · g.
Proof.
  intro H.
  intermediate_path (f · inv_from_iso f · h).
  - rewrite iso_inv_after_iso, id_left; apply idpath.
  - rewrite <- assoc. rewrite H. apply idpath.
Qed.

Lemma iso_inv_to_right {C : precategory} (a b c : ob C)
  (f : a --> b) (g : iso b c) (h : a --> c) :
     f = h · inv_from_iso g -> f · g = h.
Proof.
  intro H.
  intermediate_path (h · inv_from_iso g · g).
  - rewrite H. apply idpath.
  - rewrite <- assoc, iso_after_iso_inv, id_right. apply idpath.
Qed.


(** ** Properties of isomorphisms *)
(** Stability under composition, inverses etc *)

Definition isweqhomot' {X Y} (f g : X -> Y) (H : isweq f)
      (homot : ∏ x, f x = g x) : isweq g.
Proof.
  apply (isweqhomot f g homot H).
Defined.

Lemma is_iso_comp_of_isos {C : precategory} {a b c : ob C}
  (f : iso a b) (g : iso b c) : is_iso (f · g).
Proof.
  simpl.
  intro d.
  set (T := twooutof3c (precomp_with g) (precomp_with f (c:=d)) (pr2 g d) (pr2 f _)).
  apply (isweqhomot' _ _ T).
  intro h. apply assoc.
Defined.

Lemma is_iso_comp_of_is_isos {C : precategory} {a b c : ob C}
      (f : a --> b) (g : b --> c) (H1 : is_iso f) (H2 : is_iso g) : is_iso (f · g).
Proof.
  set (i1 := make_iso f H1).
  set (i2 := make_iso g H2).
  exact (is_iso_comp_of_isos i1 i2).
Qed.

Definition iso_comp {C : precategory} {a b c : ob C}
  (f : iso a b) (g : iso b c) : iso a c.
Proof.
  exists (f · g).
  apply is_iso_comp_of_isos.
Defined.


Lemma inv_iso_unique (C : precategory) (a b : C) (f : iso a b) (g : iso b a) :
  precomp_with f g = identity _ -> g = iso_inv_from_iso f.
Proof.
  intro H.
  apply eq_iso. simpl.
  set (T := invmaponpathsweq (make_weq (precomp_with f) (pr2 f a ))).
  apply T; simpl.
  intermediate_path (identity a).
  + assumption.
  + apply pathsinv0. apply iso_inv_after_iso.
Defined.

Lemma inv_iso_unique' (C : precategory) (a b : C) (f : iso a b) (g : b --> a) :
  precomp_with f g = identity _ -> g = inv_from_iso f.
Proof.
  intro H.
  set (T := invmaponpathsweq (make_weq (precomp_with f) (pr2 f a ))).
  apply T; simpl.
  intermediate_path (identity a).
  + assumption.
  + apply pathsinv0. apply iso_inv_after_iso.
Defined.


Lemma iso_inv_of_iso_comp (C : precategory) (a b c : ob C)
   (f : iso a b) (g : iso b c) :
   iso_inv_from_iso (iso_comp f g) = iso_comp (iso_inv_from_iso g) (iso_inv_from_iso f).
Proof.
  apply pathsinv0.
  apply inv_iso_unique. simpl. unfold precomp_with.
  intermediate_path (f · (g · inv_from_iso g) · inv_from_iso f).
  - repeat rewrite assoc.  apply idpath.
  - rewrite iso_inv_after_iso. rewrite id_right.
    apply iso_inv_after_iso.
Qed.

Lemma iso_inv_of_iso_id {C : precategory} (a : ob C) :
   iso_inv_from_iso (identity_iso a) = identity_iso a.
Proof.
  apply eq_iso.
  apply idpath.
Qed.


Lemma iso_inv_iso_inv {C : precategory} (a b : ob C) (f : iso a b) :
     iso_inv_from_iso (iso_inv_from_iso f) = f.
Proof.
  apply eq_iso. simpl.
  apply pathsinv0.
  apply inv_iso_unique'.
  apply iso_after_iso_inv.
Defined.

Lemma pre_comp_with_iso_is_inj {C : precategory_data} (a b c : ob C)
    (f : a --> b) (H : is_iso f) (g h : b --> c) : f · g = f · h -> g = h.
Proof.
  intro X.
  apply (invmaponpathsweq (make_weq (precomp_with f) (H _ ))).
  apply X.
Qed.

Lemma post_comp_with_iso_is_inj {C : precategory} (b c : ob C)
     (h : b --> c) (H : is_iso h)
   (a : ob C) (f g : a --> b) : f · h = g · h -> f = g.
Proof.
  intro HH.
  set (T := iso_inv_after_iso (h,,H)). simpl in T.
  intermediate_path (f · (h · inv_from_iso (h,,H))).
  - rewrite T. clear T.
    apply pathsinv0, id_right.
  - rewrite assoc. rewrite HH.
    rewrite <- assoc. rewrite T.
    apply id_right.
Qed.


Lemma iso_comp_right_isweq {C : precategory_data} {a b : ob C} (h : iso a b) (c : C) :
  isweq (fun f : b --> c => h · f).
Proof.
  apply (pr2 h _ ).
Defined.

Definition iso_comp_right_weq {C : precategory_data} {a b : C} (h : iso a b) (c : C) :
 (b --> c) ≃ (a --> c) := make_weq _ (iso_comp_right_isweq h c).

Lemma iso_comp_left_isweq {C : precategory} {a b : ob C} (h : iso a b) (c : C) :
  isweq (fun f : c --> a => f · h).
Proof.
  intros. apply (isweq_iso _ (λ g, g · inv_from_iso h)).
  - intro x. rewrite <- assoc. apply remove_id_right.
    apply iso_inv_after_iso. apply idpath.
  - intro y. rewrite <- assoc. apply remove_id_right.
    apply iso_after_iso_inv. apply idpath.
Defined.

Definition postcomp_with {C : precategory_data} {b c : C} (h : b --> c) {a : C}
  (f : a --> b) : a --> c := f · h.

Definition is_iso' {C : precategory} {b c : C} (f : b --> c) :=
  ∏ a, isweq (postcomp_with f (a:=a)).

Definition is_inverse_in_precat {C : precategory_data} {a b : C}
  (f : a --> b) (g : b --> a) :=
          (f · g = identity a) ×
          (g · f = identity b).

Definition make_is_inverse_in_precat {C : precategory_data} {a b : C} {f : a --> b} {g : b --> a}
           (H1 : f · g = identity a) (H2 : g · f = identity b) :
  is_inverse_in_precat f g := (H1,,H2).

Definition is_inverse_in_precat1 {C : precategory_data} {a b : C} {f : a --> b} {g : b --> a}
           (H : is_inverse_in_precat f g) :
  f · g = identity a := dirprod_pr1 H.

Definition is_inverse_in_precat2 {C : precategory_data} {a b : C} {f : a --> b} {g : b --> a}
           (H : is_inverse_in_precat f g) :
  g · f = identity b := dirprod_pr2 H.

Definition is_inverse_in_precat_inv {C : precategory_data} {a b : C} {f : a --> b} {g : b --> a}
           (H : is_inverse_in_precat f g) : is_inverse_in_precat g f :=
  make_dirprod (is_inverse_in_precat2 H) (is_inverse_in_precat1 H).

Definition is_inverse_in_precat_comp {C : precategory} {a b c : C} {f1 : a --> b} {f2 : b --> c}
           {g1 : b --> a} {g2 : c --> b} (H1 : is_inverse_in_precat f1 g1)
           (H2 : is_inverse_in_precat f2 g2) : is_inverse_in_precat (f1 · f2) (g2 · g1).
Proof.
  use make_is_inverse_in_precat.
  - rewrite assoc. rewrite <- (assoc _ f2). rewrite (is_inverse_in_precat1 H2). rewrite id_right.
    rewrite (is_inverse_in_precat1 H1). apply idpath.
  - rewrite assoc. rewrite <- (assoc _ g1). rewrite (is_inverse_in_precat2 H1). rewrite id_right.
    rewrite (is_inverse_in_precat2 H2). apply idpath.
Qed.

Definition is_inverse_in_precat_identity {C : precategory} (c : C) :
  is_inverse_in_precat (identity c) (identity c).
Proof.
  use make_is_inverse_in_precat.
  - apply id_left.
  - apply id_left.
Qed.

Definition is_iso_qinv {C:precategory} {a b : C} (f : a --> b) (g : b --> a) :
  is_inverse_in_precat f g -> is_iso f.
Proof.
  intros H c.
  apply (isweq_iso _ (precomp_with g)).
  - intro h. unfold precomp_with.
    rewrite assoc.
    apply remove_id_left.
    apply (pr2 H). apply idpath.
  - intro h. unfold precomp_with. rewrite assoc.
    apply remove_id_left.
    apply (pr1 H). apply idpath.
Defined.

Definition iso_comp_left_weq {C : precategory} {a b : C} (h : iso a b) (c : C) :
 (c --> a) ≃ (c --> b) := make_weq _ (iso_comp_left_isweq h c).

Definition iso_conjug_weq {C : precategory} {a b : C} (h : iso a b) :
 (a --> a) ≃ (b --> b) := weqcomp (iso_comp_left_weq h _ ) (iso_comp_right_weq (iso_inv_from_iso h) _ ).


(** ** Equivalence relation identifying isomorphic objects *)

Section are_isomorphic.

  Context {C : precategory}.

  (** a and b are related if there merely exists an iso between them *)
  Definition are_isomorphic : hrel C := λ a b, ∥iso a b∥.

  Lemma iseqrel_are_isomorphic : iseqrel are_isomorphic.
  Proof.
  repeat split.
  - intros x y z h1.
    apply hinhuniv; intros h2; generalize h1; clear h1.
    now apply hinhuniv; intros h1; apply hinhpr, (iso_comp h1 h2).
  - now intros x; apply hinhpr, identity_iso.
  - now intros x y; apply hinhuniv; intro h1; apply hinhpr, iso_inv_from_iso.
  Qed.

  Definition iso_eqrel : eqrel C := (are_isomorphic,,iseqrel_are_isomorphic).

End are_isomorphic.


(** ** Isomorphisms in a category [z_iso] *)

(** In a precategory with hom-sets, we can give the usual definition of
    isomorphism, called [z_iso] in the following.
*)

Lemma isaprop_is_inverse_in_precat {C : category} (a b : ob C)
   (f : a --> b) (g : b --> a) : isaprop (is_inverse_in_precat f g).
Proof.
  apply isapropdirprod; apply homset_property.
Qed.

Lemma inverse_unique_precat {C : precategory} (a b : ob C)
   (f : a --> b) (g g': b --> a) (H : is_inverse_in_precat f g)
    (H' : is_inverse_in_precat f g') : g = g'.
Proof.
  destruct H as [eta eps].
  destruct H' as [eta' eps'].
  assert (H : g = identity b · g).
    rewrite id_left; apply idpath.
  apply (pathscomp0 H).
  rewrite <- eps'.
  rewrite <- assoc.
  rewrite eta.
  apply id_right.
Qed.

Definition is_z_isomorphism {C : precategory_data} {a b : ob C}
           (f : a --> b) := ∑ g, is_inverse_in_precat f g.

Definition make_is_z_isomorphism {C : precategory_data} {a b : C} (f : a --> b)
           (g : b --> a) (H : is_inverse_in_precat f g) : is_z_isomorphism f := (g,,H).

Definition is_z_isomorphism_mor {C : precategory_data} {a b : C} {f : a --> b}
           (I : is_z_isomorphism f) : b --> a := pr1 I.

Definition is_z_isomorphism_is_inverse_in_precat {C : precategory_data} {a b : C}
           {f : a --> b} (I : is_z_isomorphism f) :
  is_inverse_in_precat f (is_z_isomorphism_mor I) := pr2 I.
Coercion is_z_isomorphism_is_inverse_in_precat : is_z_isomorphism >-> is_inverse_in_precat.

Definition is_z_isomorphism_inv {C : precategory_data} {a b : C} {f : a --> b}
           (I : is_z_isomorphism f) : is_z_isomorphism (is_z_isomorphism_mor I).
Proof.
  use make_is_z_isomorphism.
  - exact f.
  - exact (is_inverse_in_precat_inv I).
Defined.

Definition is_z_isomorphism_comp {C : precategory} {a b c : C} {f1 : a --> b} {f2 : b --> c}
           (H1 : is_z_isomorphism f1) (H2 : is_z_isomorphism f2) :
  is_z_isomorphism (f1 · f2).
Proof.
  use make_is_z_isomorphism.
  - exact (is_z_isomorphism_mor H2 · is_z_isomorphism_mor H1).
  - exact (is_inverse_in_precat_comp H1 H2).
Defined.

Definition is_z_isomorphism_identity {C : precategory} (c : C) : is_z_isomorphism (identity c).
Proof.
  use make_is_z_isomorphism.
  - exact (identity c).
  - exact (is_inverse_in_precat_identity c).
Defined.

Lemma isaprop_is_z_isomorphism {C : category} {a b : ob C}
     (f : a --> b) : isaprop (is_z_isomorphism f).
Proof.
  apply invproofirrelevance.
  intros g g'.
  set (Hpr1 := inverse_unique_precat _ _ _ _ _ (pr2 g) (pr2 g')).
  apply (total2_paths_f Hpr1).
  destruct g as [g [eta eps]].
  destruct g' as [g' [eta' eps']].
  simpl in *.
  apply isapropdirprod; apply homset_property.
Qed.

Lemma is_z_isomorphism_mor_eq {C : precategory} {a b : C} {f g : a --> b}
      (e : f = g) (I1 : is_z_isomorphism f) (I2 : is_z_isomorphism g) :
  is_z_isomorphism_mor I1 = is_z_isomorphism_mor I2.
Proof.
  use inverse_unique_precat.
  - exact f.
  - exact I1.
  - rewrite e. exact I2.
Qed.

Definition z_iso {C : precategory_data} (a b : ob C) := ∑ f : a --> b, is_z_isomorphism f.

Definition make_z_iso {C : precategory_data} {a b : C} (f : a --> b) (g : b --> a)
           (H : is_inverse_in_precat f g) : z_iso a b := (f,,make_is_z_isomorphism f g H).

Definition z_iso_mor {C : precategory_data} {a b : ob C} (f : z_iso a b) : a --> b := pr1 f.
Coercion z_iso_mor : z_iso >-> precategory_morphisms.

Definition z_iso_inv_mor {C : precategory_data} {a b : C} (i : z_iso a b) : b --> a :=
  is_z_isomorphism_mor (pr2 i).

Definition z_iso_is_inverse_in_precat {C : precategory_data} {a b : C} (i : z_iso a b) :
  is_inverse_in_precat i (z_iso_inv_mor i) := pr2 i.
Coercion z_iso_is_inverse_in_precat : z_iso >-> is_inverse_in_precat.

Definition z_iso_inv {C : precategory_data} {a b : C} (I : z_iso a b) : z_iso b a.
Proof.
  use make_z_iso.
  - exact (z_iso_inv_mor I).
  - exact I.
  - exact (is_inverse_in_precat_inv I).
Defined.

Definition z_iso_comp {C : precategory} {a b c : C} (I1 : z_iso a b) (I2 : z_iso b c) :
  z_iso a c.
Proof.
  use make_z_iso.
  - exact (I1 · I2).
  - exact ((z_iso_inv_mor I2) · (z_iso_inv_mor I1)).
  - exact (is_inverse_in_precat_comp I1 I2).
Defined.

(* see below [identity_z_iso]
Definition z_iso_identity {C : precategory} (c : C) : z_iso c c.
Proof.
  use make_z_iso.
  - exact (identity c).
  - exact (identity c).
  - exact (is_inverse_in_precat_identity c).
Defined.
*)

Definition z_iso_is_z_isomorphism1 {C : precategory} {a b : C} (I : z_iso a b) :
  is_z_isomorphism I.
Proof.
  use make_is_z_isomorphism.
  - exact (z_iso_inv_mor I).
  - exact I.
Defined.

Definition z_iso_is_z_isomorphism2 {C : precategory} {a b : C} (I : z_iso a b) :
  is_z_isomorphism (z_iso_inv_mor I).
Proof.
  use make_is_z_isomorphism.
  - exact I.
  - exact (is_inverse_in_precat_inv I).
Defined.

Lemma post_comp_with_z_iso_is_inj {C : precategory} {a' a b : C} {f : a --> b} {g : b --> a}
      (i : is_inverse_in_precat f g) : ∏ (f' g' : a' --> a), f' · f = g' · f -> f' = g'.
Proof.
  intros f' g' H.
  apply (maponpaths (postcompose g)) in H. unfold postcompose in H.
  do 2 rewrite <- assoc in H.
  rewrite (is_inverse_in_precat1 i) in H. do 2 rewrite id_right in H.
  exact H.
Qed.

Lemma post_comp_with_z_iso_inv_is_inj {C : precategory} {a b b' : C} {f : a --> b} {g : b --> a}
      (i : is_inverse_in_precat f g) : ∏ (f' g' : b' --> b), f' · g = g' · g -> f' = g'.
Proof.
  intros f' g' H.
  apply (maponpaths (postcompose f)) in H. unfold postcompose in H.
  do 2 rewrite <- assoc in H.
  rewrite (is_inverse_in_precat2 i) in H. do 2 rewrite id_right in H.
  exact H.
Qed.

Lemma pre_comp_with_z_iso_is_inj {C : precategory} {a b b' : C} {f : a --> b} {g : b --> a}
      (i : is_inverse_in_precat f g) : ∏ (f' g' : b --> b'), f · f' = f · g' -> f' = g'.
Proof.
  intros f' g' H.
  apply (maponpaths (compose g)) in H.
  do 2 rewrite assoc in H.
  rewrite (is_inverse_in_precat2 i) in H. do 2 rewrite id_left in H.
  exact H.
Qed.

Lemma pre_comp_with_z_iso_inv_is_inj {C : precategory} {a' a b : C} {f : a --> b} {g : b --> a}
      (i : is_inverse_in_precat f g) : ∏ (f' g' : a --> a'), g · f' = g · g' -> f' = g'.
Proof.
  intros f' g' H.
  apply (maponpaths (compose f)) in H.
  do 2 rewrite assoc in H.
  rewrite (is_inverse_in_precat1 i) in H. do 2 rewrite id_left in H.
  exact H.
Qed.

Lemma z_iso_eq {C : category} {a b : C} (i i' : z_iso a b) (e : z_iso_mor i = z_iso_mor i') :
  i = i'.
Proof.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. apply isaprop_is_z_isomorphism.
Qed.

Lemma z_iso_eq_inv {C : category} {a b : C} (i i' : z_iso a b)
      (e2 : z_iso_inv_mor i = z_iso_inv_mor i') : i = i'.
Proof.
  use z_iso_eq.
  assert (H : is_inverse_in_precat (z_iso_inv_mor i) i').
  {
    use make_is_inverse_in_precat.
    - rewrite e2. exact (is_inverse_in_precat2 i').
    - rewrite e2. exact (is_inverse_in_precat1 i').
  }
  exact (inverse_unique_precat _ _ _ _ _ (z_iso_inv i) H).
Qed.

Lemma eq_z_iso {C : category} (a b : ob C)
   (f g : z_iso a b) : pr1 f = pr1 g -> f = g.
Proof.
  intro H.
  apply (total2_paths_f H).
  apply proofirrelevance.
  apply isaprop_is_z_isomorphism.
Defined.

Definition morphism_from_z_iso {C : precategory_data} (a b : ob C)
   (f : z_iso a b) : a --> b := pr1 f.
Coercion morphism_from_z_iso : z_iso >-> precategory_morphisms.

Lemma isaset_z_iso {C : category} (a b : ob C) : isaset (z_iso a b).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  - apply homset_property.
  - intro f.
    apply isasetaprop.
    apply isaprop_is_z_isomorphism.
Qed.

Lemma identity_is_z_iso {C : precategory} (a : ob C) :
    is_z_isomorphism (identity a).
Proof.
  exists (identity a).
  simpl; split;
  apply id_left.
Defined.

Definition identity_z_iso {C : precategory} (a : ob C) :
   z_iso a a := tpair _ _ (identity_is_z_iso a).

Definition inv_from_z_iso {C : precategory_data} {a b : ob C}
  (f : z_iso a b) : b --> a := pr1 (pr2 f).

Lemma is_z_iso_inv_from_z_iso {C : precategory_data} (a b : ob C)
  (f : z_iso a b) : is_z_isomorphism (inv_from_z_iso f).
Proof.
  exists (pr1 f).
  simpl; split; simpl.
  - apply (pr2 (pr2 (pr2 f))).
  - apply (pr1 (pr2 (pr2 f))).
Defined.

Definition z_iso_inv_from_z_iso {C : precategory_data} {a b : ob C}
  (f : z_iso a b) : z_iso b a.
Proof.
  exists (inv_from_z_iso f).
  apply is_z_iso_inv_from_z_iso.
Defined.

Definition z_iso_inv_from_is_z_iso {C : precategory_data} {a b : ob C}
  (f : a --> b) (H : is_z_isomorphism f) : z_iso b a :=
  z_iso_inv_from_z_iso (f,,H).

Definition z_iso_inv_after_z_iso {C : precategory_data} (a b : ob C)
   (f : z_iso a b) : f · inv_from_z_iso f = identity _ :=
      pr1 (pr2 (pr2 f)).

Definition z_iso_after_z_iso_inv {C : precategory_data} (a b : ob C)
   (f : z_iso a b) : inv_from_z_iso f · f = identity _ :=
      pr2 (pr2 (pr2 f)).


Lemma z_iso_inv_on_right {C : precategory} (a b c : ob C)
  (f : z_iso a  b) (g : b --> c) (h : a --> c) (H : h = f · g) :
     inv_from_z_iso f · h = g.
Proof.
  assert (H2 : inv_from_z_iso f · h =
                  inv_from_z_iso f · (f · g)).
    apply maponpaths; assumption.
  rewrite assoc in H2.
  rewrite H2.
  rewrite z_iso_after_z_iso_inv.
  apply id_left.
Qed.

Lemma z_iso_inv_on_left {C : precategory} (a b c : ob C)
  (f : a --> b) (g : z_iso b c) (h : a --> c) (H : h = f · g) :
     f = h · inv_from_z_iso g.
Proof.
  assert (H2 : h · inv_from_z_iso g =
                         (f · g) · inv_from_z_iso g).
    rewrite H. apply idpath.
  rewrite <- assoc in H2.
  rewrite z_iso_inv_after_z_iso in H2.
  rewrite id_right in H2.
  apply pathsinv0.
  assumption.
Qed.

Lemma z_iso_inv_to_left {C : precategory} (a b c : ob C)
  (f : z_iso a  b) (g : b --> c) (h : a --> c) :
    inv_from_z_iso f · h = g -> h = f · g.
Proof.
  intro H.
  intermediate_path (f · inv_from_z_iso f · h).
  - rewrite z_iso_inv_after_z_iso, id_left; apply idpath.
  - rewrite <- assoc. apply maponpaths. assumption.
Qed.

Lemma z_iso_inv_to_right {C : precategory} (a b c : ob C)
  (f : a --> b) (g : z_iso b c) (h : a --> c) :
     f = h · inv_from_z_iso g -> f · g = h.
Proof.
  intro H.
  intermediate_path (h · inv_from_z_iso g · g).
  - rewrite H. apply idpath.
  - rewrite <- assoc, z_iso_after_z_iso_inv, id_right. apply idpath.
Qed.

Lemma wrap_inverse {M : precategory} {x y : M} (g : x --> x) (f : z_iso x y) :
  g = identity x -> z_iso_inv f · g · f = identity y.
Proof.
  intros e. rewrite e. rewrite id_right. apply z_iso_after_z_iso_inv.
Defined.

Lemma wrap_inverse' {M : precategory} {x y : M} (g : x --> x) (f : z_iso y x) :
  g = identity x -> f · g · z_iso_inv f = identity y.
Proof.
  intros e. rewrite e. rewrite id_right. apply z_iso_inv_after_z_iso.
Defined.

Lemma cancel_z_iso {M : precategory} {x y z : M} (f f' : x --> y) (g : z_iso y z) :
  f · g = f' · g -> f = f'.
Proof.
  intro e.
  destruct g as [g [g' H]].
  apply (post_comp_with_z_iso_is_inj H).
  assumption.
Qed.

Lemma cancel_z_iso' {M : precategory} {w x y : M} (g : z_iso w x) (f f' : x --> y) :
  g · f = g · f' -> f = f'.
Proof.
  intro e.
  destruct g as [g [g' H]].
  apply (pre_comp_with_z_iso_is_inj H).
  assumption.
Qed.


(** ** Properties of 0-isomorphisms *)

(** Stability under composition, inverses etc *)

Lemma are_inverse_comp_of_inverses {C : precategory} (a b c : C)
     (f : z_iso a b) (g : z_iso b c) :
  is_inverse_in_precat (f · g) (inv_from_z_iso g · inv_from_z_iso f).
Proof.
  apply is_inverse_in_precat_comp.
  - apply (pr2 f).
  - apply (pr2 g).
Qed.

Lemma inv_z_iso_unique {C : category} (a b : ob C)
  (f : z_iso a b) (g : z_iso b a) :
  is_inverse_in_precat f g -> g = z_iso_inv_from_z_iso f.
Proof.
  intro H.
  apply eq_z_iso.
  apply (inverse_unique_precat _ _ f).
    - assumption.
    - split.
      + apply z_iso_inv_after_z_iso.
      + set (h := z_iso_after_z_iso_inv _ _ f).
        apply h.
Qed.

Lemma z_iso_inv_of_z_iso_comp {C : category} (a b c : ob C)
   (f : z_iso a b) (g : z_iso b c) :
   z_iso_inv_from_z_iso (z_iso_comp f g) =
       z_iso_comp (z_iso_inv_from_z_iso g) (z_iso_inv_from_z_iso f).
Proof.
  apply eq_z_iso.
  apply idpath.
Defined.

Lemma z_iso_inv_of_z_iso_id {C : category} (a : ob C) :
   z_iso_inv_from_z_iso (identity_z_iso a) = identity_z_iso a.
Proof.
  apply eq_z_iso.
  apply idpath.
Qed.

Lemma z_iso_inv_z_iso_inv {C : category} (a b : ob C) (f : z_iso a b) :
     z_iso_inv_from_z_iso (z_iso_inv_from_z_iso f) = f.
Proof.
  apply eq_z_iso.
  apply idpath.
Defined.

Lemma z_iso_comp_right_isweq {C : precategory} {a b : ob C} (h : z_iso a b) (c : C) :
  isweq (fun f : b --> c => h · f).
Proof.
  intros. apply (isweq_iso _ (λ g, inv_from_z_iso h · g)).
       { intros f. use (_ @ maponpaths (λ m, m · f) (pr2 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } }
       { intros g. use (_ @ maponpaths (λ m, m · g) (pr1 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } }
Defined.

Definition z_iso_comp_right_weq {C : precategory} {a b : C} (h : z_iso a b) (c : C) :
 (b --> c) ≃ (a --> c) := make_weq _ (z_iso_comp_right_isweq h c).

Lemma z_iso_comp_left_isweq {C : precategory} {a b : ob C} (h : z_iso a b) (c : C) :
  isweq (fun f : c --> a => f · h).
Proof.
  intros. apply (isweq_iso _ (λ g, g · inv_from_z_iso h)).
  { intros f. use (_ @ maponpaths (λ m, f · m) (pr1 (pr2 (pr2 h))) @ _).
         { apply pathsinv0. apply assoc. }  { apply id_right. } }
       { intros g. use (_ @ maponpaths (λ m, g · m) (pr2 (pr2 (pr2 h))) @ _).
         { apply pathsinv0, assoc. } { apply id_right. } }
Defined.

Definition z_iso_comp_left_weq {C : precategory} {a b : C} (h : z_iso a b) (c : C) :
 (c --> a) ≃ (c --> b) := make_weq _ (z_iso_comp_left_isweq h c).

Definition z_iso_conjug_weq {C : precategory} {a b : C} (h : z_iso a b) :
 (a --> a) ≃ (b --> b) := weqcomp (z_iso_comp_left_weq h _ )
         (z_iso_comp_right_weq (z_iso_inv_from_z_iso h) _ ).

Lemma is_iso_from_is_z_iso {C : precategory} {a b : C} (f: a --> b) :
     is_z_isomorphism f -> is_iso f.
Proof.
  intro H.
  apply (is_iso_qinv _ (pr1 H)).
  apply (pr2 H).
Defined.

Definition z_iso_to_iso {C : precategory} {b c : C} (f : z_iso b c) : iso b c
  := pr1 f ,, is_iso_from_is_z_iso (pr1 f) (pr2 f).

Lemma is_z_iso_from_is_iso {C : precategory} {a b : C} (f : a --> b):
     is_iso f -> is_z_isomorphism f.
Proof.
  intro H.
  set (fiso := make_iso f H).
  exists (inv_from_iso fiso).
  split.
  - set (H2 := iso_inv_after_iso fiso).
    simpl in H2. apply H2.
  - set (H2 := iso_after_iso_inv fiso).
    simpl in H2. apply H2.
Defined.

Lemma is_z_iso_from_is_iso' (C : precategory) {b c : C} (f : b --> c) :
  is_iso' f -> is_z_isomorphism f.
Proof.
  intros i.
  assert (Q := i c (identity c)). induction Q as [[g E] _]. unfold postcomp_with in E.
  exists g. split.
  2 : { exact E. }
  assert (X := id_left _ : postcomp_with f (identity _) = f).
  assert (Y := ! assoc _ _ _ @ maponpaths (precomp_with f) E @ id_right _
               : postcomp_with f (f · g) = f).
  clear E.
  set (x := (_,,X) : hfiber (postcomp_with f) f).
  set (y := (_,,Y) : hfiber (postcomp_with f) f).
  exact (maponpaths pr1 (proofirrelevancecontr (i b f) y x)).
Defined.

Definition iso_to_z_iso {C : precategory} {b c : C} : iso b c -> z_iso b c
  := λ f, pr1 f ,, is_z_iso_from_is_iso (pr1 f) (pr2 f).

(** The right inverse of an invertible morphism must be equal to the known (two-sided) inverse. *)
(** TODO: Did I switch up right and left here vis a vis the conventional use? *)
Lemma right_inverse_of_iso_is_inverse {C : precategory} {c c' : C}
      (f : c --> c')
      (g : c' --> c) (H  : is_inverse_in_precat f g)
      (h : c' --> c) (HH : f · h = identity _) :
  h = g.
Proof.
  refine (!id_left _ @ _).
  refine (maponpaths (fun z => z · h) (!is_inverse_in_precat2 H) @ _).
  refine (!assoc _ _ _ @ _).
  refine (maponpaths (fun z => g · z) HH @ _).
  apply id_right.
Qed.

Lemma left_inverse_of_iso_is_inverse {C : precategory} {c c' : C}
      (f : c --> c')
      (g : c' --> c) (H  : is_inverse_in_precat f g)
      (h : c' --> c) (HH : h · f = identity _) :
  h = g.
Proof.
  refine (!id_right _ @ _).
  refine (maponpaths (fun z => h · z) (!is_inverse_in_precat1 H) @ _).
  refine (assoc _ _ _ @ _).
  refine (maponpaths (fun z => z · g) HH @ _).
  apply id_left.
Qed.
