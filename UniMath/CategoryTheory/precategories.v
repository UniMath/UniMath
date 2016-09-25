(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents :  Definition of
		Precategories,
	        Categories (aka saturated precategories)
                Setcategories

                Isomorphisms I: [iso]
                  Definition: [isiso f := isweq (precomp_with f)]
                  various lemmas:
                    uniqueness of inverse, composition etc.
                    stability under composition
                  Analogue to [gradth]: [is_iso_qinv]

                Isomorphisms II: [z_iso]
                  Definition: [is_z_iso f := Σ g, ...]
                  Relationship between [z_iso] and [iso]

                Categories have groupoid as objects

                Many lemmas about [idtoiso], [isotoid],
                   interplay with composition, transport etc.


************************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.


Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of a precategory *)

Definition precategory_ob_mor := total2 (
  fun ob : UU => ob -> ob -> UU).

Definition precategory_ob_mor_pair (ob : UU)(mor : ob -> ob -> UU) :
    precategory_ob_mor := tpair _ ob mor.

Definition ob (C : precategory_ob_mor) : UU := @pr1 _ _ C.
Coercion ob : precategory_ob_mor >-> UU.

Definition precategory_morphisms { C : precategory_ob_mor } :
       C ->  C -> UU := pr2 C.

(** We introduce notation for morphisms *)
(** in order for this notation not to pollute subsequent files,
    we define this notation locally *)

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

(** ** [precategory_data] *)
(** data of a precategory :
    - objects
    - morphisms
    - identity morphisms
    - composition
*)

Definition precategory_id_comp (C : precategory_ob_mor) :=
     dirprod (Π c : C, c --> c) (* identities *)
             (Π a b c : C,
                 a --> b -> b --> c -> a --> c).

Definition precategory_data := total2 precategory_id_comp.

Definition precategory_data_pair (C : precategory_ob_mor)
    (id : Π c : C, c --> c)
    (comp: Π a b c : C,
         a --> b -> b --> c -> a --> c) : precategory_data :=
   tpair _ C (dirprodpair id comp).

Definition precategory_ob_mor_from_precategory_data (C : precategory_data) :
     precategory_ob_mor := pr1 C.
Coercion precategory_ob_mor_from_precategory_data :
  precategory_data >-> precategory_ob_mor.

Definition identity { C : precategory_data } :
    Π c : C, c --> c :=
         pr1 (pr2 C).

Definition compose { C : precategory_data }
  { a b c : C } :
    a --> b -> b --> c -> a --> c := pr2 (pr2 C) a b c.

Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").


(** ** Axioms of a precategory *)
(**
        - identity is left and right neutral for composition
        - composition is associative
*)

Definition is_precategory (C : precategory_data) :=
   dirprod (dirprod (Π (a b : C) (f : a --> b),
                         identity a ;; f = f)
                     (Π (a b : C) (f : a --> b),
                         f ;; identity b = f))
            (Π (a b c d : C)
                    (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) = (f ;; g) ;; h).
(*
Definition is_hs_precategory_data (C : precategory_data) := Π (a b : C), isaset (a --> b).
*)
(*
Definition hs_precategory_data := total2 is_hs_precategory_data.
Definition precategory_data_from_hs_precategory_data (C : hs_precategory_data) :
  precategory_data := pr1 C.
Coercion precategory_data_from_hs_precategory_data : hs_precategory_data >-> precategory_data.
*)


Definition precategory := total2 is_precategory.

Definition hs_precategory := total2 (fun C : precategory_data =>
  dirprod (is_precategory C) (Π a b : C, isaset (a --> b))).

Definition precategory_data_from_precategory (C : precategory) :
       precategory_data := pr1 C.
Coercion precategory_data_from_precategory : precategory >-> precategory_data.
(*
Definition precategory_data_from_hs_precategory (C : hs_precategory) :
       precategory_data := pr1 C.
Coercion precategory_data_from_hs_precategory : hs_precategory >-> precategory_data.
*)
Definition precategory_from_hs_precategory (C : hs_precategory) : precategory :=
  tpair _ (pr1 C) (pr1 (pr2 C)).
Coercion precategory_from_hs_precategory : hs_precategory >-> precategory.

Definition has_homsets (C : precategory_ob_mor) := Π a b : C, isaset (a --> b).

Lemma isaprop_has_homsets (C : precategory_ob_mor) : isaprop (has_homsets C).
Proof.
  do 2 (apply impred; intro).
  apply isapropisaset.
Qed.

Definition Precategory := Σ C:precategory, has_homsets C.
Definition Precategory_pair C h : Precategory := C,,h.
Definition Precategory_to_precategory : Precategory -> precategory := pr1.
Coercion Precategory_to_precategory : Precategory >-> precategory.
Definition homset_property (C : Precategory) : has_homsets C := pr2 C.

Lemma isaprop_is_precategory (C : precategory_data)(hs: has_homsets C)
  : isaprop (is_precategory C).
Proof.
  apply isofhleveltotal2.
  { apply isofhleveltotal2. { repeat (apply impred; intro). apply hs. }
    intros _. repeat (apply impred; intro); apply hs. }
  intros _. repeat (apply impred; intro); apply hs.
Qed.


Definition id_left (C : precategory) :
   Π (a b : C) (f : a --> b),
           identity a ;; f = f := pr1 (pr1 (pr2 C)).

Definition id_right (C : precategory) :
   Π (a b : C) (f : a --> b),
           f ;; identity b = f := pr2 (pr1 (pr2 C)).

Definition assoc (C : precategory) :
   Π (a b c d : C)
          (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) = (f ;; g) ;; h := pr2 (pr2 C).

Arguments id_left [C a b] f.
Arguments id_right [C a b] f.
Arguments assoc [C a b c d] f g h.

Lemma assoc4 (C : precategory) (a b c d e : C) (f : a --> b) (g : b --> c)
       (h : c --> d) (i : d --> e) :
     ((f ;; g) ;; h) ;; i = f ;; (g ;; h) ;; i.
Proof.
  repeat rewrite assoc; apply idpath.
Qed.

Lemma remove_id_left (C : precategory) (a b : C) (f g : a --> b) (h : a --> a):
  h = identity _ -> f = g -> h ;; f = g.
Proof.
  intros H eq.
  pathvia (identity _ ;; f).
  - destruct H. apply idpath.
  - pathvia f.
    + apply id_left.
    + apply eq.
Defined.

Lemma remove_id_right (C : precategory) (a b : C) (f g : a --> b) (h : b --> b):
  h = identity _ -> f = g -> f ;; h = g.
Proof.
  intros H eq.
  pathvia (f ;; identity _).
  - destruct H. apply idpath.
  - pathvia f.
    + apply id_right.
    + apply eq.
Defined.


(** Any equality on objects a and b induces a morphism from a to b *)

Definition idtomor {C : precategory_data}
   (a b : C) (H : a = b) : a --> b.
Proof.
  destruct H.
  exact (identity a).
Defined.

Definition idtomor_inv {C : precategory_data}
    (a b : C) (H : a = b) : b --> a.
Proof.
  destruct H.
  exact (identity a).
Defined.


Lemma cancel_postcomposition (C : precategory_data) (a b c: C)
   (f f' : a --> b) (g : b --> c) : f = f' -> f ;; g = f' ;; g.
Proof.
  intro H.
  destruct H.
  apply idpath.
Defined.

Lemma cancel_precomposition (C : precategory_data) (a b c: C)
   (f f' : b --> c) (g : a --> b) : f = f' -> g ;; f = g ;; f'.
Proof.
  intro H.
  induction H.
  apply idpath.
Defined.

(** * Setcategories: Precategories whose objects and morphisms are sets *)

Definition setcategory := total2 (
   fun C : precategory => dirprod (isaset (ob C)) (has_homsets C)).

Definition precategory_from_setcategory (C : setcategory) : precategory := pr1 C.
Coercion precategory_from_setcategory : setcategory >-> precategory.

Definition setcategory_objects_set (C : setcategory) : hSet :=
    hSetpair (ob C) (pr1 (pr2 C)).

Lemma isaset_ob (C : setcategory) : isaset C.
Proof.
  exact (pr1 (pr2 C)).
Qed.

Lemma isaset_mor (C : setcategory) : has_homsets C.
Proof.
  exact (pr2 (pr2 C)).
Qed.

Lemma setcategory_eq_morphism_pi (C : setcategory) (a b : ob C)
      (e e': a = b) : idtomor _ _ e = idtomor _ _ e'.
Proof.
  assert (h : e = e').
  apply uip. apply (pr2 C).
  apply (maponpaths (idtomor _ _ ) h).
Qed.

(** * Isomorphism in a precategory *)
(** A morphism [f: a --> b] in a precategory is an isomorphism [is_iso(f)],
    if for any [c: C], precomposition with [f] yields an equivalence
    (b --> c -> a --> c].
    Definition suggested by V. Voevodsky
*)

Definition precomp_with {C : precategory_data} {a b : C} (f : a --> b) {c} (g : b --> c): a --> c :=
   f ;; g.

Definition is_iso {C : precategory_data} {a b : C} (f : a --> b) :=
  Π c, isweq (precomp_with f (c:=c)).

Definition is_isomorphism {C: precategory_data}{a b : C} (f : a --> b) := is_iso f.

Lemma isaprop_is_iso {C : precategory_data}(a b : C) (f : a --> b) : isaprop (is_iso f).
Proof.
  apply impred; intro.
  apply isapropisweq.
Qed.

Definition isaprop_is_isomorphism := @isaprop_is_iso.

Definition iso {C: precategory_data}(a b : C) := total2 (fun f : a --> b => is_iso f).
Definition morphism_from_iso (C:precategory_data)(a b : C) (f : iso a b) : a --> b := pr1 f.
Coercion morphism_from_iso : iso >-> precategory_morphisms.

Definition isopair {C: precategory_data}{a b : C} (f : a --> b) (fiso: is_iso f) : iso a b :=
   tpair _ f fiso.

Definition inv_from_iso {C:precategory_data}{a b : C} (f : iso a b) : b --> a :=
   invmap (weqpair (precomp_with f) (pr2 f a)) (identity _ ).

Definition iso_inv_after_iso {C : precategory_data}{a b : C} (f: iso a b) :
   f ;; inv_from_iso f = identity _ .
Proof.
  set (T:=homotweqinvweq (weqpair (precomp_with f) (pr2 f a ))).
  simpl in *.
  apply T.
Defined.

Definition iso_after_iso_inv {C : precategory}{a b : C} (f : iso a b) :
  inv_from_iso f ;; f = identity _ .
Proof.
  set (T:= invmaponpathsweq (weqpair (precomp_with f) (pr2 f b))).
  apply T; clear T; simpl.
  unfold precomp_with.
  pathvia ((f;; inv_from_iso f);;f).
  - apply assoc.
  - apply remove_id_left.
    + apply iso_inv_after_iso.
    + apply (!(id_right _ )).
Defined.

Definition is_iso_inv_from_iso {C:precategory}{a b : C} (f : iso a b) : is_iso (inv_from_iso f).
Proof.
  intro c.
  apply (gradth _ (precomp_with f)).
  - intro g.
    unfold precomp_with.
    pathvia ((f ;; inv_from_iso f) ;; g).
    + apply assoc.
    + apply remove_id_left. apply iso_inv_after_iso. apply idpath.
  - intro g.
    unfold precomp_with.
    pathvia ((inv_from_iso f;;f);;g).
    + apply assoc.
    + apply remove_id_left. apply iso_after_iso_inv. apply idpath.
Defined.

Definition iso_inv_from_iso {C:precategory}{a b : C} (f : iso a b) : iso b a :=
  tpair _ _ (is_iso_inv_from_iso f).

Lemma eq_iso {C: precategory_data} {a b : C} (f g : iso a b) : pr1 f = pr1 g -> f = g.
Proof.
  intro H.
  apply subtypeEquality.
  - intros t. apply isaprop_is_iso.
  - apply H.
Defined.

Lemma isaset_iso {C : precategory_data} (hs: has_homsets C) (a b :ob C) :
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
  set (T:=@isweqhomot (a --> c) (a --> c) (fun t => t) (precomp_with (identity a))).
  apply T.
  - intro g. apply pathsinv0. apply id_left.
  - apply idisweq.
Defined.

Definition identity_iso {C : precategory} (a : ob C) :
   iso a a := tpair _ _ (identity_is_iso C a).


Definition iso_inv_from_is_iso {C : precategory} {a b : ob C}
  (f : a --> b) (H : is_iso f) : iso b a :=
  iso_inv_from_iso (tpair _ f H).

Lemma iso_inv_on_right (C : precategory) (a b c: ob C)
  (f : iso a  b) (g : b --> c) (h : a --> c) (H : h = f;;g) :
     inv_from_iso f ;; h = g.
Proof.
  apply (invmaponpathsweq (weqpair (precomp_with f) (pr2 f c))).
  unfold precomp_with; simpl.
  pathvia ((f;;inv_from_iso f);;h).
  - apply assoc.
  - apply remove_id_left.
    + apply iso_inv_after_iso.
    + assumption.
Defined.

Lemma iso_inv_on_left (C : precategory) (a b c: ob C)
  (f : a --> b) (g : iso b c) (h : a --> c) (H : h = f;;g) :
     f = h ;; inv_from_iso g.
Proof.
  assert (H2 : h ;; inv_from_iso g =
                         (f;; g) ;; inv_from_iso g).
    rewrite H. apply idpath.
  rewrite <- assoc in H2.
  rewrite iso_inv_after_iso in H2.
  rewrite id_right in H2.
  apply pathsinv0.
  assumption.
Qed.

Lemma iso_inv_to_left (C : precategory) (a b c: ob C)
  (f : iso a  b) (g : b --> c) (h : a --> c) :
    inv_from_iso f ;; h = g -> h = f ;; g.
Proof.
  intro H.
  transitivity (f;; inv_from_iso f;; h).
  - rewrite iso_inv_after_iso, id_left; apply idpath.
  - rewrite <- assoc. rewrite H. apply idpath.
Qed.

Lemma iso_inv_to_right (C : precategory) (a b c: ob C)
  (f : a --> b) (g : iso b c) (h : a --> c) :
     f = h ;; inv_from_iso g -> f ;; g = h.
Proof.
  intro H.
  transitivity (h;; inv_from_iso g;; g).
  - rewrite H. apply idpath.
  - rewrite <- assoc, iso_after_iso_inv, id_right. apply idpath.
Qed.


(** ** Properties of isomorphisms *)
(** Stability under composition, inverses etc *)

Definition isweqhomot' {X Y} (f g : X -> Y) (H : isweq f)
      (homot : Π x, f x = g x) : isweq g.
Proof.
  apply (isweqhomot f g homot H).
Defined.

Lemma is_iso_comp_of_isos {C : precategory} {a b c : ob C}
  (f : iso a b) (g : iso b c) : is_iso (f ;; g).
Proof.
  simpl.
  intro d.
  set (T:=twooutof3c (precomp_with g) (precomp_with f(c:=d)) (pr2 g d) (pr2 f _)).
  apply (isweqhomot' _ _ T).
  intro h. apply assoc.
Defined.

Definition iso_comp {C : precategory} {a b c : ob C}
  (f : iso a b) (g : iso b c) : iso a c.
Proof.
  exists (f ;; g).
  apply is_iso_comp_of_isos.
Defined.


Lemma inv_iso_unique (C : precategory) (a b : C) (f : iso a b) (g : iso b a) :
  precomp_with f g = identity _ -> g = iso_inv_from_iso f.
Proof.
  intro H.
  apply eq_iso. simpl.
  set (T:=invmaponpathsweq (weqpair (precomp_with f) (pr2 f a ))).
  apply T; simpl.
  pathvia (identity a ).
  + assumption.
  + apply pathsinv0. apply iso_inv_after_iso.
Defined.

Lemma inv_iso_unique' (C : precategory) (a b : C) (f : iso a b) (g : b --> a) :
  precomp_with f g = identity _ -> g = inv_from_iso f.
Proof.
  intro H.
  set (T:=invmaponpathsweq (weqpair (precomp_with f) (pr2 f a ))).
  apply T; simpl.
  pathvia (identity a ).
  + assumption.
  + apply pathsinv0. apply iso_inv_after_iso.
Defined.


Lemma iso_inv_of_iso_comp (C : precategory) (a b c : ob C)
   (f : iso a b) (g : iso b c) :
   iso_inv_from_iso (iso_comp f g) = iso_comp (iso_inv_from_iso g) (iso_inv_from_iso f).
Proof.
  apply pathsinv0.
  apply inv_iso_unique. simpl. unfold precomp_with.
  pathvia (f ;; (g;;inv_from_iso g) ;; inv_from_iso f).
  - repeat rewrite assoc.  apply idpath.
  - rewrite iso_inv_after_iso. rewrite id_right.
    apply iso_inv_after_iso.
Qed.

Lemma iso_inv_of_iso_id (C : precategory) (a : ob C) :
   iso_inv_from_iso (identity_iso a) = identity_iso a.
Proof.
  apply eq_iso.
  apply idpath.
Qed.


Lemma iso_inv_iso_inv (C : precategory) (a b : ob C) (f : iso a b) :
     iso_inv_from_iso (iso_inv_from_iso f) = f.
Proof.
  apply eq_iso. simpl.
  apply pathsinv0.
  apply inv_iso_unique'.
  apply iso_after_iso_inv.
Defined.

Lemma pre_comp_with_iso_is_inj (C : precategory_data) (a b c : ob C)
    (f : a --> b) (H : is_iso f) (g h : b --> c) : f ;; g = f ;; h -> g = h.
Proof.
  intro X.
  apply (invmaponpathsweq (weqpair (precomp_with f) (H _ ))).
  apply X.
Qed.

Lemma post_comp_with_iso_is_inj (C : precategory) (b c : ob C)
     (h : b --> c) (H : is_iso h)
   (a : ob C) (f g : a --> b) : f ;; h = g ;; h -> f = g.
Proof.
  intro HH.
  set (T:=iso_inv_after_iso (tpair _ h H)). simpl in T.
  pathvia (f ;; (h ;; inv_from_iso (tpair _ h H))).
  - rewrite T. clear T.
    apply pathsinv0, id_right.
  - rewrite assoc. rewrite HH.
    rewrite <- assoc. rewrite T.
    apply id_right.
Qed.


Lemma iso_comp_right_isweq {C:precategory_data} {a b:ob C} (h:iso a b) (c:C) :
  isweq (fun f : b --> c => h ;; f).
Proof.
  apply (pr2 h _ ).
Defined.

Definition iso_comp_right_weq {C:precategory_data} {a b:C} (h:iso a b) (c:C) :
 weq (b --> c) (a --> c) := weqpair _ (iso_comp_right_isweq h c).

Lemma iso_comp_left_isweq {C:precategory} {a b:ob C} (h:iso a b) (c:C) :
  isweq (fun f : c --> a => f ;; h).
Proof.
  intros. apply (gradth _ (fun g => g ;; inv_from_iso h)).
  - intro x. rewrite <- assoc. apply remove_id_right.
    apply iso_inv_after_iso. apply idpath.
  - intro y. rewrite <- assoc. apply remove_id_right.
    apply iso_after_iso_inv. apply idpath.
Defined.

Definition postcomp_with {C : precategory_data}{b c : C}(h : b --> c) {a : C}
  (f : a --> b) : a --> c := f ;; h.

Definition is_inverse_in_precat {C : precategory_data} {a b : C}
  (f : a --> b) (g : b --> a) :=
  dirprod (f ;; g = identity a)
          (g ;; f = identity b).


Definition is_iso_qinv {C:precategory} {a b : C} (f : a --> b) (g : b --> a) :
  is_inverse_in_precat f g -> is_iso f.
Proof.
  intros H c.
  apply (gradth _ (precomp_with g)).
  - intro h. unfold precomp_with.
    rewrite assoc.
    apply remove_id_left.
    apply (pr2 H). apply idpath.
  - intro h. unfold precomp_with. rewrite assoc.
    apply remove_id_left.
    apply (pr1 H). apply idpath.
Defined.

Definition iso_comp_left_weq {C:precategory} {a b:C} (h:iso a b) (c:C) :
 weq (c --> a) (c --> b) := weqpair _ (iso_comp_left_isweq h c).

Definition iso_conjug_weq {C:precategory} {a b:C} (h:iso a b) :
 weq (a --> a) (b --> b) := weqcomp (iso_comp_left_weq h _ ) (iso_comp_right_weq (iso_inv_from_iso h) _ ).



(** * Isomorphisms in a precategory WITH HOM-SETS *)
(** In a precategory with hom-sets, we can give the usual definition of
    isomorphism, called [0-iso] in the following.
*)
(** ** Definition of isomorphisms *)

Lemma isaprop_is_inverse_in_precat (C : precategory_data) (hs: has_homsets C) (a b : ob C)
   (f : a --> b) (g : b --> a) : isaprop (is_inverse_in_precat f g).
Proof.
  apply isapropdirprod; apply hs.
Qed.

Lemma inverse_unique_precat (C : precategory) (a b : ob C)
   (f : a --> b) (g g': b --> a) (H : is_inverse_in_precat f g)
    (H' : is_inverse_in_precat f g') : g = g'.
Proof.
  destruct H as [eta eps].
  destruct H' as [eta' eps'].
  assert (H : g = identity b ;; g).
    rewrite id_left; apply idpath.
  apply (pathscomp0 H).
  rewrite <- eps'.
  rewrite <- assoc.
  rewrite eta.
  apply id_right.
Qed.

Definition is_z_isomorphism {C : precategory_data} {a b : ob C}
  (f : a --> b) := total2 (fun g => is_inverse_in_precat f g).

Lemma isaprop_is_z_isomorphism {C : precategory} {a b : ob C} (hs: has_homsets C)
     (f : a --> b) : isaprop (is_z_isomorphism f).
Proof.
  apply invproofirrelevance.
  intros g g'.
  set (Hpr1 := inverse_unique_precat _ _ _ _ _ _ (pr2 g) (pr2 g')).
  apply (total2_paths Hpr1).
  destruct g as [g [eta eps]].
  destruct g' as [g' [eta' eps']].
  simpl in *.
  apply isapropdirprod; apply hs.
Qed.

Definition z_iso {C : precategory_data} (a b :ob C) := total2
    (fun f : a --> b => is_z_isomorphism f).

Lemma eq_z_iso (C : precategory)(hs: has_homsets C) (a b : ob C)
   (f g : z_iso a b) : pr1 f = pr1 g -> f = g.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_z_isomorphism, hs.
Defined.

Definition morphism_from_z_iso (C : precategory_data)(a b : ob C)
   (f : z_iso a b) : a --> b := pr1 f.
Coercion morphism_from_z_iso : z_iso >-> precategory_morphisms.

Lemma isaset_z_iso {C : precategory} (hs: has_homsets C) (a b :ob C) : isaset (z_iso a b).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply hs.
  intro f.
  apply isasetaprop.
  apply isaprop_is_z_isomorphism, hs.
Qed.

Lemma identity_is_z_iso (C : precategory) (a : ob C) :
    is_z_isomorphism (identity a).
Proof.
  exists (identity a).
  simpl; split;
  apply id_left.
Defined.

Definition identity_z_iso {C : precategory} (a : ob C) :
   z_iso a a := tpair _ _ (identity_is_z_iso C a).

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
  z_iso_inv_from_z_iso (tpair _ f H).

Definition z_iso_inv_after_z_iso (C : precategory_data) (a b : ob C)
   (f : z_iso a b) : f;; inv_from_z_iso f = identity _ :=
      pr1 (pr2 (pr2 f)).

Definition z_iso_after_z_iso_inv (C : precategory_data) (a b : ob C)
   (f : z_iso a b) : inv_from_z_iso f ;; f = identity _ :=
      pr2 (pr2 (pr2 f)).


Lemma z_iso_inv_on_right (C : precategory) (a b c: ob C)
  (f : z_iso a  b) (g : b --> c) (h : a --> c) (H : h = f;;g) :
     inv_from_z_iso f ;; h = g.
Proof.
  assert (H2 : inv_from_z_iso f;; h =
                  inv_from_z_iso f;; (f ;; g)).
  apply maponpaths; assumption.
  rewrite assoc in H2.
  rewrite H2.
  rewrite z_iso_after_z_iso_inv.
  apply id_left.
Qed.

Lemma z_iso_inv_on_left (C : precategory) (a b c: ob C)
  (f : a --> b) (g : z_iso b c) (h : a --> c) (H : h = f;;g) :
     f = h ;; inv_from_z_iso g.
Proof.
  assert (H2 : h ;; inv_from_z_iso g =
                         (f;; g) ;; inv_from_z_iso g).
    rewrite H. apply idpath.
  rewrite <- assoc in H2.
  rewrite z_iso_inv_after_z_iso in H2.
  rewrite id_right in H2.
  apply pathsinv0.
  assumption.
Qed.

Lemma z_iso_inv_to_left (C : precategory) (a b c: ob C)
  (f : z_iso a  b) (g : b --> c) (h : a --> c) :
    inv_from_z_iso f ;; h = g -> h = f ;; g.
Proof.
  intro H.
  transitivity (f;; inv_from_z_iso f;; h).
  - rewrite z_iso_inv_after_z_iso, id_left; apply idpath.
  - rewrite <- assoc. rewrite H. apply idpath.
Qed.

Lemma z_iso_inv_to_right (C : precategory) (a b c: ob C)
  (f : a --> b) (g : z_iso b c) (h : a --> c) :
     f = h ;; inv_from_z_iso g -> f ;; g = h.
Proof.
  intro H.
  transitivity (h;; inv_from_z_iso g;; g).
  - rewrite H. apply idpath.
  - rewrite <- assoc, z_iso_after_z_iso_inv, id_right. apply idpath.
Qed.


(** ** Properties of isomorphisms *)
(** Stability under composition, inverses etc *)

Lemma are_inverse_comp_of_inverses (C : precategory) (a b c : C)
     (f : z_iso a b) (g : z_iso b c) :
  is_inverse_in_precat (f;; g) (inv_from_z_iso g;; inv_from_z_iso f).
Proof.
  simpl; split; simpl;
  unfold inv_from_iso; simpl.
  destruct f as [f [f' Hf]]. simpl in *.
  destruct g as [g [g' Hg]]; simpl in *.
  pathvia ((f ;; (g ;; g')) ;; f').
  repeat rewrite assoc; apply idpath.
  rewrite (pr1 Hg).
  rewrite id_right.
  rewrite (pr1 Hf).
  apply idpath.

  destruct f as [f [f' Hf]]. simpl in *.
  destruct g as [g [g' Hg]]; simpl in *.
  pathvia ((g' ;; (f' ;; f)) ;; g).
  repeat rewrite assoc; apply idpath.
  rewrite (pr2 Hf).
  rewrite id_right.
  rewrite (pr2 Hg).
  apply idpath.
Qed.


Lemma is_z_iso_comp_of_z_isos {C : precategory} {a b c : ob C}
  (f : z_iso a b) (g : z_iso b c) : is_z_isomorphism (f ;; g).
Proof.
  exists (inv_from_z_iso g ;; inv_from_z_iso f). simpl.
  apply are_inverse_comp_of_inverses.
Defined.


Definition z_iso_comp {C : precategory} {a b c : ob C}
  (f : z_iso a b) (g : z_iso b c) : z_iso a c.
Proof.
  exists (f ;; g).
  apply is_z_iso_comp_of_z_isos.
Defined.

Lemma inv_z_iso_unique (C : precategory) (hs: has_homsets C) (a b : ob C)
  (f : z_iso a b) (g : z_iso b a) :
  is_inverse_in_precat f g -> g = z_iso_inv_from_z_iso f.
Proof.
  intro H.
  apply eq_z_iso.
  apply hs.
  apply (inverse_unique_precat _ _ _ f).
  assumption.
  split.
  apply z_iso_inv_after_z_iso.
  set (h := z_iso_after_z_iso_inv _ _ _ f).
  apply h.
Qed.


Lemma z_iso_inv_of_z_iso_comp (C : precategory) (hs: has_homsets C) (a b c : ob C)
   (f : z_iso a b) (g : z_iso b c) :
   z_iso_inv_from_z_iso (z_iso_comp f g) =
       z_iso_comp (z_iso_inv_from_z_iso g) (z_iso_inv_from_z_iso f).
Proof.
  apply eq_z_iso.
  apply hs.
  reflexivity.
Defined.

Lemma z_iso_inv_of_z_iso_id (C : precategory) (hs: has_homsets C) (a : ob C) :
   z_iso_inv_from_z_iso (identity_z_iso a) = identity_z_iso a.
Proof.
  apply eq_z_iso.
  apply hs.
  apply idpath.
Qed.


Lemma z_iso_inv_z_iso_inv (C : precategory) (hs: has_homsets C) (a b : ob C) (f : z_iso a b) :
     z_iso_inv_from_z_iso (z_iso_inv_from_z_iso f) = f.
Proof.
  apply eq_z_iso.
  apply hs.
  reflexivity.
Defined.

Lemma pre_comp_with_z_iso_is_inj (C : precategory) (a b c : ob C)
    (f : a --> b) (H : is_z_isomorphism f) (g h : b --> c) : f ;; g = f ;; h -> g = h.
Proof.
  intro HH.
  pathvia (pr1 H ;; f ;; g).
  rewrite (pr2 (pr2 H)).
  rewrite id_left.
  apply idpath.
  pathvia ((pr1 H ;; f) ;; h).
  repeat rewrite <- assoc.
  apply maponpaths. assumption.
  rewrite (pr2 (pr2 H)).
  rewrite id_left.
  apply idpath.
Qed.

Lemma post_comp_with_z_iso_is_inj (C : precategory) (b c : ob C)
     (h : b --> c) (H : is_z_isomorphism h)
   (a : ob C) (f g : a --> b) : f ;; h = g ;; h -> f = g.
Proof.
  intro HH.
  pathvia (f ;; (h ;; pr1 H)).
  rewrite (pr1 (pr2 H)).
  rewrite id_right.
  apply idpath.
  pathvia (g ;; (h ;; pr1 H)).
  repeat rewrite assoc.
  rewrite HH. apply idpath.
  rewrite (pr1 (pr2 H)).
  rewrite id_right.
  apply idpath.
Qed.


Lemma z_iso_comp_right_isweq {C:precategory} {a b:ob C} (h:z_iso a b) (c:C) :
  isweq (fun f : b --> c => h ;; f).
Proof.
  intros. apply (gradth _ (fun g => inv_from_z_iso h ;; g)).
       { intros f. refine (_ @ maponpaths (fun m => m ;; f) (pr2 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } }
       { intros g. refine (_ @ maponpaths (fun m => m ;; g) (pr1 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } }
Defined.

Definition z_iso_comp_right_weq {C:precategory} {a b:C} (h:z_iso a b) (c:C) :
 weq (b --> c) (a --> c) := weqpair _ (z_iso_comp_right_isweq h c).

Lemma z_iso_comp_left_isweq {C:precategory} {a b:ob C} (h:z_iso a b) (c:C) :
  isweq (fun f : c --> a => f ;; h).
Proof.
  intros. apply (gradth _ (fun g => g ;; inv_from_z_iso h)).
       { intros f. refine (_ @ maponpaths (fun m => f;;m) (pr1 (pr2 (pr2 h))) @ _).
         { apply pathsinv0. apply assoc. }  { apply id_right. } }
       { intros g. refine (_ @ maponpaths (fun m => g;;m) (pr2 (pr2 (pr2 h))) @ _).
         { apply pathsinv0, assoc. } { apply id_right. } }
Defined.
Definition z_iso_comp_left_weq {C:precategory} {a b:C} (h:z_iso a b) (c:C) :
 weq (c --> a) (c --> b) := weqpair _ (z_iso_comp_left_isweq h c).

Definition z_iso_conjug_weq {C:precategory} {a b:C} (h:z_iso a b) :
 weq (a --> a) (b --> b) := weqcomp (z_iso_comp_left_weq h _ )
         (z_iso_comp_right_weq (z_iso_inv_from_z_iso h) _ ).

Lemma is_iso_from_is_z_iso {C: precategory}{a b : C} (f: a --> b) :
     is_z_isomorphism f -> is_iso f.
Proof.
  intro H.
  apply (is_iso_qinv _ (pr1 H)).
  apply (pr2 H).
Defined.

Lemma is_z_iso_from_is_iso {C: precategory}{a b : C} (f: a --> b):
     is_iso f -> is_z_isomorphism f.
Proof.
  intro H.
  set (fiso:= isopair f H).
  exists (inv_from_iso fiso).
  split.
  - set (H2:= iso_inv_after_iso fiso).
    simpl in H2. apply H2.
  - set (H2:=iso_after_iso_inv fiso).
    simpl in H2. apply H2.
Defined.

(** * Categories (aka saturated precategories) *)

(** ** Definition of categories *)

Definition idtoiso {C : precategory} {a b : ob C}:
      a = b -> iso a b.
Proof.
  intro H.
  destruct H.
  exact (identity_iso a).
Defined.

(* use eta expanded version to force printing of object arguments *)
Definition is_category (C : precategory) :=
  dirprod (Π (a b : ob C), isweq (fun p : a = b => idtoiso p))
          (has_homsets C).

Lemma eq_idtoiso_idtomor {C:precategory} (a b:ob C) (e:a = b) :
    pr1 (idtoiso e) = idtomor _ _ e.
Proof.
  destruct e; reflexivity.
Defined.

Lemma isaprop_is_category (C : precategory) : isaprop (is_category C).
Proof.
  apply isapropdirprod.
  - apply impred.
    intro a.
    apply impred.
    intro b.
    apply isapropisweq.
  - apply impred.
    intro a.
    apply impred.
    intro b.
    apply isapropisaset.
Qed.

Definition category := total2 (fun C : precategory => is_category C).

Definition category_to_Precategory (C : category) : Precategory.
Proof.
  exists (pr1 C).
  exact (pr2 (pr2 C)).
Defined.
Coercion category_to_Precategory : category >-> Precategory.


Lemma category_has_groupoid_ob (C : category): isofhlevel 3 (ob C).
Proof.
  change (isofhlevel 3 C) with
        (Π a b : C, isofhlevel 2 (a = b)).
  intros a b.
  apply (isofhlevelweqb _ (tpair _ _ (pr1 (pr2 C) a b))).
  apply isaset_iso.
  apply (pr2 (pr2 C)).
Qed.


(** ** Definition of [isotoid] *)

Definition isotoid (C : precategory) (H : is_category C) {a b : ob C}:
      iso a b -> a = b := invmap (weqpair _ (pr1 H a b)).

Lemma idtoiso_isotoid (C : precategory) (H : is_category C) (a b : ob C)
    (f : iso a b) : idtoiso (isotoid _ H f) = f.
Proof.
  unfold isotoid.
  set (Hw := homotweqinvweq (weqpair idtoiso (pr1 H a b))).
  simpl in Hw.
  apply Hw.
Qed.

Lemma isotoid_idtoiso (C : precategory) (H : is_category C) (a b : ob C)
    (p : a = b) : isotoid _ H (idtoiso p) = p.
Proof.
  unfold isotoid.
  set (Hw := homotinvweqweq (weqpair idtoiso (pr1 H a b))).
  simpl in Hw.
  apply Hw.
Qed.

(** ** Properties of [idtoiso] and [isotoid] *)

Definition double_transport {C : precategory} {a a' b b' : ob C}
   (p : a = a') (q : b = b') (f : a --> b) : a' --> b' :=
  transportf (fun c => a' --> c) q (transportf (fun c => c --> b) p f).

Lemma idtoiso_postcompose (C : precategory) (a b b' : ob C)
  (p : b = b') (f : a --> b) :
      f ;; idtoiso p = transportf (fun b => a --> b) p f.
Proof.
  destruct p.
  apply id_right.
Qed.

Lemma idtoiso_postcompose_iso (C : precategory) (hs: has_homsets C) (a b b' : ob C)
  (p : b = b') (f : iso a b) :
    iso_comp f (idtoiso p) = transportf (fun b => iso a b) p f.
Proof.
  destruct p.
  apply eq_iso.
  apply id_right.
Qed.


Lemma idtoiso_precompose (C : precategory) (a a' b : ob C)
  (p : a = a') (f : a --> b) :
      (idtoiso (!p)) ;; f = transportf (fun a => a --> b) p f.
Proof.
  destruct p.
  apply id_left.
Qed.

Lemma idtoiso_precompose_iso (C : precategory) (hs: has_homsets C) (a a' b : ob C)
  (p : a = a') (f : iso a b) :
      iso_comp (idtoiso (!p)) f = transportf (fun a => iso a b) p f.
Proof.
  destruct p.
  apply eq_iso.
  apply id_left.
Qed.



Lemma double_transport_idtoiso (C : precategory) (a a' b b' : ob C)
  (p : a = a') (q : b = b')  (f : a --> b) :
  double_transport p q f = inv_from_iso (idtoiso p) ;; f ;; idtoiso q.
Proof.
  destruct p.
  destruct q.
  pathvia (identity _ ;; f).
  - apply pathsinv0; apply id_left.
  - apply pathsinv0; apply id_right.
Defined.

Lemma idtoiso_inv (C : precategory) (a a' : ob C)
  (p : a = a') : idtoiso (!p) = iso_inv_from_iso (idtoiso p).
Proof.
  destruct p.
  simpl. apply eq_iso.
  apply idpath.
Defined.


Lemma idtoiso_concat (C : precategory) (a a' a'' : ob C)
  (p : a = a') (q : a' = a'') :
  idtoiso (p @ q) = iso_comp (idtoiso p) (idtoiso q).
Proof.
  destruct p.
  destruct q.
  apply eq_iso.
  simpl; apply pathsinv0, id_left.
Qed.

Lemma idtoiso_inj (C : precategory) (H : is_category C) (a a' : ob C)
   (p p' : a = a') : idtoiso p = idtoiso p' -> p = p'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply H.
Qed.

Lemma isotoid_inj (C : precategory) (H : is_category C) (a a' : ob C)
   (f f' : iso a a') : isotoid _ H f = isotoid _ H f' -> f = f'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply isweqinvmap.
Qed.

Lemma isotoid_comp (C : precategory) (H : is_category C) (a b c : ob C)
  (e : iso a b) (f : iso b c) :
  isotoid _ H (iso_comp e f) = isotoid _ H e @ isotoid _ H f.
Proof.
  apply idtoiso_inj.
    assumption.
  rewrite idtoiso_concat.
  repeat rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma isotoid_identity_iso (C : precategory) (H : is_category C) (a : C) :
  isotoid _ H (identity_iso a) = idpath _ .
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid;
  apply idpath.
Qed.


Lemma inv_isotoid (C : precategory) (H : is_category C) (a b : C)
    (f : iso a b) : ! isotoid _ H f = isotoid _ H (iso_inv_from_iso f).
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.


Lemma transportf_isotoid (C : precategory) (H : is_category C)
   (a a' b : ob C) (p : iso a a') (f : a --> b) :
 transportf (fun a0 : C => a0 --> b) (isotoid C H p) f = inv_from_iso p ;; f.
Proof.
  rewrite <- idtoiso_precompose.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid' (C : precategory) (H : is_category C)
   (a b b' : ob C) (p : iso b b') (f : a --> b) :
 transportf (fun a0 : C => a --> a0) (isotoid C H p) f = f ;; p.
Proof.
  rewrite <- idtoiso_postcompose.
  apply maponpaths.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid_dep (C : precategory)
   (a a' : C) (p : a = a') (f : Π c, a --> c) :
 transportf (fun x : C => Π c, x --> c) p f = fun c => idtoiso (!p) ;; f c.
Proof.
  destruct p.
  simpl.
  apply funextsec.
  intro.
  rewrite id_left.
  apply idpath.
Qed.

Lemma transportf_isotoid_dep' (J : UU) (C : precategory) (F : J -> C)
  (a a' : C) (p : a = a') (f : Π c, a --> F c) :
  transportf (fun x : C => Π c, x --> F c) p f = fun c => idtoiso (!p) ;; f c.
Proof.
  now destruct p; apply funextsec; intro x; rewrite id_left.
Defined.

(* This and the above name is not very good... *)
 Lemma transportf_isotoid_dep'' (J : UU) (C : precategory) (F : J -> C)
   (a a' : C) (p : a = a') (f : Π c, F c --> a) :
   transportf (fun x : C => Π c, F c --> x) p f = fun c => f c ;; idtoiso p.
Proof.
  now destruct p; apply funextsec; intro x; rewrite id_right.
Defined.


(** ** Precategories in style of essentially algebraic cats *)
(** Of course we later want SETS of objects, rather than types,
    but the construction can already be specified.
*)

Definition total_morphisms (C : precategory_ob_mor) := total2 (
   fun ab : dirprod (ob C)(ob C) =>
        precategory_morphisms (pr1 ab) (pr2 ab)).

Lemma isaset_setcategory_total_morphisms (C : setcategory):
   isaset (total_morphisms C).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply isofhleveldirprod.
  - exact (pr1 (pr2 C)).
  - exact (pr1 (pr2 C)).
  - intro ab.
    induction ab as [c c'].
    apply (pr2 (pr2 C)).
Qed.

Definition setcategory_total_morphisms_set (C : setcategory) : hSet :=
    hSetpair _ (isaset_setcategory_total_morphisms C).

Definition precategory_source (C : precategory_ob_mor) :
     total_morphisms C -> ob C :=
     fun abf => pr1 (pr1 abf).

Definition precategory_target (C : precategory_ob_mor) :
     total_morphisms C -> ob C :=
     fun abf => pr2 (pr1 abf).

Definition precategory_total_id (C : precategory_data) :
      ob C -> total_morphisms C :=
      fun c => tpair _ (dirprodpair c c) (identity c).

Definition precategory_total_comp'' (C : precategory_data) :
      Π f g : total_morphisms C,
        precategory_target C f = precategory_source C g ->
         total_morphisms C.
Proof.
  intros f g e.
  destruct f as [[a b] f]. simpl in *.
  destruct g as [[b' c] g]. simpl in *.
  unfold precategory_target in e; simpl in e.
  unfold precategory_source in e; simpl in e.
  simpl.
  exists (dirprodpair a c). simpl.
  exact ((f ;; idtomor _ _ e) ;; g).
Defined.

Definition precategory_total_comp (C : precategory_data) :
      Π f g : total_morphisms C,
        precategory_target C f = precategory_source C g ->
         total_morphisms C :=
  fun f g e =>
     tpair _ (dirprodpair (pr1 (pr1 f))(pr2 (pr1 g)))
        ((pr2 f ;; idtomor _ _ e) ;; pr2 g).
