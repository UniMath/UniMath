(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents :
- precategories: homs are arbitrary types [precategory]
- categories: hom-types are sets [category]
- univalent categories: [idtoiso] is an equivalence
   [univalent_category]
- set-categories: objects and morphisms are sets [setcategory]
- isomorphisms: [iso], [isiso f := isweq (precomp_with f)]
- various lemmas:
  - uniqueness of inverse, composition etc.
  - stability under composition
  - Analogue to [gradth]: [is_iso_qinv]

- Alternative definition of isomorphisms: [z_iso]
  - Definition: [is_z_iso f := ∑ g, ...]
  - Relationship between [z_iso] and [iso]
- Univalent categories have groupoid as objects
  [univalent_category_has_groupoid_ob]
- Many lemmas about [idtoiso], [isotoid],
  interplay with composition, transport etc.


************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.


Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of a precategory *)

Definition precategory_ob_mor := total2 (
  λ ob : UU, ob -> ob -> UU).

Definition precategory_ob_mor_pair (ob : UU)(mor : ob -> ob -> UU) :
    precategory_ob_mor := tpair _ ob mor.

Definition ob (C : precategory_ob_mor) : UU := @pr1 _ _ C.
Coercion ob : precategory_ob_mor >-> UU.

Definition precategory_morphisms { C : precategory_ob_mor } :
       C ->  C -> UU := pr2 C.

(** We introduce notation for morphisms *)
(** in order for this notation not to pollute subsequent files,
    we define this notation within the scope "cat" *)

Delimit Scope cat with cat.     (* for precategories *)

Delimit Scope cat with Cat.     (* a slight enhancement for categories *)

Delimit Scope cat_deprecated with cat_deprecated.

Local Open Scope cat.

Notation "a --> b" := (precategory_morphisms a b) : cat.

Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) : cat.
(* ⟦   to input: type "\[[" or "\(" with Agda input method
   ⟧   to input: type "\]]" or "\)" with Agda input method *)

(** ** [precategory_data] *)
(** data of a precategory :
    - objects
    - morphisms
    - identity morphisms
    - composition
*)

Definition precategory_id_comp (C : precategory_ob_mor) :=
     (∏ c : C, c --> c) × (* identities *)
             (∏ a b c : C,
                 a --> b -> b --> c -> a --> c).

Definition precategory_data := total2 precategory_id_comp.

Definition precategory_data_pair (C : precategory_ob_mor)
    (id : ∏ c : C, c --> c)
    (comp: ∏ a b c : C,
         a --> b -> b --> c -> a --> c) : precategory_data :=
   tpair _ C (dirprodpair id comp).

Definition precategory_ob_mor_from_precategory_data (C : precategory_data) :
     precategory_ob_mor := pr1 C.
Coercion precategory_ob_mor_from_precategory_data :
  precategory_data >-> precategory_ob_mor.

Definition identity { C : precategory_data } :
    ∏ c : C, c --> c :=
         pr1 (pr2 C).

Definition compose { C : precategory_data }
  { a b c : C } :
    a --> b -> b --> c -> a --> c := pr2 (pr2 C) a b c.

Notation "f ;; g" := (compose f g) : cat_deprecated.

Notation "f · g" := (compose f g) : cat.
(* to input: type "\centerdot" or "\cdot" with Agda input method *)

Notation "g ∘ f" := (compose f g) (only parsing) : cat.
(* agda input \circ *)

Definition postcompose  {C : precategory_data} {a b c : C} (g : b --> c) (f : a --> b) : a --> c :=
  compose f g.

(** ** Axioms of a precategory *)
(**
        - identity is left and right neutral for composition
        - composition is associative
*)

Definition is_precategory (C : precategory_data) :=
  ((∏ (a b : C) (f : a --> b), identity a · f = f)
     × (∏ (a b : C) (f : a --> b), f · identity b = f))
    × (∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h).

Definition mk_is_precategory {C : precategory_data}
           (H1 : ∏ (a b : C) (f : a --> b), identity a · f = f)
           (H2 : ∏ (a b : C) (f : a --> b), f · identity b = f)
           (H3 : ∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h) :
  is_precategory C := dirprodpair (dirprodpair H1 H2) H3.


(*
Definition is_hs_precategory_data (C : precategory_data) := ∏ (a b : C), isaset (a --> b).
*)
(*
Definition hs_precategory_data := total2 is_hs_precategory_data.
Definition precategory_data_from_hs_precategory_data (C : hs_precategory_data) :
  precategory_data := pr1 C.
Coercion precategory_data_from_hs_precategory_data : hs_precategory_data >-> precategory_data.
*)


Definition precategory := total2 is_precategory.

Definition mk_precategory (C : precategory_data) (H : is_precategory C) : precategory :=
  tpair _ C H.


Definition hs_precategory := total2 (λ C : precategory_data,
  dirprod (is_precategory C) (∏ a b : C, isaset (a --> b))).

Definition hs_precategory_has_homsets (C : hs_precategory) := pr2 (pr2 C).

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

Definition has_homsets (C : precategory_ob_mor) := ∏ a b : C, isaset (a --> b).

Lemma isaprop_has_homsets (C : precategory_ob_mor) : isaprop (has_homsets C).
Proof.
  do 2 (apply impred; intro).
  apply isapropisaset.
Qed.

Definition category := ∑ C:precategory, has_homsets C.
Definition category_pair C h : category := C,,h.
Definition category_to_precategory : category -> precategory := pr1.
Coercion category_to_precategory : category >-> precategory.
Definition homset_property (C : category) : has_homsets C := pr2 C.


Definition precategory_pair (C:precategory_data) (i:is_precategory C)
  : precategory := C,,i.

Definition makecategory
    (obj : UU)
    (mor : obj -> obj -> UU)
    (homsets : ∏ a b, isaset (mor a b))
    (identity : ∏ i, mor i i)
    (compose : ∏ i j k (f:mor i j) (g:mor j k), mor i k)
    (right : ∏ i j (f:mor i j), compose _ _ _ (identity i) f = f)
    (left  : ∏ i j (f:mor i j), compose _ _ _ f (identity j) = f)
    (associativity : ∏ a b c d (f:mor a b) (g:mor b c) (h:mor c d),
        compose _ _ _ f (compose _ _ _ g h) = compose _ _ _ (compose _ _ _ f g) h)
  : category
  := (precategory_pair
           (precategory_data_pair
              (precategory_ob_mor_pair
                 obj
                 (λ i j, mor i j))
              identity compose)
           ((right,,left),,associativity)),,homsets.


Lemma isaprop_is_precategory (C : precategory_data)(hs: has_homsets C)
  : isaprop (is_precategory C).
Proof.
  apply isofhleveltotal2.
  { apply isofhleveltotal2. { repeat (apply impred; intro). apply hs. }
    intros _. repeat (apply impred; intro); apply hs. }
  intros _. repeat (apply impred; intro); apply hs.
Qed.


Definition id_left (C : precategory) :
   ∏ (a b : C) (f : a --> b),
           identity a · f = f := pr1 (pr1 (pr2 C)).

Definition id_right (C : precategory) :
   ∏ (a b : C) (f : a --> b),
           f · identity b = f := pr2 (pr1 (pr2 C)).

Definition assoc (C : precategory) :
   ∏ (a b c d : C)
          (f : a --> b)(g : b --> c) (h : c --> d),
                     f · (g · h) = (f · g) · h := pr2 (pr2 C).

Arguments id_left [C a b] f.
Arguments id_right [C a b] f.
Arguments assoc [C a b c d] f g h.

Lemma assoc4 (C : precategory) (a b c d e : C) (f : a --> b) (g : b --> c)
       (h : c --> d) (i : d --> e) :
     ((f · g) · h) · i = f · (g · h) · i.
Proof.
  repeat rewrite assoc; apply idpath.
Qed.

Lemma remove_id_left (C : precategory) (a b : C) (f g : a --> b) (h : a --> a):
  h = identity _ -> f = g -> h · f = g.
Proof.
  intros H eq.
  pathvia (identity _ · f).
  - destruct H. apply idpath.
  - pathvia f.
    + apply id_left.
    + apply eq.
Defined.

Lemma remove_id_right (C : precategory) (a b : C) (f g : a --> b) (h : b --> b):
  h = identity _ -> f = g -> f · h = g.
Proof.
  intros H eq.
  pathvia (f · identity _).
  - destruct H. apply idpath.
  - pathvia f.
    + apply id_right.
    + apply eq.
Defined.

Lemma id_conjugation {A : precategory} {a b : A} (f : a --> b)
      (g : b --> a)  (x : b --> b)
  : x = identity _ -> f · g = identity _ -> f · x · g = identity _ .
Proof.
  intros H H'.
  rewrite H. rewrite id_right. apply H'.
Qed.


(** Any equality on objects a and b induces a morphism from a to b *)

Definition idtomor {C : precategory_data}
   (a b : C) (H : a = b) : a --> b.
Proof.
  induction H.
  exact (identity a).
Defined.

Definition idtomor_inv {C : precategory_data}
    (a b : C) (H : a = b) : b --> a.
Proof.
  induction H.
  exact (identity a).
Defined.

Lemma cancel_postcomposition {C : precategory_data} {a b c: C}
   (f f' : a --> b) (g : b --> c) : f = f' -> f · g = f' · g.
Proof.
  intro H.
  induction H.
  apply idpath.
Defined.

Lemma cancel_precomposition (C : precategory_data) (a b c: C)
   (f f' : b --> c) (g : a --> b) : f = f' -> g · f = g · f'.
Proof.
  intro H.
  induction H.
  apply idpath.
Defined.

(** * Setcategories: Precategories whose objects and morphisms are sets *)

Definition setcategory := total2 (
   λ C : precategory, dirprod (isaset (ob C)) (has_homsets C)).

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
   f · g.

Definition is_iso {C : precategory_data} {a b : C} (f : a --> b) :=
  ∏ c, isweq (precomp_with f (c:=c)).

Lemma isaprop_is_iso {C : precategory_data}(a b : C) (f : a --> b) : isaprop (is_iso f).
Proof.
  apply impred; intro.
  apply isapropisweq.
Qed.

Definition iso {C: precategory_data}(a b : C) := total2 (fun f : a --> b => is_iso f).
Definition morphism_from_iso (C:precategory_data)(a b : C) (f : iso a b) : a --> b := pr1 f.
Coercion morphism_from_iso : iso >-> precategory_morphisms.

Definition iso_is_iso {C: precategory_data} {a b : C} (f : iso a b) : is_iso f := pr2 f.

Definition isopair {C: precategory_data}{a b : C} (f : a --> b) (fiso: is_iso f) : iso a b :=
   tpair _ f fiso.

Definition inv_from_iso {C:precategory_data}{a b : C} (f : iso a b) : b --> a :=
   invmap (weqpair (precomp_with f) (pr2 f a)) (identity _ ).

Definition iso_inv_after_iso {C : precategory_data}{a b : C} (f: iso a b) :
   f · inv_from_iso f = identity _ .
Proof.
  set (T:=homotweqinvweq (weqpair (precomp_with f) (pr2 f a ))).
  simpl in *.
  apply T.
Defined.

Definition iso_after_iso_inv {C : precategory}{a b : C} (f : iso a b) :
  inv_from_iso f · f = identity _ .
Proof.
  set (T:= invmaponpathsweq (weqpair (precomp_with f) (pr2 f b))).
  apply T; clear T; simpl.
  unfold precomp_with.
  pathvia ((f· inv_from_iso f)·f).
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
    pathvia ((f · inv_from_iso f) · g).
    + apply assoc.
    + apply remove_id_left. apply iso_inv_after_iso. apply idpath.
  - intro g.
    unfold precomp_with.
    pathvia ((inv_from_iso f·f)·g).
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
  set (T:=@isweqhomot (a --> c) (a --> c) (λ t, t) (precomp_with (identity a))).
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
  (f : iso a  b) (g : b --> c) (h : a --> c) (H : h = f·g) :
     inv_from_iso f · h = g.
Proof.
  apply (invmaponpathsweq (weqpair (precomp_with f) (pr2 f c))).
  unfold precomp_with; simpl.
  pathvia ((f·inv_from_iso f)·h).
  - apply assoc.
  - apply remove_id_left.
    + apply iso_inv_after_iso.
    + assumption.
Defined.

Lemma iso_inv_on_left (C : precategory) (a b c: ob C)
  (f : a --> b) (g : iso b c) (h : a --> c) (H : h = f·g) :
     f = h · inv_from_iso g.
Proof.
  assert (H2 : h · inv_from_iso g =
                         (f· g) · inv_from_iso g).
    rewrite H. apply idpath.
  rewrite <- assoc in H2.
  rewrite iso_inv_after_iso in H2.
  rewrite id_right in H2.
  apply pathsinv0.
  assumption.
Qed.

Lemma iso_inv_to_left (C : precategory) (a b c: ob C)
  (f : iso a  b) (g : b --> c) (h : a --> c) :
    inv_from_iso f · h = g -> h = f · g.
Proof.
  intro H.
  transitivity (f· inv_from_iso f· h).
  - rewrite iso_inv_after_iso, id_left; apply idpath.
  - rewrite <- assoc. rewrite H. apply idpath.
Qed.

Lemma iso_inv_to_right (C : precategory) (a b c: ob C)
  (f : a --> b) (g : iso b c) (h : a --> c) :
     f = h · inv_from_iso g -> f · g = h.
Proof.
  intro H.
  transitivity (h· inv_from_iso g· g).
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
  set (T:=twooutof3c (precomp_with g) (precomp_with f(c:=d)) (pr2 g d) (pr2 f _)).
  apply (isweqhomot' _ _ T).
  intro h. apply assoc.
Defined.

Lemma is_iso_comp_of_is_isos {C : precategory} {a b c : ob C}
      (f : a --> b) (g : b --> c) (H1 : is_iso f) (H2 : is_iso g) : is_iso (f · g).
Proof.
  set (i1 := isopair f H1).
  set (i2 := isopair g H2).
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
  pathvia (f · (g·inv_from_iso g) · inv_from_iso f).
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
    (f : a --> b) (H : is_iso f) (g h : b --> c) : f · g = f · h -> g = h.
Proof.
  intro X.
  apply (invmaponpathsweq (weqpair (precomp_with f) (H _ ))).
  apply X.
Qed.

Lemma post_comp_with_iso_is_inj (C : precategory) (b c : ob C)
     (h : b --> c) (H : is_iso h)
   (a : ob C) (f g : a --> b) : f · h = g · h -> f = g.
Proof.
  intro HH.
  set (T:=iso_inv_after_iso (tpair _ h H)). simpl in T.
  pathvia (f · (h · inv_from_iso (tpair _ h H))).
  - rewrite T. clear T.
    apply pathsinv0, id_right.
  - rewrite assoc. rewrite HH.
    rewrite <- assoc. rewrite T.
    apply id_right.
Qed.


Lemma iso_comp_right_isweq {C:precategory_data} {a b:ob C} (h:iso a b) (c:C) :
  isweq (fun f : b --> c => h · f).
Proof.
  apply (pr2 h _ ).
Defined.

Definition iso_comp_right_weq {C:precategory_data} {a b:C} (h:iso a b) (c:C) :
 (b --> c) ≃ (a --> c) := weqpair _ (iso_comp_right_isweq h c).

Lemma iso_comp_left_isweq {C:precategory} {a b:ob C} (h:iso a b) (c:C) :
  isweq (fun f : c --> a => f · h).
Proof.
  intros. apply (gradth _ (λ g, g · inv_from_iso h)).
  - intro x. rewrite <- assoc. apply remove_id_right.
    apply iso_inv_after_iso. apply idpath.
  - intro y. rewrite <- assoc. apply remove_id_right.
    apply iso_after_iso_inv. apply idpath.
Defined.

Definition postcomp_with {C : precategory_data}{b c : C}(h : b --> c) {a : C}
  (f : a --> b) : a --> c := f · h.

Definition is_inverse_in_precat {C : precategory_data} {a b : C}
  (f : a --> b) (g : b --> a) :=
  dirprod (f · g = identity a)
          (g · f = identity b).

Definition mk_is_inverse_in_precat {C : precategory_data} {a b : C} {f : a --> b} {g : b --> a}
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
  dirprodpair (is_inverse_in_precat2 H) (is_inverse_in_precat1 H).

Definition is_inverse_in_precat_comp {C : precategory} {a b c : C} {f1 : a --> b} {f2 : b --> c}
           {g1 : b --> a} {g2 : c --> b} (H1 : is_inverse_in_precat f1 g1)
           (H2 : is_inverse_in_precat f2 g2) : is_inverse_in_precat (f1 · f2) (g2 · g1).
Proof.
  use mk_is_inverse_in_precat.
  - rewrite assoc. rewrite <- (assoc _ f2). rewrite (is_inverse_in_precat1 H2). rewrite id_right.
    rewrite (is_inverse_in_precat1 H1). apply idpath.
  - rewrite assoc. rewrite <- (assoc _ g1). rewrite (is_inverse_in_precat2 H1). rewrite id_right.
    rewrite (is_inverse_in_precat2 H2). apply idpath.
Qed.

Definition is_inverse_in_precat_identity {C : precategory} (c : C) :
  is_inverse_in_precat (identity c) (identity c).
Proof.
  use mk_is_inverse_in_precat.
  - apply id_left.
  - apply id_left.
Qed.

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
 (c --> a) ≃ (c --> b) := weqpair _ (iso_comp_left_isweq h c).

Definition iso_conjug_weq {C:precategory} {a b:C} (h:iso a b) :
 (a --> a) ≃ (b --> b) := weqcomp (iso_comp_left_weq h _ ) (iso_comp_right_weq (iso_inv_from_iso h) _ ).


(** * Equivalence relation identifying isomorphic objects *)
Section are_isomorphic.

Context (C : precategory).

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
  assert (H : g = identity b · g).
    rewrite id_left; apply idpath.
  apply (pathscomp0 H).
  rewrite <- eps'.
  rewrite <- assoc.
  rewrite eta.
  apply id_right.
Qed.

Definition is_z_isomorphism {C : precategory_data} {a b : ob C}
           (f : a --> b) := total2 (λ g, is_inverse_in_precat f g).

Definition mk_is_z_isomorphism {C : precategory_data} {a b : C} (f : a --> b)
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
  use mk_is_z_isomorphism.
  - exact f.
  - exact (is_inverse_in_precat_inv I).
Defined.

Definition is_z_isomorphism_comp {C : precategory} {a b c : C} {f1 : a --> b} {f2 : b --> c}
           (H1 : is_z_isomorphism f1) (H2 : is_z_isomorphism f2) :
  is_z_isomorphism (f1 · f2).
Proof.
  use mk_is_z_isomorphism.
  - exact (is_z_isomorphism_mor H2 · is_z_isomorphism_mor H1).
  - exact (is_inverse_in_precat_comp H1 H2).
Defined.

Definition is_z_isomorphism_identity {C : precategory} (c : C) : is_z_isomorphism (identity c).
Proof.
  use mk_is_z_isomorphism.
  - exact (identity c).
  - exact (is_inverse_in_precat_identity c).
Defined.

Lemma isaprop_is_z_isomorphism {C : precategory} {a b : ob C} (hs: has_homsets C)
     (f : a --> b) : isaprop (is_z_isomorphism f).
Proof.
  apply invproofirrelevance.
  intros g g'.
  set (Hpr1 := inverse_unique_precat _ _ _ _ _ _ (pr2 g) (pr2 g')).
  apply (total2_paths_f Hpr1).
  destruct g as [g [eta eps]].
  destruct g' as [g' [eta' eps']].
  simpl in *.
  apply isapropdirprod; apply hs.
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

Definition z_iso {C : precategory_data} (a b :ob C) := total2
    (fun f : a --> b => is_z_isomorphism f).

Definition mk_z_iso {C : precategory_data} {a b : C} (f : a --> b) (g : b --> a)
           (H : is_inverse_in_precat f g) : z_iso a b := (f,,mk_is_z_isomorphism f g H).

Definition z_iso_mor {C : precategory_data} {a b : ob C} (f : z_iso a b) : a --> b := pr1 f.
Coercion z_iso_mor : z_iso >-> precategory_morphisms.

Definition z_iso_inv_mor {C : precategory_data} {a b : C} (i : z_iso a b) : b --> a :=
  is_z_isomorphism_mor (pr2 i).

Definition z_iso_is_inverse_in_precat {C : precategory_data} {a b : C} (i : z_iso a b) :
  is_inverse_in_precat i (z_iso_inv_mor i) := pr2 i.
Coercion z_iso_is_inverse_in_precat : z_iso >-> is_inverse_in_precat.

Definition z_iso_inv {C : precategory_data} {a b : C} (I : z_iso a b) : z_iso b a.
Proof.
  use mk_z_iso.
  - exact (z_iso_inv_mor I).
  - exact I.
  - exact (is_inverse_in_precat_inv I).
Defined.

Definition z_iso_comp {C : precategory} {a b c : C} (I1 : z_iso a b) (I2 : z_iso b c) :
  z_iso a c.
Proof.
  use mk_z_iso.
  - exact (I1 · I2).
  - exact ((z_iso_inv_mor I2) · (z_iso_inv_mor I1)).
  - exact (is_inverse_in_precat_comp I1 I2).
Defined.

Definition z_iso_identity {C : precategory} (c : C) : z_iso c c.
Proof.
  use mk_z_iso.
  - exact (identity c).
  - exact (identity c).
  - exact (is_inverse_in_precat_identity c).
Defined.

Definition z_iso_is_z_isomorphism1 {C : precategory} {a b : C} (I : z_iso a b) :
  is_z_isomorphism I.
Proof.
  use mk_is_z_isomorphism.
  - exact (z_iso_inv_mor I).
  - exact I.
Defined.

Definition z_iso_is_z_isomorphism2 {C : precategory} {a b : C} (I : z_iso a b) :
  is_z_isomorphism (z_iso_inv_mor I).
Proof.
  use mk_is_z_isomorphism.
  - exact I.
  - exact (is_inverse_in_precat_inv I).
Defined.

Lemma post_comp_with_z_iso_is_inj {C : precategory} {a' a b : C} {f : a --> b} {g : b --> a}
      (i : is_inverse_in_precat f g) : ∏ (f' g' : a' --> a), f' · f = g' · f -> f' = g'.
Proof.
  intros f' g' H.
  apply (maponpaths (postcompose g)) in H. unfold postcompose in H.
  rewrite <- assoc in H. rewrite <- assoc in H.
  rewrite (is_inverse_in_precat1 i) in H. rewrite id_right in H. rewrite id_right in H.
  exact H.
Qed.

Lemma post_comp_with_z_iso_inv_is_inj {C : precategory} {a b b' : C} {f : a --> b} {g : b --> a}
      (i : is_inverse_in_precat f g) : ∏ (f' g' : b' --> b), f' · g = g' · g -> f' = g'.
Proof.
  intros f' g' H.
  apply (maponpaths (postcompose f)) in H. unfold postcompose in H.
  rewrite <- assoc in H. rewrite <- assoc in H.
  rewrite (is_inverse_in_precat2 i) in H. rewrite id_right in H. rewrite id_right in H.
  exact H.
Qed.

Lemma pre_comp_with_z_iso_is_inj {C : precategory} {a b b' : C} {f : a --> b} {g : b --> a}
      (i : is_inverse_in_precat f g) : ∏ (f' g' : b --> b'), f · f' = f · g' -> f' = g'.
Proof.
  intros f' g' H.
  apply (maponpaths (compose g)) in H.
  rewrite assoc in H. rewrite assoc in H.
  rewrite (is_inverse_in_precat2 i) in H. rewrite id_left in H. rewrite id_left in H.
  exact H.
Qed.

Lemma pre_comp_with_z_iso_inv_is_inj {C : precategory} {a' a b : C} {f : a --> b} {g : b --> a}
      (i : is_inverse_in_precat f g) : ∏ (f' g' : a --> a'), g · f' = g · g' -> f' = g'.
Proof.
  intros f' g' H.
  apply (maponpaths (compose f)) in H.
  rewrite assoc in H. rewrite assoc in H.
  rewrite (is_inverse_in_precat1 i) in H. rewrite id_left in H. rewrite id_left in H.
  exact H.
Qed.

Lemma z_iso_eq {C : category} {a b : C} (i i' : z_iso a b) (e : z_iso_mor i = z_iso_mor i') :
  i = i'.
Proof.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. apply isaprop_is_z_isomorphism. apply homset_property.
Qed.

Lemma z_iso_eq_inv {C : category} {a b : C} (i i' : z_iso a b)
      (e2 : z_iso_inv_mor i = z_iso_inv_mor i') : i = i'.
Proof.
  use z_iso_eq.
  assert (H : is_inverse_in_precat (z_iso_inv_mor i) i').
  {
    use mk_is_inverse_in_precat.
    - rewrite e2. exact (is_inverse_in_precat2 i').
    - rewrite e2. exact (is_inverse_in_precat1 i').
  }
  exact (inverse_unique_precat _ _ _ _ _ _ (z_iso_inv i) H).
Qed.

Lemma eq_z_iso (C : precategory)(hs: has_homsets C) (a b : ob C)
   (f g : z_iso a b) : pr1 f = pr1 g -> f = g.
Proof.
  intro H.
  apply (total2_paths_f H).
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
   (f : z_iso a b) : f· inv_from_z_iso f = identity _ :=
      pr1 (pr2 (pr2 f)).

Definition z_iso_after_z_iso_inv (C : precategory_data) (a b : ob C)
   (f : z_iso a b) : inv_from_z_iso f · f = identity _ :=
      pr2 (pr2 (pr2 f)).


Lemma z_iso_inv_on_right (C : precategory) (a b c: ob C)
  (f : z_iso a  b) (g : b --> c) (h : a --> c) (H : h = f·g) :
     inv_from_z_iso f · h = g.
Proof.
  assert (H2 : inv_from_z_iso f· h =
                  inv_from_z_iso f· (f · g)).
  apply maponpaths; assumption.
  rewrite assoc in H2.
  rewrite H2.
  rewrite z_iso_after_z_iso_inv.
  apply id_left.
Qed.

Lemma z_iso_inv_on_left (C : precategory) (a b c: ob C)
  (f : a --> b) (g : z_iso b c) (h : a --> c) (H : h = f·g) :
     f = h · inv_from_z_iso g.
Proof.
  assert (H2 : h · inv_from_z_iso g =
                         (f· g) · inv_from_z_iso g).
    rewrite H. apply idpath.
  rewrite <- assoc in H2.
  rewrite z_iso_inv_after_z_iso in H2.
  rewrite id_right in H2.
  apply pathsinv0.
  assumption.
Qed.

Lemma z_iso_inv_to_left (C : precategory) (a b c: ob C)
  (f : z_iso a  b) (g : b --> c) (h : a --> c) :
    inv_from_z_iso f · h = g -> h = f · g.
Proof.
  intro H.
  transitivity (f· inv_from_z_iso f· h).
  - rewrite z_iso_inv_after_z_iso, id_left; apply idpath.
  - rewrite <- assoc. rewrite H. apply idpath.
Qed.

Lemma z_iso_inv_to_right (C : precategory) (a b c: ob C)
  (f : a --> b) (g : z_iso b c) (h : a --> c) :
     f = h · inv_from_z_iso g -> f · g = h.
Proof.
  intro H.
  transitivity (h· inv_from_z_iso g· g).
  - rewrite H. apply idpath.
  - rewrite <- assoc, z_iso_after_z_iso_inv, id_right. apply idpath.
Qed.


(** ** Properties of isomorphisms *)
(** Stability under composition, inverses etc *)

Lemma are_inverse_comp_of_inverses (C : precategory) (a b c : C)
     (f : z_iso a b) (g : z_iso b c) :
  is_inverse_in_precat (f· g) (inv_from_z_iso g· inv_from_z_iso f).
Proof.
  simpl; split; simpl;
  unfold inv_from_iso; simpl.
  destruct f as [f [f' Hf]]. simpl in *.
  destruct g as [g [g' Hg]]; simpl in *.
  pathvia ((f · (g · g')) · f').
  repeat rewrite assoc; apply idpath.
  rewrite (pr1 Hg).
  rewrite id_right.
  rewrite (pr1 Hf).
  apply idpath.

  destruct f as [f [f' Hf]]. simpl in *.
  destruct g as [g [g' Hg]]; simpl in *.
  pathvia ((g' · (f' · f)) · g).
  repeat rewrite assoc; apply idpath.
  rewrite (pr2 Hf).
  rewrite id_right.
  rewrite (pr2 Hg).
  apply idpath.
Qed.

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

Lemma z_iso_comp_right_isweq {C:precategory} {a b:ob C} (h:z_iso a b) (c:C) :
  isweq (fun f : b --> c => h · f).
Proof.
  intros. apply (gradth _ (λ g, inv_from_z_iso h · g)).
       { intros f. refine (_ @ maponpaths (λ m, m · f) (pr2 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } }
       { intros g. refine (_ @ maponpaths (λ m, m · g) (pr1 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } }
Defined.

Definition z_iso_comp_right_weq {C:precategory} {a b:C} (h:z_iso a b) (c:C) :
 (b --> c) ≃ (a --> c) := weqpair _ (z_iso_comp_right_isweq h c).

Lemma z_iso_comp_left_isweq {C:precategory} {a b:ob C} (h:z_iso a b) (c:C) :
  isweq (fun f : c --> a => f · h).
Proof.
  intros. apply (gradth _ (λ g, g · inv_from_z_iso h)).
       { intros f. refine (_ @ maponpaths (λ m, f·m) (pr1 (pr2 (pr2 h))) @ _).
         { apply pathsinv0. apply assoc. }  { apply id_right. } }
       { intros g. refine (_ @ maponpaths (λ m, g·m) (pr2 (pr2 (pr2 h))) @ _).
         { apply pathsinv0, assoc. } { apply id_right. } }
Defined.
Definition z_iso_comp_left_weq {C:precategory} {a b:C} (h:z_iso a b) (c:C) :
 (c --> a) ≃ (c --> b) := weqpair _ (z_iso_comp_left_isweq h c).

Definition z_iso_conjug_weq {C:precategory} {a b:C} (h:z_iso a b) :
 (a --> a) ≃ (b --> b) := weqcomp (z_iso_comp_left_weq h _ )
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
  induction H.
  exact (identity_iso a).
Defined.

(* use eta expanded version to force printing of object arguments *)
Definition is_univalent (C : precategory) :=
  (∏ (a b : ob C), isweq (fun p : a = b => idtoiso p)) × (has_homsets C).

Definition mk_is_univalent {C : precategory} (H1 : ∏ (a b : ob C), isweq (fun p : a = b => idtoiso p))
           (H2 : has_homsets C) : is_univalent C := dirprodpair H1 H2.

Lemma eq_idtoiso_idtomor {C:precategory} (a b:ob C) (e:a = b) :
    pr1 (idtoiso e) = idtomor _ _ e.
Proof.
  destruct e; reflexivity.
Defined.

Lemma isaprop_is_univalent (C : precategory) : isaprop (is_univalent C).
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

Definition univalent_category : UU := total2 (λ C : precategory, is_univalent C).

Definition mk_category (C : precategory) (H : is_univalent C) : univalent_category := tpair _ C H.

Definition univalent_category_to_category (C : univalent_category) : category.
Proof.
  exists (pr1 C).
  exact (pr2 (pr2 C)).
Defined.
Coercion univalent_category_to_category : univalent_category >-> category.

Definition univalent_category_pair (C:precategory) (i:is_univalent C) : univalent_category := C,,i.


Definition univalent_category_has_homsets (C : univalent_category) := pr2 (pr2 C).

Definition univalent_category_is_univalent (C : univalent_category) : is_univalent C := pr2 C.

Lemma univalent_category_has_groupoid_ob (C : univalent_category): isofhlevel 3 (ob C).
Proof.
  change (isofhlevel 3 C) with
        (∏ a b : C, isofhlevel 2 (a = b)).
  intros a b.
  apply (isofhlevelweqb _ (tpair _ _ (pr1 (pr2 C) a b))).
  apply isaset_iso.
  apply (pr2 (pr2 C)).
Qed.

(** ** Definition of [isotoid] *)

Definition isotoid (C : precategory) (H : is_univalent C) {a b : ob C}:
      iso a b -> a = b := invmap (weqpair _ (pr1 H a b)).

Lemma idtoiso_isotoid (C : precategory) (H : is_univalent C) (a b : ob C)
    (f : iso a b) : idtoiso (isotoid _ H f) = f.
Proof.
  unfold isotoid.
  set (Hw := homotweqinvweq (weqpair idtoiso (pr1 H a b))).
  simpl in Hw.
  apply Hw.
Qed.

Lemma isotoid_idtoiso (C : precategory) (H : is_univalent C) (a b : ob C)
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
  transportf (λ c, a' --> c) q (transportf (λ c, c --> b) p f).

Lemma idtoiso_postcompose (C : precategory) (a b b' : ob C)
  (p : b = b') (f : a --> b) :
      f · idtoiso p = transportf (λ b, a --> b) p f.
Proof.
  destruct p.
  apply id_right.
Qed.

Lemma idtoiso_postcompose_iso (C : precategory) (hs: has_homsets C) (a b b' : ob C)
  (p : b = b') (f : iso a b) :
    iso_comp f (idtoiso p) = transportf (λ b, iso a b) p f.
Proof.
  destruct p.
  apply eq_iso.
  apply id_right.
Qed.

Lemma idtoiso_precompose (C : precategory) (a a' b : ob C)
  (p : a = a') (f : a --> b) :
      (idtoiso (!p)) · f = transportf (λ a, a --> b) p f.
Proof.
  destruct p.
  apply id_left.
Qed.

Lemma idtoiso_precompose_iso (C : precategory) (hs: has_homsets C) (a a' b : ob C)
  (p : a = a') (f : iso a b) :
      iso_comp (idtoiso (!p)) f = transportf (λ a, iso a b) p f.
Proof.
  destruct p.
  apply eq_iso.
  apply id_left.
Qed.

Lemma double_transport_idtoiso (C : precategory) (a a' b b' : ob C)
  (p : a = a') (q : b = b')  (f : a --> b) :
  double_transport p q f = inv_from_iso (idtoiso p) · f · idtoiso q.
Proof.
  destruct p.
  destruct q.
  pathvia (identity _ · f).
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

Lemma idtoiso_inj (C : precategory) (H : is_univalent C) (a a' : ob C)
   (p p' : a = a') : idtoiso p = idtoiso p' -> p = p'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply H.
Qed.

Lemma isotoid_inj (C : precategory) (H : is_univalent C) (a a' : ob C)
   (f f' : iso a a') : isotoid _ H f = isotoid _ H f' -> f = f'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply isweqinvmap.
Qed.

Lemma isotoid_comp (C : precategory) (H : is_univalent C) (a b c : ob C)
  (e : iso a b) (f : iso b c) :
  isotoid _ H (iso_comp e f) = isotoid _ H e @ isotoid _ H f.
Proof.
  apply idtoiso_inj.
    assumption.
  rewrite idtoiso_concat.
  repeat rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma isotoid_identity_iso (C : precategory) (H : is_univalent C) (a : C) :
  isotoid _ H (identity_iso a) = idpath _ .
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid;
  apply idpath.
Qed.

Lemma inv_isotoid (C : precategory) (H : is_univalent C) (a b : C)
    (f : iso a b) : ! isotoid _ H f = isotoid _ H (iso_inv_from_iso f).
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid (C : precategory) (H : is_univalent C)
   (a a' b : ob C) (p : iso a a') (f : a --> b) :
 transportf (λ a0 : C, a0 --> b) (isotoid C H p) f = inv_from_iso p · f.
Proof.
  rewrite <- idtoiso_precompose.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid' (C : precategory) (H : is_univalent C)
   (a b b' : ob C) (p : iso b b') (f : a --> b) :
 transportf (λ a0 : C, a --> a0) (isotoid C H p) f = f · p.
Proof.
  rewrite <- idtoiso_postcompose.
  apply maponpaths.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid_dep (C : precategory)
   (a a' : C) (p : a = a') (f : ∏ c, a --> c) :
 transportf (λ x : C, ∏ c, x --> c) p f = λ c, idtoiso (!p) · f c.
Proof.
  destruct p.
  simpl.
  apply funextsec.
  intro.
  rewrite id_left.
  apply idpath.
Qed.

Lemma forall_isotoid (A : precategory) (a_is : is_univalent A)
      (a a' : A) (P : iso a a' -> UU) :
  (∏ e, P (idtoiso e)) → ∏ i, P i.
Proof.
  intros H i.
  rewrite <- (idtoiso_isotoid _ a_is).
  apply H.
Defined.

Lemma transportf_isotoid_dep' (J : UU) (C : precategory) (F : J -> C)
  (a a' : C) (p : a = a') (f : ∏ c, a --> F c) :
  transportf (λ x : C, ∏ c, x --> F c) p f = λ c, idtoiso (!p) · f c.
Proof.
  now destruct p; apply funextsec; intro x; rewrite id_left.
Defined.

(* This and the above name is not very good... *)
 Lemma transportf_isotoid_dep'' (J : UU) (C : precategory) (F : J -> C)
   (a a' : C) (p : a = a') (f : ∏ c, F c --> a) :
   transportf (λ x : C, ∏ c, F c --> x) p f = λ c, f c · idtoiso p.
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
     λ abf, pr1 (pr1 abf).

Definition precategory_target (C : precategory_ob_mor) :
     total_morphisms C -> ob C :=
     λ abf, pr2 (pr1 abf).

Definition precategory_total_id (C : precategory_data) :
      ob C -> total_morphisms C :=
      λ c, tpair _ (dirprodpair c c) (identity c).

Definition precategory_total_comp'' (C : precategory_data) :
      ∏ f g : total_morphisms C,
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
  exact ((f · idtomor _ _ e) · g).
Defined.

Definition precategory_total_comp (C : precategory_data) :
      ∏ f g : total_morphisms C,
        precategory_target C f = precategory_source C g ->
         total_morphisms C :=
  λ f g e,
     tpair _ (dirprodpair (pr1 (pr1 f))(pr2 (pr1 g)))
        ((pr2 f · idtomor _ _ e) · pr2 g).


(** ** Transport of morphisms *)


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
