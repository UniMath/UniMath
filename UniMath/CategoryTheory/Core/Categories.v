(** * Categories

  Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman
  January 2013
 *)


(** ** Contents :

  - precategories: homs are arbitrary types [precategory]
  - categories: hom-types are sets [category]
 *)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.

(** * Definition of a precategory *)

Definition precategory_ob_mor : UU
  := ∑ ob : UU, ob -> ob -> UU.

Definition make_precategory_ob_mor (ob : UU)(mor : ob -> ob -> UU) :
    precategory_ob_mor := tpair _ ob mor.

Definition ob (C : precategory_ob_mor) : UU := @pr1 _ _ C.
Coercion ob : precategory_ob_mor >-> UU.

Definition precategory_morphisms { C : precategory_ob_mor } :
       C ->  C -> UU := pr2 C.

(** We introduce notation for morphisms *)
(** in order for this notation not to pollute subsequent files,
    we define this notation within the scope "cat" *)

Declare Scope cat.
Delimit Scope cat with cat.     (* for precategories *)
Local Open Scope cat.

Notation "a --> b" := (precategory_morphisms a b) : cat.
Notation "b <-- a" := (precategory_morphisms a b) (only parsing) : cat.

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

Definition precategory_id_comp (C : precategory_ob_mor) : UU
  :=
    (∏ c : C, c --> c) (* identities *)
      ×
    (∏ a b c : C, a --> b -> b --> c -> a --> c). (* composition *)

Definition precategory_data : UU
  := ∑ C : precategory_ob_mor, precategory_id_comp C.

Definition make_precategory_data (C : precategory_ob_mor)
    (id : ∏ c : C, c --> c)
    (comp: ∏ a b c : C, a --> b -> b --> c -> a --> c)
  : precategory_data
  := tpair _ C (make_dirprod id comp).

Definition precategory_ob_mor_from_precategory_data (C : precategory_data) :
     precategory_ob_mor := pr1 C.
Coercion precategory_ob_mor_from_precategory_data :
  precategory_data >-> precategory_ob_mor.

Definition identity {C : precategory_data}
  : ∏ c : C, c --> c
  := pr1 (pr2 C).

Definition compose {C : precategory_data} { a b c : C }
  : a --> b -> b --> c -> a --> c
  := pr2 (pr2 C) a b c.

Notation "f · g" := (compose f g) : cat.
(* to input: type "\centerdot" or "\cdot" with Agda input method *)

Notation "g ∘ f" := (compose f g) (only parsing) : cat.
(* agda input \circ *)

Definition postcompose {C : precategory_data} {a b c : C} (g : b --> c) (f : a --> b)
  : a --> c
  := compose f g.

(** ** Axioms of a precategory *)
(**
        - identity is left and right neutral for composition
        - composition is associative
*)

Definition is_precategory (C : precategory_data) : UU
  :=
    ((∏ (a b : C) (f : a --> b), identity a · f = f)
     ×
     (∏ (a b : C) (f : a --> b), f · identity b = f))
    ×
    ((∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
       ×
     (∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d), (f · g) · h = f · (g · h))).

Definition is_precategory_one_assoc (C : precategory_data) : UU
  :=
    ((∏ (a b : C) (f : a --> b), identity a · f = f)
     ×
     (∏ (a b : C) (f : a --> b), f · identity b = f))
    ×
    (∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h).

Definition is_precategory_one_assoc_to_two (C : precategory_data) :
  is_precategory_one_assoc C -> is_precategory C
  := λ i, (pr11 i,,pr21 i),,(pr2 i,,λ a b c d f g h, pathsinv0 (pr2 i a b c d f g h)).

Definition make_is_precategory {C : precategory_data}
           (H1 : ∏ (a b : C) (f : a --> b), identity a · f = f)
           (H2 : ∏ (a b : C) (f : a --> b), f · identity b = f)
           (H3 : ∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
           (H4 : ∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d), (f · g) · h = f · (g · h))
  : is_precategory C
  := (H1,,H2),,(H3,,H4).

Definition make_is_precategory_one_assoc {C : precategory_data}
           (H1 : ∏ (a b : C) (f : a --> b), identity a · f = f)
           (H2 : ∏ (a b : C) (f : a --> b), f · identity b = f)
           (H3 : ∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d), f · (g · h) = (f · g) · h)
  : is_precategory C
  := (H1,,H2),,(H3,,λ a b c d f g h, pathsinv0 (H3 a b c d f g h)).

Definition precategory := total2 is_precategory.

Definition make_precategory (C : precategory_data) (H : is_precategory C)
  : precategory
  := tpair _ C H.

Definition make_precategory_one_assoc (C : precategory_data) (H : is_precategory_one_assoc C)
  : precategory
  := tpair _ C (is_precategory_one_assoc_to_two C H).

Definition precategory_data_from_precategory (C : precategory) :
       precategory_data := pr1 C.
Coercion precategory_data_from_precategory : precategory >-> precategory_data.

Definition has_homsets (C : precategory_ob_mor) : UU := ∏ a b : C, isaset (a --> b).

Lemma isaprop_has_homsets (C : precategory_ob_mor) : isaprop (has_homsets C).
Proof.
  do 2 (apply impred; intro).
  apply isapropisaset.
Qed.

Definition category := ∑ C:precategory, has_homsets C.
Definition make_category C h : category := C,,h.
Definition category_to_precategory : category -> precategory := pr1.
Coercion category_to_precategory : category >-> precategory.
Coercion homset_property (C : category) : has_homsets C := pr2 C.

Definition homset
           {C : category}
           (x y : C)
  : hSet
  := x --> y ,, homset_property C x y.

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
    (associativity' : ∏ a b c d (f:mor a b) (g:mor b c) (h:mor c d),
        compose _ _ _ (compose _ _ _ f g) h = compose _ _ _ f (compose _ _ _ g h))
  : category
  := (make_precategory
           (make_precategory_data
              (make_precategory_ob_mor
                 obj
                 (λ i j, mor i j))
              identity compose)
           ((right,,left),,(associativity,,associativity'))),,homsets.

Lemma isaprop_is_precategory (C : precategory_data)(hs: has_homsets C)
  : isaprop (is_precategory C).
Proof.
  apply isofhleveltotal2.
  { apply isofhleveltotal2. { repeat (apply impred; intro). apply hs. }
    intros _. repeat (apply impred; intro); apply hs. }
  intros _. apply isofhleveltotal2.
  { repeat (apply impred; intro); apply hs. }
  { intros. repeat (apply impred; intro). apply hs. }
Qed.

Lemma category_eq (C D : category) :
  (C:precategory_data) = (D:precategory_data) -> C=D.
Proof.
  intro e. apply subtypePath. intro. apply isaprop_has_homsets.
  apply subtypePath'.
  { assumption. }
  apply isaprop_is_precategory.
  apply homset_property.
Defined.

Definition id_left (C : precategory) :
   ∏ (a b : C) (f : a --> b),
           identity a · f = f := pr112 C.

Definition id_right (C : precategory) :
   ∏ (a b : C) (f : a --> b),
           f · identity b = f := pr212 C.

Definition assoc (C : precategory) :
   ∏ (a b c d : C)
          (f : a --> b) (g : b --> c) (h : c --> d),
                     f · (g · h) = (f · g) · h := pr122 C.

Definition assoc' (C : precategory) :
   ∏ (a b c d : C)
          (f : a --> b) (g : b --> c) (h : c --> d),
                     (f · g) · h = f · (g · h) := pr222 C.

Arguments id_left [C a b] f.
Arguments id_right [C a b] f.
Arguments assoc [C a b c d] f g h.
Arguments assoc' [C a b c d] f g h.

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
  intermediate_path (identity _ · f).
  - destruct H. apply idpath.
  - intermediate_path f.
    + apply id_left.
    + apply eq.
Defined.

Lemma remove_id_right (C : precategory) (a b : C) (f g : a --> b) (h : b --> b):
  h = identity _ -> f = g -> f · h = g.
Proof.
  intros H eq.
  intermediate_path (f · identity _).
  - destruct H. apply idpath.
  - intermediate_path f.
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

Lemma cancel_postcomposition {C : precategory_data} {a b c: C}
   (f f' : a --> b) (g : b --> c) : f = f' -> f · g = f' · g.
Proof.
  intro; apply maponpaths_2; assumption.
Defined.

Lemma cancel_precomposition (C : precategory_data) (a b c: C)
   (f f' : b --> c) (g : a --> b) : f = f' -> g · f = g · f'.
Proof.
  apply maponpaths.
Defined.

Lemma maponpaths_compose
      {C : category} {x y z : C} (f1 f2 : C⟦x,y⟧) (g1 g2 : C⟦y,z⟧)
  : f1 = f2 -> g1 = g2 -> f1 · g1 = f2 · g2.
Proof.
  exact (λ p q, maponpaths_12 compose p q).
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

