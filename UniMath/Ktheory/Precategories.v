(* -*- coding: utf-8 -*- *)

Require Import UniMath.Ktheory.Utilities.
Require Import UniMath.CategoryTheory.precategories
               UniMath.CategoryTheory.opp_precat
               UniMath.CategoryTheory.yoneda
               UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.category_hset.
Delimit Scope cat with cat.
Local Open Scope cat.

Arguments id_left [C a b] f.
Arguments id_right [C a b] f.
Arguments assoc [C a b c d] f g h.

Notation "a → b" := (precategory_morphisms a b) (at level 50) : cat.
(* agda input \r- or \to or \-> or \rightarrow or \r menu *)

Definition src {C:precategory} {a b:C} (f:a→b) : C := a.
Definition tar {C:precategory} {a b:C} (f:a→b) : C := b.

Definition Precategory := Σ C:precategory, has_homsets C.
Definition Precategory_pair C h : Precategory := C,,h.
Definition Precategory_to_precategory : Precategory -> precategory := pr1.
Coercion Precategory_to_precategory : Precategory >-> precategory.
Definition homset_property (C:Precategory) : has_homsets C := pr2 C.
Definition Precategory_mor (C:Precategory) : ob C -> ob C -> hSet :=
  λ c c', hSetpair (c → c') (homset_property C _ _ ).
Notation Hom := Precategory_mor.

Ltac eqn_logic :=
  repeat (
      try intro; try split; try apply id_right; try apply id_left; try apply assoc;
      try apply funextsec; try apply homset_property;
      try refine (total2_paths2 _ _);
      try refine (total2_paths _ _);
      try refine (nat_trans_ax _ _ _ _); try refine (! nat_trans_ax _ _ _ _);
      try apply functor_id;
      try apply functor_comp;
      try apply isaprop_is_nat_trans
    ).

Ltac set_logic :=
  repeat (
      try intro; try apply isaset_total2; try apply isasetdirprod; try apply homset_property;
      try apply impred_isaset; try apply isasetaprop).

Definition functorPrecategory (C D:Precategory) : Precategory.
Proof.
  intros. exists (functor_precategory C D (homset_property D)).
  abstract set_logic using L.
Defined.

Notation "[ C , D ]" := (functorPrecategory C D) : cat.

Definition oppositePrecategory (C:Precategory) : Precategory.
Proof.
  intros. exists (opp_precat C). apply has_homsets_opp, homset_property.
Defined.

Notation "C '^op'" := (oppositePrecategory C) (at level 3) : cat.

Definition opp_ob {C:Precategory} : ob C -> ob C^op
  := λ c, c.

Definition opp_mor {C:Precategory} {b c:C} : Hom C b c -> Hom C^op c b
  := λ f, f.

Definition category_to_Precategory (C:category) : Precategory.
Proof.
  intros.
  refine (_,,_).
  - exact C.
  - exact (pr2 (pr2 C)).
Defined.

Coercion category_to_Precategory : category >-> Precategory.

Notation "b ← a" := (precategory_morphisms a b) (at level 50, only parsing) : cat.
(* agda input \l- or \leftarrow or \<- or \gets or or \l menu *)

(* Open scope cat' to see what categories maps are in.  This helps
   especially when a category and its opposite are both in play. *)
Notation "C [ a , b ]" := (@precategory_morphisms C a b) (at level 50) : cat'.

Notation "a ==> b" := (functor a b) (at level 50) : cat.

Notation "F ⟶ G" := (nat_trans F G) (at level 39) : cat.
(* agda-input \--> or \r-- or \r menu *)

(* Notation "f ;; g" := (precategories.compose f g) (at level 50, only parsing) : cat. *)

Notation "g ∘ f" := (precategories.compose f g) (at level 50, left associativity) : cat.
(* agda input \circ *)

Notation "# F" := (functor_on_morphisms F) (at level 3) : cat.

Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35) : cat.
(* agda input \square *)

Definition precategory_pair (C:precategory_data) (i:is_precategory C)
  : precategory := C,,i.

Definition Precategory_obmor (C:precategory) : precategory_ob_mor :=
      precategory_ob_mor_from_precategory_data (
          precategory_data_from_precategory C).

Definition Functor_obmor {C D} (F:functor C D) := pr1 F.
Definition Functor_obj {C D} (F:functor C D) := pr1 (pr1 F).
Definition Functor_mor {C D} (F:functor C D) := pr2 (pr1 F).
Definition Functor_identity {C D} (F:functor C D) := functor_id F.
Definition Functor_compose {C D} (F:functor C D) := functor_comp F.

Definition category_pair (C:precategory) (i:is_category C) : category := C,,i.

Definition theUnivalenceProperty (C:category) := pr2 _ : is_category C.

Definition reflects_isos {C D} (X:C==>D) :=
  ∀ c c' (f : c → c'), is_isomorphism (#X f) -> is_isomorphism f.

Lemma isaprop_reflects_isos {C D} (X:C==>D) : isaprop (reflects_isos X).
Proof.
  intros. apply impred; intros. apply impred; intros. apply impred; intros.
  apply impred; intros. apply isaprop_is_isomorphism. Qed.

(** *** make a precategory *)

Definition makePrecategory_ob_mor
    (obj : UU)
    (mor : obj -> obj -> UU)
    : precategory_ob_mor.
  intros.
  exact (precategory_ob_mor_pair obj (fun i j:obj => mor i j)).
Defined.

Definition makePrecategory_data
    (obj : UU)
    (mor : obj -> obj -> UU)
    (identity : ∀ i, mor i i)
    (compose : ∀ i j k (f:mor i j) (g:mor j k), mor i k)
    : precategory_data.
  intros.
  exact (precategory_data_pair (makePrecategory_ob_mor obj mor) identity compose).
Defined.

Definition makePrecategory
    (obj : UU)
    (mor : obj -> obj -> UU)
    (homsets : ∀ a b, isaset (mor a b))
    (identity : ∀ i, mor i i)
    (compose : ∀ i j k (f:mor i j) (g:mor j k), mor i k)
    (right : ∀ i j (f:mor i j), compose _ _ _ (identity i) f = f)
    (left  : ∀ i j (f:mor i j), compose _ _ _ f (identity j) = f)
    (associativity : ∀ a b c d (f:mor a b) (g:mor b c) (h:mor c d),
        compose _ _ _ f (compose _ _ _ g h) = compose _ _ _ (compose _ _ _ f g) h)
    : Precategory.
  intros.
  exact ((precategory_pair
           (precategory_data_pair
              (precategory_ob_mor_pair
                 obj
                 (fun i j => mor i j))
              identity compose)
           ((right,,left),,associativity)),,homsets). Defined.

Definition makeFunctor {C D:Precategory}
           (obj : C -> D)
           (mor : ∀ c c' : C, c → c' -> obj c → obj c')
           (identity : ∀ c, mor c c (identity c) = identity (obj c))
           (compax : ∀ (a b c : C) (f : a → b) (g : b → c),
                       mor a c (g ∘ f) = mor b c g ∘ mor a b f) :
  C ==> D
  := (obj,, mor),, identity,, compax.

(** *** opposite category of opposite category *)

Lemma opp_opp_precat_ob_mor (C : precategory_ob_mor) : C = opp_precat_ob_mor (opp_precat_ob_mor C).
Proof. intros [ob mor]. reflexivity. Defined.

Lemma opp_opp_precat_ob_mor_compute (C : precategory_ob_mor) :
  idpath _ = maponpaths precategory_id_comp (opp_opp_precat_ob_mor C).
Proof. intros [ob mor]. reflexivity. Defined.

Lemma opp_opp_precat_data (C : precategory_data)
   : C = opp_precat_data (opp_precat_data C).
Proof. intros [[ob mor] [id co]]. reflexivity. Defined.

Lemma opp_opp_precat (C:Precategory) : C = C^op^op.
Proof.
  intros.
  apply subtypeEquality'.
  (* the only reason we can't use subtypeEquality is because the homset condition is divorced from the precategory *)
  { apply subtypeEquality'.
    { apply opp_opp_precat_data. }
    { apply isaprop_is_precategory. apply has_homsets_opp, homset_property. } }
  { apply isaprop_has_homsets. }
Defined.

(* new categories from old *)

Definition categoryWithStructure {C:Precategory} (P:ob C -> UU) : Precategory.
Proof.
  intros. refine (makePrecategory _ _ _ _ _ _ _ _).
  (* add a new component to each object: *)
  - exact (Σ c:C, P c).
  (* the homsets ignore the extra structure: *)
  - intros x y. exact (pr1 x → pr1 y).
  (* the rest is the same: *)
  - intros. apply homset_property.
  - intros x. apply identity.
  - intros x y z f g. exact (g ∘ f).
  - intros. apply id_left.
  - intros. apply id_right.
  - intros. apply assoc.
Defined.

Definition functorWithStructures {C:Precategory} {P Q:ob C -> UU}
           (F : ∀ c, P c -> Q c) : categoryWithStructure P ==> categoryWithStructure Q.
Proof.
  intros. refine (makeFunctor _ _ _ _).
  (* transport the structure: *)
  - exact (λ c, (pr1 c,, F (pr1 c) (pr2 c))).
  (* the rest is the same: *)
  - intros c c' f. exact f.
  - reflexivity.
  - reflexivity.
Defined.

Definition SET : Precategory := (hset_precategory,, category_hset.has_homsets_HSET).

Lemma identityFunction : ∀ (T:SET) (f:T→T) (t:T:hSet), f = identity T -> f t = t.
Proof. intros ? ? ?. exact (apevalat t). Defined.

Lemma identityFunction' : ∀ (T:SET) (t:T:hSet), identity T t = t.
Proof. intros. reflexivity. Defined.

(** notation for dealing with functors, natural transformations, etc.  *)

Definition functor_object_application {B C:Precategory} (F : [B,C]) (b:B) : C
  := (F:_==>_) b.
Notation "F ◾ b" := (functor_object_application F b) (at level 40, left associativity) : cat. (* \sqb3 *)

Definition functor_mor_application {B C:Precategory} {b b':B} (F:[B,C]) :
  b → b'  ->  F ◾ b → F ◾ b'
  := λ f, # (F:_==>_) f.
Notation "F ▭ f" := (functor_mor_application F f) (at level 40, left associativity) : cat. (* \rew1 *)

Definition arrow {C:Precategory} (c : C) (X : [C^op,SET]) : hSet := X ◾ c.
Notation "c ⇒ X" := (arrow c X)  (at level 50) : cat. (* \r= *)

Definition arrow_morphism_composition {C:Precategory} {c' c:C} {X:[C^op,SET]} :
  c'→c -> c⇒X -> c'⇒X
  := λ f x, # (X:_==>_) f x.
Notation "x ⟲ f" := (arrow_morphism_composition f x) (at level 50, left associativity) : cat.
(* ⟲ agda-input \l C-N C-N C-N 2 the first time, \l the second time *)
(* motivation for the notation:
   the morphisms of C act on the right of the elements of X *)

Definition nattrans_arrow_composition {C:Precategory} {X X':[C^op,SET]} {c:C} :
  c⇒X -> X→X' -> c⇒X'
  := λ x q, (q:_⟶_) c (x:(X:_==>_) c:hSet).
Notation "q ⟳ x" := (nattrans_arrow_composition x q) (at level 50, left associativity) : cat.
(* ⟳ agda-input \r C-N C-N C-N 3 the first time, \r the second time *)
(* motivation for the notation:
   the natural transformations between functors act on the
   left of the elements of the functors *)

Definition nattrans_object_application {B C:Precategory} {F F' : [B,C]} (b:B) :
  F → F'  ->  F ◾ b → F' ◾ b
  := λ p, (p:_⟶_) b.
Notation "p ◽ b" := (nattrans_object_application b p) (at level 40) : cat.
(* agda input : \sqw3 *)

Definition arrow_mor_id {C:Precategory} {c:C} {X:[C^op,SET]} (x:c⇒X) :
  x ⟲ identity c = x
  := apevalat x (functor_id X c).

Definition arrow_mor_mor_assoc {C:Precategory} {c c' c'':C} {X:[C^op,SET]}
           (g:c''→c') (f:c'→c) (x:c⇒X) :
  x ⟲ (f ∘ g) = (x ⟲ f) ⟲ g
  := apevalat x (functor_comp X c c' c'' f g).

Definition nattrans_naturality {B C:Precategory} {F F':[B, C]} {b b':B}
           (p : F → F') (f : b → b') :
  p ◽ b'  ∘  F ▭ f  =  F' ▭ f  ∘  p ◽ b
  := nat_trans_ax p _ _ f.

Definition nattrans_arrow_mor_assoc {C:Precategory} {c' c:C} {X X':[C^op,SET]}
           (g:c'→c) (x:c⇒X) (p:X→X') :
  p ⟳ (x ⟲ g) = (p ⟳ x) ⟲ g
  := apevalat x (nat_trans_ax p _ _ g).

Definition nattrans_arrow_id {C:Precategory} {c:C} {X:[C^op,SET]} (x:c⇒X) :
  nat_trans_id _ ⟳ x = x
  := idpath _.

Definition nattrans_nattrans_arrow_assoc {C:Precategory} {c:C} {X X' X'':[C^op,SET]}
           (x:c⇒X) (p:X→X') (q:X'→X'') :
  q ⟳ (p ⟳ x) = (q ∘ p) ⟳ x
  := idpath _.

(*  *)
