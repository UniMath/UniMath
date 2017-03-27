(* -*- coding: utf-8 -*- *)

Require Export UniMath.Ktheory.Utilities.
Require Export UniMath.CategoryTheory.precategories. (* export its coercions, especially *)
Require Export UniMath.CategoryTheory.opp_precat
               UniMath.CategoryTheory.yoneda
               UniMath.CategoryTheory.category_hset.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.Foundations.Preamble.
Require Export UniMath.Foundations.Sets.
Require Export UniMath.CategoryTheory.category_hset.
Require Import UniMath.MoreFoundations.Tactics.

Local Open Scope cat.

Set Automatic Introduction.

Notation "a <-- b" := (@precategory_morphisms (opp_precat _) a b) (at level 50) : cat.

Definition src {C:precategory} {a b:C} (f:a-->b) : C := a.
Definition tar {C:precategory} {a b:C} (f:a-->b) : C := b.

Definition hom (C:precategory_data) : ob C -> ob C -> UU :=
  λ c c', c --> c'.

Definition Hom (C:Precategory) : ob C -> ob C -> hSet :=
  λ c c', hSetpair (c --> c') (homset_property C _ _ ).

Ltac eqn_logic :=
  abstract (
      repeat (
          try reflexivity;
          try intro; try split; try apply id_right;
          try apply id_left; try apply assoc;
          try apply funextsec;
          try apply homset_property;
          try apply isasetunit;
          try apply isapropunit;
          try refine (two_arg_paths_f _ _);
          try refine (total2_paths_f _ _);
          try refine (nat_trans_ax _ _ _ _);
          try refine (! nat_trans_ax _ _ _ _);
          try apply functor_id;
          try apply functor_comp;
          try apply isaprop_is_nat_trans
        )) using _L_.

Ltac set_logic :=
  abstract (repeat (
                try intro;
                try apply isaset_total2;
                try apply isasetdirprod;
                try apply homset_property;
                try apply impred_isaset;
                try apply isasetaprop)) using _M_.

Notation "[ C , D ]" := (functor_Precategory C D) : cat.

Definition oppositePrecategory (C:Precategory) : Precategory.
Proof.
  exists (opp_precat C).
  unfold Precategory in C.
  exact (λ a b, pr2 C b a).
Defined.

Notation "C '^op'" := (oppositePrecategory C) (at level 3) : cat. (* this overwrites the previous definition *)

Definition precategory_pair (C:precategory_data) (i:is_precategory C)
  : precategory := C,,i.

Definition Precategory_obmor (C:precategory) : precategory_ob_mor :=
      precategory_ob_mor_from_precategory_data (
          precategory_data_from_precategory C).

Definition Functor_obmor {C D} (F:functor C D) := pr1 F.
Definition Functor_obj {C D} (F:functor C D) := pr1 (pr1 F).
Definition Functor_mor {C D} (F:functor C D) := pr2 (pr1 F).
Definition Functor_identity {C D} (F:functor C D) := functor_id F.
Definition Functor_compose {C D} (F:functor C D) := @functor_comp _ _ F.

Definition category_pair (C:precategory) (i:is_category C) : category := C,,i.

Definition theUnivalenceProperty (C:category) := pr2 C : is_category C.

Lemma Precategory_eq (C D:Precategory) :
  (C:precategory_data) = (D:precategory_data) -> C=D.
Proof.
  intro e. apply subtypeEquality. intro. apply isaprop_has_homsets.
  apply subtypeEquality'.
  { assumption. }
  apply isaprop_is_precategory.
  apply homset_property.
Defined.

(** embeddings and isomorphism of categories  *)

Definition PrecategoryEmbedding (B C:Precategory) := ∑ F:[B,C], fully_faithful F.

Definition embeddingToFunctor (B C:Precategory) :
  PrecategoryEmbedding B C -> B ⟶ C
  := pr1.

Coercion embeddingToFunctor : PrecategoryEmbedding >-> functor.

Definition PrecategoryIsomorphism (B C:Precategory) :=
  ∑ F:PrecategoryEmbedding B C, isweq ((pr1 F : B ⟶ C) : ob B -> ob C).

Definition isomorphismToEmbedding (B C:Precategory) :
  PrecategoryIsomorphism B C -> PrecategoryEmbedding B C
  := pr1.

Coercion isomorphismToEmbedding : PrecategoryIsomorphism >-> PrecategoryEmbedding.

Definition isomorphismOnMor {B C:Precategory} (F:PrecategoryIsomorphism B C)
           (b b':B) : Hom B b b'  ≃  Hom C (F b) (F b')
  := weqpair _ (pr2 (pr1 F) b b').

(** *** make a precategory *)

Definition makePrecategory_ob_mor
    (obj : UU)
    (mor : obj -> obj -> UU) : precategory_ob_mor
  := precategory_ob_mor_pair obj (fun i j:obj => mor i j).

Definition makePrecategory_data
    (obj : UU)
    (mor : obj -> obj -> UU)
    (identity : ∏ i, mor i i)
    (compose : ∏ i j k (f:mor i j) (g:mor j k), mor i k)
    : precategory_data
  := precategory_data_pair (makePrecategory_ob_mor obj mor) identity compose.

Definition makePrecategory
    (obj : UU)
    (mor : obj -> obj -> UU)
    (homsets : ∏ a b, isaset (mor a b))
    (identity : ∏ i, mor i i)
    (compose : ∏ i j k (f:mor i j) (g:mor j k), mor i k)
    (right : ∏ i j (f:mor i j), compose _ _ _ (identity i) f = f)
    (left  : ∏ i j (f:mor i j), compose _ _ _ f (identity j) = f)
    (associativity : ∏ a b c d (f:mor a b) (g:mor b c) (h:mor c d),
        compose _ _ _ f (compose _ _ _ g h) = compose _ _ _ (compose _ _ _ f g) h)
  : Precategory
  := (precategory_pair
           (precategory_data_pair
              (precategory_ob_mor_pair
                 obj
                 (fun i j => mor i j))
              identity compose)
           ((right,,left),,associativity)),,homsets.

Local Open Scope cat_deprecated.

Definition makeFunctor {C D:Precategory}
           (obj : C -> D)
           (mor : ∏ c c' : C, c --> c' -> obj c --> obj c')
           (identity : ∏ c, mor c c (identity c) = identity (obj c))
           (compax : ∏ (a b c : C) (f : a --> b) (g : b --> c),
                       mor a c (g ∘ f) = mor b c g ∘ mor a b f) :
  C ⟶ D
  := (obj,, mor),, identity,, compax.

(** notation for dealing with functors, natural transformations, etc.  *)

Definition functor_object_application {B C:Precategory} (F : [B,C]) (b:B) : C
  := (F:_⟶_) b.
Notation "F ◾ b" := (functor_object_application F b) (at level 40, left associativity) : cat.
(* \sqb3 *)

Definition functor_mor_application {B C:Precategory} {b b':B} (F:[B,C]) :
  b --> b'  ->  F ◾ b --> F ◾ b'
  := λ f, # (F:_⟶_) f.
Notation "F ▭ f" := (functor_mor_application F f) (at level 40, left associativity) : cat. (* \rew1 *)

Definition arrow {C:Precategory} (c : C) (X : [C^op,SET]) : hSet := X ◾ c.
Notation "c ⇒ X" := (arrow c X)  (at level 50) : cat. (* \r= *)

Definition arrow' {C:Precategory} (c : C) (X : [C^op^op,SET]) : hSet := X ◾ c.
Notation "X ⇐ c" := (arrow' c X)  (at level 50) : cat. (* \l= *)

Definition arrow_morphism_composition {C:Precategory} {c' c:C} {X:[C^op,SET]} :
  c'-->c -> c⇒X -> c'⇒X
  := λ f x, # (X:_⟶_) f x.
Notation "x ⟲ f" := (arrow_morphism_composition f x) (at level 50, left associativity) : cat.
(* ⟲ agda-input \l C-N C-N C-N 2 the first time, \l the second time *)
(* motivation for the notation:
   the morphisms of C act on the right of the elements of X *)

Definition nattrans_arrow_composition {C:Precategory} {X X':[C^op,SET]} {c:C} :
  c⇒X -> X-->X' -> c⇒X'
  := λ x q, (q:_ ⟹ _) c (x:(X:_⟶_) c:hSet).
Notation "q ⟳ x" := (nattrans_arrow_composition x q) (at level 50, left associativity) : cat.
(* ⟳ agda-input \r C-N C-N C-N 3 the first time, \r the second time *)
(* motivation for the notation:
   the natural transformations between functors act on the
   left of the elements of the functors *)

Definition nattrans_object_application {B C:Precategory} {F F' : [B,C]} (b:B) :
  F --> F'  ->  F ◾ b --> F' ◾ b
  := λ p, (p:_ ⟹ _) b.
Notation "p ◽ b" := (nattrans_object_application b p) (at level 40) : cat.
(* agda input : \sqw3 *)

Definition arrow_mor_id {C:Precategory} {c:C} {X:[C^op,SET]} (x:c⇒X) :
  x ⟲ identity c = x
  := eqtohomot (functor_id X c) x.

Definition arrow_mor_mor_assoc {C:Precategory} {c c' c'':C} {X:[C^op,SET]}
           (g:c''-->c') (f:c'-->c) (x:c⇒X) :
  x ⟲ (f ∘ g) = (x ⟲ f) ⟲ g
  := eqtohomot (functor_comp X f g) x.

Definition nattrans_naturality {B C:Precategory} {F F':[B, C]} {b b':B}
           (p : F --> F') (f : b --> b') :
  p ◽ b'  ∘  F ▭ f  =  F' ▭ f  ∘  p ◽ b
  := nat_trans_ax p _ _ f.

Definition comp_func_on_mor {A B C:Precategory} (F:[A,B]) (G:[B,C]) {a a':A} (f:a-->a') :
  G □ F ▭ f = G ▭ (F ▭ f).
Proof. reflexivity. Defined.

Definition nattrans_arrow_mor_assoc {C:Precategory} {c' c:C} {X X':[C^op,SET]}
           (g:c'-->c) (x:c⇒X) (p:X-->X') :
  p ⟳ (x ⟲ g) = (p ⟳ x) ⟲ g
  := eqtohomot (nat_trans_ax p _ _ g) x.

Definition nattrans_arrow_id {C:Precategory} {c:C} {X:[C^op,SET]} (x:c⇒X) :
  nat_trans_id _ ⟳ x = x
  := idpath _.

Definition nattrans_nattrans_arrow_assoc {C:Precategory} {c:C} {X X' X'':[C^op,SET]}
           (x:c⇒X) (p:X-->X') (q:X'-->X'') :
  q ⟳ (p ⟳ x) = (q ∘ p) ⟳ x
  := idpath _.

Definition nattrans_nattrans_object_assoc {A B C:Precategory}
           (F:[A,B]) (G:[B, C]) {a a' : A} (f : a --> a') :
  G □ F ▭ f = G ▭ (F ▭ f)
  := idpath _.

Lemma functor_on_id {B C:Precategory} (F:[B,C]) (b:B) : F ▭ identity b = identity (F ◾ b).
Proof. exact (functor_id F b). Defined.

Lemma functor_on_comp {B C:Precategory} (F:[B,C]) {b b' b'':B} (g:b'-->b'') (f:b-->b') :
  F ▭ (g ∘ f) = F ▭ g ∘ F ▭ f.
Proof. exact (functor_comp F f g). Defined.

(*  *)

(** natural transformations and isomorphisms *)

Definition nat_iso {B C:Precategory} (F G:[B,C]) := iso F G.

Definition makeNattrans {C D:Precategory} {F G:[C,D]}
           (mor : ∏ x : C, F ◾ x --> G ◾ x)
           (eqn : ∏ c c' f, mor c' ∘ F ▭ f = G ▭ f ∘ mor c) :
  F --> G
  := (mor,,eqn).

Definition makeNattrans_op {C D:Precategory} {F G:[C^op,D]}
           (mor : ∏ x : C, F ◾ x --> G ◾ x)
           (eqn : ∏ c c' f, mor c' ∘ F ▭ f = G ▭ f ∘ mor c) :
  F --> G
  := (mor,,eqn).

Definition makeNatiso {C D:Precategory} {F G:[C,D]}
           (mor : ∏ x : C, iso (F ◾ x) (G ◾ x))
           (eqn : ∏ c c' f, mor c' ∘ F ▭ f = G ▭ f ∘ mor c) :
  nat_iso F G.
Proof.
  refine (makeNattrans mor eqn,,_). apply functor_iso_if_pointwise_iso; intro c. apply pr2.
Defined.

Definition makeNatiso_op {C D:Precategory} {F G:[C^op,D]}
           (mor : ∏ x : C, iso (F ◾ x) (G ◾ x))
           (eqn : ∏ c c' f, mor c' ∘ F ▭ f = G ▭ f ∘ mor c) :
  nat_iso F G.
Proof.
  refine (makeNattrans_op mor eqn,,_). apply functor_iso_if_pointwise_iso; intro c. apply pr2.
Defined.

Lemma move_inv {C:Precategory} {a a' b' b:C} {f : a --> b} {f' : a' --> b'}
      {i : a --> a'} {i' : a' --> a} {j : b --> b'} {j' : b' --> b} :
  is_inverse_in_precat i i' -> is_inverse_in_precat j j' ->
  j ∘ f = f' ∘ i -> j' ∘ f' = f ∘ i'.
Proof.
  intros I J r. rewrite <- id_right. rewrite (! pr1 J). rewrite assoc.
  apply (maponpaths (λ k, j' ∘ k)). rewrite <- assoc. rewrite r.
  rewrite assoc. rewrite (pr2 I). rewrite id_left. reflexivity.
Defined.

Lemma weq_iff_iso_SET {X Y:SET} (f:X-->Y) : is_iso f <-> isweq f.
Proof.
  split.
  - intro i. set (F := isopair f i).
    refine (gradth f (inv_from_iso F)
                   (λ x, eqtohomot (iso_inv_after_iso F) x)
                   (λ y, eqtohomot (iso_after_iso_inv F) y)).
  - exact (λ i Z, weqproperty (weqbfun (Z:hSet) (weqpair f i))).
Defined.

Lemma weq_to_iso_SET {X Y:SET} : iso X Y ≃ ((X:hSet) ≃ (Y:hSet)).
(* same as hset_iso_equiv_weq *)
Proof.
  intros. apply weqfibtototal; intro f. apply weqiff.
  - apply weq_iff_iso_SET.
  - apply isaprop_is_iso.
  - apply isapropisweq.
Defined.

(* opposite categories *)

Definition functor_to_opp_opp {C:Precategory} : C ⟶ C^op^op
  := makeFunctor (λ c,c) (λ a b f,f) (λ c, idpath _) (λ a b c f g, idpath _).

Definition makeFunctor_op {C D:Precategory}
           (obj : ob C -> ob D)
           (mor : ∏ a b : C, b --> a -> obj a --> obj b)
           (identity : ∏ c, mor c c (identity c) = identity (obj c))
           (compax : ∏ (a b c : C) (f : b --> a) (g : c --> b),
                       mor a c (f ∘ g) = mor b c g ∘ mor a b f) :
  C^op ⟶ D
  := (obj,, mor),, identity,, compax.

Definition opp_ob {C:Precategory} : ob C -> ob C^op
  := λ c, c.

Definition rm_opp_ob {C:Precategory} : ob C^op -> ob C
  := λ c, c.

Definition opp_mor {C:Precategory} {b c:C} : Hom C b c -> Hom C^op c b
  := λ f, f.

Definition rm_opp_mor {C:Precategory} {b c:C} : Hom C^op b c -> Hom C c b
  := λ f, f.

Definition opp_mor_eq {C:Precategory} {a b:C} (f g:a --> b) :
  opp_mor f = opp_mor g -> f = g
  := idfun _.

Lemma opp_opp_precat_ob_mor (C : precategory_ob_mor) : C = opp_precat_ob_mor (opp_precat_ob_mor C).
Proof. induction C as [ob mor]. reflexivity. Defined.

Lemma opp_opp_precat_ob_mor_compute (C : precategory_ob_mor) :
  idpath _ = maponpaths precategory_id_comp (opp_opp_precat_ob_mor C).
Proof. induction C as [ob mor]. reflexivity. Defined.

Lemma opp_opp_precat_data (C : precategory_data)
   : C = opp_precat_data (opp_precat_data C).
Proof. induction C as [[ob mor] [id co]]. reflexivity. Defined.

Lemma opp_opp_precat (C:Precategory) : C = C^op^op.
Proof.
  apply Precategory_eq.         (* we need both associativity axioms to avoid this *)
  tryif primitive_projections
  then reflexivity
  else induction C as [[[[obj mor] [id comp]] p] h]; reflexivity.
Qed.

Definition functorOp {B C : Precategory} : [B, C] ^op ⟶ [B ^op, C ^op].
Proof.
  unshelve refine (makeFunctor _ _ _ _).
  { exact functor_opp. }
  { intros H I p. exists (λ b, pr1 p b).
    abstract (intros b b' f; simpl; exact (! nat_trans_ax p _ _ f)) using _L_. }
  { abstract (intros H; now apply (nat_trans_eq (homset_property _))). }
  { abstract (intros H J K p q; now apply (nat_trans_eq (homset_property _))). }
Defined.

Definition functorOp' {B C:Precategory} : [B,C] ⟶ [B^op,C^op]^op.
Proof.
  exact (functorOp functorOp).
Defined.

Definition functorRmOp {B C : Precategory} : [B ^op, C ^op] ⟶ [B, C] ^op.
Proof.
  unshelve refine (makeFunctor _ _ _ _).
  { exact functor_opp. }
  { intros H I p. exists (λ b, pr1 p b).
    abstract (intros b b' f; simpl; exact (! nat_trans_ax p _ _ f)) using _L_. }
  { abstract (intros H; now apply (nat_trans_eq (homset_property _))) using _L_. }
  { abstract (intros H J K p q; now apply (nat_trans_eq (homset_property _))). }
Defined.

Definition functorMvOp {B C:Precategory} : [B,C^op] ⟶ [B^op,C]^op.
Proof.
  unshelve refine (makeFunctor _ _ _ _).
  { exact functor_opp. }
  { intros H I p. exists (λ b, pr1 p b).
    abstract (intros b b' f; simpl; exact (! nat_trans_ax p _ _ f)) using _L_. }
  { abstract (intros H; now apply (nat_trans_eq (homset_property _))). }
  { abstract (intros H J K p q; now apply (nat_trans_eq (homset_property _))). }
Defined.

Lemma functorOpIso {B C:Precategory} : PrecategoryIsomorphism [B, C]^op [B^op, C^op].
Proof.
  unshelve refine (_,,_).
  { unshelve refine (_,,_).
    { exact functorOp. }
    { intros H H'. unshelve refine (gradth _ _ _ _).
      { simpl. intros p. unshelve refine (makeNattrans _ _).
        { intros b. exact (pr1 p b). }
        { abstract (intros b b' f; simpl; exact (!nat_trans_ax p _ _ f)) using _L_. } }
      { abstract (intro p; apply nat_trans_eq;
                  [ apply homset_property
                  | intro b; reflexivity ]) using _L_. }
      { abstract (intro p; apply nat_trans_eq;
                  [ apply homset_property
                  | intro b; reflexivity ]) using _L_. }}}
  { simpl. unshelve refine (gradth _ _ _ _).
    { exact (functor_opp : B^op ⟶ C^op -> B ⟶ C). }
    { abstract (intros H; simpl; apply (functor_eq _ _ (homset_property C));
                unshelve refine (total2_paths_f _ _); reflexivity) using _L_. }
    { abstract (intros H; simpl; apply functor_eq;
                [ exact (homset_property C^op)
                | unshelve refine (total2_paths_f _ _); reflexivity]). } }
Defined.

Definition functorOpEmb {B C:Precategory} : PrecategoryEmbedding [B, C]^op [B^op, C^op]
  := pr1 functorOpIso.

Lemma functor_op_rm_op_eq {C D:Precategory} (F : C^op ⟶ D^op) :
  functorOp (functorRmOp F) = F.
Proof.
  apply functor_eq.
  { apply homset_property. }
  unshelve refine (total2_paths_f _ _); reflexivity.
Qed.

Lemma functor_rm_op_op_eq {C D:Precategory} (F : C ⟶ D) :
  functorRmOp (functorOp F) = F.
Proof.
  apply functor_eq.
  { apply homset_property. }
  unshelve refine (total2_paths_f _ _); reflexivity.
Qed.

Lemma functor_op_op_eq {C D:Precategory} (F : C ⟶ D) :
  functorOp (functorOp F) = F.
Proof.
  apply functor_eq.
  { apply homset_property. }
  unshelve refine (total2_paths_f _ _); reflexivity.
Qed.

(*  *)

Lemma total2_paths1 {A : UU} {B : A -> UU} (a:A) {b b':B a} :
  b=b' -> tpair B a b = tpair B a b'.
Proof. intro e. induction e. reflexivity. Defined.

Goal ∏ A : UU, ∏ B : A -> UU, ∏ p : (∑ a, B a), p = tpair B (pr1 p) (pr2 p).
  induction p as [a b]. reflexivity. Defined.

Goal ∏ X Y (f:X->Y), f = λ x, f x.
  reflexivity. Defined.

(* new categories from old *)

Definition categoryWithStructure (C:Precategory) (P:ob C -> UU) : Precategory.
Proof.
  unshelve refine (makePrecategory _ _ _ _ _ _ _ _).
  (* add a new component to each object: *)
  - exact (∑ c:C, P c).
  (* the homsets ignore the extra structure: *)
  - intros x y. exact (pr1 x --> pr1 y).
  (* the rest is the same: *)
  - intros x. apply identity.
  - intros x y z f g. exact (g ∘ f).
  - intros. simpl. refine (homset_property C _ _).
  - intros. apply id_left.
  - intros. apply id_right.
  - intros. apply assoc.
Defined.

Definition functorWithStructures {C:Precategory} {P Q:ob C -> UU}
           (F : ∏ c, P c -> Q c) : categoryWithStructure C P ⟶ categoryWithStructure C Q.
Proof.
  unshelve refine (makeFunctor _ _ _ _).
  (* transport the structure: *)
  - exact (λ c, (pr1 c,, F (pr1 c) (pr2 c))).
  (* the rest is the same: *)
  - intros c c' f. exact f.
  - reflexivity.
  - reflexivity.
Defined.

Definition addStructure {B C:Precategory} {P:ob C -> UU}
           (F:B⟶C) (h : ∏ b, P(F b)) : B ⟶ categoryWithStructure C P.
Proof.
  unshelve refine (makeFunctor _ _ _ _).
  - intros b. exact (F b,,h b).
  - intros b b' f. exact (# F f).
  - abstract (intros b; simpl; apply functor_id) using _L_.
  - abstract (intros b b' b'' f g; simpl; apply functor_comp) using _L_.
Defined.

Lemma identityFunction : ∏ (T:SET) (f:T-->T) (t:T:hSet), f = identity T -> f t = t.
Proof. intros ? ? ? e. exact (eqtohomot e t). Defined.

Lemma identityFunction' : ∏ (T:SET) (t:T:hSet), identity T t = t.
Proof. reflexivity. Defined.

(*  *)

Lemma functor_identity_object {C:Precategory} (c:C) : functor_identity C ◾ c = c.
Proof. reflexivity. Defined.

Lemma functor_identity_arrow {C:Precategory} {c c':C} (f:c-->c') : functor_identity C ▭ f = f.
Proof. reflexivity. Defined.

Definition constantFunctor (C:Precategory) {D:Precategory} (d:D) : [C,D].
Proof.
  unshelve refine (makeFunctor _ _ _ _).
  - exact (λ _, d).
  - intros c c' f; simpl. exact (identity d).
  - intros c; simpl. reflexivity.
  - abstract (simpl; intros a b c f g; apply pathsinv0, id_left) using _L_.
Defined.

(*  *)

Definition functor_composite_functor {A B C:Precategory} (F:A⟶B) :
  [B,C] ⟶ [A,C].
Proof.
  unshelve refine (makeFunctor _ _ _ _).
  - exact (λ G, G □ F).
  - intros G G' p; simpl.
    unshelve refine (@makeNattrans A C (G □ F) (G' □ F) (λ a, p ◽ (F ◾ a)) _).
    abstract (
        intros a a' f; rewrite 2? nattrans_nattrans_object_assoc;
        exact (nattrans_naturality p (F ▭ f))) using _L_.
  - abstract (
        intros G; now apply (nat_trans_eq (homset_property C))) using _M_.
  - abstract (
        intros G G' G'' p q; now apply (nat_trans_eq (homset_property C))) using _N_.
Defined.

(* zero maps, definition: *)

Definition hasZeroMaps (C:Precategory) :=
  ∑ (zero : ∏ a b:C, a --> b),
  (∏ a b c, ∏ f:b --> c, f ∘ zero a b = zero a c)
    ×
    (∏ a b c, ∏ f:c --> b, zero b a ∘ f = zero c a).

Definition is {C:Precategory} (zero: hasZeroMaps C) {a b:C} (f:a-->b)
  := f = pr1 zero _ _.

Definition hasZeroMaps_opp (C:Precategory) : hasZeroMaps C -> hasZeroMaps C^op
  := λ z, (λ a b, pr1 z b a) ,, pr2 (pr2 z) ,, pr1 (pr2 z).

Definition hasZeroMaps_opp_opp (C:Precategory) (zero:hasZeroMaps C) :
  hasZeroMaps_opp C^op (hasZeroMaps_opp C zero) = zero.
Proof.
  unshelve refine (total2_paths_f _ _).
  - reflexivity.
  - unshelve refine (total2_paths_f _ _); reflexivity.
Defined.

      (*  *)
