(* -*- coding: utf-8-with-signature -*- *)

(* Set Printing All. *)

(** * category theory 

  In this library we introduce the category theory needed for K-theory:

  - products, coproducts, direct sums, finite direct sums
  - additive categories, matrices
  - exact categories

  Using Qed, we make all proof irrelevant proofs opaque. *)

Require Import Foundations.hlevel2.hSet Foundations.hlevel2.stnfsets.

Require Import 
        RezkCompletion.precategories RezkCompletion.functors_transformations 
        RezkCompletion.category_hset RezkCompletion.yoneda RezkCompletion.auxiliary_lemmas_HoTT.
Import pathnotations.PathNotations.

Require Import Ktheory.Utilities.
Import Ktheory.Utilities.Notations.

Unset Automatic Introduction.

(** *** notation *)

Local Notation "b ← a" := (precategory_morphisms a b) (at level 50).
Local Notation Hom := precategory_morphisms.
Local Notation "a → b" := (precategory_morphisms a b) (at level 50).
Local Notation "a ==> b" := (functor a b) (at level 50).
Local Notation "f ;; g" := (precategories.compose f g) (at level 50, only parsing).
Local Notation "g ∘ f" := (precategories.compose f g) (at level 50, only parsing).
Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "x :1" := (pr1 x) (at level 3, only parsing).
Local Notation "x :2" := (pr2 x) (at level 3, only parsing).
Notation "C '^op'" := (opp_precat C) (at level 3).
Notation SET := hset_precategory.
Definition Ob (C:precategory) : Type := ob C.

Definition precategory_pair (C:precategory_data) (i:is_precategory C)
  : precategory := tpair _ C i.

Definition category_pair (C:precategory) (i:is_category C)
 : category := tpair _ C i.

(** *** make a precategory *)

Definition makePrecategory_ob_mor
    (obj : UU)
    (mor : obj -> obj -> UU)
    (imor : forall i j:obj, isaset (mor i j))
    : precategory_ob_mor.
  intros.
  exact (precategory_ob_mor_pair obj (fun i j:obj => hSetpair (mor i j) (imor i j))).
Defined.    

Definition makePrecategory_data
    (obj : UU)
    (mor : obj -> obj -> UU)
    (imor : forall i j:obj, isaset (mor i j))
    (identity : forall i:obj, mor i i)
    (compose : forall (i j k:obj) (f:mor i j) (g:mor j k), mor i k)
    : precategory_data.
  intros.
  exact (precategory_data_pair (makePrecategory_ob_mor obj mor imor) identity compose).
Defined.    

Definition makePrecategory 
    (obj : UU)
    (mor : obj -> obj -> UU)
    (imor : forall i j:obj, isaset (mor i j))
    (identity : forall i:obj, mor i i)
    (compose : forall (i j k:obj) (f:mor i j) (g:mor j k), mor i k)
    (right : forall (i j:obj) (f:mor i j), compose _ _ _ (identity i) f == f)
    (left  : forall (i j:obj) (f:mor i j), compose _ _ _ f (identity j) == f)
    (associativity : forall (a b c d:obj) (f:mor a b) (g:mor b c) (h:mor c d),
        compose _ _ _ f (compose _ _ _ g h) == compose _ _ _ (compose _ _ _ f g) h)
    : precategory.
  intros.
  apply (precategory_pair 
           (precategory_data_pair
              (precategory_ob_mor_pair 
                 obj
                 (fun i j:obj => hSetpair (mor i j) (imor i j)))
              identity
              compose)).
    split. split. exact right. exact left. exact associativity.
Defined.    

(** *** opposite category of opposite category *)

Lemma opp_opp_precat_ob_mor (C : precategory_ob_mor) : C == opp_precat_ob_mor (opp_precat_ob_mor C).
Proof.
  intro.
  unfold opp_precat_ob_mor.
  destruct C as [ob mor].  
  reflexivity.
Defined.

Lemma opp_opp_precat_ob_mor_compute (C : precategory_ob_mor) :
  idpath _ == maponpaths precategory_id_comp (opp_opp_precat_ob_mor C).
Proof. intros [ob mor]. reflexivity. Defined.

Lemma opp_opp_precat_data (C : precategory_data) 
   : C == opp_precat_data (opp_precat_data C).
Proof.
  intro.
  destruct C as [[ob mor] [id co]].
  reflexivity.
Defined.

Lemma isaprop_is_precategory (C : precategory_data)
  : isaprop (is_precategory C).
Proof.
  intro.
  apply isofhleveltotal2.
    apply isofhleveltotal2.
      repeat (apply impred; intro); apply isaset_hSet.
    intros _.
    repeat (apply impred; intro); apply isaset_hSet.
  intros _.    
  repeat (apply impred; intro); apply isaset_hSet.
Qed.

Lemma opp_opp_precat (C : precategory) : C == C^op^op.
Proof.
  intros [data ispre].
  apply (pair_path (opp_opp_precat_data data)).
  apply isaprop_is_precategory.
Defined.

Module PrimitiveTerminalObjects.

  (** *** terminal objects *)

  Definition isTerminalObject {C:precategory} (a:ob C) := forall (x:ob C), iscontr (a ← x).

  Lemma theTerminalObjectIsomorphy {C:precategory} (a b:ob C):isTerminalObject a -> isTerminalObject b -> iso a b.
  Proof.
    intros ? ? ?.
    intros map_to_a_from_ map_to_b_from_. 
    exists (the (map_to_b_from_ a)).
    exists (the (map_to_a_from_ b)). 
    split. 
      intermediate (the (map_to_a_from_ a)). 
        apply uniqueness.
      apply uniqueness'. 
    intermediate (the (map_to_b_from_ b)). 
      apply uniqueness.
    apply uniqueness'.
  Defined.

  Lemma isaprop_isTerminalObject {C:precategory} (a:ob C):isaprop(isTerminalObject a).
  Proof. prop_logic. Qed.

  Definition isTerminalObjectProp {C:precategory} (a:ob C) := 
    hProppair (isTerminalObject a) (isaprop_isTerminalObject a):hProp.

  Definition TerminalObject (C:precategory) := total2 (fun a:ob C => isTerminalObject a).
  Definition theTerminalObject {C:precategory} (z:TerminalObject C) := pr1 z.
  Definition theTerminalProperty {C:precategory} (z:TerminalObject C) := pr2 z.

  Definition theUnivalenceProperty (C:category) := pr2 _ : is_category C.

  Lemma isaprop_TerminalObject (C:category) : isaprop (TerminalObject C).
  Proof.
    intros.
    apply invproofirrelevance.
    intros a b.
    apply (total2_paths 
             (isotoid _ (theUnivalenceProperty _) 
                      (theTerminalObjectIsomorphy _ _      
                         (theTerminalProperty a)
                         (theTerminalProperty b)))).
    apply isaprop_isTerminalObject.
  Qed.

  Definition squashTerminalObject (C:precategory) := squash (TerminalObject C).

  Definition squashTerminalObjectProp (C:precategory) := 
    hProppair (squashTerminalObject C) (isaprop_squash _).

End PrimitiveTerminalObjects.

Module PrimitiveInitialObjects.

  (** *** initial objects *)

  Definition isInitialObject {C:precategory} (a:ob C) := forall (x:ob C), iscontr (x ← a).

  Lemma theInitialObjectIsomorphy {C:precategory} (a b:ob C):isInitialObject a -> isInitialObject b -> iso a b.
  Proof.
    intros ? ? ?.
    intros map_to_a_from_ map_to_b_from_. 
    exists (the (map_to_a_from_ b)). 
    exists (the (map_to_b_from_ a)).
    split. 
      intermediate (the (map_to_a_from_ a)). 
        apply uniqueness.
      apply uniqueness'. 
    intermediate (the (map_to_b_from_ b)). 
      apply uniqueness.
    apply uniqueness'.
  Defined.

  Lemma isaprop_isInitialObject {C:precategory} (a:ob C):isaprop(isInitialObject a).
  Proof. prop_logic. Qed.

  Definition isInitialObjectProp {C:precategory} (a:ob C) := 
    hProppair (isInitialObject a) (isaprop_isInitialObject a):hProp.

  Definition InitialObject (C:precategory) := total2 (fun a:ob C => isInitialObject a).
  Definition theInitialObject {C:precategory} (z:InitialObject C) := pr1 z.
  Definition theInitialProperty {C:precategory} (z:InitialObject C) := pr2 z.

  Definition theUnivalenceProperty (C:category) := pr2 _ : is_category C.

  Lemma isaprop_InitialObject (C:category) : isaprop (InitialObject C).
  Proof.
    intros.
    apply invproofirrelevance.
    intros a b.
    apply (total2_paths 
             (isotoid _ (theUnivalenceProperty _) 
                      (theInitialObjectIsomorphy _ _      
                         (theInitialProperty a)
                         (theInitialProperty b)))).
    apply isaprop_isInitialObject.
  Qed.

  Definition squashInitialObject (C:precategory) := squash (InitialObject C).

  Definition squashInitialObjectProp (C:precategory) := 
    hProppair (squashInitialObject C) (isaprop_squash _).

End PrimitiveInitialObjects.

Module StandardCategories.

  Definition compose' { C:precategory_data } { a b c:ob C }
    (g:b → c) (f:a → b) : a → c.
  Proof.
    intros.
    exact (compose f g).
  Defined.

  Definition idtomor {C:precategory} (a b:ob C) : a == b -> a → b.
  Proof.
    intros ? ? ? H.
    destruct H.
    exact (identity a).
  Defined.

  Lemma eq_idtoiso_idtomor {C:precategory} (a b:ob C) (e:a == b) :
    pr1 (idtoiso e) == idtomor _ _ e.
  Proof.
    intros.
    destruct e.
    reflexivity.
  Defined.

  (** *** the path groupoid *)

  Lemma path_assoc (X:UU) (a b c d:X) 
          (f : a == b) (g : b == c) (h : c == d)
        : f @ (g @ h) == (f @ g) @ h.
  Proof. intros. destruct f. reflexivity. Defined.

  Lemma path_assoc_opaque (X:UU) (a b c d:X) 
          (f : a == b) (g : b == c) (h : c == d)
        : f @ (g @ h) == (f @ g) @ h.
  Proof. intros. destruct f. reflexivity. Qed.

  Definition is_groupoid (C : precategory) := 
    forall (a b : ob C), isweq (fun p : a == b => idtomor a b p).

  Lemma isaprop_is_groupoid (C : precategory) : isaprop (is_groupoid C).
  Proof.
    intro C. apply impred.
    intro a. apply impred.
    intro b. apply isapropisweq.
  Qed.

  Lemma morphism_from_iso_is_incl (C : precategory) (a b : ob C) :
    isincl (morphism_from_iso C a b).
  Proof.
    intros. intro g.
    apply (isofhlevelweqf _ (ezweqpr1 _ _)).
    apply isaprop_is_isomorphism.
  Defined.

  Lemma is_category_groupoid {C : precategory} : is_groupoid C -> is_category C.
  Proof.
    intros ? ig ? ?.
    set (t := morphism_from_iso _ a b).
    apply (isofhlevelff 0 idtoiso t).
    assert (h : idtomor _ _ ~ funcomp idtoiso t). intro p. destruct p. reflexivity.
    apply (isweqhomot _ _ h).
    apply ig.
    apply morphism_from_iso_is_incl.
  Qed.

  Definition path_pregroupoid (X:UU) : isofhlevel 3 X -> precategory.
    intros obj iobj.
    set (mor := @paths obj).
    (* Later we'll define a version of this with no hlevel assumption on X,
       where [mor i j] will be defined with [pi0].  This version will still
       be useful, because in it, each arrow is a path, rather than an
       equivalence class of paths. *)
    set (identity := (fun i:obj => idpath i):forall i:obj, mor i i).
    set (compose := (
           fun i j k:obj => 
             fun f:mor i j =>
               fun g:mor j k => f @ g)
        :forall (i j k:obj) (f:mor i j) (g:mor j k), mor i k ).
    assert (right :
           forall i j:obj,
             forall f:mor i j, compose _ _ _ (identity i) f == f).
      intros. reflexivity.
    assert (left :
           forall i j:obj,
             forall f:mor i j, compose _ _ _ f (identity j) == f).
      intros. apply pathscomp0rid.
    assert (assoc:forall (a b c d:obj) 
                    (f:mor a b)(g:mor b c) (h:mor c d),
                     compose _ _ _ f (compose _ _ _ g h) == compose _ _ _ (compose _ _ _ f g) h).
      apply path_assoc_opaque.
    exact (makePrecategory obj mor iobj identity compose right left assoc).
  Defined.

  Lemma is_groupoid_path_pregroupoid (X:UU) (iobj:isofhlevel 3 X) :
    is_groupoid (path_pregroupoid X iobj).
  Proof.
    intros ? ? a b.
    assert (k : idfun (a == b) ~ idtomor a b). intro p. destruct p. reflexivity.
    apply (isweqhomot _ _ k).
    apply idisweq.
  Qed.

  Lemma is_category_path_pregroupoid (X:UU) (i:isofhlevel 3 X) :
    is_category (path_pregroupoid X i).
  Proof.
    intros.
    apply is_category_groupoid, is_groupoid_path_pregroupoid.
  Qed.

  Definition path_groupoid (X:UU) : isofhlevel 3 X -> category.
  Proof.
    intros ? iobj.
    apply (category_pair (path_pregroupoid X iobj)), is_category_path_pregroupoid.
  Defined.

  (** *** the discrete category on n objects *)

  Definition cat_n (n:nat):category.
    intro.
    apply (path_groupoid (stn n)).
    apply hlevelntosn.
    apply isasetstn.
  Defined.

  Definition is_discrete (C:precategory) := 
    dirprod (isaset (ob C)) (is_groupoid C).

  Lemma isaprop_is_discrete (C:precategory) : 
    isaprop (is_discrete C).
  Proof.
    intro.
    apply isofhleveltotal2. apply isapropisaset.
    intro is.
    apply isaprop_is_groupoid.
  Qed.

  Lemma is_discrete_cat_n (n:nat) : is_discrete (cat_n n).
  Proof.
    intro.
    split.
      apply isasetstn.
    apply is_groupoid_path_pregroupoid.
  Qed.

End StandardCategories.

(** ** representable functors *)

Module RepresentableFunctors.
  (** *** the category of elements of a functor *)
  Definition El_data {C} (F:C==>SET) : precategory_data.
    intros C F.
    set (Fobj := F:1:1).
    set (Fmor := F:1:2).
    set (iFid := F:2:1).
    set (iFcomp := F:2:2).
    set (obj := total2 (fun c : ob C => pr1hSet (Fobj c))).
    set (compat := fun a b : obj =>
                     fun f : pr1 a → pr1 b => Fmor _ _ f a:2 == b:2 ).
    set (mor := fun a b => total2 (compat a b)).
    apply (makePrecategory_data obj mor).
    - intros. apply (isofhleveltotal2 2). 
      * apply setproperty.
      * intros f.  apply (isofhlevelsnprop 1). apply isaset_hSet.
    - intro a. exact (identity a:1 ,, (apevalat a:2 (iFid a:1))).
    - intros ? ? ? f g.
      exact (      g:1 ∘ f:1,,
                   ((apevalat i:2 (iFcomp _ _ _ f:1 g:1))
                    @ 
                    (ap (Fmor _ _ g:1) f:2 @ g:2))). Defined.
  Lemma El_okay {C} (F:C==>SET) : is_precategory (El_data F).
  Proof.
    intros. split. split.
    - intros a b [f f'].
      exact (pair_path (id_left _ _ _ f) (the (isaset_hSet _ _ _ _ _))).
    - intros a b [f f'].
      exact (pair_path (id_right _ _ _ f) (the (isaset_hSet _ _ _ _ _))).
    - intros ? ? ? ? f g h.     (* destructing f,g,h adds 1.75 seconds *)
      exact (pair_path 
               (assoc _ _ _ _ _ f:1 g:1 h:1)
               (the (isaset_hSet _ _ _ _ _))). Qed.
  Definition El {C} (F:C==>SET) : precategory.
    intros.
    exact (El_data F ,, El_okay F). Defined.
  Definition El_pr1_data {C} (F:C==>SET) : functor_data (El F) C.
    intros.
    exists pr1.
    intros x x'.
    apply pr1. Defined.
  Definition El_pr1 {C} (F:C==>SET) : El F ==> C.
    intros. exists (El_pr1_data _).
    split. - intros. reflexivity. - intros. reflexivity. Defined.
  Definition reflects_isos {C D} (F:C==>D) :=
    forall c c' (f : c → c'), is_isomorphism (#F f) -> is_isomorphism f.
  Lemma isaprop_reflects_isos {C D} (F:C==>D) : isaprop (reflects_isos F).
  Proof.
    intros. apply impred; intros. apply impred; intros. apply impred; intros.
    apply impred; intros. apply isaprop_is_isomorphism. Qed.
  Lemma El_pr1_reflects_isos {C} (F:[C, SET]) : reflects_isos (El_pr1 F).
  Proof.
    intros. simpl in F.         (* why do we need this? *)
    intros cx dy fi iso_f.
    set (c := cx:1). set (x := cx:2).
    set (d := dy:1). set (y := dy:2).
    set (f := fi:1). set (i := fi:2).
    set (f' := iso_f:1). set (j := iso_f:2).
    assert (i' : #F f' y == x).
    { intermediate (#F f' (#F f x)).
      { exact (ap (#F f') (!i)). }
      { intermediate (#F (f' ∘ f) x).
        { exact (apevalat x (!functor_comp _ _ F _ _ _ f f')). }
        { intermediate (#F (identity c) x).
          { exact (apevalat x (ap #F j:1)). }
          { exact (apevalat x (functor_id _ _ F c)). }}}}
    { exists (f' ,, i'). split.
      { exact (pair_path j:1 (the (isaset_hSet _ _ _ _ _))). }
      { exact (pair_path j:2 (the (isaset_hSet _ _ _ _ _))). }} Qed.
  Import PrimitiveInitialObjects.
  Definition Representation {C} (F:C==>SET) := InitialObject (El F).
  Definition Representable {C} (F:C==>SET) := squash (Representation F).
  Definition representingElement {C} {F:C==>SET} (r:Representation F) := 
    pr1 r : El F.
  Definition representingObject {C} {F:C==>SET} (r:Representation F) := 
    pr1 (representingElement r) : ob C .
End RepresentableFunctors.

Module TerminalObjects.
  Import RepresentableFunctors.
  Definition unitset : hSet := tpair isaset unit isasetunit.
  Definition unitFunctor_data C : functor_data C SET.
    intros. exists (fun _ => unitset).
    intros. exact (idfun _). Defined.
  Definition unitFunctor C : C ==> SET.
    intros. exists (unitFunctor_data C).
    split. reflexivity. reflexivity. Defined.
  Definition InitialObject (C:precategory) := Representation (unitFunctor C).
  Definition initialObject {C} (i:InitialObject C) : ob C.
    intros C i. exact (representingObject i). Defined.
  Definition initialArrow {C} (i:InitialObject C) (c:ob C) : initialObject i → c.
    intros C [[i []] p] c. exact (pr1 (the (p (c,,tt)))). Defined.
  Definition TerminalObject (C:precategory) := Representation (unitFunctor C^op).
  Definition terminalObject {C} (t:InitialObject C) : ob C.
    intros C t. exact (representingObject t). Defined.
  Definition terminalArrow {C} (t:TerminalObject C) (c:ob C) : c → terminalObject t.
    intros C [[i []] p] c. exact (pr1 (the (p (c,,tt)))). Defined.      
End TerminalObjects.

Module BinaryProducts.
  Import RepresentableFunctors.
  Definition hom2_set (C:precategory) (c d:ob C) : ob C -> SET.
    intros ? ? ? x. exact (setdirprod (Hom c x) (Hom d x)). Defined.
  Definition hom2_map (C:precategory) (c d x y:ob C) (f : x → y) :
      pr1hSet (hom2_set C c d x) -> pr1hSet (hom2_set C c d y).
    intros ? ? ? ? ? ? [g h]. exact (f ∘ g ,, f ∘ h). Defined.
  Definition hom2_data (C:precategory) (c d:ob C) : functor_data C SET.
    intros.  exact (hom2_set C c d,, hom2_map C c d). Defined.
  Definition hom2 (C:precategory) (c d:ob C) : C ==> SET.
    intros. exists (hom2_data C c d). split.
    { intros a. apply funextfunax; intros [f g]. apply simple_pair_path.
      { apply id_right. } { apply id_right. } }
    { intros x y z p q. apply funextfunax; intros [f g]; apply simple_pair_path.
      { apply assoc. } { apply assoc. }} Defined.
  Definition Coproduct C (c d:Ob C) := Representation (hom2 C c d).
  Definition Product C (c d:Ob C) := Representation (hom2 C^op c d).
End BinaryProducts.

Module ZeroObjects.
  Import TerminalObjects.
End ZeroObjects.
