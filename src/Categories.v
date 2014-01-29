(* -*- coding: utf-8-with-signature -*- *)

(* Set Printing All. *)

(** * category theory 

  In this library we introduce the category theory needed for K-theory:

  - products, coproducts, direct sums, finite direct sums
  - additive categories, matrices
  - exact categories

  Using Qed, we make all proof irrelevant proofs opaque. *)

Require Import Foundations.hlevel2.hSet.

Require Import 
        RezkCompletion.precategories RezkCompletion.functors_transformations 
        RezkCompletion.category_hset RezkCompletion.yoneda RezkCompletion.auxiliary_lemmas_HoTT.
Import pathnotations.PathNotations.

Require Import Ktheory.Utilities.
Import Ktheory.Utilities.Notations.

Unset Automatic Introduction.

(** *** notation *)

Local Notation set_to_type := pr1hSet.
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

Definition theUnivalenceProperty (C:category) := pr2 _ : is_category C.

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
      repeat (apply impred; intro); apply setproperty.
    intros _.
    repeat (apply impred; intro); apply setproperty.
  intros _.    
  repeat (apply impred; intro); apply setproperty.
Qed.

Lemma opp_opp_precat (C : precategory) : C == C^op^op.
Proof.
  intros [data ispre].
  apply (pair_path (opp_opp_precat_data data)).
  apply isaprop_is_precategory.
Defined.

Module PrimitiveTerminalObjects. (** *** terminal objects *)
  Definition isTerminalObject (C:precategory) (a:ob C) := 
    forall (x:ob C), iscontr (a ← x).
  Lemma theTerminalObjectIsomorphy (C:precategory) (a b:ob C) :
    isTerminalObject C a -> isTerminalObject C b -> @iso C a b.
  Proof. intros ? ? ? map_to_a_from_ map_to_b_from_. 
    exists (the (map_to_b_from_ a)).
    exists (the (map_to_a_from_ b)). 
    split. { intermediate (the (map_to_a_from_ a)). 
             apply uniqueness. apply uniqueness'. }
           { intermediate (the (map_to_b_from_ b)). 
             apply uniqueness. apply uniqueness'. } Defined.
  Lemma isaprop_isTerminalObject (C:precategory) (a:ob C) :
    isaprop(isTerminalObject C a).
  Proof. prop_logic. Qed.
  Definition isTerminalObjectProp (C:precategory) (a:ob C) := 
    hProppair (isTerminalObject C a) (isaprop_isTerminalObject C a) : hProp.
  Definition TerminalObject (C:precategory) := 
    total2 (fun a:ob C => isTerminalObject C a).
  Definition theTerminalObject {C:precategory} (z:TerminalObject C) := pr1 z.
  Definition theTerminalProperty {C:precategory} (z:TerminalObject C) := pr2 z.
  Lemma isaprop_TerminalObject (C:category) : isaprop (TerminalObject C).
  Proof. intros. apply invproofirrelevance. intros a b.
    apply (total2_paths 
             (isotoid _ (theUnivalenceProperty C) 
                      (theTerminalObjectIsomorphy C _ _      
                         (theTerminalProperty a)
                         (theTerminalProperty b)))).
    apply isaprop_isTerminalObject. Qed.
  Definition squashTerminalObject (C:precategory) := squash (TerminalObject C).
  Definition squashTerminalObjectProp (C:precategory) := 
    hProppair (squashTerminalObject C) (isaprop_squash _).
End PrimitiveTerminalObjects.

Module PrimitiveInitialObjects. (** *** initial objects *)
  Definition isInitialObject (C:precategory) (a:ob C) :=
    forall (x:ob C), iscontr (x ← a).
  Lemma theInitialObjectIsomorphy (C:precategory) (a b:ob C) :
    isInitialObject C a -> isInitialObject C b -> @iso C a b.
  Proof. intros ? ? ? map_to_a_from_ map_to_b_from_. 
    exists (the (map_to_a_from_ b)). 
    exists (the (map_to_b_from_ a)).
    split. { intermediate (the (map_to_a_from_ a)). 
             apply uniqueness. apply uniqueness'. }
           { intermediate (the (map_to_b_from_ b)). 
             apply uniqueness. apply uniqueness'. } Defined.
  Lemma isaprop_isInitialObject (C:precategory) (a:ob C) :
    isaprop(isInitialObject C a).
  Proof. prop_logic. Qed.
  Definition isInitialObjectProp (C:precategory) (a:ob C) := 
    hProppair (isInitialObject C a) (isaprop_isInitialObject C a) : hProp.
  Definition InitialObject (C:precategory) := 
    total2 (fun a:ob C => isInitialObject C a).
  Definition theInitialObject {C:precategory} (z:InitialObject C) := pr1 z.
  Definition theInitialProperty {C:precategory} (z:InitialObject C) := pr2 z.
  Lemma isaprop_InitialObject (C:category) : isaprop (InitialObject C).
  Proof. intros. apply invproofirrelevance. intros a b.
    apply (total2_paths 
             (isotoid _ (theUnivalenceProperty C) 
                      (theInitialObjectIsomorphy C _ _
                         (theInitialProperty a)
                         (theInitialProperty b)))).
    apply isaprop_isInitialObject. Qed.
  Definition squashInitialObject (C:precategory) := squash (InitialObject C).
  Definition squashInitialObjectProp (C:precategory) := 
    hProppair (squashInitialObject C) (isaprop_squash _).
End PrimitiveInitialObjects.

Module ZeroObjects.
  Import PrimitiveTerminalObjects.
  Import PrimitiveInitialObjects.
  Definition ZeroObject (C:precategory) := total2 ( fun 
               z : ob C => dirprod (
                   isInitialObject C z) (
                   isTerminalObject C z) ).
  Definition zero_opp (C:precategory) : ZeroObject C -> ZeroObject C^op.
    intros C [z [i t]]. exact (z ,, (t ,, i)). Defined.
  Definition zero_object {C:precategory} (z:ZeroObject C) : ob C := pr1  z.
  Definition map_from    {C:precategory} (z:ZeroObject C) := pr1(pr2 z).
  Definition map_to      {C:precategory} (z:ZeroObject C) := pr2(pr2 z).
  Coercion zero_object : ZeroObject >-> ob.
  Lemma initMapUniqueness {C:precategory} (a:ZeroObject C) (b:ob C) (f:a→b) :
    f == the (map_from a b).
  Proof. intros. exact (uniqueness (map_from a b) f). Qed.
  Lemma initMapUniqueness2 {C:precategory} (a:ZeroObject C) (b:ob C) (f g:a→b) :
    f == g.
  Proof. intros. intermediate (the (map_from a b)).
    apply initMapUniqueness. apply pathsinv0. apply initMapUniqueness. Qed.
  Definition hasZeroObject (C:precategory) := squash (ZeroObject C).
  Definition haszero_opp (C:precategory) : hasZeroObject C -> hasZeroObject C^op.
    intros C. exact (hinhfun (zero_opp C)). Defined.
  Lemma zeroObjectIsomorphy {C:precategory} (a b:ZeroObject C) : iso a b.
  Proof. intros. 
         exact (theInitialObjectIsomorphy C a b (map_from a) (map_from b)). Defined.
  Definition zeroMap' {C:precategory} (a b:ob C) (o:ZeroObject C) := 
    the (map_from o b) ∘ the (map_to o a) : a → b.
  Lemma path_right_composition {C:precategory} (a b c:ob C) (g:a→b) (f f':b→c) :
    f == f' -> f ∘ g == f' ∘ g.
  Proof. intros ? ? ? ? ? ? ? []. reflexivity. Qed.
  Lemma path_left_composition {C:precategory} (a b c:ob C) (f:b→c) (g g':a→b) :
    g == g' -> f ∘ g == f ∘ g'.
  Proof. intros ? ? ? ? ? ? ? []. reflexivity. Qed.
  Lemma zeroMapUniqueness {C:precategory} (x y:ZeroObject C) (a b:ob C) :
    zeroMap' a b x == zeroMap' a b y.
  Proof. intros.
    set(i := the (map_to x a)).
    set(h := the (map_from x y)). 
    set(q := the (map_from y b)).
    intermediate (q ∘ (h ∘ i)). 
    { intermediate ((q ∘ h) ∘ i). 
      { apply path_right_composition. apply uniqueness'. }
      { apply assoc. }}
    apply path_left_composition. apply uniqueness. Qed.
  Lemma zeroMap {C:precategory} (a b:ob C): hasZeroObject C  ->  a → b.
  Proof. intros ? ? ?.
    apply (squash_to_set (zeroMap' a b)). apply setproperty.    
    intros. apply zeroMapUniqueness. Defined.
  Lemma zeroMap'_left_composition {C:precategory} 
        (z:ZeroObject C) (a b c:ob C) (f:b→c) :
    f ∘ zeroMap' a b z == zeroMap' a c z. 
  Proof. intros. unfold zeroMap'. 
         intermediate ((f ∘ the (map_from z b)) ∘ the (map_to z a)).
         { apply pathsinv0. apply assoc. }
         { apply path_right_composition. apply initMapUniqueness. } Qed.
  Lemma zeroMap_left_composition {C:precategory} 
        (a b c:ob C) (f:b→c) (h:hasZeroObject C) : 
    f ∘ zeroMap a b h == zeroMap a c h. 
  Proof. intros ? ? ? ? ?.
    apply (@factor_dep_through_squash (ZeroObject C)). intro. apply setproperty.
    intro z.
    assert (g : forall (b:ob C), zeroMap' a b z == zeroMap a b (squash_element z)).
    { trivial. }
    destruct (g b). destruct (g c). apply zeroMap'_left_composition. Qed.
End ZeroObjects.

Module StandardCategories.
  Definition compose' { C:precategory_data } { a b c:ob C }
    (g:b → c) (f:a → b) : a → c.
  Proof. intros. exact (compose f g). Defined.
  Definition idtomor {C:precategory} (a b:ob C) : a == b -> a → b.
  Proof. intros ? ? ? H. destruct H. exact (identity a). Defined.
  Lemma eq_idtoiso_idtomor {C:precategory} (a b:ob C) (e:a == b) :
    pr1 (idtoiso e) == idtomor _ _ e.
  Proof. intros. destruct e. reflexivity. Defined.
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
  Proof. intro. apply impred.
    intro a. apply impred. intro b. apply isapropisweq. Qed.
  Lemma morphism_from_iso_is_incl (C : precategory) (a b : ob C) :
    isincl (morphism_from_iso C a b).
  Proof. intros. intro g.
    apply (isofhlevelweqf _ (ezweqpr1 _ _)). apply isaprop_is_isomorphism. Qed.
  Lemma is_category_groupoid {C : precategory} : is_groupoid C -> is_category C.
  Proof. intros ? ig ? ?.
    refine (isofhlevelff 0 idtoiso (morphism_from_iso _ _ _) _ _).
    { refine (isweqhomot (idtomor _ _) _ _ _).
      { intro p. destruct p. reflexivity. }
      apply ig. }
      apply morphism_from_iso_is_incl.
  Qed.
  Definition path_pregroupoid (X:UU) : isofhlevel 3 X -> precategory.
    (* Later we'll define a version of this with no hlevel assumption on X,
       where [mor i j] will be defined with [pi0].  This version will still
       be useful, because in it, each arrow is a path, rather than an
       equivalence class of paths. *)
    intros obj iobj.
    refine (makePrecategory obj _ iobj _ _ _ _ _).
    { intros. reflexivity. }
    { intros. exact (f @ g). }
    { intros. reflexivity. }
    { intros. apply pathscomp0rid. }
    { intros. apply path_assoc_opaque. }
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

  Require Import Foundations.hlevel2.stnfsets.

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

Module RepresentableFunctors.
  (** ** representable functors *)
  (** *** the category of elements of a functor *)
  Definition El_data {C} (X:C==>SET) : precategory_data.
    intros C X.
    set (Fobj := X:1:1).
    set (Fmor := X:1:2).
    set (iFid := X:2:1).
    set (iFcomp := X:2:2).
    set (obj := total2 (fun c : ob C => set_to_type (Fobj c))).
    set (compat := fun a b : obj =>
                     fun f : pr1 a → pr1 b => Fmor _ _ f a:2 == b:2 ).
    set (mor := fun a b => total2 (compat a b)).
    apply (makePrecategory_data obj mor).
    - intros. apply (isofhleveltotal2 2). 
      * apply setproperty.
      * intros f.  apply (isofhlevelsnprop 1). apply setproperty.
    - intro a. exact (identity a:1 ,, (apevalat a:2 (iFid a:1))).
    - intros ? ? ? f g.
      exact (      g:1 ∘ f:1,,
                   ((apevalat i:2 (iFcomp _ _ _ f:1 g:1))
                    @ 
                    (ap (Fmor _ _ g:1) f:2 @ g:2))). Defined.
  Lemma El_okay {C} (X:C==>SET) : is_precategory (El_data X).
  Proof.
    intros. split. split.
    - intros a b [f f'].
      exact (pair_path (id_left _ _ _ f) (the (setproperty _ _ _ _ _))).
    - intros a b [f f'].
      exact (pair_path (id_right _ _ _ f) (the (setproperty _ _ _ _ _))).
    - intros ? ? ? ? f g h.     (* destructing f,g,h adds 1.75 seconds *)
      exact (pair_path 
               (assoc _ _ _ _ _ f:1 g:1 h:1)
               (the (setproperty _ _ _ _ _))). Qed.
  Definition El {C} (X:C==>SET) : precategory.
    intros. exact (El_data X ,, El_okay X). Defined.
  Definition El_pr1_data {C} (X:C==>SET) : functor_data (El X) C.
    intros. exists pr1. intros x x'. exact pr1. Defined.
  Definition El_pr1 {C} (X:C==>SET) : El X ==> C.
    intros. exists (El_pr1_data _).
    split. { intros. reflexivity. } { intros. reflexivity. } Defined.
  Definition El_make_ob {C} (X:C==>SET) 
             (c:ob C) (x:set_to_type (X c)) : ob (El X).
    intros. exact (c,,x). Defined.
  Definition El_make_mor {C} (X:C==>SET) (r s : ob (El X)) 
             (f : Hom (El_pr1 X r) (El_pr1 X s))
             (i : #X f (pr2 r) == pr2 s) : Hom r s.
    intros. exact (f,,i). Defined.
  Definition reflects_isos {C D} (X:C==>D) :=
    forall c c' (f : c → c'), is_isomorphism (#X f) -> is_isomorphism f.
  Lemma isaprop_reflects_isos {C D} (X:C==>D) : isaprop (reflects_isos X).
  Proof.
    intros. apply impred; intros. apply impred; intros. apply impred; intros.
    apply impred; intros. apply isaprop_is_isomorphism. Qed.
  Lemma El_pr1_reflects_isos {C} (X:ob [C, SET]) : reflects_isos (El_pr1 X).
  Proof.
    intros. simpl in X.         (* why do we need this? *)
    intros cx dy fi iso_f.
    set (c := cx:1). set (x := cx:2).
    set (d := dy:1). set (y := dy:2).
    set (f := fi:1). set (i := fi:2).
    set (f' := iso_f:1). set (j := iso_f:2).
    assert (i' : #X f' y == x).
    { intermediate (#X f' (#X f x)).
      { exact (ap (#X f') (!i)). }
      { intermediate (#X (f' ∘ f) x).
        { exact (apevalat x (!functor_comp _ _ X _ _ _ f f')). }
        { intermediate (#X (identity c) x).
          { exact (apevalat x (ap #X j:1)). }
          { exact (apevalat x (functor_id _ _ X c)). }}}}
    { exists (f' ,, i'). split.
      { exact (pair_path j:1 (the (setproperty _ _ _ _ _))). }
      { exact (pair_path j:2 (the (setproperty _ _ _ _ _))). }} Qed.
  Import PrimitiveInitialObjects.
  Definition Representation {C} (X:C==>SET) := InitialObject (El X).
  Definition Representable {C} (X:C==>SET) := squash (Representation X).
  Definition representingPair {C} {X:C==>SET} (r:Representation X) := 
    pr1 r : ob (El X).
  Definition representingInitiality {C} {X:C==>SET} (r:Representation X) : 
    isInitialObject (El X) (representingPair r).
  Proof. intros. exact (pr2 r). Qed.
  Definition representingObject {C} {X:C==>SET} (r:Representation X) :=
    pr1 (representingPair r) : ob C .
  Definition representingElement {C} {X:C==>SET} (r:Representation X) := 
    pr2 (representingPair r) : set_to_type (X (representingObject r)).
  Definition representingMap {C} {X:C==>SET} (r:Representation X) (d:ob C) :
    Hom (representingObject r) d -> set_to_type (X d).
  Proof. intros ? ? ? ? p. exact (#X p (representingElement r)). Defined.
  Lemma representingMap_isweq {C} {X:C==>SET} (r:Representation X) (d:ob C) :
    isweq (representingMap r d).
  Proof. intros. intros y. exact (representingInitiality r (d,,y)). Qed.
  Definition representingIso {C} {X:C==>SET} (r:Representation X) (d:ob C) 
    := weqpair (representingMap r d) (representingMap_isweq r d) 
       : weq (representingObject r → d) (set_to_type (X d)).
End RepresentableFunctors.

Module hSet.
  Definition unit : hSet := tpair isaset unit isasetunit.
End hSet.

Module TerminalObjects.
  Definition unitFunctor_data C : functor_data C SET.
    intros. refine (tpair _ _ _).
    intros. exact hSet.unit. intros. exact (idfun _). Defined.
  Definition unitFunctor C : C ==> SET.
    intros. exists (unitFunctor_data C).
    split. reflexivity. reflexivity. Defined.
  Import RepresentableFunctors.
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

Module Products.
  Definition setProduct {I} (X:I -> hSet) : hSet.
    intros. exists (sections (funcomp X set_to_type)).
    apply (impred 2); intros i. apply (pr2 (X i)). Defined.    
  Definition HomFamily_set (C:precategory) {I} (c:I -> ob C) : ob C -> ob SET.
    intros ? ? ? x. exact (setProduct (fun i => Hom (c i) x)). Defined.
  Definition HomFamily_map
             (C:precategory) {I} (c:I -> ob C) (x y:ob C) (f : x → y) :
      set_to_type (HomFamily_set C c x) -> set_to_type (HomFamily_set C c y).
    intros ? ? ? ? ? ? g j; unfold funcomp.
    exact (f ∘ (g j)). Defined.
  Definition HomFamily_data 
             (C:precategory) {I} (c:I -> ob C) : functor_data C SET.
    intros.  exact (HomFamily_set C c,, HomFamily_map C c). Defined.
  Definition HomFamily (C:precategory) {I} (c:I -> ob C) : C ==> SET.
    intros. exists (HomFamily_data C c). split.
    { intros a. apply funextfunax; intros f.  apply funextsec; intros i.
      apply id_right. }
    { intros x y z p q. apply funextfunax; intros f. apply funextsec; intros i.
      apply assoc. } Defined.
  Import RepresentableFunctors.
  Definition Coproduct (C:precategory) {I} (c:I -> ob C) :=
    Representation (HomFamily C c).
  Definition Product (C:precategory) {I} (c:I -> ob C) :=
    Representation (HomFamily C^op c).
  Definition coproductObject {C:precategory} {I} {c:I -> ob C} (r:Coproduct C c)
             : ob C := representingObject r.
  Definition productObject {C:precategory} {I} {c:I -> ob C} (r:Product C c)
             (* the representing object of r is in C^op, so here we convert it *)
             : ob C := representingObject r.
  Coercion coproductObject : Coproduct >-> ob.
  Coercion productObject : Product >-> ob.
  Definition coprod_in
             {C:precategory} {I} {b:I -> ob C} (B:Coproduct C b) i :
     Hom (b i) B.
  Proof. intros. exact (representingElement B i). Defined.
  Definition prod_pr
             {C:precategory} {I} {b:I -> ob C} (B:Product C b) i :
     Hom B (b i).
  Proof. intros. exact (representingElement B i). Defined.
End Products.

Module Matrices.
  Import Products.
  Import RepresentableFunctors.
  (* the representing map is the matrix *)
  Definition to_row {C:precategory} {I} {b:I -> ob C} (B:Coproduct C b) {d:ob C} :
    weq (Hom B d) (forall j, Hom (b j) d).
  Proof. intros. exact (representingIso B d). Defined.
  Definition from_row {C:precategory} {I} {b:I -> ob C} (B:Coproduct C b) {d:ob C} :
    weq (forall j, Hom (b j) d) (Hom B d).
  Proof. intros. apply invweq. apply to_row. Defined.
  Definition to_col {C:precategory} {I} {d:I -> ob C} (D:Product C d) {b:ob C} :
    weq (Hom b D) (forall i, Hom b (d i)).
  Proof. intros. exact (representingIso D b). Defined.
  Definition from_col {C:precategory} {I} {d:I -> ob C} (D:Product C d) {b:ob C} :
    weq (forall i, Hom b (d i)) (Hom b D).
  Proof. intros. apply invweq. apply to_col. Defined.
  Definition to_matrix {C:precategory} 
             {I} {d:I -> ob C} (D:Product C d)
             {J} {b:J -> ob C} (B:Coproduct C b) :
             weq (Hom B D) (forall i j, Hom (b j) (d i)).
  Proof. intros. apply @weqcomp with (Y := forall i, Hom B (d i)).
         { apply to_col. }
         { apply weqonseqfibers; intro i. apply to_row. } Defined.
  Definition from_matrix {C:precategory} 
             {I} {d:I -> ob C} (D:Product C d)
             {J} {b:J -> ob C} (B:Coproduct C b) :
             weq (forall i j, Hom (b j) (d i)) (Hom B D).
  Proof. intros. apply invweq. apply to_matrix. Defined.
  Definition to_matrix' {C:precategory} 
             {I} {d:I -> ob C} (D:Product C d)
             {J} {b:J -> ob C} (B:Coproduct C b) :
             weq (Hom B D) (forall j i, Hom (b j) (d i)).
  Proof. intros. apply @weqcomp with (Y := forall j, Hom (b j) D).
         { apply to_row. }
         { apply weqonseqfibers; intro i. apply to_col. } Defined.
  Definition from_matrix' {C:precategory} 
             {I} {d:I -> ob C} (D:Product C d)
             {J} {b:J -> ob C} (B:Coproduct C b) :
             weq (forall j i, Hom (b j) (d i)) (Hom B D).
  Proof. intros. apply invweq. apply to_matrix'. Defined.
  Lemma to_matrix_equal {C:precategory} 
             {I} {d:I -> ob C} (D:Product C d)
             {J} {b:J -> ob C} (B:Coproduct C b) :
    forall p i j, to_matrix D B p i j == to_matrix' D B p j i.
  Proof. intros. exact (assoc _ _ _ _ _ (coprod_in B j) p (prod_pr D i)). Qed.
End Matrices.

Module FiniteSets.
  Require Import Foundations.hlevel2.finitesets.
  Definition fSet := total2 isfinite.
  Definition fSet_to_type (X:fSet) : Type := pr1 X.
  Coercion fSet_to_type : fSet >-> Sortclass.
  Lemma fSet_isdeceq (I:fSet) : isdeceq I.
  Proof. intros [I i]; simpl. apply @factor_through_squash with (X := finstruct I).
         { apply isapropisdeceq. }
         { intros [n [f j]]. apply @isdeceqweqf with (X := stn n).
           { exists f. assumption. }
           { apply isdeceqstn. } }
         { assumption. } Qed.
End FiniteSets.

Module DirectSums.
  Import Products ZeroObjects.
  Definition identity_matrix {C:precategory} (h:hasZeroObject C)
             {I} {d:I -> ob C} (dec : isdeceq I) : forall i j, Hom (d j) (d i).
  Proof. intros. destruct (dec i j) as [ [] | _ ].
         { apply identity. } { apply zeroMap. apply h. } Defined.
  Definition identity_map {C:precategory} (h:hasZeroObject C)
             {I} {d:I -> ob C} (dec : isdeceq I) (B:Coproduct C d) (D:Product C d)
             : Hom B D.
  Proof. intros. apply Matrices.from_matrix. apply identity_matrix.  
         assumption. assumption. Defined.
  Definition DirectSum {C:precategory} (h:hasZeroObject C)
             {I} (d:I -> ob C) (dec : isdeceq I) 
             := total2 (fun 
                   BD : dirprod (Coproduct C d) (Product C d) =>
                        is_isomorphism (identity_map h dec (pr1 BD) (pr2 BD))).
  Import FiniteSets.
  Definition FiniteDirectSum {C:precategory} (h:hasZeroObject C) 
             {I:fSet} (d:I -> ob C)
    := DirectSum h d (fSet_isdeceq I).
End DirectSums.

Module Kernels.
  Import RepresentableFunctors.
  Import ZeroObjects.
  Definition zerocomp_type {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
    ob C -> Type.
  Proof. intros ? ? ? ? ? x.
    exact (total2( fun g:Hom d x => g ∘ f == zeroMap c x z)). Defined.
  Definition zerocomp_type_isaset {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
    forall x:ob C, isaset (zerocomp_type z f x).
  Proof. intros ? ? ? ? ? x.
    apply (isofhleveltotal2 2).
    { apply setproperty. }
    { intro g.  
      assert( t:isofhlevel 3 (Hom c x) ).
      { apply hlevelntosn.  apply setproperty. }
      exact (t _ _).            (* why doesn't apply t work here? *)
      } Qed.  
  Definition zerocomp_set {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
    ob C -> ob SET.
  Proof. intros ? ? ? ? ? x.
    exact (zerocomp_type z f x,, zerocomp_type_isaset z f x). Defined.
  Definition zerocomp_map {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
    forall x y:ob C,
    x → y 
    ->
    set_to_type (zerocomp_set z f x) -> set_to_type (zerocomp_set z f y).
  Proof. intros ? ? ? ? ? ? ? p [k s]. exists (p ∘ k). rewrite assoc.  rewrite s.
         apply zeroMap_left_composition. Defined.
  Definition zerocomp_data {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
    functor_data C SET.
  Proof. intros. 
         exact (zerocomp_set z f,, zerocomp_map z f). Defined.
  Definition zerocomp {C} (z:hasZeroObject C) {c d:ob C} (f:c → d):C ==> SET.
    intros. exists (zerocomp_data z f). split.
    { intros x. apply funextfunax; intros [r rf0].
      apply (pair_path (id_right _ _ _ r)). apply setproperty. }
    { intros w x y t u. apply funextfunax. intros [r rf0].
      apply (pair_path (assoc _ _ _ _ _ r t u)).
      apply setproperty. } Defined.
  Import RepresentableFunctors.
  Definition Cokernel {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :=
    Representation (zerocomp z f).
  Definition Kernel C (z:hasZeroObject C) (c d:ob C) (f:c → d) :=
    Representation (zerocomp (haszero_opp C z) f).
End Kernels.

Module Magma.
  Require Import Foundations.hlevel2.algebra1a.
  Definition zero : setwithbinop.
    exists hSet.unit. exact (fun _ _ => tt). Defined.
  Definition product {I} (X:I->setwithbinop) : setwithbinop.
    intros.
    assert (is : isaset (sections X)). apply (impred 2); intros i. apply pr2.
    exists (sections X,,is). exact (fun v w i => op (v i) (w i)). Defined.
  Definition productProj {I} (X:I->setwithbinop) (i:I) : binopfun (product X) (X i).
    intros. exists (fun y => y i). intros a b. reflexivity. Defined.
  Definition productFun {I} (X:I->setwithbinop) 
             (T:setwithbinop) (g: forall i, binopfun T (X i))
             : binopfun T (product X).
    intros. exists (fun t i => g i t).
    intros t u. apply funextsec; intro i. apply (pr2 (g i)). Defined.
End Magma.

Module Monoid.
  Require Import Foundations.hlevel2.algebra1b.
  Definition zero : monoid.
    exists Magma.zero. split. intros x y z. reflexivity.
    exists tt. split. intros []. reflexivity. intros []. reflexivity.
  Defined.
  Definition product {I} (X:I->monoid) : monoid.
    intros. exists (Magma.product X). split.
    intros a b c. apply funextsec; intro. apply assocax.
    exists (fun i => unel (X i)). split.
    intros a. apply funextsec; intro. apply lunax.
    intros a. apply funextsec; intro. apply runax. Defined.
  Definition productProj {I} (X:I->monoid) (i:I) : monoidfun (product X) (X i).
    intros. exists (pr1 (Magma.productProj X i)). split. 
    exact (pr2 (Magma.productProj X i)). simpl. reflexivity. Defined.
  Definition productFun {I} (X:I->monoid) 
             (T:monoid) (g: forall i, monoidfun T (X i))
             : monoidfun T (product X).
    intros.  exists (pr1 (Magma.productFun X T g)). 
    exists (pr2 (Magma.productFun X T g)). apply funextsec; intro i.
    apply (pr2 (pr2 (g i))). Defined.
End Monoid.

Module Gr.
  Require Import Foundations.hlevel2.algebra1b.
  Definition zero : gr.
    exists Monoid.zero. exists (pr2 Monoid.zero). exists (idfun unit).
    split. intro x. apply (idpath _). intro x. apply (idpath _). Defined.
  Definition product {I} (X:I->gr) : gr.
    intros. 
    set (Y := Monoid.product X). exists (pr1monoid Y). exists (pr2 Y).
    exists (fun y i => grinv (X i) (y i)).
    split.
    intro y. apply funextsec; intro i. apply grlinvax.
    intro y. apply funextsec; intro i. apply grrinvax.
  Defined.    
  Definition productProj {I} (X:I->gr) (i:I) : monoidfun (product X) (X i).
    intros. apply (Monoid.productProj X i). Defined.
  Definition productFun {I} (X:I->gr) 
             (T:gr) (g: forall i, monoidfun T (X i))
             : monoidfun T (product X).
    intros. exact (Monoid.productFun X T g). Defined.
End Gr.

Module Abgr.
  Require Import Foundations.hlevel2.algebra1b.
  Definition commax (G:abgr) := pr2 (pr2 G).
  Definition zero : abgr.
    exists Gr.zero. split. exact (pr2 Gr.zero). intros x y. apply (idpath _).
  Defined.
  Require Import Foundations.hlevel2.hz.
  Definition Z : abgr := hzaddabgr.
  Import FiniteSets.
  Definition product {I} (X:I->abgr) : abgr.
    intros. exists (pr1 (Gr.product X)).
    split. exact (pr2 (Gr.product X)).
    intros a b. apply funextsec; intro i. apply commax. Defined.
  Definition productProj {I} (X:I->abgr) (i:I) : monoidfun (product X) (X i).
    intros. apply (Gr.productProj X i). Defined.
  Definition productFun {I} (X:I->abgr) 
             (T:abgr) (g: forall i, monoidfun T (X i))
             : monoidfun T (product X).
    intros. exact (Gr.productFun X T g). Defined.
  Definition power (I:Type) (X:abgr) : abgr.
    intros. exact (product (fun _:I => Z)). Defined.
End Abgr.

Module Ab.                      (* the category of abelian groups *)
  Require Import Foundations.hlevel2.algebra1a Foundations.hlevel2.algebra1b.
  Definition ob_mor : precategory_ob_mor.
    exists abgr. intros G H. exists (monoidfun G H). exact (isasetmonoidfun G H).
  Defined.
  Definition data : precategory_data.
    exists ob_mor. split. intro G. exists (idfun (G : abgr)). split. 
    split. reflexivity. intros a b c.  exact monoidfuncomp. Defined.
  Definition cat : precategory.
    exists data. split; simpl. split; simpl.
    intros a b [f i]. apply (pair_path (idpath _)). apply isapropismonoidfun.
    intros a b [f i]. apply (pair_path (idpath _)). apply isapropismonoidfun.
    intros a b c d f g h. apply (pair_path (idpath _)). apply isapropismonoidfun.
  Defined.
  Import Products.
  Definition productObject {I} (X:I->ob cat) : ob cat := Abgr.product X.
  Definition productProj {I} (X:I->ob cat) (i:I) : Hom (productObject X) (X i)
     := Abgr.productProj X i.
  Definition productMor {I} (X:I->ob cat) 
             (T:ob cat) (g: forall i, @Hom cat T (X i))
             : @Hom cat T (productObject X).
    intros. exists (pr1 (Abgr.productFun X T g)).
    exact (pr2 (Abgr.productFun X T g)). Defined.
  Import PrimitiveInitialObjects RepresentableFunctors.
  Definition product {I} (X:I->ob cat) : Product cat X.
    intros.
    set (P := productObject X).
    set (p := productProj X).
    exists (P,,p).
    intros [T g].
    simpl in g.
    unfold funcomp in g.
    simpl in g.
    admit.
  Defined.
End Ab.

(**
  We are working toward definitions of "additive category" and "abelian
  category" as properties of a category, rather than as an added structure.
  That is the approach of Mac Lane in sections 18, 19, and 21 of :

  #<a href="http://projecteuclid.org/DPubS/Repository/1.0/Disseminate?view=body&id=pdf_1&handle=euclid.bams/1183515045">Duality for groups</a>#,
  Bull. Amer. Math. Soc., Volume 56, Number 6 (1950), 485-516.
 *)
