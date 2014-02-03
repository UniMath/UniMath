(* -*- coding: utf-8 -*- *)

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
Local Notation "a → b" := (precategory_morphisms a b) (at level 50).
Local Notation "a ==> b" := (functor a b) (at level 50).
Local Notation "f ;; g" := (precategories.compose f g) (at level 50, only parsing).
Local Notation "g ∘ f" := (precategories.compose f g) (at level 50, only parsing).
Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Notation "C '^op'" := (opp_precat C) (at level 3).
Notation SET := hset_precategory.

Definition Ob (C:precategory) : Type := ob C.

Definition precategory_pair (C:precategory_data) (i:is_precategory C)
  : precategory := tpair _ C i.
Module Precategory.
  Definition obmor (C:precategory) : precategory_ob_mor := 
        precategory_ob_mor_from_precategory_data (
            precategory_data_from_precategory C).
  Definition obj (C:precategory) : Type :=
    ob (
        precategory_ob_mor_from_precategory_data (
            precategory_data_from_precategory C)).
  Definition mor {C:precategory} : ob C -> ob C -> hSet :=
    pr2 (
        precategory_ob_mor_from_precategory_data (
            precategory_data_from_precategory C)).
End Precategory.
Local Notation Hom := Precategory.mor.

Module Functor.
  Definition obmor {C D} (F:functor C D) := pr1 F.
  Definition obj {C D} (F:functor C D) := pr1 (pr1 F).
  Definition mor {C D} (F:functor C D) := pr2 (pr1 F).
  Definition identity {C D} (F:functor C D) := functor_id F.
  Definition compose {C D} (F:functor C D) := functor_comp F.
End Functor.

Definition category_pair (C:precategory) (i:is_category C)
 : category := tpair _ C i.

Definition theUnivalenceProperty (C:category) := pr2 _ : is_category C.

Definition reflects_isos {C D} (X:C==>D) :=
  forall c c' (f : c → c'), is_isomorphism (#X f) -> is_isomorphism f.

Lemma isaprop_reflects_isos {C D} (X:C==>D) : isaprop (reflects_isos X).
Proof.
  intros. apply impred; intros. apply impred; intros. apply impred; intros.
  apply impred; intros. apply isaprop_is_isomorphism. Qed.

(** *** make a precategory *)

Definition makePrecategory_ob_mor
    (obj : UU)
    (mor : obj -> obj -> UU)
    (imor : ∀ i j:obj, isaset (mor i j))
    : precategory_ob_mor.
  intros.
  exact (precategory_ob_mor_pair obj (fun i j:obj => hSetpair (mor i j) (imor i j))).
Defined.    

Definition makePrecategory_data
    (obj : UU)
    (mor : obj -> obj -> UU)
    (imor : ∀ i j, isaset (mor i j))
    (identity : ∀ i, mor i i)
    (compose : forall i j k (f:mor i j) (g:mor j k), mor i k)
    : precategory_data.
  intros.
  exact (precategory_data_pair (makePrecategory_ob_mor obj mor imor) identity compose).
Defined.    

Definition makePrecategory 
    (obj : UU)
    (mor : obj -> obj -> UU)
    (imor : forall i j, isaset (mor i j))
    (identity : forall i, mor i i)
    (compose : forall i j k (f:mor i j) (g:mor j k), mor i k)
    (right : forall i j (f:mor i j), compose _ _ _ (identity i) f == f)
    (left  : forall i j (f:mor i j), compose _ _ _ f (identity j) == f)
    (associativity : forall a b c d (f:mor a b) (g:mor b c) (h:mor c d),
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
  intro. apply isofhleveltotal2.
  { apply isofhleveltotal2. { repeat (apply impred; intro); apply setproperty. }
    intros _. repeat (apply impred; intro); apply setproperty. }
  intros _. repeat (apply impred; intro); apply setproperty. Qed.

Lemma opp_opp_precat (C : precategory) : C == C^op^op.
Proof.
  intros [data ispre]. apply (pair_path (opp_opp_precat_data data)).
  apply isaprop_is_precategory. Defined.

Module Primitive.
  Module TerminalObject. (** *** terminal objects *)
    Definition isTerminalObject (C:precategory) (a:ob C) := 
      ∀ x:ob C, iscontr (a ← x).
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
  End TerminalObject.

  Module InitialObject.
    Definition isInitialObject (C:precategory) (a:ob C) :=
      ∀ x:ob C, iscontr (x ← a).
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
    Record InitialObject (C:precategory) := make_InitialObject {
         theInitialObject : ob C ;
         theInitialProperty : isInitialObject C theInitialObject }.
    Definition InitialObject_total (C:precategory) := total2 (fun a:ob C => isInitialObject C a).
    Definition unpack {C:precategory} : InitialObject_total C -> InitialObject C
      := fun X => make_InitialObject C (pr1 X) (pr2 X).
    Definition pack {C:precategory} : InitialObject C -> InitialObject_total C
      := fun Y => (theInitialObject _ Y,,theInitialProperty _ Y).
    Definition h {C:precategory} (X:InitialObject_total C) : pack (unpack X) == X
      := match X as t return (pack (unpack t) == t) with X1,, X2 => idpath (X1,, X2) end.
    Definition k {C:precategory} (Y:InitialObject C) : unpack (pack Y) == Y
      := match Y as i return (unpack (pack i) == i) 
         with make_InitialObject Y1 Y2 => idpath _ end.
    Lemma unpack_weq (C:precategory) : weq (InitialObject_total C) (InitialObject C).
    Proof. intros. exists unpack. intros Y. exists (pack Y,,k Y). intros [X m].
           destruct m. set (H := h X). destruct H. reflexivity. Qed.
    Lemma isaprop_InitialObject' (C:category) : isaprop (InitialObject_total C).
    Proof. intros. apply invproofirrelevance. intros a b.
      apply (total2_paths (isotoid _ (theUnivalenceProperty C) 
                                   (theInitialObjectIsomorphy C _ _ (pr2 a) (pr2 b)))).
      apply isaprop_isInitialObject. Qed.
    Lemma isaprop_InitialObject (C:category) : isaprop (InitialObject C).
      intros. apply isofhlevelweqf with (X := InitialObject_total C).
      apply unpack_weq. apply isaprop_InitialObject'. Qed.
    Definition squashInitialObject (C:precategory) := squash (InitialObject C).
    Definition squashInitialObjectProp (C:precategory) := 
      hProppair (squashInitialObject C) (isaprop_squash _).
  End InitialObject.
End Primitive.

Module ZeroObject.
  Import Primitive.TerminalObject.
  Import Primitive.InitialObject.
  Definition ZeroObject (C:precategory) := total2 ( fun 
               z : ob C => dirprod (
                   isInitialObject C z) (
                   isTerminalObject C z) ).
  Definition zero_opp (C:precategory) : ZeroObject C -> ZeroObject C^op.
    intros C [z [i t]]. exact (z ,, (t ,, i)). Defined.
  Definition zero_opp' (C:precategory) : ZeroObject C^op -> ZeroObject C.
    intros ? X. exact (zero_opp C^op X). Defined.
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
  Proof. intros. set(i := the (map_to x a)).
    set(h := the (map_from x y)). set(q := the (map_from y b)).
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
    assert (g : ∀ b:ob C, zeroMap' a b z == zeroMap a b (squash_element z)).
    { trivial. }
    destruct (g b). destruct (g c). apply zeroMap'_left_composition. Qed.
End ZeroObject.

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
    ∀ a b : ob C, isweq (fun p : a == b => idtomor a b p).
  Lemma isaprop_is_groupoid (C : precategory) : isaprop (is_groupoid C).
  Proof. intro. apply impred.
    intro a. apply impred. intro b. apply isapropisweq. Qed.
  Lemma morphism_from_iso_is_incl (C : precategory) (a b : ob C) :
    isincl (morphism_from_iso C a b).
  Proof. intros ? ? ? g.
    apply (isofhlevelweqf _ (ezweqpr1 _ _)). apply isaprop_is_isomorphism. Qed.
  Lemma is_category_groupoid {C : precategory} : is_groupoid C -> is_category C.
  Proof. intros ? ig ? ?.
    refine (isofhlevelff 0 idtoiso (morphism_from_iso _ _ _) _ _).
    { refine (isweqhomot (idtomor _ _) _ _ _).
      { intro p. destruct p. reflexivity. }
      apply ig. }
      apply morphism_from_iso_is_incl. Qed.
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
  Proof. intros ? ? a b.
    assert (k : idfun (a == b) ~ idtomor a b). { intro p. destruct p. reflexivity. }
    apply (isweqhomot _ _ k). apply idisweq. Qed.
  Lemma is_category_path_pregroupoid (X:UU) (i:isofhlevel 3 X) :
    is_category (path_pregroupoid X i).
  Proof. intros. apply is_category_groupoid. apply is_groupoid_path_pregroupoid.
  Qed.
  Definition path_groupoid (X:UU) : isofhlevel 3 X -> category.
  Proof. intros ? iobj. apply (category_pair (path_pregroupoid X iobj)). 
    apply is_category_path_pregroupoid. Defined.

  (** *** the discrete category on n objects *)
  Require Import Foundations.hlevel2.stnfsets.
  Definition cat_n (n:nat):category.
    intro. apply (path_groupoid (stn n)). apply hlevelntosn.
    apply isasetstn. Defined.
  Definition is_discrete (C:precategory) := 
    dirprod (isaset (ob C)) (is_groupoid C).
  Lemma isaprop_is_discrete (C:precategory) : 
    isaprop (is_discrete C).
  Proof. intro. apply isofhleveltotal2. apply isapropisaset.
    intro is. apply isaprop_is_groupoid. Qed.
  Lemma is_discrete_cat_n (n:nat) : is_discrete (cat_n n).
  Proof. intro. split. apply isasetstn. apply is_groupoid_path_pregroupoid. Qed.
End StandardCategories.

Module Elements.
  (** *** the category of elements of a functor *)
  Definition cat_data {C} (X:C==>SET) : precategory_data.
    intros C X.
    set (obj := total2 (fun c : ob C => set_to_type ((Functor.obj X) c))).
    apply (makePrecategory_data 
             obj 
             (fun a b : obj => 
                total2 (fun f : pr1 a → pr1 b => 
                          (Functor.mor X) _ _ f (pr2 a) == (pr2 b)))).
    - abstract (
          intros; apply (isofhleveltotal2 2);
          [ apply setproperty |
            intros f;  apply (isofhlevelsnprop 1); apply setproperty])
      using cat_data_isaset.
    - intro a. 
      exact (identity (pr1 a),, (apevalat (pr2 a) ((functor_id X) (pr1 a)))).
    - intros ? ? ? f g.
      exact (pr1 g ∘ pr1 f,,
             (  (apevalat (pr2 i) ((functor_comp X) _ _ _ (pr1 f) (pr1 g)))
              @ (ap ((Functor.mor X) _ _ (pr1 g)) (pr2 f) @ (pr2 g)))). Defined.
  Definition get_mor {C} {X:C==>SET} {x y:ob (cat_data X)} (f:x → y) := pr1 f.
  Lemma mor_equality {C} (X:C==>SET) (x y:ob (cat_data X)) (f g:x → y) :
        get_mor f == get_mor g -> f == g.
  Proof. intros ? ? ? ? [f i] [g j] p. simpl in p. destruct p.
         assert (k : i==j). { apply equality_proof_irrelevance. }
         destruct k. reflexivity. Qed.
  Lemma isPrecategory {C} (X:C==>SET) : is_precategory (cat_data X).
  Proof. intros. split. split.
         - intros. apply mor_equality. apply id_left.
         - intros. apply mor_equality. apply id_right.
         - intros. apply mor_equality. apply assoc. Qed.
  Definition cat {C} (X:C==>SET) : precategory.
    intros. exact (cat_data X ,, isPrecategory X). Defined.
  Definition get_ob {C} {X:C==>SET} (x:ob (cat X)) := pr1 x.
  Definition get_el {C} {X:C==>SET} (x:ob (cat X)) := pr2 x.
  Definition make_ob {C} (X:C==>SET) 
             (c:ob C) (x:set_to_type (X c)) : ob (cat X).
    intros. exact (c,,x). Defined.
  Definition make_mor {C} (X:C==>SET) (r s : ob (cat X)) 
             (f : Hom (pr1 r) (pr1 s))
             (i : #X f (pr2 r) == pr2 s) : Hom r s.
    intros. exact (f,,i). Defined.
  Module pr1.
    Definition fun_data {C} (X:C==>SET) : 
        functor_data (Precategory.obmor (cat X)) (Precategory.obmor C).
      intros. exists pr1. intros x x'. exact pr1. Defined.
    Definition func {C} (X:C==>SET) : cat X ==> C.
      intros. exists (fun_data _).
      split. { intros. reflexivity. } { intros. reflexivity. } Defined.
    Lemma func_reflects_isos {C} (X:C==>SET) : reflects_isos (func X).
    Proof. intros ? ? [c x] [d y] [f i] [f' j].
      assert (i' : #X f' y == x).
      { intermediate (#X f' (#X f x)).
        { exact (ap (#X f') (!i)). }
        { intermediate (#X (f' ∘ f) x).
          { exact (apevalat x (!functor_comp X _ _ _ f f')). }
          { intermediate (#X (identity c) x).
            { exact (apevalat x (ap #X (pr1 j))). }
            { exact (apevalat x (functor_id X c)). }}}}
      { exists (f' ,, i'). split.
        { apply mor_equality.  exact (pr1 j). }
        { apply mor_equality.  exact (pr2 j). } } Qed.
  End pr1.
End Elements.

Module Representation.
  Import Primitive.InitialObject.
  Definition Data {C} (X:C==>SET) := InitialObject (Elements.cat X).
  Definition Property {C} (X:C==>SET) := squash (Data X).
  Definition Pair {C} {X:C==>SET} (r:Data X) : ob (Elements.cat X)
    := theInitialObject _ r.
  Definition IsInitial {C} {X:C==>SET} (r:Data X) : 
    isInitialObject (Elements.cat X) (Pair r).
  Proof. intros. exact (theInitialProperty _ r). Qed.
  Definition Object {C} {X:C==>SET} (r:Data X) := pr1 (Pair r) : ob C .
  Definition Element {C} {X:C==>SET} (r:Data X) : set_to_type (X (Object r))
    := pr2 (Pair r).
  Definition Map {C} {X:C==>SET} (r:Data X) (d:ob C) : 
    Hom (Object r) d -> set_to_type (X d).
  Proof. intros ? ? ? ? p. exact (#X p (Element r)). Defined.
  Lemma MapIsweq {C} {X:C==>SET} (r:Data X) (d:ob C) : isweq (Map r d).
  Proof. intros. intros y. exact (IsInitial r (d,,y)). Qed.
  Definition Iso {C} {X:C==>SET} (r:Data X) (d:ob C) 
       := weqpair (Map r d) (MapIsweq r d) 
        : weq (Object r → d) (set_to_type (X d)).
End Representation.

Module hSet.
  Definition unit : hSet := tpair isaset unit isasetunit.
  Definition Product {I} (X:I -> hSet) : hSet.
    intros. exists (sections (funcomp X set_to_type)).
    apply (impred 2); intros i. apply (pr2 (X i)). Defined.    
End hSet.

Module FiniteSet.
  Require Import Foundations.hlevel2.finitesets.
  Definition Data := total2 isfinite.
  Definition ToType (X:Data) : Type := pr1 X.
  Module Import Coercions.
    Coercion ToType : Data >-> Sortclass.
  End Coercions.
  Lemma Isdeceq (I:Data) : isdeceq I.
  Proof. intros [I i]; simpl. apply @factor_through_squash with (X := finstruct I).
         { apply isapropisdeceq. }
         { intros [n [f j]]. apply @isdeceqweqf with (X := stn n).
           { exists f. assumption. }
           { apply isdeceqstn. } }
         { assumption. } Qed.
End FiniteSet.

Module TerminalObject.
  Definition unitFunctor_data (C:precategory) 
       : functor_data (Precategory.obmor C) (Precategory.obmor SET).
    intros. refine (tpair _ _ _).
    intros. exact hSet.unit. intros. exact (idfun _). Defined.
  Definition unitFunctor C : C ==> SET.
    intros. exists (unitFunctor_data C).
    split. reflexivity. reflexivity. Defined.
  Definition InitialObject (C:precategory) := Representation.Data (unitFunctor C).
  Definition initialObject {C} (i:InitialObject C) : ob C.
    intros C i. exact (Representation.Object i). Defined.
  Definition initialArrow {C} (i:InitialObject C) (c:ob C) : initialObject i → c.
    intros C [[i []] p] c. exact (pr1 (the (p (c,,tt)))). Defined.
  Definition TerminalObject (C:precategory) 
    := Representation.Data (unitFunctor C^op).
  Definition terminalObject {C} (t:InitialObject C) : ob C.
    intros C t. exact (Representation.Object t). Defined.
  Definition terminalArrow {C} (t:TerminalObject C) (c:ob C) : c → terminalObject t.
    intros C [[i []] p] c. exact (pr1 (the (p (c,,tt)))). Defined.      
End TerminalObject.

Module HomFamily.
  Definition set (C:precategory) {I} (c:I -> ob C) : ob C -> ob SET.
    intros ? ? ? x. exact (hSet.Product (fun i => Hom (c i) x)). Defined.
  Definition map (C:precategory) {I} (c:I -> ob C) (x y:ob C) (f : x → y) :
      set_to_type (HomFamily.set C c x) -> set_to_type (HomFamily.set C c y).
    intros ? ? ? ? ? ? g j; unfold funcomp.
    exact (f ∘ (g j)). Defined.
  Definition data (C:precategory) {I} (c:I -> ob C)
       : functor_data (Precategory.obmor C) (Precategory.obmor SET).
    intros.  exact (HomFamily.set C c,, HomFamily.map C c). Defined.
  Definition precat (C:precategory) {I} (c:I -> ob C) : C ==> SET.
    intros. exists (HomFamily.data C c). split.
    { intros a. apply funextfunax; intros f.  apply funextsec; intros i.
      apply id_right. }
    { intros x y z p q. apply funextfunax; intros f. apply funextsec; intros i.
      apply assoc. } Defined.
End HomFamily.

Module Product.
  Definition type (C:precategory) {I} (c:I -> ob C) :=
    Representation.Data (HomFamily.precat C^op c).
  Definition Object {C:precategory} {I} {c:I -> ob C} (r:type C c)
             (* the representing object of r is in C^op, so here we convert it *)
             : ob C := Representation.Object r.
  Definition Proj {C:precategory} {I} {b:I -> ob C} (B:type C b) i : 
    Hom (Object B) (b i).
  Proof. intros. exact (Representation.Element B i). Defined.
  Module Coercions.
    Coercion Object : type >-> ob.
  End Coercions.
End Product.

Module Coproduct.
  Definition make (C:precategory) {I} (c:I -> ob C) :=
    Representation.Data (HomFamily.precat C c).
  Definition Object {C:precategory} {I} {c:I -> ob C} (r:make C c)
             : ob C := Representation.Object r.
  Definition In {C:precategory} {I} {b:I -> ob C} (B:make C b) i :
       Hom (b i) (Object B).
  Proof. intros. exact (Representation.Element B i). Defined.
  Module Coercions.
    Coercion Object : make >-> ob.
  End Coercions.
End Coproduct.

Module Matrix.
  (* the representing map is the matrix *)
  Import Coproduct.Coercions Product.Coercions.
  Definition to_row {C:precategory} {I} {b:I -> ob C} 
             (B:Coproduct.make C b) {d:ob C} :
    weq (Hom B d) (∀ j, Hom (b j) d).
  Proof. intros. exact (Representation.Iso B d). Defined.
  Definition from_row {C:precategory} {I} {b:I -> ob C} 
             (B:Coproduct.make C b) {d:ob C} :
    weq (∀ j, Hom (b j) d) (Hom B d).
  Proof. intros. apply invweq. apply to_row. Defined.
  Definition to_col {C:precategory} {I} {d:I -> ob C} (D:Product.type C d) {b:ob C} :
    weq (Hom b D) (∀ i, Hom b (d i)).
  Proof. intros. exact (Representation.Iso D b). Defined.
  Definition from_col {C:precategory} {I} {d:I -> ob C} 
             (D:Product.type C d) {b:ob C} :
    weq (∀ i, Hom b (d i)) (Hom b D).
  Proof. intros. apply invweq. apply to_col. Defined.
  Definition to_matrix {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Coproduct.make C b) :
             weq (Hom B D) (∀ i j, Hom (b j) (d i)).
  Proof. intros. apply @weqcomp with (Y := ∀ i, Hom B (d i)).
         { apply to_col. } { apply weqonseqfibers; intro i. apply to_row. } Defined.
  Definition from_matrix {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Coproduct.make C b) :
             weq (∀ i j, Hom (b j) (d i)) (Hom B D).
  Proof. intros. apply invweq. apply to_matrix. Defined.
  Definition to_matrix' {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Coproduct.make C b) :
             weq (Hom B D) (∀ j i, Hom (b j) (d i)).
  Proof. intros. apply @weqcomp with (Y := ∀ j, Hom (b j) D).
         { apply to_row. } { apply weqonseqfibers; intro i. apply to_col. } Defined.
  Definition from_matrix' {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Coproduct.make C b) :
             weq (∀ j i, Hom (b j) (d i)) (Hom B D).
  Proof. intros. apply invweq. apply to_matrix'. Defined.
  Lemma to_matrix_equal {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Coproduct.make C b) :
    ∀ p i j, to_matrix D B p i j == to_matrix' D B p j i.
  Proof. intros. 
         exact_op (assoc _ _ _ _ _ (Coproduct.In B j) p (Product.Proj D i)). Qed.
End Matrix.

Module DirectSum.
  Import ZeroObject FiniteSet.Coercions Coproduct.Coercions Product.Coercions.
  Definition identity_matrix {C:precategory} (h:hasZeroObject C)
             {I} {d:I -> ob C} (dec : isdeceq I) : ∀ i j, Hom (d j) (d i).
  Proof. intros. destruct (dec i j) as [ [] | _ ].
         { apply identity. } { apply zeroMap. apply h. } Defined.
  Definition identity_map {C:precategory} (h:hasZeroObject C)
             {I} {d:I -> ob C} (dec : isdeceq I) 
             (B:Coproduct.make C d) (D:Product.type C d)
        : Hom B D.
  Proof. intros. apply Matrix.from_matrix. apply identity_matrix.  
         assumption. assumption. Defined.
  Definition DirectSum {C:precategory} (h:hasZeroObject C)
             {I} (d:I -> ob C) (dec : isdeceq I) 
             := total2 (fun 
                   BD : dirprod (Coproduct.make C d) (Product.type C d) =>
                        is_isomorphism (identity_map h dec (pr1 BD) (pr2 BD))).
  Definition FiniteDirectSum {C:precategory} (h:hasZeroObject C) 
             {I:FiniteSet.Data} (d:I -> ob C)
    := DirectSum h d (FiniteSet.Isdeceq I).
End DirectSum.

Module Kernel.
  Import ZeroObject.
  Definition zerocomp_type {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
    ob C -> Type.
  Proof. intros ? ? ? ? ? x.
    exact (total2( fun g:Hom d x => g ∘ f == zeroMap c x z)). Defined.
  Definition zerocomp_type_isaset {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
    ∀ x:ob C, isaset (zerocomp_type z f x).
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
    ∀ x y:ob C, Hom x y ->
    set_to_type (zerocomp_set z f x) -> set_to_type (zerocomp_set z f y).
  Proof. intros ? ? ? ? ? ? ? p [k s]. exists (p ∘ k). rewrite assoc.  rewrite s.
         apply zeroMap_left_composition. Defined.
  Definition zerocomp_data {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :
    functor_data (Precategory.obmor C) (Precategory.obmor SET).
  Proof. intros. 
         exact (zerocomp_set z f,, zerocomp_map z f). Defined.
  Definition zerocomp {C} (z:hasZeroObject C) {c d:ob C} (f:c → d):C ==> SET.
    intros. exists (zerocomp_data z f). split.
    { intros x. apply funextfunax; intros [r rf0].
      apply (pair_path (id_right _ _ _ r)). apply setproperty. }
    { intros w x y t u. apply funextfunax. intros [r rf0].
      apply (pair_path (assoc _ _ _ _ _ r t u)).
      apply setproperty. } Defined.
  Definition Cokernel {C} (z:hasZeroObject C) {c d:ob C} (f:c → d) :=
    Representation.Data (zerocomp z f).
  Definition Kernel C (z:hasZeroObject C) (c d:ob C) (f:c → d) :=
    Representation.Data (zerocomp (haszero_opp C z) f).
End Kernel.

Module Magma.
  Require Import Foundations.hlevel2.algebra1a.
  Local Notation "x * y" := (op x y). 
  Local Notation "g ∘ f" := (binopfuncomp f g) (at level 50, only parsing).
  Local Notation Hom := binopfun.
  Definition funEquality G H (p q : Hom G H)
             (v : pr1 p == pr1 q) : p == q.
    intros ? ? [p i] [q j] v. simpl in v. destruct v.
    destruct (pr1 (isapropisbinopfun p i j)). reflexivity. Qed.
  Definition zero : setwithbinop.
    exists hSet.unit. exact (fun _ _ => tt). Defined.
  Module Product.
    Lemma i1 {I} (X:I->setwithbinop) : isaset(sections X).
    Proof. intros. apply (impred 2); intros i. apply pr2. Qed.
    Definition make {I} (X:I->setwithbinop) : setwithbinop.
      intros.
      exists (sections X,,i1 X). exact (fun v w i => v i * w i). Defined.
    Definition Proj {I} (X:I->setwithbinop) : ∀ i:I, Hom (make X) (X i).
      intros. exists (fun y => y i). intros a b. reflexivity. Defined.
    Definition Fun {I} (X:I->setwithbinop) (T:setwithbinop) (g: ∀ i, Hom T (X i))
               : Hom T (make X).
      intros. exists (fun t i => g i t).
      intros t u. apply funextsec; intro i. apply (pr2 (g i)). Defined.
    Definition Eqn {I} (X:I->setwithbinop) (T:setwithbinop) (g: ∀ i, Hom T (X i))
               : ∀ i, Proj X i ∘ Fun X T g == g i.
      intros. apply funEquality. reflexivity. Qed.
  End Product.
End Magma.

Module Monoid.
  Require Import Foundations.hlevel2.algebra1b.
  Local Notation Hom := monoidfun (only parsing).
  Local Notation "g ∘ f" := (monoidfuncomp f g) (at level 50, only parsing).
  Definition funEquality G H (p q : monoidfun G H) : pr1 p == pr1 q -> p == q.
    intros ? ? [p i] [q j] v. simpl in v. destruct v.
    destruct (pr1 (isapropismonoidfun p i j)). reflexivity. Qed.
  Definition zero : monoid.
    exists Magma.zero. split. intros x y z. reflexivity.
    exists tt. split. intros []. reflexivity. intros []. reflexivity.
  Defined.
  Module Product.
    Definition make {I} (X:I->monoid) : monoid.
      intros. exists (Magma.Product.make X). split.
      intros a b c. apply funextsec; intro. apply assocax.
      exists (fun i => unel (X i)). split.
      intros a. apply funextsec; intro. apply lunax.
      intros a. apply funextsec; intro. apply runax. Defined.
    Definition Proj {I} (X:I->monoid) (i:I) : Hom (make X) (X i).
      intros. exists (pr1 (Magma.Product.Proj X i)). split. 
      exact (pr2 (Magma.Product.Proj X i)). simpl. reflexivity. Defined.
    Definition Fun {I} (X:I->monoid) (T:monoid) (g: ∀ i, Hom T (X i))
               : Hom T (make X).
      intros.  exists (pr1 (Magma.Product.Fun X T g)). 
      exists (pr2 (Magma.Product.Fun X T g)). apply funextsec; intro i.
      exact (pr2 (pr2 (g i))). Defined.
    Definition Eqn {I} (X:I->monoid) (T:monoid) (g: ∀ i, Hom T (X i))
               : ∀ i, Proj X i ∘ Fun X T g == g i.
      intros. apply funEquality. reflexivity. Qed.
    Lemma issurjective_projection {I} (X:I->monoid) (i:I) :
      isdeceq I -> issurjective (Proj X i).
    (* reminder: by 'isasetifdeceq', I is a set, too *)
    Proof. intros ? ? ? decide_equality xi. apply hinhpr. 
      exists (fun j => two_cases (decide_equality i j)
                  (fun p => transport X p xi) (fun _ => unel (X j))).
      simpl. destruct (decide_equality i i) as [q|r]; simpl.
      { assert (e : idpath i == q).
        { apply equality_proof_irrelevance'. apply isasetifdeceq. assumption. }
        destruct e. reflexivity. }
      { destruct (r (idpath i)). } Qed.
    Lemma issurjective_projection' {I} (X:I->monoid) (i:I) :
      LEM -> isaset I -> issurjective (Proj X i).
    Proof. intros ? ? ? lem is. apply issurjective_projection.
      apply LEM_for_sets. assumption. assumption. Qed.
  End Product.
End Monoid.

Module Group.
  Require Import Foundations.hlevel2.algebra1b.
  Local Notation Hom := monoidfun.
  Local Notation "g ∘ f" := (monoidfuncomp f g) (at level 50, only parsing).
  Definition zero : gr.
    exists Monoid.zero. exists (pr2 Monoid.zero). exists (idfun unit).
    split. intro x. reflexivity. intro x. reflexivity. Defined.
  Module Product.
    Definition make {I} (X:I->gr) : gr.
      intros. set (Y := Monoid.Product.make X). exists (pr1monoid Y). exists (pr2 Y).
      exists (fun y i => grinv (X i) (y i)). split.
      - intro y. apply funextsec; intro i. apply grlinvax.
      - intro y. apply funextsec; intro i. apply grrinvax. Defined.    
    Definition Proj {I} (X:I->gr) (i:I) : Hom (make X) (X i).
      intros. exact (Monoid.Product.Proj X i). Defined.
    Definition Fun {I} (X:I->gr) (T:gr) (g: ∀ i, Hom T (X i)) : Hom T (make X).
      intros. exact (Monoid.Product.Fun X T g). Defined.
    Definition Eqn {I} (X:I->gr) (T:gr) (g: ∀ i, Hom T (X i))
               : ∀ i, Proj X i ∘ Fun X T g == g i.
      intros. apply Monoid.funEquality. reflexivity. Qed.
  End Product.
End Group.

(** * abelian groups *)
Module AbelianGroup.
  Require Import Foundations.hlevel2.algebra1b.
  Local Notation Hom := monoidfun.
  Local Notation "g ∘ f" := (monoidfuncomp f g) (at level 50, only parsing).
  Definition commax (G:abgr) := pr2 (pr2 G).
  Definition zero : abgr.
    exists Group.zero. split. exact (pr2 Group.zero). intros x y. reflexivity.
  Defined.
  Require Import Foundations.hlevel2.hz.
  Definition Z : abgr := hzaddabgr.
  Module Product.
    Definition make {I} (X:I->abgr) : abgr.
      intros. exists (pr1 (Group.Product.make X)).
      split. exact (pr2 (Group.Product.make X)).
      intros a b. apply funextsec; intro i. apply commax. Defined.
    Definition Proj {I} (X:I->abgr) (i:I) : Hom (make X) (X i).
      exact @Group.Product.Proj. Defined.
    Definition Map {I} (X:I->abgr) (T:abgr) (g: ∀ i, Hom T (X i)) :
        Hom T (make X).
      exact @Group.Product.Fun. Defined.
    Definition Eqn {I} (X:I->abgr) (T:abgr) (g: ∀ i, Hom T (X i))
             : ∀ i, Proj X i ∘ Map X T g == g i.
      exact @Group.Product.Eqn. Qed.
    Definition UniqueMap {I} (X:I->abgr) (T:abgr) (h h' : Hom T (make X)) :
         (∀ i, Proj X i ∘ h == Proj X i ∘ h') -> h == h'.
      intros ? ? ? ? ? e. apply Monoid.funEquality.
      apply funextfunax; intro t. apply funextsec; intro i.
      exact (apevalat t (ap pr1 (e i))). Qed.
  End Product.
  Definition power (I:Type) (X:abgr) : abgr.
    intros. exact (Product.make (fun _:I => Z)). Defined.
  (** ** the category of abelian groups *)
  Module Category.
    Require Import Foundations.hlevel2.algebra1a Foundations.hlevel2.algebra1b.
    Local Notation Hom := Precategory.mor.
    Definition Ob := abgr.
    Identity Coercion Ob_to_abgr : Ob >-> abgr.
    Definition Mor : Ob -> Ob -> hSet.
      intros G H. exists (monoidfun G H). exact (isasetmonoidfun G H). Defined.
    Definition ObMor : precategory_ob_mor := Ob,,Mor.
    Definition Data : precategory_data.
      exists ObMor. split. intro G. exists (idfun (G : abgr)). split. 
      split. reflexivity. intros a b c.  exact monoidfuncomp. Defined.
    Definition MorEquality G H (p q : Mor G H) : pr1 p == pr1 q -> p == q.
      intros. apply Monoid.funEquality. assumption. Qed.
    Definition Precat : precategory.
      exists Data. split; simpl. split; simpl.
      - intros. apply MorEquality. reflexivity.
      - intros. apply MorEquality. reflexivity.
      - intros. apply MorEquality. reflexivity. Defined.
    Module Product.
      Definition Object {I} (X:I->ob Precat) : ob Precat
        := AbelianGroup.Product.make X.
      Import Primitive.InitialObject.
      Definition make {I} (X:I->ob Precat) : Product.type Precat X.
        intros.
        set (Q := Elements.make_ob (HomFamily.precat Precat^op X) (Object X)
                                   (AbelianGroup.Product.Proj X)).
        exists Q. intros T.
        assert ( k' : Hom Q T ).
        { destruct T as [T_ob T_el].
          exists (AbelianGroup.Product.Map X T_ob T_el). simpl.
          apply funextsec. exact_op (AbelianGroup.Product.Eqn X T_ob T_el). }
        exists k'. intros k. apply Elements.mor_equality.
        exact (AbelianGroup.Product.UniqueMap X (pr1 T) (pr1 k) (pr1 k')
                 (fun i => (apevalsecat i (pr2 k)) @ ! (apevalsecat i (pr2 k')))).
      Defined.
    End Product.
  End Category.
End AbelianGroup.

(**
  We are working toward definitions of "additive category" and "abelian
  category" as properties of a category, rather than as an added structure.
  That is the approach of Mac Lane in sections 18, 19, and 21 of :

  #<a href="http://projecteuclid.org/DPubS/Repository/1.0/Disseminate?view=body&id=pdf_1&handle=euclid.bams/1183515045">Duality for groups</a>#,
  Bull. Amer. Math. Soc., Volume 56, Number 6 (1950), 485-516.
 *)
