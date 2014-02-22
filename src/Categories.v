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

Lemma iso_set_isweq {X Y:hSet} (f:X->Y) (g:Y->X) :
  (forall x, g(f x) == x) ->
  (forall y, f(g y) == y) ->
  isweq f.
Proof.
  intros ? ? ? ? p q y.
  refine ((g y,,_),,_).
  - exact (q y).
  - intros [x e]. induction e. refine (pair_path (! p x) _).
    apply setproperty.
Defined.  

Lemma iso_comp_right_isweq {C:precategory} {a b:ob C} (h:iso a b) (c:C) :
  isweq (fun f : Hom b c => f ∘ h).
Proof. intros. apply (iso_set_isweq (fun f => f ∘ h) (fun g  => g ∘ inv_from_iso h)).
       { intros f. refine (_ @ ap (fun m => f ∘ m) (pr2 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } }
       { intros g. refine (_ @ ap (fun m => g ∘ m) (pr1 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } } Qed.

Definition opp_iso {C:precategory} {a b:ob C} : @iso C a b -> @iso C^op b a.
  intros ? ? ? f.
  exact (pr1 f,,pr1 (pr2 f),,pr2 (pr2 (pr2 f)),,pr1 (pr2 (pr2 f))).
Defined.

Lemma iso_comp_left_isweq {C:precategory} {a b:ob C} (h:iso a b) (c:C) :
  isweq (fun f : Hom c a => h ∘ f).
Proof. intros. apply (@iso_comp_right_isweq C^op b a (opp_iso h)). Qed.

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
    (imor : forall i j:obj, isaset (mor i j))
    : precategory_ob_mor.
  intros.
  exact (precategory_ob_mor_pair obj (fun i j:obj => hSetpair (mor i j) (imor i j))).
Defined.    

Definition makePrecategory_data
    (obj : UU)
    (mor : obj -> obj -> UU)
    (imor : forall i j, isaset (mor i j))
    (identity : forall i, mor i i)
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

Lemma opp_opp_precat (C : precategory) : C == C^op^op.
Proof.
  intros [data ispre]. apply (pair_path (opp_opp_precat_data data)).
  apply isaprop_is_precategory. Defined.

Module Primitive.
  (** *** terminal objects *)
  Module TerminalObject.
    Definition isTerminalObject (C:precategory) (a:ob C) := 
      forall x:ob C, iscontr (a ← x).
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

  (** *** initial objects *)
  Module InitialObject.
    Definition isInitialObject (C:precategory) (a:ob C) :=
      forall x:ob C, iscontr (x ← a).
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
    Definition InitialObject_total (C:precategory) := 
      total2 (fun a:ob C => isInitialObject C a).
    Definition unpack {C:precategory} : InitialObject_total C -> InitialObject C
      := fun X => make_InitialObject C (pr1 X) (pr2 X).
    Definition pack {C:precategory} : InitialObject C -> InitialObject_total C
      := fun Y => (theInitialObject _ Y,,theInitialProperty _ Y).
    Definition h {C:precategory} (X:InitialObject_total C) : pack (unpack X) == X
      := match X as t return (pack (unpack t) == t) 
         with X1,, X2 => idpath (X1,, X2) end.
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
    { apply path_left_composition. apply uniqueness. } Qed.
  Lemma zeroMap {C:precategory} (a b:ob C): hasZeroObject C  ->  a → b.
  Proof. intros ? ? ?. apply (squash_to_set (zeroMap' a b)). apply setproperty.    
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
  Proof. intros ? ? ? ? ?. apply (@factor_dep_through_squash (ZeroObject C)). 
         intro. apply setproperty. intro z. apply zeroMap'_left_composition. Qed.
End ZeroObject.

Module StandardCategories.
  Definition compose' { C:precategory_data } { a b c:ob C }
    (g:b → c) (f:a → b) : a → c.
  Proof. intros. exact (compose f g). Defined.
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
    forall a b : ob C, isweq (fun p : a == b => idtomor a b p).
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

Module Sum.                     (* coproducts *)
  Definition type (C:precategory) {I} (c:I -> ob C) :=
    Representation.Data (HomFamily.precat C c).
  Definition Object {C:precategory} {I} {c:I -> ob C} (r:type C c)
             : ob C := Representation.Object r.
  Definition In {C:precategory} {I} {b:I -> ob C} (B:type C b) i :
       Hom (b i) (Object B).
  Proof. intros. exact (Representation.Element B i). Defined.
  Module Coercions.
    Coercion Object : type >-> ob.
  End Coercions.
End Sum.

Module Matrix.
  (* the representing map is the matrix *)
  Import Sum.Coercions Product.Coercions.
  Definition to_row {C:precategory} {I} {b:I -> ob C} 
             (B:Sum.type C b) {d:ob C} :
    weq (Hom B d) (forall j, Hom (b j) d).
  Proof. intros. exact (Representation.Iso B d). Defined.
  Definition from_row {C:precategory} {I} {b:I -> ob C} 
             (B:Sum.type C b) {d:ob C} :
    weq (forall j, Hom (b j) d) (Hom B d).
  Proof. intros. apply invweq. apply to_row. Defined.
  Lemma from_row_entry {C:precategory} {I} {b:I -> ob C} 
             (B:Sum.type C b) {d:ob C} (f : forall j, Hom (b j) d) :
    forall j, from_row B f ∘ Sum.In B j == f j.
  Proof. intros. exact (apevalsecat j (homotweqinvweq (to_row B) f)). Qed.
  Definition to_col {C:precategory} {I} {d:I -> ob C} (D:Product.type C d) {b:ob C} :
    weq (Hom b D) (forall i, Hom b (d i)).
  Proof. intros. exact (Representation.Iso D b). Defined.
  Definition from_col {C:precategory} {I} {d:I -> ob C} 
             (D:Product.type C d) {b:ob C} :
    weq (forall i, Hom b (d i)) (Hom b D).
  Proof. intros. apply invweq. apply to_col. Defined.
  Lemma from_col_entry {C:precategory} {I} {b:I -> ob C} 
             (D:Product.type C b) {d:ob C} (f : forall i, Hom d (b i)) :
    forall i, Product.Proj D i ∘ from_col D f == f i.
  Proof. intros. exact (apevalsecat i (homotweqinvweq (to_row D) f)). Qed.
  Definition to_matrix {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Sum.type C b) :
             weq (Hom B D) (forall i j, Hom (b j) (d i)).
  Proof. intros. apply @weqcomp with (Y := forall i, Hom B (d i)).
         { apply to_col. } { apply weqonseqfibers; intro i. apply to_row. } Defined.
  Definition from_matrix {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Sum.type C b) :
             weq (forall i j, Hom (b j) (d i)) (Hom B D).
  Proof. intros. apply invweq. apply to_matrix. Defined.
  Lemma from_matrix_entry {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Sum.type C b)
             (f : forall i j, Hom (b j) (d i)) :
    forall i j, (Product.Proj D i ∘ from_matrix D B f) ∘ Sum.In B j == f i j.
  Proof. intros. exact (apevalsecat j (apevalsecat i (homotweqinvweq (to_matrix D B) f))). Qed.
  Lemma from_matrix_entry_assoc {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Sum.type C b)
             (f : forall i j, Hom (b j) (d i)) :
    forall i j, Product.Proj D i ∘ (from_matrix D B f ∘ Sum.In B j) == f i j.
  Proof. intros. refine ( !_ @ from_matrix_entry D B f i j ). apply assoc. Qed.
  Definition to_matrix' {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Sum.type C b) :
             weq (Hom B D) (forall j i, Hom (b j) (d i)).
  Proof. intros. apply @weqcomp with (Y := forall j, Hom (b j) D).
         { apply to_row. } { apply weqonseqfibers; intro i. apply to_col. } Defined.
  Definition from_matrix' {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Sum.type C b) :
             weq (forall j i, Hom (b j) (d i)) (Hom B D).
  Proof. intros. apply invweq. apply to_matrix'. Defined.
  Lemma from_matrix_entry' {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Sum.type C b)
             (f : forall j i, Hom (b j) (d i)) :
    forall j i, Product.Proj D i ∘ (from_matrix' D B f ∘ Sum.In B j) == f j i.
  Proof. intros. exact (apevalsecat i (apevalsecat j (homotweqinvweq (to_matrix' D B) f))). Qed.
  Lemma from_matrix_entry_assoc' {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Sum.type C b)
             (f : forall j i, Hom (b j) (d i)) :
    forall j i, (Product.Proj D i ∘ from_matrix' D B f) ∘ Sum.In B j == f j i.
  Proof. intros. refine ( _ @ from_matrix_entry' D B f j i ). apply assoc. Qed.
  Lemma to_matrix_equal {C:precategory} 
             {I} {d:I -> ob C} (D:Product.type C d)
             {J} {b:J -> ob C} (B:Sum.type C b) :
    forall p i j, to_matrix D B p i j == to_matrix' D B p j i.
  Proof. intros. 
         exact_op (assoc _ _ _ _ _ (Sum.In B j) p (Product.Proj D i)). Qed.
End Matrix.

Module DirectSum.
  (** *** direct sums

      Recall that X is a family of objects in a category, and the map from the 
      sum to the product is an isomorphism, then the sum is called a direct sum. *)
  Import ZeroObject FiniteSet.Coercions Sum.Coercions Product.Coercions.
  Definition identity_matrix {C:precategory} (h:hasZeroObject C)
             {I} (d:I -> ob C) (dec : isdeceq I) : forall i j, Hom (d j) (d i).
  Proof. intros. destruct (dec i j) as [ [] | _ ].
         { apply identity. } { apply zeroMap. apply h. } Defined.
  Definition identity_map {C:precategory} (h:hasZeroObject C)
             {I} {d:I -> ob C} (dec : isdeceq I) 
             (B:Sum.type C d) (D:Product.type C d)
        : Hom B D.
  Proof. intros. apply Matrix.from_matrix. apply identity_matrix.  
         assumption. assumption. Defined.
  Record DirectSum {C:precategory} (h:hasZeroObject C) := 
    (* we express this without using addition of morphisms *)
    make_DirectSum {
        ds_I;
        ds_dec : isdeceq ds_I;
        ds_c : ds_I -> ob C;
        ds : C;
        ds_pr : forall i, Hom ds (ds_c i);
        ds_in : forall i, Hom (ds_c i) ds;
        ds_id : forall i j, ds_pr i ∘ ds_in j == identity_matrix h ds_c ds_dec i j;
        ds_isprod : forall c, isweq (fun f : Hom c ds => fun i => ds_pr i ∘ f);
        ds_issum  : forall c, isweq (fun f : Hom ds c => fun i => f ∘ ds_in i)
      }.
  Definition makeDirectSum {C:precategory} (h:hasZeroObject C)
             {I} (dec : isdeceq I) (d:I -> ob C) 
             (B:Sum.type C d) (D:Product.type C d)
             (is: is_isomorphism (identity_map h dec B D)) : DirectSum h.
  Proof. intros. set (id := identity_map h dec B D).
    refine (make_DirectSum C h I dec d D
                           (fun i => Product.Proj D i)
                           (fun i => id ∘ Sum.In B i) _ _ _).
    { intros. exact (Matrix.from_matrix_entry_assoc D B (identity_matrix h d dec) i j). }
    { intros. exact (pr2 (Representation.Iso D c)). }
    { intros. 
      assert (b : (fun (f : Hom D c) (i : I) => (f ∘ id) ∘ Sum.In B i)
               == (fun (f : Hom D c) (i : I) => f ∘ (id ∘ Sum.In B i))).
      { apply funextfunax; intros f. apply funextsec; intros i. apply assoc. }
      destruct b.
      exact (twooutof3c (fun f => f ∘ id) 
                        (fun g i => g ∘ Sum.In B i)
                        (iso_comp_right_isweq (id,,is) c)
                        (pr2 (Representation.Iso B c))). }
  Defined.
End DirectSum.

Module Kernel.
  Import ZeroObject.
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
    forall x y:ob C, Hom x y ->
    set_to_type (zerocomp_set z f x) -> set_to_type (zerocomp_set z f y).
  Proof. intros ? ? ? ? ? ? ? p [k s]. exists (p ∘ k). rewrite assoc. rewrite s.
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
    Definition Proj {I} (X:I->setwithbinop) : forall i:I, Hom (make X) (X i).
      intros. exists (fun y => y i). intros a b. reflexivity. Defined.
    Definition Fun {I} (X:I->setwithbinop) (T:setwithbinop)
               (g: forall i, Hom T (X i))
               : Hom T (make X).
      intros. exists (fun t i => g i t).
      intros t u. apply funextsec; intro i. apply (pr2 (g i)). Defined.
    Definition Eqn {I} (X:I->setwithbinop) (T:setwithbinop) (g: forall i, Hom T (X i))
               : forall i, Proj X i ∘ Fun X T g == g i.
      intros. apply funEquality. reflexivity. Qed.
  End Product.
End Magma.

Module QuotientSet.
    Definition iscomprelfun2 {X Y Z} (RX:hrel X) (RY:hrel Y)
               (f:X->Y->Z) : Type
      := dirprod (forall x x', RX x x' -> forall y, f x y == f x' y)
                (forall y y', RY y y' -> forall x, f x y == f x y').
    Definition iscomprelrelfun2 {X Y Z} (RX:hrel X) (RY:hrel Y) (RZ:eqrel Z) 
               (f:X->Y->Z) : Type
      := dirprod (forall x x' y, RX x x' -> RZ (f x y) (f x' y))
                (forall x y y', RY y y' -> RZ (f x y) (f x y')).
    Lemma setquotuniv_equal { X : UU } ( R : hrel X ) ( Y : hSet ) 
          ( f f' : X -> Y ) (p : f == f')
          ( is : iscomprelfun R f ) ( is' : iscomprelfun R f' )
    : setquotuniv R Y f is == setquotuniv R Y f' is'.
    Proof. intros. destruct p. apply funextfunax; intro c.
           assert(ip : isaprop (iscomprelfun R f)). { 
             apply impred; intro x; apply impred; intro x'.
             apply impred; intro p. apply setproperty. }
           assert( q : is == is' ). { apply ip. }
	   destruct q. reflexivity. Qed.
    Definition setquotuniv2 {X Y} (RX:hrel X) (RY:hrel Y) 
               {Z:hSet} (f:X->Y->Z) (is:iscomprelfun2 RX RY f) :
      setquot RX -> setquot RY -> Z.
    Proof. intros ? ? ? ? ? ? ? x''.
           refine (setquotuniv RX (funset (setquot RY) Z) _ _ _).
           { simpl. intro x. apply (setquotuniv RY Z (f x)).
             intros y y' e. unfold iscomprelfun2 in is.
             apply (pr2 is). assumption. }
           { intros x x' e.
             assert( p : f x == f x' ). 
             { apply funextfunax; intro y. apply (pr1 is). assumption. }
           apply setquotuniv_equal. assumption. } assumption. Defined.
    Definition setquotfun2 {X Y Z} {RX:hrel X} {RY:hrel Y} {RZ:eqrel Z}
               (f:X->Y->Z) (is:iscomprelrelfun2 RX RY RZ f) :
      setquot RX -> setquot RY -> setquot RZ.
    Proof. intros ? ? ? ? ? ? ? ?.
           set (f' := fun x y => setquotpr RZ (f x y) : setquotinset RZ).
           apply (setquotuniv2 RX RY f'). split.
           { intros ? ? p ?. apply iscompsetquotpr. exact (pr1 is x x' y p). }
           { intros ? ? p ?. apply iscompsetquotpr. exact (pr2 is x y y' p). }
    Defined.
    Lemma setquotfun2_equal {X Y Z} (RX:eqrel X) (RY:eqrel Y) (RZ:eqrel Z)
               (f:X->Y->Z) (is:iscomprelrelfun2 RX RY RZ f)
               (x:X) (y:Y) :
      setquotfun2 f is (setquotpr RX x) (setquotpr RY y) ==
      setquotpr RZ (f x y).
    Proof. intros. reflexivity. (* it computes! *) Defined.
End QuotientSet.

Module Monoid.
  Require Import Foundations.hlevel2.algebra1b.
  Local Notation Hom := monoidfun (only parsing).
  Local Notation "x * y" := ( op x y ). 
  Local Notation "g ∘ f" := (monoidfuncomp f g) (at level 50, only parsing).
  Definition funEquality G H (p q : Hom G H) : pr1 p == pr1 q -> p == q.
    intros ? ? [p i] [q j] v. simpl in v. destruct v.
    destruct (pr1 (isapropismonoidfun p i j)). reflexivity. Qed.
  Definition unitproperty {G H} (p:Hom G H) : p (unel G) == unel H 
    := pr2 (pr2 p).
  Definition multproperty {G H} (p:Hom G H) (g g':G) : p(g * g') == p g * p g'
    := pr1 (pr2 p) g g'.
  Definition zero : monoid.
    exists Magma.zero. split. intros x y z. reflexivity.
    exists tt. split. intros []. reflexivity. intros []. reflexivity.
  Defined.
  Inductive word X : Type :=
    | word_unit : word X
    | word_gen : X -> word X 
    | word_op : word X -> word X -> word X.
  Arguments word_unit {X}.
  Arguments word_gen {X} x.
  Arguments word_op {X} v w.
  Record reln X := make_reln { lhs : word X; rhs : word X }.
  Arguments lhs {X} r.
  Arguments rhs {X} r.
  Arguments make_reln {X} _ _.
  Module Presentation.
    (** * monoids by generators and relations *)
    (** ** premonoids over X
           A pre-monoid over X modulo an adequate relation over R will be a
           monoid M equipped with a map X -> M that respects the relations R. *)
    Record MarkedPremonoid X := 
      make_preMonoid {
          elem :> Type;
          op0 : elem;
          op1 : X -> elem;
          op2 : elem -> elem -> elem }.
    Arguments elem {X} M : rename.
    Arguments op0 {X M} : rename.
    Arguments op1 {X M} x : rename.
    Arguments op2 {X M} v w : rename.
    Definition wordop X := make_preMonoid X (word X) word_unit word_gen word_op.
    Fixpoint evalword {X} (Y:MarkedPremonoid X) (w:word X) : elem Y.
      intros ? Y [|x|v w]. { exact op0. } { exact (op1 x). }
      { exact (op2 (evalword X Y v) (evalword X Y w)). } Defined.
    Definition MarkedPremonoid_to_hrel {X} (M:MarkedPremonoid X) (is:isaset (elem M)) : 
        hrel (word X) :=
      fun v w => (evalword M v == evalword M w) ,, is _ _.
    (** eta expansion principle for words *)
    Fixpoint reassemble {X I} (R:I->reln X) (v:wordop X) : evalword (wordop X) v == v.
    Proof. intros ? ? ? [|x|v w]. { reflexivity. } { reflexivity. }
           { exact (aptwice word_op (reassemble _ _ R v) (reassemble _ _ R w)). } Qed.
    (** ** adequate relations over R *)
    Record AdequateRelation {X I} (R:I->reln X) (r : hrel (word X)) := 
      make_AdequateRelation {
          base: forall i, r (lhs (R i)) (rhs (R i));
          reflex : forall w, r w w;
          symm : forall v w, r v w -> r w v;
          trans : forall u v w, r u v -> r v w -> r u w;
          left_compat : forall u v w, r v w -> r (word_op u v) (word_op u w);
          right_compat: forall u v w, r u v -> r (word_op u w) (word_op v w);
          left_unit : forall w, r (word_op word_unit w) w;
          right_unit : forall w, r (word_op w word_unit) w;
          assoc : forall u v w, r (word_op (word_op u v) w) (word_op u (word_op v w)) }.
    Arguments make_AdequateRelation {X I} R r _ _ _ _ _ _ _ _ _.
    Arguments base {X I R r} _ _.
    Definition adequacy_to_eqrel {X I} (R:I->reln X) (r : hrel (word X)) :
      AdequateRelation R r -> eqrel (word X).
    Proof. intros ? ? ? ? ra. exists r.
           abstract ( split; [ split; [ exact (trans R r ra) | exact (reflex R r ra) ] |
                               exact (symm R r ra)]). Defined.
    (** ** the smallest adequate relation over R 
           It is defined as the intersection of all the adequate relations.
           Later we'll have to deal with the "resizing" to resolve issues
           with universes. *)
    Definition smallestAdequateRelation0 {X I} (R:I->reln X) : hrel (word X).
      intros ? ? ? v w.
      exists (forall r: hrel (word X), AdequateRelation R r -> r v w).
      abstract (apply impred; intro r; apply impred; intros _; apply propproperty).
    Defined.
    Lemma adequacy {X I} (R:I->reln X) : 
      AdequateRelation R (smallestAdequateRelation0 R).
    Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _).
           { intros ? r ra. apply base. exact ra. }
           { intros ? r ra. apply (reflex R). exact ra. }
           { intros ? ? p r ra. apply (symm R). exact ra. exact (p r ra). }
           { exact (fun u v w p q r ra => trans R r ra u v w (p r ra) (q r ra)). }
           { intros ? ? ? p r ra. apply (left_compat R). exact ra. exact (p r ra). }
           { intros ? ? ? p r ra. apply (right_compat R). exact ra. exact (p r ra). }
           { intros ? r ra. apply (left_unit R). exact ra. }
           { intros ? r ra. apply (right_unit R). exact ra. }
           { exact (fun u v w r ra => assoc R r ra u v w). } Qed.
    Definition smallestAdequateRelation {X I} (R:I->reln X) : eqrel (word X).
      intros. exact (adequacy_to_eqrel R _ (adequacy R)). Defined.
    (** *** the underlying set of the monoid with generators X and relations R *)
    Definition universalMarkedPremonoid0 {X I} (R:I->reln X) : hSet := 
      setquotinset (smallestAdequateRelation R).
    Lemma op2_compatibility {X I} (R:I->reln X) : 
      QuotientSet.iscomprelrelfun2
        (smallestAdequateRelation R) (smallestAdequateRelation R) (smallestAdequateRelation R)
        word_op.    
    Proof. intros. split.
      { intros x x' y p r ra. exact (right_compat R r ra x x' y (p r ra)). }
      { intros x y y' p r ra. exact ( left_compat R r ra x y y' (p r ra)). } Qed.
    (** *** the multiplication on on it *)
    Definition univ_binop {X I} (R:I->reln X) : binop (universalMarkedPremonoid0 R).
      intros. refine (QuotientSet.setquotfun2 word_op _). apply op2_compatibility. Defined.
    Definition univ_setwithbinop {X I} (R:I->reln X) : setwithbinop
               := setwithbinoppair (universalMarkedPremonoid0 R) (univ_binop R).
    (** *** the universal premonoid *)
    Definition universalMarkedPremonoid {X I} (R:I->reln X) : MarkedPremonoid X.
      intros. refine (make_preMonoid X (universalMarkedPremonoid0 R) _ _ _).
      { exact (setquotpr _ word_unit). }
      { exact (fun x => setquotpr _ (word_gen x)). }
      { exact (univ_binop _). } Defined.
    (** *** identities for the universal premonoid *)
    Lemma is_left_unit_univ_binop {X I} (R:I->reln X) : 
      forall w : universalMarkedPremonoid0 R, ((univ_binop _) (setquotpr _ word_unit) w) == w.
    Proof. intros ? ? ? w'. assert (lift := issurjsetquotpr (smallestAdequateRelation R)).
      isaprop_goal ig. { apply setproperty. } 
      apply (unsquash (lift w') ig); intros [w i]; destruct i; simpl.
      exact (iscompsetquotpr (smallestAdequateRelation R) _ _ 
                             (fun r ra => left_unit R r ra w)). Qed.
    Lemma is_right_unit_univ_binop {X I} (R:I->reln X) : 
      forall w : universalMarkedPremonoid0 R, ((univ_binop _) w (setquotpr _ word_unit)) == w.
    Proof. intros ? ? ? w'. assert (lift := issurjsetquotpr (smallestAdequateRelation R)).
      isaprop_goal ig. { apply setproperty. } 
      apply (unsquash (lift w') ig); intros [w i]; destruct i; simpl.
      exact (iscompsetquotpr (smallestAdequateRelation R) _ _ 
                             (fun r ra => right_unit R r ra w)). Qed.
    Lemma isassoc_univ_binop {X I} (R:I->reln X) : isassoc(univ_binop R).
    Proof. intros. set (e := smallestAdequateRelation R). intros u' v' w'. 
           isaprop_goal ig. { apply setproperty. } assert (lift := issurjsetquotpr e).
 	   apply (unsquash (lift u') ig); intros [u i]; destruct i; simpl.
 	   apply (unsquash (lift v') ig); intros [v j]; destruct j; simpl.
 	   apply (unsquash (lift w') ig); intros [w k]; destruct k; simpl.
           exact (iscompsetquotpr e _ _ (fun r ra => assoc R r ra u v w)). Qed.
    Fixpoint reassemble_pr {X I} (R:I->reln X) (v:word X) : 
      evalword (universalMarkedPremonoid R) v == setquotpr _ v.
    Proof. intros ? ? ? [|x|v w]. { reflexivity. } { reflexivity. }
           { simpl. assert (p := ! reassemble_pr _ _ R v). destruct p.
                    assert (q := ! reassemble_pr _ _ R w). destruct q.
                    reflexivity. } Qed.
    Lemma pr_eval_compat {X I} (R:I->reln X) (w:word X) :
      setquotpr (smallestAdequateRelation R) (evalword (wordop X) w) 
      == evalword (universalMarkedPremonoid R) w.
    Proof. intros. destruct w as [|x|v w]. { reflexivity. } { reflexivity. } 
      { assert (p := !reassemble R (word_op v w)). destruct p. 
        exact (!reassemble_pr R (word_op v w)). } Qed.
    (** *** monoids over X modulo R *)
    Definition toMarkedPremonoid {X I} (R:I->reln X) (M:monoid) (el:X->M) : MarkedPremonoid X.
      intros. exact {| elem := M; op0 := unel _; op1 := el; op2 := op |}. Defined.
    Record MarkedMonoid {X I} (R:I->reln X) := 
      make_MarkedMonoid {
          m_base :> monoid;
          m_mark : X -> m_base;
          m_reln : forall i, evalword (toMarkedPremonoid R m_base m_mark) (lhs (R i)) ==
                             evalword (toMarkedPremonoid R m_base m_mark) (rhs (R i)) }.
    Arguments make_MarkedMonoid {X I} R _ _ _.
    Arguments m_base {X I R} _.
    Arguments m_mark {X I R} _ x.
    Definition toMarkedPremonoid' {X I} {R:I->reln X} (M:MarkedMonoid R) : MarkedPremonoid X :=
      toMarkedPremonoid R (m_base M) (m_mark M).
    Definition evalwordMM {X I} {R:I->reln X} (M:MarkedMonoid R) : word X -> M :=
      evalword (toMarkedPremonoid' M).
    Definition MarkedMonoid_to_hrel {X I} {R:I->reln X} (M:MarkedMonoid R) : hrel (word X) :=
      fun v w  => eqset (evalwordMM M v) (evalwordMM M w).
    Lemma monoid_adequacy {X I} (R:I->reln X) (M:MarkedMonoid R) :
      AdequateRelation R (MarkedMonoid_to_hrel M).
    Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _).
           { exact (fun i => m_reln R M i). } { reflexivity. }
           { intros ? ?. exact pathsinv0. } { intros ? ? ?. exact pathscomp0. }
           { intros ? ? ? p. simpl in p; simpl. 
             unfold evalwordMM,evalword in *. destruct p. reflexivity. }
           { intros ? ? ? p. simpl in p; simpl. 
             unfold evalwordMM,evalword in *. destruct p. reflexivity. }
           { intros. apply lunax. } { intros. apply runax. } { intros. apply assocax. } Qed.
    Record MarkedMonoidMap {X I} {R:I->reln X} (M N:MarkedMonoid R) :=
      make_MarkedMonoidMap {
          map_base :> Hom M N;
          map_mark : forall x, map_base (m_mark M x) == m_mark N x }.
    Arguments map_base {X I R M N} m.
    Arguments map_mark {X I R M N} m x.
    Lemma MarkedMonoidMapEquality {X I} {R:I->reln X} {M N:MarkedMonoid R}
          (f g:MarkedMonoidMap M N) : map_base f == map_base g -> f == g.
    Proof. intros ? ? ? ? ? ? ? j.
           destruct f as [f ft], g as [g gt]; simpl in j. destruct j.
           assert(k : ft == gt). { apply funextsec; intro x. apply setproperty. } destruct k. 
           reflexivity. Qed.
    Fixpoint MarkedMonoidMap_compat {X I} {R:I->reln X}
             {M N:MarkedMonoid R} (f:MarkedMonoidMap M N) (w:word X) :
      map_base f (evalwordMM M w) == evalwordMM N w.
    Proof. intros. destruct w as [|x|v w].
           { exact (unitproperty f). }
           { exact (map_mark f x). }
           { exact (multproperty f (evalwordMM M v) (evalwordMM M w)
                    @ aptwice (fun r s => r * s) 
                              (MarkedMonoidMap_compat _ _ _ _ _ f v) 
                              (MarkedMonoidMap_compat _ _ _ _ _ f w)). } Qed.
    Lemma MarkedMonoidMap_compat2 {X I} {R:I->reln X} 
             {M N:MarkedMonoid R} (f g:MarkedMonoidMap M N) (w:word X) :
      map_base f (evalwordMM M w) == map_base g (evalwordMM M w).
    Proof. intros. exact (MarkedMonoidMap_compat f w @ !MarkedMonoidMap_compat g w). Qed.
    (** *** the universal marked monoid over X modulo R *)
    Definition universalMarkedMonoid0 {X I} (R:I->reln X) : monoid.
      intros. 
      { exists (univ_setwithbinop R). split.
        { exact (isassoc_univ_binop R). }
        { exists (setquotpr _ word_unit). split. 
          { exact (is_left_unit_univ_binop R). }
          { exact (is_right_unit_univ_binop R). } } } Defined.
    Definition universalMarkedMonoid1 {X I} (R:I->reln X) : MarkedPremonoid X :=
      (toMarkedPremonoid R 
                    (universalMarkedMonoid0 R)
                    (fun x : X => setquotpr (smallestAdequateRelation R) (word_gen x))). 
    Lemma universalMarkedMonoid2 {X I} (R:I->reln X) (w:word X) : 
      setquotpr (smallestAdequateRelation R) w == evalword (universalMarkedMonoid1 R) w.
    Proof. intros.
      exact (! (ap (setquotpr (smallestAdequateRelation R)) (reassemble R w))
             @ pr_eval_compat R w). Qed.
    Definition universalMarkedMonoid3 {X I} (R:I->reln X) (i:I) : 
      evalword (universalMarkedMonoid1 R) (lhs (R i)) ==
      evalword (universalMarkedMonoid1 R) (rhs (R i)).
    Proof. intros.
           exact (! universalMarkedMonoid2 R (lhs (R i))
                  @ iscompsetquotpr (smallestAdequateRelation R) _ _ (fun r ra => base ra i)
                  @ universalMarkedMonoid2 R (rhs (R i))). Qed.
    Definition universalMarkedMonoid {X I} (R:I->reln X) : MarkedMonoid R :=
      make_MarkedMonoid R (universalMarkedMonoid0 R) 
                  (fun x => setquotpr (smallestAdequateRelation R) (word_gen x)) 
                  (universalMarkedMonoid3 R).
    Definition universality0 {X I} {R:I->reln X} (M:MarkedMonoid R) : 
      universalMarkedMonoid0 R -> M.
    Proof. intros ? ? ? ?. 
      apply (setquotuniv _ _ (evalwordMM M)).
      exact (fun _ _ r => r (MarkedMonoid_to_hrel M) (monoid_adequacy R M)).
    Defined.
    Definition universality1 {X I} (R:I->reln X) 
                             (M:MarkedMonoid R) (v w:universalMarkedMonoid0 R) :
      universality0 M (v * w) == universality0 M v * universality0 M w.
    Proof. intros.
           assert (lift := issurjsetquotpr (smallestAdequateRelation R)).
           isaprop_goal ig. { apply setproperty. }
           apply (unsquash (lift v) ig); intros [v' j]; destruct j; simpl.
           apply (unsquash (lift w) ig); intros [w' k]; destruct k; simpl.
           reflexivity. Qed.
    Definition universality2 {X I} {R:I->reln X} (M:MarkedMonoid R) : 
      monoidfun (universalMarkedMonoid R) M.
    Proof. intros. exists (universality0 M).
        split. { intros v w. apply universality1. } { reflexivity. } Defined.
    (** * universality of the universal marked monoid *)
    Local Arguments pr1monoidfun {X Y} f x.
    Theorem iscontrMarkedMonoidMap {X I} {R:I->reln X} (M:MarkedMonoid R) :
          iscontr (MarkedMonoidMap (universalMarkedMonoid R) M).
    Proof. intros. assert (g := make_MarkedMonoidMap X I R (universalMarkedMonoid R) M 
                                               (universality2 M) (fun x => idpath _)).
           exists g. intros f. apply MarkedMonoidMapEquality.
           apply funEquality. apply funextfunax; intro v.
           assert (lift := issurjsetquotpr (smallestAdequateRelation R)).
           isaprop_goal ig. { apply setproperty. }
           apply (unsquash (lift v) ig); intros [w j]; destruct j; simpl.
           exact ((ap f (universalMarkedMonoid2 R w)) 
                @ MarkedMonoidMap_compat2 f g w @ !(ap g (universalMarkedMonoid2 R w))).
           Qed.
  End Presentation.
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
    Definition Fun {I} (X:I->monoid) (T:monoid) (g: forall i, Hom T (X i))
               : Hom T (make X).
      intros.  exists (pr1 (Magma.Product.Fun X T g)). 
      exists (pr2 (Magma.Product.Fun X T g)). apply funextsec; intro i.
      exact (pr2 (pr2 (g i))). Defined.
    Definition Eqn {I} (X:I->monoid) (T:monoid) (g: forall i, Hom T (X i))
               : forall i, Proj X i ∘ Fun X T g == g i.
      intros. apply funEquality. reflexivity. Qed.
    Lemma issurjective_projection {I} (X:I->monoid) (i:I) :
      isdeceq I -> issurjective (Proj X i).
    (** Reminder: by [isasetifdeceq], I is a set, too.
        We should strengthen this lemma by assuming [isaset I] instead of
        [isdeceq I]. *)
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
  Module Presentation.
    (** * groups by generators and relations *)
  End Presentation.
  Module Product.
    Definition make {I} (X:I->gr) : gr.
      intros. set (Y := Monoid.Product.make X). exists (pr1monoid Y). exists (pr2 Y).
      exists (fun y i => grinv (X i) (y i)). split.
      - intro y. apply funextsec; intro i. apply grlinvax.
      - intro y. apply funextsec; intro i. apply grrinvax. Defined.    
    Definition Proj {I} (X:I->gr) (i:I) : Hom (make X) (X i).
      intros. exact (Monoid.Product.Proj X i). Defined.
    Definition Fun {I} (X:I->gr) (T:gr) (g: forall i, Hom T (X i)) : Hom T (make X).
      intros. exact (Monoid.Product.Fun X T g). Defined.
    Definition Eqn {I} (X:I->gr) (T:gr) (g: forall i, Hom T (X i))
               : forall i, Proj X i ∘ Fun X T g == g i.
      intros. apply Monoid.funEquality. reflexivity. Qed.
  End Product.
End Group.

(** * abelian groups *)
Module AbelianGroup.
  Require Import Foundations.hlevel2.algebra1b.
  Local Notation Hom := monoidfun.
  Local Notation "0" := (unel _).
  Local Notation "x + y" := ( op x y ). 
  Local Notation "g ∘ f" := (monoidfuncomp f g) (at level 50, only parsing).
  Definition commax (G:abgr) := pr2 (pr2 G).
  Definition zero : abgr.
    exists Group.zero. split. exact (pr2 Group.zero). intros x y. reflexivity.
  Defined.
  Require Import Foundations.hlevel2.hz.
  Definition Z : abgr := hzaddabgr.
  Definition unitproperty {G H:abgr} (p:Hom G H) : p (unel G) == unel H
    := pr2 (pr2 p).
  Definition addproperty {G H:abgr} (p:Hom G H) (g g':G) : p(g + g') == p g + p g'
    := pr1 (pr2 p) g g'.
  Module Presentation.
    (** * abelian groups by generators and relations *)
    (** This code is derived from the code in the module Monoid.Presentation.

        Reduce the duplication later, if possible. *)
    Inductive word X : Type :=
      | word_unit : word X
      | word_gen : X -> word X 
      | word_inv : word X -> word X 
      | word_op : word X -> word X -> word X.
    Arguments word_unit {X}.
    Arguments word_gen {X} x.
    Arguments word_inv {X} w.
    Arguments word_op {X} v w.
    Record reln X := make_reln { lhs : word X; rhs : word X }.
    Arguments lhs {X} r.
    Arguments rhs {X} r.
    Arguments make_reln {X} _ _.
    Record MarkedPreAbelianGroup X := 
      make_preAbelianGroup {
          elem :> Type;
          op0 : elem;
          op1 : X -> elem;
          op_inv : elem -> elem;
          op2 : elem -> elem -> elem }.
    Arguments elem {X} M : rename.
    Arguments op0 {X M} : rename.
    Arguments op1 {X M} x : rename.
    Arguments op_inv {X M} x : rename.
    Arguments op2 {X M} v w : rename.
    Definition wordop X := make_preAbelianGroup X (word X) word_unit word_gen word_inv word_op.
    Fixpoint evalword {X} (Y:MarkedPreAbelianGroup X) (w:word X) : elem Y.
      intros ? Y [|x|w|v w]. { exact op0. } { exact (op1 x). }
      { exact (op_inv (evalword X Y w)). }
      { exact (op2 (evalword X Y v) (evalword X Y w)). } Defined.
    Definition MarkedPreAbelianGroup_to_hrel {X} 
               (M:MarkedPreAbelianGroup X) (is:isaset (elem M)) : 
        hrel (word X) :=
      fun v w => (evalword M v == evalword M w) ,, is _ _.
    (** eta expansion principle for words *)
    Fixpoint reassemble {X I} (R:I->reln X) (v:wordop X) : evalword (wordop X) v == v.
    Proof. intros ? ? ? [|x|w|v w]. { reflexivity. } { reflexivity. }
           { exact (ap word_inv (reassemble _ _ R w)). }
           { exact (aptwice word_op (reassemble _ _ R v) (reassemble _ _ R w)). } Qed.
    (** ** adequate relations over R *)
    Record AdequateRelation {X I} (R:I->reln X) (r : hrel (word X)) := 
      make_AdequateRelation {
          base: forall i, r (lhs (R i)) (rhs (R i));
          reflex : forall w, r w w;
          symm : forall v w, r v w -> r w v;
          trans : forall u v w, r u v -> r v w -> r u w;
          left_compat : forall u v w, r v w -> r (word_op u v) (word_op u w);
          right_compat: forall u v w, r u v -> r (word_op u w) (word_op v w);
          left_unit : forall w, r (word_op word_unit w) w;
          right_unit : forall w, r (word_op w word_unit) w;
          assoc : forall u v w, r (word_op (word_op u v) w) (word_op u (word_op v w));
          inverse_compat : forall v w, r v w -> r (word_inv v) (word_inv w);
          left_inverse : forall w, r (word_op (word_inv w) w) word_unit;
          right_inverse: forall w, r (word_op w (word_inv w)) word_unit;
          comm : forall v w, r (word_op v w) (word_op w v)
        }.
    Arguments make_AdequateRelation {X I} R r _ _ _ _ _ _ _ _ _ _ _ _ _.
    Arguments base {X I R r} _ _.
    Definition adequacy_to_eqrel {X I} (R:I->reln X) (r : hrel (word X)) :
      AdequateRelation R r -> eqrel (word X).
    Proof. intros ? ? ? ? ra. exists r.
           abstract ( split; [ split; [ exact (trans R r ra) | exact (reflex R r ra) ] |
                               exact (symm R r ra)]). Defined.
    (** ** the smallest adequate relation over R 
           It is defined as the intersection of all the adequate relations.
           Later we'll have to deal with the "resizing" to resolve issues
           withe universes. *)
    Definition smallestAdequateRelation0 {X I} (R:I->reln X) : hrel (word X).
      intros ? ? ? v w.
      exists (forall r: hrel (word X), AdequateRelation R r -> r v w).
      abstract (apply impred; intro r; apply impred; intros _; apply propproperty).
    Defined.
    Lemma adequacy {X I} (R:I->reln X) : 
      AdequateRelation R (smallestAdequateRelation0 R).
    Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _ _ _ _ _).
           { intros ? r ra. apply base. exact ra. }
           { intros ? r ra. apply (reflex R). exact ra. }
           { intros ? ? p r ra. apply (symm R). exact ra. exact (p r ra). }
           { exact (fun u v w p q r ra => trans R r ra u v w (p r ra) (q r ra)). }
           { intros ? ? ? p r ra. apply (left_compat R). exact ra. exact (p r ra). }
           { intros ? ? ? p r ra. apply (right_compat R). exact ra. exact (p r ra). }
           { intros ? r ra. apply (left_unit R). exact ra. }
           { intros ? r ra. apply (right_unit R). exact ra. }
           { exact (fun u v w r ra => assoc R r ra u v w). } 
           { exact (fun v w p r ra => inverse_compat R r ra v w (p r ra)). }
           { exact (fun w r ra => left_inverse R r ra w). } 
           { exact (fun w r ra => right_inverse R r ra w). }
           { exact (fun v w r ra => comm R r ra v w). }
    Qed.
    Definition smallestAdequateRelation {X I} (R:I->reln X) : eqrel (word X).
      intros. exact (adequacy_to_eqrel R _ (adequacy R)). Defined.
    (** *** the underlying set of the abelian group with generators X and relations R *)
    Definition universalMarkedPreAbelianGroup0 {X I} (R:I->reln X) : hSet := 
      setquotinset (smallestAdequateRelation R).
    Lemma op_inv_compatibility {X I} (R:I->reln X) : 
      iscomprelrelfun (smallestAdequateRelation R) (smallestAdequateRelation R) word_inv.
    Proof. intros. intros v w p r ra. exact (inverse_compat R r ra v w (p r ra)). Qed.
    Lemma op2_compatibility {X I} (R:I->reln X) : 
      QuotientSet.iscomprelrelfun2
        (smallestAdequateRelation R) (smallestAdequateRelation R) (smallestAdequateRelation R)
        word_op.    
    Proof. intros. split.
      { intros x x' y p r ra. exact (right_compat R r ra x x' y (p r ra)). }
      { intros x y y' p r ra. exact ( left_compat R r ra x y y' (p r ra)). } Qed.
    (** *** the multiplication on on it *)
    Definition univ_inverse {X I} (R:I->reln X) : 
        universalMarkedPreAbelianGroup0 R -> universalMarkedPreAbelianGroup0 R.
      intros ? ? ?.  refine (setquotfun _ _ word_inv _). apply op_inv_compatibility. Defined.
    Definition univ_binop {X I} (R:I->reln X) : binop (universalMarkedPreAbelianGroup0 R).
      intros. refine (QuotientSet.setquotfun2 word_op _). apply op2_compatibility. Defined.
    Definition univ_setwithbinop {X I} (R:I->reln X) : setwithbinop
               := setwithbinoppair (universalMarkedPreAbelianGroup0 R) (univ_binop R).
    (** *** the universal pre-Abelian group *)
    Definition universalMarkedPreAbelianGroup {X I} (R:I->reln X) : MarkedPreAbelianGroup X.
      intros. refine (make_preAbelianGroup X (universalMarkedPreAbelianGroup0 R) _ _ _ _).
      { exact (setquotpr _ word_unit). }
      { exact (fun x => setquotpr _ (word_gen x)). }
      { exact (univ_inverse _). }
      { exact (univ_binop _). } Defined.
    (** *** identities for the universal preabelian group *)
    Lemma lift {X I} (R:I->reln X) : issurjective (setquotpr (smallestAdequateRelation R)).
    Proof. intros. exact (issurjsetquotpr (smallestAdequateRelation R)). Qed.
    Lemma is_left_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreAbelianGroup0 R) :
      ((univ_binop _) (setquotpr _ word_unit) w) == w.
    Proof. intros ? ? ? w'. isaprop_goal ig. { apply setproperty. } 
      apply (unsquash (lift R w') ig); intros [w i]; destruct i; simpl.
      exact (iscompsetquotpr (smallestAdequateRelation R) _ _ 
                             (fun r ra => left_unit R r ra w)). Qed.
    Lemma is_right_unit_univ_binop {X I} (R:I->reln X) (w:universalMarkedPreAbelianGroup0 R) :
      ((univ_binop _) w (setquotpr _ word_unit)) == w.
    Proof. intros ? ? ? w'. isaprop_goal ig. { apply setproperty. } 
      apply (unsquash (lift R w') ig); intros [w i]; destruct i; simpl.
      exact (iscompsetquotpr (smallestAdequateRelation R) _ _ 
                             (fun r ra => right_unit R r ra w)). Qed.
    Lemma isassoc_univ_binop {X I} (R:I->reln X) : isassoc(univ_binop R).
    Proof. intros. set (e := smallestAdequateRelation R). intros u' v' w'. 
           isaprop_goal ig. { apply setproperty. } 
 	   apply (unsquash (lift R u') ig); intros [u i]; destruct i; simpl.
 	   apply (unsquash (lift R v') ig); intros [v j]; destruct j; simpl.
 	   apply (unsquash (lift R w') ig); intros [w k]; destruct k; simpl.
           exact (iscompsetquotpr e _ _ (fun r ra => assoc R r ra u v w)). Qed.
    Lemma is_left_inverse_univ_binop {X I} (R:I->reln X) :
      forall w:setquot (smallestAdequateRelation0 R),
        univ_binop R (univ_inverse R w) w ==
        setquotpr (smallestAdequateRelation R) word_unit.
    Proof. intros. isaprop_goal ig. { apply setproperty. } 
      apply (unsquash (lift R w) ig); intros [v i]; destruct i; simpl.
      exact (iscompsetquotpr (smallestAdequateRelation R) _ _ 
                             (fun r ra => left_inverse R r ra v)). Qed.
    Lemma is_right_inverse_univ_binop {X I} (R:I->reln X) :
      forall w:setquot (smallestAdequateRelation0 R),
        univ_binop R w (univ_inverse R w) ==
        setquotpr (smallestAdequateRelation R) word_unit.
    Proof. intros. isaprop_goal ig. { apply setproperty. } 
      apply (unsquash (lift R w) ig); intros [v i]; destruct i; simpl.
      exact (iscompsetquotpr (smallestAdequateRelation R) _ _ 
                             (fun r ra => right_inverse R r ra v)). Qed.
    Lemma iscomm_univ_binop {X I} (R:I->reln X) : iscomm(univ_binop R).
    Proof. intros. set (e := smallestAdequateRelation R). intros v' w'. 
           isaprop_goal ig. { apply setproperty. }
 	   apply (unsquash (lift R v') ig); intros [v j]; destruct j; simpl.
 	   apply (unsquash (lift R w') ig); intros [w k]; destruct k; simpl.
           exact (iscompsetquotpr e _ _ (fun r ra => comm R r ra v w)). Qed.
    Fixpoint reassemble_pr {X I} (R:I->reln X) (v:word X) : 
      evalword (universalMarkedPreAbelianGroup R) v == setquotpr _ v.
    Proof. intros ? ? ? [|x|w|v w]. { reflexivity. } { reflexivity. }
           { simpl. assert (q := ! reassemble_pr _ _ R w). destruct q. reflexivity. }
           { simpl. assert (p := ! reassemble_pr _ _ R v). destruct p.
                    assert (q := ! reassemble_pr _ _ R w). destruct q.
                    reflexivity. } Qed.
    Lemma pr_eval_compat {X I} (R:I->reln X) (w:word X) :
      setquotpr (smallestAdequateRelation R) (evalword (wordop X) w) 
      == evalword (universalMarkedPreAbelianGroup R) w.
    Proof. intros. destruct w as [|x|w|v w]. { reflexivity. } { reflexivity. } 
      { exact (ap (setquotpr (smallestAdequateRelation R)) (reassemble R (word_inv w))
             @ !reassemble_pr R (word_inv w)). }
      { assert (p := !reassemble R (word_op v w)). destruct p. 
        exact (!reassemble_pr R (word_op v w)). } Qed.
    (** *** abelian groups over X modulo R *)
    Definition toMarkedPreAbelianGroup {X I} (R:I->reln X) (M:abgr) (el:X->M) : 
        MarkedPreAbelianGroup X.
      intros. exact {| elem := M; op0 := unel _; op1 := el; op_inv := grinv _; op2 := op |}.
    Defined.
    Record MarkedAbelianGroup {X I} (R:I->reln X) := 
      make_MarkedAbelianGroup {
          m_base :> abgr;
          m_mark : X -> m_base;
          m_reln : forall i, evalword (toMarkedPreAbelianGroup R m_base m_mark) (lhs (R i)) ==
                             evalword (toMarkedPreAbelianGroup R m_base m_mark) (rhs (R i)) }.
    Arguments make_MarkedAbelianGroup {X I} R _ _ _.
    Arguments m_base {X I R} _.
    Arguments m_mark {X I R} _ x.
    Definition toMarkedPreAbelianGroup' {X I} {R:I->reln X} (M:MarkedAbelianGroup R) : MarkedPreAbelianGroup X :=
      toMarkedPreAbelianGroup R (m_base M) (m_mark M).
    Definition evalwordMM {X I} {R:I->reln X} (M:MarkedAbelianGroup R) : word X -> M :=
      evalword (toMarkedPreAbelianGroup' M).
    Definition MarkedAbelianGroup_to_hrel {X I} {R:I->reln X} (M:MarkedAbelianGroup R) : hrel (word X) :=
      fun v w  => eqset (evalwordMM M v) (evalwordMM M w).
    Lemma abelian_group_adequacy {X I} (R:I->reln X) (M:MarkedAbelianGroup R) :
      AdequateRelation R (MarkedAbelianGroup_to_hrel M).
    Proof. intros. refine (make_AdequateRelation R _ _ _ _ _ _ _ _ _ _ _ _ _ _).
           { exact (fun i => m_reln R M i). } { reflexivity. }
           { intros ? ?. exact pathsinv0. } { intros ? ? ?. exact pathscomp0. }
           { intros ? ? ? p. simpl in p; simpl. 
             unfold evalwordMM,evalword in *. destruct p. reflexivity. }
           { intros ? ? ? p. simpl in p; simpl. 
             unfold evalwordMM,evalword in *. destruct p. reflexivity. }
           { intros. apply lunax. } { intros. apply runax. } { intros. apply assocax. } 
           { intros ? ? p. simpl in p; simpl.
             unfold evalwordMM,evalword in *. destruct p. reflexivity. }
           { intros. apply grlinvax. } { intros. apply grrinvax. } { intros. apply commax. }
    Qed.
    Record MarkedAbelianGroupMap {X I} {R:I->reln X} (M N:MarkedAbelianGroup R) :=
      make_MarkedAbelianGroupMap {
          map_base :> Hom M N;
          map_mark : forall x, map_base (m_mark M x) == m_mark N x }.
    Arguments map_base {X I R M N} m.
    Arguments map_mark {X I R M N} m x.
    Lemma MarkedAbelianGroupMapEquality {X I} {R:I->reln X} {M N:MarkedAbelianGroup R}
          (f g:MarkedAbelianGroupMap M N) : map_base f == map_base g -> f == g.
    Proof. intros ? ? ? ? ? ? ? j.
           destruct f as [f ft], g as [g gt]; simpl in j. destruct j.
           assert(k : ft == gt). { apply funextsec; intro x. apply setproperty. } destruct k. 
           reflexivity. Qed.
    Fixpoint MarkedAbelianGroupMap_compat {X I} {R:I->reln X}
             {M N:MarkedAbelianGroup R} (f:MarkedAbelianGroupMap M N) (w:word X) :
      map_base f (evalwordMM M w) == evalwordMM N w.
    Proof. intros. destruct w as [|x|w|v w].
           { exact (Monoid.unitproperty f). }
           { exact (map_mark f x). }
           { exact (monoidfuninvtoinv f (evalwordMM M w)
                  @ ap (grinv N) (MarkedAbelianGroupMap_compat _ _ _ _ _ f w)). }
           { exact (Monoid.multproperty f (evalwordMM M v) (evalwordMM M w)
                    @ aptwice (fun r s => r + s) 
                              (MarkedAbelianGroupMap_compat _ _ _ _ _ f v) 
                              (MarkedAbelianGroupMap_compat _ _ _ _ _ f w)). } Qed.
    Lemma MarkedAbelianGroupMap_compat2 {X I} {R:I->reln X} 
             {M N:MarkedAbelianGroup R} (f g:MarkedAbelianGroupMap M N) (w:word X) :
      map_base f (evalwordMM M w) == map_base g (evalwordMM M w).
    Proof. intros. 
           exact (MarkedAbelianGroupMap_compat f w @ !MarkedAbelianGroupMap_compat g w). Qed.
    (** *** the universal marked abelian group over X modulo R *)
    Definition universalMarkedAbelianGroup0 {X I} (R:I->reln X) : abgr.
      intros. 
      { exists (univ_setwithbinop R). split.
        { refine (_,,_).
          { split.
            { exact (isassoc_univ_binop R). }
            { exists (setquotpr _ word_unit). split. 
              { exact (is_left_unit_univ_binop R). }
              { exact (is_right_unit_univ_binop R). } } }
          { refine (_,,_).
            { exact (univ_inverse R). }
            { split.
              { exact (is_left_inverse_univ_binop R). }
              { exact (is_right_inverse_univ_binop R). } } } }
        { exact (iscomm_univ_binop R). } }
    Defined.
    Definition universalMarkedAbelianGroup1 {X I} (R:I->reln X) : MarkedPreAbelianGroup X :=
      (toMarkedPreAbelianGroup R 
                    (universalMarkedAbelianGroup0 R)
                    (fun x : X => setquotpr (smallestAdequateRelation R) (word_gen x))). 
    Lemma universalMarkedAbelianGroup2 {X I} (R:I->reln X) (w:word X) : 
      setquotpr (smallestAdequateRelation R) w == evalword (universalMarkedAbelianGroup1 R) w.
    Proof. intros.
      exact (! (ap (setquotpr (smallestAdequateRelation R)) (reassemble R w))
             @ pr_eval_compat R w). Qed.
    Definition universalMarkedAbelianGroup3 {X I} (R:I->reln X) (i:I) : 
      evalword (universalMarkedAbelianGroup1 R) (lhs (R i)) ==
      evalword (universalMarkedAbelianGroup1 R) (rhs (R i)).
    Proof. intros.
           exact (! universalMarkedAbelianGroup2 R (lhs (R i))
                  @ iscompsetquotpr (smallestAdequateRelation R) _ _ (fun r ra => base ra i)
                  @ universalMarkedAbelianGroup2 R (rhs (R i))). Qed.
    Definition universalMarkedAbelianGroup {X I} (R:I->reln X) : MarkedAbelianGroup R :=
      make_MarkedAbelianGroup R (universalMarkedAbelianGroup0 R) 
                  (fun x => setquotpr (smallestAdequateRelation R) (word_gen x)) 
                  (universalMarkedAbelianGroup3 R).
    Fixpoint agreement_on_gens0 {X I} {R:I->reln X} {M:abgr}
          (f g:Hom (universalMarkedAbelianGroup R) M)
          (p:forall i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) ==
                     g (setquotpr (smallestAdequateRelation R) (word_gen i)))
          (w:word X) :
            pr1 f (setquotpr (smallestAdequateRelation R) w) ==
            pr1 g (setquotpr (smallestAdequateRelation R) w).
    Proof. intros. destruct w as [|x|w|v w].
           { intermediate (unel M). exact (unitproperty f). exact (!unitproperty g). }
           { apply p. }
           (* compare duplication with the proof of MarkedAbelianGroupMap_compat *)
           { refine (monoidfuninvtoinv f (setquotpr (smallestAdequateRelation R) w)
               @ _ @ ! monoidfuninvtoinv g (setquotpr (smallestAdequateRelation R) w)).
             apply (ap (grinv M)). apply agreement_on_gens0. assumption. }
           { refine (
                 Monoid.multproperty f (setquotpr (smallestAdequateRelation R) v)
                     (setquotpr (smallestAdequateRelation R) w)
               @ _ @ !
                 Monoid.multproperty g (setquotpr (smallestAdequateRelation R) v)
                     (setquotpr (smallestAdequateRelation R) w)).
             apply (aptwice (fun r s => r + s)).
             { apply agreement_on_gens0. assumption. }
             { apply agreement_on_gens0. assumption. } } Qed.
    Lemma agreement_on_gens {X I} {R:I->reln X} {M:abgr}
          (f g:Hom (universalMarkedAbelianGroup R) M) :
          (forall i, f (setquotpr (smallestAdequateRelation R) (word_gen i)) ==
                     g (setquotpr (smallestAdequateRelation R) (word_gen i))) 
            -> f == g.
      intros ? ? ? ? ? ? p. apply Monoid.funEquality.
      apply funextfunax; intro t; simpl in t. 
      apply (surjectionisepitosets _ _ _ (issurjsetquotpr _)).
      { apply setproperty. } { apply agreement_on_gens0. assumption. } Qed.
    Definition universality0 {X I} {R:I->reln X} (M:MarkedAbelianGroup R) : 
      universalMarkedAbelianGroup0 R -> M.
    Proof. intros ? ? ? ?. 
      apply (setquotuniv _ _ (evalwordMM M)).
      exact (fun _ _ r => r (MarkedAbelianGroup_to_hrel M) (abelian_group_adequacy R M)).
    Defined.
    Definition universality1 {X I} (R:I->reln X) 
                             (M:MarkedAbelianGroup R) (v w:universalMarkedAbelianGroup0 R) :
      universality0 M (v + w) == universality0 M v + universality0 M w.
    Proof. intros. isaprop_goal ig. { apply setproperty. }
      apply (unsquash (lift R v) ig); intros [v' j]; destruct j; simpl.
      apply (unsquash (lift R w) ig); intros [w' k]; destruct k; simpl.
      reflexivity. Qed.
    Definition universality2 {X I} {R:I->reln X} (M:MarkedAbelianGroup R) : 
      monoidfun (universalMarkedAbelianGroup R) M.
    Proof. intros. exists (universality0 M).
        split. { intros v w. apply universality1. } { reflexivity. } Defined.
    (** * universality of the universal marked abelian group *)
    Local Arguments pr1monoidfun {X Y} f x.
    Theorem iscontrMarkedAbelianGroupMap {X I} {R:I->reln X} (M:MarkedAbelianGroup R) :
          iscontr (MarkedAbelianGroupMap (universalMarkedAbelianGroup R) M).
    Proof. intros. 
      assert (g := make_MarkedAbelianGroupMap X I R 
                             (universalMarkedAbelianGroup R) M 
                             (universality2 M) (fun x => idpath _)).
      exists g. intros f. apply MarkedAbelianGroupMapEquality.
      apply Monoid.funEquality. apply funextfunax; intro v.
      isaprop_goal ig. { apply setproperty. }
      apply (unsquash (lift R v) ig); intros [w j]; destruct j; simpl.
      exact ((ap f (universalMarkedAbelianGroup2 R w)) 
           @ MarkedAbelianGroupMap_compat2 f g w @ !(ap g (universalMarkedAbelianGroup2 R w))).
    Defined.
  End Presentation.
  Module Product.
    Definition make {I} (G:I->abgr) : abgr.
      intros. exists (pr1 (Group.Product.make G)).
      split. exact (pr2 (Group.Product.make G)).
      intros a b. apply funextsec; intro i. apply commax. Defined.
    Definition Proj {I} (G:I->abgr) (i:I) : Hom (make G) (G i).
      exact @Group.Product.Proj. Defined.
    Definition Map {I} (G:I->abgr) (T:abgr) (g: forall i, Hom T (G i)) :
        Hom T (make G).
      exact @Group.Product.Fun. Defined.
    Lemma Eqn {I} (G:I->abgr) (T:abgr) (g: forall i, Hom T (G i))
             : forall i, Proj G i ∘ Map G T g == g i.
      exact @Group.Product.Eqn. Qed.
    Definition UniqueMap {I} (G:I->abgr) (T:abgr) (h h' : Hom T (make G)) :
         (forall i, Proj G i ∘ h == Proj G i ∘ h') -> h == h'.
      intros ? ? ? ? ? e. apply Monoid.funEquality.
      apply funextfunax; intro t. apply funextsec; intro i.
      exact (apevalat t (ap pr1 (e i))). Qed.
  End Product.
  Module Sum.                   (* coproducts *)
    Import Presentation.
    Definition X {I} (G:I->abgr) := total2 G. (* the generators *)
    Inductive J {I} (G:I->abgr) : Type := (* index set for the relations *)
      | J_zero : I -> J G                 (* (i,0) ~ 0 *)
      | J_sum : total2 (fun i => dirprod (G i) (G i)) -> J G. (* (i,g)+(i,h) ~ (i,g+h) *)
    (* We could replace this with:
       Definition J {I} (G:I->abgr) := coprod I (total2 (fun i => dirprod (G i) (G i))).
       *)
    Definition R {I} (G:I->abgr) : J G -> reln (X G).
      intros ? ? [i|[i [g h]]].
      { exact (make_reln (word_gen (i,,0)) (word_unit)). }
      { exact (make_reln (word_gen (i,,g+h))
                         (word_op (word_gen (i,,g)) (word_gen (i,,h)))). } Defined.
    Definition make {I} (G:I->abgr) : abgr.
      intros. exact (Presentation.universalMarkedAbelianGroup (R G)). Defined.
    Definition Incl {I} (G:I->abgr) (i:I) : Hom (G i) (make G).
      intros. refine (_,,_).
      { intro g. apply setquotpr. apply word_gen. exact (i,,g). } { split.
        { intros g h. apply iscompsetquotpr. exact (base (adequacy _) (J_sum _ (i,,(g,,h)))). }
        { apply iscompsetquotpr. exact (base (adequacy _) (J_zero _ i)). } } Defined.
    Definition Map0 {I} {G:I->abgr} {T:abgr} (f: forall i, Hom (G i) T) :
        MarkedAbelianGroup (R G).
      intros. refine (make_MarkedAbelianGroup (R G) T _ _).
      { intros [i g]. exact (f i g). }
      { intros [i|[i [g h]]].
        { simpl. apply unitproperty. }
        { simpl. apply addproperty. } } Defined.
    Definition Map {I} (G:I->abgr) (T:abgr) (f: forall i, Hom (G i) T) :
        Hom (make G) T.
      intros. exact (the (iscontrMarkedAbelianGroupMap (Map0 f))). Defined.
    Lemma Eqn {I} (G:I->abgr) (T:abgr) (f: forall i, Hom (G i) T)
             : forall i, Map G T f ∘ Incl G i == f i.
      intros. apply Monoid.funEquality. reflexivity. Qed.
    Definition UniqueMap {I} (G:I->abgr) (T:abgr) (h h' : Hom (make G) T) :
         (forall i, h ∘ Incl G i == h' ∘ Incl G i) -> h == h'.
      intros ? ? ? ? ? e. apply (agreement_on_gens h h').
      { intros [i g]. exact (ap (evalat g) (ap pr1 (e i))). }
    Qed.
  End Sum.
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
    (** *** products in the category of abelian groups *)
    Module Product.
      Definition Object {I} (X:I->ob Precat) : ob Precat
        := AbelianGroup.Product.make X.
      Import Primitive.InitialObject.
      Definition make {I} (X:I->ob Precat) : Product.type Precat X.
        intros.
        set (Q := Elements.make_ob (HomFamily.precat Precat^op X) (Object X)
                                   (AbelianGroup.Product.Proj X)).
        exists Q. intros T. assert ( k' : Hom Q T ).
        { destruct T as [T_ob T_el].
          exists (AbelianGroup.Product.Map X T_ob T_el). simpl.
          apply funextsec. exact_op (AbelianGroup.Product.Eqn X T_ob T_el). }
        exists k'. intros k. apply Elements.mor_equality.
        exact (AbelianGroup.Product.UniqueMap X (pr1 T) (pr1 k) (pr1 k')
                 (fun i => (apevalsecat i (pr2 k)) @ ! (apevalsecat i (pr2 k')))). Defined.
    End Product.
    (** *** sums (coproducts) in the category of abelian groups *)
    Module Sum.
      Definition Object {I} (X:I->ob Precat) : ob Precat
        := AbelianGroup.Sum.make X.
      Import Primitive.InitialObject.
      Definition make {I} (X:I->ob Precat) : Sum.type Precat X.
        intros.
        set (Q := Elements.make_ob (HomFamily.precat Precat X) (Object X)
                                   (AbelianGroup.Sum.Incl X)).
        exists Q. intros T. assert ( k' : Hom Q T ).
        { destruct T as [T_ob T_el].
          exists (AbelianGroup.Sum.Map X T_ob T_el). simpl.
          apply funextsec. exact_op (AbelianGroup.Sum.Eqn X T_ob T_el). }
        exists k'. intros k. apply Elements.mor_equality.
        exact (AbelianGroup.Sum.UniqueMap X (pr1 T) (pr1 k) (pr1 k')
                 (fun i => (apevalsecat i (pr2 k)) @ ! (apevalsecat i (pr2 k')))). Defined.
    End Sum.
    Module DirectSum.
      (** *** finite direct sums in the category of abelian groups *)
      
    End DirectSum.
  End Category.
End AbelianGroup.

(**
  We are working toward definitions of "additive category" and "abelian
  category" as properties of a category, rather than as an added structure.
  That is the approach of Mac Lane in sections 18, 19, and 21 of :

  #<a href="http://projecteuclid.org/DPubS/Repository/1.0/Disseminate?view=body&id=pdf_1&handle=euclid.bams/1183515045">Duality for groups</a>#,
  Bull. Amer. Math. Soc., Volume 56, Number 6 (1950), 485-516.
 *)
