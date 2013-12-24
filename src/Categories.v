(* -*- coding: utf-8-unix -*- *)

(* Set Printing All. *)

(** * category theory 

  In this library we introduce the category theory needed for K-theory:

  - products, coproducts, direct sums, finite direct sums
  - additive categories, matrices
  - exact categories

  Using Qed, we make all proof irrelevant proofs opaque. *)

Require Import Foundations.hlevel2.hSet.
Require Import Foundations.hlevel2.stnfsets.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.
Require Import RezkCompletion.category_hset.
Require Import RezkCompletion.yoneda.
        Import pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Add LoadPath "." as Ktheory.
Require Import Ktheory.Utilities.
        Import Ktheory.Utilities.Notations.

Unset Automatic Introduction.

(** *** notation *)

Local Notation "b ← a" := (precategory_morphisms a b) (at level 50).
Local Notation "a → b" := (precategory_morphisms a b) (at level 50).
Local Notation "f ;; g" := (precategories.compose f g) (at level 50).
Local Notation "g ∘ f" := (precategories.compose f g) (at level 50).
Local Notation car := pr1 (only parsing).
Local Notation cadr := (fun x => pr1(pr2 x)).
Local Notation caddr := (fun x => pr1(pr2 (pr2 x))).
Local Notation cadddr := (fun x => pr1(pr2 (pr2 (pr2 x)))).
Local Notation cdr := pr2 (only parsing).
Local Notation cddr := (fun x => pr2(pr2 x)).
Local Notation cdddr := (fun x => pr2(pr2 (pr2 x))).
Local Notation cddddr := (fun x => pr2(pr2 (pr2 (pr2 x)))).
Notation "C '^op'" := (opp_precat C) (at level 3).
Notation SET := hset_precategory.

Definition precategory_pair (C:precategory_data) (i:is_precategory C)
  : precategory := tpair _ C i.

Definition category_pair (C:precategory) (i:is_category C)
 : category := tpair _ C i.

Definition objectToFunctor {C D:precategory} : ob [C,D] -> functor C D.
  intros ? ? F. exact F.
Defined.

Definition functorToObject {C D:precategory} : functor C D -> ob [C,D].
  intros ? ? F. exact F.
Defined.

(** *** make a precategory *)

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
  set (C := (precategory_data_pair
              (precategory_ob_mor_pair 
                 obj 
                 (fun i j:obj => hSetpair (mor i j) (imor i j))) identity compose)).
  assert (iC : is_precategory C).
    split. 
    split. apply right. apply left.
    apply associativity.
  set (D := precategory_pair C iC).
  exact D.
Defined.    

(** *** opposite category of opposite category *)

Lemma opp_opp_precat_ob_mor (C : precategory_ob_mor) : C == opp_precat_ob_mor (opp_precat_ob_mor C).
Proof.
  intro.
  unfold opp_precat_ob_mor.
  destruct C as [ob mor].  
  apply idpath.
Defined.

Lemma opp_opp_precat_ob_mor_compute (C : precategory_ob_mor) :
  idpath _ == maponpaths precategory_id_comp (opp_opp_precat_ob_mor C).
Proof. intros [ob mor]. apply idpath. Defined.

Lemma opp_opp_precat_data (C : precategory_data) 
   : C == opp_precat_data (opp_precat_data C).
Proof.
  intro.
  destruct C as [[ob mor] [id co]].
  apply idpath.
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
  destruct C as [data q].
  apply (pair_path (opp_opp_precat_data data)).
  apply isaprop_is_precategory.
Defined.

(** ** products *)

Module Products.

  (** *** terminal objects *)

  Definition isTerminalObject {C:precategory} (a:C) := forall (x:C), iscontr (a ← x).

  Lemma terminalObjectIsomorphy {C:precategory} (a b:C):isTerminalObject a -> isTerminalObject b -> iso a b.
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

  Lemma isaprop_isTerminalObject {C:precategory} (a:C):isaprop(isTerminalObject a).
  Proof. prop_logic. Qed.

  Definition isTerminalObjectProp {C:precategory} (a:C) := 
    hProppair (isTerminalObject a) (isaprop_isTerminalObject a):hProp.

  Definition TerminalObject (C:precategory) := total2 (fun a:C => isTerminalObject a).
  Definition terminalObject {C:precategory} (z:TerminalObject C) := car z.
  Definition terminalProperty {C:precategory} (z:TerminalObject C) := cdr z.

  Definition is_category_category (C:category) := cdr _ : is_category C.

  Lemma isaprop_TerminalObject (C:category) : isaprop (TerminalObject C).
  Proof.
    intros.
    apply invproofirrelevance.
    intros a b.
    apply (total2_paths 
             (isotoid _ (is_category_category _) 
                      (terminalObjectIsomorphy _ _      
                         (terminalProperty a)
                         (terminalProperty b)))).
    apply isaprop_isTerminalObject.
  Qed.

  Definition squashTerminalObject (C:precategory) := squash (TerminalObject C).

  Definition squashTerminalObjectProp (C:precategory) := 
    hProppair (squashTerminalObject C) (isaprop_squash _).

  (** *** binary products *)

  Definition isBinaryProduct {C:precategory} {a b p:C} (f:p → a) (g:p → b) :=
    forall p' (f':p' → a) (g':p' → b),
      iscontr ( total2 ( fun h => dirprod (f ∘ h == f') (g ∘ h == g'))).

  Lemma isaprop_isBinaryProduct {C:precategory} {a b p:C} (f:p → a) (g:p → b):isaprop(isBinaryProduct f g).
  Proof. prop_logic. Qed.

  Definition isBinaryProductProp {C:precategory} {a b p:C} (f:p → a) (g:p → b) :=
    hProppair (isBinaryProduct f g) (isaprop_isBinaryProduct _ _).

  Definition BinaryProduct {C:precategory} (a b:C) := 
    total2 (fun p => 
    total2 (fun f:p → a => 
    total2 (fun g:p → b => 
                    isBinaryProduct f g))).

  Definition squashBinaryProducts (C:precategory) := forall a b:C, squash (BinaryProduct a b).

  Lemma isaprop_squashBinaryProducts (C:precategory):isaprop (squashBinaryProducts C).
  Proof. prop_logic. Qed.

  Definition squashBinaryProductsProp (C:precategory) := 
    hProppair (squashBinaryProducts C) (isaprop_squashBinaryProducts _).

End Products.

(** ** coproducts *)

Module Coproducts.

  (** This module is obtained from the module Products by copying and then reversing arrows from → to ←,
   reversing composition from ∘ to ;;, and changing various words. *)

  (** *** initial objects *)

  Definition isInitialObject {C:precategory} (a:C) := forall (x:C), iscontr (a → x).

  Lemma initialObjectIsomorphy {C:precategory} (a b:C):isInitialObject a -> isInitialObject b -> iso a b.
  Proof.
    intros ? ? ?.
    intros map_from_a_to map_from_b_to. 
    exists (the (map_from_a_to b)). 
    exists (the (map_from_b_to a)).
    split. 
      intermediate (the (map_from_a_to a)). 
        apply uniqueness.
      apply uniqueness'. 
    intermediate (the (map_from_b_to b)). 
      apply uniqueness.
    apply uniqueness'.
  Defined.

  Lemma isaprop_isInitialObject {C:precategory} (a:C):isaprop(isInitialObject a).
  Proof. prop_logic. Qed.

  Definition isInitialObjectProp {C:precategory} (a:C) := 
    hProppair (isInitialObject a) (isaprop_isInitialObject a):hProp.

  Definition InitialObject (C:precategory) := total2 (fun a:C => isInitialObject a).

  Definition squashInitialObject (C:precategory) := squash (InitialObject C).

  Definition squashInitialObjectProp (C:precategory) := 
    hProppair (squashInitialObject C) (isaprop_squash _).

  (** *** binary coproducts *)

  Definition isBinaryCoproduct {C:precategory} {a b p:C} (f:p ← a) (g:p ← b) :=
    forall p' (f':p' ← a) (g':p' ← b),
      iscontr ( total2 ( fun h => dirprod (f ;; h == f') (g ;; h == g'))).

  Lemma isaprop_isBinaryCoproduct {C:precategory} {a b p:C} (f:p ← a) (g:p ← b):isaprop(isBinaryCoproduct f g).
  Proof. prop_logic. Qed.

  Definition isBinaryCoproductProp {C:precategory} {a b p:C} (f:p ← a) (g:p ← b) :=
    hProppair (isBinaryCoproduct f g) (isaprop_isBinaryCoproduct _ _).

  Definition BinaryCoproduct {C:precategory} (a b:C) := 
    total2 (fun p => 
    total2 (fun f:p ← a => 
    total2 (fun g:p ← b => 
          isBinaryCoproduct f g))).

  Definition squashBinaryCoproducts (C:precategory) := forall a b:C, squash (BinaryCoproduct a b).

  Lemma isaprop_squashBinaryCoproducts (C:precategory):isaprop (squashBinaryCoproducts C).
  Proof. prop_logic. Qed.

  Definition squashBinaryCoproductsProp (C:precategory) := 
    hProppair (squashBinaryCoproducts C) (isaprop_squashBinaryCoproducts _).

End Coproducts.

Module StandardCategories.

  Definition compose' { C:precategory_data } { a b c:C }
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
    apply idpath.
  Defined.

  (** *** the path groupoid *)

  Lemma path_assoc (X:UU) (a b c d:X) 
          (f : a == b) (g : b == c) (h : c == d)
        : f @ (g @ h) == (f @ g) @ h.
  Proof. intros. destruct f. apply idpath. Defined.

  Lemma path_assoc_opaque (X:UU) (a b c d:X) 
          (f : a == b) (g : b == c) (h : c == d)
        : f @ (g @ h) == (f @ g) @ h.
  Proof. intros. destruct f. apply idpath. Qed.

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
    assert (h : idtomor _ _ ~ funcomp idtoiso t). intro p. destruct p. apply idpath.
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
      intros. apply idpath.
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
    assert (k : idfun (a == b) ~ idtomor a b). intro p. destruct p. apply idpath.
    apply (isweqhomot _ _ k).
    apply idisweq.
  Qed.

  Lemma is_category_path_pregropoid (X:UU) (i:isofhlevel 3 X) :
    is_category (path_pregroupoid X i).
  Proof.
    intros.
    apply is_category_groupoid, is_groupoid_path_pregroupoid.
  Qed.

  Definition path_groupoid (X:UU) : isofhlevel 3 X -> category.
  Proof.
    intros ? iobj.
    apply (category_pair (path_pregroupoid X iobj)), is_category_path_pregropoid.
  Defined.

  (** *** the discrete category on n objects *)

  Definition cat_n (n:nat):category.
    intro.
    apply (path_groupoid (stn n)).
    apply hlevelntosn.
    apply isasetstn.
  Defined.

  Definition is_identity {C:precategory} {a b:C} (f:a→b) :=
    total2 ( fun e:a == b => transportf (fun x => x→b) e f == identity b ).

  Lemma isaprop_is_identity {C:precategory} {a b:C} (f:a→b) :
    isaset (ob C) -> isaprop (is_identity f).
  Proof.
    intros ? ? ? ? is.
    apply invproofirrelevance.
    intros [p q] [p' q'].
    assert (e : p == p'). apply is. destruct e.
    assert (d : q == q'). apply isaset_hSet. destruct d.
    trivial.
  Qed.

  Definition is_discrete_precategory (C:precategory) := 
    dirprod
    (isaset (ob C))
    (forall (a b:C) (f:a→b), is_identity f).

  Lemma isaprop_is_discrete_precategory (C:precategory) : 
    isaprop (is_discrete_precategory C).
  Proof.
    intro.
    apply isofhleveltotal2. apply isapropisaset.
    intro is.
    repeat (apply impred; intros).
    exact (isaprop_is_identity _ is).
  Qed.

  Lemma is_discrete_cat_n (n:nat) : is_discrete_precategory (cat_n n).
  Proof.
    intro.
    split.
      simpl.
      apply isasetstn.
    intros ? ? f.
    exists f.
    destruct f.
    apply idpath.
  Qed.

End StandardCategories.

(** ** limits via cones *)

Module ConeLimits.

  Require Import RezkCompletion.limits.cones.

  Import Products.
  Import StandardCategories.

  Definition finite_product_structure (C:precategory) :=
    forall (n:nat) F, TerminalObject (@CONE (cat_n n) C F).

  Definition finite_coproduct_structure (C:precategory) :=
    forall (n:nat) F, TerminalObject (@CONE (cat_n n) (C^op) F).

End ConeLimits.

(** ** fibered categories *)

Module FiberedCategories.

  (* Make a fibered category over C and produce a terminal object in it
     from a representation.  Use that to get uniqueness of representations. *)


  Module DebugMe.
    Parameter C : precategory.
    Parameter F : functor C^op SET.
    Parameter F': [C^op,SET].
    (* F and F' should be of the same type, but they don't appear to be *)
    Definition obj  := total2 (fun c => pr1hSet (F c)).
    Definition obj' := total2 (fun c => pr1hSet ((pr1 F') c)).
    (* I should be able to eliminate all projections above, because of coercions *)

    Definition obj'' := total2 (fun c => pr1hSet ((objectToFunctor F') c)).
  End DebugMe.

End FiberedCategories.

(** ** representable functors *)

Module RepresentableFunctors.

  Definition Representation {C} (F:[C^op, SET])
    := total2 (fun c => iso (yoneda _ c) F).
  Definition representingObject {C} {F:[C^op, SET]} (i:Representation F) 
    := car i.
  Definition representingIso {C} {F:[C^op, SET]} (i:Representation F)
    := cdr i.
  Definition representingElement {C} {F:[C^op, SET]} (i:Representation F)
    := yoneda_map_1 _ _ _ (representingIso i).
  Definition isRepresentatable {C} (F:[C^op, SET])
    := squash (Representation F).

  (** *** the Grothendieck construction *)

  Definition precategoryOfElements {C} (F:[C, SET]) : precategory.
    intros.
    destruct F as [[F aF] [iFid iFcomp]].
    simpl in iFid, iFcomp.
    set (obj := total2 (fun c : C => pr1hSet (F c))).
    set (compat := fun a b:obj => 
                     fun f : car a → car b => (aF _ _ f) (cdr a) == cdr b ).
    set (mor := fun a b:obj => total2 (compat a b)).
    unfold compat in mor.
    assert (imor : forall i j:obj, isaset (mor i j)).
      intros. apply (isofhleveltotal2 2). 
        apply setproperty.
      intros f.  apply (isofhlevelsnprop 1). apply isaset_hSet.
    set (id_compat 
         := (fun a => @ap _ _ (evalat (cdr a)) _ (idfun _) (iFid (car a)))
         :  forall a, compat a a (identity (car a))).
    set (ident := fun a => tpair _ (identity (pr1 _)) (id_compat _)
                           : mor a a).
    assert (compose_compat : 
         forall (i j k:obj) (f:mor i j) (g:mor j k), compat i k (car g ∘ car f)).
      intros [c x] j [e z] [f f'] [g g'].
      simpl in f, g, f', g'. destruct f', g'.
      exact (ap (evalat x) (iFcomp _ _ _ f g)).
    set (compo :=
           fun (i j k:obj) (f:mor i j) (g:mor j k)
               => tpair (compat i k) (pr1 g ∘ pr1 f) (compose_compat _ _ _ f g)
                 : mor i k).
    assert (right : forall i j:obj, forall f:mor i j, compo _ _ _ (ident _) f == f).
      intros [c x] [d y] [f f'].
      simpl in f, f'. destruct f'.
      assert (p : f ∘ identity _ == f). apply id_left.
      apply (@pair_path _ (fun g => aF _ _ g _ == aF _ _ f _) _ _ _ _ p).
      apply isaset_hSet.
    assert (left : forall i j:obj, forall f:mor i j, compo _ _ _ f (ident _) == f).
      intros [c x] [d y] [f f'].
      simpl in f, f'. destruct f'.
      assert (p : identity _ ∘ f == f). apply id_right.
      apply (@pair_path _ (fun g => aF _ _ g _ == aF _ _ f _) _ _ _ _ p).
      apply isaset_hSet.
    assert (assoc : forall (a b c d:obj) (f:mor a b) (g:mor b c) (h:mor c d),
        compo _ _ _ f (compo _ _ _ g h) == compo _ _ _ (compo _ _ _ f g) h).
      intros ? ? ? ? [f f'] [g g'] [h h'].
      assert (p : (h ∘ g) ∘ f == h ∘ (g ∘ f)). apply assoc.
      apply (pair_path p). apply isaset_hSet.
    exact (makePrecategory obj mor imor ident compo right left assoc).
  Defined.

End RepresentableFunctors.

(** ** direct sums *)

Module DirectSums.

  Import Coproducts Products.

  Definition ZeroObject (C:precategory) := total2 ( fun 
               zero_object : C => dirprod (
                             isInitialObject zero_object) (
                             isTerminalObject zero_object) ).
  Definition zero_object {C:precategory} (z:ZeroObject C) := car  z.
  Definition map_from    {C:precategory} (z:ZeroObject C) := cadr z.
  Definition map_to      {C:precategory} (z:ZeroObject C) := cddr z.
  Coercion zero_object : ZeroObject >-> ob.

  Lemma initMapUniqueness {C:precategory} (a:ZeroObject C) (b:C) (f:a→b) : f == the (map_from a b).
  Proof. intros. exact (uniqueness (map_from a b) f). Qed.

  Lemma initMapUniqueness2 {C:precategory} (a:ZeroObject C) (b:C) (f g:a→b) : f == g.
  Proof.
   intros.
   intermediate (the (map_from a b)).
   apply initMapUniqueness.
   apply pathsinv0.
   apply initMapUniqueness.
  Qed.

  Definition hasZeroObject (C:precategory) := squash (ZeroObject C).

  Lemma zeroObjectIsomorphy {C:precategory} (a b:ZeroObject C) : iso a b.
  Proof.
    intros.
    exact (initialObjectIsomorphy a b (map_from a) (map_from b)).
  Defined.

  Definition zeroMap' {C:precategory} (a b:C) (o:ZeroObject C) := the (map_from o b) ∘ the (map_to o a) : a → b.

  Lemma path_right_composition {C:precategory} : forall (a b c:C) (g:a→b) (f f':b→c), f == f' -> f ∘ g == f' ∘ g.
  Proof. intros ? ? ? ? ? ? ? []. apply idpath. Qed.

  Lemma path_left_composition {C:precategory} : forall (a b c:C) (f:b→c) (g g':a→b), g == g' -> f ∘ g == f ∘ g'.
  Proof. intros ? ? ? ? ? ? ? []. apply idpath. Qed.

  Lemma zeroMapUniqueness {C:precategory} (x y:ZeroObject C) : forall a b:C, zeroMap' a b x == zeroMap' a b y.
  Proof.
    intros.
    set(i := the (map_to x a)).
    set(h := the (map_from x y)).
    set(q := the (map_from y b)).
    intermediate (q ∘ (h ∘ i)). 
      intermediate ((q ∘ h) ∘ i). 
        apply path_right_composition.
        apply uniqueness'.
      apply assoc. 
    apply path_left_composition.
    apply uniqueness.
  Qed.

  Lemma zeroMap {C:precategory} (a b:C): hasZeroObject C  ->  a → b.
  Proof.
    intros ? ? ?.
    apply (squash_to_set (zeroMap' a b)).
    apply isaset_hSet.    
    intros. apply zeroMapUniqueness.
  Defined.

  Lemma zeroMap'_left_composition {C:precategory} (z:ZeroObject C) : forall (a b c:C) (f:b→c), f ∘ zeroMap' a b z == zeroMap' a c z. 
  Proof.
   intros. unfold zeroMap'.
   intermediate ((f ∘ the (map_from z b)) ∘ the (map_to z a)).
     apply pathsinv0. apply assoc.
   apply path_right_composition.
   apply initMapUniqueness.
  Qed.

  Lemma zeroMap_left_composition {C:precategory} (a b c:C) (f:b→c) (h:hasZeroObject C) : f ∘ zeroMap a b h == zeroMap a c h. 
  Proof.
    intros ? ? ? ? ?.
    apply (@factor_dep_through_squash (ZeroObject C)). intro. apply isaset_hSet.
    intro z.
    assert( g : forall (b:C), zeroMap' a b z == zeroMap a b (squash_element z) ). trivial.
    destruct (g b).
    destruct (g c).
    apply zeroMap'_left_composition.
  Qed.

  (* the following definition is not right yet *)
  Definition isBinarySum {C:precategory} {a b s : C} (p : s → a) (q : s → b) (i : a → s) (j : b → s) :=
    dirprod (isBinaryProduct p q) (isBinaryCoproduct i j).
  
  Lemma isaprop_isBinarySum {C:precategory} {a b s : C} (p : s → a) (q : s → b) (i : a → s) (j : b → s) :
    isaprop (isBinarySum p q i j).
  Proof. prop_logic. Qed.

  Definition BinarySum {C:precategory} (a b : C) := 
                    total2 (fun 
      s          => total2 (fun 
      p : s → a  => total2 (fun  
      q : s → b  => total2 (fun 
      i : a → s  => total2 (fun  
      j : b → s  => 
          isBinarySum p q i j ))))).

  Definition squashBinarySums (C:precategory) :=
    forall a b : C, squash (BinarySum a b).

(**
  We are working toward definitions of "additive category" and "abelian
  category" as properties of a category, rather than as an added structure.
  That is the approach of Mac Lane in sections 18, 19, and 21 of :

  #<a href="http://projecteuclid.org/DPubS/Repository/1.0/Disseminate?view=body&id=pdf_1&handle=euclid.bams/1183515045">Duality for groups</a>#,
  Bull. Amer. Math. Soc., Volume 56, Number 6 (1950), 485-516.
 *)

End DirectSums.

