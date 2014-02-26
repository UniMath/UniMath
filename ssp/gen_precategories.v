(** **********************************************************

Benedikt Ahrens



************************************************************)


(** **********************************************************

Contents :  

  - generalization of precategories


************************************************************)

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of a generalized precategory *)

Definition precategory_ob_mor := total2 (
  fun ob : UU => ob -> ob -> UU).

Definition precategory_ob_mor_pair (ob : UU)(mor : ob -> ob -> UU) :
    precategory_ob_mor := tpair _ ob mor.

Definition ob (C : precategory_ob_mor) : Type := @pr1 _ _ C.
Coercion ob : precategory_ob_mor >-> Sortclass.

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
     dirprod (forall c : C, c --> c) (* identities *) 
             (forall a b c : C,
                 a --> b -> b --> c -> a --> c).

Definition precategory_data := total2 precategory_id_comp.

Definition precategory_data_pair (C : precategory_ob_mor)
    (id : forall c : C, c --> c)
    (comp: forall a b c : C,
         a --> b -> b --> c -> a --> c) : precategory_data :=
   tpair _ C (dirprodpair id comp).

Definition precategory_ob_mor_from_precategory_data (C : precategory_data) :
     precategory_ob_mor := pr1 C.
Coercion precategory_ob_mor_from_precategory_data : 
  precategory_data >-> precategory_ob_mor.

Definition identity { C : precategory_data } :
    forall c : C, c --> c := 
         pr1 (pr2 C).

Definition compose { C : precategory_data } 
  { a b c : C } : 
    a --> b -> b --> c -> a --> c := pr2 (pr2 C) a b c.

Local Notation "f ;; g" := (compose f g)(at level 50).


(** ** Axioms of a precategory *)
(** 
        - identity is left and right neutral for composition 
        - composition is associative
*)

Definition is_precategory (C : precategory_data) := 
   dirprod (dirprod (forall (a b : C) (f : a --> b),
                         identity a ;; f == f)
                     (forall (a b : C) (f : a --> b),
                         f ;; identity b == f))
            (forall (a b c d : C) 
                    (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) == (f ;; g) ;; h).

Definition precategory := total2 is_precategory.

Definition precategory_data_from_precategory (C : precategory) : 
       precategory_data := pr1 C.
Coercion precategory_data_from_precategory : precategory >-> precategory_data.

Definition id_left (C : precategory) : 
   forall (a b : C) (f : a --> b),
           identity a ;; f == f := pr1 (pr1 (pr2 C)).

Definition id_right (C : precategory) :
   forall (a b : C) (f : a --> b),
           f ;; identity b == f := pr2 (pr1 (pr2 C)).

Definition assoc (C : precategory) : 
   forall (a b c d : C) 
          (f : a --> b)(g : b --> c) (h : c --> d),
                     f ;; (g ;; h) == (f ;; g) ;; h := pr2 (pr2 C).

(** Any equality on objects a and b induces a morphism from a to b *)

Definition idtomor {C : precategory_data}
   (a b : C) (H : a == b) : a --> b.
Proof.
  destruct H.
  exact (identity a).
Defined.

Definition idtomor_inv {C : precategory}
    (a b : C) (H : a == b) : b --> a.
Proof.
  destruct H.
  exact (identity a).
Defined.


Lemma cancel_postcomposition (C : precategory_data) (a b c: C)
   (f f' : a --> b) (g : b --> c) : f == f' -> f ;; g == f' ;; g.
Proof.
  intro H.
  destruct H.
  apply idpath.
Defined.



(** * Equivalence in a generalized precategory *)

(** ** Definition of equivalences *)

Definition postcompose_with {C : precategory} {b c : ob C} (g : b --> c) : 
      forall {a}, a --> b -> a --> c :=
   fun a f =>  f ;; g.

Definition is_left_equivalence {C : precategory} {b c : ob C} (g : b --> c) :=
     forall a : ob C, isweq (postcompose_with g (a:=a)).

(** being a left equivalence is a proposition *)
Lemma isaprop_is_left_equivalence {C : precategory} {b c : ob C} (g : b --> c) :
   isaprop (is_left_equivalence g).
Proof.
  apply impred;
  intro t; apply isapropisweq.
Qed.

Definition left_equivalence {C : precategory} (b c : ob C) : UU :=
   total2 (fun g : b --> c => is_left_equivalence g).

Lemma identity_is_left_equivalence {C : precategory} (a : ob C) : 
     is_left_equivalence (identity a).
Proof.
  intro b.
  apply (gradth _ (fun x => x)).
  - intro g; apply id_right.
  - intro g; apply id_right.
Qed.

Definition identity_left_equivalence {C : precategory} (a : ob C) : 
   left_equivalence a a := tpair _ _ (identity_is_left_equivalence a).

Lemma postcompose_with_composition_ext {C : precategory} (b c d: ob C)
   (f : b --> c) (g : c --> d) :
   forall a (h : a --> b), postcompose_with (f ;; g) h == 
        postcompose_with g (postcompose_with f h).
Proof.
  intros a h; apply assoc.
Defined.

Lemma postcompose_with_composition {C : precategory} (b c d: ob C)
   (f : b --> c) (g : c --> d) :
   forall a, postcompose_with (f ;; g) (a:=a) == 
        fun x => postcompose_with g (postcompose_with f x).
Proof.
  intro a. apply funextfun.
  apply postcompose_with_composition_ext.
Defined.


Lemma is_left_identity_composition {C : precategory} (b c d: ob C)
   (f : b --> c) (g : c --> d) :
   is_left_equivalence f -> is_left_equivalence g -> 
        is_left_equivalence (f ;; g).
Proof.
  unfold is_left_equivalence; intros Hf Hg a.
  rewrite postcompose_with_composition.
  apply twooutof3c; auto.
Qed.
   
  
(** for producing the inverse, we seem to need that
 - a "natural transformation" alpha : F -> G : C -> UU
   which is pointwise an equiv, is a "natural iso".
 - a natural iso has an inverse
 - natural transformations are representable
*)


(** define the category UU *)

Definition UUcat_data : precategory_data.
  exists (tpair (fun x => x -> x -> UU) UU (fun A B : UU => A -> B)).
  split; simpl.
  intro c; exact (fun x => x).
  intros a b c f g ; exact (fun x => g (f x)).
Defined.

Lemma is_precategory_UUcat : is_precategory UUcat_data.
Proof.
  repeat split; simpl.
Qed.

Definition UUcat : precategory := tpair _ _ is_precategory_UUcat.
  

(** ** Functors *)

Definition functor_data (C C' : precategory_ob_mor) := total2 (
    fun F : ob C -> ob C' => 
             forall a b : ob C, a --> b -> F a --> F b).

Definition mkfunctor_data (C C' : precategory_ob_mor) 
    a b : functor_data C C' := tpair _ a b.

Definition functor_on_objects {C C' : precategory_ob_mor}
     (F : functor_data C C') :  ob C -> ob C' := pr1 F.
Coercion functor_on_objects : functor_data >-> Funclass.


Definition functor_on_morphisms {C C' : precategory_ob_mor} (F : functor_data C C') 
  { a b : ob C} :  a --> b -> F a --> F b := pr2 F a b.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).


Definition is_functor {C C' : precategory_data} (F : functor_data C C') :=
     dirprod (forall a : ob C, #F (identity a) == identity (F a))
             (forall a b c : ob C, forall f : a --> b, forall g : b --> c, 
                #F (f ;; g) == #F f ;; #F g).

(*
Lemma isaprop_is_functor (C C' : precategory_data) 
       (F : functor_data C C'): isaprop (is_functor F).
Proof.
  apply isofhleveldirprod.
  apply impred; intro a.
  apply (pr2 (_ --> _)).
  repeat (apply impred; intro).
  apply (pr2 (_ --> _)).
Qed.
*)

Definition functor (C C' : precategory) := total2 (
   fun F : functor_data C C' => is_functor F).


Definition functor_data_from_functor (C C': precategory)
     (F : functor C C') : functor_data C C' := pr1 F.
Coercion functor_data_from_functor : functor >-> functor_data.


Definition functor_id {C C' : precategory}(F : functor C C'):
       forall a : ob C, #F (identity a) == identity (F a) := pr1 (pr2 F).

Definition functor_comp {C C' : precategory}
      (F : functor C C'):
       forall a b c : ob C, forall f : a --> b,
                 forall g : b --> c, 
                #F (f ;; g) == #F f ;; #F g := pr2 (pr2 F).


(** * Natural transformations *)


(** ** Definition of natural transformations *)

Definition is_nat_trans {C C' : precategory_data}
  (F F' : functor_data C C')
  (t : forall x : ob C, F x -->  F' x) := 
  forall (x x' : ob C)(f : x --> x'),
    #F f ;; t x' == t x ;; #F' f.



Definition nat_trans {C C' : precategory_data}
  (F F' : functor_data C C') := total2 (
   fun t : forall x : ob C, F x -->  F' x => is_nat_trans F F' t).


Definition nat_trans_data (C C' : precategory_data)
 (F F' : functor_data C C')(a : nat_trans F F') :
   forall x : ob C, F x --> F' x := pr1 a.
Coercion nat_trans_data : nat_trans >-> Funclass.

Definition nat_trans_ax {C C' : precategory_data}
  (F F' : functor_data C C') (a : nat_trans F F') :
  forall (x x' : ob C)(f : x --> x'),
    #F f ;; a x' == a x ;; #F' f := pr2 a.

(** ** opposite category *)

Definition opp_precat_ob_mor (C : precategory_ob_mor) : precategory_ob_mor :=
   tpair (fun ob : UU => ob -> ob -> UU) (ob C) 
        (fun a b : ob C => b --> a  ).

Definition opp_precat_data (C : precategory_data) : precategory_data.
Proof.
  exists (opp_precat_ob_mor C).
  split.
  exact (fun c => identity c).
  simpl.
  intros a b c f g.
  exact (g ;; f).
Defined.

Hint Unfold identity.

Ltac unf := unfold identity, 
                   compose, 
                   precategory_morphisms;
                   simpl.

Lemma is_precat_opp_precat_data (C : precategory) : is_precategory (opp_precat_data C).
Proof.
  repeat split; simpl.
  intros. unf.
  apply id_right.
  intros; unf.
  apply id_left.
  intros; unf.
  rewrite assoc.
  apply idpath.
Qed.

Definition opp_precat (C : precategory) : precategory := 
  tpair _ (opp_precat_data C) (is_precat_opp_precat_data C).

Local Notation "C '^op'" := (opp_precat C) (at level 3).





