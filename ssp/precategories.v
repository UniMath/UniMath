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


(** * Setcategories: Precategories whose objects form a set *)

Definition setcategory := total2 (
   fun C : precategory => isaset (ob C)).

Definition precategory_from_setcategory (C : setcategory) : precategory := pr1 C.
Coercion precategory_from_setcategory : setcategory >-> precategory.

Definition setcategory_objects_set (C : setcategory) : hSet :=
    hSetpair (ob C) (pr2 C).

Lemma setcategory_eq_morphism_pi (C : setcategory) (a b : ob C)
      (e e': a == b) : idtomor _ _ e == idtomor _ _ e'.
Proof.
  assert (h : e == e').
  apply uip. apply (pr2 C).
  apply (maponpaths (idtomor _ _ ) h).
Qed.

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

(** ** Functors preserve isomorphisms *)


Lemma is_inverse_functor_image (C C' : precategory) (F : functor C C')
    (a b : C) (f : iso a b):
   is_inverse_in_precat (#F f) (#F (inv_from_iso f)).
Proof.
  simpl; split; simpl.
  rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  apply functor_id.
  
  rewrite <- functor_comp.
  rewrite (iso_after_iso_inv _ _ _ f).
  apply functor_id.
Qed.


Lemma functor_on_iso_is_iso (C C' : precategory) (F : functor C C')
    (a b : ob C)(f : iso a b) : is_isomorphism (#F f).
Proof.
  exists (#F (inv_from_iso f)). 
  simpl; apply is_inverse_functor_image.
Defined.


Definition functor_on_iso (C C' : precategory) (F : functor C C')
    (a b : ob C)(f : iso a b) : iso (F a) (F b).
Proof.
  exists (#F f).
  apply functor_on_iso_is_iso.
Defined.
 
Lemma functor_on_iso_inv (C C' : precategory) (F : functor C C')
    (a b : ob C) (f : iso a b) : 
   functor_on_iso _ _ F _ _ (iso_inv_from_iso f) == 
       iso_inv_from_iso (functor_on_iso _ _ F _ _ f).
Proof.
  apply eq_iso.
  simpl.
  apply idpath.
Defined.
  
(** ** Functors preserve inverses *)

Lemma functor_on_inv_from_iso (C C' : precategory) (F : functor C C')
    (a b : ob C)(f : iso a b) :
      #F (inv_from_iso f) == inv_from_iso (functor_on_iso _ _ F _ _ f) .
Proof.
  apply idpath.
Qed. 


(** ** Fully faithful functors *)

Definition fully_faithful {C D : precategory} (F : functor C D) := 
  forall a b : ob C, 
    isweq (functor_on_morphisms F (a:=a) (b:=b)).

Lemma isaprop_fully_faithful (C D : precategory) (F : functor C D) :
   isaprop (fully_faithful F).
Proof.
  apply impred; intro a.
  apply impred; intro b.
  apply isapropisweq.
Qed.

Definition weq_from_fully_faithful {C D : precategory}{F : functor C D}
      (FF : fully_faithful F) (a b : ob C) : 
   weq (a --> b) (F a --> F b).
Proof.
  exists (functor_on_morphisms F (a:=a) (b:=b)).
  exact (FF a b).
Defined.


Definition fully_faithful_inv_hom {C D : precategory}{F : functor C D} 
      (FF : fully_faithful F) (a b : ob C) :
      F a --> F b -> a --> b :=
 invweq (weq_from_fully_faithful FF a b).

Local Notation "FF ^-1" := (fully_faithful_inv_hom FF _ _ ) (at level 20).

Lemma fully_faithful_inv_identity (C D : precategory) (F : functor C D)
      (FF : fully_faithful F) (a : ob C) : 
         FF^-1 (identity (F a)) == identity _.
Proof.
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful FF a a)).
  unfold fully_faithful_inv_hom.
  set (HFaa:=homotweqinvweq (weq_from_fully_faithful FF a a)(identity _ )).
  simpl in *. 
  rewrite HFaa.
  rewrite functor_id; apply idpath.
Qed.


Lemma fully_faithful_inv_comp (C D : precategory) (F : functor C D)
      (FF : fully_faithful F) (a b c : ob C) 
      (f : F a --> F b) (g : F b --> F c) : 
        FF^-1 (f ;; g) == FF^-1 f ;; FF^-1 g.
Proof.
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful FF a c)).
  set (HFFac := homotweqinvweq (weq_from_fully_faithful FF a c)
                 (f ;; g)).
  unfold fully_faithful_inv_hom.
  simpl in *.
  rewrite HFFac; clear HFFac.
  rewrite functor_comp.
  set (HFFab := homotweqinvweq (weq_from_fully_faithful FF a b) f).
  set (HFFbc := homotweqinvweq (weq_from_fully_faithful FF b c) g).
  simpl in *.
  rewrite HFFab; clear HFFab.
  rewrite HFFbc; clear HFFbc.
  apply idpath.
Qed.



(** *** Fully faithful functors reflect isos *)

Lemma inv_of_ff_inv_is_inv (C D : precategory) (F : functor C D)
   (FF : fully_faithful F) (a b : C) (f : iso (F a) (F b)) :
  is_inverse_in_precat ((FF ^-1) f) ((FF ^-1) (inv_from_iso f)).
Proof.
  unfold fully_faithful_inv_hom; simpl.
  split.
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful FF a a)).
  set (HFFab := homotweqinvweq (weq_from_fully_faithful FF a b)).
  set (HFFba := homotweqinvweq (weq_from_fully_faithful FF b a)).
  simpl in *.
  rewrite functor_comp.
  rewrite HFFab; clear HFFab.
  rewrite HFFba; clear HFFba.
  rewrite functor_id.
  apply iso_inv_after_iso.
  
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful FF b b)).
  set (HFFab := homotweqinvweq (weq_from_fully_faithful FF a b)).
  set (HFFba := homotweqinvweq (weq_from_fully_faithful FF b a)).
  simpl in *.
  rewrite functor_comp.
  rewrite HFFab.
  rewrite HFFba.
  rewrite functor_id.
  apply iso_after_iso_inv.
Qed.


Lemma fully_faithful_reflects_iso_proof (C D : precategory)(F : functor C D) 
        (FF : fully_faithful F)
    (a b : ob C) (f : iso (F a) (F b)) : 
     is_isomorphism (FF^-1 f).
Proof.
  exists (FF^-1 (inv_from_iso f)).
  simpl;
  apply inv_of_ff_inv_is_inv.
Defined.

Definition  iso_from_fully_faithful_reflection {C D : precategory}{F : functor C D} 
        (HF : fully_faithful F)
    (a b : ob C) (f : iso (F a) (F b)) : 
      iso a b.
Proof.
  exists (fully_faithful_inv_hom HF a b f).
  apply fully_faithful_reflects_iso_proof.
Defined.

Lemma functor_on_iso_iso_from_fully_faithful_reflection (C D : precategory)
      (F : functor C D) (HF : fully_faithful F) (a b : ob C)
   (f : iso (F a) (F b)) :
      functor_on_iso _ _  F a b
        (iso_from_fully_faithful_reflection HF a b f) == f.
Proof.
  apply eq_iso. 
  simpl;
  apply (homotweqinvweq (weq_from_fully_faithful HF a b)).
Qed.



(** ** Essentially surjective functors *)

Definition essentially_surjective {C D : precategory} (F : functor C D) :=
  forall b, ishinh (total2 (fun a => iso (F a) b)).
   
(** ** Faithful functors *)

Definition faithful {C D : precategory} (F : functor C D) := 
  forall a b : ob C, forall f g : a --> b,
       #F f == #F g -> f == g.

Lemma isaprop_faithful (C D : precategory) (F : functor C D) : 
   isaprop (faithful F).
Proof.
  repeat (apply impred; intro).
  apply (pr2 (_ --> _)).
Qed.

(** ** Full functors *)


Definition full {C D : precategory} (F : functor C D) :=
   forall a b (g : F a --> F b), ishinh (total2 (fun f : a --> b => #F f == g)).



(** ** Fully faithful is the same as full and faithful *)

Definition full_and_faithful {C D : precategory} (F : functor C D) :=
   dirprod (full F) (faithful F).



Lemma fully_faithful_implies_full_and_faithful (C D : precategory) (F : functor C D) :
   fully_faithful F -> full_and_faithful F.
Proof.
  intro H.
  split; simpl.
  unfold full. 
  intros a b f.
  apply hinhpr.
  exists (fully_faithful_inv_hom H _ _ f).
  set (HFFaa := homotweqinvweq (weq_from_fully_faithful H a b)).
  simpl in HFFaa.
  apply HFFaa.
  
  unfold faithful.
  intros a b f g Heq.
  apply (equal_transport_along_weq _ _ (weq_from_fully_faithful H a b)).
  simpl. assumption.
Qed.

Lemma full_and_faithful_implies_fully_faithful (C D : precategory) (F : functor C D) :
   full_and_faithful F -> fully_faithful F.
Proof. 
  intros [Hfull Hfaith].
  intros a b g.
  unfold full in Hfull.
  set (Hfull_f :=  Hfull a b g).
  assert (H : isaprop (iscontr (hfiber #F g))).
     apply isapropiscontr.
  apply (Hfull_f (hProppair (iscontr (hfiber #F g)) H)).
  simpl. intro X. exists X.
  unfold hfiber.
  intro t.
  unfold faithful in Hfaith.
  assert (HX : pr1 t == pr1 X).
  apply Hfaith.
  rewrite (pr2 t). 
  set (H':= pr2 X).
  simpl in H'.
  rewrite H'. apply idpath.
  simpl in *.
  apply (total2_paths HX).
  apply proofirrelevance.
  apply (pr2 (F a --> F b)).
Qed.
 
Lemma isaprop_full_and_faithful (C D : precategory) (F : functor C D) :
   isaprop (full_and_faithful F).
Proof.
  apply isofhleveldirprod.
  apply impred; intro.
  apply impred; intro.
  apply impred; intro.
  simpl. repeat (apply impred; intro).
  apply isapropishinh.
  apply isaprop_faithful.
Qed.
  
  
Definition weq_fully_faithful_full_and_faithful (C D : precategory) (F : functor C D) :
   weq (fully_faithful F) (full_and_faithful F) :=
  weqimplimpl (fully_faithful_implies_full_and_faithful _ _ F)
              (full_and_faithful_implies_fully_faithful _ _ F)
              (isaprop_fully_faithful _ _ F)
              (isaprop_full_and_faithful _ _ F).

(** ** Image on objects of a functor  *)
(** is used later to define the full image subcategory of a category [D] 
       defined by a functor [F : C -> D] *)

Definition is_in_img_functor {C D : precategory} (F : functor C D) 
      (d : ob D) :=
  ishinh (
  total2 (fun c : ob C => iso (F c) d)).

Definition sub_img_functor {C D : precategory}(F : functor C D) :
    hsubtypes (ob D) := 
       fun d : ob D => is_in_img_functor F d.



(** ** Composition of Functors, Identity Functors *)

(** *** Composition *)
Lemma functor_composite_ob_mor {C C' C'' : precategory}
       (F : functor C C') (F' : functor C' C'') :
 is_functor  
  (tpair (fun F : ob C -> ob C'' => 
             forall a b : ob C, a --> b -> F a --> F b) 
    (fun a => F' (F a))
               (fun (a b : ob C) f => #F' (#F f))).
Proof.
  split; simpl.
  intro a.
  repeat rewrite functor_id.
  apply idpath.
  
  intros.
  repeat rewrite functor_comp.
  apply idpath.
Qed.

Definition functor_composite (C C' C'' : precategory)
       (F : functor C C') (F' : functor C' C'') :
  functor C C'' := tpair _ _ (functor_composite_ob_mor F F').

(** *** Identity functor *)

Lemma functor_identity_ob_mor (C : precategory) :
 is_functor  
  (tpair (fun F : ob C -> ob C => 
             forall a b : ob C, a --> b -> F a --> F b) 
    (fun a => a)
               (fun (a b : ob C) f => f)).
Proof.
  split; simpl.
  intros; apply idpath.
  intros; apply idpath.
Qed.

Definition functor_identity (C : precategory) :
     functor C  C.
Proof.
  exists (tpair (fun F : ob C -> ob C => 
             forall a b : ob C, a --> b -> F a --> F b) 
    (fun a => a)
               (fun (a b : ob C) f => f)).
  apply  (functor_identity_ob_mor C).
Defined.
   


(** * Natural transformations *)


(** ** Definition of natural transformations *)

Definition is_nat_trans {C C' : precategory_data}
  (F F' : functor_data C C')
  (t : forall x : ob C, F x -->  F' x) := 
  forall (x x' : ob C)(f : x --> x'),
    #F f ;; t x' == t x ;; #F' f.


Lemma isaprop_is_nat_trans (C C' : precategory_data)
  (F F' : functor_data C C') (t : forall x : ob C, F x -->  F' x):
  isaprop (is_nat_trans F F' t).
Proof.
  repeat (apply impred; intro).
  apply (pr2 (_ --> _)).
Qed.


Definition nat_trans {C C' : precategory_data}
  (F F' : functor_data C C') := total2 (
   fun t : forall x : ob C, F x -->  F' x => is_nat_trans F F' t).

Lemma isaset_nat_trans {C C' : precategory_data}
  (F F' : functor_data C C') : isaset (nat_trans F F').
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply impred.
  intro t. apply (pr2 (_ --> _)).
  intro x. 
  apply isasetaprop.
  apply isaprop_is_nat_trans.
Qed.

Definition nat_trans_data (C C' : precategory_data)
 (F F' : functor_data C C')(a : nat_trans F F') :
   forall x : ob C, F x --> F' x := pr1 a.
Coercion nat_trans_data : nat_trans >-> Funclass.

Definition nat_trans_ax {C C' : precategory_data}
  (F F' : functor_data C C') (a : nat_trans F F') :
  forall (x x' : ob C)(f : x --> x'),
    #F f ;; a x' == a x ;; #F' f := pr2 a.

(** Equality between two natural transformations *)

Lemma nat_trans_eq {C C' : precategory_data}
  (F F' : functor_data C C')(a a' : nat_trans F F'):
  (forall x, a x == a' x) -> a == a'.
Proof.
  intro H.
  assert (H' : pr1 a == pr1 a').
  apply funextsec.
  assumption.
  apply (total2_paths H').
  apply proofirrelevance.
  apply isaprop_is_nat_trans.
Qed.

Definition nat_trans_eq_pointwise (C C' : precategory_data)
   (F F' : functor_data C C') (a a' : nat_trans F F'):
      a == a' -> forall x, a x == a' x.
Proof.
  intro h.
  apply toforallpaths.
  apply maponpaths.
  assumption.
Qed.


(** ** Functor category [[C, D]] *)

Definition functor_precategory_ob_mor (C C' : precategory): 
  precategory_ob_mor := precategory_ob_mor_pair 
   (functor C C') (fun F F' : functor C C' =>
                              hSetpair (nat_trans F F') 
                                       (isaset_nat_trans F F')).

(** *** Identity natural transformation *)

Lemma is_nat_trans_id {C C' : precategory}
  (F : functor_data C C') : is_nat_trans F F
     (fun c : ob C => identity (F c)).
Proof.
  intros ? ? ? .
  rewrite id_left.
  rewrite id_right.
  apply idpath.
Qed.

Definition nat_trans_id {C C' : precategory}
  (F : functor_data C C') : nat_trans F F :=
    tpair _ _ (is_nat_trans_id F).

(** *** Composition of natural transformations *)

Lemma is_nat_trans_comp {C C' : precategory}
  {F G H : functor_data C C'}
  (a : nat_trans F G)
  (b : nat_trans G H): is_nat_trans F H
     (fun x : ob C => a x ;; b x).
Proof.
  intros ? ? ? .
  rewrite assoc.
  rewrite nat_trans_ax.
  rewrite <- assoc.
  rewrite nat_trans_ax.
  apply assoc.
Qed.


Definition nat_trans_comp {C C' : precategory}
  (F G H: functor_data C C') 
  (a : nat_trans F G)
  (b : nat_trans G H): nat_trans F H :=
    tpair _ _ (is_nat_trans_comp a b).


(** *** The data of the functor precategory *)

Definition functor_precategory_data (C C' : precategory): precategory_data.
Proof.
  apply ( precategory_data_pair 
        (functor_precategory_ob_mor C C')).
  intro a. simpl.
  apply (nat_trans_id (pr1 a)).
  intros a b c f g.
  apply (nat_trans_comp _ _ _ f g).
Defined.

(** *** Above data forms a precategory *)

Lemma is_precategory_functor_precategory_data (C C' : precategory) :
   is_precategory (functor_precategory_data C C').
Proof.
  repeat split; simpl; intros.
  unfold identity.
  simpl.
  apply nat_trans_eq.
  intro x; simpl.
  apply id_left.
  
  apply nat_trans_eq.
  intro x; simpl.
  apply id_right.
  
  apply nat_trans_eq.
  intro x; simpl.
  apply assoc.
Qed.

Definition functor_precategory (C C' : precategory): precategory := 
  tpair _ _ (is_precategory_functor_precategory_data C C').

Notation "[ C , D ]" := (functor_precategory C D).

Lemma nat_trans_comp_pointwise (C C' : precategory)
  (F G H : ob [C, C']) (A : F --> G) (A' : G --> H) 
   (B : F --> H) : A ;; A' == B -> 
        forall a, pr1 A a ;; pr1 A' a == pr1 B a.
Proof.
  intros H' a.
  pathvia (pr1 (A ;; A') a).
  apply idpath.
  destruct H'.
  apply idpath.
Defined.
  
  

(** Characterizing isomorphisms in the functor category *)

Lemma is_nat_trans_inv_from_pointwise_inv (C D : precategory)
  (F G : ob [C,D]) (A : F --> G) 
  (H : forall a : ob C, is_isomorphism (pr1 A a)) :
  is_nat_trans _ _ 
     (fun a : ob C => inv_from_iso (tpair _ _ (H a))).
Proof.
  unfold is_nat_trans.
  intros x x' f.
  apply pathsinv0.
  apply iso_inv_on_right.
  rewrite assoc.
  apply iso_inv_on_left.
  set (HA:= pr2 A).
  simpl in *.
  unfold is_nat_trans in HA.
  rewrite HA.
  apply idpath.
Qed.

Definition nat_trans_inv_from_pointwise_inv (C D : precategory)
  (F G : ob [C,D]) (A : F --> G) 
  (H : forall a : ob C, is_isomorphism (pr1 A a)) :
    G --> F := tpair _ _ (is_nat_trans_inv_from_pointwise_inv _ _ _ _ _ H).


Lemma is_inverse_nat_trans_inv_from_pointwise_inv (C C' : precategory)
    (F G : [C, C']) (A : F --> G)
   (H : forall a : C, is_isomorphism (pr1 A a)) : 
  is_inverse_in_precat A (nat_trans_inv_from_pointwise_inv C C' F G A H).
Proof.
  simpl; split; simpl.
  apply nat_trans_eq.
  intro x; simpl.
  apply (pr2 (H _)).
  apply nat_trans_eq.
  intro x; simpl.
  apply (pr2 (pr2 (H _))).
Qed.  


Lemma functor_iso_if_pointwise_iso (C C' : precategory)
 (F G : ob [C, C']) (A : F --> G) : 
   (forall a : ob C, is_isomorphism (pr1 A a)) ->  
           is_isomorphism A .
Proof.
  intro H.
  exists (nat_trans_inv_from_pointwise_inv _ _ _ _ _ H).
  simpl; apply is_inverse_nat_trans_inv_from_pointwise_inv.
Defined.

Definition functor_iso_from_pointwise_iso (C C' : precategory)
 (F G : ob [C, C']) (A : F --> G) 
   (H : forall a : ob C, is_isomorphism (pr1 A a)) : 
     iso F G := 
 tpair _ _ (functor_iso_if_pointwise_iso _ _ _ _ _  H).


Lemma is_functor_iso_pointwise_if_iso (C C' : precategory)
 (F G : ob [C, C']) (A : F --> G) : 
  is_isomorphism A -> 
       forall a : ob C, is_isomorphism (pr1 A a).  
Proof.
  intros H a.
  simpl in *.
  set (R := pr1 H).
  simpl in *.
  exists (R a).
  unfold is_inverse_in_precat in *; simpl; split.
  set (H1' := nat_trans_eq_pointwise _ _ _ _ _ _ (pr1 (pr2 H))).
  simpl in H1'.
  apply H1'.
  apply (nat_trans_eq_pointwise _ _ _ _ _ _ (pr2 (pr2 H))).
Defined.


Definition functor_iso_pointwise_if_iso (C C' : precategory)
 (F G : ob [C, C']) (A : F --> G) 
  (H : is_isomorphism A) : 
     forall a : ob C, 
       iso (pr1 F a) (pr1 G a) := 
  fun a => tpair _ _ (is_functor_iso_pointwise_if_iso C C' F G A H a).
 

Definition pr1_pr1_functor_eq_from_functor_iso (C D : precategory)
    (H : is_category D) (F G : ob [C , D]) :
   iso F G -> pr1 (pr1 F) == pr1 (pr1 G).
Proof.
  intro A.
  apply funextsec.
  intro t.
  apply isotoid.
  assumption.
  apply (functor_iso_pointwise_if_iso _ _ _ _ A).
  apply (pr2 A).
Defined.




Lemma transport_of_functor_map_is_pointwise (C D : precategory) 
      (F0 G0 : ob C -> ob D)
    (F1 : forall a b : ob C, a --> b -> F0 a --> F0 b)
   (gamma : F0  == G0 ) 
    (a b : ob C) (f : a --> b) :
transportf (fun x : ob C -> ob D => 
            forall a0 b0 : ob  C, a0 --> b0 -> x a0 --> x b0)
           gamma  F1 a b f == 
transportf (fun TT : ob D => G0 a --> TT)
  (toforallpaths (fun _ : ob C => D) F0 G0 gamma b)
  (transportf (fun SS : ob D => SS --> F0 b)
     (toforallpaths (fun _ : ob C => D) F0 G0 gamma a) (F1 a b f)).
Proof.
  induction gamma.
  apply idpath.
Defined.


Lemma toforallpaths_funextsec : forall (T : UU) (P : T -> UU) (f g : forall t : T, P t)
          (h : forall t : T, f t == g t), 
            toforallpaths _  _ _ (funextsec _ _ _ h) == h.
Proof.
  intros T P f g h.
  Opaque weqtoforallpaths. 
  exact ((homotweqinvweq (weqtoforallpaths _ f g)) h : (pr1weq _ _ (tpair _ _ _) _) == _).
Qed.

Transparent weqtoforallpaths.

Definition pr1_functor_eq_from_functor_iso (C D : precategory)
    (H : is_category D) (F G : ob [C , D]) :
   iso F G -> pr1 F == pr1 G.
Proof.
  intro A.
  apply (total2_paths (pr1_pr1_functor_eq_from_functor_iso C D H F G A)).
  unfold pr1_pr1_functor_eq_from_functor_iso.
  apply funextsec; intro a.
  apply funextsec; intro b.
  apply funextsec; intro f.
  rewrite transport_of_functor_map_is_pointwise.
  rewrite toforallpaths_funextsec.  
  pathvia ((inv_from_iso
        (idtoiso
           (isotoid D H
              (functor_iso_pointwise_if_iso C D F G A (pr2 A) a)));;
      pr2 (pr1 F) a b f);;
     idtoiso
       (isotoid D H
          (functor_iso_pointwise_if_iso C D F G A (pr2 A) b))).
    set (H':= double_transport_idtoiso D _ _ _ _  
         (isotoid D H (functor_iso_pointwise_if_iso C D F G A (pr2 A) a))
         (isotoid D H (functor_iso_pointwise_if_iso C D F G A (pr2 A) b))
          (pr2 (pr1 F) a b f)).
      unfold double_transport in H'. 
      apply H'; clear H'.
  rewrite idtoiso_isotoid.
  rewrite idtoiso_isotoid.
  destruct A as [A Aiso].
  simpl in *.
  pathvia 
    (inv_from_iso (functor_iso_pointwise_if_iso C D F G A Aiso a) ;;
       (A a ;; #G f)).
  rewrite <- assoc.
  apply maponpaths.
  apply (nat_trans_ax _ _ A).
  rewrite assoc.

  unfold functor_iso_pointwise_if_iso.
  unfold inv_from_iso.
  simpl in *.

  destruct Aiso as [A' AH].
  simpl in *.
  destruct AH as [A1 A2].
  rewrite (nat_trans_comp_pointwise _ _ _ _ _ _ _ _ A2).
  simpl.
  rewrite id_left.
  apply idpath.
Defined.

Definition functor_eq_from_functor_iso {C D : precategory}
    (H : is_category D) (F G : ob [C , D]) 
    (H' : iso F G) : F == G.
Proof.
  apply (functor_eq _ _ F G).
  apply pr1_functor_eq_from_functor_iso;
  assumption.
Defined.


Lemma idtoiso_compute_pointwise (C D : precategory) (F G : ob [C, D])
     (p : F == G) (a : ob C) :
  functor_iso_pointwise_if_iso C D F G (idtoiso p) (pr2 (idtoiso p)) a ==
idtoiso
  (toforallpaths (fun _ : ob C => D) (pr1 (pr1 F)) (pr1 (pr1 G))
     (base_paths (pr1 F) (pr1 G) (base_paths F G p)) a).
Proof.
  induction p.
  apply eq_iso. apply idpath.
Qed.


Lemma functor_eq_from_functor_iso_idtoiso (C D : precategory)
    (H : is_category D)
    (F G : ob [C, D]) (p : F == G) :
  functor_eq_from_functor_iso H F G (idtoiso p) == p.
Proof.
  simpl; apply functor_eq_eq_from_functor_ob_eq.
  unfold functor_eq_from_functor_iso.
  unfold functor_eq.
  rewrite base_total_path.
  unfold pr1_functor_eq_from_functor_iso.
  rewrite base_total_path.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  apply (equal_transport_along_weq _ _   (weqtoforallpaths _ _ _ )).
  simpl.
  rewrite toforallpaths_funextsec.
  apply funextsec; intro a. 
  rewrite idtoiso_compute_pointwise.
  apply isotoid_idtoiso.
Qed.

Lemma idtoiso_functor_eq_from_functor_iso (C D : precategory)
    (H : is_category D)
    (F G : ob [C, D]) (gamma : iso F G) :
        idtoiso (functor_eq_from_functor_iso H F G gamma) == gamma.
Proof.
  apply eq_iso.
  simpl; apply nat_trans_eq; intro a.
  assert (H':= idtoiso_compute_pointwise C D F G (functor_eq_from_functor_iso H F G gamma) a).
  simpl in *.
  pathvia (pr1
       (idtoiso
          (toforallpaths (fun _ : ob C => D) (pr1 (pr1 F)) (pr1 (pr1 G))
             (base_paths (pr1 F) (pr1 G)
                (base_paths F G (functor_eq_from_functor_iso H F G gamma))) a))).
      assert (H2 := maponpaths (@pr1 _ _ ) H').
      simpl in H2. apply H2. 
  unfold functor_eq_from_functor_iso.
  unfold functor_eq.
  rewrite base_total_path.
  unfold pr1_functor_eq_from_functor_iso.
  rewrite base_total_path.
  pathvia (pr1 (idtoiso
     (isotoid D H (functor_iso_pointwise_if_iso C D F G gamma (pr2 gamma) a)))).
  apply maponpaths.
  apply maponpaths.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  rewrite toforallpaths_funextsec.
  apply idpath.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma isweq_idtoiso_functorcat (C D : precategory) (H : is_category D) 
    (F G : ob [C, D]) :
   isweq (@idtoiso _ F G).
Proof.
  apply (gradth _ (functor_eq_from_functor_iso H F G)).
  apply functor_eq_from_functor_iso_idtoiso.
  apply idtoiso_functor_eq_from_functor_iso.
Defined.

Lemma is_category_functor_category (C D : precategory) (H : is_category D) :
   is_category [C, D].
Proof.
  intros F G.
  apply isweq_idtoiso_functorcat.
  apply H.
Qed.


 := 
   tpair _ (tpair _ UU (fun A B : UU => A -> B)) 


Definition nat_trans_UU : 



  
Definition is_inverse_in_precat {C : precategory} {a b : C}
  (f : a --> b) (g : b --> a) := 
  dirprod (f ;; g == identity a)
          (g ;; f == identity b).

Lemma isaprop_is_inverse_in_precat (C : precategory) (a b : ob C)
   (f : a --> b) (g : b --> a) : isaprop (is_inverse_in_precat f g).
Proof.
  apply isapropdirprod.
  apply (pr2 (a --> a)).
  apply (pr2 (b --> b)).
Qed.

Lemma inverse_unique_precat (C : precategory) (a b : ob C)
   (f : a --> b) (g g': b --> a) (H : is_inverse_in_precat f g)
    (H' : is_inverse_in_precat f g') : g == g'.
Proof.
  destruct H as [eta eps].
  destruct H' as [eta' eps'].
  assert (H : g == identity b ;; g).
    rewrite id_left; apply idpath.
  apply (pathscomp0 H).
  rewrite <- eps'.
  rewrite <- assoc.
  rewrite eta.
  apply id_right.
Qed.

Definition is_isomorphism {C : precategory} {a b : ob C}
  (f : a --> b) := total2 (fun g => is_inverse_in_precat f g).

Lemma isaprop_is_isomorphism {C : precategory} {a b : ob C}
     (f : a --> b) : isaprop (is_isomorphism f).
Proof.
  apply invproofirrelevance.
  intros g g'.
  set (Hpr1 := inverse_unique_precat _ _ _ _ _ _ (pr2 g) (pr2 g')).
  apply (total2_paths Hpr1).
  destruct g as [g [eta eps]].
  destruct g' as [g' [eta' eps']].
  simpl in *.
  apply pairofobuip.
Qed.

Definition iso {C : precategory} (a b :ob C) := total2
    (fun f : a --> b => is_isomorphism f).

Lemma eq_iso (C : precategory)(a b : ob C)
   (f g : iso a b) : pr1 f == pr1 g -> f == g.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_isomorphism.
Defined.

Definition morphism_from_iso (C : precategory)(a b : ob C) 
   (f : iso a b) : a --> b := pr1 f.
Coercion morphism_from_iso : iso >-> pr1hSet.

Lemma isaset_iso {C : precategory} (a b :ob C) :
  isaset (iso a b).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply (pr2 (a --> b)).
  intro f.
  apply isasetaprop.
  apply isaprop_is_isomorphism.
Qed.

Lemma identity_is_iso (C : precategory) (a : ob C) :
    is_isomorphism (identity a).
Proof.
  exists (identity a).
  simpl; split;
  apply id_left.
Defined.

Definition identity_iso {C : precategory} (a : ob C) :
   iso a a := tpair _ _ (identity_is_iso C a).

Definition inv_from_iso {C : precategory} {a b : ob C}
  (f : iso a b) : b --> a := pr1 (pr2 f).

Lemma is_iso_inv_from_iso {C : precategory} (a b : ob C)
  (f : iso a b) : is_isomorphism (inv_from_iso f).
Proof.
  exists (pr1 f).
  simpl; split; simpl.
  unfold inv_from_iso.
  apply (pr2 (pr2 (pr2 f))).
  apply (pr1 (pr2 (pr2 f))).
Defined.

Definition iso_inv_from_iso {C : precategory} {a b : ob C}
  (f : iso a b) : iso b a.
Proof.
  exists (inv_from_iso f).
  apply is_iso_inv_from_iso.
Defined.

Definition iso_inv_from_is_iso {C : precategory} {a b : ob C}
  (f : a --> b) (H : is_isomorphism f) : iso b a :=
  iso_inv_from_iso (tpair _ f H).

Definition iso_inv_after_iso (C : precategory) (a b : ob C)
   (f : iso a b) : f;; inv_from_iso f == identity _ :=
      pr1 (pr2 (pr2 f)).

Definition iso_after_iso_inv (C : precategory) (a b : ob C)
   (f : iso a b) : inv_from_iso f ;; f == identity _ :=
      pr2 (pr2 (pr2 f)).


Lemma iso_inv_on_right (C : precategory) (a b c: ob C)
  (f : iso a  b) (g : b --> c) (h : a --> c) (H : h == f;;g) :
     inv_from_iso f ;; h == g.
Proof.
  assert (H2 : inv_from_iso f;; h == 
                  inv_from_iso f;; (f ;; g)).
  apply maponpaths; assumption.
  rewrite assoc in H2.
  rewrite H2.
  rewrite iso_after_iso_inv.
  apply id_left.
Qed.

Lemma iso_inv_on_left (C : precategory) (a b c: ob C)
  (f : a --> b) (g : iso b c) (h : a --> c) (H : h == f;;g) :
     f == h ;; inv_from_iso g.
Proof.
  assert (H2 : h ;; inv_from_iso g == 
                         (f;; g) ;; inv_from_iso g).
    rewrite H. apply idpath.
  rewrite <- assoc in H2.
  rewrite iso_inv_after_iso in H2.
  rewrite id_right in H2.
  apply pathsinv0.
  assumption.
Qed.


(** ** Properties of isomorphisms *)
(** Stability under composition, inverses etc *)

Lemma are_inverse_comp_of_inverses (C : precategory) (a b c : C)
     (f : iso a b) (g : iso b c) :  
  is_inverse_in_precat (f;; g) (inv_from_iso g;; inv_from_iso f).
Proof.
  simpl; split; simpl;
  unfold inv_from_iso; simpl.
  destruct f as [f [f' Hf]]. simpl in *.
  destruct g as [g [g' Hg]]; simpl in *.
  pathvia ((f ;; (g ;; g')) ;; f').
  repeat rewrite assoc; apply idpath.
  rewrite (pr1 Hg).
  rewrite id_right.
  rewrite (pr1 Hf).
  apply idpath.

  destruct f as [f [f' Hf]]. simpl in *.
  destruct g as [g [g' Hg]]; simpl in *.
  pathvia ((g' ;; (f' ;; f)) ;; g).
  repeat rewrite assoc; apply idpath.
  rewrite (pr2 Hf).
  rewrite id_right.
  rewrite (pr2 Hg).
  apply idpath.
Qed. 


Lemma is_iso_comp_of_isos {C : precategory} {a b c : ob C}
  (f : iso a b) (g : iso b c) : is_isomorphism (f ;; g).
Proof.
  exists (inv_from_iso g ;; inv_from_iso f). simpl.
  apply are_inverse_comp_of_inverses.
Defined. (* Qed. *)


Definition iso_comp {C : precategory} {a b c : ob C}
  (f : iso a b) (g : iso b c) : iso a c.
Proof.
  exists (f ;; g).
  apply is_iso_comp_of_isos.
Defined.

Lemma inv_iso_unique (C : precategory) (a b : ob C)
  (f : iso a b) (g : iso b a) :
  is_inverse_in_precat f g -> g == iso_inv_from_iso f.
Proof.
  intro H.
  apply eq_iso.
  apply (inverse_unique_precat _ _ _ f).
  assumption.
  split.
  apply iso_inv_after_iso.
  set (h := iso_after_iso_inv _ _ _ f).
  unfold iso_inv_from_iso.
  simpl in *.
  apply h.
Qed.


Lemma iso_inv_of_iso_comp (C : precategory) (a b c : ob C)
   (f : iso a b) (g : iso b c) :
   iso_inv_from_iso (iso_comp f g) == iso_comp (iso_inv_from_iso g) (iso_inv_from_iso f).
Proof.
  apply eq_iso. 
  reflexivity.
Qed.

Lemma iso_inv_of_iso_id (C : precategory) (a : ob C) :
   iso_inv_from_iso (identity_iso a) == identity_iso a.
Proof.
  apply eq_iso.
  apply idpath.
Qed.


Lemma iso_inv_iso_inv (C : precategory) (a b : ob C)
   (f : iso a b) : 
     iso_inv_from_iso (iso_inv_from_iso f) == f.
Proof.
  apply eq_iso.
  reflexivity.
Defined.

Lemma pre_comp_with_iso_is_inj (C : precategory) (a b c : ob C)
    (f : a --> b) (H : is_isomorphism f) (g h : b --> c) : f ;; g == f ;; h -> g == h.
Proof.
  intro HH.
  pathvia (pr1 H ;; f ;; g).
  rewrite (pr2 (pr2 H)).
  rewrite id_left.
  apply idpath.
  pathvia ((pr1 H ;; f) ;; h).
  repeat rewrite <- assoc.
  apply maponpaths. assumption.
  rewrite (pr2 (pr2 H)).
  rewrite id_left.
  apply idpath.
Qed.
  
Lemma post_comp_with_iso_is_inj (C : precategory) (b c : ob C)
     (h : b --> c) (H : is_isomorphism h) 
   (a : ob C) (f g : a --> b) : f ;; h == g ;; h -> f == g.
Proof.
  intro HH.
  pathvia (f ;; (h ;; pr1 H)).
  rewrite (pr1 (pr2 H)).
  rewrite id_right.
  apply idpath.
  pathvia (g ;; (h ;; pr1 H)).
  repeat rewrite assoc.
  rewrite HH. apply idpath.
  rewrite (pr1 (pr2 H)).
  rewrite id_right.
  apply idpath.
Qed.

(** ***  *)
Lemma iso_set_isweq {X Y:hSet} (f:X->Y) (g:Y->X) :
  (forall x, g(f x) == x) ->
  (forall y, f(g y) == y) ->
  isweq f.
Proof.
  intros p q y.
  refine (tpair _ (tpair _ (g y) _) _).
  - exact (q y).
  - intros [x e]. induction e.
    apply (total2_paths2 (! p x)).
    apply setproperty.
Defined.

Lemma iso_comp_right_isweq {C:precategory} {a b:ob C} (h:iso a b) (c:C) :
  isweq (fun f : b --> c => h ;; f).
Proof. intros. apply (iso_set_isweq (fun f => h ;; f) (fun g => inv_from_iso h ;; g)).
       { intros f. refine (_ @ maponpaths (fun m => m ;; f) (pr2 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } }
       { intros g. refine (_ @ maponpaths (fun m => m ;; g) (pr1 (pr2 (pr2 h))) @ _).
         { apply assoc. } { apply id_left. } } Qed.



(** * Categories (aka saturated precategories) *)

(** ** Definition of categories *)

Definition idtoiso {C : precategory} {a b : ob C}:
      a == b -> iso a b.
Proof.
  intro H.
  destruct H.
  exact (identity_iso a).
Defined.
      
(* use eta expanded version to force printing of object arguments *)
Definition is_category (C : precategory) := forall (a b : ob C),
    isweq (fun p : a == b => idtoiso p).

Lemma eq_idtoiso_idtomor {C:precategory} (a b:ob C) (e:a == b) :
    pr1 (idtoiso e) == idtomor _ _ e.
Proof. 
  destruct e; reflexivity. 
Defined.

Lemma isaprop_is_category (C : precategory) : isaprop (is_category C).
Proof.
  apply impred.
  intro a.
  apply impred.
  intro b.
  apply isapropisweq.
Qed.

Definition category := total2 (fun C : precategory => is_category C).

Definition precat_from_cat (C : category) : precategory := pr1 C.
Coercion precat_from_cat : category >-> precategory.

Lemma category_has_groupoid_ob (C : category) : 
  isofhlevel 3 (ob C).
Proof.
  change (isofhlevel 3 C) with
        (forall a b : C, isofhlevel 2 (a == b)).
  intros a b.
  apply (isofhlevelweqb _ (tpair _ _ (pr2 C a b))).
  apply isaset_iso.
Qed.
  

(** ** Definition of [isotoid] *)

Definition isotoid (C : precategory) (H : is_category C) {a b : ob C}:
      iso a b -> a == b := invmap (weqpair _ (H a b)).

Lemma idtoiso_isotoid (C : precategory) (H : is_category C) (a b : ob C)
    (f : iso a b) : idtoiso (isotoid _ H f) == f.
Proof.
  unfold isotoid.
  set (Hw := homotweqinvweq (weqpair idtoiso (H a b))).
  simpl in Hw.
  apply Hw.
Qed.

Lemma isotoid_idtoiso (C : precategory) (H : is_category C) (a b : ob C)
    (p : a == b) : isotoid _ H (idtoiso p) == p.
Proof.
  unfold isotoid.
  set (Hw := homotinvweqweq (weqpair idtoiso (H a b))).
  simpl in Hw.
  apply Hw.
Qed.

(** ** Properties of [idtoiso] and [isotoid] *)

Definition double_transport {C : precategory} {a a' b b' : ob C}
   (p : a == a') (q : b == b') (f : a --> b) : a' --> b' :=
  transportf (fun c => a' --> c) q (transportf (fun c => c --> b) p f).

Lemma idtoiso_postcompose (C : precategory) (a b b' : ob C)
  (p : b == b') (f : a --> b) :
      f ;; idtoiso p == transportf (fun b => a --> b) p f.
Proof.
  destruct p.
  apply id_right.
Qed.

Lemma idtoiso_postcompose_iso (C : precategory) (a b b' : ob C)
  (p : b == b') (f : iso a b) : 
    iso_comp f (idtoiso p) == transportf (fun b => iso a b) p f.
Proof.
  destruct p.
  apply eq_iso.
  simpl.
  apply id_right.
Qed.


Lemma idtoiso_precompose (C : precategory) (a a' b : ob C)
  (p : a == a') (f : a --> b) : 
      (idtoiso (!p)) ;; f == transportf (fun a => a --> b) p f.
Proof.
  destruct p.
  apply id_left.
Qed.

Lemma idtoiso_precompose_iso (C : precategory) (a a' b : ob C)
  (p : a == a') (f : iso a b) : 
      iso_comp (idtoiso (!p)) f == transportf (fun a => iso a b) p f.
Proof.
  destruct p.
  apply eq_iso.
  simpl.
  apply id_left.
Qed.



Lemma double_transport_idtoiso (C : precategory) (a a' b b' : ob C) 
  (p : a == a') (q : b == b')  (f : a --> b) : 
  double_transport p q f == inv_from_iso (idtoiso p) ;; f ;; idtoiso q.
Proof.
  destruct p.
  destruct q.
  rewrite id_right.
  rewrite id_left.
  apply idpath.
Qed.

Lemma idtoiso_inv (C : precategory) (a a' : ob C)
  (p : a == a') : idtoiso (!p) == iso_inv_from_iso (idtoiso p).
Proof.
  destruct p. 
  apply idpath.
Qed.


Lemma idtoiso_concat (C : precategory) (a a' a'' : ob C)
  (p : a == a') (q : a' == a'') :
  idtoiso (p @ q) == iso_comp (idtoiso p) (idtoiso q).
Proof.
  destruct p.
  destruct q.
  apply eq_iso.
  simpl;  
  rewrite id_left.
  apply idpath.
Qed.

Lemma idtoiso_inj (C : precategory) (H : is_category C) (a a' : ob C)
   (p p' : a == a') : idtoiso p == idtoiso p' -> p == p'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply H.
Qed.

Lemma isotoid_inj (C : precategory) (H : is_category C) (a a' : ob C)
   (f f' : iso a a') : isotoid _ H f == isotoid _ H f' -> f == f'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply isweqinvmap.
Qed.

Lemma isotoid_comp (C : precategory) (H : is_category C) (a b c : ob C)
  (e : iso a b) (f : iso b c) :
  isotoid _ H (iso_comp e f) == isotoid _ H e @ isotoid _ H f.
Proof.
  apply idtoiso_inj.
    assumption.
  rewrite idtoiso_concat.
  repeat rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma isotoid_identity_iso (C : precategory) (H : is_category C) (a : C) :
  isotoid _ H (identity_iso a) == idpath _ .
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid;
  apply idpath.
Qed.


Lemma inv_isotoid (C : precategory) (H : is_category C) (a b : C)
    (f : iso a b) : ! isotoid _ H f == isotoid _ H (iso_inv_from_iso f).
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.
  

Lemma transportf_isotoid (C : precategory) (H : is_category C) 
   (a a' b : ob C) (p : iso a a') (f : a --> b) : 
 transportf (fun a0 : C => a0 --> b) (isotoid C H p) f == inv_from_iso p ;; f.
Proof.
  rewrite <- idtoiso_precompose.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid_dep (C : precategory) 
   (a a' : C) (p : a == a') (f : forall c, a --> c) :
 transportf (fun x : C => forall c, x --> c) p f == fun c => idtoiso (!p) ;; f c.
Proof.
  destruct p.
  simpl.
  apply funextsec.
  intro.
  rewrite id_left.
  apply idpath.
Qed.

Lemma transportf_isotoid_dep' (J C : precategory) 
  (F : J -> C)
   (a a' : C) (p : a == a') (f : forall c, a --> F c) :
 transportf (fun x : C => forall c, x --> F c) p f == fun c => idtoiso (!p) ;; f c.
Proof.
  destruct p.
  apply funextsec.
  intro. simpl.
  apply (! id_left _ _ _ _).
Defined.


(** ** Precategories in style of essentially algebraic cats *)
(** Of course we later want SETS of objects, rather than types,
    but the construction can already be specified.
*)
       
Definition total_morphisms (C : precategory_ob_mor) := total2 (
   fun ab : dirprod (ob C)(ob C) =>
        precategory_morphisms (pr1 ab) (pr2 ab)).

Lemma isaset_setcategory_total_morphisms (C : setcategory) : 
   isaset (total_morphisms C).
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply isofhleveldirprod.
  exact (pr2 C).
  exact (pr2 C).
  exact (fun x => (pr2 (pr1 x --> pr2 x))).
Qed.

Definition setcategory_total_morphisms_set (C : setcategory) : hSet :=
    hSetpair _ (isaset_setcategory_total_morphisms C).

Definition precategory_source (C : precategory_ob_mor) : 
     total_morphisms C -> ob C := 
     fun abf => pr1 (pr1 abf).

Definition precategory_target (C : precategory_ob_mor) : 
     total_morphisms C -> ob C := 
     fun abf => pr2 (pr1 abf).

Definition precategory_total_id (C : precategory_data) : 
      ob C -> total_morphisms C :=
      fun c => tpair _ (dirprodpair c c) (identity c).

Definition precategory_total_comp'' (C : precategory_data) : 
      forall f g : total_morphisms C,
        precategory_target C f == precategory_source C g ->
         total_morphisms C.
Proof.
  intros f g e.
  destruct f as [[a b] f]. simpl in *.
  destruct g as [[b' c] g]. simpl in *.
  unfold precategory_target in e; simpl in e.
  unfold precategory_source in e; simpl in e. 
  simpl.
  exists (dirprodpair a c). simpl.
  exact ((f ;; idtomor _ _ e) ;; g).
Defined.

Definition precategory_total_comp (C : precategory_data) : 
      forall f g : total_morphisms C,
        precategory_target C f == precategory_source C g ->
         total_morphisms C := 
  fun f g e => 
     tpair _ (dirprodpair (pr1 (pr1 f))(pr2 (pr1 g)))
        ((pr2 f ;; idtomor _ _ e) ;; pr2 g).



