(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman
january 2013


************************************************************)


(** **********************************************************

Contents :  

		- Functors
                  - preserve isos, inverses
                                    
                  - fully faithful functors
                    - preserve isos, inverses, composition 
                            backwards
                    
                  - essentially surjective
                  - faithful
                  - full
                  - fully faithful is the same as full and faithful
                  
                  - Image of a functor, full subcat specified
                                       by a functor
                 
                      
                      
		- Natural transformations
                  - Equality is pointwise equality.
                  
                  
		- Functor (pre)category			
                  - Isomorphisms in functor category are pointwise
                         isomorphisms
                         
                - Isomorphic Functors are equal
                   if target precategory is category
                   [functor_eq_from_functor_iso]
                  
                - Functor precategory is category if
                   target precategory is
                   [is_category_functor_category]
		
		           
************************************************************)


Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).




(** * Functors : Morphisms of precategories *)


Definition functor_data (C C' : precategory_ob_mor) :=
  total2 ( fun F : ob C -> ob C' =>  forall a b : ob C, a --> b -> F a --> F b).

Definition functor_data_constr ( C C' : precategory_ob_mor )
           ( F : ob C -> ob C' ) ( Fm : forall a b : ob C, a --> b -> F a --> F b ) :
  functor_data C C' := tpair _ F Fm . 

Definition functor_on_objects {C C' : precategory_ob_mor}
     (F : functor_data C C') :  ob C -> ob C' := pr1 F.
Coercion functor_on_objects : functor_data >-> Funclass.


Definition functor_on_morphisms {C C' : precategory_ob_mor} (F : functor_data C C') 
  { a b : ob C} :  a --> b -> F a --> F b := pr2 F a b.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Definition functor_idax {C C' : precategory_data} (F : functor_data C C') :=
  forall a : ob C, #F (identity a) = identity (F a).

Definition functor_compax {C C' : precategory_data} (F : functor_data C C') :=
  forall a b c : ob C, forall f : a --> b, forall g : b --> c, #F (f ;; g) = #F f ;; #F g .

Definition is_functor {C C' : precategory_data} (F : functor_data C C') :=
     dirprod ( functor_idax F ) ( functor_compax F ) . 

Lemma isaprop_is_functor (C C' : precategory_data) (hs: has_homsets C')
      (F : functor_data C C') : isaprop (is_functor F).
Proof.
  apply isofhleveldirprod.
  apply impred; intro a.
  apply hs.
  repeat (apply impred; intro).
  apply hs.
Qed.

Definition functor (C C' : precategory_data) :=
  total2 ( fun F : functor_data C C' => is_functor F ).


Lemma functor_eq (C C' : precategory_data) (hs: has_homsets C') (F F': functor C C'):
    pr1 F = pr1 F' -> F = F'.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_functor.
  apply hs.
Defined.

Definition functor_data_from_functor (C C': precategory_data)
     (F : functor C C') : functor_data C C' := pr1 F.
Coercion functor_data_from_functor : functor >-> functor_data.


Definition functor_eq_eq_from_functor_ob_eq (C C' : precategory_data) (hs: has_homsets C')
   (F G : functor C C') (p q : F = G) 
   (H : base_paths _ _ (base_paths _ _  p) = 
         base_paths _ _ (base_paths _ _ q)) :
    p = q.
Proof.
  apply (invmaponpathsweq (total2_paths_equiv _ _ _ )).
  simpl.
  assert (H' : base_paths _ _ p = base_paths _ _ q).
  apply (invmaponpathsweq (total2_paths_equiv _ _ _ )).
  simpl. 
  apply (@total2_paths2 _ (fun p : pr1 (pr1 F) = pr1 (pr1 G) =>
          transportf
            (fun x : ob C -> ob C' =>
            (fun x0 : ob C -> ob C' => 
            forall a b : ob C, a --> b -> x0 a --> x0 b) x)
            p (pr2 (pr1 F)) = pr2 (pr1 G)) _ 
   (fiber_paths (base_paths F G p)) _ (fiber_paths (base_paths F G q))  H).
   apply uip.
   change (isaset) with (isofhlevel 2).
   apply impred; intro a.
   apply impred; intro b.
   apply impred; intro f.
   apply hs.
   apply (@total2_paths2 (pr1 F = pr1 G)  
    (fun x : pr1 F = pr1 G => transportf _ x (pr2 F) = pr2 G)
          (base_paths F G p) (fiber_paths p) (base_paths F G q) (fiber_paths q) H').
   apply uip.
   apply isasetaprop.
   apply isaprop_is_functor.
   apply hs.
Defined.


 

Definition functor_id {C C' : precategory_data}(F : functor C C'):
       forall a : ob C, #F (identity a) = identity (F a) := pr1 (pr2 F).

Definition functor_comp {C C' : precategory_data}
      (F : functor C C'):
       forall a b c : ob C, forall f : a --> b,
                 forall g : b --> c, 
                #F (f ;; g) = #F f ;; #F g := pr2 (pr2 F).

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
  rewrite iso_after_iso_inv.
  apply functor_id.
Qed.


Lemma functor_on_iso_is_iso (C C' : precategory) (F : functor C C')
    (a b : ob C)(f : iso a b) : is_isomorphism (#F f).
Proof.
  apply (is_iso_qinv _ (#F (inv_from_iso f))).
  apply is_inverse_functor_image.
Defined.


Definition functor_on_iso (C C' : precategory) (F : functor C C')
    (a b : ob C)(f : iso a b) : iso (F a) (F b).
Proof.
  exists (#F f).
  apply functor_on_iso_is_iso.
Defined.
 
Lemma functor_on_iso_inv (C C' : precategory) (F : functor C C')
    (a b : ob C) (f : iso a b) : 
   functor_on_iso _ _ F _ _ (iso_inv_from_iso f) = 
       iso_inv_from_iso (functor_on_iso _ _ F _ _ f).
Proof.
  apply eq_iso; simpl.
  apply inv_iso_unique'; simpl.
  unfold precomp_with. rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  apply functor_id.
Defined.
  
(** ** Functors preserve inverses *)

Lemma functor_on_inv_from_iso (C C' : precategory) (F : functor C C')
    (a b : ob C)(f : iso a b) :
      #F (inv_from_iso f) = inv_from_iso (functor_on_iso _ _ F _ _ f) .
Proof.
  apply inv_iso_unique'; simpl.  
  unfold precomp_with. rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  apply functor_id.
Qed. 


(** ** Fully faithful functors *)

Definition fully_faithful {C D : precategory_data} (F : functor C D) := 
  forall a b : ob C, 
    isweq (functor_on_morphisms F (a:=a) (b:=b)).

Lemma isaprop_fully_faithful (C D : precategory_data) (F : functor C D) :
   isaprop (fully_faithful F).
Proof.
  apply impred; intro a.
  apply impred; intro b.
  apply isapropisweq.
Qed.

Definition weq_from_fully_faithful {C D : precategory_data}{F : functor C D}
      (FF : fully_faithful F) (a b : ob C) : 
   weq (a --> b) (F a --> F b).
Proof.
  exists (functor_on_morphisms F (a:=a) (b:=b)).
  exact (FF a b).
Defined.


Definition fully_faithful_inv_hom {C D : precategory_data}{F : functor C D} 
      (FF : fully_faithful F) (a b : ob C) :
      F a --> F b -> a --> b :=
 invweq (weq_from_fully_faithful FF a b).

Local Notation "FF ^-1" := (fully_faithful_inv_hom FF _ _ ) (at level 20).

Lemma fully_faithful_inv_identity (C D : precategory_data) (F : functor C D)
      (FF : fully_faithful F) (a : ob C) : 
         FF^-1 (identity (F a)) = identity _.
Proof.
  apply (invmaponpathsweq (weq_from_fully_faithful FF a a)).
  unfold fully_faithful_inv_hom.
  set (HFaa:=homotweqinvweq (weq_from_fully_faithful FF a a)(identity _ )).
  simpl in *. 
  rewrite HFaa.
  rewrite functor_id; apply idpath.
Qed.


Lemma fully_faithful_inv_comp (C D : precategory_data) (F : functor C D)
      (FF : fully_faithful F) (a b c : ob C) 
      (f : F a --> F b) (g : F b --> F c) : 
        FF^-1 (f ;; g) = FF^-1 f ;; FF^-1 g.
Proof.
  apply (invmaponpathsweq (weq_from_fully_faithful FF a c)).
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
  apply (invmaponpathsweq (weq_from_fully_faithful FF a a)).
  set (HFFab := homotweqinvweq (weq_from_fully_faithful FF a b)).
  set (HFFba := homotweqinvweq (weq_from_fully_faithful FF b a)).
  simpl in *.
  rewrite functor_comp.
  rewrite HFFab; clear HFFab.
  rewrite HFFba; clear HFFba.
  rewrite functor_id.
  apply iso_inv_after_iso.
  
  apply (invmaponpathsweq (weq_from_fully_faithful FF b b)).
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
  apply (is_iso_qinv _ (FF^-1 (inv_from_iso f))).
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
        (iso_from_fully_faithful_reflection HF a b f) = f.
Proof.
  apply eq_iso. 
  simpl;
  apply (homotweqinvweq (weq_from_fully_faithful HF a b)).
Qed.



(** ** Essentially surjective functors *)

Definition essentially_surjective {C D : precategory_data} (F : functor C D) :=
  forall b, ishinh (total2 (fun a => iso (F a) b)).
   
(** ** Faithful functors *)

Definition faithful {C D : precategory_data} (F : functor C D) := 
  forall a b : ob C, isincl (fun f : a --> b => #F f).

Lemma isaprop_faithful (C D : precategory_data) (F : functor C D) : 
   isaprop (faithful F).
Proof.
  repeat (apply impred; intro).
  apply isapropiscontr.
Qed.

(** ** Full functors *)


Definition full {C D : precategory_data} (F : functor C D) :=
   forall a b: C, issurjective (fun f : a --> b => #F f).



(** ** Fully faithful is the same as full and faithful *)

Definition full_and_faithful {C D : precategory_data} (F : functor C D) :=
   dirprod (full F) (faithful F).


Lemma fully_faithful_implies_full_and_faithful (C D : precategory_data) (F : functor C D) :
   fully_faithful F -> full_and_faithful F.
Proof.
  intro H.
  split; simpl.
  unfold full. intros a b.
  apply issurjectiveweq.
  apply H.
  intros a b.
  apply isinclweq.
  apply H.
Qed.

  
Lemma full_and_faithful_implies_fully_faithful (C D : precategory_data) (F : functor C D) :
   full_and_faithful F -> fully_faithful F.
Proof. 
  intros [Hfull Hfaith].
  intros a b.
  simpl in *.
  apply isweqinclandsurj.
  - apply Hfaith.
  - apply Hfull.
Qed.
 
Lemma isaprop_full_and_faithful (C D : precategory_data) (F : functor C D) :
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
  
  
Definition weq_fully_faithful_full_and_faithful (C D : precategory_data) (F : functor C D) :
   weq (fully_faithful F) (full_and_faithful F) :=
  weqimplimpl (fully_faithful_implies_full_and_faithful _ _ F)
              (full_and_faithful_implies_fully_faithful _ _ F)
              (isaprop_fully_faithful _ _ F)
              (isaprop_full_and_faithful _ _ F).

(** ** Image on objects of a functor  *)
(** is used later to define the full image subcategory of a category [D] 
       defined by a functor [F : C -> D] *)

Definition is_in_img_functor {C D : precategory_data} (F : functor C D) 
      (d : ob D) :=
  ishinh (
  total2 (fun c : ob C => iso (F c) d)).

Definition sub_img_functor {C D : precategory_data}(F : functor C D) :
    hsubtypes (ob D) := 
       fun d : ob D => is_in_img_functor F d.



(** ** Composition of Functors, Identity Functors *)

(** *** Composition *)

Definition functor_composite_data {C C' C'' : precategory_ob_mor } (F : functor_data C C')
           (F' : functor_data C' C'') : functor_data C C'' :=           
  functor_data_constr C C'' (fun a => F' (F a))  (fun (a b : ob C) f => #F' (#F f)) .


Lemma is_functor_composite {C C' C'' : precategory_data}
       (F : functor C C') (F' : functor C' C'') :
 is_functor ( functor_composite_data F F' ) . 
Proof.
  split; simpl.
  intro a.
  assert ( e1 := functor_id F a ) .
  assert ( e2 := functor_id F' ( F a ) ) .
  apply ( ( maponpaths ( # F' ) e1 ) @ e2 ) .

  unfold functor_compax .  intros . 
  assert ( e1 := functor_comp F _ _ _ f g ) . 
  assert ( e2 := functor_comp F' _ _ _ ( # F f ) ( # F g ) ) .
  apply ( ( maponpaths ( # F' ) e1 ) @ e2 ) . 
Defined.


Definition functor_composite (C C' C'' : precategory_data) (F : functor C C') (F' : functor C' C'') :
  functor C C'' := tpair _ _ (is_functor_composite F F').

(** *** Identity functor *)

Definition functor_identity_data ( C  : precategory_data ) : functor_data C C :=
  functor_data_constr C C (fun a => a) (fun (a b : ob C) f => f) . 

Lemma is_functor_identity (C : precategory_data) : is_functor ( functor_identity_data C ) . 
Proof.
  split; simpl.
  unfold functor_idax. intros; apply idpath.
  unfold functor_compax. intros; apply idpath.
Defined.

Definition functor_identity (C : precategory_data) : functor C C :=
  tpair _ _ ( is_functor_identity C ) . 



(** * Natural transformations *)


(** ** Definition of natural transformations *)

Definition is_nat_trans {C C' : precategory_data}
  (F F' : functor_data C C')
  (t : forall x : ob C, F x -->  F' x) := 
  forall (x x' : ob C)(f : x --> x'),
    #F f ;; t x' = t x ;; #F' f.


Lemma isaprop_is_nat_trans (C C' : precategory_data) (hs: has_homsets C')
  (F F' : functor_data C C') (t : forall x : ob C, F x -->  F' x):
  isaprop (is_nat_trans F F' t).
Proof.
  repeat (apply impred; intro).
  apply hs.
Qed.


Definition nat_trans {C C' : precategory_data}
  (F F' : functor_data C C') := total2 (
   fun t : forall x : ob C, F x -->  F' x => is_nat_trans F F' t).

Lemma isaset_nat_trans {C C' : precategory_data} (hs: has_homsets C')
  (F F' : functor_data C C') : isaset (nat_trans F F').
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply impred.
  intro t. apply hs.
  intro x. 
  apply isasetaprop.
  apply isaprop_is_nat_trans.
  apply hs.
Qed.

Definition nat_trans_data {C C' : precategory_data}
 {F F' : functor_data C C'}(a : nat_trans F F') :
   forall x : ob C, F x --> F' x := pr1 a.
Coercion nat_trans_data : nat_trans >-> Funclass.

Definition nat_trans_ax {C C' : precategory_data}
  {F F' : functor_data C C'} (a : nat_trans F F') :
  forall (x x' : ob C)(f : x --> x'),
    #F f ;; a x' = a x ;; #F' f := pr2 a.

(** Equality between two natural transformations *)

Lemma nat_trans_eq {C C' : precategory_data} (hs: has_homsets C')
  (F F' : functor_data C C')(a a' : nat_trans F F'):
  (forall x, a x = a' x) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  apply funextsec.
  assumption.
  apply (total2_paths H').
  apply proofirrelevance.
  apply isaprop_is_nat_trans.
  apply hs.
Qed.

Definition nat_trans_eq_pointwise {C C' : precategory_data}
   {F F' : functor_data C C'} {a a' : nat_trans F F'}:
      a = a' -> forall x, a x = a' x.
Proof.
  intro h.
  apply toforallpaths.
  apply maponpaths.
  assumption.
Qed.


(** ** Functor category [[C, D]] *)

Definition functor_precategory_ob_mor (C C' : precategory_data): 
  precategory_ob_mor := precategory_ob_mor_pair 
   (functor C C') (fun F F' : functor C C' => nat_trans F F').
                        

(** *** Identity natural transformation *)

Lemma is_nat_trans_id {C : precategory_data}{C' : precategory}
  (F : functor_data C C') : is_nat_trans F F
     (fun c : ob C => identity (F c)).
Proof.
  intros ? ? ? .
  rewrite id_left.
  rewrite id_right.
  apply idpath.
Qed.

Definition nat_trans_id {C:precategory_data}{C' : precategory}
  (F : functor_data C C') : nat_trans F F :=
    tpair _ _ (is_nat_trans_id F).

(** *** Composition of natural transformations *)

Lemma is_nat_trans_comp {C : precategory_data}{C' : precategory}
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


Definition nat_trans_comp {C:precategory_data}{C' : precategory}
  (F G H: functor_data C C') 
  (a : nat_trans F G)
  (b : nat_trans G H): nat_trans F H :=
    tpair _ _ (is_nat_trans_comp a b).


(** *** The data of the functor precategory *)

Definition functor_precategory_data (C : precategory_data)(C' : precategory): precategory_data.
Proof.
  apply ( precategory_data_pair 
        (functor_precategory_ob_mor C C')).
  intro a. simpl.
  apply (nat_trans_id (pr1 a)).
  intros a b c f g.
  apply (nat_trans_comp _ _ _ f g).
Defined.

(** *** Above data forms a precategory *)

Lemma is_precategory_functor_precategory_data 
  (C:precategory_data)(C' : precategory) (hs: has_homsets C'):
   is_precategory (functor_precategory_data C C').
Proof.
  repeat split; simpl; intros.
  unfold identity.
  simpl.
  apply nat_trans_eq. apply hs.
  intro x; simpl.
  apply id_left.
  
  apply nat_trans_eq. apply hs.
  intro x; simpl.
  apply id_right.
  
  apply nat_trans_eq. apply hs.
  intro x; simpl.
  apply assoc.
Qed.

Definition functor_precategory (C : precategory_data) (C' : precategory) 
  (hs: has_homsets C'): precategory := 
  tpair (fun C => is_precategory C)   
        (functor_precategory_data C C')
        (is_precategory_functor_precategory_data C C' hs).

Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Lemma nat_trans_comp_pointwise (C : precategory_data)(C' : precategory) (hs: has_homsets C')
  (F G H : ob [C, C', hs]) (A : F --> G) (A' : G --> H) 
   (B : F --> H) : A ;; A' = B -> 
        forall a, pr1 A a ;; pr1 A' a = pr1 B a.
Proof.
  intros H' a.
  pathvia (pr1 (A ;; A') a).
  apply idpath.
  destruct H'.
  apply idpath.
Defined.
  

(** Characterizing isomorphisms in the functor category *)

Lemma is_nat_trans_inv_from_pointwise_inv (C : precategory_data)(D : precategory) 
  (hs: has_homsets D)
  (F G : ob [C,D,hs]) (A : F --> G) 
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

Definition nat_trans_inv_from_pointwise_inv (C : precategory_data)(D : precategory) 
  (hs: has_homsets D)
  (F G : ob [C,D,hs]) (A : F --> G) 
  (H : forall a : ob C, is_isomorphism (pr1 A a)) :
    G --> F := tpair _ _ (is_nat_trans_inv_from_pointwise_inv _ _ _ _ _ _ H).


Lemma is_inverse_nat_trans_inv_from_pointwise_inv (C : precategory_data)(C' : precategory) (hs: has_homsets C')
    (F G : [C, C', hs]) (A : F --> G)
   (H : forall a : C, is_isomorphism (pr1 A a)) : 
  is_inverse_in_precat A (nat_trans_inv_from_pointwise_inv C C' _ F G A H).
Proof.
  simpl; split; simpl.
  - apply nat_trans_eq. apply hs.
    intro x; simpl.
    set (T:=iso_inv_after_iso (tpair _ (pr1 A x) (H x))).
    apply T.
  - apply nat_trans_eq. apply hs.
    intro x; simpl.
    set (T:=iso_after_iso_inv (tpair _ (pr1 A x) (H x))).
    apply T. 
Qed.  


Lemma functor_iso_if_pointwise_iso (C : precategory_data) (C' : precategory) 
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) : 
   (forall a : ob C, is_isomorphism (pr1 A a)) ->  
           is_isomorphism A .
Proof.
  intro H.
  apply (is_iso_qinv _ (nat_trans_inv_from_pointwise_inv _ _ _ _ _ _ H)).
  simpl; apply is_inverse_nat_trans_inv_from_pointwise_inv.
Defined.

Definition functor_iso_from_pointwise_iso (C : precategory_data)(C' : precategory) 
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) 
   (H : forall a : ob C, is_isomorphism (pr1 A a)) : 
     iso F G := 
 tpair _ _ (functor_iso_if_pointwise_iso _ _ _ _ _ _ H).


Lemma is_functor_iso_pointwise_if_iso (C : precategory_data)(C' : precategory) 
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) : 
  is_isomorphism A -> 
       forall a : ob C, is_isomorphism (pr1 A a).  
Proof.
  intros H a.
  set (T:= inv_from_iso (tpair _ A H)). 
  set (TA:=iso_inv_after_iso (tpair _ A H)).
  set (TA':= iso_after_iso_inv (tpair _ A H)).
  simpl in *.
  apply (is_iso_qinv _ (T a)).
  simpl in *.
  unfold is_inverse_in_precat in *; simpl; split.
  - unfold T. 
    set (H1' := nat_trans_eq_pointwise TA). apply H1'.
  - apply (nat_trans_eq_pointwise TA').
Defined.

Lemma nat_trans_inv_pointwise_inv_before (C : precategory_data) (C' : precategory) 
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) (Aiso: is_isomorphism A) :
       forall a : C, pr1 (inv_from_iso (isopair A Aiso)) a ;; pr1 A a = identity _ .  
Proof.
  intro a.
  set (T:= inv_from_iso (isopair A Aiso)). 
  set (TA:=iso_inv_after_iso (isopair A Aiso)).
  set (TA':= iso_after_iso_inv (isopair A Aiso)).
  apply (nat_trans_eq_pointwise TA').
Defined.  

Lemma nat_trans_inv_pointwise_inv_after (C : precategory_data) (C' : precategory) 
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) (Aiso: is_isomorphism A) :
       forall a : C, pr1 A a ;; pr1 (inv_from_iso (isopair A Aiso)) a = identity _ .  
Proof.
  intro a.
  set (T:= inv_from_iso (isopair A Aiso)). 
  set (TA:=iso_inv_after_iso (isopair A Aiso)).
  set (TA':= iso_after_iso_inv (isopair A Aiso)).
  apply (nat_trans_eq_pointwise TA).
Defined.  


Definition functor_iso_pointwise_if_iso (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C',hs]) (A : F --> G) 
  (H : is_isomorphism A) : 
     forall a : ob C, 
       iso (pr1 F a) (pr1 G a) := 
  fun a => tpair _ _ (is_functor_iso_pointwise_if_iso C C' _ F G A H a).

Lemma nat_trans_inv_pointwise_inv_after_p (C : precategory_data) (C' : precategory) 
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) (Aiso: is_isomorphism A) a :
  inv_from_iso (functor_iso_pointwise_if_iso C C' hs F G A Aiso a) = 
        pr1 (inv_from_iso (isopair A Aiso)) a.
Proof.
  apply pathsinv0.
  apply inv_iso_unique'. 
  simpl.  
  set (TA:=iso_inv_after_iso (isopair A Aiso)).
  simpl in TA.
  apply (nat_trans_eq_pointwise TA).
Defined.

Definition pr1_pr1_functor_eq_from_functor_iso (C : precategory_data) (D : precategory) 
  (hs: has_homsets D)
    (H : is_category D) (F G : ob [C , D, hs]) :
   iso F G -> pr1 (pr1 F) = pr1 (pr1 G).
Proof.
  intro A.
  apply funextsec.
  intro t.
  apply isotoid.
  assumption.
  apply (functor_iso_pointwise_if_iso _ _ _ _ _ A).
  apply (pr2 A).
Defined.




Lemma transport_of_functor_map_is_pointwise (C : precategory_data) (D : precategory) 
      (F0 G0 : ob C -> ob D)
    (F1 : forall a b : ob C, a --> b -> F0 a --> F0 b)
   (gamma : F0  = G0 ) 
    (a b : ob C) (f : a --> b) :
transportf (fun x : ob C -> ob D => 
            forall a0 b0 : ob  C, a0 --> b0 -> x a0 --> x b0)
           gamma  F1 a b f = 
transportf (fun TT : ob D => G0 a --> TT)
  (toforallpaths (fun _ : ob C => D) F0 G0 gamma b)
  (transportf (fun SS : ob D => SS --> F0 b)
     (toforallpaths (fun _ : ob C => D) F0 G0 gamma a) (F1 a b f)).
Proof.
  induction gamma.
  apply idpath.
Defined.

Lemma toforallpaths_funextsec : forall (T : UU) (P : T -> UU) (f g : forall t : T, P t)
          (h : forall t : T, f t = g t), 
            toforallpaths _  _ _ (funextsec _ _ _ h) = h.
Proof.
  intros T P f g h.
  exact (homotweqinvweq (weqtoforallpaths _ f g) h).
Qed.

Definition pr1_functor_eq_from_functor_iso (C : precategory_data) (D : precategory)(hs: has_homsets D)
    (H : is_category D) (F G : ob [C , D, hs]) :
   iso F G -> pr1 F = pr1 G.
Proof.
  intro A.
  apply (total2_paths (pr1_pr1_functor_eq_from_functor_iso C D _ H F G A)).
  unfold pr1_pr1_functor_eq_from_functor_iso.
  apply funextsec; intro a.
  apply funextsec; intro b.
  apply funextsec; intro f.
  rewrite transport_of_functor_map_is_pointwise.
  rewrite toforallpaths_funextsec.  
  pathvia ((inv_from_iso
        (idtoiso
           (isotoid D H
              (functor_iso_pointwise_if_iso C D _ F G A (pr2 A) a)));;
      pr2 (pr1 F) a b f);;
     idtoiso
       (isotoid D H
          (functor_iso_pointwise_if_iso C D _ F G A (pr2 A) b))).
    set (H':= double_transport_idtoiso D _ _ _ _  
         (isotoid D H (functor_iso_pointwise_if_iso C D _ F G A (pr2 A) a))
         (isotoid D H (functor_iso_pointwise_if_iso C D _ F G A (pr2 A) b))
          (pr2 (pr1 F) a b f)).
      unfold double_transport in H'. 
      apply H'; clear H'.
  rewrite idtoiso_isotoid.
  rewrite idtoiso_isotoid.
  destruct A as [A Aiso].
  simpl in *.
  pathvia 
    (inv_from_iso (functor_iso_pointwise_if_iso C D hs F G A Aiso a) ;;
       (A a ;; #G f)).
  rewrite <- assoc.
  apply maponpaths.
  apply (nat_trans_ax A).
  rewrite assoc.

  apply remove_id_left.
  - rewrite nat_trans_inv_pointwise_inv_after_p.
    set (T:= inv_from_iso (C:=[C,D,hs])(tpair _ A Aiso)). 
    set (TA:=iso_inv_after_iso (C:=[C,D,hs])(tpair _ A Aiso)).
    set (TA':= iso_after_iso_inv (C:=[C,D,hs])(tpair _ A Aiso)).
    set (TA'':=nat_trans_comp_pointwise _ _ _ _ _ _ _ _  _ TA').
    apply TA''.
  - apply idpath.
Defined.

Definition functor_eq_from_functor_iso {C : precategory_data} {D : precategory} 
  (hs: has_homsets D)
    (H : is_category D) (F G : ob [C , D, hs]) 
    (H' : iso F G) : F = G.
Proof.
  apply (functor_eq _ _ hs F G).
  apply pr1_functor_eq_from_functor_iso;
  assumption.
Defined.


Lemma idtoiso_compute_pointwise (C : precategory_data) (D : precategory) 
  (hs: has_homsets D) (F G : ob [C, D, hs])
     (p : F = G) (a : ob C) :
  functor_iso_pointwise_if_iso C D _ F G (idtoiso p) (pr2 (idtoiso p)) a =
idtoiso
  (toforallpaths (fun _ : ob C => D) (pr1 (pr1 F)) (pr1 (pr1 G))
     (base_paths (pr1 F) (pr1 G) (base_paths F G p)) a).
Proof.
  induction p.
  apply eq_iso. apply idpath.
Qed.


Lemma functor_eq_from_functor_iso_idtoiso (C : precategory_data) (D : precategory) 
  (hs: has_homsets D)
    (H : is_category D)
    (F G : ob [C, D, hs]) (p : F = G) :
  functor_eq_from_functor_iso _ H F G (idtoiso p) = p.
Proof.
  simpl; apply functor_eq_eq_from_functor_ob_eq. apply hs.
  unfold functor_eq_from_functor_iso.
  unfold functor_eq.
  rewrite base_total2_paths.
  unfold pr1_functor_eq_from_functor_iso.
  rewrite base_total2_paths.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  apply (invmaponpathsweq (weqtoforallpaths _ _ _ )).
  simpl.
  rewrite toforallpaths_funextsec.
  apply funextsec; intro a. 
  rewrite idtoiso_compute_pointwise.
  apply isotoid_idtoiso.
Qed.

Lemma idtoiso_functor_eq_from_functor_iso (C : precategory_data) (D : precategory) 
  (hs: has_homsets D)
    (H : is_category D)
    (F G : ob [C, D, hs]) (gamma : iso F G) :
        idtoiso (functor_eq_from_functor_iso _ H F G gamma) = gamma.
Proof.
  apply eq_iso.   
  simpl; apply nat_trans_eq; intro a. apply hs.
  assert (H':= idtoiso_compute_pointwise C D _ F G (functor_eq_from_functor_iso _ H F G gamma) a).
  simpl in *.
  pathvia (pr1
       (idtoiso
          (toforallpaths (fun _ : ob C => D) (pr1 (pr1 F)) (pr1 (pr1 G))
             (base_paths (pr1 F) (pr1 G)
                (base_paths F G (functor_eq_from_functor_iso hs H F G gamma))) a))).
      assert (H2 := maponpaths (@pr1 _ _ ) H').
      simpl in H2. apply H2. 
  unfold functor_eq_from_functor_iso.
  unfold functor_eq.
  rewrite base_total2_paths.
  unfold pr1_functor_eq_from_functor_iso.
  rewrite base_total2_paths.
  pathvia (pr1 (idtoiso
     (isotoid D H (functor_iso_pointwise_if_iso C D hs F G gamma (pr2 gamma) a)))).
  apply maponpaths.
  apply maponpaths.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  rewrite toforallpaths_funextsec.
  apply idpath.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma isweq_idtoiso_functorcat (C : precategory_data) (D : precategory) (H : is_category D) 
    (F G : ob [C, D, (pr2 H)]) :
   isweq (@idtoiso _ F G).
Proof.
  apply (gradth _ (functor_eq_from_functor_iso _ H F G)).
  apply functor_eq_from_functor_iso_idtoiso.
  apply idtoiso_functor_eq_from_functor_iso.
Defined.

Lemma is_category_functor_category (C : precategory_data) (D : precategory) (H : is_category D) :
   is_category [C, D, (pr2 H)].
Proof.
  split.
  - intros F G.
    apply isweq_idtoiso_functorcat.
  - intros a b.
    apply isaset_nat_trans.
    apply (pr2 H).
Qed.


Lemma functor_category_has_homsets (C D : precategory) (hs: has_homsets D):
  has_homsets [C, D, hs].
Proof.  
  intros F G.
  apply isaset_nat_trans.
  apply hs.
Qed.

Lemma functor_identity_left (C D : precategory) (F : functor C D) :
  functor_composite C C D (functor_identity C) F = F.
Proof.
  destruct F as [ [ Fob Fmor ] is ] . destruct is as [ idax compax ] . apply idpath . 
   
Defined.



Lemma functor_identity_right (C D : precategory) (F : functor C D) :
  functor_composite C D D F (functor_identity D) = F.
Proof.
  destruct F as [ [ Fob Fmor ] is ] .
  apply ( maponpaths ( fun p => tpair is_functor (tpair _ Fob Fmor) p ) ) .
  destruct is as [ idax compax ] . 
  apply pathsdirprod .
  simpl . apply funextsec . intro t . unfold functor_identity .  unfold functor_id . simpl .
  rewrite maponpathsidfun . 
  rewrite pathscomp0rid . 
  apply idpath . 

  apply funextsec . intro t . apply funextsec . intro t0 . apply funextsec . intro t1 . 
  apply funextsec . intro f . apply funextsec . intro g . unfold functor_identity . simpl . 
  unfold functor_comp . simpl .
  rewrite maponpathsidfun . 
  rewrite pathscomp0rid . 
  apply idpath.

Defined.

(** Note: the following should be somewhere upstream: *)

Lemma pathscomp0assoc { X : UU } { a b c d : X } ( e1 : a = b ) ( e2 : b = c ) ( e3 : c = d ) :
  e1 @ ( e2 @ e3 ) = ( e1 @ e2 ) @ e3 .
Proof.
  intros . destruct e1 . destruct e2 . apply idpath .
Defined.


Lemma functor_assoc (C0 C1 C2 C3 : precategory) 
  (F0 : functor C0 C1) (F1 : functor C1 C2) (F2 : functor C2 C3) :
    functor_composite _ _ _ (functor_composite _ _ _ F0 F1) F2 =
    functor_composite _ _ _ F0 (functor_composite _ _ _ F1 F2).
Proof.
  destruct F0 as [ [ F0ob F0mor ] is0 ] .  
  destruct F1 as [ [ F1ob F1mor ] is1 ] .
  destruct F2 as [ [ F2ob F2mor ] is2 ] . simpl .
  unfold functor_composite . simpl . 
  apply ( maponpaths ( fun p => tpair is_functor _ p ) ) . simpl . 
  apply pathsdirprod .
  apply funextsec . 
  intro t .
  
  simpl .
  unfold functor_comp . simpl . unfold functor_id . simpl . unfold functor_id . simpl . 
  destruct is0 as [ is0id is0comp ] .
  destruct is1 as [ is1id is1comp ] .
  destruct is2 as [ is2id is2comp ] .
  simpl .

  rewrite pathscomp0assoc . 
  apply ( maponpaths ( fun e => pathscomp0 e ( is2id (F1ob (F0ob t)) ) ) ) .
  rewrite maponpathscomp0 .
  apply ( maponpaths ( fun e => pathscomp0 e ( maponpaths
                                                 (F2mor (F1ob (F0ob t)) (F1ob (F0ob t)))
                                                 (is1id (F0ob t)) ) ) ) .
  apply maponpathscomp . 

  apply funextsec . intro t . apply funextsec . intro t0 . apply funextsec . intro t1 . 
  apply funextsec . intro f . apply funextsec . intro g .

  simpl . 
  unfold functor_comp . simpl . unfold functor_comp .  simpl . 
  destruct is0 as [ is0id is0comp ] .
  destruct is1 as [ is1id is1comp ] .
  destruct is2 as [ is2id is2comp ] .
  simpl .

  rewrite pathscomp0assoc . 
  apply ( maponpaths ( fun e =>
                         pathscomp0 e ( is2comp (F1ob (F0ob t)) (F1ob (F0ob t0)) (F1ob (F0ob t1))
                                                (F1mor (F0ob t) (F0ob t0) (F0mor t t0 f))
                                                (F1mor (F0ob t0) (F0ob t1) (F0mor t0 t1 g)) ) ) ) .
  rewrite maponpathscomp0 .
  apply ( maponpaths ( fun e =>
                         pathscomp0 e ( maponpaths (F2mor (F1ob (F0ob t)) (F1ob (F0ob t1)))
                                                   (is1comp (F0ob t) (F0ob t0) (F0ob t1)
                                                            (F0mor t t0 f) (F0mor t0 t1 g)) ))).
  apply maponpathscomp . 

  Defined.
