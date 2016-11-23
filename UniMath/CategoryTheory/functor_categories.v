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


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).




(** * Functors : Morphisms of precategories *)


Definition functor_data (C C' : precategory_ob_mor) :=
  total2 ( fun F : ob C -> ob C' =>  Π a b : ob C, a --> b -> F a --> F b).

Definition functor_data_constr ( C C' : precategory_ob_mor )
           ( F : ob C -> ob C' ) ( Fm : Π a b : ob C, a --> b -> F a --> F b ) :
  functor_data C C' := tpair _ F Fm .

Definition functor_on_objects {C C' : precategory_ob_mor}
     (F : functor_data C C') :  ob C -> ob C' := pr1 F.
Coercion functor_on_objects : functor_data >-> Funclass.


Definition functor_on_morphisms {C C' : precategory_ob_mor} (F : functor_data C C')
  { a b : ob C} :  a --> b -> F a --> F b := pr2 F a b.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Definition functor_idax {C C' : precategory_data} (F : functor_data C C') :=
  Π a : ob C, #F (identity a) = identity (F a).

Definition functor_compax {C C' : precategory_data} (F : functor_data C C') :=
  Π a b c : ob C, Π f : a --> b, Π g : b --> c, #F (f ;; g) = #F f ;; #F g .

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
  apply (invmaponpathsweq (total2_paths_equiv _ _ _ )); simpl.
  assert (H' : base_paths _ _ p = base_paths _ _ q).
  { apply (invmaponpathsweq (total2_paths_equiv _ _ _ )); simpl.
    apply (total2_paths2 H), uip.
    apply impred_isaset; intro a; apply impred_isaset; intro b; apply impred_isaset; intro f.
    apply hs.
  }
  apply (total2_paths2 H'), uip, isasetaprop, isaprop_is_functor, hs.
Defined.

Definition functor_id {C C' : precategory_data}(F : functor C C'):
       Π a : ob C, #F (identity a) = identity (F a) := pr1 (pr2 F).


Definition functor_comp {C C' : precategory_data}
      (F : functor C C'):
       Π a b c : ob C, Π f : a --> b,
                 Π g : b --> c,
                #F (f ;; g) = #F f ;; #F g := pr2 (pr2 F).


Lemma functor_id_id (A B : precategory) (G : functor A B) (a : A) (f : a --> a)
  : f = identity _ -> #G f = identity _ .
Proof.
  intro e.
  pathvia (#G (identity a )).
  - apply maponpaths. apply e.
  - apply functor_id.
Defined.




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


Definition functor_on_iso {C C' : precategory} (F : functor C C')
    {a b : ob C}(f : iso a b) : iso (F a) (F b).
Proof.
  exists (#F f).
  apply functor_on_iso_is_iso.
Defined.

Lemma functor_on_iso_inv (C C' : precategory) (F : functor C C')
    (a b : ob C) (f : iso a b) :
   functor_on_iso F (iso_inv_from_iso f) =
       iso_inv_from_iso (functor_on_iso F f).
Proof.
  apply eq_iso; simpl.
  apply inv_iso_unique'; simpl.
  unfold precomp_with. rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  apply functor_id.
Defined.

(** ** Functors and [idtoiso] *)

Section functors_and_idtoiso.

Variables C D : precategory.
Variable F : functor C D.

Lemma maponpaths_idtoiso (a b : C) (e : a = b)
: idtoiso (maponpaths (functor_on_objects F) e)
  =
  functor_on_iso F (idtoiso e).
Proof.
  induction e.
  apply eq_iso.
  apply (! functor_id _ _ ).
Qed.

Hypothesis HC : is_category C.
Hypothesis HD : is_category D.

Lemma maponpaths_isotoid (a b : C) (i : iso a b)
: maponpaths (functor_on_objects F) (isotoid _ HC i)
  =
  isotoid _ HD (functor_on_iso F i).
Proof.
  apply (invmaponpathsweq (weqpair (idtoiso) (pr1 HD _ _ ))).
  simpl.
  rewrite maponpaths_idtoiso.
  repeat rewrite idtoiso_isotoid.
  apply idpath.
Qed.

End functors_and_idtoiso.


(** ** Functors preserve inverses *)

Lemma functor_on_inv_from_iso (C C' : precategory) (F : functor C C')
    (a b : ob C)(f : iso a b) :
      #F (inv_from_iso f) = inv_from_iso (functor_on_iso F f) .
Proof.
  apply inv_iso_unique'; simpl.
  unfold precomp_with. rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  apply functor_id.
Qed.


(** ** Fully faithful functors *)

Definition fully_faithful {C D : precategory_data} (F : functor C D) :=
  Π a b : ob C,
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
    {a b : ob C} (f : iso (F a) (F b)) :
      iso a b.
Proof.
  exists (fully_faithful_inv_hom HF a b f).
  apply fully_faithful_reflects_iso_proof.
Defined.

Lemma functor_on_iso_iso_from_fully_faithful_reflection (C D : precategory)
      (F : functor C D) (HF : fully_faithful F) (a b : ob C)
   (f : iso (F a) (F b)) :
      functor_on_iso F
        (iso_from_fully_faithful_reflection HF f) = f.
Proof.
  apply eq_iso.
  simpl;
  apply (homotweqinvweq (weq_from_fully_faithful HF a b)).
Qed.

Lemma iso_from_fully_faithful_reflection_functor_on_iso (C D : precategory)
      (F : functor C D) (HF : fully_faithful F) (a b : ob C)
   (f : iso a b) :
      iso_from_fully_faithful_reflection HF (functor_on_iso F f) = f.
Proof.
  apply eq_iso.
  simpl;
  apply (homotinvweqweq (weq_from_fully_faithful HF a b)).
Qed.

Definition weq_ff_functor_on_iso {C D : precategory}{F : functor C D}
           (HF : fully_faithful F) (a b : ob C)
  : iso a b ≃ iso (F a) (F b).
Proof.
  exists (functor_on_iso F).
  apply (gradth _ (iso_from_fully_faithful_reflection HF (a:=a)(b:=b))).
  - apply iso_from_fully_faithful_reflection_functor_on_iso.
  - apply functor_on_iso_iso_from_fully_faithful_reflection.
Defined.

(** Computation check *)

Lemma weq_ff_functor_on_iso_compute {C D : precategory} (F : functor C D)
      (HF : fully_faithful F) {a b : C} (f : iso a b)
: #F f = weq_ff_functor_on_iso HF _ _ f.
Proof.
apply idpath.
Qed.

Lemma functor_on_iso_iso_from_ff_reflection (C D : precategory)
      (F : functor C D) (HF : fully_faithful F) (a b : C)
      (f : iso (F a) (F b)):
  functor_on_iso F
                 (iso_from_fully_faithful_reflection HF f) = f.
Proof.
  apply eq_iso.
  simpl.
  apply (homotweqinvweq (weq_from_fully_faithful HF a b ) ).
Qed.


(** Alternative implementation of [weq_ff_functor_on_iso] *)

Lemma ff_reflects_is_iso (C D : precategory) (F : functor C D)
  (HF : fully_faithful F) (a b : C) (f : a --> b)
  : is_iso (# F f) -> is_iso f.
Proof.
  intro H.
  set (X:= fully_faithful_reflects_iso_proof _ _ F HF _ _ (isopair _ H)).
  simpl in X.
  set (T:= homotinvweqweq (weq_from_fully_faithful HF a b ) ).
  simpl in T.
  unfold fully_faithful_inv_hom in X.
  simpl in X.
  rewrite T in X.
  apply X.
Defined.


Definition weq_ff_functor_on_iso_weqbandf {C D : precategory}
  {F : functor C D}
  (HF : fully_faithful F) (a b : C)
  : iso a b ≃ iso (F a) (F b).
Proof.
  simple refine (weqbandf _ _ _ _ ).
  - apply (weqpair _ (HF a b)).
  - simpl; intro f.
    apply weqimplimpl.
    + intro H.
      apply (functor_on_iso_is_iso _ _ _ _ _ (isopair f H)).
    + apply ff_reflects_is_iso. apply HF.
    + apply isaprop_is_iso.
    + apply isaprop_is_iso.
Defined.

(** Computation check *)

Lemma weq_ff_functor_on_iso_weqbandf_compute {C D : precategory} (F : functor C D)
      (HF : fully_faithful F) {a b : C} (f : iso a b)
: #F f = weq_ff_functor_on_iso_weqbandf HF _ _ f.
Proof.
  apply idpath.
Defined.

Lemma ff_is_inclusion_on_objects {C D : precategory}
      (HC : is_category C) (HD : is_category D)
      (F : functor C D) (HF : fully_faithful F)
      : isofhlevelf 1 (functor_on_objects F).
Proof.
  intro d.
  apply invproofirrelevance.
  intros [c e] [c' e'].
  simple refine (total2_paths _ _ ).
  - simpl.
    set (X := idtoiso (e @ ! e')).
    (* set (X' := invmap (@weq_ff_functor_on_iso _ _ _ HF _ _ ) X). *)
        (* we cannot use X' because we lack the preceding, commented-out,
           lemma *)
    set (X2 := iso_from_fully_faithful_reflection HF X).
    apply (isotoid _ HC X2).
  - simpl.
    set (T:=@functtransportf _ _ (functor_on_objects F)).
    set (T' := T (fun c => c = d)). simpl in T'.
    rewrite T'.
    rewrite (maponpaths_isotoid _ _ _ HC HD).
    rewrite functor_on_iso_iso_from_ff_reflection.
    rewrite isotoid_idtoiso.
    rewrite transportf_id2.
    rewrite pathscomp_inv.
    rewrite pathsinv0inv0.
    rewrite <- path_assoc.
    rewrite pathsinv0l.
    apply pathscomp0rid.
Qed.


(** ** Essentially surjective functors *)

Definition essentially_surjective {C D : precategory_data} (F : functor C D) :=
  Π b, ishinh (total2 (fun a => iso (F a) b)).

(** ** Faithful functors *)

Definition faithful {C D : precategory_data} (F : functor C D) :=
  Π a b : ob C, isincl (fun f : a --> b => #F f).

Lemma isaprop_faithful (C D : precategory_data) (F : functor C D) :
   isaprop (faithful F).
Proof.
  repeat (apply impred; intro).
  apply isapropiscontr.
Qed.

(** ** Full functors *)


Definition full {C D : precategory_data} (F : functor C D) :=
   Π a b: C, issurjective (fun f : a --> b => #F f).



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


Definition functor_composite {C C' C'' : precategory_data} (F : functor C C') (F' : functor C' C'') :
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

Lemma identity_functor_is_fully_faithful { C : precategory_data }
  : fully_faithful (functor_identity C).
Proof.
  intros a b.
  apply idisweq.
Defined.

(** *** Constant functor *)

Section Constant_Functor.
Variables C D : precategory.
Variable d : D.

Definition constant_functor_data: functor_data C D :=
   functor_data_constr C D (fun _ => d) (fun _ _ _  => identity _) .

Lemma is_functor_constant: is_functor constant_functor_data.
Proof.
  split; simpl.
  red; intros; apply idpath.
  red; intros; simpl.
  apply pathsinv0.
  apply id_left.
Qed.

Definition constant_functor: functor C D := tpair _ _ is_functor_constant.

End Constant_Functor.





(** * Natural transformations *)


(** ** Definition of natural transformations *)

Definition is_nat_trans {C C' : precategory_data}
  (F F' : functor_data C C')
  (t : Π x : ob C, F x -->  F' x) :=
  Π (x x' : ob C)(f : x --> x'),
    #F f ;; t x' = t x ;; #F' f.


Lemma isaprop_is_nat_trans (C C' : precategory_data) (hs: has_homsets C')
  (F F' : functor_data C C') (t : Π x : ob C, F x -->  F' x):
  isaprop (is_nat_trans F F' t).
Proof.
  repeat (apply impred; intro).
  apply hs.
Qed.


Definition nat_trans {C C' : precategory_data}
  (F F' : functor_data C C') := total2 (
   fun t : Π x : ob C, F x -->  F' x => is_nat_trans F F' t).

Lemma isaset_nat_trans {C C' : precategory_data} (hs: has_homsets C')
  (F F' : functor_data C C') : isaset (nat_trans F F').
Proof.
  apply (isofhleveltotal2 2).
  + apply impred; intro t; apply hs.
  + intro x; apply isasetaprop, isaprop_is_nat_trans, hs.
Qed.

Definition nat_trans_data {C C' : precategory_data}
 {F F' : functor_data C C'}(a : nat_trans F F') :
   Π x : ob C, F x --> F' x := pr1 a.
Coercion nat_trans_data : nat_trans >-> Funclass.

Definition nat_trans_ax {C C' : precategory_data}
  {F F' : functor_data C C'} (a : nat_trans F F') :
  Π (x x' : ob C)(f : x --> x'),
    #F f ;; a x' = a x ;; #F' f := pr2 a.

(** Equality between two natural transformations *)

Lemma nat_trans_eq {C C' : precategory_data} (hs: has_homsets C')
  (F F' : functor_data C C')(a a' : nat_trans F F'):
  (Π x, a x = a' x) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  { now apply funextsec. }
  apply (total2_paths H'), proofirrelevance, isaprop_is_nat_trans, hs.
Qed.

Definition nat_trans_eq_pointwise {C C' : precategory_data}
   {F F' : functor_data C C'} {a a' : nat_trans F F'}:
      a = a' -> Π x, a x = a' x.
Proof.
  intro h.
  now apply toforallpaths, maponpaths.
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
  now rewrite id_left, id_right.
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
  intros ? ? ?.
  now rewrite assoc, nat_trans_ax, <- assoc, nat_trans_ax, assoc.
Qed.


Definition nat_trans_comp {C:precategory_data}{C' : precategory}
  (F G H: functor_data C C')
  (a : nat_trans F G)
  (b : nat_trans G H): nat_trans F H :=
    tpair _ _ (is_nat_trans_comp a b).


(** *** The data of the functor precategory *)

Definition functor_precategory_data (C : precategory_data)(C' : precategory): precategory_data.
Proof.
  apply (precategory_data_pair (functor_precategory_ob_mor C C')).
  + intro a; simpl.
    apply (nat_trans_id (pr1 a)).
  + intros a b c f g.
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

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Definition functor_identity_as_ob (C : precategory) (hsC : has_homsets C)
  : [C, C, hsC]
  := (functor_identity C).

Definition functor_composite_as_ob {C C' C'' : precategory}
  {hsC' : has_homsets C'} {hsC'' : has_homsets C''}
  (F : [C, C', hsC']) (F' : [C', C'', hsC'']) :
  [C, C'', hsC''] := tpair _ _ (is_functor_composite F F').

Lemma nat_trans_comp_pointwise (C : precategory_data)(C' : precategory) (hs: has_homsets C')
  (F G H : ob [C, C', hs]) (A : F --> G) (A' : G --> H)
   (B : F --> H) : A ;; A' = B ->
        Π a, pr1 A a ;; pr1 A' a = pr1 B a.
Proof.
  intros H' a.
  pathvia (pr1 (A ;; A') a).
  apply idpath.
  destruct H'.
  apply idpath.
Defined.

Section nat_trans_eq.

Context {C D : precategory}.
Variable hsD : has_homsets D.
Context {F G : functor C D}.
Variables alpha beta : nat_trans F G.

Definition nat_trans_eq_weq : weq (alpha = beta) (Π c, alpha c = beta c).
Proof.
  eapply weqcomp.
  - apply subtypeInjectivity.
    intro x. apply isaprop_is_nat_trans. apply hsD.
  - apply weqtoforallpaths.
Defined.
End nat_trans_eq.


(** Characterizing isomorphisms in the functor category *)

Lemma is_nat_trans_inv_from_pointwise_inv_ext {C : precategory_data} {D : precategory}
  (hs: has_homsets D)
  {F G : functor_data C D} {A : nat_trans F G}
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

Lemma is_nat_trans_inv_from_pointwise_inv (C : precategory_data)(D : precategory)
  (hs: has_homsets D)
  (F G : ob [C,D,hs]) (A : F --> G)
  (H : forall a : ob C, is_isomorphism (pr1 A a)) :
  is_nat_trans _ _
     (fun a : ob C => inv_from_iso (tpair _ _ (H a))).
Proof.
  apply is_nat_trans_inv_from_pointwise_inv_ext.
  exact hs.
Qed.

Definition nat_trans_inv_from_pointwise_inv (C : precategory_data)(D : precategory)
  (hs: has_homsets D)
  (F G : ob [C,D,hs]) (A : F --> G)
  (H : Π a : ob C, is_isomorphism (pr1 A a)) :
    G --> F := tpair _ _ (is_nat_trans_inv_from_pointwise_inv _ _ _ _ _ _ H).

Definition nat_trans_inv_from_pointwise_inv_ext {C : precategory_data}{D : precategory}
  (hs: has_homsets D)
  {F G : functor_data C D} (A : nat_trans F G)
  (H : forall a : ob C, is_isomorphism (pr1 A a)) :
    nat_trans G F := tpair _ _ (is_nat_trans_inv_from_pointwise_inv_ext hs H).

Lemma nat_trans_inv_is_iso {C : precategory_data}{D : precategory}
  (hs: has_homsets D)
  {F G : functor_data C D} (A : nat_trans F G)
  (H : forall a : ob C, is_isomorphism (pr1 A a)) :
  forall a : ob C, is_isomorphism ((nat_trans_inv_from_pointwise_inv_ext hs A H) a).
Proof.
  intros a.
  apply is_iso_inv_from_iso.
Defined.

Lemma is_inverse_nat_trans_inv_from_pointwise_inv (C : precategory_data)(C' : precategory) (hs: has_homsets C')
    (F G : [C, C', hs]) (A : F --> G)
   (H : Π a : C, is_isomorphism (pr1 A a)) :
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
   (Π a : ob C, is_isomorphism (pr1 A a)) ->
           is_isomorphism A .
Proof.
  intro H.
  apply (is_iso_qinv _ (nat_trans_inv_from_pointwise_inv _ _ _ _ _ _ H)).
  simpl; apply is_inverse_nat_trans_inv_from_pointwise_inv.
Defined.

Definition functor_iso_from_pointwise_iso (C : precategory_data)(C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G)
   (H : Π a : ob C, is_isomorphism (pr1 A a)) :
     iso F G :=
 tpair _ _ (functor_iso_if_pointwise_iso _ _ _ _ _ _ H).


Lemma is_functor_iso_pointwise_if_iso (C : precategory_data)(C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) :
  is_isomorphism A ->
       Π a : ob C, is_isomorphism (pr1 A a).
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
       Π a : C, pr1 (inv_from_iso (isopair A Aiso)) a ;; pr1 A a = identity _ .
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
       Π a : C, pr1 A a ;; pr1 (inv_from_iso (isopair A Aiso)) a = identity _ .
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
     Π a : ob C,
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
    (F1 : Π a b : ob C, a --> b -> F0 a --> F0 b)
   (gamma : F0  = G0 )
    (a b : ob C) (f : a --> b) :
transportf (fun x : ob C -> ob D =>
            Π a0 b0 : ob  C, a0 --> b0 -> x a0 --> x b0)
           gamma  F1 a b f =
transportf (fun TT : ob D => G0 a --> TT)
  (toforallpaths (fun _ : ob C => D) F0 G0 gamma b)
  (transportf (fun SS : ob D => SS --> F0 b)
     (toforallpaths (fun _ : ob C => D) F0 G0 gamma a) (F1 a b f)).
Proof.
  induction gamma.
  apply idpath.
Defined.

Lemma toforallpaths_funextsec : Π (T : UU) (P : T -> UU) (f g : Π t : T, P t)
          (h : Π t : T, f t = g t),
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


Definition functor_Precategory (C : precategory) (D : Precategory) : Precategory.
Proof.
  exists (functor_precategory C D (homset_property D)).
  apply functor_category_has_homsets.
Defined.

Lemma functor_identity_left (C D : precategory) (F : functor C D) :
  functor_composite (functor_identity C) F = F.
Proof.
  destruct F as [ [ Fob Fmor ] is ].
  destruct is as [ idax compax ] .
  apply idpath .
Defined.



Lemma functor_identity_right (C D : precategory) (F : functor C D) :
  functor_composite F (functor_identity D) = F.
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

Lemma functor_assoc (C0 C1 C2 C3 : precategory)
  (F0 : functor C0 C1) (F1 : functor C1 C2) (F2 : functor C2 C3) :
    functor_composite (functor_composite F0 F1) F2 =
    functor_composite F0 (functor_composite F1 F2).
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

  rewrite path_assoc.
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

  rewrite path_assoc.
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


Definition iter_functor {C : precategory} (F : functor C C) (n : nat) : functor C C.
Proof.
  induction n as [ | n IHn].
  - apply functor_identity.
  - apply (functor_composite IHn F).
Defined.
