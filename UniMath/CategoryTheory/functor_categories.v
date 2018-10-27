(** * Functors, natural transformations, and functor categories

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)

*)


(** ** Contents:

  - Functors
    - preserve isos, inverses
    - Conservative functors ([conservative])
    - Composition of functors, identity functors
    - fully faithful functors
      - preserve isos, inverses, composition backwards
    - (Split) essentially surjective functors
    - faithful
    - full
    - fully faithful is the same as full and faithful
    - Image of a functor, full subcat specified by a functor

  - Natural transformations
    - Equality is pointwise equality.

  - Functor (pre)category
    - Isomorphisms in functor category are pointwise isomorphisms

    - Isomorphic Functors are equal if target precategory is univalent_category
      [functor_eq_from_functor_iso]

    - Functor precategory is univalent_category if target precategory is
      [is_univalent_functor_category]

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.

Local Open Scope cat.

(** * Functors : Morphisms of precategories *)
Section functors.

Definition functor_data (C C' : precategory_ob_mor) : UU :=
  total2 ( fun F : ob C -> ob C' =>  ∏ a b : ob C, a --> b -> F a --> F b).

Definition mk_functor_data {C C' : precategory_ob_mor} (F : ob C -> ob C')
           (H : ∏ a b : ob C, a --> b -> F a --> F b) : functor_data C C' := tpair _ F H.

Lemma functor_data_isaset (C C' : precategory_ob_mor) (hs : has_homsets C') (hsC' : isaset C') :
  isaset (functor_data C C').
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply impred; intro.
  apply hsC'.
  intro.
  do 3 (apply impred; intro).
  apply hs.
Qed.

Definition functor_data_constr (C C' : precategory_ob_mor)
           (F : ob C -> ob C') (Fm : ∏ a b : ob C, a --> b -> F a --> F b) :
  functor_data C C' := tpair _ F Fm .

Definition functor_on_objects {C C' : precategory_ob_mor}
     (F : functor_data C C') :  ob C -> ob C' := pr1 F.
Coercion functor_on_objects : functor_data >-> Funclass.

Definition functor_on_morphisms {C C' : precategory_ob_mor} (F : functor_data C C')
  { a b : ob C} :  a --> b -> F a --> F b := pr2 F a b.

Notation "# F" := (functor_on_morphisms F) (at level 3) : cat.

Definition functor_idax {C C' : precategory_data} (F : functor_data C C') :=
  ∏ a : ob C, #F (identity a) = identity (F a).

Definition functor_compax {C C' : precategory_data} (F : functor_data C C') :=
  ∏ a b c : ob C, ∏ f : a --> b, ∏ g : b --> c, #F (f · g) = #F f · #F g .

Definition is_functor {C C' : precategory_data} (F : functor_data C C') :=
  ( functor_idax F ) × ( functor_compax F ) .

Lemma isaprop_is_functor (C C' : precategory_data) (hs: has_homsets C')
      (F : functor_data C C') : isaprop (is_functor F).
Proof.
  apply isofhleveldirprod.
  apply impred; intro.
  apply hs.
  do 5 (apply impred; intro).
  apply hs.
Qed.

Definition functor (C C' : precategory_data) : UU :=
  total2 ( λ F : functor_data C C', is_functor F ).

Notation "a ⟶ b" := (functor a b) (at level 39) : cat.
(* to input: type "\-->" with Agda input method *)

(** Note that this makes the second component opaque for efficiency reasons *)
Definition mk_functor {C C' : precategory_data} (F : functor_data C C') (H : is_functor F) :
  functor C C'.
Proof.
exists F.
abstract (exact H).
Defined.

Lemma functor_data_eq_prf (C C': precategory_ob_mor) (F F' : functor_data C C')
      (H : ∏ c, F c = F' c)
      (H1 : ∏ C1 C2 (f : C1 --> C2),
            double_transport (H C1) (H C2) (pr2 F C1 C2 f) =
            pr2 F' C1 C2 f) :
  transportf (λ x : C → C', ∏ a b : C, C ⟦ a, b ⟧ → C' ⟦ x a, x b ⟧)
    (funextfun F F' (λ c : C, H c)) (pr2 F) = pr2 F'.
Proof.
use funextsec. intros C1. use funextsec. intros C2. use funextsec. intros f.
assert (e : transportf (λ x, ∏ a b : C, a --> b → x a --> x b)
                       (funextfun F F' (λ c : C, H c)) (pr2 F) C1 C2 f =
            transportf (λ x, x C1 --> x C2)
                       (funextfun F F' (λ c : C, H c)) (pr2 F C1 C2 f)).
{ now induction (funextfun F F' (λ c, H c)). }
rewrite e, transport_mor_funextfun, transport_source_funextfun, transport_target_funextfun.
exact (H1 C1 C2 f).
Qed.

Lemma functor_data_eq (C C': precategory_ob_mor) (F F' : functor_data C C')
      (H : F ~ F') (H1 : ∏ C1 C2 (f : C1 --> C2),
            double_transport (H C1) (H C2) (pr2 F C1 C2 f) =
            pr2 F' C1 C2 f) :
      F = F'.
Proof.
use total2_paths_f.
- use funextfun. intros c. exact (H c).
- now apply functor_data_eq_prf.
Defined.



Lemma functor_eq (C C' : precategory_data) (hs: has_homsets C') (F F': functor C C'):
    pr1 F = pr1 F' -> F = F'.
Proof.
  intro H.
  apply (total2_paths_f H).
  apply proofirrelevance.
  apply isaprop_is_functor.
  apply hs.
Defined.

Lemma functor_isaset (C C' : precategory_data) (hs : has_homsets C') (hsC' : isaset C') :
  isaset (functor C C').
Proof.
  change isaset with (isofhlevel 2).
  apply isofhleveltotal2.
  apply (functor_data_isaset C C' hs hsC').
  intros x.
  apply isasetaprop.
  apply (isaprop_is_functor C C' hs).
Qed.

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
    apply (two_arg_paths_f H), uip.
    apply impred_isaset; intro a; apply impred_isaset; intro b; apply impred_isaset; intro f.
    apply hs.
  }
  apply (two_arg_paths_f H'), uip, isasetaprop, isaprop_is_functor, hs.
Defined.

Definition functor_id {C C' : precategory_data}(F : functor C C'):
       ∏ a : ob C, #F (identity a) = identity (F a) := pr1 (pr2 F).


Definition functor_comp {C C' : precategory_data}
           (F : functor C C') {a b c : C} (f : a --> b) (g : b --> c)
  : #F (f · g) = #F f · #F g
  := pr2 (pr2 F) _ _ _ _ _ .


Lemma functor_id_id (A B : precategory) (G : functor A B) (a : A) (f : a --> a)
  : f = identity _ -> #G f = identity _ .
Proof.
  intro e.
  intermediate_path (#G (identity a )).
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

Lemma functor_on_is_iso_is_iso {C C' : precategory} {F : functor C C'}
      {a b : ob C} {f : a --> b} (H : is_iso f)  : is_iso (#F f).
Proof.
  apply (is_iso_qinv _ (#F (inv_from_iso (isopair _ H)))).
  apply (is_inverse_functor_image _ _ _ _ _ (isopair _ H)).
Qed.

Lemma functor_on_iso_is_iso (C C' : precategory) (F : functor C C')
    (a b : ob C) (f : iso a b) : is_iso (#F f).
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

Lemma functor_on_inv_from_iso' {C C' : precategory} (F : functor C C')
      {a b : ob C} {f : a --> b} (H : is_iso f) :
  inv_from_iso (isopair _ (functor_on_is_iso_is_iso H)) = # F (inv_from_iso (isopair _ H)).
Proof.
  apply pathsinv0. use inv_iso_unique'. cbn. unfold precomp_with.
  rewrite <- functor_comp. set (tmp := iso_inv_after_iso (isopair _ H)). cbn in tmp.
  rewrite tmp. apply functor_id.
Qed.

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

Hypothesis HC : is_univalent C.
Hypothesis HD : is_univalent D.

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

Notation "# F" := (functor_on_morphisms F)(at level 3) : cat. (* Notations do not survive the end of sections.  *)

(** ** Functors preserve inverses *)

Lemma functor_on_inv_from_iso {C C' : precategory} (F : functor C C')
    {a b : ob C}(f : iso a b) :
      #F (inv_from_iso f) = inv_from_iso (functor_on_iso F f) .
Proof.
  apply inv_iso_unique'; simpl.
  unfold precomp_with. rewrite <- functor_comp.
  rewrite iso_inv_after_iso.
  apply functor_id.
Qed.

(** ** Conservative functors *)

(** The generic property of "reflecting" a property of a morphism. *)

Definition reflects_morphism {C D : precategory} (F : functor C D)
           (P : ∏ (C : precategory) (a b : ob C), C⟦a, b⟧ → UU) : UU :=
  ∏ a b f, P D (F a) (F b) (# F f) → P C a b f.

(** These are functors that reflect isomorphisms. F : C ⟶ D is conservative
    if whenever # F f is an iso, so is f. *)

Definition conservative {C D : precategory} (F : functor C D) : UU :=
  reflects_morphism F (@is_iso).

(** ** Composition of functors, identity functors *)

(** *** Composition *)

Definition functor_composite_data {C C' C'' : precategory_ob_mor } (F : functor_data C C')
           (F' : functor_data C' C'') : functor_data C C'' :=
  functor_data_constr C C'' (λ a, F' (F a))  (λ (a b : ob C) f, #F' (#F f)) .


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
  assert ( e1 := functor_comp F f g ) .
  assert ( e2 := functor_comp F' ( # F f ) ( # F g ) ) .
  apply ( ( maponpaths ( # F' ) e1 ) @ e2 ) .
Defined.


Definition functor_composite {C C' C'' : precategory_data} (F : functor C C') (F' : functor C' C'') :
  functor C C'' := tpair _ _ (is_functor_composite F F').

(** *** Identity functor *)

Definition functor_identity_data ( C  : precategory_data ) : functor_data C C :=
  functor_data_constr C C (λ a, a) (λ (a b : ob C) f, f) .

Lemma is_functor_identity (C : precategory_data) : is_functor ( functor_identity_data C ) .
Proof.
  split; simpl.
  unfold functor_idax. intros; apply idpath.
  unfold functor_compax. intros; apply idpath.
Defined.

Definition functor_identity (C : precategory_data) : functor C C :=
  tpair _ _ ( is_functor_identity C ) .

(** *** Constant functor *)

Section Constant_Functor.
Variables C D : precategory.
Variable d : D.

Definition constant_functor_data: functor_data C D :=
   functor_data_constr C D (λ _, d) (λ _ _ _ , identity _) .

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

Definition iter_functor {C : precategory} (F : functor C C) (n : nat) : functor C C.
Proof.
  induction n as [ | n IHn].
  - apply functor_identity.
  - apply (functor_composite IHn F).
Defined.

End functors.

(** Notations do not survive the end of sections, so we redeclare them here. *)
Notation "a ⟶ b" := (functor a b) (at level 39) : cat.
Notation "# F" := (functor_on_morphisms F) (at level 3) : cat.

(** ** Fully faithful functors *)

Definition fully_faithful {C D : precategory_data} (F : functor C D) :=
  ∏ a b : ob C,
    isweq (functor_on_morphisms F (a:=a) (b:=b)).

Lemma isaprop_fully_faithful (C D : precategory_data) (F : functor C D) :
   isaprop (fully_faithful F).
Proof.
  apply impred; intro a.
  apply impred; intro b.
  apply isapropisweq.
Qed.

Lemma identity_functor_is_fully_faithful { C : precategory_data }
  : fully_faithful (functor_identity C).
Proof.
  intros a b.
  apply idisweq.
Defined.

Definition weq_from_fully_faithful {C D : precategory_data}{F : functor C D}
      (FF : fully_faithful F) (a b : ob C) :
   (a --> b) ≃ (F a --> F b).
Proof.
  exists (functor_on_morphisms F (a:=a) (b:=b)).
  exact (FF a b).
Defined.

Definition fully_faithful_inv_hom {C D : precategory_data} {F : functor C D}
      (FF : fully_faithful F) (a b : ob C) :
      F a --> F b -> a --> b :=
 invweq (weq_from_fully_faithful FF a b).

Local Notation "FF ^-1" := (fully_faithful_inv_hom FF _ _ ) (at level 20).

(** FF^1 is indeed post-inverse to # F. *)
Lemma fully_faithful_inv_hom_is_inv {C D : precategory} {F : functor C D}
      (FF : fully_faithful F) {a b : ob C} (f : C⟦a, b⟧) :
  FF^-1 (# F f) = f.
Proof.
  cbn.
  apply invmap_eq.
  reflexivity.
Defined.

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
        FF^-1 (f · g) = FF^-1 f · FF^-1 g.
Proof.
  apply (invmaponpathsweq (weq_from_fully_faithful FF a c)).
  set (HFFac := homotweqinvweq (weq_from_fully_faithful FF a c)
                 (f · g)).
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
     is_iso (FF^-1 f).
Proof.
  apply (is_iso_qinv _ (FF^-1 (inv_from_iso f))).
  apply inv_of_ff_inv_is_inv.
Defined.

(** A slight restatement of the above: fully faithful functors are conservative. *)
Lemma fully_faithful_conservative {C D : precategory} (F : functor C D)
      (FF : fully_faithful F) : conservative F.
Proof.
  unfold conservative.
  intros a b f is_iso_Ff.
  use transportf.
  - exact (FF^-1 (# F f)).
  - apply fully_faithful_inv_hom_is_inv.
  - apply (fully_faithful_reflects_iso_proof _ _ _ _ _ _ (isopair _ is_iso_Ff)).
Defined.

Definition  iso_from_fully_faithful_reflection {C D : precategory} {F : functor C D}
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
  apply (isweq_iso _ (iso_from_fully_faithful_reflection HF (a:=a)(b:=b))).
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

Definition reflects_isos {C D : precategory} (F : C ⟶ D) :=
  ∏ c c' (f : C⟦c,c'⟧), is_iso (# F f) → is_iso f.

Lemma isaprop_reflects_isos {C D : precategory} (F : C ⟶ D) : isaprop (reflects_isos F).
Proof.
apply impred; intros c; apply impred; intros c'.
apply impred; intros f; apply impred; intros f'.
apply isaprop_is_iso.
Qed.

Lemma ff_reflects_is_iso (C D : precategory) (F : functor C D)
  (HF : fully_faithful F) : reflects_isos F.
Proof.
  intros a b f H.
  set (X:= fully_faithful_reflects_iso_proof _ _ F HF _ _ (isopair _ H)).
  simpl in X.
  set (T:= homotinvweqweq (weq_from_fully_faithful HF a b ) ).
  simpl in T.
  unfold fully_faithful_inv_hom in X.
  simpl in X.
  rewrite T in X.
  apply X.
Defined.


Definition weq_ff_functor_on_weq_isobandf {C D : precategory}
  {F : functor C D}
  (HF : fully_faithful F) (a b : C)
  : iso a b ≃ iso (F a) (F b).
Proof.
  use weqbandf.
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

Lemma weq_ff_functor_on_weq_isobandf_compute {C D : precategory} (F : functor C D)
      (HF : fully_faithful F) {a b : C} (f : iso a b)
: #F f = weq_ff_functor_on_weq_isobandf HF _ _ f.
Proof.
  apply idpath.
Defined.

Lemma ff_is_inclusion_on_objects {C D : precategory}
      (HC : is_univalent C) (HD : is_univalent D)
      (F : functor C D) (HF : fully_faithful F)
      : isofhlevelf 1 (functor_on_objects F).
Proof.
  intro d.
  apply invproofirrelevance.
  intros [c e] [c' e'].
  use total2_paths_f.
  - simpl.
    set (X := idtoiso (e @ ! e')).
    (* set (X' := invmap (@weq_ff_functor_on_iso _ _ _ HF _ _ ) X). *)
        (* we cannot use X' because we lack the preceding, commented-out,
           lemma *)
    set (X2 := iso_from_fully_faithful_reflection HF X).
    apply (isotoid _ HC X2).
  - simpl.
    set (T:=@functtransportf _ _ (functor_on_objects F)).
    set (T' := T (λ c, c = d)). simpl in T'.
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


(** ** (Split) essentially surjective functors *)

(** See [CategoryTheory.equivalences] for more lemmas about (split) essential
    surjectivity, especially where the domain is a [univalent_category]. *)

(** See "Univalent categories and the Rezk completion" (arXiv:1303.0584v2)
    Definition 6.5. *)
Definition split_essentially_surjective {C D : precategory_data} (F : functor C D) :=
  ∏ b, (∑ a : ob C, iso (F a) b).

(** Split essentially surjective functors have "inverses" on objects, where we
    map d : ob D to the c : ob C such that F c ≅ d. *)
Definition split_essentially_surjective_inv_on_obj {C D : precategory_data}
           (F : functor C D) (HF : split_essentially_surjective F) : ob D → ob C :=
  λ d, (pr1 (HF d)).

Definition essentially_surjective {C D : precategory_data} (F : functor C D) :=
  ∏ b, ishinh (total2 (λ a, iso (F a) b)).

Lemma isaprop_essentially_surjective {C D : precategory_data} (F : functor C D) :
   isaprop (essentially_surjective F).
Proof.
  apply impred; intro; apply isapropishinh.
Defined.

(** Composition of essentially surjective functors yields an essentially
    surjective functor. *)

(** Let e : E. Since G is essentially surjective, there is some g
    such that e ≅ G g. Since F is essentially surjective, there is some f
    such that G g ≅ F f. Composing these isomorphisms proves the goal.
 *)
Lemma comp_essentially_surjective {C D E : precategory}
      (F : functor C D) (esF : essentially_surjective F)
      (G : functor D E) (esG : essentially_surjective G) :
  essentially_surjective (functor_composite F G).
Proof.
  unfold essentially_surjective.
  intros e.
  apply (squash_to_prop (esG e)); [apply isapropishinh|]; intros isoGe.
  apply (squash_to_prop (esF (pr1 isoGe))); [apply isapropishinh|]; intros isoFGe.
  apply hinhpr.
  exists (pr1 isoFGe); unfold functor_composite; cbn.
  apply (@iso_comp E _ (G (pr1 isoGe))).
  - apply functor_on_iso.
    exact (pr2 isoFGe).
  - apply (pr2 isoGe).
Defined.

(** ** Faithful functors *)

Definition faithful {C D : precategory_data} (F : functor C D) :=
  ∏ a b : ob C, isincl (fun f : a --> b => #F f).

Lemma isaprop_faithful (C D : precategory_data) (F : functor C D) :
   isaprop (faithful F).
Proof.
  unfold faithful.
  do 2 (apply impred; intro).
  apply isapropisincl.
Qed.

(** Composition of faithful functors yields a faithful functor. *)

Lemma comp_faithful_is_faithful (C D E : precategory)
      (F : functor C D) (faithF : faithful F)
      (G : functor D E) (faithG : faithful G) : faithful (functor_composite F G).
Proof.
  unfold faithful in *.
  intros ? ?; apply (isinclcomp (_,, faithF _ _) (_,, faithG _ _)).
Qed.

(** Faithful functors reflect commutative triangles. If F f · F g = F h,
    in D, then f · g = h in C. (Really, this is true more generally for any
    diagram.) *)

Lemma faithful_reflects_commutative_triangle {C D : precategory} (F : functor C D)
      (FF : faithful F) {a b c : ob C} (f : C ⟦a, b⟧) (g : C ⟦b, c⟧) (h : C ⟦a, c⟧) :
  # F f · # F g = # F h → f · g = h.
Proof.
  intros feq.
  apply (Injectivity (# F)).
  - apply isweqonpathsincl, FF.
  - exact (functor_comp F f g @ feq).
Defined.

(** ** Full functors *)

Definition full {C D : precategory_data} (F : functor C D) :=
   ∏ a b: C, issurjective (fun f : a --> b => #F f).

Lemma isaprop_full (C D : precategory_data) (F : functor C D) :
   isaprop (full F).
Proof.
  unfold full.
  do 2 (apply impred; intro).
  apply isapropissurjective.
Qed.

(** Composition of full functors yields a full functor *)

Lemma comp_full_is_full (C D E : precategory)
      (F : functor C D) (fullF : full F)
      (G : functor D E) (fullG : full G) : full (functor_composite F G).
Proof.
  unfold full in *.
  intros ? ?; apply (issurjcomp _ _ (fullF _ _) (fullG _ _)).
Qed.

(** ** Fully faithful is the same as full and faithful *)

Definition full_and_faithful {C D : precategory_data} (F : functor C D) :=
   (full F) × (faithful F).

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
   (fully_faithful F) ≃ (full_and_faithful F) :=
  weqimplimpl (fully_faithful_implies_full_and_faithful _ _ F)
              (full_and_faithful_implies_fully_faithful _ _ F)
              (isaprop_fully_faithful _ _ F)
              (isaprop_full_and_faithful _ _ F).

(** Composition of fully faithful functors yields a fully faithful functor. *)

Lemma comp_full_and_faithful_is_full_and_faithful (C D E : precategory)
      (F : functor C D) (f_and_f_F : full_and_faithful F)
      (G : functor D E) (f_and_f_G : full_and_faithful G) :
  full_and_faithful (functor_composite F G).
Proof.
  split.
  - apply comp_full_is_full; [apply (pr1 f_and_f_F)|apply (pr1 f_and_f_G)].
  - apply comp_faithful_is_faithful; [apply (pr2 f_and_f_F)|apply (pr2 f_and_f_G)].
Qed.

Lemma comp_ff_is_ff (C D E : precategory)
      (F : functor C D) (ffF : fully_faithful F)
      (G : functor D E) (ffG : fully_faithful G) :
  fully_faithful (functor_composite F G).
Proof.
  unfold fully_faithful in *.
  intros ? ?; apply (pr2 (weqcomp (_,, ffF _ _) (_,, ffG _ _))).
Qed.

(** ** Image on objects of a functor  *)
(** is used later to define the full image subcategory of a category [D]
       defined by a functor [F : C -> D] *)

Definition is_in_img_functor {C D : precategory_data} (F : functor C D)
      (d : ob D) :=
  ishinh (
  total2 (λ c : ob C, iso (F c) d)).

Definition sub_img_functor {C D : precategory_data}(F : functor C D) :
    hsubtype (ob D) :=
       λ d : ob D, is_in_img_functor F d.

(** * Natural transformations *)
Section nat_trans.

  (** ** Definition of natural transformations *)

Definition nat_trans_data {C C' : precategory_ob_mor} (F F' : functor_data C C'): UU :=
  ∏ x : ob C, F x -->  F' x.

Definition is_nat_trans {C C' : precategory_data}
  (F F' : functor_data C C') (t : nat_trans_data F F') :=
  ∏ (x x' : ob C)(f : x --> x'), # F f · t x' = t x · #F' f.


Lemma isaprop_is_nat_trans (C C' : precategory_data) (hs: has_homsets C')
  (F F' : functor_data C C') (t : nat_trans_data F F'):
  isaprop (is_nat_trans F F' t).
Proof.
  repeat (apply impred; intro).
  apply hs.
Qed.

Definition nat_trans {C C' : precategory_data} (F F' : functor_data C C') : UU :=
  total2 (fun t : nat_trans_data F F' => is_nat_trans F F' t).

Notation "F ⟹ G" := (nat_trans F G) (at level 39) : cat.
(* to input: type "\==>" with Agda input method *)

(** Note that this makes the second component opaque for efficiency reasons *)
Definition mk_nat_trans {C C' : precategory_data} (F F' : functor_data C C')
           (t : nat_trans_data F F') (H : is_nat_trans F F' t) :
           nat_trans F F'.
Proof.
exists t.
abstract (exact H).
Defined.

Lemma isaset_nat_trans {C C' : precategory_data} (hs: has_homsets C')
  (F F' : functor_data C C') : isaset (nat_trans F F').
Proof.
  apply (isofhleveltotal2 2).
  + apply impred; intro t; apply hs.
  + intro x; apply isasetaprop, isaprop_is_nat_trans, hs.
Qed.

Definition nat_trans_data_from_nat_trans {C C' : precategory_data}
  {F F' : functor_data C C'}(a : nat_trans F F') :
  nat_trans_data F F' := pr1 a.

Definition nat_trans_data_from_nat_trans_funclass {C C' : precategory_data}
  {F F' : functor_data C C'}(a : nat_trans F F') :
  ∏ x : ob C, F x -->  F' x := pr1 a.
Coercion nat_trans_data_from_nat_trans_funclass : nat_trans >-> Funclass.

Definition nat_trans_ax {C C' : precategory_data}
  {F F' : functor_data C C'} (a : nat_trans F F') :
  ∏ (x x' : ob C)(f : x --> x'),
    #F f · a x' = a x · #F' f := pr2 a.

(** Equality between two natural transformations *)

Lemma nat_trans_eq {C C' : precategory_data} (hs: has_homsets C')
  (F F' : functor_data C C')(a a' : nat_trans F F'):
  (∏ x, a x = a' x) -> a = a'.
Proof.
  intro H.
  assert (H' : pr1 a = pr1 a').
  { now apply funextsec. }
  apply (total2_paths_f H'), proofirrelevance, isaprop_is_nat_trans, hs.
Qed.

Definition nat_trans_eq_pointwise {C C' : precategory_data}
   {F F' : functor_data C C'} {a a' : nat_trans F F'}:
      a = a' -> ∏ x, a x = a' x.
Proof.
  intro h.
  now apply toforallpaths, maponpaths.
Qed.

(** a more intuitive variant of [functor_data_eq] *)
Lemma functor_data_eq_from_nat_trans (C C': precategory) (F F' : functor_data C C')
      (H : F ~ F') (H1 : is_nat_trans F F' (fun c:C => idtomor _ _ (H c))) :
      F = F'.
Proof.
  apply (functor_data_eq _ _ _ _ H).
  intros c1 c2 f.
  rewrite double_transport_idtoiso.
  rewrite <- assoc.
  apply iso_inv_on_right.
(* make the coercion visible: *)
  unfold morphism_from_iso.
  do 2 rewrite eq_idtoiso_idtomor.
  apply H1.
Qed.


(** ** Functor category [[C, D]] *)

Definition functor_precategory_ob_mor (C C' : precategory_data):
  precategory_ob_mor := precategory_ob_mor_pair
   (functor C C') (λ F F' : functor C C', nat_trans F F').


(** *** Identity natural transformation *)

Lemma is_nat_trans_id {C : precategory_data}{C' : precategory}
  (F : functor_data C C') : is_nat_trans F F
     (λ c : ob C, identity (F c)).
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
     (λ x : ob C, a x · b x).
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
  tpair (λ C, is_precategory C)
        (functor_precategory_data C C')
        (is_precategory_functor_precategory_data C C' hs).

Notation "[ C , D , hs ]" := (functor_precategory C D hs) : cat.

Definition functor_identity_as_ob (C : precategory) (hsC : has_homsets C)
  : [C, C, hsC]
  := (functor_identity C).

Definition functor_composite_as_ob {C C' C'' : precategory}
  {hsC' : has_homsets C'} {hsC'' : has_homsets C''}
  (F : [C, C', hsC']) (F' : [C', C'', hsC'']) :
  [C, C'', hsC''] := tpair _ _ (is_functor_composite F F').

Lemma nat_trans_comp_pointwise (C : precategory_data)(C' : precategory) (hs: has_homsets C')
  (F G H : ob [C, C', hs]) (A : F --> G) (A' : G --> H)
   (B : F --> H) : A · A' = B ->
        ∏ a, pr1 A a · pr1 A' a = pr1 B a.
Proof.
  intros H' a.
  intermediate_path (pr1 (A · A') a).
  apply idpath.
  destruct H'.
  apply idpath.
Defined.

Section nat_trans_eq.

Context {C D : precategory}.
Variable hsD : has_homsets D.
Context {F G : functor C D}.
Variables alpha beta : nat_trans F G.

Definition nat_trans_eq_weq : (alpha = beta) ≃ (∏ c, alpha c = beta c).
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
  (H : forall a : ob C, is_iso (pr1 A a)) :
  is_nat_trans _ _
     (λ a : ob C, inv_from_iso (tpair _ _ (H a))).
Proof.
  red.
  intros x x' f.
  apply pathsinv0.
  apply iso_inv_on_right.
  rewrite assoc.
  apply iso_inv_on_left.
  set (HA:= pr2 A).
  simpl in *.
  apply pathsinv0.
  unfold is_nat_trans in HA.
  apply HA.
Qed.

Lemma is_nat_trans_inv_from_pointwise_inv (C : precategory_data)(D : precategory)
  (hs: has_homsets D)
  (F G : ob [C,D,hs]) (A : F --> G)
  (H : forall a : ob C, is_iso (pr1 A a)) :
  is_nat_trans _ _
     (λ a : ob C, inv_from_iso (tpair _ _ (H a))).
Proof.
  apply is_nat_trans_inv_from_pointwise_inv_ext.
  exact hs.
Qed.

Definition nat_trans_inv_from_pointwise_inv (C : precategory_data)(D : precategory)
  (hs: has_homsets D)
  (F G : ob [C,D,hs]) (A : F --> G)
  (H : ∏ a : ob C, is_iso (pr1 A a)) :
    G --> F := tpair _ _ (is_nat_trans_inv_from_pointwise_inv _ _ _ _ _ _ H).

Definition nat_trans_inv_from_pointwise_inv_ext {C : precategory_data}{D : precategory}
  (hs: has_homsets D)
  {F G : functor_data C D} (A : nat_trans F G)
  (H : forall a : ob C, is_iso (pr1 A a)) :
    nat_trans G F := tpair _ _ (is_nat_trans_inv_from_pointwise_inv_ext hs H).

Lemma nat_trans_inv_is_iso {C : precategory_data}{D : precategory}
  (hs: has_homsets D)
  {F G : functor_data C D} (A : nat_trans F G)
  (H : forall a : ob C, is_iso (pr1 A a)) :
  forall a : ob C, is_iso ((nat_trans_inv_from_pointwise_inv_ext hs A H) a).
Proof.
  intros a.
  apply is_iso_inv_from_iso.
Defined.

Lemma is_inverse_nat_trans_inv_from_pointwise_inv (C : precategory_data)(C' : precategory) (hs: has_homsets C')
    (F G : [C, C', hs]) (A : F --> G)
   (H : ∏ a : C, is_iso (pr1 A a)) :
  is_inverse_in_precat A (nat_trans_inv_from_pointwise_inv C C' _ F G A H).
Proof.
  simpl; split; simpl.
  - apply nat_trans_eq. apply hs.
    intro x; simpl.
    set (T := iso_inv_after_iso (tpair _ (pr1 A x) (H x))).
    apply T.
  - apply nat_trans_eq. apply hs.
    intro x; simpl.
    set (T := iso_after_iso_inv (tpair _ (pr1 A x) (H x))).
    apply T.
Qed.


Lemma functor_iso_if_pointwise_iso (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) :
   (∏ a : ob C, is_iso (pr1 A a)) ->
           is_iso A .
Proof.
  intro H.
  apply (is_iso_qinv _ (nat_trans_inv_from_pointwise_inv _ _ _ _ _ _ H)).
  simpl; apply is_inverse_nat_trans_inv_from_pointwise_inv.
Defined.

Definition functor_iso_from_pointwise_iso (C : precategory_data)(C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G)
   (H : ∏ a : ob C, is_iso (pr1 A a)) :
     iso F G :=
 tpair _ _ (functor_iso_if_pointwise_iso _ _ _ _ _ _ H).


Lemma is_functor_iso_pointwise_if_iso (C : precategory_data)(C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) :
  is_iso A ->
       ∏ a : ob C, is_iso (pr1 A a).
Proof.
  intros H a.
  set (T := inv_from_iso (tpair _ A H)).
  set (TA := iso_inv_after_iso (tpair _ A H)).
  set (TA' := iso_after_iso_inv (tpair _ A H)).
  simpl in *.
  apply (is_iso_qinv _ (T a)).
  unfold is_inverse_in_precat in *; simpl; split.
  - unfold T.
    set (H1' := nat_trans_eq_pointwise TA). apply H1'.
  - apply (nat_trans_eq_pointwise TA').
Defined.

Lemma nat_trans_inv_pointwise_inv_before (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) (Aiso: is_iso A) :
       ∏ a : C, pr1 (inv_from_iso (isopair A Aiso)) a · pr1 A a = identity _ .
Proof.
  intro a.
  set (T := inv_from_iso (isopair A Aiso)).
  set (TA := iso_inv_after_iso (isopair A Aiso)).
  set (TA' := iso_after_iso_inv (isopair A Aiso)).
  apply (nat_trans_eq_pointwise TA').
Defined.

Lemma nat_trans_inv_pointwise_inv_after (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) (Aiso: is_iso A) :
       ∏ a : C, pr1 A a · pr1 (inv_from_iso (isopair A Aiso)) a = identity _ .
Proof.
  intro a.
  set (T := inv_from_iso (isopair A Aiso)).
  set (TA := iso_inv_after_iso (isopair A Aiso)).
  set (TA' := iso_after_iso_inv (isopair A Aiso)).
  apply (nat_trans_eq_pointwise TA).
Defined.


Definition functor_iso_pointwise_if_iso (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C',hs]) (A : F --> G)
  (H : is_iso A) :
     ∏ a : ob C,
       iso (pr1 F a) (pr1 G a) :=
  λ a, tpair _ _ (is_functor_iso_pointwise_if_iso C C' _ F G A H a).

Lemma nat_trans_inv_pointwise_inv_after_p (C : precategory_data) (C' : precategory)
  (hs: has_homsets C')
 (F G : ob [C, C', hs]) (A : F --> G) (Aiso: is_iso A) a :
  inv_from_iso (functor_iso_pointwise_if_iso C C' hs F G A Aiso a) =
        pr1 (inv_from_iso (isopair A Aiso)) a.
Proof.
  apply pathsinv0.
  apply inv_iso_unique'.
  unfold precomp_with.
  simpl.
  set (TA := iso_inv_after_iso (isopair A Aiso)).
  simpl in TA.
  apply (nat_trans_eq_pointwise TA).
Defined.

Definition pr1_pr1_functor_eq_from_functor_iso (C : precategory_data) (D : precategory)
  (hs: has_homsets D)
    (H : is_univalent D) (F G : ob [C , D, hs]) :
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
      (F1 : ∏ a b : ob C, a --> b -> F0 a --> F0 b)
      (gamma : F0  = G0 )
      (a b : ob C) (f : a --> b) :
  transportf (fun x : ob C -> ob D =>
                ∏ a0 b0 : ob  C, a0 --> b0 -> x a0 --> x b0)
             gamma F1 a b f =
  double_transport (toforallpaths (λ _ : ob C, D) F0 G0 gamma a)
                   (toforallpaths (λ _ : ob C, D) F0 G0 gamma b)
                   (F1 a b f).
Proof.
  induction gamma.
  apply idpath.
Defined.

Definition pr1_functor_eq_from_functor_iso (C : precategory_data) (D : precategory)(hs: has_homsets D)
    (H : is_univalent D) (F G : ob [C , D, hs]) :
   iso F G -> pr1 F = pr1 G.
Proof.
  intro A.
  apply (total2_paths_f (pr1_pr1_functor_eq_from_functor_iso C D _ H F G A)).
  unfold pr1_pr1_functor_eq_from_functor_iso.
  apply funextsec; intro a.
  apply funextsec; intro b.
  apply funextsec; intro f.
  rewrite transport_of_functor_map_is_pointwise.
  rewrite toforallpaths_funextsec.
  etrans.
  { apply double_transport_idtoiso. }
  rewrite idtoiso_isotoid.
  rewrite idtoiso_isotoid.
  etrans.
  { rewrite <- assoc.
    apply cancel_precomposition.
    apply (nat_trans_ax (pr1 A)).
  }
  etrans.
  { apply cancel_postcomposition.
    apply nat_trans_inv_pointwise_inv_after_p. }
  rewrite assoc.
  apply remove_id_left; try apply idpath.
  set (TA' := iso_after_iso_inv A).
  set (TA'' := nat_trans_comp_pointwise _ _ _ _ _ _ _ _  _ TA').
  apply TA''.
Defined.

Definition functor_eq_from_functor_iso {C : precategory_data} {D : precategory}
  (hs: has_homsets D)
    (H : is_univalent D) (F G : ob [C , D, hs])
    (H' : iso F G) : F = G.
Proof.
  apply (functor_eq _ _ hs F G).
  apply pr1_functor_eq_from_functor_iso;
  assumption.
Defined.


Lemma idtoiso_functorcat_compute_pointwise (C : precategory_data) (D : precategory)
  (hs: has_homsets D) (F G : ob [C, D, hs])
     (p : F = G) (a : ob C) :
  functor_iso_pointwise_if_iso C D _ F G (idtoiso p) (pr2 (idtoiso p)) a =
idtoiso
  (toforallpaths (λ _ : ob C, D) (pr1 (pr1 F)) (pr1 (pr1 G))
     (base_paths (pr1 F) (pr1 G) (base_paths F G p)) a).
Proof.
  induction p.
  apply eq_iso. apply idpath.
Qed.


Lemma functor_eq_from_functor_iso_idtoiso (C : precategory_data) (D : precategory)
  (hs: has_homsets D)
    (H : is_univalent D)
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
  rewrite idtoiso_functorcat_compute_pointwise.
  apply isotoid_idtoiso.
Qed.

Lemma idtoiso_functor_eq_from_functor_iso (C : precategory_data) (D : precategory)
  (hs: has_homsets D)
    (H : is_univalent D)
    (F G : ob [C, D, hs]) (gamma : iso F G) :
        idtoiso (functor_eq_from_functor_iso _ H F G gamma) = gamma.
Proof.
  apply eq_iso.
  simpl; apply nat_trans_eq; intro a. apply hs.
  assert (H' := idtoiso_functorcat_compute_pointwise C D _ F G (functor_eq_from_functor_iso _ H F G gamma) a).
  simpl in *.
  assert (H2 := maponpaths (@pr1 _ _ ) H'). simpl in H2.
  etrans.
  { apply H2. }
  clear H' H2.
  unfold functor_eq_from_functor_iso.
  unfold functor_eq.
  rewrite base_total2_paths.
  unfold pr1_functor_eq_from_functor_iso.
  rewrite base_total2_paths.
  intermediate_path (pr1 (idtoiso
     (isotoid D H (functor_iso_pointwise_if_iso C D hs F G gamma (pr2 gamma) a)))).
  2: { rewrite idtoiso_isotoid.
       apply idpath.
  }
  apply maponpaths.
  apply maponpaths.
  unfold pr1_pr1_functor_eq_from_functor_iso.
  rewrite toforallpaths_funextsec.
  apply idpath.
Qed.

Lemma isweq_idtoiso_functorcat (C : precategory_data) (D : precategory) (H : is_univalent D)
    (F G : ob [C, D, (pr2 H)]) :
   isweq (@idtoiso _ F G).
Proof.
  apply (isweq_iso _ (functor_eq_from_functor_iso _ H F G)).
  apply functor_eq_from_functor_iso_idtoiso.
  apply idtoiso_functor_eq_from_functor_iso.
Defined.

Lemma is_univalent_functor_category (C : precategory_data) (D : precategory) (H : is_univalent D) :
   is_univalent [C, D, (pr2 H)].
Proof.
  split.
  - intros F G.
    apply isweq_idtoiso_functorcat.
  - intros a b.
    apply isaset_nat_trans.
    apply (pr2 H).
Defined.


Lemma functor_category_has_homsets (C D : precategory) (hs: has_homsets D):
  has_homsets [C, D, hs].
Proof.
  intros F G.
  apply isaset_nat_trans.
  apply hs.
Qed.


Definition functor_category (C : precategory) (D : category) : category.
Proof.
  exists (functor_precategory C D (homset_property D)).
  apply functor_category_has_homsets.
Defined.

End nat_trans.

Section functor_equalities.

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
  apply ( maponpaths ( λ p, tpair is_functor (tpair _ Fob Fmor) p ) ) .
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
  apply ( maponpaths ( λ p, tpair is_functor _ p ) ) . simpl .
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
  apply ( maponpaths ( λ e, pathscomp0 e ( is2id (F1ob (F0ob t)) ) ) ) .
  rewrite maponpathscomp0 .
  apply ( maponpaths ( λ e, pathscomp0 e ( maponpaths
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
  apply ( maponpaths ( λ e,
                         pathscomp0 e ( is2comp (F1ob (F0ob t)) (F1ob (F0ob t0)) (F1ob (F0ob t1))
                                                (F1mor (F0ob t) (F0ob t0) (F0mor t t0 f))
                                                (F1mor (F0ob t0) (F0ob t1) (F0mor t0 t1 g)) ) ) ) .
  rewrite maponpathscomp0 .
  apply ( maponpaths ( λ e,
                         pathscomp0 e ( maponpaths (F2mor (F1ob (F0ob t)) (F1ob (F0ob t1)))
                                                   (is1comp (F0ob t) (F0ob t0) (F0ob t1)
                                                            (F0mor t t0 f) (F0mor t0 t1 g)) ))).
  apply maponpathscomp .
Defined.

End functor_equalities.

(** Natural transformations for reasoning about various compositions of functors *)
Section nat_trans_functor.

Context {A B C D : precategory}.

Definition nat_trans_functor_id_right (F : functor A B) :
  nat_trans (functor_composite F (functor_identity B)) F.
Proof.
exists (λ x, identity _).
abstract (now intros a b f; rewrite id_left, id_right).
Defined.

Definition nat_trans_functor_id_right_inv (F : functor A B) :
  nat_trans F (functor_composite F (functor_identity B)) :=
    nat_trans_functor_id_right F.

Definition nat_trans_functor_id_left (F : functor A B) :
  nat_trans (functor_composite (functor_identity A) F) F :=
    nat_trans_functor_id_right F.

Definition nat_trans_functor_id_left_inv (F : functor A B) :
  nat_trans F (functor_composite (functor_identity A) F) :=
    nat_trans_functor_id_right F.

Definition nat_trans_functor_assoc (F1 : functor A B) (F2 : functor B C) (F3 : functor C D) :
  nat_trans (functor_composite (functor_composite F1 F2) F3)
            (functor_composite F1 (functor_composite F2 F3)).
Proof.
exists (λ x, identity _).
abstract (now intros a b f; rewrite id_right, id_left).
Defined.

Definition nat_trans_functor_assoc_inv (F1 : functor A B) (F2 : functor B C) (F3 : functor C D) :
  nat_trans (functor_composite F1 (functor_composite F2 F3))
            (functor_composite (functor_composite F1 F2) F3) :=
    nat_trans_functor_assoc F1 F2 F3.

End nat_trans_functor.

Section functors_on_iso_with_inv.

  Lemma functor_on_is_inverse_in_precat {C C' : precategory} (F : functor C C')
        {a b : ob C} {f : a --> b} {g : b --> a} (H : is_inverse_in_precat f g) :
    is_inverse_in_precat (# F f) (# F g).
  Proof.
    use mk_is_inverse_in_precat.
    - rewrite <- functor_comp. rewrite (is_inverse_in_precat1 H). apply functor_id.
    - rewrite <- functor_comp. rewrite (is_inverse_in_precat2 H). apply functor_id.
  Qed.

  Definition functor_on_is_z_isomorphism {C C' : precategory} (F : functor C C')
             {a b : ob C} {f : a --> b} (I : is_z_isomorphism f) :
    is_z_isomorphism (# F f).
  Proof.
    use mk_is_z_isomorphism.
    - exact (# F (is_z_isomorphism_mor I)).
    - exact (functor_on_is_inverse_in_precat F I).
  Defined.

  Definition functor_on_z_iso {C C' : precategory} (F : functor C C') {a b : ob C}
             (f : z_iso a b) : z_iso (F a) (F b).
  Proof.
    use mk_z_iso.
    - exact (# F f).
    - exact (# F (z_iso_inv_mor f)).
    - exact (functor_on_is_inverse_in_precat F f).
  Defined.

End functors_on_iso_with_inv.

Notation "[ C , D , hs ]" := (functor_precategory C D hs) : cat.

Notation "[ C , D ]" := (functor_category C D) : cat.

Notation "F ⟹ G" := (nat_trans F G) (at level 39) : cat.
(* to input: type "\==>" with Agda input method *)

Notation "F ∙ G" := (functor_composite F G) (at level 35) : cat.
(* to input: type "\." with Agda input method *)
(* the old notation had the arguments in the opposite order *)

Notation "G □ F" := (functor_composite F G) (at level 35, only parsing) : cat.
(* to input: type "\Box" or "\square" or "\sqw" or "\sq" with Agda input method *)

Notation "G □ F" := (functor_composite (F:[_,_]) (G:[_,_]) : [_,_]) (at level 35) : Cat.
(* to input: type "\Box" or "\square" or "\sqw" or "\sq" with Agda input method *)

Lemma functor_comp_pw {C C' D D' : precategory} hsD hsD'
           (F : [C,D,hsD] ⟶ [C',D',hsD']) {a b c}  (f : [C,D,hsD] ⟦ a, b ⟧)
           (g : [C,D,hsD] ⟦ b, c ⟧) (x :C') :
  (# F f:nat_trans _ _) x · (# F g:nat_trans _ _) x = ((# F (f · g)) :  nat_trans _ _ ) x .
Proof.
  now rewrite functor_comp.
Qed.

Lemma functor_cancel_pw {C C' D D' : precategory} hsD hsD'
           (F : [C,D,hsD] ⟶ [C',D',hsD']) {a b }  (f g : [C,D,hsD] ⟦ a, b ⟧)
           (x :C') : f = g ->
                     ((# F f ) :  nat_trans _ _ ) x = (# F g:nat_trans _ _) x .
Proof.
  intro e.
  now induction e.
Qed.

(* Natural isomorphisms *)
Definition is_nat_iso {C D : precategory} {F G : C ⟶ D} (μ : F ⟹ G) : UU :=
∏ (c : C), is_iso (μ c).

Definition is_nat_id {C D : precategory} {F : C ⟶ D} (μ : F ⟹ F) : UU :=
∏ (c : C), μ c = identity (F c).

Definition nat_iso {C D : precategory} (F G : C ⟶ D) : UU
:= ∑ (μ : F ⟹ G), is_nat_iso μ.

Definition mk_nat_iso {C D : precategory} (F G : C ⟶ D) (μ : F ⟹ G) (is_iso : is_nat_iso μ) : nat_iso F G.
Proof.
  exists μ.
  abstract (exact is_iso).
Defined.

Definition iso_inv_after_iso' {C : precategory} {a b : C} (f : a --> b) (f' : iso a b) (deref : pr1 f' = f) : f · inv_from_iso f' = identity _.
Proof.
  rewrite <- deref.
  exact (iso_inv_after_iso f').
Defined.

Definition iso_after_iso_inv' {C : precategory} {a b : C} (f : a --> b) (f' : iso a b) (deref : pr1 f' = f) : inv_from_iso f' · f = identity _.
Proof.
  rewrite <- deref.
  exact (iso_after_iso_inv f').
Defined.

Definition nat_iso_inv {C D : precategory} {F G : C ⟶ D} (μ : nat_iso F G) : nat_iso G F.
Proof.
  pose (iso := (λ c, mk_iso (pr2 μ c))).
  pose (inv := (λ c, inv_from_iso (iso c))).
  use tpair.
  - exists inv.
    intros c c' f.
    pose (coher := pr2 (pr1 μ) c c' f).
    pose (coher_inv := maponpaths (λ p, inv c · p · inv c') coher).
    simpl in coher_inv.
    repeat rewrite <- assoc in coher_inv.
    unfold inv in coher_inv.
    assert (coher_inv' : (inv_from_iso (iso c) · (# F f · ((pr1 μ) c' · inv_from_iso (iso c'))) = inv_from_iso (iso c) · (pr1 (pr1 μ) c · (# G f · inv_from_iso (iso c'))))) by assumption.
    clear coher_inv; rename coher_inv' into coher_inv.
    assert (deref' : pr1 (iso c') = (pr1 μ) c') by reflexivity.
    rewrite (iso_inv_after_iso' ((pr1 μ) c') (iso c') deref') in coher_inv.
    rewrite id_right in coher_inv.
    repeat rewrite assoc in coher_inv.
    assert (deref : pr1 (iso c) = (pr1 μ) c) by reflexivity.
    assert (coher_inv' : (inv_from_iso (iso c) · # F f = inv_from_iso (iso c) · (pr1 μ) c · # G f · inv_from_iso (iso c'))) by assumption.
    clear coher_inv; rename coher_inv' into coher_inv.
    rewrite (iso_after_iso_inv' ((pr1 μ) c) (iso c) deref) in coher_inv.
    rewrite id_left in coher_inv.
    unfold inv.
    symmetry.
    assumption.
  - intro c.
    exact (is_iso_inv_from_iso (iso c)).
Defined.

Definition nat_iso_to_trans {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : F ⟹ G :=
  pr1 ν.

(* ⁻¹ *)
Definition nat_iso_to_trans_inv {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : G ⟹ F :=
  pr1 (nat_iso_inv ν).

Definition nat_comp_to_endo {C D : precategory} {F G : C ⟶ D} (eq : F = G) {c : C} (f : F c --> G c) : F c --> F c.
Proof.
  rewrite <- eq in f.
  assumption.
Defined.

Definition is_nat_iso_id {C D : precategory} {F G : C ⟶ D} (eq : F = G) (ν : nat_iso F G) : UU :=
  ∏ (c : C), nat_comp_to_endo eq (nat_iso_to_trans ν c) = identity (F c).
