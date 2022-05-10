(** * Functors

Authors: Benedikt Ahrens, Chris Kapulkin, Mike Shulman (January 2013)

*)

(** ** Contents:

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


*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Import UniMath.CategoryTheory.Core.Univalence.

Local Open Scope cat.

(** * Functors : Morphisms of precategories *)
Section functors.

Definition functor_data (C C' : precategory_ob_mor) : UU :=
  total2 ( fun F : ob C -> ob C' =>  ∏ a b : ob C, a --> b -> F a --> F b).

Definition make_functor_data {C C' : precategory_ob_mor} (F : ob C -> ob C')
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

Notation "a ⟶ b" := (functor a b) : cat.
(* to input: type "\-->" with Agda input method *)


Definition make_functor {C C' : precategory_data} (F : functor_data C C') (H : is_functor F) :
  functor C C'.
Proof.
exists F.
exact H.
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

Lemma functor_on_is_iso_is_iso {C C' : precategory} (F : functor C C')
      {a b : ob C} {f : a --> b} (H : is_iso f)  : is_iso (#F f).
Proof.
  apply (is_iso_qinv _ (#F (inv_from_iso (make_iso _ H)))).
  apply (is_inverse_functor_image _ _ _ _ _ (make_iso _ H)).
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
  inv_from_iso (make_iso _ (functor_on_is_iso_is_iso F H)) = # F (inv_from_iso (make_iso _ H)).
Proof.
  apply pathsinv0. use inv_iso_unique'. cbn. unfold precomp_with.
  rewrite <- functor_comp. set (tmp := iso_inv_after_iso (make_iso _ H)). cbn in tmp.
  rewrite tmp. apply functor_id.
Qed.



Section functors_on_iso_with_inv.

  Lemma functor_on_is_inverse_in_precat {C C' : precategory} (F : functor C C')
        {a b : ob C} {f : a --> b} {g : b --> a} (H : is_inverse_in_precat f g) :
    is_inverse_in_precat (# F f) (# F g).
  Proof.
    use make_is_inverse_in_precat.
    - rewrite <- functor_comp. rewrite (is_inverse_in_precat1 H). apply functor_id.
    - rewrite <- functor_comp. rewrite (is_inverse_in_precat2 H). apply functor_id.
  Qed.

  Definition functor_on_is_z_isomorphism {C C' : precategory} (F : functor C C')
             {a b : ob C} {f : a --> b} (I : is_z_isomorphism f) :
    is_z_isomorphism (# F f).
  Proof.
    use make_is_z_isomorphism.
    - exact (# F (is_z_isomorphism_mor I)).
    - exact (functor_on_is_inverse_in_precat F I).
  Defined.

  Lemma functor_is_inverse_in_precat_inv_from_iso {C D : precategory} {c c' : ob C}
        (F : functor C D) (f : iso c c') :
    is_inverse_in_precat (# F f) (# F (inv_from_iso f)).
  Proof.
    apply functor_on_is_inverse_in_precat.
    split.
    + apply is_inverse_in_precat1.
      split.
      * apply (iso_inv_after_iso f).
      * apply (iso_after_iso_inv f).
    + apply is_inverse_in_precat2.
      split.
      * apply (iso_inv_after_iso f).
      * apply (iso_after_iso_inv f).
  Qed.

  Definition functor_on_z_iso {C C' : precategory} (F : functor C C') {a b : ob C}
             (f : z_iso a b) : z_iso (F a) (F b).
  Proof.
    use make_z_iso.
    - exact (# F f).
    - exact (# F (inv_from_z_iso f)).
    - exact (functor_on_is_inverse_in_precat F f).
  Defined.

  Lemma functor_on_z_iso_inv (C C' : category) (F : functor C C')
    (a b : ob C) (f : z_iso a b) :
   functor_on_z_iso F (z_iso_inv_from_z_iso f) =
       z_iso_inv_from_z_iso (functor_on_z_iso F f).
  Proof.
    apply eq_z_iso; simpl.
    apply idpath.
  Defined.

  Lemma functor_on_inv_from_z_iso' {C C' : precategory} (F : functor C C')
      {a b : ob C} {f : a --> b} (H : is_z_isomorphism f) :
  inv_from_z_iso (make_z_iso _ _ (functor_on_is_z_isomorphism F H)) = # F (inv_from_z_iso (make_z_iso _ _ H)).
  Proof.
    apply idpath.
  Qed.

End functors_on_iso_with_inv.

(** ** Functors and [idtoiso] *)

Section functors_and_idtoiso.

Variables C D : category.
Variable F : functor C D.

Lemma maponpaths_idtoiso (a b : C) (e : a = b)
: idtoiso (maponpaths (functor_on_objects F) e)
  =
  functor_on_z_iso F (idtoiso e).
Proof.
  induction e.
  apply eq_z_iso.
  apply (! functor_id _ _ ).
Qed.

Hypothesis HC : is_univalent C.
Hypothesis HD : is_univalent D.

Lemma maponpaths_isotoid (a b : C) (i : z_iso a b)
: maponpaths (functor_on_objects F) (isotoid _ HC i)
  =
  isotoid _ HD (functor_on_z_iso F i).
Proof.
  apply (invmaponpathsweq (make_weq (idtoiso) (HD _ _ ))).
  simpl.
  rewrite maponpaths_idtoiso.
  repeat rewrite idtoiso_isotoid.
  apply idpath.
Qed.

End functors_and_idtoiso.

Notation "# F" := (functor_on_morphisms F)(at level 3) : cat. (* Notations do not survive the end of sections.  *)

Lemma idtoiso_functor_precompose
      {C₁ C₂ : category}
      (F : C₁ ⟶ C₂)
      {y : C₂}
      {x₁ x₂ : C₁}
      (p : x₁ = x₂)
      (f : F x₁ --> y)
  : idtoiso (maponpaths (λ z, F z) (!p)) · f
    =
    transportf (λ z, F z --> y) p f.
Proof.
  induction p.
  cbn.
  apply id_left.
Qed.

Definition transportf_functor_isotoid
           {C₁ C₂ : category}
           (HC₁ : is_univalent C₁)
           (F : C₁ ⟶ C₂)
           {y : C₂}
           {x₁ x₂ : C₁}
           (i : z_iso x₁ x₂)
           (f : F x₁ --> y)
  : transportf
      (λ z, F z --> y)
      (isotoid _ HC₁ i)
      f
    =
    #F (inv_from_z_iso i) · f.
Proof.
  rewrite <- idtoiso_functor_precompose.
  rewrite maponpaths_idtoiso.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

(** ** Functors preserve inverses *)

Lemma functor_on_inv_from_z_iso {C C' : precategory} (F : functor C C')
    {a b : ob C}(f : z_iso a b) :
      #F (inv_from_z_iso f) = inv_from_z_iso (functor_on_z_iso F f) .
Proof.
  destruct f.
  apply functor_on_inv_from_z_iso'.
Qed.

(** ** Conservative functors *)

(** The generic property of "reflecting" a property of a morphism. *)

Definition reflects_morphism {C D : category} (F : functor C D)
           (P : ∏ (C : category) (a b : ob C), C⟦a, b⟧ → UU) : UU :=
  ∏ a b f, P D (F a) (F b) (# F f) → P C a b f.

(** These are functors that reflect isomorphisms. F : C ⟶ D is conservative
    if whenever # F f is an iso, so is f. *)

Definition conservative {C D : category} (F : functor C D) : UU :=
  reflects_morphism F (@is_z_isomorphism).

Definition isaprop_conservative
           {C D : category}
           (F : functor C D)
  : isaprop (conservative F).
Proof.
  do 4 (use impred ; intro).
  apply isaprop_is_z_isomorphism.
Qed.

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
Notation "a ⟶ b" := (functor a b) : cat.
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

Local Notation "FF ^-1" := (fully_faithful_inv_hom FF _ _ ).

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
   (FF : fully_faithful F) (a b : C) (f : z_iso (F a) (F b)) :
  is_inverse_in_precat ((FF ^-1) f) ((FF ^-1) (inv_from_z_iso f)).
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
  apply z_iso_inv_after_z_iso.

  apply (invmaponpathsweq (weq_from_fully_faithful FF b b)).
  set (HFFab := homotweqinvweq (weq_from_fully_faithful FF a b)).
  set (HFFba := homotweqinvweq (weq_from_fully_faithful FF b a)).
  simpl in *.
  rewrite functor_comp.
  rewrite HFFab.
  rewrite HFFba.
  rewrite functor_id.
  apply z_iso_after_z_iso_inv.
Qed.

Lemma fully_faithful_reflects_iso_proof (C D : precategory)(F : functor C D)
        (FF : fully_faithful F)
    (a b : ob C) (f : z_iso (F a) (F b)) :
     is_z_isomorphism (FF^-1 f).
Proof.
  exists (FF^-1 (inv_from_z_iso f)).
  apply inv_of_ff_inv_is_inv.
Defined.

(** A slight restatement of the above: fully faithful functors are conservative. *)
Lemma fully_faithful_conservative {C D : category} (F : functor C D)
      (FF : fully_faithful F) : conservative F.
Proof.
  unfold conservative.
  intros a b f is_iso_Ff.
  use transportf.
  - exact (FF^-1 (# F f)).
  - apply fully_faithful_inv_hom_is_inv.
  - apply (fully_faithful_reflects_iso_proof _ _ _ _ _ _ (_,,is_iso_Ff)).
Defined.

Definition  iso_from_fully_faithful_reflection {C D : precategory} {F : functor C D}
        (HF : fully_faithful F)
    {a b : ob C} (f : z_iso (F a) (F b)) :
      z_iso a b.
Proof.
  exists (fully_faithful_inv_hom HF a b f).
  apply fully_faithful_reflects_iso_proof.
Defined.

Lemma functor_on_iso_iso_from_fully_faithful_reflection (C : precategory)(D : category)
      (F : functor C D) (HF : fully_faithful F) (a b : ob C)
   (f : z_iso (F a) (F b)) :
      functor_on_z_iso F
        (iso_from_fully_faithful_reflection HF f) = f.
Proof.
  apply eq_z_iso.
  simpl;
  apply (homotweqinvweq (weq_from_fully_faithful HF a b)).
Qed.

Lemma iso_from_fully_faithful_reflection_functor_on_iso (C : category)(D : precategory)
      (F : functor C D) (HF : fully_faithful F) (a b : ob C)
   (f : z_iso a b) :
      iso_from_fully_faithful_reflection HF (functor_on_z_iso F f) = f.
Proof.
  apply eq_z_iso.
  simpl;
  apply (homotinvweqweq (weq_from_fully_faithful HF a b)).
Qed.

Definition weq_ff_functor_on_z_iso {C D : category}{F : functor C D}
           (HF : fully_faithful F) (a b : ob C)
  : z_iso a b ≃ z_iso (F a) (F b).
Proof.
  exists (functor_on_z_iso F).
  apply (isweq_iso _ (iso_from_fully_faithful_reflection HF (a:=a)(b:=b))).
  - apply iso_from_fully_faithful_reflection_functor_on_iso.
  - apply functor_on_iso_iso_from_fully_faithful_reflection.
Defined.

(** Computation check *)

Lemma weq_ff_functor_on_iso_compute {C D : category} (F : functor C D)
      (HF : fully_faithful F) {a b : C} (f : z_iso a b)
: #F f = weq_ff_functor_on_z_iso HF _ _ f.
Proof.
apply idpath.
Qed.

Lemma functor_on_iso_iso_from_ff_reflection (C : precategory)(D : category)
      (F : functor C D) (HF : fully_faithful F) (a b : C)
      (f : z_iso (F a) (F b)):
  functor_on_z_iso F
                 (iso_from_fully_faithful_reflection HF f) = f.
Proof.
  apply eq_z_iso.
  simpl.
  apply (homotweqinvweq (weq_from_fully_faithful HF a b ) ).
Qed.

(** Alternative implementation of [weq_ff_functor_on_iso] *)

Definition reflects_isos {C D : precategory} (F : C ⟶ D) :=
  ∏ c c' (f : C⟦c,c'⟧), is_z_isomorphism (# F f) → is_z_isomorphism f.

Lemma isaprop_reflects_isos {C : category} {D : precategory} (F : C ⟶ D) : isaprop (reflects_isos F).
Proof.
apply impred; intros c; apply impred; intros c'.
apply impred; intros f; apply impred; intros f'.
apply isaprop_is_z_isomorphism.
Qed.

Lemma ff_reflects_is_iso (C D : precategory) (F : functor C D)
  (HF : fully_faithful F) : reflects_isos F.
Proof.
  intros a b f H.
  set (X:= fully_faithful_reflects_iso_proof _ _ F HF _ _ (_,,H)).
  simpl in X.
  set (T:= homotinvweqweq (weq_from_fully_faithful HF a b ) ).
  simpl in T.
  unfold fully_faithful_inv_hom in X.
  simpl in X.
  rewrite T in X.
  apply X.
Defined.


Definition weq_ff_functor_on_weq_isobandf {C D : category}
  {F : functor C D}
  (HF : fully_faithful F) (a b : C)
  : z_iso a b ≃ z_iso (F a) (F b).
Proof.
  use weqbandf.
  - apply (make_weq _ (HF a b)).
  - simpl; intro f.
    apply weqimplimpl.
    + intro H.
      exact (pr2(functor_on_z_iso _ (_,,H))).
    + apply ff_reflects_is_iso. apply HF.
    + apply isaprop_is_z_isomorphism.
    + apply isaprop_is_z_isomorphism.
Defined.

(** Computation check *)

Lemma weq_ff_functor_on_weq_isobandf_compute {C D : category} (F : functor C D)
      (HF : fully_faithful F) {a b : C} (f : z_iso a b)
: #F f = weq_ff_functor_on_weq_isobandf HF _ _ f.
Proof.
  apply idpath.
Defined.

Lemma ff_is_inclusion_on_objects {C D : category}
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
  ∏ b, (∑ a : ob C, z_iso (F a) b).

(** Split essentially surjective functors have "inverses" on objects, where we
    map d : ob D to the c : ob C such that F c ≅ d. *)
Definition split_essentially_surjective_inv_on_obj {C D : precategory_data}
           (F : functor C D) (HF : split_essentially_surjective F) : ob D → ob C :=
  λ d, (pr1 (HF d)).

Definition essentially_surjective {C D : precategory_data} (F : functor C D) :=
  ∏ b, ishinh (total2 (λ a, z_iso (F a) b)).

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
  apply (@z_iso_comp E _ (G (pr1 isoGe))).
  - apply functor_on_z_iso.
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
Defined.

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

(** Fully faithful functors induce equivalences on commutative triangles

    Compare to [faithful_reflects_commutative_triangle]. *)
Lemma fully_faithful_commutative_triangle_weq
      {C D : precategory} (F : functor C D) (fff : fully_faithful F)
      {X Y Z : ob C} (f : X --> Y) (g : Y --> Z) (h : X --> Z) :
  (f · g = h) ≃ (#F f · #F g = #F h).
Proof.
  apply (@weqcomp _ (# F (f · g) = # F h)).
  - eapply make_weq.
    apply (isweqmaponpaths (weq_from_fully_faithful fff _ _) (f · g) h).
  - use weq_iso; intros p.
    + refine (_ @ p).
      apply (!functor_comp _ _ _).
    + refine (_ @ p).
      apply (functor_comp _ _ _).
    + refine (path_assoc _ _ _ @ _).
      refine (maponpaths (λ pp, pp @ _) (pathsinv0r _) @ _).
      reflexivity.
    + cbn.
      refine (path_assoc _ _ _ @ _).
      refine (maponpaths (λ pp, pp @ _) (pathsinv0l _) @ _).
      reflexivity.
Qed.

(** ** Image on objects of a functor  *)
(** is used later to define the full image subcategory of a category [D]
       defined by a functor [F : C -> D] *)

Definition is_in_img_functor {C D : precategory_data} (F : functor C D)
      (d : ob D) :=
  ishinh (
  total2 (λ c : ob C, z_iso (F c) d)).

Definition sub_img_functor {C D : precategory_data}(F : functor C D) :
    hsubtype (ob D) :=
       λ d : ob D, is_in_img_functor F d.

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


(**
 Pseudomonic functors
 *)
Definition full_on_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y : C₁),
     issurjective (λ (f : z_iso x y), functor_on_z_iso F f).

Definition pseudomonic
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := faithful F × full_on_iso F.

Definition isweq_functor_on_iso_pseudomonic
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           (HF : pseudomonic F)
           (x y : C₁)
  : isweq (@functor_on_z_iso _ _ F x y).
Proof.
  intro g.
  use (factor_through_squash _ _ (pr2 HF x y g)).
  {
    apply isapropiscontr.
  }
  intro inv.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply isaset_z_iso ; apply homset_property | ] ;
       use subtypePath ; [ intro ; apply isaprop_is_z_isomorphism | ] ;
       use (maponpaths pr1 (proofirrelevance _ (pr1 HF x y g) (_ ,, _) (_ ,, _))) ;
       [ exact (maponpaths pr1 (pr2 φ₁)) | exact (maponpaths pr1 (pr2 φ₂)) ]).
  - exact inv.
Defined.

Definition isaprop_pseudomonic
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : isaprop (pseudomonic F).
Proof.
  use isapropdirprod.
  - apply isaprop_faithful.
  - do 2 (use impred ; intro).
    apply isapropissurjective.
Qed.


Notation "F ∙ G" := (functor_composite F G) : cat.
(* to input: type "\." with Agda input method *)
(* the old notation had the arguments in the opposite order *)

(* Notation "G □ F" := (functor_composite F G) (at level 35, only parsing) : cat. *)
(* to input: type "\Box" or "\square" or "\sqw" or "\sq" with Agda input method *)
