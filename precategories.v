(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents :  Definition of 
		Precategories, 
	        Categories (aka saturated precategories)         	
                Setcategories
                
                Isomorphisms
                  various lemmas:
                    uniqueness of inverse, composition etc.
                    stability under composition
                
                Categories have groupoid as objects
                	
           
************************************************************)

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** * Definition of a precategory *)

Definition precategory_ob_mor := total2 (
  fun ob : UU => ob -> ob -> hSet).

Definition precategory_ob_mor_pair (ob : UU)(mor : ob -> ob -> hSet) :
    precategory_ob_mor := tpair _ ob mor.

Definition ob (C : precategory_ob_mor) : Type := @pr1 _ _ C.
Coercion ob : precategory_ob_mor >-> Sortclass.

Definition precategory_morphisms { C : precategory_ob_mor } : 
       C ->  C -> hSet := pr2 C.

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

Definition precategory_data := total2 (
   fun C : precategory_ob_mor =>
     dirprod (forall c : C, c --> c) (* identities *) 
             (forall a b c : C,
                 a --> b -> b --> c -> a --> c)).

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

Definition precategory_eq_morphism (C : precategory_data)
   (a b : C) (H : a == b) : a --> b.
Proof.
  destruct H.
  exact (identity a).
Defined.

Definition precategory_eq_morphism_inv (C : precategory_data) 
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
      (H H': a == b) : precategory_eq_morphism C a b H == 
                       precategory_eq_morphism C a b H'.
Proof.
  assert (h : H == H').
  apply uip. apply (pr2 C).
  apply (maponpaths (precategory_eq_morphism C a b) h).
Qed.

(** * Isomorphisms in a precategory *)

(** ** Definition of isomorphisms *)

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
  intros f g H.
  destruct f as [[a b] f]. simpl in *.
  destruct g as [[b' c] g]. simpl in *.
  unfold precategory_target in H; simpl in H.
  unfold precategory_source in H; simpl in H. 
  simpl.
  exists (dirprodpair a c). simpl.
  exact ((f ;; precategory_eq_morphism C b b' H) ;; g).
Defined.

Definition precategory_total_comp (C : precategory_data) : 
      forall f g : total_morphisms C,
        precategory_target C f == precategory_source C g ->
         total_morphisms C := 
  fun f g H => 
     tpair _ (dirprodpair (pr1 (pr1 f))(pr2 (pr1 g)))
        ((pr2 f ;; precategory_eq_morphism _ _ _ H) ;; pr2 g).



