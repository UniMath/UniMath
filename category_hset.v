(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents :  
	    
            Precategory HSET of hSets

	    HSET is a category
                	
           
************************************************************)



Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.
Require Import Foundations.Proof_of_Extensionality.funextfun. 

Require Import RezkCompletion.auxiliary_lemmas_HoTT.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.HLevel_n_is_of_hlevel_Sn.

Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).




(** * Precategory of hSets *)

Lemma isaset_set_fun_space (A B : hSet) : isaset (A -> B).
Proof.
  change isaset with (isofhlevel 2).
  apply impred.
  apply (fun _ => (pr2 B)).
Qed.

Definition hset_fun_space (A B : hSet) : hSet := 
  hSetpair _ (isaset_set_fun_space A B).

Definition hset_precategory_ob_mor : precategory_ob_mor :=
  tpair (fun ob : UU => ob -> ob -> hSet) hSet 
        (fun A B : hSet => hset_fun_space A B).

Definition hset_precategory_data : precategory_data :=
  precategory_data_pair hset_precategory_ob_mor (fun (A:hSet) (x : A) => x) 
     (fun (A B C : hSet) (f : A -> B) (g : B -> C) (x : A) => g (f x)).

Lemma is_precategory_hset_precategory_data :
  is_precategory hset_precategory_data.
Proof.
  repeat split; simpl.
  intros a b f.
  apply funextfunax; intros;
  apply idpath.
  intros;
  apply funextfunax; intros;
  apply idpath.
Qed.

Definition hset_precategory : precategory := 
  tpair _ _ is_precategory_hset_precategory_data.

Notation HSET := hset_precategory.

(* 
  Canonical Structure hset_precategory. :-)
*)


(** * The precategory of hSets is a category. *)

(** ** Equivalence between isomorphisms and weak equivalences 
       of two hsets. 
*)

(** Given an iso, we construct a weak equivalence.
   This is basically unpacking and packing again.
*)

Lemma hset_iso_is_equiv (A B : ob HSET) 
   (f : iso A B) : isweq (pr1 f).
Proof.

  destruct f as [f fax]; simpl in *.
  apply (gradth _ (pr1 fax)).
  destruct fax as [g [eta eps]]; simpl in *.
  unfold compose, identity in *; 
  simpl in *.
  intro x.
  apply (toforallpaths _ _ _ eta).
  destruct fax as [g [eta eps]]; simpl in *.
  unfold compose, identity in *; 
  simpl in *.
  intro x.
  apply (toforallpaths _ _ _ eps).
Defined.
  

Lemma hset_iso_equiv (A B : ob HSET) : iso A B -> weq (pr1 A) (pr1 B).
Proof.
  intro f.
  exists (pr1 f).
  apply hset_iso_is_equiv.
Defined.

(** Given a weak equivalence, we construct an iso.
    Again mostly unwrapping and packing. 
*)

Lemma hset_equiv_is_iso (A B : hSet) 
      (f : weq (pr1 A) (pr1 B)) :
           is_isomorphism (C:=HSET) (pr1 f).
Proof.
  exists (invmap f).
  split; simpl.
  apply funextfunax; intro x; simpl in *.
  unfold compose, identity; simpl. 
  apply homotinvweqweq.
  apply funextfunax; intro x; simpl in *.
  unfold compose, identity; simpl.
  apply homotweqinvweq.
Defined.

Lemma hset_equiv_iso (A B : ob HSET) : weq (pr1 A) (pr1 B) -> iso A B.
Proof.
  intro f.
  simpl in *.
  exists (pr1 f).
  apply hset_equiv_is_iso.
Defined.

(** Both maps defined above are weak equivalences. *)


Lemma hset_iso_equiv_is_equiv (A B : ob HSET) : isweq (hset_iso_equiv A B).
Proof.
  apply (gradth _ (hset_equiv_iso A B)).
  intro; apply eq_iso; reflexivity.  
  intro; apply total2_paths_hProp.
    intro; apply isapropisweq.
    reflexivity.
Qed.

Definition hset_iso_equiv_weq (A B : ob HSET) : weq (iso A B) (weq (pr1 A) (pr1 B)).
Proof.
  exists (hset_iso_equiv A B).
  apply hset_iso_equiv_is_equiv.
Defined.

Lemma hset_equiv_iso_is_equiv (A B : ob HSET) : isweq (hset_equiv_iso A B).
Proof.
  apply (gradth _ (hset_iso_equiv A B)).
  intro f.
  apply total2_paths_hProp. 
    apply isapropisweq.
    reflexivity.
  intro; apply eq_iso.
  reflexivity.
Qed.

Definition hset_equiv_iso_weq (A B : ob HSET) :
  weq (weq (pr1 A) (pr1 B))(iso A B).
Proof.
  exists (hset_equiv_iso A B).
  apply hset_equiv_iso_is_equiv.
Defined.
  
(** ** HSET is a category. *)

Definition univalenceweq (X X' : UU) : weq (X == X') (weq X X') :=
   tpair _ _ (univalenceaxiom X X').

Definition hset_id_iso_weq (A B : ob HSET) :
  weq (A == B) (iso A B) :=
  weqcomp (UA_for_HLevels 2 A B) (hset_equiv_iso_weq A B).


(** The map [precat_paths_to_iso] 
    for which we need to show [isweq] is actually 
    equal to the carrier of the weak equivalence we 
    constructed above.
    We use this fact to show that that [precat_paths_to_iso]
    is an equivalence.
*)

Lemma hset_id_iso_weq_is (A B : ob HSET):
    @idtoiso _ A B == pr1 (hset_id_iso_weq A B).
Proof.
  apply funextfunax.
  intro p; elim p.
  apply eq_iso; simpl.
  apply funextfun;
  intro x; 
  destruct A. 
  apply idpath.
Defined.


Lemma is_weq_precat_paths_to_iso_hset (A B : ob HSET):
   isweq (@idtoiso _ A B).
Proof.
  rewrite hset_id_iso_weq_is.
  apply (pr2 (hset_id_iso_weq A B)).
Defined.

Lemma is_category_HSET : is_category HSET.
Proof.
  unfold is_category.
  apply is_weq_precat_paths_to_iso_hset.
Defined.

















