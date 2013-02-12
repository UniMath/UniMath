(** **********************************************************

Benedikt Ahrens and Chris Kapulkin
january 2013


************************************************************)


(** **********************************************************

Contents :  
	    
            Precategory HSET of hSets

	    HSET is a category
                	
           
************************************************************)



Require Import uu0.
Require Import hProp.
Require Import hSet.
Require Import funextfun. 

Require Import auxiliary_lemmas_HoTT.

Require Import precategories.
Require Import HLevel_n_is_of_hlevel_Sn.


Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).




(** * Precategory of hSets *)

Lemma isaset_set_fun_space (A B : hSet) : isaset (A -> B).
Proof.
  change isaset with (isofhlevel 2).
  apply impred.
  apply (fun _ => B).
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
Qed.
  

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
  simpl.
  set (H := homotweqinvweq f).
  set (H':= homotinvweqweq f).
  split; simpl.
  apply funextfunax; intro x; simpl in *.
  unfold compose, identity; simpl.
  apply H'.
  apply funextfunax; intro x; simpl in *.
  unfold compose, identity; simpl.
  apply H.
Qed.

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
  intro f.
  assert (H : pr1 (hset_equiv_iso A B (hset_iso_equiv A B f)) ==
              pr1 f).
  simpl. 
  apply idpath.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_isomorphism.
  intro g.
  assert (H : pr1 (hset_iso_equiv A B (hset_equiv_iso A B g)) == 
              pr1 g).
  simpl. 
  apply idpath.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isapropisweq.
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
  assert (H : pr1 (hset_iso_equiv A B (hset_equiv_iso A B f)) ==
              pr1 f).
  simpl. 
  apply idpath.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isapropisweq.
  intro g.
  assert (H : pr1 (hset_equiv_iso A B (hset_iso_equiv A B g)) == 
              pr1 g).
  simpl. 
  apply idpath.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_isomorphism.
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
    precat_paths_to_iso A B == pr1 (hset_id_iso_weq A B).
Proof.
  apply funextfunax.
  intro p.
  elim p.
  simpl.
  assert (H : pr1 (identity_iso A) ==
              pr1 (hset_equiv_iso A A (pr1 (UA_for_HLevels 2 A A) (idpath A)))).
  
             simpl.
  simpl in *.
  apply funextfun.
  unfold identity. simpl.
  intro x; 
  simpl. clear p.
  destruct A as [A As].
  simpl. apply idpath.
  
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_is_isomorphism.
Defined.


Lemma is_weq_precat_paths_to_iso_hset (A B : ob HSET):
   isweq (precat_paths_to_iso A B).
Proof.
  rewrite hset_id_iso_weq_is.
  apply (hset_id_iso_weq A B).
Qed.

Lemma is_category_HSET : is_category HSET.
Proof.
  unfold is_category.
  apply is_weq_precat_paths_to_iso_hset.
Qed.

















