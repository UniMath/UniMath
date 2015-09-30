(** **********************************************************

Started by: Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013

Extended by: Anders Mörtberg

************************************************************)


(** **********************************************************

Contents :  
	    
            Precategory HSET of hSets

	    HSET is a category
                	
           
************************************************************)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.FunctionalExtensionality. 

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.HLevel_n_is_of_hlevel_Sn.

Local Notation "a --> b" :=
  (precategory_morphisms a b) (at level 50, left associativity).

Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

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
  tpair (fun ob : UU => ob -> ob -> UU) hSet 
        (fun A B : hSet => hset_fun_space A B).

Definition hset_precategory_data : precategory_data :=
  precategory_data_pair hset_precategory_ob_mor (fun (A:hSet) (x : A) => x) 
     (fun (A B C : hSet) (f : A -> B) (g : B -> C) (x : A) => g (f x)).

Lemma is_precategory_hset_precategory_data :
  is_precategory hset_precategory_data.
Proof.
  repeat split; simpl.
Qed.

Definition hset_precategory : precategory := 
  tpair _ _ is_precategory_hset_precategory_data.

Notation HSET := hset_precategory.

Lemma has_homsets_HSET : has_homsets HSET.
Proof. intros a b; apply isaset_set_fun_space. Qed.

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
  apply (gradth _ (inv_from_iso f)).
  - intro x. 
    set (T:=iso_inv_after_iso f). 
    set (T':=toforallpaths _ _ _ T). apply T'.
  - intro x.
    apply (toforallpaths _ _ _ (iso_after_iso_inv f)).
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
  apply (is_iso_qinv (C:=HSET) _ (invmap f)).
  split; simpl.
  - apply funextfunax; intro x; simpl in *.
    unfold compose, identity; simpl. 
    apply homotinvweqweq.
  - apply funextfunax; intro x; simpl in *.
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
  intro; apply eq_iso. 
  - reflexivity.  
  - intro; apply total2_paths_isaprop.
    + intro; apply isapropisweq.
    + reflexivity.
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
  apply total2_paths_isaprop. 
    apply isapropisweq.
    reflexivity.
  intro; apply eq_iso.
  - reflexivity.
Qed.

Definition hset_equiv_iso_weq (A B : ob HSET) :
  weq (weq (pr1 A) (pr1 B))(iso A B).
Proof.
  exists (hset_equiv_iso A B).
  apply hset_equiv_iso_is_equiv.
Defined.
  
(** ** HSET is a category. *)

Definition univalenceweq (X X' : UU) : weq (X = X') (weq X X') :=
   tpair _ _ (univalenceaxiom X X').

Definition hset_id_iso_weq (A B : ob HSET) :
  weq (A = B) (iso A B) :=
  weqcomp (UA_for_HLevels 2 A B) (hset_equiv_iso_weq A B).


(** The map [precat_paths_to_iso] 
    for which we need to show [isweq] is actually 
    equal to the carrier of the weak equivalence we 
    constructed above.
    We use this fact to show that that [precat_paths_to_iso]
    is an equivalence.
*)

Lemma hset_id_iso_weq_is (A B : ob HSET):
    @idtoiso _ A B = pr1 (hset_id_iso_weq A B).
Proof.
  apply funextfunax.
  intro p; elim p.
  apply eq_iso; simpl.
  - apply funextfun;
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
  split.
  - apply is_weq_precat_paths_to_iso_hset.
  - apply has_homsets_HSET.
Defined.






(***** NEW STUFF *)

Section rel_extras.

Variable A : UU.
Variable R0 : hrel A.
(* Variable P : UU -> hProp. *)

Definition isaprop_hProp (X : hProp) : isaprop X.
Proof. exact (pr2 X). Qed.

Lemma isaprop_eqrel_from_hrel a b :
  isaprop (∀ R : eqrel A, (∀ x y, R0 x y -> R x y) -> R a b).
Proof.
repeat (apply impred; intro).
now apply isaprop_hProp.
Qed.

Definition eqrel_from_hrel : hrel A :=
  fun a b => hProppair _ (isaprop_eqrel_from_hrel a b).

Lemma iseqrel_eqrel_from_hrel : iseqrel eqrel_from_hrel.
Proof.
repeat split.
- intros x y z; simpl.
  unfold eqrel_from_hrel; intros H1 H2 R HR.
  apply (eqreltrans R _ y); [ now apply H1 | now apply H2].
- intros x R _; apply (eqrelrefl R).
- intros x y H R H'.
  apply (eqrelsymm R).
  now apply H.
Qed.

Lemma eqrel_impl a b : R0 a b -> eqrel_from_hrel a b.
Proof. intros H R HR; now apply HR. Qed.

End rel_extras.

Section colimits.

Variable (J : precategory).
Variable (F : functor J HSET).

(* TODO: Define using Σ = Sigma *)
(* Definition test x := total2 (x). *)

(* TODO: Define notation for pr1hSet? Or can we trigger computation so that
   coercion "ob  HSET = hSet :> UU" can be applied? *)
Definition cobase : UU := total2 (fun j => pr1hSet (F j)).

(* hprop stuff is in UniMath.Foundations.Propositions *)
Definition relation : cobase -> cobase -> hProp :=
  fun ja j'a' => hProppair (ishinh (total2 (fun f : pr1 ja --> pr1 j'a' => # F f (pr2 ja) = pr2 j'a'))) (isapropishinh _).

(* Defined in UniMath.Foundations.Sets *)
Definition colimit := setquot relation.

(* 

  (X,~) ----------
    |             \
    |setquotpr     \
    V               \
   X/~ -----------> (Y,=)

*)

Lemma eqrel_relation : iseqrel relation.
Proof.
repeat split.
intros x y z H1 H2.
apply (H1 (relation x z)); clear H1; intro H1.
apply (H2 (relation x z)); clear H2; intro H2.
apply hinhpr.
case H1; clear H1; intros f Hf.
case H2; clear H2; intros g Hg.
exists (f ;; g).
rewrite <- Hg, <- Hf.
rewrite functor_comp.
apply idpath.

intros x.
apply hinhpr.
exists (identity (pr1 x)).
rewrite functor_id.
apply idpath.

intros x y H.
apply (H (relation y x)); clear H; intro H.
case H; clear H; intros f Hf.
apply hinhpr.



Definition projection (j : J) : pr1hSet (F j) -> colimit.
intros fj.
unfold colimit..
eapply setquotpr.

simpl.

End colimits. 