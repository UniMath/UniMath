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
  (precategory_morphisms a b) (at level 50).
Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).
Local Notation "# F" := (functor_on_morphisms F) (at level 3).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

(* This should be moved upstream. Constructs the smallest eqrel
   containing a given relation *)
Section extras.

Variable A : UU.
Variable R0 : hrel A.

Definition isaprop_hProp (X : hProp) : isaprop X.
Proof.
exact (pr2 X).
Qed.

Lemma isaprop_eqrel_from_hrel a b :
  isaprop (∀ R : eqrel A, (∀ x y, R0 x y -> R x y) -> R a b).
Proof.
apply impred; intro R; apply impred; intro HR.
now apply isaprop_hProp.
Qed.

Definition eqrel_from_hrel : hrel A :=
  fun a b => hProppair _ (isaprop_eqrel_from_hrel a b).

Lemma iseqrel_eqrel_from_hrel : iseqrel eqrel_from_hrel.
Proof.
repeat split.
- intros x y z H1 H2 R HR.
  apply (eqreltrans R _ y); [ now apply H1 | now apply H2].
- now intros x R _; apply (eqrelrefl R).
- intros x y H R H'.
  now apply (eqrelsymm R), H.
Qed.

Lemma eqrel_impl a b : R0 a b -> eqrel_from_hrel a b.
Proof.
now intros H R HR; apply HR.
Qed.

(* eqrel_from_hrel is the *smallest* relation containing R0 *)
Lemma minimal_eqrel_from_hrel (R : eqrel A) (H : ∀ a b, R0 a b -> R a b) :
  ∀ a b, eqrel_from_hrel a b -> R a b.
Proof.
now intros a b H'; apply H'.
Qed.

End extras.

Arguments eqrel_from_hrel {_} _ _ _.

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

(** * colimits in HSET *)
Require Import UniMath.CategoryTheory.colimits.colimits.

Section colimits.

Variable g : graph.
Variable J : diagram g HSET.

Definition cobase : UU := Σ j : vertex g, pr1hSet (dob J j).

(* Theory about hprop is in UniMath.Foundations.Propositions *)
Definition rel0 : hrel cobase := λ (ia jb : cobase),
  hProppair (ishinh (Σ f : pr1 ia --> pr1 jb, dmor J f (pr2 ia) = pr2 jb))
            (isapropishinh _).

Definition rel : hrel cobase := eqrel_from_hrel rel0.

Lemma iseqrel_rel : iseqrel rel.
Proof.
now apply iseqrel_eqrel_from_hrel.
Qed.

Definition eqr : eqrel cobase := eqrelpair _ iseqrel_rel.

(* Defined in UniMath.Foundations.Sets *)
Definition colimit : HSET :=
  hSetpair (setquot eqr) (isasetsetquot _).

(*        
           (X,~)
            | \
            |   \
            |     \
  setquotpr |       \
            |         \
            |           \
            |             \
            V              V
           X/~ ----------> (Y,=)
*)

Definition injections j : dob J j --> colimit.
Proof.
intros Fj; apply (setquotpr _).
exact (tpair _ j Fj).
Defined.

(* Define the morphism out of the colimit *)
Section from_colimit.

(* Variables (c : ColimitCocone HSET J). *)
Variables (c : HSET) (fc : ∀ v : vertex g, HSET ⟦ dob J v, c ⟧).
Variable (Hc : ∀ (u v : vertex g) (e : edge u v), dmor J e ;; fc v = fc u).

Definition from_cobase : cobase -> pr1hSet c.
Proof.
now intro iA; apply (fc (pr1 iA) (pr2 iA)).
Defined.
  
Definition from_cobase_rel : hrel cobase.
Proof.
intros x x'; exists (from_cobase x = from_cobase x').
now apply setproperty.
Defined.

Definition from_cobase_eqrel : eqrel cobase.
Proof.
exists from_cobase_rel.
repeat split.
- intros x y z H1 H2.
  exact (pathscomp0 H1 H2).
- intros x y H.
  exact (pathsinv0 H).
Defined.

Lemma rel0_impl a b (Hab : rel0 a b) : from_cobase_eqrel a b.
Proof.
apply Hab; clear Hab; intro H; simpl.
destruct H as [f Hf].
generalize (toforallpaths _ _ _ (Hc (pr1 a) (pr1 b) f) (pr2 a)).
unfold compose, from_cobase; simpl; intro H.
now rewrite <- H, Hf.
Qed.

Lemma rel_impl a b (Hab : rel a b) : from_cobase_eqrel a b.
Proof.
now apply (@minimal_eqrel_from_hrel _ rel0); [apply rel0_impl|].
Qed.

Lemma iscomprel_from_base : iscomprelfun rel from_cobase.
Proof.
now intros a b; apply rel_impl.
Qed.

Definition from_colimit : colimit --> c.
Proof.
now simpl; apply (setquotuniv _ _ from_cobase iscomprel_from_base).
Defined.

End from_colimit.

Definition colimitCocone : Σ c : HSET, ∀ v : vertex g, HSET ⟦ dob J v, c ⟧ :=
  tpair _ colimit injections.

Definition colimitCoconeCommutes : ∀ (u v : vertex g) (e : edge u v),
  dmor J e ;; pr2 colimitCocone v = pr2 colimitCocone u.
Proof.
intros i j f.
apply funextfun; intros Fi; simpl.
unfold compose, injections; simpl.
apply (weqpathsinsetquot eqr), (eqrelsymm eqr), eqrel_impl, hinhpr; simpl.
now exists f.
Qed.

Definition foo (c : HSET) (fc : ∀ v : vertex g, HSET ⟦ dob J v, c ⟧)
  (Hc : ∀ (u v : vertex g) (e : edge u v), dmor J e ;; fc v = fc u) :
  Σ x : HSET ⟦ colimit, c ⟧, ∀ v : vertex g, injections v ;; x = fc v.
Proof.
exists (from_colimit _ fc Hc); intro i; simpl.
unfold injections, compose, from_colimit; simpl.
apply funextfun; intro Fi.
now rewrite (setquotunivcomm eqr).
Defined.

Definition ColimitCoconeHSET : ColimitCocone HSET J.
Proof.
refine (tpair _ _ _).
- refine (tpair _ _ _).
  + exact thing0.
  + apply thing. 
- simpl; unfold isColimitCocone.
intros c fc Hc.
unfold iscontr.
exists (foo _ fc Hc).
simpl; intro f. 
apply total2_paths_second_isaprop.
  apply impred.
  intro i.
  now apply has_homsets_HSET.
apply funextfun; intro x; simpl.
apply (surjectionisepitosets (setquotpr eqr)).
+ now apply issurjsetquotpr.
+ now apply pr2.
+ intro y.
destruct y as [i Fi].
unfold injections in f.
simpl in *.
destruct f as [f Hf]; simpl.
generalize (Hf i); unfold compose; simpl; intro H.
assert (H' := toforallpaths _ _ _ H Fi).
unfold compose in H'.
simpl in *.
eapply pathscomp0.
apply H'.
apply idpath.
Defined.

End colimits.
