(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : 

- Precomposition with a functor for 
   - functors and
   - natural transformations (whiskering)

- Functoriality of precomposition	

- Precomposition with an essentially surjective 
	   functor yields a faithful functor

************************************************************)

Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
(*Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).*)
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").
Notation "[ C , D ]" := (functor_precategory C D).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).


Definition functor_compose {A B C : precategory} (hsB: has_homsets B) 
                           (hsC: has_homsets C) (F : ob [A, B, hsB])
      (G : ob [B , C, hsC]) : ob [A , C, hsC] := 
   functor_composite _ _ _ F G.

(*
Local Notation "G 'O' F '{' hsB  hsC '}'" := 
        (functor_compose hsB hsC F G) (at level 200).
Local Notation "G 'o' F '{' hsB  hsC '}'" := 
        (functor_compose hsB hsC  F G : functor _ _ ) (at level 200).
*)
(** * Whiskering: Composition of a natural transformation with a functor *)

(** Prewhiskering *)

Lemma is_nat_trans_pre_whisker (A B C : precategory_data)
   (F : functor_data A B) (G H : functor_data B C) (gamma : nat_trans G H) :
   is_nat_trans 
        (functor_composite_data F G) 
        (functor_composite_data F H) 
   (fun a : A => gamma (F a)).
Proof.
  intros a b f; simpl.
  apply nat_trans_ax.
Defined.
 
(*
Lemma is_nat_trans_pre_whisker (A B C : precategory) (hsB: has_homsets B) 
   (hsC: has_homsets C) (F : functor A B)
   (G H : functor B C) (gamma : nat_trans G H) : 
  is_nat_trans (functor_compose hsB hsC F G : functor _ _ ) 
               (functor_compose hsB hsC F H : functor _ _ )
     (fun a : ob A =>  gamma (F a)).
Proof.
  unfold is_nat_trans.
  intros; simpl;
  rewrite nat_trans_ax.
  apply idpath.
Qed.
*)

(*
Definition pre_whisker (A B C : precategory) (hsB : has_homsets B) (hsC : has_homsets C) 
   (F : ob [A, B, hsB])  (G H : ob [B, C, hsC]) (gamma : G --> H) : 
   functor_compose _ _ F G --> functor_compose _ _ F H.
Proof.
  exists (fun a => pr1 gamma (pr1 F a)).
  apply is_nat_trans_pre_whisker.
Defined.
*)

Definition pre_whisker {A B C : precategory_data}
   (F : functor_data A B)  {G H : functor_data B C} (gamma : nat_trans G H) : 
   nat_trans (functor_composite_data F G)  (functor_composite_data F H).
Proof.
  exists (fun a => pr1 gamma (pr1 F a)).
  apply is_nat_trans_pre_whisker.
Defined.



(** Postwhiskering *)

Lemma is_nat_trans_post_whisker (B C D : precategory_data) 
   (G H : functor_data B C) (gamma : nat_trans G  H) 
        (K : functor C D): 
  is_nat_trans (functor_composite_data  G K) 
                         (functor_composite_data H K) 
     (fun b : B => #K (gamma b)).
Proof.
  unfold is_nat_trans.
  simpl in *.
  intros;
  repeat rewrite <- functor_comp.
  rewrite (nat_trans_ax gamma).
  apply idpath.
Qed.

Definition post_whisker {B C D : precategory_data}
   {G H : functor_data B C} (gamma : nat_trans G H) 
        (K : functor C D) 
  : nat_trans (functor_composite_data G K) (functor_composite_data H K).
Proof.
  exists (fun a : ob B => #(pr1 K) (pr1 gamma  a)).
  apply is_nat_trans_post_whisker.
Defined.

(** Precomposition with a functor is functorial *)
(** Postcomposition is, too, but that's not of our concern for now. *)

Definition pre_composition_functor_data (A B C : precategory) 
  (hsB: has_homsets B) (hsC: has_homsets C) 
      (H : ob [A, B, hsB]) : functor_data [B,C,hsC] [A,C,hsC].
Proof.
  exists (fun G => functor_compose _ _ H G).
  exact (fun a b gamma => pre_whisker (pr1 H)  gamma).
Defined.


Lemma pre_whisker_identity (A B : precategory_data) (C : precategory)(hsC : has_homsets C)
  (H : functor_data A B) (G : functor_data B C)
  : pre_whisker H (nat_trans_id G) =
   nat_trans_id (functor_composite_data H G).
Proof.
  apply nat_trans_eq.
  - apply hsC.
  - intro a. apply idpath.
Qed.

Lemma pre_whisker_composition (A B : precategory_data) (C : precategory)
  (hsC : has_homsets C)
  (H : functor_data A B) (a b c : functor_data B C)
  (f : nat_trans a b) (g : nat_trans b c)
  : pre_whisker H (nat_trans_comp _ _ _ f g) =
     nat_trans_comp _ _ _ (pre_whisker H f) (pre_whisker H g).
Proof.
  apply nat_trans_eq.
  - apply hsC.
  - intro; simpl.
    apply idpath.
Qed.

Lemma pre_composition_is_functor (A B C : precategory) (hsB: has_homsets B) 
  (hsC: has_homsets C)  (H : [A, B, hsB]) :
    is_functor (pre_composition_functor_data A B C hsB hsC H).
Proof.
  split; simpl in *.
  - unfold functor_idax .
    intros.
    apply pre_whisker_identity.
    assumption.
  - unfold functor_compax .
    intros.
    apply pre_whisker_composition.
    assumption.
Qed.

Definition pre_composition_functor (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) 
   (H : [A , B, hsB]) : functor [B, C, hsC] [A, C, hsC].
Proof.
  exists (pre_composition_functor_data A B C hsB hsC H).
  apply pre_composition_is_functor.
Defined.



  






