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

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
(*Local Notation "'hom' C" := (precategory_morphisms (C := C)) (at level 2).*)
Local Notation "f ;; g" := (compose f g)(at level 50).
Notation "[ C , D ]" := (functor_precategory C D).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).


Definition functor_compose {A B C : precategory} (hsB: has_homsets B) 
                           (hsC: has_homsets C) (F : ob [A, B, hsB])
      (G : ob [B , C, hsC]) : ob [A , C, hsC] := 
   functor_composite _ _ _ F G.


Local Notation "G 'O' F '{' hsB  hsC '}'" := 
        (functor_compose hsB hsC F G) (at level 200).
Local Notation "G 'o' F '{' hsB  hsC '}'" := 
        (functor_compose hsB hsC  F G : functor _ _ ) (at level 200).

(** * Whiskering: Composition of a natural transformation with a functor *)

(** Prewhiskering *)

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

Definition pre_whisker (A B C : precategory) (hsB : has_homsets B) (hsC : has_homsets C) 
   (F : ob [A, B, hsB])  (G H : ob [B, C, hsC]) (gamma : G --> H) : 
   functor_compose _ _ F G --> functor_compose _ _ F H.
Proof.
  exists (fun a => pr1 gamma (pr1 F a)).
  apply is_nat_trans_pre_whisker.
Defined.

(** Postwhiskering *)

Lemma is_precat_fun_fun_post_whisker (B C D : precategory) 
   (G H : functor B C) (gamma : nat_trans G  H) 
        (K : functor C D): 
  is_nat_trans (functor_composite _ _ _ G K) 
                         (functor_composite _ _ _ H K) 
     (fun b : B => #K (gamma b)).
Proof.
  unfold is_nat_trans.
  simpl in *.
  intros;
  repeat rewrite <- functor_comp.
  rewrite (nat_trans_ax gamma).
  apply idpath.
Qed.
(*
Definition post_whisker (B C D : precategory) 
   (G H : ob [B, C]) (gamma : G --> H) 
        (K : ob [C, D]) : K O G --> K O H.
Proof.
  exists (fun a : ob B => #(pr1 K) (pr1 gamma  a)).
  apply is_precat_fun_fun_post_whisker.
Defined.
*)
(** Precomposition with a functor is functorial *)
(** Postcomposition is, too, but that's not of our concern for now. *)

Definition pre_composition_functor_data (A B C : precategory) 
  (hsB: has_homsets B) (hsC: has_homsets C) 
      (H : ob [A, B, hsB]) : functor_data [B,C,hsC] [A,C,hsC].
Proof.
  exists (fun G => functor_compose _ _ H G).
  exact (fun a b gamma => pre_whisker _ _ _ _ _ H _ _ gamma).
Defined.

Lemma pre_composition_is_functor (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) 
  (H : [A, B, hsB]) :
    is_functor (pre_composition_functor_data A B C hsB hsC H).
Proof.
  split; simpl.
  intro G.
  apply nat_trans_eq.
  - apply hsC. 
  - intro a. apply idpath.
  - intros; apply nat_trans_eq.
    + apply hsC.
    + intro; apply idpath.
Qed.

Definition pre_composition_functor (A B C : precategory) (hsB: has_homsets B) (hsC: has_homsets C) 
   (H : [A , B, hsB]) : functor [B, C, hsC] [A, C, hsC].
Proof.
  exists (pre_composition_functor_data A B C hsB hsC H).
  apply pre_composition_is_functor.
Defined.



  






