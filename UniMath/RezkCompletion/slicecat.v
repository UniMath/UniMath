(** Definition of slice categories *)

Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50, left associativity).
Local Notation "f ;; g"  := (compose f g) (at level 50, format "f  ;;  g").

(* Slice category:

Given a category C and x : obj C. The slice category C/x is given by:

- obj C/x: pairs (a,f) where f : a -> x

- morphism (a,f) -> (b,g): morphism h : a -> b with

           h
       a - - -> b
       |       /
       |     /
     f |   / g
       | /
       v
       x
    
    where h ;; g = f

*)

(* I prefer having as much implicit as possible in order not having *)
(* to type so many _ everywhere... *)
Arguments tpair {T _} _ _.
Arguments id_left {_ _ _} _.

Section slicecat_def.

Variable C : precategory.
Variable x : ob C.

Definition slicecat_ob := total2 (fun (a : C) => a --> x).
Definition slicecat_mor (f g : slicecat_ob) :=
  total2 (fun h : pr1 f --> pr1 g => h ;; pr2 g = pr2 f).

Definition slice_precategory_ob_mor : precategory_ob_mor := tpair _ slicecat_mor.
   
Definition id_slice_precat (c : slice_precategory_ob_mor) : c --> c := tpair _ (id_left (pr2 c)).

(* It is not so nice to define terms using tactics, how to do it properly? *)
Definition comp_slice_precat (a b c : slice_precategory_ob_mor)
                             (f : a --> b) (g : b --> c) : a --> c.
apply (@tpair _ _ (pr1 f ;; pr1 g)).
rewrite <- assoc.
rewrite (pr2 g).
exact (pr2 f).
Defined.

Definition slice_precategory_data : precategory_data :=
  precategory_data_pair _ id_slice_precat comp_slice_precat.

Lemma is_precategory_slice_precategory_data (hsC : has_homsets C) :
  is_precategory slice_precategory_data.
Proof.
repeat split; unfold identity; unfold compose; simpl;
              unfold id_slice_precat; unfold comp_slice_precat; simpl.
* intros a b f.
  case f; clear f; intros h hP.
  apply total2_paths2_second_isaprop; [ apply id_left | apply hsC ].
* intros a b f.
  case f; clear f; intros h hP.
  apply total2_paths2_second_isaprop; [ apply id_right | apply hsC ].
* intros a b c d f g h.
  apply total2_paths2_second_isaprop; [ apply assoc | apply hsC ].
Qed.

Definition slice_precategory (hsC : has_homsets C) : precategory :=
  tpair _ (is_precategory_slice_precategory_data hsC).

Lemma isasetisofhlevelssz (X : UU) : isofhlevel (S (S O)) X -> isaset X.
Proof.
  unfold isaset; unfold isaprop; trivial.
Qed.

Lemma has_homsets_slice_precategory (hsC : has_homsets C) :
  has_homsets (slice_precategory hsC).
Proof.
unfold has_homsets; intros a b.
case a; clear a; intros a f; case b; clear b; intros b g; simpl.
unfold slicecat_mor; simpl.
apply isasetisofhlevelssz.
apply isofhleveltotal2.
  apply hsC.
intro h.
apply hlevelntosn.
apply hsC.
Qed.

End slicecat_def.

