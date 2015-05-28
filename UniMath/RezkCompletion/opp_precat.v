
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Definition of opposite category and functor

************************************************************)

Require Import Foundations.Generalities.uu0.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50, left associativity).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").

(** * The opposite precategory of a precategory *)

Definition opp_precat_ob_mor (C : precategory_ob_mor) : precategory_ob_mor :=
   tpair (fun ob : UU => ob -> ob -> UU) C (fun a b : C => b --> a ).

Definition opp_precat_data (C : precategory_data) : precategory_data :=
  tpair _ _ (tpair _ (fun c : opp_precat_ob_mor C => identity c)
                     (fun (a b c : opp_precat_ob_mor C) f g => g ;; f)).

Lemma is_precat_opp_precat_data (C : precategory) : is_precategory (opp_precat_data C).
Proof.
repeat split; intros; unfold compose; simpl.
- apply id_right.
- apply id_left.
- rewrite assoc; apply idpath.
Qed.

Definition opp_precat (C : precategory) : precategory :=
  tpair _ (opp_precat_data C) (is_precat_opp_precat_data C).

Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

Definition opp_iso {C : precategory} {a b : C} : @iso C a b -> @iso C^op b a.
intro f.
exists (pr1 f).
set (T := is_z_iso_from_is_iso _ (pr2 f)).
apply (is_iso_qinv (C:=C^op) _ (pr1 T)).
split; [ apply (pr2 (pr2 T)) | apply (pr1 (pr2 T)) ].
Defined.

Lemma has_homsets_opp {C : precategory} (hsC : has_homsets C) : has_homsets C^op.
Proof. intros a b; apply hsC. Qed.


(** * The opposite functor *)

Definition functor_opp_data {C D : precategory} (F : functor C D) :
  functor_data C^op D^op :=
    tpair (fun F : C^op -> D^op => forall a b, a --> b -> F a --> F b) F
          (fun (a b : C) (f : b --> a) => functor_on_morphisms F f).

Lemma is_functor_functor_opp {C D : precategory} (F : functor C D) :
  is_functor (functor_opp_data F).
Proof. split; intros; [ apply (functor_id F) | apply (functor_comp F) ]. Qed.

Definition functor_opp {C D : precategory} (F : functor C D) : functor C^op D^op :=
  tpair _ _ (is_functor_functor_opp F).

Lemma functor_opp_identity {C : precategory} (hsC : has_homsets C) :
  functor_opp (functor_identity C) = functor_identity C^op.
Proof. apply (functor_eq _ _ (has_homsets_opp hsC)); trivial. Qed.

Lemma functor_opp_composite {C D E : precategory} (F : functor C D) (G : functor D E)
  (hsE : has_homsets E) : functor_opp (functor_composite _ _ _ F G) =
                          functor_composite _ _ _ (functor_opp F) (functor_opp G).
Proof. apply (functor_eq _ _ (has_homsets_opp hsE)); trivial. Qed.
