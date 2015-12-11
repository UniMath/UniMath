
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Definition of opposite category and functor

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.


(** * The opposite precategory of a precategory *)

Definition opp_precat_ob_mor (C : precategory_ob_mor) : precategory_ob_mor :=
   tpair (fun ob : UU => ob -> ob -> UU) C (fun a b : C => C⟦b, a⟧ ).

Definition opp_precat_data (C : precategory_data) : precategory_data :=
  tpair _ _ (tpair _ (fun c : opp_precat_ob_mor C => identity c)
                     (fun (a b c : opp_precat_ob_mor C) f g => g ;; f)).

Lemma is_precat_opp_precat_data (C : precategory) : is_precategory (opp_precat_data C).
Proof.
  split.
  { split.
    { intros. apply id_right. }
    { intros. apply id_left. } }
  { abstract (intros; apply pathsinv0, assoc). }
Defined.

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
Proof. intros a b; apply hsC. Defined.


(** * The opposite functor *)

Definition functor_opp_data {C D : precategory} (F : functor C D) :
  functor_data C^op D^op :=
    tpair (fun F : C^op -> D^op => forall a b, C^op ⟦a, b⟧ -> D^op ⟦F a, F b⟧) F
          (fun (a b : C) (f : C⟦b, a⟧) => functor_on_morphisms F f).

Lemma is_functor_functor_opp {C D : precategory} (F : functor C D) :
  is_functor (functor_opp_data F).
Proof. split; intros.
  - unfold functor_idax; simpl.
    apply (functor_id F).
  - unfold functor_compax; simpl.
    intros.
    apply (functor_comp F).
Qed.

Definition functor_opp {C D : precategory} (F : functor C D) : functor C^op D^op :=
  tpair _ _ (is_functor_functor_opp F).

Lemma functor_opp_identity {C : precategory} (hsC : has_homsets C) :
  functor_opp (functor_identity C) = functor_identity C^op.
Proof. apply (functor_eq _ _ (has_homsets_opp hsC)); trivial. Qed.

Lemma functor_opp_composite {C D E : precategory} (F : functor C D) (G : functor D E)
  (hsE : has_homsets E) : functor_opp (functor_composite _ _ _ F G) =
                          functor_composite _ _ _ (functor_opp F) (functor_opp G).
Proof. apply (functor_eq _ _ (has_homsets_opp hsE)); trivial. Qed.

Definition from_opp_to_opp_opp (A C : precategory) (hsC : has_homsets C) :
  functor_data [A, C, hsC]^op [A^op, C^op, has_homsets_opp hsC].
Proof.
apply (tpair _ functor_opp).
simpl; intros F G α.
refine (tpair _ _ _).
+ simpl; intro a; apply α.
+ abstract (intros a b f; simpl in *;
            apply pathsinv0, (nat_trans_ax α)).
Defined.

Lemma is_functor_from_opp_to_opp_opp (A C : precategory) (hsC : has_homsets C) :
  is_functor (from_opp_to_opp_opp A C hsC).
Proof.
split.
- now intro F; simpl; apply (nat_trans_eq (has_homsets_opp hsC)); simpl; intro a.
- now intros F G H α β; simpl; apply (nat_trans_eq (has_homsets_opp hsC)); simpl; intro a.
Qed.

Definition functor_from_opp_to_opp_opp (A C : precategory) (hsC : has_homsets C) :
  functor [A, C, hsC]^op [A^op, C^op, has_homsets_opp hsC] :=
    tpair _ _ (is_functor_from_opp_to_opp_opp A C hsC).

Definition from_opp_opp_to_opp (A C : precategory) (hsC : has_homsets C) :
  functor_data [A^op, C^op, has_homsets_opp hsC] [A, C, hsC]^op.
Proof.
refine (tpair _ _ _); simpl.
- intro F.
  refine (tpair _ _ _).
  + exists F.
    apply (fun a b f => # F f).
  + abstract (split; [ intro a; apply (functor_id F)
                     | intros a b c f g; apply (functor_comp F)]).
- intros F G α; exists α.
  abstract (intros a b f; apply pathsinv0, (nat_trans_ax α)).
Defined.

Lemma is_functor_from_opp_opp_to_opp (A C : precategory) (hsC : has_homsets C) :
  is_functor (from_opp_opp_to_opp A C hsC).
Proof.
split.
- now intro F; simpl; apply (nat_trans_eq hsC); intro a.
- now intros F G H α β; simpl; apply (nat_trans_eq hsC); intro a.
Qed.

Definition functor_from_opp_opp_to_opp (A C : precategory) (hsC : has_homsets C) :
  functor [A^op, C^op, has_homsets_opp hsC] [A, C, hsC]^op :=
    tpair _ _ (is_functor_from_opp_opp_to_opp A C hsC).
