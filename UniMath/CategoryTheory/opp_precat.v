
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Definition of opposite category and functor

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

(** * The opposite precategory of a precategory *)

Definition opp_precat_ob_mor (C : precategory_ob_mor) : precategory_ob_mor :=
   tpair (λ ob : UU, ob -> ob -> UU) C (λ a b : C, C⟦b, a⟧ ).

Definition opp_precat_data (C : precategory_data) : precategory_data :=
  tpair _ _ (tpair _ (λ c : opp_precat_ob_mor C, identity c)
                     (λ (a b c : opp_precat_ob_mor C) f g, g · f)).

Lemma is_precat_opp_precat_data (C : precategory) : is_precategory (opp_precat_data C).
Proof.
repeat split; intros; unfold compose; simpl.
- apply id_right.
- apply id_left.
- apply pathsinv0.              (* this prevents C^op^op and C being the same, judgmentally *)
  apply assoc.
Qed.

Definition opp_precat (C : precategory) : precategory :=
  tpair _ (opp_precat_data C) (is_precat_opp_precat_data C).

Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op") : cat.

Definition opp_ob {C : precategory} (c : ob C) : ob C^op := c.

Definition rm_opp_ob {C : precategory} (cop : ob C^op) : ob C := cop.

Definition opp_mor {C : precategory} {b c : C} (f : C⟦b, c⟧) : C^op⟦c, b⟧ := f.

Definition rm_opp_mor {C : precategory} {b c : C} (f : C^op⟦c, b⟧) : C⟦b, c⟧ := f.

Definition opp_mor_eq {C : precategory} {a b : C} {f g : a --> b} (e : opp_mor f = opp_mor g) :
  f = g := e.

Lemma opp_opp_precat_ob_mor (C : precategory_ob_mor) : C = opp_precat_ob_mor (opp_precat_ob_mor C).
Proof.
  reflexivity.
Defined.

Lemma opp_opp_precat_ob_mor_compute (C : precategory_ob_mor) :
  idpath _ = maponpaths precategory_id_comp (opp_opp_precat_ob_mor C).
Proof.
  reflexivity.
Defined.

Lemma opp_opp_precat_data (C : precategory_data) : C = opp_precat_data (opp_precat_data C).
Proof.
  reflexivity.
Defined.

Lemma opp_opp_precat (C : precategory) (hs : has_homsets C) : C = C^op^op.
Proof.


  use total2_paths_f.
  - apply opp_opp_precat_data.
  - apply (isaprop_is_precategory _ hs).
Qed.

Definition opp_is_iso {C : precategory} {a b : C} (f : a --> b) :
  @is_iso C a b f -> @is_iso C^op b a f.
Proof.
  intros H.
  set (T := is_z_iso_from_is_iso _ H).
  apply (is_iso_qinv (C:=C^op) _ (pr1 T)).
  split; [ apply (pr2 (pr2 T)) | apply (pr1 (pr2 T)) ].
Qed.

Definition opp_iso {C : precategory} {a b : C} : @iso C a b -> @iso C^op b a.
  intro f.
  exists (pr1 f).
  set (T := is_z_iso_from_is_iso _ (pr2 f)).
  apply (is_iso_qinv (C:=C^op) _ (pr1 T)).
  split; [ apply (pr2 (pr2 T)) | apply (pr1 (pr2 T)) ].
Defined.

Lemma opp_is_inverse_in_precat {C : precategory} {a b : C} {f : a --> b} {g : b --> a} :
  @is_inverse_in_precat C a b f g -> @is_inverse_in_precat (opp_precat C) a b g f.
Proof.
  intros H.
  use mk_is_inverse_in_precat.
  - exact (is_inverse_in_precat1 H).
  - exact (is_inverse_in_precat2 H).
Defined.

Definition opp_is_z_isomorphism {C : precategory} {a b : C} (f : a --> b) :
  @is_z_isomorphism C a b f -> @is_z_isomorphism C^op b a f.
Proof.
  intros H.
  use mk_is_z_isomorphism.
  - exact (is_z_isomorphism_mor H).
  - exact (opp_is_inverse_in_precat (is_inverse_in_precat_inv H)).
Defined.

Definition opp_z_iso {C : precategory} {a b : C} (f : a --> b) : @z_iso C a b -> @z_iso C^op b a.
Proof.
  intros H.
  use mk_z_iso.
  - exact (z_iso_mor H).
  - exact (z_iso_inv_mor H).
  - exact (opp_is_inverse_in_precat (is_inverse_in_precat_inv H)).
Defined.

Lemma has_homsets_opp {C : precategory} (hsC : has_homsets C) : has_homsets C^op.
Proof. intros a b; apply hsC. Qed.


(** * The opposite functor *)

Definition functor_opp_data {C D : precategory} (F : functor C D) :
  functor_data C^op D^op :=
    tpair (fun F : C^op -> D^op => ∏ a b, C^op ⟦a, b⟧ -> D^op ⟦F a, F b⟧) F
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


(** Properties of the opp functor *)

Section opp_functor_properties.

Variables C D : precategory.
Variable F : functor C D.

Lemma opp_functor_fully_faithful : fully_faithful F -> fully_faithful (functor_opp F).
Proof.
  intros HF a b.
  apply HF.
Defined.

Lemma opp_functor_essentially_surjective :
  essentially_surjective F -> essentially_surjective (functor_opp F).
Proof.
  intros HF d.
  set (TH := HF d).
  set (X:=@hinhuniv  (∑ a : C, iso (F a) d)).
  refine (X _ _ TH).
  intro H. clear TH. clear X.
  apply hinhpr.
  destruct H as [a X].
  exists a. simpl in *.
  apply  opp_iso.
  apply (iso_inv_from_iso X).
Qed.

End opp_functor_properties.

Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op") : cat.

Lemma functor_opp_identity {C : precategory} (hsC : has_homsets C) :
  functor_opp (functor_identity C) = functor_identity C^op.
Proof. apply (functor_eq _ _ (has_homsets_opp hsC)); trivial. Qed.

Lemma functor_opp_composite {C D E : precategory} (F : functor C D) (G : functor D E)
  (hsE : has_homsets E) : functor_opp (functor_composite F G) =
                          functor_composite (functor_opp F) (functor_opp G).
Proof. apply (functor_eq _ _ (has_homsets_opp hsE)); trivial. Qed.

Definition from_opp_to_opp_opp (A C : precategory) (hsC : has_homsets C) :
  functor_data [A, C, hsC]^op [A^op, C^op, has_homsets_opp hsC].
Proof.
apply (tpair _ functor_opp).
simpl; intros F G α.
simple refine (tpair _ _ _).
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
simple refine (tpair _ _ _); simpl.
- intro F.
  simple refine (tpair _ _ _).
  + exists F.
    apply (λ a b f, # F f).
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
