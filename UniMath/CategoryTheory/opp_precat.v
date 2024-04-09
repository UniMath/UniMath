
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Definition of opposite category and functor

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.FunctorCategory.

Local Open Scope cat.

(** * The opposite precategory of a precategory *)

Definition opp_precat_ob_mor (C : precategory_ob_mor) : precategory_ob_mor :=
   tpair (λ ob : UU, ob -> ob -> UU) C (λ a b : C, C⟦b, a⟧ ).

Definition opp_precat_data (C : precategory_data) : precategory_data :=
  tpair _ _ (tpair _ (λ c : opp_precat_ob_mor C, identity c)
                     (λ (a b c : opp_precat_ob_mor C) f g, g · f)).

Definition is_precat_opp_precat_data (C : precategory) : is_precategory (opp_precat_data C)
  := ((λ a b, pr212 C b a),,(λ a b, pr112 C b a)),,
     ((λ a b c d f g h, pr222 C d c b a h g f),,(λ a b c d f g h, pr122 C d c b a h g f)).

Definition opp_precat (C : precategory) : precategory :=
  tpair _ (opp_precat_data C) (is_precat_opp_precat_data C).

Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op") : cat.

Goal ∏ C:precategory, C^op^op = C. reflexivity. Qed.

Definition opp_ob {C : precategory} (c : ob C) : ob C^op := c.

Definition rm_opp_ob {C : precategory} (cop : ob C^op) : ob C := cop.

Definition opp_mor {C : precategory} {b c : C} (f : C⟦b, c⟧) : C^op⟦c, b⟧ := f.

Definition rm_opp_mor {C : precategory} {b c : C} (f : C^op⟦c, b⟧) : C⟦b, c⟧ := f.

Definition oppositeCategory : category -> category
  := λ M, @tpair precategory has_homsets (opp_precat M) (λ A B, homset_property M (rm_opp_ob B) (rm_opp_ob A)).

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

Definition iso_from_opp {C : precategory} {a b : C} (f : a --> b) :
  @is_iso C^op b a f → @is_iso C a b f.
Proof.
  intros H.
  set (T := is_z_iso_from_is_iso _ H).
  apply (is_iso_qinv (C:=C) _ (pr1 T)).
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
  use make_is_inverse_in_precat.
  - exact (is_inverse_in_precat1 H).
  - exact (is_inverse_in_precat2 H).
Defined.

Definition opp_is_z_isomorphism {C : precategory} {a b : C} (f : a --> b) :
  @is_z_isomorphism C a b f -> @is_z_isomorphism C^op b a f.
Proof.
  intros H.
  use make_is_z_isomorphism.
  - exact (is_z_isomorphism_mor H).
  - exact (opp_is_inverse_in_precat (is_inverse_in_precat_inv H)).
Defined.

Definition opp_z_iso {C : precategory} {a b : C} : @z_iso C a b -> @z_iso C^op b a.
Proof.
  intros H.
  use make_z_iso.
  - exact (z_iso_mor H).
  - exact (inv_from_z_iso H).
  - exact (opp_is_inverse_in_precat (is_inverse_in_precat_inv H)).
Defined.

Definition z_iso_from_opp {C : precategory} {a b : C} (f : a --> b) :
  @is_z_isomorphism C^op b a f → @is_z_isomorphism C a b f.
Proof.
  intros H.
  exists (pr1 H).
  split; [ apply (pr2 (pr2 H)) | apply (pr1 (pr2 H)) ].
Qed.

Lemma has_homsets_opp {C : precategory} (hsC : has_homsets C) : has_homsets C^op.
Proof. intros a b; apply hsC. Defined.

Definition op_cat (c : category) : category := (opp_precat c,, has_homsets_opp (homset_property c) ).

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
  set (X:=@hinhuniv  (∑ a : C, z_iso (F a) d)).
  use (X _ _ TH).
  intro H. clear TH. clear X.
  apply hinhpr.
  destruct H as [a X].
  exists a. simpl in *.
  apply  opp_z_iso.
  apply (z_iso_inv_from_z_iso X).
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
use tpair.
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
use tpair; simpl.
- intro F.
  use tpair.
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


Definition op_nt {c d : category} {f g : functor c d} (a : nat_trans f g)
  : nat_trans (functor_opp g) (functor_opp f).
Proof.
  use tpair.
  - exact (λ c, a c).
  - abstract
      (intros x y h;
       apply (! (nat_trans_ax a _ _ _ ))).
Defined.

Lemma op_nt_is_z_iso {C D : category} {f g : functor C D} (a : nat_trans f g) (is : is_nat_z_iso a)
  : is_nat_z_iso (op_nt a).
Proof.
  intro c.
  use opp_is_z_isomorphism.
  exact (is c).
Defined.

Lemma op_nt_is_iso {C D : category} {f g : functor C D} (a : nat_trans f g) (is : is_nat_iso a) : is_nat_iso (op_nt a).
Proof.
  intro c.
  use opp_is_iso.
  exact (is c).
Defined.


(** It's univalent *)

Definition op_iso_is_cat_iso
           {C : category}
           (X Y : C^op)
  : @iso C Y X ≃ iso X Y.
Proof.
  use weqfibtototal.
  intro f.
  use weqimplimpl.
  - apply opp_is_iso.
  - apply iso_from_opp.
  - apply isaprop_is_iso.
  - apply isaprop_is_iso.
Defined.

Definition has_homsets_op (C : category) : has_homsets (C^op).
Proof.
  intros a b.
  apply C.
Defined.

Definition op_category (C : category) : category := make_category C^op (has_homsets_op C).

Definition op_z_iso_is_cat_z_iso
           {C : category}
           (X Y : C^op)
  : @z_iso C Y X ≃ z_iso X Y.
Proof.
  use weqfibtototal.
  intro f.
  use weqimplimpl.
  - apply opp_is_z_isomorphism.
  - apply z_iso_from_opp.
  - apply isaprop_is_z_isomorphism.
  - apply (isaprop_is_z_isomorphism(C:=op_category C)).
Defined.

Definition from_op_op_to_op (A C : category)
  : functor [op_category A, op_category C] (op_category [A,C])
  := tpair _ _ (is_functor_from_opp_opp_to_opp A C C).

Definition op_is_univalent (C : univalent_category)
  : is_univalent (op_category C).
Proof.
  intros X Y.
  use weqhomot.
  + exact ((op_z_iso_is_cat_z_iso X Y)
             ∘ make_weq (@idtoiso C Y X) (pr2( C) Y X)
             ∘ weqpathsinv0 _ _)%weq.
  + intros p.
    induction p ; cbn.
    apply subtypePath.
    * intro ; apply (isaprop_is_z_isomorphism(C:=op_category C)).
    * apply idpath.
Defined.

Definition op_unicat (C : univalent_category)
  : univalent_category
  := (op_category C ,, op_is_univalent C).

Notation "C '^op'" := (op_category C) (at level 3, format "C ^op") : cat.


Definition op_ob {C : category} (c : ob C) : ob C^op := c.

Definition rm_op_ob {C : category} (cop : ob C^op) : ob C := cop.

Definition op_mor {C : category} {b c : C} (f : C⟦b, c⟧) : C^op⟦c, b⟧ := f.

Definition rm_op_mor {C : category} {b c : C} (f : C^op⟦c, b⟧) : C⟦b, c⟧ := f.

(** Functoriality of taking the opposite *)
Definition functor_identity_op
           (C : category)
  : functor_identity (C^op)
    ⟹
    functor_opp (functor_identity C).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition is_nat_z_iso_functor_identity_op
           (C : category)
  : is_nat_z_iso (functor_identity_op C).
Proof.
  intros x.
  apply is_z_isomorphism_identity.
Defined.

Definition functor_identity_op_nat_z_iso
           (C : category)
  : nat_z_iso
      (functor_identity (C^op))
      (functor_opp (functor_identity C)).
Proof.
  use make_nat_z_iso.
  - exact (functor_identity_op C).
  - exact (is_nat_z_iso_functor_identity_op C).
Defined.

Definition functor_comp_op
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₂ ⟶ C₃)
  : functor_opp F ∙ functor_opp G ⟹ functor_opp (F ∙ G).
Proof.
  use make_nat_trans.
  - exact (λ x, identity _).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition is_nat_z_iso_functor_comp_op
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₂ ⟶ C₃)
  : is_nat_z_iso (functor_comp_op F G).
Proof.
  intros x.
  apply is_z_isomorphism_identity.
Defined.

Definition functor_comp_op_nat_z_iso
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₂ ⟶ C₃)
  : nat_z_iso
      (functor_opp F ∙ functor_opp G)
      (functor_opp (F ∙ G)).
Proof.
  use make_nat_z_iso.
  - exact (functor_comp_op F G).
  - exact (is_nat_z_iso_functor_comp_op F G).
Defined.

(** It forms a duality involution *)
Definition op_unit_nat_trans
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : functor_identity _ ∙ functor_opp (functor_opp F)
    ⟹
    F ∙ functor_identity _.
Proof.
  use make_nat_trans.
  - exact (λ x, identity (F x)).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_nat_z_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : nat_z_iso
      (functor_identity _ ∙ functor_opp (functor_opp F))
      (F ∙ functor_identity _).
Proof.
  use make_nat_z_iso.
  - exact (op_unit_nat_trans F).
  - intro.
    apply identity_is_z_iso.
Defined.

Definition op_unit_inv_nat_trans
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : functor_identity _ ∙ F
    ⟹
    functor_opp (functor_opp F) ∙ functor_identity _.
Proof.
  use make_nat_trans.
  - exact (λ x, identity (F x)).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_inv_nat_z_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : nat_z_iso
      (functor_identity _ ∙ F)
      (functor_opp (functor_opp F) ∙ functor_identity _).
Proof.
  use make_nat_z_iso.
  - exact (op_unit_inv_nat_trans F).
  - intro.
    apply identity_is_z_iso.
Defined.

Definition op_triangle_nat_trans
           (C : category)
  : functor_identity _ ⟹ functor_opp (functor_identity C).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_triangle_nat_z_iso
           (C : category)
  : nat_z_iso
      (functor_identity _)
      (functor_opp (functor_identity C)).
Proof.
  use make_nat_z_iso.
  - exact (op_triangle_nat_trans C).
  - intro.
    apply identity_is_z_iso.
Defined.

Definition op_unit_unit_inv_nat_trans
           (C : category)
  : nat_trans
      (functor_identity C)
      (functor_identity C ∙ functor_identity ((C^op)^op)).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_unit_inv_nat_z_iso
           (C : category)
  : nat_z_iso
      (functor_identity C)
      (functor_identity C ∙ functor_identity ((C^op)^op)).
Proof.
  use make_nat_z_iso.
  - exact (op_unit_unit_inv_nat_trans C).
  - intro.
    apply identity_is_z_iso.
Defined.

Definition op_unit_inv_unit_nat_trans
           (C : category)
  : nat_trans
      (functor_identity ((C^op)^op) ∙ functor_identity C)
      (functor_identity ((C^op)^op)).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_inv_unit_nat_z_iso
           (C : category)
  : nat_z_iso
      (functor_identity ((C^op)^op) ∙ functor_identity C)
      (functor_identity ((C^op)^op)).
Proof.
  use make_nat_z_iso.
  - exact (op_unit_inv_unit_nat_trans C).
  - intro.
    apply identity_is_z_iso.
Defined.

(**
 idtoiso in the opposite
 *)
Proposition idtoiso_opp
            {C : category}
            {x y : C}
            (p : x = y)
  : pr1 (@idtoiso (C^op) _ _ p) = pr1 (@idtoiso C _ _ (!p)).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

(** The opposite of a setcategory *)
Definition is_setcategory_opp
           {C : category}
           (HC : is_setcategory C)
  : is_setcategory (C^op).
Proof.
  split.
  - apply HC.
  - apply homset_property.
Qed.

Definition opp_setcategory
           (C : setcategory)
  : setcategory.
Proof.
  use make_setcategory.
  - exact (C^op).
  - apply C.
Defined.
