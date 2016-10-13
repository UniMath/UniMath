Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.

Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.Signatures.

Section SignatureCategory.

Variables (C : precategory) (hsC : has_homsets C).

(** The forgetful functor from pointed endofunctors to endofunctors *)
Local Notation "'U'" := (functor_ptd_forget C hsC).
(** The precategory of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (precategory_Ptd C hsC).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hsC]) .


(* Define the commutative diagram used in the morphisms *)
Section Signature_category_mor.

Variables (Ht Ht' : Signature C hsC).

Let H := Signature_Functor _ _ Ht.
Let H' := Signature_Functor _ _ Ht'.
Let θ : nat_trans (θ_source C hsC Ht) (θ_target C hsC Ht) := theta Ht.
Let θ' : nat_trans (θ_source C hsC Ht') (θ_target C hsC Ht') := theta Ht'.

Variables (α : nat_trans H H').
Variables (X : [C,C,hsC]) (Y : Ptd).

Let f1 : [C,C,hsC] ⟦H X • U Y,H (X • U Y)⟧ := θ (X,,Y).
Let f2 : [C,C,hsC] ⟦H (X • U Y),H' (X • U Y)⟧ := α (X • U Y).

Let g1 : [C,C,hsC] ⟦H X • U Y,H' X • U Y⟧ := α X ∙∙ identity (U Y).
Let g2 : [C,C,hsC] ⟦H' X • U Y,H' (X • U Y)⟧ := θ' (X,,Y).

Definition Signature_category_mor_diagram : UU := f1 ;; f2 = g1 ;; g2.

End Signature_category_mor.


Definition Signature_precategory_data : precategory_data.
Proof.
mkpair.
+ mkpair.
  - apply (Signature C hsC).
  - intros Ht Ht'.
    use total2.
    * apply (nat_trans Ht Ht').
    * intros α; apply (Π X Y, Signature_category_mor_diagram Ht Ht' α X Y).
+ split.
  - simpl; intro Ht.
    mkpair.
    * apply (nat_trans_id Ht).
    * intros X Y.
      apply (nat_trans_eq hsC); intro c; simpl.
      now rewrite functor_id, !id_left, id_right.
  - simpl; intros Ht1 Ht2 Ht3 [α Hα] [β Hβ].
    mkpair.
    * apply (@nat_trans_comp _ _ _ _ (pr1 Ht3) α β).
    * intros X Y.
      unfold Signature_category_mor_diagram in *; simpl.
rewrite (assoc ((theta Ht1) (X,, Y))).
eapply pathscomp0.
eapply (cancel_postcomposition [C,C,hsC] _ _ _ ((theta Ht1) (X,, Y) ;; α (functor_composite (pr1 Y) X)) _ (β (functor_composite (pr1 Y) X))).
apply Hα.
eapply pathscomp0.
rewrite <-assoc.
eapply maponpaths.
apply Hβ.
rewrite assoc.
apply (cancel_postcomposition [C,C,hsC] _ _ _ _ ((α X ;; β X) ∙∙ identity (U Y)) ((theta Ht3) (X,, Y)) ).
apply (nat_trans_eq hsC); intro c.
simpl.
now rewrite assoc, !functor_id, !id_right.
Defined.

Lemma is_precategory_Signature_precategory_data :
  is_precategory Signature_precategory_data.
Proof.
split; try split; simpl.
- intros Ht Ht' [F HF].
  apply subtypeEquality.
  + intros xx; repeat (apply impred; intro); apply functor_category_has_homsets.
  + apply (nat_trans_eq (functor_category_has_homsets _ _ hsC)); intros X.
    apply (@id_left [C,C,hsC]).
- intros Ht Ht' [F HF].
  apply subtypeEquality.
  + intros xx; repeat (apply impred; intro); apply functor_category_has_homsets.
  + apply (nat_trans_eq (functor_category_has_homsets _ _ hsC)); intros X.
    apply (@id_right [C,C,hsC]).
- intros Ht1 Ht2 Ht3 Ht4 [F1 HF1] [F2 HF2] [F3 HF3].
  apply subtypeEquality.
  + intros xx; repeat (apply impred; intro); apply functor_category_has_homsets.
  + apply (nat_trans_eq (functor_category_has_homsets _ _ hsC)); intros X.
    apply (@assoc [C,C,hsC]).
Qed.

Definition Signature_precategory : precategory.
Proof.
mkpair.
- apply Signature_precategory_data.
- apply is_precategory_Signature_precategory_data.
Defined.


End SignatureCategory.