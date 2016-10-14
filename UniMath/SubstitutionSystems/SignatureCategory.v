Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.

Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.

Section SignatureCategory.

Variables (C : precategory) (hsC : has_homsets C).

Local Notation "'U'" := (functor_ptd_forget C hsC).
Local Notation "'Ptd'" := (precategory_Ptd C hsC).

(** Define the commutative diagram used in the morphisms *)
Section Signature_category_mor.

Variables (Ht Ht' : Signature C hsC).

Let H := Signature_Functor _ _ Ht.
Let H' := Signature_Functor _ _ Ht'.
Let θ : nat_trans (θ_source Ht) (θ_target Ht) := theta Ht.
Let θ' : nat_trans (θ_source Ht') (θ_target Ht') := theta Ht'.

Variables (α : nat_trans H H').
Variables (X : [C,C,hsC]) (Y : Ptd).

Let f1 : [C,C,hsC] ⟦H X • U Y,H (X • U Y)⟧ := θ (X,,Y).
Let f2 : [C,C,hsC] ⟦H (X • U Y),H' (X • U Y)⟧ := α (X • U Y).

Let g1 : [C,C,hsC] ⟦H X • U Y,H' X • U Y⟧ := α X ∙∙ identity (U Y).
Let g2 : [C,C,hsC] ⟦H' X • U Y,H' (X • U Y)⟧ := θ' (X,,Y).

Definition Signature_category_mor_diagram : UU := f1 ;; f2 = g1 ;; g2.

End Signature_category_mor.

Definition SignatureMor : Signature C hsC → Signature C hsC → UU.
Proof.
intros Ht Ht'.
use total2.
+ apply (nat_trans Ht Ht').
+ intros α; apply (Π X Y, Signature_category_mor_diagram Ht Ht' α X Y).
Defined.

Lemma SignatureMor_eq (Ht Ht' : Signature C hsC) (f g : SignatureMor Ht Ht') :
  pr1 f = pr1 g -> f = g.
Proof.
intros H.
apply subtypeEquality; trivial.
now intros α; repeat (apply impred; intro); apply functor_category_has_homsets.
Qed.

Local Lemma SignatureMor_id_subproof (Ht : Signature C hsC) X Y :
  Signature_category_mor_diagram Ht Ht (nat_trans_id Ht) X Y.
Proof.
apply (nat_trans_eq hsC); intro c; simpl.
now rewrite functor_id, !id_left, id_right.
Qed.

Definition SignatureMor_id (Ht : Signature C hsC) : SignatureMor Ht Ht :=
  (nat_trans_id Ht,,SignatureMor_id_subproof Ht).

Definition SignatureMor_comp_subproof (Ht1 Ht2 Ht3 : Signature C hsC)
  (α : SignatureMor Ht1 Ht2) (β : SignatureMor Ht2 Ht3) X Y :
  Signature_category_mor_diagram Ht1 Ht3 (nat_trans_comp (pr1 α) (pr1 β)) X Y.
Proof.
destruct α as [α Hα]; destruct β as [β Hβ].
unfold Signature_category_mor_diagram in *; simpl.
rewrite (assoc ((theta Ht1) (X,,Y))).
eapply pathscomp0; [apply (cancel_postcomposition _ _ _ _ ((theta Ht1) (X,,Y) ;; _)), Hα|].
rewrite <- assoc; eapply pathscomp0; [apply maponpaths, Hβ|].
rewrite assoc; apply (cancel_postcomposition [C,C,hsC] _ _ _ _ (_ ∙∙ identity (U Y))).
apply (nat_trans_eq hsC); intro c; simpl.
now rewrite assoc, !functor_id, !id_right.
Qed.

Definition SignatureMor_comp (Ht1 Ht2 Ht3 : Signature C hsC)
  (α : SignatureMor Ht1 Ht2) (β : SignatureMor Ht2 Ht3) : SignatureMor Ht1 Ht3 :=   (nat_trans_comp (pr1 α) (pr1 β),,(SignatureMor_comp_subproof Ht1 Ht2 Ht3 α β)).
Definition Signature_precategory_data : precategory_data.
Proof.
apply (tpair _ (Signature C hsC,,SignatureMor)), (SignatureMor_id,,SignatureMor_comp).
Defined.

Lemma is_precategory_Signature_precategory_data :
  is_precategory Signature_precategory_data.
Proof.
repeat split; simpl.
- intros Ht Ht' F; apply SignatureMor_eq; simpl.
  apply (nat_trans_eq (functor_category_has_homsets _ _ hsC)); intros X; apply id_left.
- intros Ht Ht' F; apply SignatureMor_eq; simpl.
  apply (nat_trans_eq (functor_category_has_homsets _ _ hsC)); intros X; apply id_right.
- intros Ht1 Ht2 Ht3 Ht4 F1 F2 F3; apply SignatureMor_eq; simpl.
  apply (nat_trans_eq (functor_category_has_homsets _ _ hsC)); intros X; apply assoc.
Qed.

Definition Signature_precategory : precategory :=
 (Signature_precategory_data,,is_precategory_Signature_precategory_data).

Lemma has_homsets_Signature_precategory : has_homsets Signature_precategory.
Admitted.

End SignatureCategory.

Section BinProducts.

Variables (C : precategory) (hsC : has_homsets C) (BC : BinProducts C).

Lemma BinProducts_Signature_precategory : BinProducts (Signature_precategory C hsC).
Proof.
intros A B.
use mk_BinProductCone.
- apply (BinProduct_of_Signatures _ _ BC A B).
- simpl in *.
mkpair.
+
simpl.
(* destruct A as [A1 [A2 [A3 A4]]]; destruct B as [B1 [B2 [B3 B4]]]; simpl. *)
apply (binproduct_nat_trans_pr1 [C,C,hsC] [C,C,hsC]). (* Can we use BinProductPr1 instead? *)
+ abstract (
destruct A as [A1 [A2 [A3 A4]]]; destruct B as [B1 [B2 [B3 B4]]]; simpl;
intros X Y;
apply (nat_trans_eq hsC); intro c; simpl;
rewrite functor_id, id_right;
apply BinProductOfArrowsPr1).
- simpl in *.
mkpair.
+
(* destruct A as [A1 [A2 [A3 A4]]]; destruct B as [B1 [B2 [B3 B4]]]; simpl. *)
apply (binproduct_nat_trans_pr2 [C,C,hsC] [C,C,hsC]). (* Can we use BinProductPr2 instead? *)
+ abstract (
destruct A as [A1 [A2 [A3 A4]]]; destruct B as [B1 [B2 [B3 B4]]]; simpl;
intros X Y;
apply (nat_trans_eq hsC); intro c; simpl;
rewrite functor_id, id_right;
apply BinProductOfArrowsPr2).
-
(* destruct A as [A1 [A2 [A3 A4]]]; destruct B as [B1 [B2 [B3 B4]]]. *)
use mk_isBinProductCone.
+ apply has_homsets_Signature_precategory.
+ simpl.
  intros Ht F G.
assert (temp : BinProducts [C,C,hsC]).
  admit.
assert (temp2 : has_homsets [C,C,hsC]).
  admit.
generalize (binproduct_nat_trans_univ_prop _ _ temp temp2 (pr1 A) (pr1 B) (pr1 Ht)).
admit.
Admitted.

End BinProducts.