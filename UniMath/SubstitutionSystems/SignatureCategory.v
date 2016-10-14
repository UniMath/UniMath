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
Proof.
intros Ht1 Ht2.
change isaset with (isofhlevel 2); apply isofhleveltotal2.
* apply isaset_nat_trans, functor_category_has_homsets.
* intros α.
  apply isasetaprop.
  apply impred; intros X; apply impred; intros Y.
  apply functor_category_has_homsets.
Qed.

End SignatureCategory.

Section BinProducts.

Variables (C : precategory) (hsC : has_homsets C) (BC : BinProducts C).

Let BCC : BinProducts [[C,C,hsC],[C,C,hsC],functor_category_has_homsets _ _ hsC].
Proof.
apply BinProducts_functor_precat.
apply (BinProducts_functor_precat C _ BC hsC).
Defined.

Lemma BinProducts_Signature_precategory : BinProducts (Signature_precategory C hsC).
Proof.
intros Ht1 Ht2.
use mk_BinProductCone.
- apply (BinProduct_of_Signatures _ _ BC Ht1 Ht2).
- simpl in *.
mkpair.
+
apply (BinProductPr1 _ (BCC (pr1 Ht1) (pr1 Ht2))).
+
abstract (intros X Y; apply (nat_trans_eq hsC); intro c; simpl;
eapply pathscomp0; [apply BinProductOfArrowsPr1|];
eapply pathscomp0; [|apply assoc]; apply maponpaths;
apply pathsinv0; eapply pathscomp0; [apply cancel_postcomposition, functor_id|];
apply id_left).
- simpl in *.
mkpair.
+
apply (BinProductPr2 _ (BCC (pr1 Ht1) (pr1 Ht2))).
+
abstract (
intros X Y;
apply (nat_trans_eq hsC); intro c; simpl;
rewrite functor_id, id_right;
apply BinProductOfArrowsPr2).
-
use mk_isBinProductCone.
+ apply has_homsets_Signature_precategory.
+ simpl.
  intros Ht3 F G.
set (H := @BinProductArrow _ _ _ (BCC (pr1 Ht1) (pr1 Ht2)) (pr1 Ht3) (pr1 F) (pr1 G)).
use unique_exists; simpl.
* apply (tpair _ H).
intros X Y.
generalize (pr2 G X Y).
generalize (pr2 F X Y).
unfold Signature_category_mor_diagram.
unfold H.
intros HH1 HH2.
apply (nat_trans_eq hsC); intro c.
simpl.
rewrite <- assoc.
apply pathsinv0.
eapply pathscomp0.
eapply maponpaths.
apply BinProductOfArrows_comp.
rewrite !functor_id.
rewrite !id_left.
eapply pathscomp0.
apply postcompWithBinProductArrow.
apply pathsinv0.
apply BinProductArrowUnique.
eapply pathscomp0.
rewrite <- assoc.
apply maponpaths.
apply BinProductPr1Commutes.
eapply pathscomp0.
apply (nat_trans_eq_pointwise HH1 c).
simpl.
rewrite functor_id.
rewrite id_right.
apply idpath.
eapply pathscomp0.
rewrite <- assoc.
apply maponpaths.
apply BinProductPr2Commutes.
eapply pathscomp0.
apply (nat_trans_eq_pointwise HH2 c).
simpl.
rewrite functor_id.
rewrite id_right.
apply idpath.
* split.
{ apply SignatureMor_eq, (BinProductPr1Commutes _ _ _ (BCC  _ _)). }
{ apply SignatureMor_eq, (BinProductPr2Commutes _ _ _ (BCC  _ _)). }
* intros X; simpl in *.
apply isapropdirprod.
apply has_homsets_Signature_precategory.
apply has_homsets_Signature_precategory.
* intros X.
intros H1H2.
apply SignatureMor_eq; simpl.
apply (BinProductArrowUnique _ _ _ (BCC  _ _)).
apply (maponpaths pr1 (pr1 H1H2)).
apply (maponpaths pr1 (pr2 H1H2)).
Admitted.

End BinProducts.