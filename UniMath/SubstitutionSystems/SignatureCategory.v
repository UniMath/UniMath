(**

Definition of the category of signatures with strength ([Signature_precategory]) with

- Binary products ([BinProducts_Signature_precategory])
- Coproducts ([Coproducts_Signature_precategory])

Written by: Anders Mörtberg in October 2016 based on a note of Benedikt Ahrens.

*)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.
Require Import UniMath.SubstitutionSystems.Signatures.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.

Local Open Scope cat.

Local Notation "[ C , D ]" := (functor_category C D).

(** * The category of signatures with strength *)
Section SignatureCategory.

Variables (C D D': category).

Let hsC : has_homsets C := homset_property C.
Let hsD : has_homsets D := homset_property D.
Let hsD' : has_homsets D' := homset_property D'.

Local Notation "'U'" := (functor_ptd_forget C hsC).
Local Notation "'Ptd'" := (precategory_Ptd C hsC).

(** Define the commutative diagram used in the morphisms *)
Section Signature_category_mor.

Variables (Ht Ht' : Signature C hsC D hsD D' hsD').

Let H := Signature_Functor Ht.
Let H' := Signature_Functor Ht'.
Let θ : nat_trans (θ_source Ht) (θ_target Ht) := theta Ht.
Let θ' : nat_trans (θ_source Ht') (θ_target Ht') := theta Ht'.

Variables (α : nat_trans H H').
Variables (X : [C,D']) (Y : Ptd).

Let f1 : [C,D] ⟦H X • U Y,H (X • U Y)⟧ := θ (X,,Y).
Let f2 : [C,D] ⟦H (X • U Y),H' (X • U Y)⟧ := α (X • U Y).

Let g1 : [C,D] ⟦H X • U Y,H' X • U Y⟧ := α X ∙∙ identity (U Y).
Let g2 : [C,D] ⟦H' X • U Y,H' (X • U Y)⟧ := θ' (X,,Y).

Definition Signature_category_mor_diagram : UU := f1 · f2 = g1 · g2.

(** Special comparison lemma that speeds things up a lot *)
Lemma Signature_category_mor_diagram_pointwise
  (Hc : ∏ c, pr1 f1 c · pr1 f2 c = pr1 (α X) ((pr1 Y) c) · pr1 g2 c) :
   Signature_category_mor_diagram.
Proof.
apply (nat_trans_eq hsD); intro c; simpl.
rewrite functor_id, id_right; apply (Hc c).
Qed.

End Signature_category_mor.

Definition SignatureMor : Signature C hsC D hsD D' hsD' → Signature C hsC D hsD D' hsD' → UU.
Proof.
intros Ht Ht'.
use total2.
+ apply (nat_trans Ht Ht').
+ intros α; apply (∏ X Y, Signature_category_mor_diagram Ht Ht' α X Y).
Defined.

Lemma SignatureMor_eq (Ht Ht' : Signature C hsC D hsD D' hsD') (f g : SignatureMor Ht Ht') :
  pr1 f = pr1 g -> f = g.
Proof.
intros H.
apply subtypePath; trivial.
now intros α; repeat (apply impred; intro); apply functor_category_has_homsets.
Qed.

Local Lemma SignatureMor_id_subproof (Ht : Signature C hsC D hsD D' hsD') X Y :
  Signature_category_mor_diagram Ht Ht (nat_trans_id Ht) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c; simpl.
now rewrite id_left, id_right.
Qed.

Definition SignatureMor_id (Ht : Signature C hsC D hsD D' hsD') : SignatureMor Ht Ht :=
  (nat_trans_id Ht,,SignatureMor_id_subproof Ht).

Definition SignatureMor_comp_subproof (Ht1 Ht2 Ht3 : Signature C hsC D hsD D' hsD')
  (α : SignatureMor Ht1 Ht2) (β : SignatureMor Ht2 Ht3) X Y :
  Signature_category_mor_diagram Ht1 Ht3 (nat_trans_comp (pr1 α) (pr1 β)) X Y.
Proof.
destruct α as [α Hα]; destruct β as [β Hβ].
unfold Signature_category_mor_diagram in *; simpl.
rewrite (assoc ((theta Ht1) (X,,Y))).
etrans; [apply (cancel_postcomposition ((theta Ht1) (X,,Y) · _)), Hα|].
rewrite <- assoc; etrans; [apply maponpaths, Hβ|].
rewrite assoc; apply (cancel_postcomposition (C:=[C,D]) _  (_ ∙∙ identity (U Y))).
apply (nat_trans_eq hsD); intro c; simpl.
now rewrite assoc, !functor_id, !id_right.
Qed.

Definition SignatureMor_comp (Ht1 Ht2 Ht3 : Signature C hsC D hsD D' hsD')
  (α : SignatureMor Ht1 Ht2) (β : SignatureMor Ht2 Ht3) : SignatureMor Ht1 Ht3 :=
    (nat_trans_comp (pr1 α) (pr1 β),,SignatureMor_comp_subproof Ht1 Ht2 Ht3 α β).

Definition Signature_precategory_data : precategory_data.
Proof.
apply (tpair _ (Signature C hsC D hsD D' hsD',,SignatureMor)), (SignatureMor_id,,SignatureMor_comp).
Defined.

Lemma is_precategory_Signature_precategory_data :
  is_precategory Signature_precategory_data.
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat split; simpl.
- intros Ht Ht' F; apply SignatureMor_eq; simpl.
  apply (nat_trans_eq (functor_category_has_homsets _ _ hsD)); intros X; apply id_left.
- intros Ht Ht' F; apply SignatureMor_eq; simpl.
  apply (nat_trans_eq (functor_category_has_homsets _ _ hsD)); intros X; apply id_right.
- intros Ht1 Ht2 Ht3 Ht4 F1 F2 F3; apply SignatureMor_eq; simpl.
  apply (nat_trans_eq (functor_category_has_homsets _ _ hsD)); intros X; apply assoc.
Qed.

Definition Signature_precategory : precategory :=
 (Signature_precategory_data,,is_precategory_Signature_precategory_data).

Lemma has_homsets_Signature_precategory : has_homsets Signature_precategory.
Proof.
intros Ht1 Ht2.
apply (isofhleveltotal2 2).
* apply isaset_nat_trans, functor_category_has_homsets.
* intros α.
  apply isasetaprop.
  apply impred; intros X; apply impred; intros Y.
  apply functor_category_has_homsets.
Qed.

Definition Signature_category : category :=
 (Signature_precategory,,has_homsets_Signature_precategory).

Definition SignatureForgetfulFunctor : functor Signature_precategory [[C,D'],[C,D]].
Proof.
use tpair.
- use tpair.
  + intros F; apply(Signature_Functor F).
  + intros F G α; apply α.
- abstract (now split).
Defined.

Lemma SignatureForgetfulFunctorFaithful : faithful SignatureForgetfulFunctor.
Proof.
intros F G.
apply isinclbetweensets.
+ apply has_homsets_Signature_precategory.
+ apply functor_category_has_homsets.
+ apply SignatureMor_eq.
Qed.

Section AsDisplayedCategory.

  Definition Signature_precategory_displayed : disp_cat [[C,D'],[C,D]].
  Proof.
    use disp_cat_from_SIP_data.
    - intro H.
      exact (StrengthForSignature C hsC D hsD D' hsD' H).
    - intros H1 H2 str1 str2 α.
      exact (∏ X Y, Signature_category_mor_diagram (H1,,str1) (H2,,str2) α X Y).
    - intros H1 H2 str1 str2 α.
      do 2 (apply impred; intro).
      apply functor_category_has_homsets.
    - intros H a X Z.
      apply SignatureMor_id_subproof.
    - intros H1 H2 H3 str1 str2 str3 a1 a2 a1mor a2mor. simpl in a1mor, a2mor.
      simpl.
      exact (SignatureMor_comp_subproof (H1,,str1) (H2,,str2) (H3,,str3) (a1,,a1mor) (a2,,a2mor)).
  Defined.

  Definition Signature_precategory' : precategory := total_category Signature_precategory_displayed.

  Lemma Signature_precategory_Pisset (H : [[C, D'], [C, D]]) : isaset (StrengthForSignature C hsC D hsD D' hsD' H).
  Proof.
    change isaset with (isofhlevel 2).
    apply isofhleveltotal2.
    apply (functor_category_has_homsets ([C, D', hsD'] ⊠ precategory_Ptd C hsC) ([C, D]) (functor_category_has_homsets _ _ hsD)).
    intro θ.
    apply isasetaprop.
    apply isapropdirprod.
    + apply isaprop_θ_Strength1_int.
    + apply isaprop_θ_Strength2_int.
  Qed.

  Lemma Signature_precategory_Hstandard (H : [[C, D'], [C, D]]) (a a' : StrengthForSignature C hsC D hsD D' hsD' H) :
 (∏ (X : [C, D']) (Y : precategory_Ptd C hsC),
  Signature_category_mor_diagram (H,, a) (H,, a') (identity H) X Y)
 → (∏ (X : [C, D']) (Y : precategory_Ptd C hsC),
    Signature_category_mor_diagram (H,, a') (H,, a) (identity H) X Y)
 → a = a'.
  Proof.
    intros leq geq.
    apply StrengthForSignature_eq.
    apply (nat_trans_eq (functor_category_has_homsets _ _ hsD)).
    intro XZ.
    assert (leqinst := leq (pr1 XZ) (pr2 XZ)).
    (* assert (geqinst := geq (pr1 XZ) (pr2 XZ)). *)
    clear leq geq.
    red in leqinst.
    unfold theta in leqinst.
    etrans.
    { apply pathsinv0.
      apply id_right. }
    etrans.
    { exact leqinst. }
    clear leqinst.
    etrans.
    2: { apply id_left. }
    apply cancel_postcomposition.
    apply nat_trans_eq; try exact hsD.
    intro c.
    cbn.
    rewrite id_left.
    apply functor_id.
  Qed.

  Definition is_univalent_Signature_precategory_displayed : is_univalent_disp Signature_precategory_displayed.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - exact Signature_precategory_Pisset.
    - exact Signature_precategory_Hstandard.
  Defined.

End AsDisplayedCategory.

End SignatureCategory.

Definition is_univalent_Signature_precategory' (C : category) (D: univalent_category) (D' : category) :
  is_univalent (Signature_precategory' C D D').
Proof.
  apply SIP.
  - exact (is_univalent_functor_category [C, D'] _ (is_univalent_functor_category C D (pr2 D))).
  - apply Signature_precategory_Pisset.
  - apply Signature_precategory_Hstandard.
Defined.



(** * Binary products in the category of signatures *)
Section BinProducts.

Variables (C : category) (BC : BinProducts C) (D : category) (BD : BinProducts D) (D' : category).

Let hsC : has_homsets C := homset_property C.
Let hsD : has_homsets D := homset_property D.
Let hsD' : has_homsets D' := homset_property D'.

Local Definition BCD : BinProducts [[C,D'],[C,D]].
Proof.
apply BinProducts_functor_precat, (BinProducts_functor_precat C _ BD).
Defined.

Local Lemma Signature_precategory_pr1_diagram (Ht1 Ht2 : Signature C hsC D hsD D' hsD') X Y :
  Signature_category_mor_diagram _ _ _ (BinProduct_of_Signatures _ _ _ _ _ _ _ Ht1 Ht2) _
    (BinProductPr1 _ (BCD _ _)) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c; apply BinProductOfArrowsPr1.
Qed.

Local Definition Signature_precategory_pr1 (Ht1 Ht2 : Signature C hsC D hsD D' hsD') :
  SignatureMor C D D' (BinProduct_of_Signatures C hsC D hsD D' hsD' BD Ht1 Ht2) Ht1.
Proof.
use tpair.
+ apply (BinProductPr1 _ (BCD (pr1 Ht1) (pr1 Ht2))).
+ cbn. apply Signature_precategory_pr1_diagram.
Defined.

Local Lemma Signature_precategory_pr2_diagram (Ht1 Ht2 : Signature C hsC D hsD D' hsD') X Y :
  Signature_category_mor_diagram _ _ _ (BinProduct_of_Signatures _ _ _ _ _ _ _ Ht1 Ht2) _
    (BinProductPr2 _ (BCD _ _)) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c; apply BinProductOfArrowsPr2.
Qed.

Local Definition Signature_precategory_pr2 (Ht1 Ht2 : Signature C hsC D hsD D' hsD') :
  SignatureMor C D D' (BinProduct_of_Signatures C hsC D hsD D' hsD' BD Ht1 Ht2) Ht2.
Proof.
use tpair.
+ apply (BinProductPr2 _ (BCD (pr1 Ht1) (pr1 Ht2))).
+ cbn. apply Signature_precategory_pr2_diagram.
Defined.

Local Lemma BinProductArrow_diagram Ht1 Ht2 Ht3
  (F : SignatureMor C D D' Ht3 Ht1) (G : SignatureMor C D D' Ht3 Ht2) X Y :
  Signature_category_mor_diagram _ _ _ _ (BinProduct_of_Signatures _ _ _ _ _ _ _ Ht1 Ht2)
    (BinProductArrow _ (BCD _ _) (pr1 F) (pr1 G)) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c.
apply pathsinv0.
etrans; [apply postcompWithBinProductArrow|].
apply pathsinv0, BinProductArrowUnique; rewrite <- assoc.
+ etrans; [apply maponpaths, BinProductPr1Commutes|].
  etrans; [apply (nat_trans_eq_pointwise (pr2 F X Y) c)|].
  now etrans; [apply cancel_postcomposition, horcomp_id_left|].
+ etrans; [apply maponpaths, BinProductPr2Commutes|].
  etrans; [apply (nat_trans_eq_pointwise (pr2 G X Y) c)|].
  now etrans; [apply cancel_postcomposition, horcomp_id_left|].
Qed.

Local Lemma isBinProduct_Signature_precategory (Ht1 Ht2 : Signature C hsC D hsD D' hsD') :
  isBinProduct (Signature_precategory C D D') Ht1 Ht2
                   (BinProduct_of_Signatures C hsC D hsD D' hsD' BD Ht1 Ht2)
                   (Signature_precategory_pr1 Ht1 Ht2) (Signature_precategory_pr2 Ht1 Ht2).
Proof.
apply (make_isBinProduct _ (has_homsets_Signature_precategory C D D')).
simpl; intros Ht3 F G.
use unique_exists; simpl.
- apply (tpair _ (BinProductArrow _ (BCD (pr1 Ht1) (pr1 Ht2)) (pr1 F) (pr1 G))).
  apply BinProductArrow_diagram.
- abstract (split;
    [ apply SignatureMor_eq, (BinProductPr1Commutes _ _ _ (BCD  _ _))
    | apply SignatureMor_eq, (BinProductPr2Commutes _ _ _ (BCD  _ _))]).
- abstract (intros X; apply isapropdirprod; apply has_homsets_Signature_precategory).
- abstract (intros X H1H2; apply SignatureMor_eq; simpl;
    apply (BinProductArrowUnique _ _ _ (BCD  _ _));
      [ apply (maponpaths pr1 (pr1 H1H2)) | apply (maponpaths pr1 (pr2 H1H2)) ]).
Defined.

Lemma BinProducts_Signature_precategory : BinProducts (Signature_precategory C D D').
Proof.
intros Ht1 Ht2.
use make_BinProduct.
- apply (BinProduct_of_Signatures _ _ _ _ _ _ BD Ht1 Ht2).
- apply Signature_precategory_pr1.
- apply Signature_precategory_pr2.
- apply isBinProduct_Signature_precategory.
Defined.

End BinProducts.

(** * Coproducts in the category of signatures *)
Section Coproducts.

Variables (I : UU).
Variables (C D D' : category) (CD : Coproducts I D).

Let hsC : has_homsets C := homset_property C.
Let hsD : has_homsets D := homset_property D.
Let hsD' : has_homsets D' := homset_property D'.

Local Definition CCD : Coproducts I [[C,D'],[C,D]].
Proof.
now repeat apply Coproducts_functor_precat.
Defined.

Local Lemma Signature_precategory_in_diagram (Ht : I → Signature_precategory C D D') i X Y :
  Signature_category_mor_diagram _ _ _ _ (Sum_of_Signatures I C _ _ _ _ _ CD Ht)
    (CoproductIn _ _ (CCD (λ j : I, pr1 (Ht j))) i) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c.
apply pathsinv0.
set (C1 := CD (λ j, pr1 (pr1 (Ht j) X) ((pr1 Y) c))).
set (C2 := CD (λ j, pr1 (pr1 (Ht j) (functor_composite (pr1 Y) X)) c)).
apply (@CoproductOfArrowsIn I D _ C1 _ C2).
Defined.

Local Definition Signature_precategory_in (Ht : I → Signature_precategory C D D') (i : I) :
  SignatureMor C D D' (Ht i) (Sum_of_Signatures I C _ D _ D' _ CD Ht).
Proof.
use tpair.
+ apply (CoproductIn _ _ (CCD (λ j, pr1 (Ht j))) i).
+ cbn. apply Signature_precategory_in_diagram.
Defined.

Lemma CoproductArrow_diagram (Hti : I → Signature_precategory C D D')
  (Ht : Signature C hsC D hsD D' hsD') (F : ∏ i : I, SignatureMor C D D' (Hti i) Ht) X Y :
  Signature_category_mor_diagram C D D' (Sum_of_Signatures I C hsC D hsD D' hsD' CD Hti) Ht
    (CoproductArrow I _ (CCD _) (λ i, pr1 (F i))) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c.
etrans; [apply precompWithCoproductArrow|].
apply pathsinv0, CoproductArrowUnique; intro i; rewrite assoc; simpl.
etrans;
  [apply cancel_postcomposition, (CoproductInCommutes _ _ _ (CD (λ j, pr1 (pr1 (Hti j) X) _)))|].
apply pathsinv0; etrans; [apply (nat_trans_eq_pointwise (pr2 (F i) X Y) c)|].
now etrans; [apply cancel_postcomposition, horcomp_id_left|].
Qed.

Local Lemma isCoproduct_Signature_precategory (Hti : I → Signature_precategory C D D') :
  isCoproduct I (Signature_precategory C D D') _
    (Sum_of_Signatures I C hsC D hsD D' hsD' CD Hti) (Signature_precategory_in Hti).
Proof.
apply (make_isCoproduct _ _ (has_homsets_Signature_precategory C D D')); simpl.
intros Ht F.
use unique_exists; simpl.
+ use tpair.
  - apply (CoproductArrow I _ (CCD (λ j, pr1 (Hti j))) (λ i, pr1 (F i))).
  - cbn. apply CoproductArrow_diagram.
+ abstract (intro i; apply SignatureMor_eq, (CoproductInCommutes _ _ _ (CCD (λ j, pr1 (Hti j))))).
+ abstract (intros X; apply impred; intro i; apply has_homsets_Signature_precategory).
+ abstract (intros X Hi;  apply SignatureMor_eq; simpl;
            apply (CoproductArrowUnique _ _ _ (CCD (λ j, pr1 (Hti j)))); intro i;
            apply (maponpaths pr1 (Hi i))).
Defined.

Lemma Coproducts_Signature_precategory : Coproducts I (Signature_precategory C D D').
Proof.
intros Ht.
use make_Coproduct.
- apply (Sum_of_Signatures I _ _ _ _ _ _ CD Ht).
- apply Signature_precategory_in.
- apply isCoproduct_Signature_precategory.
Defined.

End Coproducts.
