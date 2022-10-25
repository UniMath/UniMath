(**

Definition of the category of signatures with strength ([Signature_category]) with

- Binary products ([BinProducts_Signature_category])
- Coproducts ([Coproducts_Signature_category])

Written by: Anders Mörtberg in October 2016 based on a note of Benedikt Ahrens.

In 2021 obtained by Ralph Matthes from the Structure Identity Principle through a displayed category, hence allowing for a short proof of univalence.

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
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.

Local Open Scope cat.

Local Notation "[ C , D ]" := (functor_category C D).

(** * The category of signatures with strength *)
Section SignatureCategory.

Variables (C D D': category).

Local Notation "'U'" := (functor_ptd_forget C).
Local Notation "'Ptd'" := (category_Ptd C).

(** Define the commutative diagram used in the morphisms *)
Section Signature_category_mor.

Variables (Ht Ht' : Signature C D D').

Let H := Signature_Functor Ht.
Let H' := Signature_Functor Ht'.
Let θ : PrestrengthForSignature Ht := theta Ht.
Let θ' : PrestrengthForSignature Ht' := theta Ht'.

Variables (α : nat_trans H H').

Section Signature_category_mor_diagram.
Variables (X : [C,D']) (Y : Ptd).

Let f1 : [C,D] ⟦H X • U Y,H (X • U Y)⟧ := θ (X,,Y).
Let f2 : [C,D] ⟦H (X • U Y),H' (X • U Y)⟧ := α (X • U Y).

Let g1 : [C,D] ⟦H X • U Y,H' X • U Y⟧ := α X ⋆ identity (U Y).
Let g2 : [C,D] ⟦H' X • U Y,H' (X • U Y)⟧ := θ' (X,,Y).

Definition Signature_category_mor_diagram : UU := f1 · f2 = g1 · g2.

(** Special comparison lemma that speeds things up a lot *)
Lemma Signature_category_mor_diagram_pointwise
  (Hc : ∏ c, pr1 f1 c · pr1 f2 c = pr1 (α X) ((pr1 Y) c) · pr1 g2 c) :
   Signature_category_mor_diagram.
Proof.
  apply nat_trans_eq_alt; intro c; simpl. unfold horcomp_data; simpl.
  rewrite functor_id, id_right; apply (Hc c).
Qed.

End Signature_category_mor_diagram.

Definition quantified_signature_category_mor_diagram : UU := ∏ X Y, Signature_category_mor_diagram X Y.

End Signature_category_mor.

Local Lemma SignatureMor_id_subproof (Ht : Signature C D D') X Y :
  Signature_category_mor_diagram Ht Ht (nat_trans_id Ht) X Y.
Proof.
  apply Signature_category_mor_diagram_pointwise; intro c; simpl.
  now rewrite id_left, id_right.
Qed.

Local Lemma SignatureMor_comp_subproof (Ht1 Ht2 Ht3 : Signature C D D')
           (α : nat_trans Ht1 Ht2) (β : nat_trans Ht2 Ht3):
  quantified_signature_category_mor_diagram Ht1 Ht2 α ->
  quantified_signature_category_mor_diagram Ht2 Ht3 β ->
  quantified_signature_category_mor_diagram Ht1 Ht3 (nat_trans_comp α β).
Proof.
  intros Hα Hβ X Y.
  unfold quantified_signature_category_mor_diagram in *|-.
  unfold Signature_category_mor_diagram in *; simpl.
  rewrite (assoc ((theta Ht1) (X,,Y))).
  etrans; [apply (cancel_postcomposition ((theta Ht1) (X,,Y) · _)), Hα|].
  rewrite <- assoc; etrans; [apply maponpaths, Hβ|].
  rewrite assoc; apply (cancel_postcomposition (C:=[C,D]) _  (_ ⋆ identity (U Y))).
  apply nat_trans_eq_alt; intro c; simpl. unfold horcomp_data; simpl.
  now rewrite assoc, !functor_id, !id_right.
Qed.

  Definition Signature_category_displayed : disp_cat [[C,D'],[C,D]].
  Proof.
    use disp_cat_from_SIP_data.
    - intro H.
      exact (@StrengthForSignature C D D' H).
    - intros H1 H2 str1 str2 α.
      exact (quantified_signature_category_mor_diagram (H1,,str1) (H2,,str2) α).
    - intros H1 H2 str1 str2 α.
      do 2 (apply impred; intro).
      apply functor_category_has_homsets.
    - intros H a X Z.
      apply SignatureMor_id_subproof.
    - intros H1 H2 H3 str1 str2 str3 a1 a2 a1mor a2mor. simpl in a1mor, a2mor.
      simpl.
      exact (SignatureMor_comp_subproof (H1,,str1) (H2,,str2) (H3,,str3) a1 a2 a1mor a2mor).
  Defined.

  Definition Signature_category : category := total_category Signature_category_displayed.

  Lemma Signature_category_ob_ok : ob Signature_category = Signature C D D'.
  Proof.
    apply idpath.
  Qed.

  (* what would be the right source class for the following coercion?
  Definition Signature_category_ob_to_functor_data (sig : Signature_category) :
    functor_data [C, D', hsD'] [C, D, hsD]
    := pr1 (pr1 sig).
  Coercion Signature_category_ob_to_functor_data : Signature_category >-> functor_data.
*)

  Definition SignatureMor : Signature C D D' → Signature C D D' → UU.
  Proof.
    exact (pr2 (precategory_ob_mor_from_precategory_data Signature_category)).
  Defined.

  Lemma SignatureMor_ok (Ht Ht' : Signature C D D') :
    SignatureMor Ht Ht' = total2 (quantified_signature_category_mor_diagram Ht Ht').
  Proof.
    apply idpath.
  Qed.

  Definition SignatureMor_to_nat_trans (Ht Ht' : Signature C D D') :
    SignatureMor Ht Ht' -> Ht ⟹ Ht'.
  Proof.
    intro f.
    exact (pr1 f).
  Defined.
  Coercion SignatureMor_to_nat_trans : SignatureMor >-> nat_trans.

  Lemma SignatureMor_eq (Ht Ht' : Signature C D D') (f g : SignatureMor Ht Ht') :
    (pr1 f: pr1 Ht ⟹ pr1 Ht') = (pr1 g: pr1 Ht ⟹ pr1 Ht') -> f = g.
  Proof.
    intros H.
    apply subtypePath; trivial.
    now intros α; repeat (apply impred; intro); apply functor_category_has_homsets.
  Qed.

  Definition SignatureForgetfulFunctor : functor Signature_category [[C,D'],[C,D]].
  Proof.
    use tpair.
    - use tpair.
      + intros F; apply (Signature_Functor F).
      + intros F G α; apply α.
    - abstract (now split).
  Defined.

  Lemma SignatureForgetfulFunctorFaithful : faithful SignatureForgetfulFunctor.
  Proof.
    intros F G.
    apply isinclbetweensets.
    + apply Signature_category.
    + apply functor_category_has_homsets.
    + apply SignatureMor_eq.
  Qed.

(** towards univalence *)

  Lemma Signature_category_Pisset (H : [[C, D'], [C, D]]) : isaset (@StrengthForSignature C D D' H).
  Proof.
    change isaset with (isofhlevel 2).
    apply isofhleveltotal2.
    { apply (functor_category_has_homsets ([C, D'] ⊠ category_Ptd C) ([C, D]) (functor_category_has_homsets _ _ _)). }
    intro θ.
    apply isasetaprop.
    apply isapropdirprod.
    + apply isaprop_θ_Strength1_int.
    + apply isaprop_θ_Strength2_int.
  Qed.

  Lemma Signature_category_Hstandard (H : [[C, D'], [C, D]]) (a a' : @StrengthForSignature C D D' H) :
  (∏ (X : [C, D']) (Y : category_Ptd C),
  Signature_category_mor_diagram (H,, a) (H,, a') (identity H) X Y)
 → (∏ (X : [C, D']) (Y : category_Ptd C),
    Signature_category_mor_diagram (H,, a') (H,, a) (identity H) X Y)
 → a = a'.
  Proof.
    intros leq geq.
    apply StrengthForSignature_eq.
    apply (nat_trans_eq (functor_category_has_homsets _ _ _)).
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
    apply nat_trans_eq; [apply homset_property |].
    intro c.
    cbn. unfold horcomp_data; simpl.
    rewrite id_left.
    apply functor_id.
  Qed.

  Definition is_univalent_Signature_category_displayed : is_univalent_disp Signature_category_displayed.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - exact Signature_category_Pisset.
    - exact Signature_category_Hstandard.
  Defined.


End SignatureCategory.

Definition is_univalent_Signature_category (C : category) (D: univalent_category) (D' : category) :
  is_univalent (Signature_category C D D').
Proof.
  apply SIP.
  - exact (is_univalent_functor_category [C, D'] _ (is_univalent_functor_category C D (pr2 D))).
  - apply Signature_category_Pisset.
  - apply Signature_category_Hstandard.
Defined.



(** * Binary products in the category of signatures *)
Section BinProducts.

Variables (C : category) (BC : BinProducts C) (D : category) (BD : BinProducts D) (D' : category).

Local Definition BCD : BinProducts [[C,D'],[C,D]].
Proof.
apply BinProducts_functor_precat, (BinProducts_functor_precat C _ BD).
Defined.

Local Lemma Signature_category_pr1_diagram (Ht1 Ht2 : Signature C D D') X Y :
  Signature_category_mor_diagram _ _ _ (BinProduct_of_Signatures _ _ _ _ Ht1 Ht2) _
    (BinProductPr1 _ (BCD _ _)) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c; apply BinProductOfArrowsPr1.
Qed.

Local Definition Signature_category_pr1 (Ht1 Ht2 : Signature C D D') :
  SignatureMor C D D' (BinProduct_of_Signatures C D D' BD Ht1 Ht2) Ht1.
Proof.
use tpair.
+ apply (BinProductPr1 _ (BCD (pr1 Ht1) (pr1 Ht2))).
+ cbn. intros X Y. apply Signature_category_pr1_diagram.
Defined.

Local Lemma Signature_category_pr2_diagram (Ht1 Ht2 : Signature C D D' ) X Y :
  Signature_category_mor_diagram _ _ _ (BinProduct_of_Signatures _ _ _ _ Ht1 Ht2) _
    (BinProductPr2 _ (BCD _ _)) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c; apply BinProductOfArrowsPr2.
Qed.

Local Definition Signature_category_pr2 (Ht1 Ht2 : Signature C D D' ) :
  SignatureMor C D D' (BinProduct_of_Signatures C D D' BD Ht1 Ht2) Ht2.
Proof.
use tpair.
+ apply (BinProductPr2 _ (BCD (pr1 Ht1) (pr1 Ht2))).
+ cbn. intros X Y. apply Signature_category_pr2_diagram.
Defined.

Local Lemma BinProductArrow_diagram Ht1 Ht2 Ht3
  (F : SignatureMor C D D' Ht3 Ht1) (G : SignatureMor C D D' Ht3 Ht2) X Y :
  Signature_category_mor_diagram _ _ _ _ (BinProduct_of_Signatures _ _ _ _ Ht1 Ht2)
    (BinProductArrow _ (BCD _ _) (pr1 F) (pr1 G)) X Y.
Proof.
  apply Signature_category_mor_diagram_pointwise; intro c.
  apply pathsinv0.
  etrans; [ apply postcompWithBinProductArrow |].
  apply pathsinv0, BinProductArrowUnique; rewrite <- assoc.
  + etrans; [ apply maponpaths, BinProductPr1Commutes |].
  etrans; [ apply (nat_trans_eq_pointwise (pr2 F X Y) c) |].
  now etrans; [ apply cancel_postcomposition, horcomp_id_left |].
+ etrans; [ apply maponpaths, BinProductPr2Commutes |].
  etrans; [ apply (nat_trans_eq_pointwise (pr2 G X Y) c) |].
  now etrans; [ apply cancel_postcomposition, horcomp_id_left |].
Qed.

Local Lemma isBinProduct_Signature_category (Ht1 Ht2 : Signature C D D') :
  isBinProduct (Signature_category C D D') Ht1 Ht2
                   (BinProduct_of_Signatures C D D' BD Ht1 Ht2)
                   (Signature_category_pr1 Ht1 Ht2) (Signature_category_pr2 Ht1 Ht2).
Proof.
  apply make_isBinProduct.
  intros Ht3 F G.
  use unique_exists.
  - apply (tpair _ (BinProductArrow _ (BCD (pr1 Ht1) (pr1 Ht2)) (pr1 F) (pr1 G))).
    intros X Y. apply BinProductArrow_diagram.
  - abstract (split;
              [ apply SignatureMor_eq, (BinProductPr1Commutes _ _ _ (BCD  _ _))
              | apply SignatureMor_eq, (BinProductPr2Commutes _ _ _ (BCD  _ _))]).
  - abstract (intros X; apply isapropdirprod; apply Signature_category).
  - abstract (intros X H1H2; apply SignatureMor_eq; simpl;
              apply (BinProductArrowUnique _ _ _ (BCD  _ _));
              [ apply (maponpaths pr1 (pr1 H1H2)) | apply (maponpaths pr1 (pr2 H1H2)) ]).
Defined.

Lemma BinProducts_Signature_category : BinProducts (Signature_category C D D').
Proof.
  intros Ht1 Ht2.
  use make_BinProduct.
  - apply (BinProduct_of_Signatures _ _ _ BD Ht1 Ht2).
  - apply Signature_category_pr1.
  - apply Signature_category_pr2.
  - apply isBinProduct_Signature_category.
Defined.

End BinProducts.

(** * Coproducts in the category of signatures *)
Section Coproducts.

Variables (I : UU).
Variables (C D D' : category) (CD : Coproducts I D).

Local Definition CCD : Coproducts I [[C,D'],[C,D]].
Proof.
  now repeat apply Coproducts_functor_precat.
Defined.

Local Lemma Signature_category_in_diagram (Ht : I → Signature_category C D D') i X Y :
  Signature_category_mor_diagram _ _ _ _ (Sum_of_Signatures I C _ _ CD Ht)
    (CoproductIn _ _ (CCD (λ j : I, pr1 (Ht j))) i) X Y.
Proof.
  apply Signature_category_mor_diagram_pointwise; intro c.
  apply pathsinv0.
  set (C1 := CD (λ j, pr1 (pr1 (pr1 (Ht j)) X) ((pr1 Y) c))).
  set (C2 := CD (λ j, pr1 (pr1 (pr1 (Ht j)) (functor_composite (pr1 Y) X)) c)).
  apply (@CoproductOfArrowsIn I D _ C1 _ C2).
Defined.

Local Definition Signature_category_in (Ht : I → Signature_category C D D') (i : I) :
  SignatureMor C D D' (Ht i) (Sum_of_Signatures I C D D' CD Ht).
Proof.
  use tpair.
  + apply (CoproductIn _ _ (CCD (λ j, pr1 (Ht j))) i).
  + cbn. intros X Y. apply Signature_category_in_diagram.
Defined.

Lemma CoproductArrow_diagram (Hti : I → Signature_category C D D')
  (Ht : Signature C D D') (F : ∏ i : I, SignatureMor C D D' (Hti i) Ht) X Y :
  Signature_category_mor_diagram C D D' (Sum_of_Signatures I C D D' CD Hti) Ht
    (CoproductArrow I _ (CCD _) (λ i, pr1 (F i))) X Y.
Proof.
  apply Signature_category_mor_diagram_pointwise; intro c.
  etrans; [apply precompWithCoproductArrow|].
  apply pathsinv0, CoproductArrowUnique; intro i; rewrite assoc; simpl.
  etrans;
    [apply cancel_postcomposition, (CoproductInCommutes _ _ _ (CD (λ j, pr1 (pr1 (pr1 (Hti j)) X) _)))|].
  apply pathsinv0; etrans; [apply (nat_trans_eq_pointwise (pr2 (F i) X Y) c)|].
  now etrans; [apply cancel_postcomposition, horcomp_id_left|].
Qed.

Local Lemma isCoproduct_Signature_category (Hti : I → Signature_category C D D') :
  isCoproduct I (Signature_category C D D') _
    (Sum_of_Signatures I C D D' CD Hti) (Signature_category_in Hti).
Proof.
  apply (make_isCoproduct _ _ (Signature_category C D D')).
  intros Ht F.
  use unique_exists.
  + use tpair.
  - apply (CoproductArrow I _ (CCD (λ j, pr1 (Hti j))) (λ i, pr1 (F i))).
  - cbn. intros X Y. apply CoproductArrow_diagram.
    + abstract (intro i; apply SignatureMor_eq, (CoproductInCommutes _ _ _ (CCD (λ j, pr1 (Hti j))))).
    + abstract (intros X; apply impred; intro i; apply Signature_category).
    + abstract (intros X Hi;  apply SignatureMor_eq; simpl;
                apply (CoproductArrowUnique _ _ _ (CCD (λ j, pr1 (Hti j)))); intro i;
                apply (maponpaths pr1 (Hi i))).
Defined.

Lemma Coproducts_Signature_category : Coproducts I (Signature_category C D D').
Proof.
  intros Ht.
  use make_Coproduct.
  - apply (Sum_of_Signatures I _ _ _ CD Ht).
  - apply Signature_category_in.
  - apply isCoproduct_Signature_category.
Defined.

End Coproducts.
