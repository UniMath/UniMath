(**

Definition of the category of signatures with strength ([Signature_precategory]) with

- Binary products ([BinProducts_Signature_precategory])
- Coproducts ([Coproducts_Signature_precategory])

Written by: Anders Mörtberg in October 2016 based on a note of Benedikt Ahrens.

*)
Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.

Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.

Local Notation "[ C , D ]" := (functor_Precategory C D).

(** * The category of signatures with strength *)
Section SignatureCategory.

Variables (C : Precategory).

Let hsC : has_homsets C := homset_property C.

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
Variables (X : [C,C]) (Y : Ptd).

Let f1 : [C,C] ⟦H X • U Y,H (X • U Y)⟧ := θ (X,,Y).
Let f2 : [C,C] ⟦H (X • U Y),H' (X • U Y)⟧ := α (X • U Y).

Let g1 : [C,C] ⟦H X • U Y,H' X • U Y⟧ := α X ∙∙ identity (U Y).
Let g2 : [C,C] ⟦H' X • U Y,H' (X • U Y)⟧ := θ' (X,,Y).

Definition Signature_category_mor_diagram : UU := f1 ;; f2 = g1 ;; g2.

(** Special comparison lemma that speeds things up a lot *)
Lemma Signature_category_mor_diagram_pointwise
  (Hc : Π c, pr1 f1 c ;; pr1 f2 c = pr1 (α X) ((pr1 Y) c) ;; pr1 g2 c) :
   Signature_category_mor_diagram.
Proof.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite functor_id, id_right; apply (Hc c).
Qed.

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
apply Signature_category_mor_diagram_pointwise; intro c; simpl.
now rewrite id_left, id_right.
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
etrans; [apply (cancel_postcomposition _ _ _ _ ((theta Ht1) (X,,Y) ;; _)), Hα|].
rewrite <- assoc; etrans; [apply maponpaths, Hβ|].
rewrite assoc; apply (cancel_postcomposition [C,C] _ _ _ _ (_ ∙∙ identity (U Y))).
apply (nat_trans_eq hsC); intro c; simpl.
now rewrite assoc, !functor_id, !id_right.
Qed.

Definition SignatureMor_comp (Ht1 Ht2 Ht3 : Signature C hsC)
  (α : SignatureMor Ht1 Ht2) (β : SignatureMor Ht2 Ht3) : SignatureMor Ht1 Ht3 :=
    (nat_trans_comp (pr1 α) (pr1 β),,SignatureMor_comp_subproof Ht1 Ht2 Ht3 α β).

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
apply (isofhleveltotal2 2).
* apply isaset_nat_trans, functor_category_has_homsets.
* intros α.
  apply isasetaprop.
  apply impred; intros X; apply impred; intros Y.
  apply functor_category_has_homsets.
Qed.

Definition SignatureForgetfulFunctor : functor Signature_precategory [[C,C],[C,C]].
Proof.
mkpair.
- mkpair.
  + intros F; apply(Signature_Functor _ _ F).
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

End SignatureCategory.

(** * Binary products in the category of signatures *)
Section BinProducts.

Variables (C : Precategory) (BC : BinProducts C).

Let hsC : has_homsets C := homset_property C.

Local Definition BCC : BinProducts [[C,C],[C,C]].
Proof.
apply BinProducts_functor_precat, (BinProducts_functor_precat C _ BC).
Defined.

Local Lemma Signature_precategory_pr1_diagram (Ht1 Ht2 : Signature C hsC) X Y :
  Signature_category_mor_diagram _ (BinProduct_of_Signatures _ _ _ Ht1 Ht2) _
    (BinProductPr1 _ (BCC _ _)) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c; apply BinProductOfArrowsPr1.
Qed.

Local Definition Signature_precategory_pr1 (Ht1 Ht2 : Signature C hsC) :
  SignatureMor C (BinProduct_of_Signatures C hsC BC Ht1 Ht2) Ht1.
Proof.
mkpair.
+ apply (BinProductPr1 _ (BCC (pr1 Ht1) (pr1 Ht2))).
+ apply Signature_precategory_pr1_diagram.
Defined.

Local Lemma Signature_precategory_pr2_diagram (Ht1 Ht2 : Signature C hsC) X Y :
  Signature_category_mor_diagram _ (BinProduct_of_Signatures _ _ _ Ht1 Ht2) _
    (BinProductPr2 _ (BCC _ _)) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c; apply BinProductOfArrowsPr2.
Qed.

Local Definition Signature_precategory_pr2 (Ht1 Ht2 : Signature C hsC) :
  SignatureMor C (BinProduct_of_Signatures C hsC BC Ht1 Ht2) Ht2.
Proof.
mkpair.
+ apply (BinProductPr2 _ (BCC (pr1 Ht1) (pr1 Ht2))).
+ apply Signature_precategory_pr2_diagram.
Defined.

Local Lemma BinProductArrow_diagram Ht1 Ht2 Ht3
  (F : SignatureMor C Ht3 Ht1) (G : SignatureMor C Ht3 Ht2) X Y :
  Signature_category_mor_diagram _ _ (BinProduct_of_Signatures _ _ _ Ht1 Ht2)
    (BinProductArrow _ (BCC _ _) (pr1 F) (pr1 G)) X Y.
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

Local Lemma isBinProductCone_Signature_precategory (Ht1 Ht2 : Signature C hsC) :
  isBinProductCone (Signature_precategory C) Ht1 Ht2
                   (BinProduct_of_Signatures C hsC BC Ht1 Ht2)
                   (Signature_precategory_pr1 Ht1 Ht2) (Signature_precategory_pr2 Ht1 Ht2).
Proof.
apply (mk_isBinProductCone _ (has_homsets_Signature_precategory C)).
simpl; intros Ht3 F G.
use unique_exists; simpl.
- apply (tpair _ (BinProductArrow _ (BCC (pr1 Ht1) (pr1 Ht2)) (pr1 F) (pr1 G))).
  apply BinProductArrow_diagram.
- abstract (split;
    [ apply SignatureMor_eq, (BinProductPr1Commutes _ _ _ (BCC  _ _))
    | apply SignatureMor_eq, (BinProductPr2Commutes _ _ _ (BCC  _ _))]).
- abstract (intros X; apply isapropdirprod; apply has_homsets_Signature_precategory).
- abstract (intros X H1H2; apply SignatureMor_eq; simpl;
    apply (BinProductArrowUnique _ _ _ (BCC  _ _));
      [ apply (maponpaths pr1 (pr1 H1H2)) | apply (maponpaths pr1 (pr2 H1H2)) ]).
Defined.

Lemma BinProducts_Signature_precategory : BinProducts (Signature_precategory C).
Proof.
intros Ht1 Ht2.
use mk_BinProductCone.
- apply (BinProduct_of_Signatures _ _ BC Ht1 Ht2).
- apply Signature_precategory_pr1.
- apply Signature_precategory_pr2.
- apply isBinProductCone_Signature_precategory.
Defined.

End BinProducts.

(** * Coproducts in the category of signatures *)
Section Coproducts.

Variables (I : UU) (HI : isdeceq I).
Variables (C : Precategory) (CC : Coproducts I C).

Let hsC : has_homsets C := homset_property C.

Local Definition CCC : Coproducts I [[C,C],[C,C]].
Proof.
now repeat apply Coproducts_functor_precat.
Defined.

Local Lemma Signature_precategory_in_diagram (Ht : I → Signature_precategory C) i X Y :
  Signature_category_mor_diagram _ _ (Sum_of_Signatures I C _ CC Ht)
    (CoproductIn _ _ (CCC (λ j : I, pr1 (Ht j))) i) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c.
apply pathsinv0.
set (C1 := CC (λ j, pr1 (pr1 (Ht j) X) ((pr1 Y) c))).
set (C2 := CC (λ j, pr1 (pr1 (Ht j) (functor_composite (pr1 Y) X)) c)).
apply (@CoproductOfArrowsIn I C _ C1 _ C2).
Defined.

Local Definition Signature_precategory_in (Ht : I → Signature_precategory C) (i : I) :
  SignatureMor C (Ht i) (Sum_of_Signatures I C _ CC Ht).
Proof.
mkpair.
+ apply (CoproductIn _ _ (CCC (λ j, pr1 (Ht j))) i).
+ apply Signature_precategory_in_diagram.
Defined.

Lemma CoproductArrow_diagram (Hti : I → Signature_precategory C)
  (Ht : Signature C hsC) (F : Π i : I, SignatureMor C (Hti i) Ht) X Y :
  Signature_category_mor_diagram C (Sum_of_Signatures I C hsC CC Hti) Ht
    (CoproductArrow I _ (CCC _) (λ i, pr1 (F i))) X Y.
Proof.
apply Signature_category_mor_diagram_pointwise; intro c.
etrans; [apply precompWithCoproductArrow|].
apply pathsinv0, CoproductArrowUnique; intro i; rewrite assoc; simpl.
etrans;
  [apply cancel_postcomposition, (CoproductInCommutes _ _ _ (CC (λ j, pr1 (pr1 (Hti j) X) _)))|].
apply pathsinv0; etrans; [apply (nat_trans_eq_pointwise (pr2 (F i) X Y) c)|].
now etrans; [apply cancel_postcomposition, horcomp_id_left|].
Qed.

Local Lemma isCoproductCocone_Signature_precategory (Hti : I → Signature_precategory C) :
  isCoproductCocone I (Signature_precategory C) _
    (Sum_of_Signatures I C hsC CC Hti) (Signature_precategory_in Hti).
Proof.
apply (mk_isCoproductCocone _ _ (has_homsets_Signature_precategory C)); simpl.
intros Ht F.
use unique_exists; simpl.
+ mkpair.
  - apply (CoproductArrow I _ (CCC (λ j, pr1 (Hti j))) (λ i, pr1 (F i))).
  - apply CoproductArrow_diagram.
+ abstract (intro i; apply SignatureMor_eq, (CoproductInCommutes _ _ _ (CCC (λ j, pr1 (Hti j))))).
+ abstract (intros X; apply impred; intro i; apply has_homsets_Signature_precategory).
+ abstract (intros X Hi;  apply SignatureMor_eq; simpl;
            apply (CoproductArrowUnique _ _ _ (CCC (λ j, pr1 (Hti j)))); intro i;
            apply (maponpaths pr1 (Hi i))).
Defined.

Lemma Coproducts_Signature_precategory : Coproducts I (Signature_precategory C).
Proof.
intros Ht.
use mk_CoproductCocone.
- apply (Sum_of_Signatures I _ _ CC Ht).
- apply Signature_precategory_in.
- apply isCoproductCocone_Signature_precategory.
Defined.

End Coproducts.
