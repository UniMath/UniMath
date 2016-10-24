(** **********************************************************

Contents:

- Definition of the binary product of two signatures
  ([BinProduct_of_Signatures]), in particular proof of strength
  laws for the product


Written by Anders Mörtberg, 2016 (adapted from SumOfSignatures.v)

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.exponentials.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Arguments θ_source {_ _} _ .
Arguments θ_target {_ _} _ .
Arguments θ_Strength1 {_ _ _} _ .
Arguments θ_Strength2 {_ _ _} _ .
Arguments θ_Strength1_int {_ _ _} _ .
Arguments θ_Strength2_int {_ _ _} _ .

Section binproduct_of_signatures.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable PC : BinProducts C.

Section construction.

Local Notation "'CCC'" := (BinProducts_functor_precat C C PC hsC : BinProducts [C, C, hsC]).

Variables H1 H2 : functor [C, C, hsC] [C, C, hsC].

Variable θ1 : θ_source H1 ⟶ θ_target H1.
Variable θ2 : θ_source H2 ⟶ θ_target H2.

Variable S11 : θ_Strength1 θ1.
Variable S12 : θ_Strength2 θ1.
Variable S21 : θ_Strength1 θ2.
Variable S22 : θ_Strength2 θ2.

(** * Definition of the data of the product of two signatures *)

Definition H : functor [C, C, hsC] [C, C, hsC] :=
  BinProduct_of_functors _ _ CCC H1 H2.

Local Definition θ_ob_fun (X : [C, C, hsC]) (Z : precategory_Ptd C hsC) :
   Π c : C,
    (functor_composite_data (pr1 Z)
     (BinProduct_of_functors_data C C PC (H1 X) (H2 X))) c
   --> (BinProduct_of_functors_data C C PC (H1 (functor_composite (pr1 Z) X))
       (H2 (functor_composite (pr1 Z) X))) c.
Proof.
  intro c.
  apply BinProductOfArrows.
  - exact (pr1 (θ1 (X ⊗ Z)) c).
  - exact (pr1 (θ2 (X ⊗ Z)) c).
Defined.

Local Lemma is_nat_trans_θ_ob_fun (X : [C, C, hsC]) (Z : precategory_Ptd C hsC):
   is_nat_trans _ _ (θ_ob_fun X Z).
Proof.
  intros x x' f.
  eapply pathscomp0; [ apply BinProductOfArrows_comp | ].
  eapply pathscomp0; [ | eapply pathsinv0; apply BinProductOfArrows_comp].
  apply BinProductOfArrows_eq.
  * apply (nat_trans_ax (θ1 (X ⊗ Z))).
  * apply (nat_trans_ax (θ2 (X ⊗ Z))).
Qed.

Definition θ_ob : Π XZ, θ_source H XZ --> θ_target H XZ.
Proof.
  intro XZ.
  exists (θ_ob_fun (pr1 XZ) (pr2 XZ)).
  apply is_nat_trans_θ_ob_fun.
Defined.

Local Lemma is_nat_trans_θ_ob :
 is_nat_trans (θ_source_functor_data C hsC H) (θ_target_functor_data C hsC H)
     θ_ob.
Proof.
  intros [X Z] [X' Z'] [α β].
  apply (nat_trans_eq hsC); intro c; simpl.
  eapply pathscomp0; [ | eapply pathsinv0, BinProductOfArrows_comp].
  eapply pathscomp0; [ apply cancel_postcomposition, BinProductOfArrows_comp |].
  eapply pathscomp0; [ apply BinProductOfArrows_comp |].
  apply BinProductOfArrows_eq.
  + exact (nat_trans_eq_pointwise (nat_trans_ax θ1 _ _ (α,,β)) c).
  + exact (nat_trans_eq_pointwise (nat_trans_ax θ2 _ _ (α,,β)) c).
Qed.

Local Definition θ : θ_source H ⟶ θ_target H.
Proof.
  exists θ_ob.
  apply is_nat_trans_θ_ob.
Defined.

(** * Proof of the laws of the product of two signatures *)

Lemma ProductStrength1 : θ_Strength1 θ.
Proof.
  intro X.
  apply (nat_trans_eq hsC); intro x.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  apply pathsinv0, BinProduct_endo_is_identity.
  + rewrite BinProductOfArrowsPr1.
    eapply pathscomp0; [ | apply id_right].
    apply maponpaths, (nat_trans_eq_pointwise (S11 X) x).
  + rewrite BinProductOfArrowsPr2.
    eapply pathscomp0; [ | apply id_right].
    apply maponpaths, (nat_trans_eq_pointwise (S21 X) x).
Qed.

Lemma ProductStrength2 : θ_Strength2 θ.
Proof.
  intros X Z Z' Y α.
  apply (nat_trans_eq hsC); intro x.
  eapply pathscomp0; [ apply BinProductOfArrows_comp |].
  apply pathsinv0.
  eapply pathscomp0; [ apply cancel_postcomposition; simpl; apply BinProductOfArrows_comp|].
  eapply pathscomp0; [ apply BinProductOfArrows_comp|].
  apply pathsinv0, BinProductOfArrows_eq.
  - assert (Ha := S12 X Z Z' Y α); simpl in Ha.
    apply (nat_trans_eq_pointwise Ha x).
  - assert (Ha := S22 X Z Z' Y α); simpl in Ha.
    apply (nat_trans_eq_pointwise Ha x).
Qed.

Variable S11' : θ_Strength1_int θ1.
Variable S12' : θ_Strength2_int θ1.
Variable S21' : θ_Strength1_int θ2.
Variable S22' : θ_Strength2_int θ2.

Lemma ProductStrength1' : θ_Strength1_int θ.
Proof.
  clear S11 S12 S21 S22 S12' S22'; intro X.
  apply (nat_trans_eq hsC); intro x.
  eapply pathscomp0; [ apply BinProductOfArrows_comp |].
  apply pathsinv0, BinProduct_endo_is_identity.
  + rewrite BinProductOfArrowsPr1.
    eapply pathscomp0; [ | apply id_right]; apply maponpaths.
    exact (nat_trans_eq_pointwise (S11' X) x).
  + rewrite BinProductOfArrowsPr2.
    eapply pathscomp0; [ | apply id_right]; apply maponpaths.
    exact (nat_trans_eq_pointwise (S21' X) x).
Qed.

Lemma ProductStrength2' : θ_Strength2_int θ.
Proof.
  clear S11 S12 S21 S22 S11' S21'; intros X Z Z'.
  apply (nat_trans_eq hsC); intro x; simpl.
  rewrite id_left.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  apply pathsinv0.
  eapply pathscomp0; [apply BinProductOfArrows_comp|].
  apply pathsinv0, BinProductOfArrows_eq.
  - assert (Ha_x := nat_trans_eq_pointwise (S12' X Z Z') x).
    simpl in Ha_x; rewrite id_left in Ha_x.
    exact Ha_x.
  - assert (Ha_x := nat_trans_eq_pointwise (S22' X Z Z') x).
    simpl in Ha_x; rewrite id_left in Ha_x.
    exact Ha_x.
Qed.

End construction.

(** Binary product of signatures *)
Definition BinProduct_of_Signatures (S1 S2 : Signature C hsC) : Signature C hsC.
Proof.
  (* destruct S1 as [H1 [θ1 [S11' S12']]]. *)
  (* destruct S2 as [H2 [θ2 [S21' S22']]]. *)
  exists (H (pr1 S1) (pr1 S2)).
  exists (θ (pr1 S1) (pr1 S2) (pr1 (pr2 S1)) (pr1 (pr2 S2))).
  split.
  + apply ProductStrength1'; [apply (pr1 (pr2 (pr2 S1)))|apply (pr1 (pr2 (pr2 S2)))].
  + apply ProductStrength2'; [apply (pr2 (pr2 (pr2 S1)))|apply (pr2 (pr2 (pr2 S2)))].
Defined.

Lemma is_omega_cocont_BinProduct_of_Signatures (S1 S2 : Signature C hsC)
  (h1 : is_omega_cocont S1) (h2 : is_omega_cocont S2)
  (hE : Π x, is_omega_cocont (constprod_functor1 (BinProducts_functor_precat C C PC hsC) x)) :
  is_omega_cocont (BinProduct_of_Signatures S1 S2).
Proof.
destruct S1 as [F1 [F2 [F3 F4]]]; simpl in *.
destruct S2 as [G1 [G2 [G3 G4]]]; simpl in *.
unfold H.
apply is_omega_cocont_BinProduct_of_functors; try assumption.
- apply (BinProducts_functor_precat _ _ PC).
- apply functor_category_has_homsets.
- apply functor_category_has_homsets.
Defined.

End binproduct_of_signatures.
