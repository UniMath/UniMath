(** **********************************************************

Anders Mörtberg, 2016

************************************************************)

(** **********************************************************

Contents :

- Definition of the sum of a family of signatures ([Sum_of_Signatures)]

Adapted from the binary case

************************************************************)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.SubstitutionSystems.Notation.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.limits.products.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Arguments θ_source {_ _} _ .
Arguments θ_target {_ _} _ .
Arguments θ_Strength1 {_ _ _} _ .
Arguments θ_Strength2 {_ _ _} _ .
Arguments θ_Strength1_int {_ _ _} _ .
Arguments θ_Strength2_int {_ _ _} _ .

Section sum_of_signatures.

Variables (I : UU) (C : precategory) (hsC : has_homsets C).
Variables (CC : Coproducts I C).

Section construction.

Local Notation "'CCC'" := (Coproducts_functor_precat I C C CC hsC : Coproducts I [C, C, hsC]).

Variables H1 : I -> functor [C, C, hsC] [C, C, hsC].

Variable θ1 : ∏ i, θ_source (H1 i) ⟶ θ_target (H1 i).

(** * Definition of the data of the sum of two signatures *)

Local Definition H : functor [C, C, hsC] [C, C, hsC] := coproduct_of_functors _ _ _ CCC H1.

Local Definition θ_ob_fun (X : [C, C, hsC]) (Z : precategory_Ptd C hsC) (x : C) :
   C ⟦ coproduct_of_functors_ob _ _ _ CC (λ i, H1 i X) (pr1 Z x),
       coproduct_of_functors_ob _ _ _ CC (λ i, H1 i (functor_composite (pr1 Z) X)) x ⟧.
Proof.
apply CoproductOfArrows; intro i.
exact (pr1 (θ1 i (X ⊗ Z)) x).
Defined.

Local Lemma is_nat_trans_θ_ob_fun (X : [C, C, hsC]) (Z : precategory_Ptd C hsC) :
  is_nat_trans (functor_composite_data (pr1 Z)
                 (coproduct_of_functors_data _ _ _  CC (λ i, H1 i X)))
                 (coproduct_of_functors_data _ _ _ CC (λ i, H1 i (functor_composite (pr1 Z) X)))
               (θ_ob_fun X Z).
Proof.
intros x x' f.
eapply pathscomp0; [ apply CoproductOfArrows_comp | ].
eapply pathscomp0; [ | eapply pathsinv0; apply CoproductOfArrows_comp].
apply CoproductOfArrows_eq, funextsec; intro i.
apply (nat_trans_ax (θ1 i (X ⊗ Z))).
Qed.

Definition θ_ob : ∏ XF, θ_source H XF --> θ_target H XF.
Proof.
intros [X Z]; exists (θ_ob_fun X Z); apply is_nat_trans_θ_ob_fun.
Defined.

Local Lemma is_nat_trans_θ_ob :
  is_nat_trans (θ_source_functor_data C hsC H) (θ_target_functor_data C hsC H) θ_ob.
Proof.
intros [X Z] [X' Z'] αβ.
apply (nat_trans_eq hsC); intro c.
eapply pathscomp0; [ | eapply pathsinv0, CoproductOfArrows_comp].
eapply pathscomp0; [ apply cancel_postcomposition, CoproductOfArrows_comp |].
eapply pathscomp0; [ apply CoproductOfArrows_comp |].
apply CoproductOfArrows_eq, funextsec; intro i.
apply (nat_trans_eq_pointwise (nat_trans_ax (θ1 i) (X,,Z) (X',,Z') αβ) c).
Qed.

Local Definition θ : θ_source H ⟶ θ_target H := tpair _ _ is_nat_trans_θ_ob.

(** * Proof of the strength laws of the sum of two signatures *)

Variable S11' : ∏ i, θ_Strength1_int (θ1 i).
Variable S12' : ∏ i, θ_Strength2_int (θ1 i).

Lemma SumStrength1' : θ_Strength1_int θ.
Proof.
intro X.
apply (nat_trans_eq hsC); intro x; simpl.
eapply pathscomp0; [apply CoproductOfArrows_comp|].
apply pathsinv0, Coproduct_endo_is_identity; intro i.
eapply pathscomp0.
  apply (CoproductOfArrowsIn _ _ (CC (λ i, pr1 (pr1 (H1 i) X) x))).
eapply pathscomp0; [ | apply id_left].
apply cancel_postcomposition, (nat_trans_eq_pointwise (S11' i X) x).
Qed.

Lemma SumStrength2' : θ_Strength2_int θ.
Proof.
intros X Z Z'.
apply (nat_trans_eq hsC); intro x; simpl; rewrite id_left.
eapply pathscomp0; [apply CoproductOfArrows_comp|].
apply pathsinv0.
eapply pathscomp0; [apply CoproductOfArrows_comp|].
apply pathsinv0, CoproductOfArrows_eq, funextsec; intro i.
assert (Ha_x := nat_trans_eq_pointwise (S12' i X Z Z') x); simpl in Ha_x.
rewrite id_left in Ha_x; apply Ha_x.
Qed.

End construction.

Definition Sum_of_Signatures (S : I -> Signature C hsC) : Signature C hsC.
Proof.
mkpair.
- apply H; intro i.
  apply (S i).
- exists (θ (fun i => S i) (fun i => theta (S i))).
  split.
  + apply SumStrength1'; intro i; apply (Sig_strength_law1 _ _ (S i)).
  + apply SumStrength2'; intro i; apply (Sig_strength_law2 _ _ (S i)).
Defined.

Lemma is_omega_cocont_Sum_of_Signatures (S : I -> Signature C hsC)
  (h : ∏ i, is_omega_cocont (S i)) (PC : Products I C) :
  is_omega_cocont (Sum_of_Signatures S).
Proof.
apply is_omega_cocont_coproduct_of_functors; try assumption.
- apply functor_category_has_homsets.
Defined.

End sum_of_signatures.
