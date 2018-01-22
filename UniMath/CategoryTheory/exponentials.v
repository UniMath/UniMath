
(** **********************************************************

Anders Mörtberg, 2016

************************************************************)


(** **********************************************************

Contents:

- Definition of the functors given by binary product with
  a fixed object
- Definition of exponentials


************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.limits.binproducts.

Local Open Scope cat.

Section exponentials.

Context {C : precategory} (PC : BinProducts C) (hsC : has_homsets C).

(* The functor "a * _" and "_ * a" *)
Definition constprod_functor1 (a : C) : functor C C :=
  BinProduct_of_functors C C PC (constant_functor C C a) (functor_identity C).

Definition constprod_functor2 (a : C) : functor C C :=
  BinProduct_of_functors C C PC (functor_identity C) (constant_functor C C a).

Definition is_exponentiable (a : C) : UU := is_left_adjoint (constprod_functor1 a).

Definition has_exponentials : UU := ∏ (a : C), is_exponentiable a.

Definition nat_trans_constprod_functor1 (a : C) :
  nat_trans (constprod_functor1 a) (constprod_functor2 a).
Proof.
use tpair.
- intro x; simpl; unfold BinProduct_of_functors_ob; simpl.
  apply BinProductArrow; [ apply BinProductPr2 | apply BinProductPr1 ].
- abstract (intros x y f; simpl; unfold BinProduct_of_functors_mor; simpl;
  eapply pathscomp0; [apply precompWithBinProductArrow|];
  apply pathsinv0; eapply pathscomp0; [apply postcompWithBinProductArrow|];
  now rewrite (BinProductOfArrowsPr2 C _ (PC a x)), (BinProductOfArrowsPr1 C _ (PC a x))).
Defined.

Definition nat_trans_constprod_functor2 (a : C) :
  nat_trans (constprod_functor2 a) (constprod_functor1 a).
Proof.
use tpair.
- intro x; simpl; unfold BinProduct_of_functors_ob; simpl.
  apply BinProductArrow; [ apply BinProductPr2 | apply BinProductPr1 ].
- abstract (intros x y f; simpl; unfold BinProduct_of_functors_mor; simpl;
  eapply pathscomp0; [apply precompWithBinProductArrow|];
  apply pathsinv0; eapply pathscomp0; [apply postcompWithBinProductArrow|];
  now rewrite (BinProductOfArrowsPr2 C _ (PC x a)), (BinProductOfArrowsPr1 C _ (PC x a))).
Defined.

Lemma is_iso_constprod_functor1 a :
  @is_iso [C,C,hsC] _ _ (nat_trans_constprod_functor1 a).
Proof.
apply (@is_iso_qinv [C,C,hsC] _ _ _ (nat_trans_constprod_functor2 a)).
  split.
  + abstract (
    apply (nat_trans_eq hsC); intro x; simpl; unfold BinProduct_of_functors_ob; simpl;
    eapply pathscomp0; [apply precompWithBinProductArrow|];
    now rewrite BinProductPr1Commutes, BinProductPr2Commutes, BinProductArrowEta, !id_left).
  + abstract (
    apply (nat_trans_eq hsC); intro x; simpl; unfold BinProduct_of_functors_ob; simpl;
    eapply pathscomp0; [apply precompWithBinProductArrow|];
    now rewrite BinProductPr1Commutes, BinProductPr2Commutes, BinProductArrowEta, !id_left).
Defined.

(* This is not used *)
Lemma is_iso_constprod_functor2 a :
  @is_iso [C,C,hsC] _ _ (nat_trans_constprod_functor2 a).
Proof.
apply (@is_iso_qinv [C,C,hsC] _ _ _ (nat_trans_constprod_functor1 a)).
use tpair.
+ abstract (
  apply (nat_trans_eq hsC); intro x; simpl; unfold BinProduct_of_functors_ob; simpl;
  eapply pathscomp0; [apply precompWithBinProductArrow|];
  now rewrite BinProductPr1Commutes, BinProductPr2Commutes, BinProductArrowEta, !id_left).
+ abstract (
  apply (nat_trans_eq hsC); intro x; simpl; unfold BinProduct_of_functors_ob; simpl;
  eapply pathscomp0; [apply precompWithBinProductArrow|];
  now rewrite BinProductPr1Commutes, BinProductPr2Commutes, BinProductArrowEta, !id_left).
Defined.

Definition flip_iso a : @iso [C,C,hsC] (constprod_functor1 a) (constprod_functor2 a) :=
  tpair _ _ (is_iso_constprod_functor1 a).

Variable (a : C).
Variable (HF : is_left_adjoint (constprod_functor1 a)).

Local Notation F := (constprod_functor1 a).
Local Notation F' := (constprod_functor2 a).
Let G := right_adjoint HF.
Let H := pr2 HF : are_adjoints F G.
Let eta : [C,C,hsC]⟦functor_identity C,functor_composite F G⟧ := unit_from_left_adjoint H.
Let eps : [C,C,hsC]⟦functor_composite G F,functor_identity C⟧ := counit_from_left_adjoint H.
Let H1 := triangle_id_left_ad H.
Let H2 := triangle_id_right_ad H.

Arguments constprod_functor1 : simpl never.
Arguments constprod_functor2 : simpl never.
Arguments flip_iso : simpl never.

Local Definition eta' : [C,C,hsC]⟦functor_identity C,functor_composite F' G⟧ :=
  let G' := (post_composition_functor C C C hsC hsC G)
  in eta · (# G' (flip_iso a)).

Local Definition eps' : [C,C,hsC]⟦functor_composite G F',functor_identity C⟧ :=
  let G' := (pre_composition_functor C C C hsC hsC G)
  in # G' (inv_from_iso (flip_iso a)) · eps.

Local Lemma form_adjunction_eta'_eps' : form_adjunction F' G eta' eps'.
Proof.
fold eta in H1; fold eps in H1; fold eta in H2; fold eps in H2; fold G in H2.
use tpair.
+ intro x; unfold eta', eps'; cbn.
  rewrite assoc.
  eapply pathscomp0.
  - eapply cancel_postcomposition.
    exact (nat_trans_ax (inv_from_iso (flip_iso _)) _ _ _).
  - rewrite functor_comp, assoc.
    eapply pathscomp0; [rewrite <- assoc; apply maponpaths, (nat_trans_ax eps)|].
    rewrite <- assoc.
    eapply pathscomp0; [apply maponpaths; rewrite assoc; apply cancel_postcomposition, H1|].
    rewrite id_left.
    apply (nat_trans_eq_pointwise (iso_after_iso_inv (flip_iso a)) x).
+ intro x; cbn.
  rewrite <- (H2 x), <- assoc, <- (functor_comp G).
  apply maponpaths, maponpaths.
  rewrite assoc.
  apply remove_id_left; try apply idpath.
  apply (nat_trans_eq_pointwise (iso_inv_after_iso (flip_iso a))).
Qed.

Lemma is_left_adjoint_constprod_functor2 : is_left_adjoint F'.
Proof.
apply (tpair _ G).
apply (tpair _ (dirprodpair eta' eps')).
apply form_adjunction_eta'_eps'.
Defined.

End exponentials.
