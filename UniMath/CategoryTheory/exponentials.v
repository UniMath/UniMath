Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinProduct.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section exponentials.

Context {C : precategory} (PC : Products C) (hsC : has_homsets C).

(* The functor "a * _" and "_ * a" *)
Definition constprod_functor1 (a : C) : functor C C :=
  product_functor C C PC (constant_functor C C a) (functor_identity C).

Definition constprod_functor2 (a : C) : functor C C :=
  product_functor C C PC (functor_identity C) (constant_functor C C a).

Definition is_exponentiable (a : C) : UU := is_left_adjoint (constprod_functor1 a).

Definition has_exponentials : UU := forall (a : C), is_exponentiable a.

Definition nat_trans_constprod_functor1 (a : C) :
  nat_trans (constprod_functor1 a) (constprod_functor2 a).
Proof.
mkpair.
- intro x; simpl; unfold product_functor_ob; simpl.
  apply ProductArrow; [ apply ProductPr2 | apply ProductPr1 ].
- abstract (intros x y f; simpl; unfold product_functor_mor; simpl;
  eapply pathscomp0; [apply precompWithProductArrow|];
  apply pathsinv0; eapply pathscomp0; [apply postcompWithProductArrow|];
  now rewrite (ProductOfArrowsPr2 C _ (PC a x)), (ProductOfArrowsPr1 C _ (PC a x))).
Defined.

Definition nat_trans_constprod_functor2 (a : C) :
  nat_trans (constprod_functor2 a) (constprod_functor1 a).
Proof.
mkpair.
- intro x; simpl; unfold product_functor_ob; simpl.
  apply ProductArrow; [ apply ProductPr2 | apply ProductPr1 ].
- abstract (intros x y f; simpl; unfold product_functor_mor; simpl;
  eapply pathscomp0; [apply precompWithProductArrow|];
  apply pathsinv0; eapply pathscomp0; [apply postcompWithProductArrow|];
  now rewrite (ProductOfArrowsPr2 C _ (PC x a)), (ProductOfArrowsPr1 C _ (PC x a))).
Defined.

Lemma is_iso_constprod_functor1 a :
  @is_iso [C,C,hsC] _ _ (nat_trans_constprod_functor1 a).
Proof.
apply (@is_iso_qinv [C,C,hsC] _ _ _ (nat_trans_constprod_functor2 a)).
  split.
  + abstract (
    apply (nat_trans_eq hsC); intro x; simpl; unfold product_functor_ob; simpl;
    eapply pathscomp0; [apply precompWithProductArrow|];
    now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left).
  + abstract (
    apply (nat_trans_eq hsC); intro x; simpl; unfold product_functor_ob; simpl;
    eapply pathscomp0; [apply precompWithProductArrow|];
    now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left).
Defined.

(* This is not used *)
Lemma is_iso_constprod_functor2 a :
  @is_iso [C,C,hsC] _ _ (nat_trans_constprod_functor2 a).
Proof.
apply (@is_iso_qinv [C,C,hsC] _ _ _ (nat_trans_constprod_functor1 a)).
mkpair.
+ abstract (
  apply (nat_trans_eq hsC); intro x; simpl; unfold product_functor_ob; simpl;
  eapply pathscomp0; [apply precompWithProductArrow|];
  now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left).
+ abstract (
  apply (nat_trans_eq hsC); intro x; simpl; unfold product_functor_ob; simpl;
  eapply pathscomp0; [apply precompWithProductArrow|];
  now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left).
Defined.

Definition flip_iso a : @iso [C,C,hsC] (constprod_functor1 a) (constprod_functor2 a) :=
  tpair _ _ (is_iso_constprod_functor1 a).

Variable (a : C).
Variable (H : is_left_adjoint (constprod_functor1 a)).

Local Notation F := (constprod_functor1 a).
Local Notation F' := (constprod_functor2 a).
Let G := right_adjoint H.
Let eta : [C,C,hsC]⟦functor_identity C,functor_composite F G⟧ := unit_from_left_adjoint H.
Let eps : [C,C,hsC]⟦functor_composite G F,functor_identity C⟧ := counit_from_left_adjoint H.
Let H1 := triangle_id_left_ad _ _ _ H.
Let H2 := triangle_id_right_ad _ _ _ H.

Arguments constprod_functor1 : simpl never.
Arguments constprod_functor2 : simpl never.
Arguments flip_iso : simpl never.

Local Definition eta' : [C,C,hsC]⟦functor_identity C,functor_composite F' G⟧ :=
  let G' := (post_composition_functor C C C hsC hsC G)
  in eta ;; (# G' (flip_iso a)).

Local Definition eps' : [C,C,hsC]⟦functor_composite G F',functor_identity C⟧ :=
  let G' := (pre_composition_functor C C C hsC hsC G)
  in # G' (inv_from_iso (flip_iso a)) ;; eps.

Local Lemma form_adjunction_eta'_eps' : form_adjunction F' G eta' eps'.
Proof.
fold eta in H1; fold eps in H1; fold eta in H2; fold eps in H2; fold G in H2.
mkpair.
+ intro x; unfold eta', eps'; cbn.
  rewrite assoc.
  eapply pathscomp0; [eapply cancel_postcomposition; apply nat_trans_ax|].
  rewrite functor_comp, assoc.
  eapply pathscomp0; [rewrite <- assoc; apply maponpaths, (nat_trans_ax eps)|].
  rewrite <- assoc.
  eapply pathscomp0; [apply maponpaths; rewrite assoc; apply cancel_postcomposition, H1|].
  rewrite id_left.
  apply (nat_trans_eq_pointwise (iso_after_iso_inv (flip_iso a)) x).
+ intro x.
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
