Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
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

(* Arguments nat_trans_constprod_functor1 : simpl never. *)
(* Arguments nat_trans_constprod_functor2 : simpl never. *)
(* Arguments constprod_functor1 : simpl never. *)
(* Arguments constprod_functor2 : simpl never. *)

Lemma is_iso_constprod_functor1 a : @is_iso  [C,C,hsC] _ _ (nat_trans_constprod_functor1 a).
Proof.
apply (@is_iso_qinv [C,C,hsC] _ _ _ (nat_trans_constprod_functor2 a)).
  split.
  + apply (nat_trans_eq hsC).
    intro x; simpl; unfold product_functor_ob; simpl.
    eapply pathscomp0; [apply precompWithProductArrow|].
    now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left.
  + apply (nat_trans_eq hsC).
    intro x; simpl; unfold product_functor_ob; simpl.
    eapply pathscomp0; [apply precompWithProductArrow|].
    now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left.
Defined.

Lemma is_iso_constprod_functor2 a : @is_iso  [C,C,hsC] _ _ (nat_trans_constprod_functor2 a).
Proof.
apply (@is_iso_qinv [C,C,hsC] _ _ _ (nat_trans_constprod_functor1 a)).
  split.
  + apply (nat_trans_eq hsC).
    intro x; simpl; unfold product_functor_ob; simpl.
    eapply pathscomp0; [apply precompWithProductArrow|].
    now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left.
  + apply (nat_trans_eq hsC).
    intro x; simpl; unfold product_functor_ob; simpl.
    eapply pathscomp0; [apply precompWithProductArrow|].
    now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left.
Defined.


Definition iso_constprod_functor a : @iso [C,C,hsC] (constprod_functor1 a) (constprod_functor2 a).
Proof.
mkpair.
- apply nat_trans_constprod_functor1.
- apply (@is_iso_qinv [C,C,hsC] _ _ _ (nat_trans_constprod_functor2 a)).
  split.
  + apply (nat_trans_eq hsC).
    intro x; simpl; unfold product_functor_ob; simpl.
    eapply pathscomp0; [apply precompWithProductArrow|].
    now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left.
  + apply (nat_trans_eq hsC).
    intro x; simpl; unfold product_functor_ob; simpl.
    eapply pathscomp0; [apply precompWithProductArrow|].
    now rewrite ProductPr1Commutes, ProductPr2Commutes, ProductArrowEta, !id_left.
Defined.

Lemma is_left_adjoint_constprod_functor2 (a : C) :
  is_left_adjoint (constprod_functor1 a) -> is_left_adjoint (constprod_functor2 a).
Proof.
intros H; destruct H as [G [[eta eps] [H1 H2]]].
simpl in *.
apply (tpair _ G).
mkpair.
- split.
  + set (G' := (post_composition_functor C C C hsC hsC G)).
Check (# G' (nat_trans_constprod_functor1 a)).
    (* exact (nat_trans_comp _ _ _ eta (# G' (iso_constprod_functor a))). *)
    exact (nat_trans_comp _ _ _ eta (# G' (nat_trans_constprod_functor1 a))).
  + set (G' := (pre_composition_functor C C C hsC hsC G)).
    (* exact (nat_trans_comp _ _ _ (# G' (inv_from_iso (iso_constprod_functor a))) eps). *)
    exact (nat_trans_comp _ _ _ (# G' (nat_trans_constprod_functor2 a)) eps).
- mkpair.
+ intro x.
simpl.
unfold product_functor_mor, product_functor_ob in *; simpl in *.
rewrite !assoc.
rewrite precompWithProductArrow.
rewrite ProductOfArrowsPr1.
rewrite ProductOfArrowsPr2.
admit.
+
intro x.
rewrite <- (H2 x).
rewrite <- assoc.
rewrite <- (functor_comp G).
apply maponpaths.
apply maponpaths.
rewrite assoc.
apply remove_id_left; try apply idpath.
eapply pathscomp0.
apply precompWithProductArrow.
rewrite ProductPr1Commutes.
rewrite ProductPr2Commutes.
now rewrite ProductArrowEta, !id_left.
Admitted.

Definition has_exponentials : UU :=
  forall (a : C), is_left_adjoint (constprod_functor1 a).

End exponentials.