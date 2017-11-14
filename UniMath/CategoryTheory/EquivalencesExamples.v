(**

This file contains some adjunctions:

- The binary delta_functor is left adjoint to binproduct_functor

- The general delta functor is left adjoint to the general product
  functor

- The bincoproduct_functor is left adjoint to the binary delta functor

- The general coproduct functor is left adjoint to the general delta
  functor

- Swapping of arguments in functor categories

Written by: Anders Mörtberg, 2016

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.

Local Open Scope cat.

Section bindelta_functor_adjunction.

Context {C : precategory} (PC : BinProducts C).

(** The binary delta_functor is left adjoint to binproduct_functor *)
Lemma is_left_adjoint_bindelta_functor : is_left_adjoint (bindelta_functor C).
Proof.
apply (tpair _ (binproduct_functor PC)).
use tpair.
- split.
  + use tpair.
    * simpl; intro x.
      apply (BinProductArrow _ _ (identity x) (identity x)).
    * abstract (intros p q f; simpl;
                now rewrite precompWithBinProductArrow, id_right, postcompWithBinProductArrow, id_left).
  + use tpair.
    * simpl; intro x; split; [ apply BinProductPr1 | apply BinProductPr2 ].
    * abstract (intros p q f; unfold precatbinprodmor, compose; simpl;
                now rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2).
- abstract (split; simpl; intro x;
  [ unfold precatbinprodmor, compose; simpl;
    now rewrite BinProductPr1Commutes, BinProductPr2Commutes
  | cbn; rewrite postcompWithBinProductArrow, !id_left;
    apply pathsinv0, BinProduct_endo_is_identity;
      [ apply BinProductPr1Commutes | apply BinProductPr2Commutes ]]).
Defined.

End bindelta_functor_adjunction.

Section delta_functor_adjunction.

Context (I : UU) {C : precategory} (PC : Products I C).

(** The general delta functor is left adjoint to the general product functor *)
Lemma is_left_adjoint_delta_functor :
  is_left_adjoint (delta_functor I C).
Proof.
apply (tpair _ (product_functor _ PC)).
use tpair.
- split.
  + use tpair.
    * simpl; intro x.
      apply (ProductArrow _ _ _ (λ _, identity x)).
    * abstract (intros p q f; simpl;
                now rewrite precompWithProductArrow, id_right,
                            postcompWithProductArrow, id_left).
  + use tpair.
    * intros x i; apply ProductPr.
    * abstract (intros p q f; apply funextsec; intro i; unfold compose; simpl;
                now rewrite ProductOfArrowsPr).
- abstract (split; simpl; intro x;
    [ apply funextsec; intro i; apply (ProductPrCommutes _ _ (λ _, x))
    | cbn; rewrite postcompWithProductArrow;
      apply pathsinv0, Product_endo_is_identity; intro i;
      eapply pathscomp0; [|apply (ProductPrCommutes I C _ (PC x))];
      apply cancel_postcomposition, maponpaths, funextsec; intro j; apply id_left]).
Defined.

End delta_functor_adjunction.

Section bincoproduct_functor_adjunction.

Context {C : precategory} (PC : BinCoproducts C).

(** The bincoproduct_functor left adjoint to delta_functor *)
Lemma is_left_adjoint_bincoproduct_functor : is_left_adjoint (bincoproduct_functor PC).
Proof.
apply (tpair _ (bindelta_functor _)).
use tpair.
- split.
  + use tpair.
    * simpl; intro p; set (x := pr1 p); set (y := pr2 p).
      split; [ apply (BinCoproductIn1 _ (PC x y)) | apply (BinCoproductIn2 _ (PC x y)) ].
    * abstract (intros p q f; unfold precatbinprodmor, compose; simpl;
                now rewrite BinCoproductOfArrowsIn1, BinCoproductOfArrowsIn2).
  + use tpair.
    * intro x; apply (BinCoproductArrow _ _ (identity x) (identity x)).
    * abstract (intros p q f; simpl;
                now rewrite precompWithBinCoproductArrow, postcompWithBinCoproductArrow,
                            id_right, id_left).
- abstract (split; simpl; intro x;
  [ cbn; rewrite precompWithBinCoproductArrow, !id_right;
    apply pathsinv0, BinCoproduct_endo_is_identity;
      [ apply BinCoproductIn1Commutes | apply BinCoproductIn2Commutes ]
  | unfold precatbinprodmor, compose; simpl;
    now rewrite BinCoproductIn1Commutes, BinCoproductIn2Commutes ]).
Defined.

End bincoproduct_functor_adjunction.

Section coproduct_functor_adjunction.

Context (I : UU) {C : precategory} (PC : Coproducts I C).

(** The general coproduct functor left adjoint to the general delta functor *)
Lemma is_left_adjoint_coproduct_functor :
  is_left_adjoint (coproduct_functor I PC).
Proof.
apply (tpair _ (delta_functor _ _)).
use tpair.
- split.
  + use tpair.
    * intros p i; apply CoproductIn.
    * abstract (intros p q f; apply funextsec; intro i; unfold compose; simpl;
                now rewrite CoproductOfArrowsIn).
  + use tpair.
    * intro x; apply (CoproductArrow _ _ _ (λ _, identity x)).
    * abstract (intros p q f; simpl;
                now rewrite precompWithCoproductArrow,
                            postcompWithCoproductArrow,
                            id_right, id_left).
- abstract (split; simpl; intro x;
    [ cbn; rewrite precompWithCoproductArrow;
      apply pathsinv0, Coproduct_endo_is_identity; intro i;
      eapply pathscomp0; [|apply CoproductInCommutes];
      apply maponpaths, maponpaths, funextsec; intro j; apply id_right
    | apply funextsec; intro i; apply (CoproductInCommutes _ _ (λ _, x))]).
Defined.

End coproduct_functor_adjunction.

(** * Swapping of arguments in functor categories *)
Section functor_swap.

Local Notation "[ C , D ]" := (functor_category C D).

Lemma functor_swap {C D : precategory} {E : category} : functor C [D,E] → functor D [C,E].
Proof.
intros F.
use tpair.
- use tpair.
  + intro d; simpl.
  { use tpair.
    - use tpair.
      + intro c.
        apply (pr1 (F c) d).
      + intros a b f; apply (# F f).
    - abstract (split;
      [ now intro x; simpl; rewrite (functor_id F)
      | now intros a b c f g; simpl; rewrite (functor_comp F)]).
  }
  + intros a b f; simpl.
  { use tpair.
    - intros x; apply (# (pr1 (F x)) f).
    - abstract (intros c d g; simpl; apply pathsinv0, nat_trans_ax).
  }
- abstract (split;
  [ intros d; apply (nat_trans_eq (homset_property E)); intro c; simpl; apply functor_id
  | intros a b c f g; apply (nat_trans_eq (homset_property E)); intro x; simpl; apply functor_comp]).
Defined.

Lemma functor_cat_swap_nat_trans {C D : precategory} {E : category}
  (F G : functor C [D, E]) (α : nat_trans F G) :
  nat_trans (functor_swap F) (functor_swap G).
Proof.
use tpair.
+ intros d; simpl.
  use tpair.
  * intro c; apply (α c).
  * abstract (intros a b f; apply (nat_trans_eq_pointwise (nat_trans_ax α _ _ f) d)).
+ abstract (intros a b f; apply (nat_trans_eq (homset_property E)); intro c; simpl; apply nat_trans_ax).
Defined.

Lemma functor_cat_swap (C D : precategory) (E : category) : functor [C, [D, E]] [D, [C, E]].
Proof.
use tpair.
- use tpair.
  + apply functor_swap.
  + cbn. apply functor_cat_swap_nat_trans.
- abstract (split;
  [ intro F; apply (nat_trans_eq (functor_category_has_homsets _ _ (homset_property E))); simpl; intro d;
    now apply (nat_trans_eq (homset_property E))
  | intros F G H α β; cbn; apply (nat_trans_eq (functor_category_has_homsets _ _ (homset_property E))); intro d;
    now apply (nat_trans_eq (homset_property E))]).
Defined.

Definition id_functor_cat_swap (C D : precategory) (E : category) :
  nat_trans (functor_identity [C,[D,E]])
            (functor_composite (functor_cat_swap C D E) (functor_cat_swap D C E)).
Proof.
set (hsE := homset_property E).
use tpair.
+ intros F.
  use tpair.
  - intro c.
     use tpair.
     * now intro f; apply identity.
     * abstract (now intros a b f; rewrite id_left, id_right).
  - abstract (now intros a b f; apply (nat_trans_eq hsE); intro d; simpl; rewrite id_left, id_right).
+ abstract (now intros a b f; apply nat_trans_eq; [apply functor_category_has_homsets|]; intro c;
            apply (nat_trans_eq hsE); intro d; simpl; rewrite id_left, id_right).
Defined.

Definition functor_cat_swap_id (C D : precategory) (E : category) :
  nat_trans (functor_composite (functor_cat_swap D C E) (functor_cat_swap C D E))
            (functor_identity [D,[C,E]]).
Proof.
set (hsE := homset_property E).
use tpair.
+ intros F.
  use tpair.
  - intro c.
    use tpair.
    * now intro f; apply identity.
    * abstract (now intros a b f; rewrite id_left, id_right).
  - abstract (now intros a b f; apply (nat_trans_eq hsE); intro d; simpl; rewrite id_left, id_right).
+ abstract (now intros a b f; apply nat_trans_eq; [apply functor_category_has_homsets|]; intro c;
            apply (nat_trans_eq hsE); intro d; simpl; rewrite id_left, id_right).
Defined.

Lemma form_adjunction_functor_cat_swap (C D : precategory) (E : category) :
  form_adjunction _ _ (id_functor_cat_swap C D E) (functor_cat_swap_id C D E).
Proof.
set (hsE := homset_property E).
split; intro F.
+ apply (nat_trans_eq (functor_category_has_homsets _ _ hsE)
                      (pr1 (pr1 (functor_cat_swap C D E) F))
                      (pr1 (pr1 (functor_cat_swap C D E) F))).
  now intro d; apply (nat_trans_eq hsE); intro c; apply id_right.
+ apply (nat_trans_eq (functor_category_has_homsets _ _ hsE)
                      (pr1 (pr1 (functor_cat_swap D C E) F))
                      (pr1 (pr1 (functor_cat_swap D C E) F))).
  now intro d; apply (nat_trans_eq hsE); intro c; apply id_left.
Qed. (* This Qed is very slow... I don't see how to make it faster *)

Lemma are_adjoint_functor_cat_swap (C D : precategory) (E : category) :
  are_adjoints (@functor_cat_swap C D E) (@functor_cat_swap D C E).
Proof.
use tpair.
- split; [ apply id_functor_cat_swap | apply functor_cat_swap_id ].
- apply form_adjunction_functor_cat_swap.
Defined.

Lemma is_left_adjoint_functor_cat_swap (C D : precategory) (E : category) :
  is_left_adjoint (functor_cat_swap C D E).
Proof.
use tpair.
+ apply functor_cat_swap.
+ apply are_adjoint_functor_cat_swap.
Defined.

End functor_swap.
