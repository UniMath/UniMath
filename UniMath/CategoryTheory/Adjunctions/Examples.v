(**************************************************************************************************

  Examples of Adjunctions

  The binary delta functor C → C × C is a left (right) adjoint to the binary (co)product functor
  C × C → C, and the general delta functor C → C^I is a left (right) adjoint to the general
  (co)product functor C^I → C.
  The swapping functor [C, [D, E]] → [D, [C, E]] is a left adjoint to itself.
  Lastly, the constant functor that sends everything to the initial object is a left adjoint to the
  functor that sends everything to the terminal object.

  Contents
  1. Adjunctions between delta functors and (co)product functors
  1.1. The adjunction between the binary delta and product functor
    [is_left_adjoint_bindelta_functor]
  1.2. The adjunction between the general delta and product functor
    [is_left_adjoint_delta_functor]
  1.3. The adjunction between the binary coproduct and delta functor
    [is_left_adjoint_bincoproduct_functor]
  1.4. The adjunction between the general coproduct and delta functor
    [is_left_adjoint_coproduct_functor]
  2. Swapping of arguments in functor categories [are_adjoint_functor_cat_swap]
  3. Adjunctions are closed under natural isomorphism [is_left_adjoint_nat_z_iso]
  4. The adjunction between the constant initial and terminal functors
    [initial_terminal_are_adjoints]

  Started by: Anders Mörtberg, 2016

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(** ** 1. Adjunctions between delta functors and (co)product functors *)
Section DeltaProductAdjunctions.

  Context {C : category}.

(** ** 1.1. The adjunction between the binary delta and product functor *)
  Lemma is_left_adjoint_bindelta_functor
    (PC : BinProducts C)
    : is_left_adjoint (bindelta_functor C).
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
      * abstract (intros p q f; unfold catbinprodmor, compose; simpl;
                  now rewrite BinProductOfArrowsPr1, BinProductOfArrowsPr2).
  - abstract (split; simpl; intro x;
    [ unfold catbinprodmor, compose; simpl;
      now rewrite BinProductPr1Commutes, BinProductPr2Commutes
    | cbn; rewrite postcompWithBinProductArrow, !id_left;
      apply pathsinv0, BinProduct_endo_is_identity;
        [ apply BinProductPr1Commutes | apply BinProductPr2Commutes ]]).
  Defined.

(** ** 1.2. The adjunction between the general delta and product functor *)
  Lemma is_left_adjoint_delta_functor
    (I : UU)
    (PC : Products I C)
    : is_left_adjoint (delta_functor I C).
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

(** ** 1.3. The adjunction between the binary coproduct and delta functor *)
  Lemma is_left_adjoint_bincoproduct_functor
    (PC : BinCoproducts C)
    : is_left_adjoint (bincoproduct_functor PC).
  Proof.
  apply (tpair _ (bindelta_functor _)).
  use tpair.
  - split.
    + use tpair.
      * simpl; intro p; set (x := pr1 p); set (y := pr2 p).
        split; [ apply (BinCoproductIn1 (PC x y)) | apply (BinCoproductIn2 (PC x y)) ].
      * abstract (intros p q f; unfold catbinprodmor, compose; simpl;
                  now rewrite BinCoproductOfArrowsIn1, BinCoproductOfArrowsIn2).
    + use tpair.
      * intro x; apply (BinCoproductArrow _ (identity x) (identity x)).
      * abstract (intros p q f; simpl;
                  now rewrite precompWithBinCoproductArrow, postcompWithBinCoproductArrow,
                              id_right, id_left).
  - abstract (split; simpl; intro x;
    [ cbn; rewrite precompWithBinCoproductArrow, !id_right;
      apply pathsinv0, BinCoproduct_endo_is_identity;
        [ apply BinCoproductIn1Commutes | apply BinCoproductIn2Commutes ]
    | unfold catbinprodmor, compose; simpl;
      now rewrite BinCoproductIn1Commutes, BinCoproductIn2Commutes ]).
  Defined.

(** ** 1.4. The adjunction between the general coproduct and delta functor *)
  Lemma is_left_adjoint_coproduct_functor
    (I : UU)
    (PC : Coproducts I C)
    : is_left_adjoint (coproduct_functor I PC).
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

End DeltaProductAdjunctions.

(** ** 2. Swapping of arguments in functor categories *)
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

(** ** 3. Adjunctions are closed under natural isomorphism *)
Section LeftAdjointIso.
  Context {C D : category}
          {L₁ L₂ : C ⟶ D}
          (HL₁ : is_left_adjoint L₁)
          (τ : nat_z_iso L₁ L₂).

  Let R : D ⟶ C := right_adjoint HL₁.
  Let η : functor_identity C ⟹ L₁ ∙ R := unit_from_left_adjoint HL₁.
  Let ε : R ∙ L₁ ⟹ functor_identity _ := counit_from_left_adjoint HL₁.

  Let η' : functor_identity C ⟹ L₂ ∙ R
    := nat_trans_comp
         _ _ _
         η
         (post_whisker τ R).

  Let ε' : R ∙ L₂ ⟹ functor_identity D
    := nat_trans_comp
         _ _ _
         (pre_whisker R (nat_z_iso_inv τ))
         ε.

  Proposition is_left_adjoint_nat_z_iso_triangle_1
    : triangle_1_statement (L₂ ,, R ,, η' ,, ε').
  Proof.
    intros x ; cbn -[η ε].
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      exact (nat_trans_ax (nat_z_iso_inv τ) _ _ (η x · #R(τ x))).
    }
    rewrite functor_comp.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply (nat_trans_ax ε).
    }
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply (pr122 HL₁).
    }
    rewrite id_left.
    exact (z_iso_after_z_iso_inv (nat_z_iso_pointwise_z_iso τ x)).
  Qed.

  Proposition is_left_adjoint_nat_z_iso_triangle_2
    : triangle_2_statement (L₂ ,, R ,, η' ,, ε').
  Proof.
    intros x ; cbn.
    rewrite !assoc'.
    rewrite <- functor_comp.
    rewrite assoc.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      exact (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso τ (R x))).
    }
    rewrite id_left.
    apply (pr222 HL₁).
  Qed.

  Definition is_left_adjoint_nat_z_iso
    : is_left_adjoint L₂.
  Proof.
    simple refine (R ,, (η' ,, ε') ,, (_ ,, _)).
    - exact is_left_adjoint_nat_z_iso_triangle_1.
    - exact is_left_adjoint_nat_z_iso_triangle_2.
  Defined.
End LeftAdjointIso.

(** ** 4. The adjunction between the constant initial and terminal functors *)
Section InitialTerminal.

  Context {C C' : category}.
  Context (I : Initial C').
  Context (T : Terminal C).

  Definition initial_terminal_are_adjoints
    : are_adjoints (Initial_functor_precat C C' I : [_, _]) (Terminal_functor_precat C' C T : [_, _]).
  Proof.
    apply adjunction_homsetiso_weq.
    use tpair.
    - intros A B.
      use weq_iso.
      + intro.
        apply TerminalArrow.
      + intro.
        apply InitialArrow.
      + abstract (
          intro;
          apply InitialArrowEq
        ).
      + abstract (
          intro;
          apply TerminalArrowEq
        ).
    - abstract (
        split;
        intros;
        apply TerminalArrowEq
      ).
  Defined.

  Definition initial_terminal_adjunction
    : adjunction C C'
    := left_adjoint_to_adjunction initial_terminal_are_adjoints.

End InitialTerminal.
