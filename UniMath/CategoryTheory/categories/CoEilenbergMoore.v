(******************************************************************************

 The Eilenberg-Moore category dualized (after the file [EilenbergMoore.v])

 We define Eilenberg-Moore categories of comonads.

 The construction in this file uses dialgebras and full
 subcategories which makes it easy to prove univalence.

 Contents
 1. The definition
 2. The univalence
 3. Constructors and projections
 4. The universal property
 4.1 The cone
 4.2 The universal property for functors
 4.3 The universal property for natural transformations

 ******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.Monads.Comonads.

Local Open Scope cat.

Section CoEilenbergMooreCategory.
  Context {C : category}
          (m : Comonad C).

  (**
   1. The definition
   *)
  Definition co_eilenberg_moore_cat_pred
             (f : dialgebra (functor_identity C) m)
    : hProp.
  Proof.
    use make_hProp.
    - exact (pr2 f · ε m _  = identity _
             ×
             pr2 f · δ m (pr1 f) = pr2 f · # m (pr2 f)).
    - apply isapropdirprod ; apply homset_property.
  Defined.

  Definition co_eilenberg_moore_cat
    : category
    := full_sub_category
         (dialgebra (functor_identity _) m)
         co_eilenberg_moore_cat_pred.

  (**
   2. The univalence
   *)
  Definition is_univalent_co_eilenberg_moore_cat
             (HC : is_univalent C)
    : is_univalent co_eilenberg_moore_cat.
  Proof.
    apply is_univalent_full_sub_category.
    apply is_univalent_dialgebra.
    exact HC.
  Defined.

  (**
   3. Constructors and projections
   *)
  Definition make_ob_co_eilenberg_moore
             (x : C)
             (f : x --> m x)
             (p : f · ε m x = identity x)
             (q : f · δ m x = f · # m f)
    : co_eilenberg_moore_cat
    := (x ,, _) ,, (p ,, q).

  Definition make_mor_co_eilenberg_moore
             {x y : co_eilenberg_moore_cat}
             (f : pr11 x --> pr11 y)
             (p : pr21 x · # m f = f · pr21 y)
    : x --> y
    := (f ,, p) ,, tt.

  Definition eq_mor_co_eilenberg_moore
             {x y : co_eilenberg_moore_cat}
             (f g : x --> y)
             (p : pr11 f = pr11 g)
    : f = g.
  Proof.
    use subtypePath.
    {
      intro ; apply isapropunit.
    }
    use subtypePath.
    {
      intro ; apply homset_property.
    }
    exact p.
  Qed.

  Definition is_z_iso_co_eilenberg_moore
             {x y : co_eilenberg_moore_cat}
             (f : x --> y)
             (Hf : is_z_isomorphism (pr11 f))
    : is_z_isomorphism f.
  Proof.
    pose (H := make_z_iso _ _ Hf).
    use make_is_z_isomorphism.
    - use make_mor_co_eilenberg_moore.
      + exact (inv_from_z_iso H).
      + apply (is_z_iso_disp_dialgebra _ _ Hf (pr21 f)).
     - split.
      + abstract
          (use eq_mor_co_eilenberg_moore ; cbn ;
           apply (z_iso_inv_after_z_iso H)).
      + abstract
          (use eq_mor_co_eilenberg_moore ; cbn ;
           apply (z_iso_after_z_iso_inv H)).
  Defined.
End CoEilenbergMooreCategory.

Definition co_eilenberg_moore_univalent_cat
           (C : univalent_category)
           (m : Comonad C)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (co_eilenberg_moore_cat m).
  - exact (is_univalent_co_eilenberg_moore_cat m (pr2 C)).
Defined.

Definition ob_of_co_eilenberg_moore_ob
           {C : category}
           {m : Comonad C}
           (h : co_eilenberg_moore_cat m)
  : C
  := pr11 h.

Definition mor_of_co_eilenberg_moore_ob
           {C : category}
           {m : Comonad C}
           (h : co_eilenberg_moore_cat m)
  : ob_of_co_eilenberg_moore_ob h --> m (ob_of_co_eilenberg_moore_ob h)
  := pr21 h.

Definition co_eilenberg_moore_ob_unit
           {C : category}
           {m : Comonad C}
           (h : co_eilenberg_moore_cat m)
  : mor_of_co_eilenberg_moore_ob h · ε m (ob_of_co_eilenberg_moore_ob h)
    =
    identity _
  := pr12 h.

Definition co_eilenberg_moore_ob_mult
           {C : category}
           {m : Comonad C}
           (h : co_eilenberg_moore_cat m)
  : mor_of_co_eilenberg_moore_ob h · δ m _
    =
    mor_of_co_eilenberg_moore_ob h · # m (mor_of_co_eilenberg_moore_ob h)
  := pr22 h.

Definition mor_of_co_eilenberg_moore_mor
           {C : category}
           {m : Comonad C}
           {x y : co_eilenberg_moore_cat m}
           (f : x --> y)
    : ob_of_co_eilenberg_moore_ob x --> ob_of_co_eilenberg_moore_ob y
    := pr11 f.

Definition eq_of_co_eilenberg_moore_mor
           {C : category}
           {m : Comonad C}
           {x y : co_eilenberg_moore_cat m}
           (f : x --> y)
  : mor_of_co_eilenberg_moore_ob x · # m (pr11 f)
    =
    pr11 f · mor_of_co_eilenberg_moore_ob y
  := pr21 f.

(**
 4. The universal property
 *)

(**
 4.1 The cone
 *)
Definition co_eilenberg_moore_pr
           {C : category}
           (m : Comonad C)
  : co_eilenberg_moore_cat m ⟶ C.
Proof.
  refine (functor_composite _ _).
  - apply full_sub_category_pr.
  - apply dialgebra_pr1.
Defined.

Definition co_eilenberg_moore_nat_trans
           {C : category}
           (m : Comonad C)
  : functor_identity _ ∙ co_eilenberg_moore_pr m
    ⟹
    co_eilenberg_moore_pr m ∙ m.
Proof.
  use make_nat_trans.
  - exact (λ f, mor_of_co_eilenberg_moore_ob f).
  - abstract
      (intros f₁ f₂ α ; cbn ;
       exact (!(eq_of_co_eilenberg_moore_mor α))).
Defined.

(**
 4.2 The universal property for functors
 *)
Section CoEilenbergMooreUMP1.
  Context {C₁ C₂ : category}
          (m : Comonad C₂)
          (F : C₁ ⟶ C₂)
          (α : functor_identity _ ∙ F ⟹ F ∙ m)
          (αε : ∏ (x : C₁), α x · ε m (F x) = identity _)
          (αδ : ∏ (x : C₁), α x · # m (α x) = α x · δ m (F x)).

  Definition functor_to_co_eilenberg_moore_cat_data
    : functor_data C₁ (co_eilenberg_moore_cat m).
  Proof.
    use make_functor_data.
    - intro x.
      use make_ob_co_eilenberg_moore.
      + exact (F x).
      + exact (α x).
      + exact (αε x).
      + exact (!(αδ x)).
    - intros x y f.
      use make_mor_co_eilenberg_moore.
      + exact (#F f).
      + exact (!(nat_trans_ax α _ _ f)).
  Defined.

  Definition functor_to_co_eilenberg_moore_is_functor
    : is_functor functor_to_co_eilenberg_moore_cat_data.
  Proof.
    split.
    - intro x.
      use eq_mor_co_eilenberg_moore ; cbn.
      apply functor_id.
    - intros x y z f g.
      use eq_mor_co_eilenberg_moore ; cbn.
      apply functor_comp.
  Qed.

  Definition functor_to_co_eilenberg_moore_cat
    : C₁ ⟶ co_eilenberg_moore_cat m.
  Proof.
    use make_functor.
    - exact functor_to_co_eilenberg_moore_cat_data.
    - exact functor_to_co_eilenberg_moore_is_functor.
  Defined.

  Definition functor_to_co_eilenberg_moore_cat_pr
    : functor_to_co_eilenberg_moore_cat ∙ co_eilenberg_moore_pr m ⟹ F.
  Proof.
    use make_nat_trans.
    - exact (λ _, identity _).
    - abstract
        (intros x y f ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition functor_to_co_eilenberg_moore_cat_pr_is_nat_z_iso
    : is_nat_z_iso functor_to_co_eilenberg_moore_cat_pr.
  Proof.
    intro.
    apply identity_is_z_iso.
  Defined.

  Definition functor_to_co_eilenberg_moore_cat_pr_nat_z_iso
    : nat_z_iso
        (functor_to_co_eilenberg_moore_cat ∙ co_eilenberg_moore_pr m)
        F.
  Proof.
    use make_nat_z_iso.
    - exact functor_to_co_eilenberg_moore_cat_pr.
    - exact functor_to_co_eilenberg_moore_cat_pr_is_nat_z_iso.
  Defined.
End CoEilenbergMooreUMP1.

(**
 4.3 The universal property for natural transformations
 *)
Definition nat_trans_to_co_eilenberg_moore_cat
           {C₁ C₂ : category}
           (m : Comonad C₂)
           (F₁ F₂ : C₁ ⟶ co_eilenberg_moore_cat m)
           (α : F₁ ∙ co_eilenberg_moore_pr m ⟹ F₂ ∙ co_eilenberg_moore_pr m)
           (p : ∏ (x : C₁),
               mor_of_co_eilenberg_moore_ob (F₁ x) · # m (α x)
               =
               α x · mor_of_co_eilenberg_moore_ob (F₂ x))
  : F₁ ⟹ F₂.
Proof.
  use make_nat_trans.
  - intro x.
    use make_mor_co_eilenberg_moore.
    + exact (α x).
    + exact (p x).
  - abstract
      (intros x y f ;
       use eq_mor_co_eilenberg_moore ; cbn ;
       exact (nat_trans_ax α _ _ f)).
Defined.
