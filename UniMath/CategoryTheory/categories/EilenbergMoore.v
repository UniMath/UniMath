(******************************************************************************

 The Eilenberg-Moore category

 We define Eilenberg-Moore categories of monads.

 Note: a direct definition is given in Monads/MonadAlgebras.v.
 The construction in this file reuses other notions (dialgebras and full
 subcategories) and that makes it easier to prove univalence.

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
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Section EilenbergMooreCategory.
  Context {C : category}
          (m : Monad C).

  (**
   1. The definition
   *)
  Definition eilenberg_moore_cat_pred
             (f : dialgebra m (functor_identity C))
    : hProp.
  Proof.
    use make_hProp.
    - exact (η m _ · pr2 f = identity _
             ×
             μ m (pr1 f)  · pr2 f = # m (pr2 f) · pr2 f).
    - apply isapropdirprod ; apply homset_property.
  Defined.

  Definition eilenberg_moore_cat
    : category
    := full_sub_category
         (dialgebra m (functor_identity _))
         eilenberg_moore_cat_pred.

  (**
   2. The univalence
   *)
  Definition is_univalent_eilenberg_moore_cat
             (HC : is_univalent C)
    : is_univalent eilenberg_moore_cat.
  Proof.
    apply is_univalent_full_subcat.
    apply is_univalent_dialgebra.
    exact HC.
  Defined.

  (**
   3. Constructors and projections
   *)
  Definition make_ob_eilenberg_moore
             (x : C)
             (f : m x --> x)
             (p : η m x · f = identity x)
             (q : μ m x · f = # m f · f)
    : eilenberg_moore_cat
    := (x ,, _) ,, (p ,, q).

  Definition make_mor_eilenberg_moore
             {x y : eilenberg_moore_cat}
             (f : pr11 x --> pr11 y)
             (p : pr21 x · f = # m f · pr21 y)
    : x --> y
    := (f ,, p) ,, tt.

  Definition eq_mor_eilenberg_moore
             {x y : eilenberg_moore_cat}
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

  Definition is_z_iso_eilenberg_moore
             {x y : eilenberg_moore_cat}
             (f : x --> y)
             (Hf : is_z_isomorphism (pr11 f))
    : is_z_isomorphism f.
  Proof.
    pose (H := make_z_iso _ _ Hf).
    use make_is_z_isomorphism.
    - use make_mor_eilenberg_moore.
      + exact (inv_from_z_iso H).
      + abstract
          (refine (!_) ;
           use z_iso_inv_on_left ;
           rewrite !assoc' ;
           rewrite functor_on_inv_from_z_iso ;
           refine (!_) ;
           use z_iso_inv_on_right ;
           exact (pr21 f)).
    - split.
      + abstract
          (use eq_mor_eilenberg_moore ; cbn ;
           apply (z_iso_inv_after_z_iso H)).
      + abstract
          (use eq_mor_eilenberg_moore ; cbn ;
           apply (z_iso_after_z_iso_inv H)).
  Defined.
End EilenbergMooreCategory.

Definition eilenberg_moore_univalent_cat
           (C : univalent_category)
           (m : Monad C)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (eilenberg_moore_cat m).
  - exact (is_univalent_eilenberg_moore_cat m (pr2 C)).
Defined.

Definition ob_of_eilenberg_moore_ob
           {C : category}
           {m : Monad C}
           (h : eilenberg_moore_cat m)
  : C
  := pr11 h.

Definition mor_of_eilenberg_moore_ob
           {C : category}
           {m : Monad C}
           (h : eilenberg_moore_cat m)
  : m (ob_of_eilenberg_moore_ob h) --> ob_of_eilenberg_moore_ob h
  := pr21 h.

Definition eilenberg_moore_ob_unit
           {C : category}
           {m : Monad C}
           (h : eilenberg_moore_cat m)
  : η m (ob_of_eilenberg_moore_ob h) · mor_of_eilenberg_moore_ob h
    =
    identity _
  := pr12 h.

Definition eilenberg_moore_ob_mult
           {C : category}
           {m : Monad C}
           (h : eilenberg_moore_cat m)
  : μ m _ · mor_of_eilenberg_moore_ob h
    =
    # m (mor_of_eilenberg_moore_ob h) · mor_of_eilenberg_moore_ob h
  := pr22 h.

Definition mor_of_eilenberg_moore_mor
           {C : category}
           {m : Monad C}
           {x y : eilenberg_moore_cat m}
           (f : x --> y)
    : ob_of_eilenberg_moore_ob x --> ob_of_eilenberg_moore_ob y
    := pr11 f.

Definition eq_of_eilenberg_moore_mor
           {C : category}
           {m : Monad C}
           {x y : eilenberg_moore_cat m}
           (f : x --> y)
  : mor_of_eilenberg_moore_ob x · pr11 f
    =
    # m (pr11 f) · mor_of_eilenberg_moore_ob y
  := pr21 f.

(**
 4. The universal property
 *)

(**
 4.1 The cone
 *)
Definition eilenberg_moore_pr_data
           {C : category}
           (m : Monad C)
  : functor_data (eilenberg_moore_cat m) C.
Proof.
  use make_functor_data.
  - exact (λ h, ob_of_eilenberg_moore_ob h).
  - exact (λ h₁ h₂ α, mor_of_eilenberg_moore_mor α).
Defined.

Definition eilenberg_moore_pr_is_functor
           {C : category}
           (m : Monad C)
  : is_functor (eilenberg_moore_pr_data m).
Proof.
  split.
  - intro x ; cbn.
    apply idpath.
  - intros x y z f g ; cbn.
    apply idpath.
Qed.

Definition eilenberg_moore_pr
           {C : category}
           (m : Monad C)
  : eilenberg_moore_cat m ⟶ C.
Proof.
  use make_functor.
  - exact (eilenberg_moore_pr_data m).
  - exact (eilenberg_moore_pr_is_functor m).
Defined.

Definition eilenberg_moore_nat_trans
           {C : category}
           (m : Monad C)
  : eilenberg_moore_pr m ∙ m
    ⟹
    functor_identity _ ∙ eilenberg_moore_pr m.
Proof.
  use make_nat_trans.
  - exact (λ f, mor_of_eilenberg_moore_ob f).
  - abstract
      (intros f₁ f₂ α ; cbn ;
       exact (!(eq_of_eilenberg_moore_mor α))).
Defined.

(**
 4.2 The universal property for functors
 *)
Section EilenbergMooreUMP1.
  Context {C₁ C₂ : category}
          (m : Monad C₂)
          (F : C₁ ⟶ C₂)
          (α : F ∙ m ⟹ functor_identity _ ∙ F)
          (αη : ∏ (x : C₁), η m (F x) · α x = identity _)
          (αμ : ∏ (x : C₁), # m (α x) · α x = μ m (F x) · α x).

  Definition functor_to_eilenberg_moore_cat_data
    : functor_data C₁ (eilenberg_moore_cat m).
  Proof.
    use make_functor_data.
    - intro x.
      use make_ob_eilenberg_moore.
      + exact (F x).
      + exact (α x).
      + exact (αη x).
      + exact (!(αμ x)).
    - intros x y f.
      use make_mor_eilenberg_moore.
      + exact (#F f).
      + exact (!(nat_trans_ax α _ _ f)).
  Defined.

  Definition functor_to_eilenberg_moore_is_functor
    : is_functor functor_to_eilenberg_moore_cat_data.
  Proof.
    split.
    - intro x.
      use eq_mor_eilenberg_moore ; cbn.
      apply functor_id.
    - intros x y z f g.
      use eq_mor_eilenberg_moore ; cbn.
      apply functor_comp.
  Qed.

  Definition functor_to_eilenberg_moore_cat
    : C₁ ⟶ eilenberg_moore_cat m.
  Proof.
    use make_functor.
    - exact functor_to_eilenberg_moore_cat_data.
    - exact functor_to_eilenberg_moore_is_functor.
  Defined.

  Definition functor_to_eilenberg_moore_cat_pr
    : functor_to_eilenberg_moore_cat ∙ eilenberg_moore_pr m ⟹ F.
  Proof.
    use make_nat_trans.
    - exact (λ _, identity _).
    - abstract
        (intros x y f ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition functor_to_eilenberg_moore_cat_pr_is_nat_z_iso
    : is_nat_z_iso functor_to_eilenberg_moore_cat_pr.
  Proof.
    intro.
    apply identity_is_z_iso.
  Defined.
End EilenbergMooreUMP1.

(**
 4.3 The universal property for natural transformations
 *)
Definition nat_trans_to_eilenberg_moore_cat
           {C₁ C₂ : category}
           (m : Monad C₂)
           (F₁ F₂ : C₁ ⟶ eilenberg_moore_cat m)
           (α : F₁ ∙ eilenberg_moore_pr m ⟹ F₂ ∙ eilenberg_moore_pr m)
           (p : ∏ (x : C₁),
               mor_of_eilenberg_moore_ob (F₁ x) · α x
               =
               # m (α x) · mor_of_eilenberg_moore_ob (F₂ x))
  : F₁ ⟹ F₂.
Proof.
  use make_nat_trans.
  - intro x.
    use make_mor_eilenberg_moore.
    + exact (α x).
    + exact (p x).
  - abstract
      (intros x y f ;
       use eq_mor_eilenberg_moore ; cbn ;
       exact (nat_trans_ax α _ _ f)).
Defined.
