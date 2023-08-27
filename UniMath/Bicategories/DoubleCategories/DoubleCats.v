(**********************************************************************************

 Double categories

 In this file, we provide an interface for the bicategory of double categories.
 More specifically, we give definitions and notations for accessors of double
 categories, double functors, and double transformations. We also give builders
 for each of them.

 Contents
 1. Double categories
 2. Accessors for double categories
 2.1. The vertical category
 2.2. Horizontal morphisms
 2.3. Squares
 2.4. Functoriality of horizontal identities
 2.5. Functoriality of horizontal composition
 2.6. Left unitor
 2.7. Right unitor
 2.8. Associator
 2.9. Triangle and pentagon equations
 3. Builder for double categories
 4. Lax functors for double categories
 5. Accessors for lax functors
 6. Builder for lax functors
 7. Double transformations
 8. Accessors for double transformations
 9. Builder for double transformations

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfTwoSidedDispCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.DoubleFunctor.
Require Import UniMath.Bicategories.DoubleCategories.DoubleTransformation.
Require Import UniMath.Bicategories.DoubleCategories.BicatOfDoubleCats.

Local Open Scope cat.

Declare Scope double_cat.

Local Open Scope double_cat.

(**
 1. Double categories
 *)
Definition double_cat
  : UU
  := ob bicat_of_double_cats.

(**
 2. Accessors for double categories
 *)

(**
 2.1. The vertical category
 *)
Definition ob_double_cat
           (C : double_cat)
  : category
  := pr11 (pr111 C).

Coercion ob_double_cat : double_cat >-> category.

Definition ver_mor_double_cat
           {C : double_cat}
           (x y : C)
  : UU
  := x --> y.

Notation "x -->v y" := (ver_mor_double_cat x y) (at level 55) : double_cat.

Definition identity_v
           {C : double_cat}
           (x : C)
  : x -->v x
  := identity _.

Definition ver_comp_double_cat
           {C : double_cat}
           {x y z : C}
           (f : x -->v y)
           (g : y -->v z)
  : x -->v z
  := f · g.

Notation "f ·v g" := (ver_comp_double_cat f g) (at level 60) : double_cat.

Proposition id_v_left
            {C : double_cat}
            {x y : C}
            (f : x -->v y)
  : identity_v x · f = f.
Proof.
  apply id_left.
Defined.

Proposition id_v_right
            {C : double_cat}
            {x y : C}
            (f : x -->v y)
  : f ·v identity_v y = f.
Proof.
  apply id_right.
Defined.

Proposition assocl_v
            {C : double_cat}
            {w x y z : C}
            (f : w -->v x)
            (g : x -->v y)
            (h : y -->v z)
  : f ·v (g ·v h) = (f ·v g) ·v h.
Proof.
  apply assoc.
Defined.

Proposition assocr_v
            {C : double_cat}
            {w x y z : C}
            (f : w -->v x)
            (g : x -->v y)
            (h : y -->v z)
  : (f ·v g) ·v h = f ·v (g ·v h).
Proof.
  apply assoc'.
Defined.

Proposition isaset_ver_mor
            {C : double_cat}
            (x y : C)
  : isaset (x -->v y).
Proof.
  apply homset_property.
Qed.

(**
 2.2. Horizontal morphisms
 *)
Definition hor_mor
           (C : double_cat)
  : twosided_disp_cat C C
  := pr12 (pr111 C).

Notation "x -->h y" := (hor_mor _ x y) (at level 55) : double_cat.

Proposition is_univalent_twosided_disp_cat_hor_mor
            (C : double_cat)
  : is_univalent_twosided_disp_cat (hor_mor C).
Proof.
  exact (pr22 (pr111 C)).
Qed.

Definition hor_id_double_cat
           (C : double_cat)
  : hor_id (hor_mor C)
  := pr1 (pr211 C).

Definition identity_h
           {C : double_cat}
           (x : C)
  : x -->h x
  := pr111 (pr211 C) x.

Definition hor_comp_double_cat
           (C : double_cat)
  : hor_comp (hor_mor C)
  := pr2 (pr211 C).

Definition hor_mor_comp_double_cat
           {C : double_cat}
           {x y z : C}
           (f : x -->h y)
           (g : y -->h z)
  : x -->h z
  := pr112 (pr211 C) x y z f g.

Notation "f ·h g" := (hor_mor_comp_double_cat f g) (at level 60) : double_cat.

(**
 2.3. Squares
 *)
Definition square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ : C}
           (v₁ : x₁ -->v y₁)
           (v₂ : x₂ -->v y₂)
           (h₁ : x₁ -->h x₂)
           (h₂ : y₁ -->h y₂)
  : UU
  := h₁ -->[ v₁ ][ v₂ ] h₂.

Definition id_v_square
           {C : double_cat}
           {x y : C}
           (h : x -->h y)
  : square (identity_v x) (identity_v y) h h
  := id_two_disp _.

Definition comp_v_square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ z₁ z₂ : C}
           {v₁ : x₁ -->v y₁} {v₁' : y₁ --> z₁}
           {v₂ : x₂ -->v y₂} {v₂' : y₂ --> z₂}
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           {h₃ : z₁ -->h z₂}
           (s₁ : square v₁ v₂ h₁ h₂)
           (s₂ : square v₁' v₂' h₂ h₃)
  : square (v₁ ·v v₁') (v₂ ·v v₂') h₁ h₃
  := s₁ ;;2 s₂.

Notation "s₁ ⋆v s₂" := (comp_v_square s₁ s₂) (at level 40, left associativity) : double_cat.

Definition transportf_square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ : C}
           {v₁ v₁' : x₁ -->v y₁}
           {v₂ v₂' : x₂ -->v y₂}
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           (s₁ : square v₁ v₂ h₁ h₂)
           (p : v₁ = v₁')
           (q : v₂ = v₂')
  : square v₁' v₂' h₁ h₂
  := transportf_disp_mor2 p q s₁.

Definition transportb_square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ : C}
           {v₁ v₁' : x₁ -->v y₁}
           {v₂ v₂' : x₂ -->v y₂}
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           (s₁ : square v₁' v₂' h₁ h₂)
           (p : v₁ = v₁')
           (q : v₂ = v₂')
  : square v₁ v₂ h₁ h₂
  := transportb_disp_mor2 p q s₁.

Proposition square_id_left_v
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : id_v_square h₁ ⋆v s
    =
    transportb_square s (id_left _) (id_left _).
Proof.
  apply id_two_disp_left.
Qed.

Proposition square_id_right_v
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : s ⋆v id_v_square h₂
    =
    transportb_square s (id_right _) (id_right _).
Proof.
  apply id_two_disp_right.
Qed.

Proposition square_assoc_v
            {C : double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : w₁ -->v x₁} {v₁' : x₁ -->v y₁} {v₁'' : y₁ -->v z₁}
            {v₂ : w₂ -->v x₂} {v₂' : x₂ -->v y₂} {v₂'' : y₂ -->v z₂}
            {h₁ : w₁ -->h w₂}
            {h₂ : x₁ -->h x₂}
            {h₃ : y₁ -->h y₂}
            {h₄ : z₁ -->h z₂}
            (s₁ : square v₁ v₂ h₁ h₂)
            (s₂ : square v₁' v₂' h₂ h₃)
            (s₃ : square v₁'' v₂'' h₃ h₄)
  : s₁ ⋆v (s₂ ⋆v s₃)
    =
    transportb_square ((s₁ ⋆v s₂) ⋆v s₃) (assoc _ _ _) (assoc _ _ _).
Proof.
  exact (assoc_two_disp s₁ s₂ s₃).
Qed.

(**
 2.4. Functoriality of horizontal identities
 *)
Definition id_h_square
           {C : double_cat}
           {x y : C}
           (v : x -->v y)
  : square v v (identity_h x) (identity_h y)
  := pr211 (pr211 C) x y v.

Proposition id_h_square_id
            {C : double_cat}
            (x : C)
  : id_h_square (identity_v x) = id_v_square (identity_h x).
Proof.
  exact (pr121 (pr211 C) x).
Qed.

Proposition id_h_square_comp
            {C : double_cat}
            {x y z : C}
            (v₁ : x -->v y)
            (v₂ : y -->v z)
  : id_h_square (v₁ ·v v₂)
    =
    id_h_square v₁ ⋆v id_h_square v₂.
Proof.
  exact (pr221 (pr211 C) x y z v₁ v₂).
Qed.

(**
 2.5. Functoriality of horizontal composition
 *)
Definition comp_h_square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ z₁ z₂ : C}
           {v₁ : x₁ -->v x₂}
           {v₂ : y₁ -->v y₂}
           {v₃ : z₁ -->v z₂}
           {h₁ : x₁ -->h y₁}
           {h₂ : y₁ -->h z₁}
           {k₁ : x₂ -->h y₂}
           {k₂ : y₂ -->h z₂}
           (s₁ : square v₁ v₂ h₁ k₁)
           (s₂ : square v₂ v₃ h₂ k₂)
  : square v₁ v₃ (h₁ ·h h₂) (k₁ ·h k₂)
  := pr212 (pr211 C) x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂.

Notation "s₁ ⋆h s₂" := (comp_h_square s₁ s₂) (at level 40, left associativity) : double_cat.

Proposition comp_h_square_id
            {C : double_cat}
            {x y z : C}
            (h₁ : x -->h y)
            (h₂ : y -->h z)
  : id_v_square h₁ ⋆h id_v_square h₂ = id_v_square (h₁ ·h h₂).
Proof.
  exact (pr122 (pr211 C) x y z h₁ h₂).
Qed.

Proposition comp_h_square_comp
            {C : double_cat}
            {x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C}
            {v₁ : x₁ -->v x₂} {v₁' : x₂ -->v x₃}
            {v₂ : y₁ -->v y₂} {v₂' : y₂ -->v y₃}
            {v₃ : z₁ -->v z₂} {v₃' : z₂ -->v z₃}
            {h₁ : x₁ -->h y₁} {h₂ : y₁ -->h z₁}
            {k₁ : x₂ -->h y₂} {k₂ : y₂ -->h z₂}
            {l₁ : x₃ -->h y₃} {l₂ : y₃ -->h z₃}
            (s₁ : square v₁ v₂ h₁ k₁)
            (s₁' : square v₁' v₂' k₁ l₁)
            (s₂ : square v₂ v₃ h₂ k₂)
            (s₂' : square v₂' v₃' k₂ l₂)
  : (s₁ ⋆v s₁') ⋆h (s₂ ⋆v s₂') = (s₁ ⋆h s₂) ⋆v (s₁' ⋆h s₂').
Proof.
  exact (pr222 (pr211 C)
           x₁ x₂ x₃
           y₁ y₂ y₃
           z₁ z₂ z₃
           v₁ v₁'
           v₂ v₂'
           v₃ v₃'
           h₁ h₂
           k₁ k₂
           l₁ l₂
           s₁ s₁'
           s₂ s₂').
Qed.

(**
 2.6. Left unitor
 *)
Definition double_cat_double_lunitor
           (C : double_cat)
  : double_cat_lunitor (hor_id_double_cat C) (hor_comp_double_cat C)
  := pr121 C.

Definition lunitor_h
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : square (identity_v x) (identity_v y) (identity_h x ·h f) f
  := pr1 (pr1 (pr121 C) x y f).

Definition linvunitor_h
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : square (identity_v x) (identity_v y) f (identity_h x ·h f)
  := pr12 (pr1 (pr121 C) x y f).

Proposition lunitor_linvunitor_h
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : lunitor_h f ⋆v linvunitor_h f
    =
    transportb_square (id_v_square _) (id_v_left _) (id_v_left _).
Proof.
  exact (pr122 (pr1 (pr121 C) x y f)).
Qed.

Proposition linvunitor_lunitor_h
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : linvunitor_h f ⋆v lunitor_h f
    =
    transportb_square (id_v_square _) (id_v_left _) (id_v_left _).
Proof.
  exact (pr222 (pr1 (pr121 C) x y f)).
Qed.

Proposition lunitor_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : (id_h_square _ ⋆h s) ⋆v lunitor_h h₂
    =
    transportb_square
      (lunitor_h h₁ ⋆v s)
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _)).
Proof.
  exact (!(pr2 (pr121 C) x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ s)).
Qed.

(**
 2.7. Right unitor
 *)
Definition double_cat_double_runitor
           (C : double_cat)
  : double_cat_runitor (hor_id_double_cat C) (hor_comp_double_cat C)
  := pr1 (pr221 C).

Definition runitor_h
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : square (identity_v x) (identity_v y) (f ·h identity_h y) f
  := pr1 (pr11 (pr221 C) x y f).

Definition rinvunitor_h
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : square (identity_v x) (identity_v y) f (f ·h identity_h y)
  := pr12 (pr11 (pr221 C) x y f).

Proposition runitor_rinvunitor_h
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : runitor_h f ⋆v rinvunitor_h f
    =
    transportb_square (id_v_square _) (id_v_left _) (id_v_left _).
Proof.
  exact (pr122 (pr11 (pr221 C) x y f)).
Qed.

Proposition rinvunitor_runitor_h
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : rinvunitor_h f ⋆v runitor_h f
    =
    transportb_square (id_v_square _) (id_v_left _) (id_v_left _).
Proof.
  exact (pr222 (pr11 (pr221 C) x y f)).
Qed.

Proposition runitor_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : (s ⋆h id_h_square _) ⋆v runitor_h h₂
    =
    transportb_square
      (runitor_h h₁ ⋆v s)
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _)).
Proof.
  exact (!(pr21 (pr221 C) x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ s)).
Qed.

(**
 2.8. Associator
 *)
Definition double_cat_double_associator
           (C : double_cat)
  : double_cat_associator (hor_comp_double_cat C)
  := pr2 (pr221 C).

Definition lassociator_h
           {C : double_cat}
           {w x y z : C}
           (f : w -->h x)
           (g : x -->h y)
           (h : y -->h z)
  : square (identity_v w) (identity_v z) (f ·h (g ·h h)) ((f ·h g) ·h h)
  := pr1 (pr12 (pr221 C) w x y z f g h).

Definition rassociator_h
           {C : double_cat}
           {w x y z : C}
           (f : w -->h x)
           (g : x -->h y)
           (h : y -->h z)
  : square (identity_v w) (identity_v z) ((f ·h g) ·h h) (f ·h (g ·h h))
  := pr12 (pr12 (pr221 C) w x y z f g h).

Proposition lassociator_rassociator_h
            {C : double_cat}
            {w x y z : C}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : lassociator_h f g h ⋆v rassociator_h f g h
    =
    transportb_square (id_v_square _) (id_v_left _) (id_v_left _).
Proof.
  exact (pr122 (pr12 (pr221 C) w x y z f g h)).
Qed.

Proposition rassociator_lassociator_h
            {C : double_cat}
            {w x y z : C}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : rassociator_h f g h ⋆v lassociator_h f g h
    =
    transportb_square (id_v_square _) (id_v_left _) (id_v_left _).
Proof.
  exact (pr222 (pr12 (pr221 C) w x y z f g h)).
Qed.

Proposition lassociator_h_square
            {C : double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {vw : w₁ -->v w₂} {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂} {vz : z₁ -->v z₂}
            {h₁ : w₁ -->h x₁} {h₂ : w₂ -->h x₂}
            {j₁ : x₁ -->h y₁} {j₂ : x₂ -->h y₂}
            {k₁ : y₁ -->h z₁} {k₂ : y₂ -->h z₂}
            (s₁ : square vw vx h₁ h₂)
            (s₂ : square vx vy j₁ j₂)
            (s₃ : square vy vz k₁ k₂)
  : (s₁ ⋆h (s₂ ⋆h s₃)) ⋆v lassociator_h h₂ j₂ k₂
    =
    transportb_square
      (lassociator_h h₁ j₁ k₁ ⋆v ((s₁ ⋆h s₂) ⋆h s₃))
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _)).
Proof.
  exact (!(pr22 (pr221 C) w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ j₁ j₂ k₁ k₂ vw vx vy vz s₁ s₂ s₃)).
Qed.

(**
 2.9. Triangle and pentagon equations
 *)
Proposition double_triangle
            {C : double_cat}
            {x y z : C}
            (h : x -->h y)
            (k : y -->h z)
  : transportf_square
      (lassociator_h h _ k ⋆v (runitor_h h ⋆h id_v_square _))
      (id_v_left _)
      (id_v_left _)
    =
    id_v_square h ⋆h lunitor_h k.
Proof.
  exact (pr12 C x y z h k).
Qed.

Proposition double_pentagon
            {C : double_cat}
            {v w x y z : C}
            (h₁ : v -->h w)
            (h₂ : w -->h x)
            (h₃ : x -->h y)
            (h₄ : y -->h z)
  : transportb_square
      (lassociator_h h₁ h₂ (h₃ ·h h₄) ⋆v lassociator_h (h₁ ·h h₂) h₃ h₄)
      (id_right _)
      (id_right _)
    =
    (id_v_square h₁ ⋆h lassociator_h h₂ h₃ h₄)
    ⋆v lassociator_h h₁ (h₂ ·h h₃) h₄
    ⋆v (lassociator_h h₁ h₂ h₃ ⋆h id_v_square h₄).
Proof.
  exact (pr22 C v w x y z h₁ h₂ h₃ h₄).
Qed.

(**
 3. Builder for double categories
 *)
Definition make_double_cat
           (C : category)
           (D : twosided_disp_cat C C)
           (I : hor_id D)
           (Cm : hor_comp D)
           (l : double_cat_lunitor I Cm)
           (r : double_cat_runitor I Cm)
           (a : double_cat_associator Cm)
           (tr : triangle_law l r a)
           (pe : pentagon_law a)
           (HC : is_univalent C)
           (HD : is_univalent_twosided_disp_cat D)
  : double_cat.
Proof.
  simple refine ((((_ ,, _) ,, _) ,, _) ,, _).
  - exact (C ,, HC).
  - exact (D ,, HD).
  - exact (I ,, Cm).
  - exact (l ,, r ,, a).
  - exact (tr ,, pe).
Defined.

(**
 4. Lax functors for double categories
 *)
Definition lax_double_functor
           (C₁ C₂ : double_cat)
  : UU
  := C₁ --> C₂.

Definition id_lax_double_functor
           (C : double_cat)
  : lax_double_functor C C
  := identity _.

Definition comp_lax_double_functor
           {C₁ C₂ C₃ : double_cat}
           (F : lax_double_functor C₁ C₂)
           (G : lax_double_functor C₂ C₃)
  : lax_double_functor C₁ C₃
  := F · G.

(**
 5. Accessors for lax functors
 *)
Definition lax_double_functor_ver
           {C₁ C₂ : double_cat}
           (F : lax_double_functor C₁ C₂)
  : C₁ ⟶ C₂
  := pr1 (pr111 F).

Coercion lax_double_functor_ver : lax_double_functor >-> functor.

Definition lax_double_functor_ver_mor
           {C₁ C₂ : double_cat}
           (F : lax_double_functor C₁ C₂)
           {x y : C₁}
           (f : x -->v y)
  : F x -->v F y
  := pr211 (pr111 F) x y f.

Notation "'#v' F f" := (lax_double_functor_ver_mor F f)
                         (at level 10, F at next level, f at next level) : double_cat.

Proposition lax_double_functor_id_v
            {C₁ C₂ : double_cat}
            (F : lax_double_functor C₁ C₂)
            (x : C₁)
  : #v F (identity_v x) = identity_v _.
Proof.
  apply functor_id.
Defined.

Proposition lax_double_functor_comp_v
            {C₁ C₂ : double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y z : C₁}
            (f : x -->v y)
            (g : y -->v z)
  : #v F (f ·v g) = #v F f ·v #v F g.
Proof.
  apply functor_comp.
Defined.

Definition lax_double_functor_hor_mor
           {C₁ C₂ : double_cat}
           (F : lax_double_functor C₁ C₂)
  : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂)
  := pr2 (pr111 F).

Notation "'#h' F f" := (lax_double_functor_hor_mor F _ _ f)
                         (at level 10, F at next level, f at next level) : double_cat.
Notation "'#s' F s" := (#2 (lax_double_functor_hor_mor F) s)
                         (at level 10, F at next level, s at next level) : double_cat.

Proposition lax_double_functor_id_square
            {C₁ C₂ : double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y : C₁}
            (h : x -->h y)
  : #s F (id_v_square h)
    =
    transportb_square
      (id_v_square _)
      (lax_double_functor_id_v _ _)
      (lax_double_functor_id_v _ _).
Proof.
  exact (twosided_disp_functor_id _ _ _ _ (lax_double_functor_hor_mor F) h).
Qed.

Proposition lax_double_functor_comp_v_square
            {C₁ C₂ : double_cat}
            (F : lax_double_functor C₁ C₂)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C₁}
            {v₁ : x₁ -->v y₁} {v₁' : y₁ --> z₁}
            {v₂ : x₂ -->v y₂} {v₂' : y₂ --> z₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            {h₃ : z₁ -->h z₂}
            (s₁ : square v₁ v₂ h₁ h₂)
            (s₂ : square v₁' v₂' h₂ h₃)
  : #s F (s₁ ⋆v s₂)
    =
    transportb_square
      (#s F s₁ ⋆v #s F s₂)
      (lax_double_functor_comp_v _ _ _)
      (lax_double_functor_comp_v _ _ _).
Proof.
  apply (twosided_disp_functor_comp _ _ _ _ (lax_double_functor_hor_mor F)).
Qed.

Definition lax_double_functor_hor_id
           {C₁ C₂ : double_cat}
           (F : lax_double_functor C₁ C₂)
  : double_functor_hor_id
      (lax_double_functor_hor_mor F)
      (hor_id_double_cat C₁)
      (hor_id_double_cat C₂)
  := pr1 (pr211 F).

Definition lax_double_functor_id_h
           {C₁ C₂ : double_cat}
           (F : lax_double_functor C₁ C₂)
           (x : C₁)
  : square (identity_v _) (identity_v (F x)) (identity_h _) (#h F (identity_h _)).
Proof.
  exact (pr11 (pr211 F) x).
Defined.

Proposition lax_double_functor_id_h_mor
            {C₁ C₂ : double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y : C₁}
            (f : x -->v y)
  : id_h_square (#v F f) ⋆v lax_double_functor_id_h F y
    =
    transportb_square
      (lax_double_functor_id_h F x ⋆v #s F (id_h_square f))
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _)).
Proof.
  exact (pr21 (pr211 F) x y f).
Qed.

Definition lax_double_functor_hor_comp
           {C₁ C₂ : double_cat}
           (F : lax_double_functor C₁ C₂)
  : double_functor_hor_comp
      (lax_double_functor_hor_mor F)
      (hor_comp_double_cat C₁)
      (hor_comp_double_cat C₂)
  := pr2 (pr211 F).

Definition lax_double_functor_comp_h
           {C₁ C₂ : double_cat}
           (F : lax_double_functor C₁ C₂)
           {x y z : C₁}
           (h : x -->h y)
           (k : y -->h z)
  : square (identity _) (identity _) (#h F h ·h #h F k) (#h F (h ·h k))
  := pr12 (pr211 F) x y z h k.

Proposition lax_double_functor_comp_h_mor
            {C₁ C₂ : double_cat}
            (F : lax_double_functor C₁ C₂)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C₁}
            {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂}
            {vz : z₁ -->v z₂}
            {h₁ : x₁ -->h y₁} {h₂ : x₂ -->h y₂}
            {k₁ : y₁ -->h z₁} {k₂ : y₂ -->h z₂}
            (sh : square vx vy h₁ h₂)
            (sk : square vy vz k₁ k₂)
  : (#s F sh ⋆h #s F sk) ⋆v lax_double_functor_comp_h F h₂ k₂
    =
    transportb_square
      (lax_double_functor_comp_h F h₁ k₁ ⋆v #s F (sh ⋆h sk))
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _)).
Proof.
  exact (pr22 (pr211 F) x₁ x₂ y₁ y₂ z₁ z₂ vx vy vz h₁ h₂ k₁ k₂ sh sk).
Qed.

Proposition lax_double_functor_lunitor_h
            {C₁ C₂ : double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y : C₁}
            (f : x -->h y)
  : lunitor_h (#h F f)
    =
    transportf_square
      ((lax_double_functor_id_h F _ ⋆h id_v_square _)
       ⋆v lax_double_functor_comp_h F _ _
       ⋆v #s F (lunitor_h f))
      (assocr_v _ _ _ @ id_v_left _ @ id_v_left _ @ lax_double_functor_id_v _ _)
      (assocr_v _ _ _ @ id_v_left _ @ id_v_left _ @ lax_double_functor_id_v _ _).
Proof.
  exact (pr121 F x y f).
Qed.

Proposition lax_double_functor_runitor_h
            {C₁ C₂ : double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y : C₁}
            (f : x -->h y)
  : runitor_h (#h F f)
    =
    transportf_square
      ((id_v_square _ ⋆h lax_double_functor_id_h F _)
       ⋆v lax_double_functor_comp_h F _ _
       ⋆v #s F (runitor_h f))
      (assocr_v _ _ _ @ id_v_left _ @ id_v_left _ @ lax_double_functor_id_v _ _)
      (assocr_v _ _ _ @ id_v_left _ @ id_v_left _ @ lax_double_functor_id_v _ _).
Proof.
  exact (pr1 (pr221 F) x y f).
Qed.

Proposition lax_double_functor_lassociator_h
            {C₁ C₂ : double_cat}
            (F : lax_double_functor C₁ C₂)
            {w x y z : C₁}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : lassociator_h (#h F f) (#h F g) (#h F h)
    ⋆v (lax_double_functor_comp_h F f g ⋆h id_v_square _)
    ⋆v lax_double_functor_comp_h F (f ·h g) h
    =
    transportf_square
      ((id_v_square _ ⋆h lax_double_functor_comp_h F g h)
       ⋆v lax_double_functor_comp_h F f (g ·h h)
       ⋆v #s F (lassociator_h f g h))
      (maponpaths _ (lax_double_functor_id_v _ _))
      (maponpaths _ (lax_double_functor_id_v _ _)).
Proof.
  exact (pr2 (pr221 F) w x y z f g h).
Qed.

(**
 6. Builder for lax functors
 *)
Definition make_lax_double_functor
           {C₁ C₂ : double_cat}
           (F : C₁ ⟶ C₂)
           (FF : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂))
           (FI : double_functor_hor_id
                   FF
                   (hor_id_double_cat C₁)
                   (hor_id_double_cat C₂))
           (FC : double_functor_hor_comp
                   FF
                   (hor_comp_double_cat C₁)
                   (hor_comp_double_cat C₂))
           (Fl : double_functor_lunitor
                   (double_cat_double_lunitor C₁)
                   (double_cat_double_lunitor C₂)
                   FI FC)
           (Fr : double_functor_runitor
                   (double_cat_double_runitor C₁)
                   (double_cat_double_runitor C₂)
                   FI FC)
           (Fa : double_functor_associator
                   (double_cat_double_associator C₁)
                   (double_cat_double_associator C₂)
                   FC)
  : lax_double_functor C₁ C₂.
Proof.
  simple refine ((((F ,, FF) ,, _) ,, _) ,, tt).
  - split ; cbn.
    + exact FI.
    + exact FC.
  - repeat split ; cbn.
    + exact Fl.
    + exact Fr.
    + exact Fa.
Defined.

(**
 7. Double transformations
 *)
Definition double_transformation
           {C₁ C₂ : double_cat}
           (F G : lax_double_functor C₁ C₂)
  : UU
  := F ==> G.

(**
 8. Accessors for double transformations
 *)
Definition double_transformation_to_nat_trans
           {C₁ C₂ : double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : double_transformation F G)
  : F ⟹ G
  := pr1 (pr111 τ).

Coercion double_transformation_to_nat_trans : double_transformation >-> nat_trans.

Proposition double_transformation_ver_mor
            {C₁ C₂ : double_cat}
            {F G : lax_double_functor C₁ C₂}
            (τ : double_transformation F G)
            {x y : C₁}
            (f : x -->v y)
  : #v F f ·v τ y = τ x ·v #v G f.
Proof.
  exact (nat_trans_ax τ x y f).
Defined.

Definition double_transformation_hor_mor
           {C₁ C₂ : double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : double_transformation F G)
           {x y : C₁}
           (f : x -->h y)
  : square (τ x) (τ y) (#h F f) (#h G f)
  := pr12 (pr111 τ) x y f.

Proposition double_transformation_square
            {C₁ C₂ : double_cat}
            {F G : lax_double_functor C₁ C₂}
            (τ : double_transformation F G)
            {x₁ x₂ y₁ y₂ : C₁}
            {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂}
            {h : x₁ -->h y₁}
            {k : x₂ -->h y₂}
            (s : square vx vy h k)
  : #s F s ⋆v double_transformation_hor_mor τ k
    =
    transportb_square
      (double_transformation_hor_mor τ h ⋆v #s G s)
      (double_transformation_ver_mor _ _)
      (double_transformation_ver_mor _ _).
Proof.
  exact (pr22 (pr111 τ) x₁ x₂ y₁ y₂ vx vy h k s).
Qed.

Proposition double_transformation_id_h
            {C₁ C₂ : double_cat}
            {F G : lax_double_functor C₁ C₂}
            (τ : double_transformation F G)
            (x : C₁)
  : lax_double_functor_id_h F x ⋆v double_transformation_hor_mor τ (identity_h x)
    =
    transportb_square
      (id_h_square (τ x) ⋆v lax_double_functor_id_h G x)
      (id_v_left _ @ !(id_v_right _))
      (id_v_left _ @ !(id_v_right _)).
Proof.
  exact (pr1 (pr211 τ) x).
Qed.

Proposition double_transformation_comp_h
            {C₁ C₂ : double_cat}
            {F G : lax_double_functor C₁ C₂}
            (τ : double_transformation F G)
            {x y z : C₁}
            (h : x -->h y)
            (k : y -->h z)
  : lax_double_functor_comp_h F h k
    ⋆v double_transformation_hor_mor τ (h ·h k)
    =
    transportb_square
      ((double_transformation_hor_mor τ h ⋆h double_transformation_hor_mor τ k)
       ⋆v lax_double_functor_comp_h G h k)
      (id_v_left _ @ !(id_v_right _))
      (id_v_left _ @ !(id_v_right _)).
Proof.
  exact (pr2 (pr211 τ) x y z h k).
Qed.

(**
 9. Builder for double transformations
 *)
Definition make_double_transformation
           {C₁ C₂ : double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : F ⟹ G)
           (ττ : twosided_disp_nat_trans
                   τ τ
                   (lax_double_functor_hor_mor F)
                   (lax_double_functor_hor_mor G))
           (τI : double_nat_trans_hor_id
                   ττ
                   (lax_double_functor_hor_id F)
                   (lax_double_functor_hor_id G))
           (τC : double_nat_trans_hor_comp
                   ττ
                   (lax_double_functor_hor_comp F)
                   (lax_double_functor_hor_comp G))
  : double_transformation F G.
Proof.
  simple refine ((((_ ,, _) ,, _) ,, (tt ,, tt ,, tt)) ,, tt).
  - exact τ.
  - exact ττ.
  - split ; cbn.
    + exact τI.
    + exact τC.
Defined.
