(************************************************************************

 Limits and colimits in the unit category

 Contents
 1. Terminal objects
 2. Products
 3. Pullbacks
 4. Initial objects
 5. Coproducts

 ************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.

Local Open Scope cat.

(**
 1. Terminal objects
 *)
Definition isTerminal_unit_category
           (x : unit_category)
  : isTerminal unit_category x.
Proof.
  use make_isTerminal.
  intro y.
  use iscontraprop1 ; [ apply isasetunit | ].
  apply isapropunit.
Qed.

Definition terminal_unit_category
  : Terminal unit_category.
Proof.
  simple refine (_ ,, _).
  - exact tt.
  - exact (isTerminal_unit_category tt).
Defined.

Definition functor_to_unit_preserves_terminal
           (C : category)
  : preserves_terminal (functor_to_unit C).
Proof.
  intros x Hx.
  apply isTerminal_unit_category.
Defined.

(**
 2. Products
 *)
Definition isBinProduct_unit_category
           {x y z : unit_category}
           (f : z --> x)
           (g : z --> y)
  : isBinProduct unit_category x y z f g.
Proof.
  intros w h₁ h₂.
  use iscontraprop1.
  - apply invproofirrelevance.
    intros fg₁ fg₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    apply isasetunit.
  - simple refine (_ ,, _ ,, _).
    + apply isapropunit.
    + apply isasetunit.
    + apply isasetunit.
Qed.

Definition binproduct_unit_category
  : BinProducts unit_category.
Proof.
  intros x y.
  use make_BinProduct.
  - exact tt.
  - apply isapropunit.
  - apply isapropunit.
  - apply isBinProduct_unit_category.
Defined.

Definition functor_to_unit_preserves_binproduct
           (C : category)
  : preserves_binproduct (functor_to_unit C).
Proof.
  intro ; intros.
  apply isBinProduct_unit_category.
Defined.

(**
 3. Pullbacks
 *)
Definition isPullback_unit_category
           {w x y z : unit_category}
           {f : x --> z}
           {g : y --> z}
           {p₁ : w --> x}
           {p₂ : w --> y}
           (eq : p₁ · f = p₂ · g)
  : isPullback eq.
Proof.
  intros r h₁ h₂ q.
  use iscontraprop1.
  - apply invproofirrelevance.
    intros fg₁ fg₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    apply isasetunit.
  - simple refine (_ ,, _ ,, _).
    + apply isapropunit.
    + apply isasetunit.
    + apply isasetunit.
Qed.

Definition pullbacks_unit_category
  : Pullbacks unit_category.
Proof.
  intros x y z f g.
  use make_Pullback.
  - exact tt.
  - apply isapropunit.
  - apply isapropunit.
  - apply isasetunit.
  - apply isPullback_unit_category.
Defined.

Definition functor_to_unit_preserves_pullback
           (C : category)
  : preserves_pullback (functor_to_unit C).
Proof.
  intro ; intros.
  apply isPullback_unit_category.
Defined.

(**
 4. Initial objects
 *)
Definition isInitial_unit_category
           (x : unit_category)
  : isInitial unit_category x.
Proof.
  intro y.
  use iscontraprop1 ; [ apply isasetunit | ].
  apply isapropunit.
Qed.

Definition initial_unit_category
  : Initial unit_category.
Proof.
  simple refine (_ ,, _).
  - exact tt.
  - exact (isInitial_unit_category tt).
Defined.

Definition functor_to_unit_preserves_initial
           (C : category)
  : preserves_initial (functor_to_unit C).
Proof.
  intros x Hx.
  apply isInitial_unit_category.
Defined.

(**
 5. Coproducts
 *)
Definition isBinCoproduct_unit_category
           {x y z : unit_category}
           (f : x --> z)
           (g : y --> z)
  : isBinCoproduct unit_category x y z f g.
Proof.
  intros w h₁ h₂.
  use iscontraprop1.
  - apply invproofirrelevance.
    intros fg₁ fg₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    apply isasetunit.
  - simple refine (_ ,, _ ,, _).
    + apply isapropunit.
    + apply isasetunit.
    + apply isasetunit.
Qed.

Definition bincoproduct_unit_category
  : BinCoproducts unit_category.
Proof.
  intros x y.
  use make_BinCoproduct.
  - exact tt.
  - apply isapropunit.
  - apply isapropunit.
  - apply isBinCoproduct_unit_category.
Defined.

Definition functor_to_unit_preserves_bincoproduct
           (C : category)
  : preserves_bincoproduct (functor_to_unit C).
Proof.
  intro ; intros.
  apply isBinCoproduct_unit_category.
Defined.
