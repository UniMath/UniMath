(****************************************************************************

 Linear categories

 In this file, we define linear categories.

 Note that the thirteen laws in [linear_category_laws] are written out explicitly.
 In the "other accessors" (part 3 below), each of the laws enters a mathematical structure, so as
 to validate its purpose.

 Contents
 1. Data of linear categories
 2. Laws of linear categories
 3. Other accessors for linear categories

 ****************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Examples.ConstantFunctor.
Require Import UniMath.CategoryTheory.Monoidal.CategoriesOfMonoids.
Require Import UniMath.CategoryTheory.Categories.Dialgebras.
Require Import UniMath.CategoryTheory.Monoidal.Examples.DiagonalFunctor.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

(**
 1. Data of linear categories
 *)
Definition linear_category_data
  : UU
  := ∑ (𝕃 : sym_mon_closed_cat)
       (bang : sym_monoidal_cmd 𝕃),
     (∏ (x : 𝕃), bang x --> bang x ⊗ bang x)
     ×
     (∏ (x : 𝕃), bang x --> I_{𝕃}).

Definition make_linear_category_data
           (𝕃 : sym_mon_closed_cat)
           (bang : sym_monoidal_cmd 𝕃)
           (δ : ∏ (x : 𝕃), bang x --> bang x ⊗ bang x)
           (ε : ∏ (x : 𝕃), bang x --> I_{𝕃})
  : linear_category_data
  := 𝕃 ,, bang ,, δ ,, ε.

#[reversible=no] Coercion linear_category_data_to_sym_mon_closed_cat
         (𝕃 : linear_category_data)
  : sym_mon_closed_cat
  := pr1 𝕃.

Definition linear_category_bang
           (𝕃 : linear_category_data)
  : sym_monoidal_cmd 𝕃
  := pr12 𝕃.

Definition linear_category_bang_functor
           (𝕃 : linear_category_data)
  : lax_monoidal_functor 𝕃 𝕃
  := _ ,, lax_monoidal_from_symmetric_monoidal_comonad _ (linear_category_bang 𝕃).

Definition linear_category_comult
           (𝕃 : linear_category_data)
           (x : 𝕃)
  : linear_category_bang 𝕃 x
    -->
    linear_category_bang 𝕃 x ⊗ linear_category_bang 𝕃 x
  := pr122 𝕃 x.

Definition linear_category_counit
           (𝕃 : linear_category_data)
           (x : 𝕃)
  : linear_category_bang 𝕃 x --> I_{𝕃}
  := pr222 𝕃 x.

(**
 2. Laws of linear categories
 *)
Definition linear_category_laws
           (𝕃 : linear_category_data)
  : UU
  := (** naturality of comultiplication *)
     (∏ (x y : 𝕃)
        (f : x --> y),
      #(linear_category_bang 𝕃) f
      · linear_category_comult 𝕃 y
      =
      linear_category_comult 𝕃 x
      · (#(linear_category_bang 𝕃) f #⊗ #(linear_category_bang 𝕃) f))
     ×
     (** naturality of counit *)
     (∏ (x y : 𝕃)
        (f : x --> y),
      #(linear_category_bang 𝕃) f · linear_category_counit 𝕃 y
      =
      linear_category_counit 𝕃 x)
     ×
     (** the comultiplication is a coalgebra morphism *)
     (∏ (x : 𝕃),
      linear_category_comult 𝕃 x
      · (δ (linear_category_bang 𝕃) x #⊗ δ (linear_category_bang 𝕃) x)
      · mon_functor_tensor (linear_category_bang_functor 𝕃) _ _
      =
      δ (linear_category_bang 𝕃) x
      · #(linear_category_bang 𝕃) (linear_category_comult 𝕃 x))
     ×
     (** the counit is a coalgebra morphism *)
     (∏ (x : 𝕃),
      linear_category_counit 𝕃 x
      · mon_functor_unit (linear_category_bang_functor 𝕃)
      =
      δ (linear_category_bang 𝕃) x
      · #(linear_category_bang 𝕃) (linear_category_counit 𝕃 x))
     ×
     (** the comultiplication of the comonad is a comonoid morphism (counit) *)
     (∏ (x : 𝕃),
      δ (linear_category_bang 𝕃) x
      · linear_category_counit 𝕃 (linear_category_bang 𝕃 x)
      =
      linear_category_counit 𝕃 x)
     ×
     (** the comultiplication of the comonad is a comonoid morphism (comultiplication) *)
     (∏ (x : 𝕃),
      δ (linear_category_bang 𝕃) x
      · linear_category_comult 𝕃 (linear_category_bang 𝕃 x)
      =
      linear_category_comult 𝕃 x
      · (δ (linear_category_bang 𝕃) x #⊗ δ (linear_category_bang 𝕃) x))
     ×
     (** coassociativity *)
     (∏ (x : 𝕃),
      linear_category_comult 𝕃 x
      · (identity _ #⊗ linear_category_comult 𝕃 x)
      =
      linear_category_comult 𝕃 x
      · (linear_category_comult 𝕃 x #⊗ identity _)
      · mon_lassociator _ _ _)
     ×
     (** counitality *)
     (∏ (x : 𝕃),
      linear_category_comult 𝕃 x
      · (linear_category_counit 𝕃 x #⊗ identity _)
      · mon_lunitor _
      =
      identity _)
     ×
     (** cocommutativity *)
     (∏ (x : 𝕃),
      linear_category_comult 𝕃 x
      · sym_mon_braiding 𝕃 _ _
      =
        linear_category_comult 𝕃 x)
     ×
     (** comult preserves tensor *)
     (∏ x y : 𝕃,
         mon_functor_tensor (linear_category_bang_functor 𝕃) x y
           · linear_category_comult 𝕃 (x ⊗ y)
         = (linear_category_comult 𝕃 x) #⊗ (linear_category_comult 𝕃 y)
             · (inner_swap 𝕃
                  (linear_category_bang 𝕃 x)
                  (linear_category_bang 𝕃 x)
                  (linear_category_bang 𝕃 y)
                  (linear_category_bang 𝕃 y)
                  · mon_functor_tensor (linear_category_bang_functor 𝕃) x y
                  #⊗ mon_functor_tensor (linear_category_bang_functor 𝕃) x y))
     ×
     (** comult preserves unit *)
     (mon_functor_unit (linear_category_bang_functor 𝕃)
                · linear_category_comult 𝕃 I_{𝕃}
              = mon_linvunitor I_{𝕃}
                  · mon_functor_unit (linear_category_bang_functor 𝕃)
                  #⊗ mon_functor_unit (linear_category_bang_functor 𝕃))
     ×
     (** counit preserves tensor *)
     (∏ x y : 𝕃, mon_functor_tensor (linear_category_bang_functor 𝕃) x y
                           · linear_category_counit 𝕃 (x ⊗ y)
                         = linear_category_counit 𝕃 x #⊗ linear_category_counit 𝕃 y
                             · mon_lunitor (monoidal_unit 𝕃))
     ×
     (** counit preserves unit *)
     (mon_functor_unit (linear_category_bang_functor 𝕃)
                · linear_category_counit 𝕃 I_{𝕃}
              = identity I_{𝕃}).


Definition linear_category
  : UU
  := ∑ (𝕃 : linear_category_data), linear_category_laws 𝕃.

Definition make_linear_category
           (𝕃 : linear_category_data)
           (H : linear_category_laws 𝕃)
  : linear_category
  := 𝕃 ,, H.

#[reversible=no] Coercion linear_category_to_data
         (𝕃 : linear_category)
  : linear_category_data
  := pr1 𝕃.

Section AccessorsLaws.
  Context {𝕃 : linear_category}.

  Proposition linear_category_comult_nat
              {x y : 𝕃}
              (f : x --> y)
    : #(linear_category_bang 𝕃) f
      · linear_category_comult 𝕃 y
      =
      linear_category_comult 𝕃 x
      · (#(linear_category_bang 𝕃) f #⊗ #(linear_category_bang 𝕃) f).
  Proof.
    exact (pr12 𝕃 x y f).
  Qed.

  Proposition linear_category_counit_nat
              {x y : 𝕃}
              (f : x --> y)
    : #(linear_category_bang 𝕃) f · linear_category_counit 𝕃 y
      =
      linear_category_counit 𝕃 x.
  Proof.
    exact (pr122 𝕃 x y f).
  Qed.

  Proposition linear_category_comult_coalgebra_mor
              (x : 𝕃)
    : linear_category_comult 𝕃 x
      · (δ (linear_category_bang 𝕃) x #⊗ δ (linear_category_bang 𝕃) x)
      · mon_functor_tensor (linear_category_bang_functor 𝕃) _ _
      =
      δ (linear_category_bang 𝕃) x
      · #(linear_category_bang 𝕃) (linear_category_comult 𝕃 x).
  Proof.
    exact (pr1 (pr222 𝕃) x).
  Qed.

  Proposition linear_category_counit_coalgebra_mor
              (x : 𝕃)
    : linear_category_counit 𝕃 x
      · mon_functor_unit (linear_category_bang_functor 𝕃)
      =
      δ (linear_category_bang 𝕃) x
      · #(linear_category_bang 𝕃) (linear_category_counit 𝕃 x).
  Proof.
    exact (pr12 (pr222 𝕃) x).
  Qed.

  Proposition linear_category_comult_comonoid_mor_counit
              (x : 𝕃)
    : δ (linear_category_bang 𝕃) x
      · linear_category_counit 𝕃 (linear_category_bang 𝕃 x)
      =
      linear_category_counit 𝕃 x.
  Proof.
    exact (pr122 (pr222 𝕃) x).
  Qed.

  Proposition linear_category_comult_comonoid_mor_comult
              (x : 𝕃)
    : δ (linear_category_bang 𝕃) x
      · linear_category_comult 𝕃 (linear_category_bang 𝕃 x)
      =
      linear_category_comult 𝕃 x
      · (δ (linear_category_bang 𝕃) x #⊗ δ (linear_category_bang 𝕃) x).
  Proof.
    exact (pr1 (pr222 (pr222 𝕃)) x).
  Qed.

  Proposition linear_category_coassoc
              (x : 𝕃)
    : linear_category_comult 𝕃 x
      · (identity _ #⊗ linear_category_comult 𝕃 x)
      =
      linear_category_comult 𝕃 x
      · (linear_category_comult 𝕃 x #⊗ identity _)
      · mon_lassociator _ _ _.
  Proof.
    exact (pr12 (pr222 (pr222 𝕃)) x).
  Qed.

  Proposition linear_category_counitality
              (x : 𝕃)
    : linear_category_comult 𝕃 x
      · (linear_category_counit 𝕃 x #⊗ identity _)
      · mon_lunitor _
      =
      identity _.
  Proof.
    exact (pr122 (pr222 (pr222 𝕃)) x).
  Qed.

  Proposition linear_category_cocommutative
              (x : 𝕃)
    : linear_category_comult 𝕃 x
      · sym_mon_braiding 𝕃 _ _
      =
      linear_category_comult 𝕃 x.
  Proof.
    exact (pr1 (pr222 (pr222 (pr222 𝕃))) x).
  Qed.

  Proposition linear_category_comult_preserves_tensor
    (x y : 𝕃)
    : mon_functor_tensor (linear_category_bang_functor 𝕃) x y
           · linear_category_comult 𝕃 (x ⊗ y)
         = (linear_category_comult 𝕃 x) #⊗ (linear_category_comult 𝕃 y)
             · (inner_swap 𝕃
                  (linear_category_bang 𝕃 x)
                  (linear_category_bang 𝕃 x)
                  (linear_category_bang 𝕃 y)
                  (linear_category_bang 𝕃 y)
                  · mon_functor_tensor (linear_category_bang_functor 𝕃) x y
                  #⊗ mon_functor_tensor (linear_category_bang_functor 𝕃) x y).
  Proof.
    exact (pr12 (pr222 (pr222 (pr222 𝕃))) x y).
  Qed.

  Proposition linear_category_comult_preserves_unit
    : mon_functor_unit (linear_category_bang_functor 𝕃)
        · linear_category_comult 𝕃 I_{𝕃}
      = mon_linvunitor I_{𝕃}
          · mon_functor_unit (linear_category_bang_functor 𝕃)
          #⊗ mon_functor_unit (linear_category_bang_functor 𝕃).
  Proof.
    exact (pr122 (pr222 (pr222 (pr222 𝕃)))).
  Qed.

  Proposition linear_category_counit_preserves_tensor
    (x y : 𝕃)
    : mon_functor_tensor (linear_category_bang_functor 𝕃) x y
        · linear_category_counit 𝕃 (x ⊗ y)
      = linear_category_counit 𝕃 x #⊗ linear_category_counit 𝕃 y
          · mon_lunitor (monoidal_unit 𝕃).
  Proof.
    exact (pr1 (pr222 (pr222 (pr222 (pr222 𝕃)))) x y).
  Qed.

  Proposition linear_category_counit_preserves_unit
    : mon_functor_unit (linear_category_bang_functor 𝕃)
        · linear_category_counit 𝕃 I_{𝕃}
      = identity I_{𝕃}.
  Proof.
    exact (pr2 (pr222 (pr222 (pr222 (pr222 𝕃))))).
  Qed.

End AccessorsLaws.

(**
 3. Other accessors for linear categories
 *)
Definition linear_category_cocommutative_comonoid
           (𝕃 : linear_category)
           (x : 𝕃)
  : commutative_comonoid 𝕃.
Proof.
  use make_commutative_comonoid.
  - exact (linear_category_bang 𝕃 x).
  - exact (linear_category_comult 𝕃 x).
  - exact (linear_category_counit 𝕃 x).
  - exact (linear_category_counitality x).
  - exact (!(linear_category_coassoc x)).
  - exact (linear_category_cocommutative x).
Defined.

Proposition linear_category_comult_comonoid_mor_struct
            (𝕃 : linear_category)
            (x : 𝕃)
  : comonoid_mor_struct
      𝕃
      (linear_category_cocommutative_comonoid 𝕃 x)
      (linear_category_cocommutative_comonoid 𝕃
         (linear_category_cocommutative_comonoid 𝕃 x))
      (δ (linear_category_bang 𝕃) x).
Proof.
  use make_is_comonoid_mor ; cbn.
  - exact (!(linear_category_comult_comonoid_mor_comult x)).
  - rewrite id_right.
    exact (!(linear_category_comult_comonoid_mor_counit x)).
Qed.

Definition linear_category_comult_nat_trans
           (𝕃 : linear_category)
  : linear_category_bang 𝕃
    ⟹
    linear_category_bang 𝕃∙ diag_functor 𝕃.
Proof.
  use make_nat_trans.
  - exact (λ x, linear_category_comult 𝕃 x).
  - abstract
      (intros x y f ; cbn ;
       apply linear_category_comult_nat).
Defined.

Definition linear_category_counit_nat_trans
           (𝕃 : linear_category)
  : linear_category_bang 𝕃 ⟹ constant_functor _ _ I_{𝕃}.
Proof.
  use make_nat_trans.
  - exact (λ x, linear_category_counit 𝕃 x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_right ;
       apply linear_category_counit_nat).
Defined.

Definition linear_category_comult_is_mon_nat_trans
  (𝕃 : linear_category):
  is_mon_nat_trans (linear_category_bang_functor 𝕃)
    (comp_fmonoidal_lax (linear_category_bang_functor 𝕃) (diag_functor_fmonoidal_lax 𝕃))
    (linear_category_comult_nat_trans 𝕃).
Proof.
  split.
  - intros x y. apply linear_category_comult_preserves_tensor.
  - apply linear_category_comult_preserves_unit.
Defined.

Definition linear_category_counit_is_mon_nat_trans
  (𝕃 : linear_category):
  is_mon_nat_trans (linear_category_bang_functor 𝕃)
    (constant_functor_fmonoidal_lax _ (unit_monoid 𝕃)) (linear_category_counit_nat_trans 𝕃).
Proof.
  split.
  - intros x y. apply linear_category_counit_preserves_tensor.
  - apply linear_category_counit_preserves_unit.
Qed.

Definition linear_category_comult_coalgebra_morphism
  (𝕃 : linear_category) (x : 𝕃)
  :  CoAlg_category (linear_category_bang 𝕃)
        ⟦ ((linear_category_bang 𝕃) x) ,, δ (linear_category_bang 𝕃) x,
          (linear_category_bang 𝕃 x ⊗ linear_category_bang 𝕃 x ,,
             (δ (linear_category_bang 𝕃) x #⊗ δ (linear_category_bang 𝕃) x)
             · mon_functor_tensor (linear_category_bang_functor 𝕃) _ _ )⟧.
Proof.
  use tpair.
  - exact (linear_category_comult 𝕃 x).
  - abstract (cbn; rewrite assoc; apply pathsinv0, linear_category_comult_coalgebra_mor).
Defined.

Definition linear_category_counit_coalgebra_morphism
  (𝕃 : linear_category) (x : 𝕃)
  : CoAlg_category (linear_category_bang 𝕃)
        ⟦ ((linear_category_bang 𝕃) x) ,, δ (linear_category_bang 𝕃) x,
          (I_{𝕃} ,, mon_functor_unit (linear_category_bang_functor 𝕃)) ⟧.
Proof.
  use tpair.
  - exact (linear_category_counit 𝕃 x).
  - abstract (apply pathsinv0, linear_category_counit_coalgebra_mor).
Defined.
