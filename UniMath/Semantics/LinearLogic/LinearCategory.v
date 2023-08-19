(****************************************************************************

 Linear categories

 In this file, we define linear categories.

 Note that the laws in [linear_category_laws] are written out explicitly.

 Contents
 1. Data of linear categories
 2. Laws of linear categories

 ****************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.

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

Coercion linear_category_data_to_sym_mon_closed_cat
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
  := (* naturality of comultiplication *)
     (∏ (x y : 𝕃)
        (f : x --> y),
      #(linear_category_bang 𝕃) f
      · linear_category_comult 𝕃 y
      =
      linear_category_comult 𝕃 x
      · (#(linear_category_bang 𝕃) f #⊗ #(linear_category_bang 𝕃) f))
     ×
     (* naturality of counit *)
     (∏ (x y : 𝕃)
        (f : x --> y),
      #(linear_category_bang 𝕃) f · linear_category_counit 𝕃 y
      =
      linear_category_counit 𝕃 x)
     ×
     (* the comultiplication is a coalgebra morphism *)
     (∏ (x : 𝕃),
      linear_category_comult 𝕃 x
      · (δ (linear_category_bang 𝕃) x #⊗ δ (linear_category_bang 𝕃) x)
      · mon_functor_tensor (linear_category_bang_functor 𝕃) _ _
      =
      δ (linear_category_bang 𝕃) x
      · #(linear_category_bang 𝕃) (linear_category_comult 𝕃 x))
     ×
     (* the counit is a coalgebra morphism *)
     (∏ (x : 𝕃),
      linear_category_counit 𝕃 x
      · mon_functor_unit (linear_category_bang_functor 𝕃)
      =
      δ (linear_category_bang 𝕃) x
      · #(linear_category_bang 𝕃) (linear_category_counit 𝕃 x))
     ×
     (* the comultiplication of the comonad is a comonoid morphism (counit) *)
     (∏ (x : 𝕃),
      δ (linear_category_bang 𝕃) x
      · linear_category_counit 𝕃 (linear_category_bang 𝕃 x)
      =
      linear_category_counit 𝕃 x)
     ×
     (* the comultiplication of the comonad is a comonoid morphism (comultiplication) *)
     (∏ (x : 𝕃),
      δ (linear_category_bang 𝕃) x
      · linear_category_comult 𝕃 (linear_category_bang 𝕃 x)
      =
      linear_category_comult 𝕃 x
      · (δ (linear_category_bang 𝕃) x #⊗ δ (linear_category_bang 𝕃) x))
     ×
     (* coassociativity *)
     (∏ (x : 𝕃),
      linear_category_comult 𝕃 x
      · (identity _ #⊗ linear_category_comult 𝕃 x)
      =
      linear_category_comult 𝕃 x
      · (linear_category_comult 𝕃 x #⊗ identity _)
      · mon_lassociator _ _ _)
     ×
     (* counitality *)
     (∏ (x : 𝕃),
      linear_category_comult 𝕃 x
      · (linear_category_counit 𝕃 x #⊗ identity _)
      · mon_lunitor _
      =
      identity _)
     ×
     (* cocommutativity *)
     (∏ (x : 𝕃),
      linear_category_comult 𝕃 x
      · sym_mon_braiding 𝕃 _ _
      =
      linear_category_comult 𝕃 x).

Definition linear_category
  : UU
  := ∑ (𝕃 : linear_category_data), linear_category_laws 𝕃.

Definition make_linear_category
           (𝕃 : linear_category_data)
           (H : linear_category_laws 𝕃)
  : linear_category
  := 𝕃 ,, H.

Coercion linear_category_to_data
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

  Proposition linear_category_counit_comonoid_mor_counit
              (x : 𝕃)
    : δ (linear_category_bang 𝕃) x
      · linear_category_counit 𝕃 (linear_category_bang 𝕃 x)
      =
      linear_category_counit 𝕃 x.
  Proof.
    exact (pr122 (pr222 𝕃) x).
  Qed.

  Proposition linear_category_counit_comonoid_mor_comult
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
    exact (pr222 (pr222 (pr222 𝕃)) x).
  Qed.

  Definition linear_category_cocommutative_comonoid
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

  Proposition linear_category_counit_comonoid_mor_struct
              (x : 𝕃)
    : comonoid_mor_struct
        𝕃
        (linear_category_cocommutative_comonoid x)
        (linear_category_cocommutative_comonoid
           (linear_category_cocommutative_comonoid x))
        (δ (linear_category_bang 𝕃) x).
  Proof.
    use make_is_comonoid_mor ; cbn.
    - exact (!(linear_category_counit_comonoid_mor_comult x)).
    - rewrite id_right.
      exact (!(linear_category_counit_comonoid_mor_counit x)).
  Qed.
End AccessorsLaws.
