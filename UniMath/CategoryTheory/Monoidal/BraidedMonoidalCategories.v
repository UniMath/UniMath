(** Braided monoidal precategories.

   Authors: Mario Román, based on a previous implementation by Anthony Bordg.

   References: https://ncatlab.org/nlab/show/braided+monoidal+category#the_coherence_laws

**)

(** ** Contents:

   - braidings
   - hexagon equations
   - braided monoidal precategories
     - accessors
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Local Open Scope cat.

(** * Braidings *)
Section Braiding.

(** In this section, fix a monoidal category. *)
Context (MonM : monoidal_precat).
Let M        := monoidal_precat_precat MonM.
Let tensor   := monoidal_precat_tensor MonM.
Let α        := monoidal_precat_associator MonM.

Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

(* A braiding is a natural isomorphism from (- ⊗ =) to (= ⊗ -). *)
Definition braiding : UU := nat_iso tensor (tensor □ binswap_pair_functor).

(** * Hexagon equations. *)
Section HexagonEquations.

Context (braid : braiding).
Let γ := pr1 braid.
Let α₁ := pr1 α.
Let α₂ := pr1 (nat_iso_inv α).

Definition first_hexagon_eq : UU :=
  ∏ (a b c : M) ,
  (α₁ ((a , b) , c)) · (γ (a , (b ⊗ c))) · (α₁ ((b , c) , a))  =
  (γ (a , b) #⊗ (id c)) · (α₁ ((b , a) , c)) · ((id b) #⊗ γ (a , c)).

Definition second_hexagon_eq : UU :=
  ∏ (a b c : M) ,
  α₂ ((a , b) , c) · (γ (a ⊗ b , c)) · α₂ ((c , a) , b)  =
  ((id a) #⊗ γ (b , c)) · α₂ ((a , c) , b) · (γ (a , c) #⊗ (id b)).

End HexagonEquations.

End Braiding.

(** * Braided monoidal precategories *)
Definition braided_monoidal_precat : UU :=
  ∑ M : monoidal_precat ,
  ∑ γ : braiding M ,
  (first_hexagon_eq M γ) × (second_hexagon_eq M γ).

(** ** Accessors *)
Section Braided_Monoidal_Precat_Acessors.

Context (M : braided_monoidal_precat).

Definition braided_monoidal_precat_monoidal_precat := pr1 M.
Definition braided_monoidal_precat_braiding := pr1 (pr2 M).
Definition braided_monoidal_precat_first_hexagon_eq := pr1 (pr2 (pr2 M)).
Definition braided_monoidal_precat_second_hexagon_eq := pr2 (pr2 (pr2 M)).

End Braided_Monoidal_Precat_Acessors.

Coercion braided_monoidal_precat_monoidal_precat : braided_monoidal_precat >-> monoidal_precat.
