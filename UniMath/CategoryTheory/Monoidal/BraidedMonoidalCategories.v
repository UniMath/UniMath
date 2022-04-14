(** Braided monoidal precategories.

   Authors: Mario Román, based on a previous implementation by Anthony Bordg.

   References: https://ncatlab.org/nlab/show/braided+monoidal+category#the_coherence_laws

**)

(** ** Contents:

   - braidings
   - hexagon equations
   - braided monoidal categories
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
Context (MonM : monoidal_cat).

Local Definition tensor   := monoidal_cat_tensor MonM.
Local Definition α        := monoidal_cat_associator MonM.

Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

(* A braiding is a natural isomorphism from (- ⊗ =) to (= ⊗ -). *)
Definition braiding : UU := nat_z_iso tensor (binswap_pair_functor ∙ tensor).

(** * Hexagon equations. *)
Section HexagonEquations.

Context (braid : braiding).
Local Definition γ := pr1 braid.
Local Definition α₁ := pr1 α.
Local Definition α₂ := pr1 (nat_z_iso_inv α).

Definition first_hexagon_eq : UU :=
  ∏ (a b c : MonM) ,
  (α₁ ((a , b) , c)) · (γ (a , (b ⊗ c))) · (α₁ ((b , c) , a))  =
  (γ (a , b) #⊗ (id c)) · (α₁ ((b , a) , c)) · ((id b) #⊗ γ (a , c)).

Definition second_hexagon_eq : UU :=
  ∏ (a b c : MonM) ,
  α₂ ((a , b) , c) · (γ (a ⊗ b , c)) · α₂ ((c , a) , b)  =
  ((id a) #⊗ γ (b , c)) · α₂ ((a , c) , b) · (γ (a , c) #⊗ (id b)).

End HexagonEquations.

End Braiding.

(** * Braided monoidal categories *)
Definition braided_monoidal_cat : UU :=
  ∑ M : monoidal_cat ,
  ∑ γ : braiding M ,
  (first_hexagon_eq M γ) × (second_hexagon_eq M γ).

(** ** Accessors *)
Section Braided_Monoidal_Cat_Acessors.

Context (M : braided_monoidal_cat).

Definition braided_monoidal_cat_monoidal_cat := pr1 M.
Definition braided_monoidal_cat_braiding := pr1 (pr2 M).
Definition braided_monoidal_cat_first_hexagon_eq := pr1 (pr2 (pr2 M)).
Definition braided_monoidal_cat_second_hexagon_eq := pr2 (pr2 (pr2 M)).

End Braided_Monoidal_Cat_Acessors.

Coercion braided_monoidal_cat_monoidal_cat : braided_monoidal_cat >-> monoidal_cat.
