(** constructs the full symmetric monoidal subcategory through a displayed monoidal category *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.FullMonoidalSubcategory.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section FullSubcategory.

  Import BifunctorNotations.
  Import MonoidalNotations.

  Context {C: category} {V : monoidal C} (B : symmetric V)
    (P : C -> UU) (Punit : P I_{V}) (Ptensor : ∏ x y, P x -> P y -> P (x ⊗_{V} y)).

Definition full_symmetric_monoidal_sub_disp_data :
  disp_braiding_data (full_monoidal_sub_disp V P Punit Ptensor) B.
Proof.
  intros c c' Pc Pc'. exact tt.
Defined.

Definition full_symmetric_monoidal_sub_disp :
  disp_symmetric (full_monoidal_sub_disp V P Punit Ptensor) B.
Proof.
  use tpair.
  - exact full_symmetric_monoidal_sub_disp_data.
  - abstract (repeat split; try red; intros; apply isProofIrrelevantUnit).
Defined.

Definition full_symmetric_monoidal_subcat
  : symmetric (total_monoidal (full_monoidal_sub_disp V P Punit Ptensor))
  :=  total_symmetric (full_monoidal_sub_disp V P Punit Ptensor)
        full_symmetric_monoidal_sub_disp.

End FullSubcategory.
