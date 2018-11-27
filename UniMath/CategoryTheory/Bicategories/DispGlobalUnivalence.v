Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.DispUnivalence.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Section internal_adjoint_equivalences.

Context {B : bicat} {D : disp_bicat B}.
Local Definition E := total_bicat D.

Definition disp_internal_left_adjoint_data {a b : B}
           {f : a --> b}
           (j : internal_left_adjoint_data f)
           {aa : D a} {bb : D b}
           (g := internal_right_adjoint j)
           (ff : aa -->[f] bb)
  : UU
  := ∑ (gg : bb -->[g] aa), disp_internal_adjunction_over j ff gg.


Coercion disp_internal_adjunction_over_from_left_adjoint
         {a b : B}
         {f : a --> b}
         {j : internal_left_adjoint_data f}
         {aa : D a} {bb : D b}
         {ff : aa -->[f] bb}
         (jj : disp_internal_left_adjoint_data j ff) :
  disp_internal_adjunction_over j ff (pr1 jj) := pr2 jj.

Definition is_disp_internal_left_adjoint
         {a b : B}
         {f : a --> b}
         (j : is_internal_left_adjoint f)
         {aa : D a} {bb : D b}
         (ff : aa -->[f] bb)
  : UU
  := ∑ (jj : disp_internal_left_adjoint_data j ff),
     is_disp_internal_adjunction j jj.

(* Coercion disp_internal_adjunction_from_left_adjoint *)
(*          {a b : B} *)
(*          {f : a --> b} *)
(*          (j : is_internal_left_adjoint f) *)
(*          {aa : D a} {bb : D b} *)
(*          (ff : aa -->[f] bb) *)
(*          (jj : is_disp_internal_left_adjoint j ff) *)
(*   : @disp_internal_adjunction _ D a b j. *)

End internal_adjoint_equivalences.
