(** **********************************************************

Ralph Matthes

2022
*)

(** **********************************************************

Contents :

- constructs a displayed monoidal category that is displayed over a cartesian monoidal category with the displayed tensor and displayed unit coming from displayed binary products and displayed terminal objects

 ************************************************************)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.

Require Import UniMath.CategoryTheory.Monoidal.CartesianMonoidalCategoriesWhiskered.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import MonoidalNotations.
Import DisplayedBifunctorNotations.

Section FixADisplayedCategory.

  Context {C : category} (CP : BinProducts C) (terminal : Terminal C)
    (D : disp_cat C) (dP : dispBinProducts D CP) (dterminal : dispTerminal D terminal).

  Local Definition M : monoidal C := cartesianmonoidalcat C CP terminal.

  Definition DCM_tensor_data : disp_bifunctor_data M D D D.
  Proof.
    use make_disp_bifunctor_data.
    - intros c d cc dd.
      exact (dispBinProductObject D (CP c d) (dP c d cc dd)).
    - intros c d1 d2 g cc dd1 dd2 gg.
      exact (dispBinProductOfArrows _ _ _ (id_disp cc) gg).
    - intros c1 c2 d f cc1 cc2 dd ff.
      exact (dispBinProductOfArrows _ _ _ ff (id_disp dd)).
  Defined.

  Definition DCM_tensor_laws : is_disp_bifunctor DCM_tensor_data.
  Proof.
  Admitted.

  Definition DCM_tensor : disp_tensor D M.
  Proof.
    use make_disp_bifunctor.
    - exact DCM_tensor_data.
    - exact DCM_tensor_laws.
  Defined.

  Definition DCM_unit : D I_{ M}.
  Proof.
  Admitted.

  Definition DCM_leftunitor_data : disp_leftunitor_data DCM_tensor DCM_unit.
  Proof.
  Admitted.

  Definition DCM_leftunitorinv_data : disp_leftunitorinv_data DCM_tensor DCM_unit.
  Proof.
  Admitted.

  Definition DCM_rightunitor_data : disp_rightunitor_data DCM_tensor DCM_unit.
  Proof.
  Admitted.

  Definition DCM_rightunitorinv_data : disp_rightunitorinv_data DCM_tensor DCM_unit.
  Proof.
  Admitted.

  Definition DCM_associator_data : disp_associator_data DCM_tensor.
  Proof.
  Admitted.

  Definition DCM_associatorinv_data : disp_associatorinv_data DCM_tensor.
  Proof.
  Admitted.

  Definition DCM_data : disp_monoidal_data D M.
  Proof.
    exists DCM_tensor. exists DCM_unit.
    repeat split.
    - exact DCM_leftunitor_data.
    - exact DCM_leftunitorinv_data.
    - exact DCM_rightunitor_data.
    - exact DCM_rightunitorinv_data.
    - exact DCM_associator_data.
    - exact DCM_associatorinv_data.
  Defined.

  Lemma DCM_laws : disp_monoidal_laws DCM_data.
  Proof.
    repeat split.

  Admitted.

  Definition displayedcartesianmonoidalcat: disp_monoidal D M := DCM_data ,, DCM_laws.


End FixADisplayedCategory.
