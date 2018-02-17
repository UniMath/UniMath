(* ========================================================================= *)
(* Every prebicategory of UniMath.CategoryTheory.bicategories is a           *)
(* prebicategory of UniMath.CategoryTheory.bicat.                            *)
(* ========================================================================= *)

Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.bicategories.prebicategory.

Require Import UniMath.CategoryTheory.bicat.bicat.

Open Scope cat.

(* ------------------------------------------------------------------------- *)
(* From bicategory structure to bicat structor.                              *)
(* ------------------------------------------------------------------------- *)

Section unfold_data.

(* Projections. *)

Variable C : prebicategory_data.

Local Definition C_id_comp : prebicategory_id_comp := pr1 C.

Local Definition C_ob_1mor_2mor : prebicategory_ob_1mor_2mor := pr1 C_id_comp.

Local Definition C0 : UU := pr1 C_ob_1mor_2mor.

Local Definition Chom : C0 → C0 → precategory := pr2 C_ob_1mor_2mor.

Local Definition C_id1 : ∏ a : C_ob_1mor_2mor, homprecat a a :=
  pr1 (pr2 C_id_comp).

Local Definition C_comp1
  : ∏ (a b c : C0),
    precategory_binproduct (homprecat a b) (homprecat b c) ⟶ homprecat a c
  := pr2 (pr2 C_id_comp).

Local Definition C_lassociator
  : ∏ a b c d : C0, associator_trans_type a b c d
  := pr1 (pr2 C).

Local Definition C_left_unitor
  : ∏ a b : C0, left_unitor_trans_type a b
  := pr1 (pr2 (pr2 C)).

Local Definition C_right_unitor
  : ∏ a b : C0, right_unitor_trans_type a b
  := pr2 (pr2 (pr2 C)).

(* Packing back into a bicat_data. *)

Definition bcat_precategory_ob_mor : precategory_ob_mor.
Proof.
  use (C0,, _). simpl.
  intros a b.
  exact (Chom a b).
Defined.

Definition bcat_cell_struct : bicat_cell_struct bcat_precategory_ob_mor
  := λ (a b : C0) (f g : Chom a b), (Chom a b) ⟦ f, g ⟧.

Definition bcat_ob_mor_cells : ∑ (C : precategory_ob_mor), bicat_cell_struct C.
Proof.
  refine (bcat_precategory_ob_mor,, _).
  exact bcat_cell_struct.
Defined.

(*
Definition bcat_cells_1_id_comp : ∑ C : bicat_ob_mor_cells, precategory_id_comp C.
Proof.
  refine (bcat_ob_mor_cells,, _).
  split.
  - simpl. intros.
 *)

End unfold_data.
