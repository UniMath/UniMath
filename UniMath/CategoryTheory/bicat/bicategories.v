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

Variable C : prebicategory.

Definition bcat_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists C.
  exact (λ a b, homprecat a b).
Defined.

Definition bcat_cell_struct : bicat_cell_struct bcat_precategory_ob_mor
  := λ (a b : C) (f g : homprecat a b), (homprecat a b) ⟦ f, g ⟧.

Definition bcat_ob_mor_cells : ∑ (C : precategory_ob_mor), bicat_cell_struct C.
Proof.
  exists bcat_precategory_ob_mor.
  exact bcat_cell_struct.
Defined.

Definition bcat_cells_1_id_comp : ∑ C : bicat_ob_mor_cells, precategory_id_comp C.
Proof.
  exists bcat_ob_mor_cells. split.
  - simpl. intros. exact (identity_1mor _).
  - simpl. intros a b c f g. exact (compose_1mor f g).
Defined.

Definition bcat_2_id_comp_struct : bicat_2_id_comp_struct bcat_cells_1_id_comp.
Proof.
  repeat split; simpl; unfold bcat_cell_struct.
  - (* 2-unit *)
    intros. exact (identity _).
  - (* left unitor *)
    intros.
    set (p := left_unitor_trans a b).
    unfold left_unitor_trans_type in p.
    exact (p f).
  - (* right unitor *)
    intros.
    set (p := right_unitor_trans a b).
    unfold right_unitor_trans_type in p.
    exact (p f).
  - (* left inverse unitor *)
    intros. exact (inv_from_iso (left_unitor f)).
  - (* right inverse unitor *)
    intros. exact (inv_from_iso (right_unitor f)).
  - (* right associator *)
    intros. exact (inv_from_iso (associator f g h)).
  - (* left associator *)
    intros.
    exact (associator_2mor f g h).
  - (* vertical composition *)
    intros a b f g h x y.
    exact (x · y).
  - (* left whiskering *)
    intros a b c f g1 g2 x.
    exact (compose_2mor_horizontal (identity f) x).
  - (* right whiskering *)
    intros a b c f1 f2 g x.
    exact (compose_2mor_horizontal x (identity g)).
Defined.

Definition bcat_data : ∑ C, bicat_2_id_comp_struct C.
Proof.
  exists bcat_cells_1_id_comp.
  exact bcat_2_id_comp_struct.
Defined.

End unfold_data.
