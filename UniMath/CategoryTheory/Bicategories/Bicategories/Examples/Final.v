Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.EquivToAdjequiv.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.

Local Open Scope cat.
Local Open Scope bicategory_scope.

(* ----------------------------------------------------------------------------------- *)
(** ** Final bicategory.

   Note: UniMath.CategoryTheory.categories.StandardCategories has the definition of
   final 1-category ([unit_category]).                                                *)
(* ----------------------------------------------------------------------------------- *)

Section Final_Bicategory.
  Definition final_1_id_comp_cells : prebicat_1_id_comp_cells
    := tpair (λ C : precategory_data, prebicat_2cell_struct C)
             unit_category
             (λ (a b : unit_category) (f g : a --> b), unit).

  Definition final_2_id_comp_struct
    : prebicat_2_id_comp_struct final_1_id_comp_cells.
  Proof.
    repeat split; exact tounit.
  Defined.

  Definition final_prebicat_data : prebicat_data
    := final_1_id_comp_cells,, final_2_id_comp_struct.

  Lemma final_bicat_laws : prebicat_laws final_prebicat_data.
  Proof.
    repeat apply dirprodpair; intros; apply isProofIrrelevantUnit.
  Qed.

  Definition final_prebicat : prebicat
    := final_prebicat_data,, final_bicat_laws.

  Definition cellset_final_prebicat
    : isaset_cells final_prebicat.
  Proof.
    red. cbn. intros. exact isasetunit.
  Qed.

  Definition final_bicat : bicat
    := final_prebicat,, cellset_final_prebicat.

  Definition final_bicat_invertible_2cell
             {x y : final_bicat}
             {f g : x --> y}
             (α : f ==> g)
    : is_invertible_2cell α.
  Proof.
    refine (tt ,, (_ ,, _)) ; reflexivity.
  Defined.

  Definition final_bicat_adjoint_equivalence
             {x y : final_bicat}
             (f : x --> y)
    : left_adjoint_equivalence f.
  Proof.
    use tpair.
    - use tpair.
      + exact (!f).
      + exact (tt ,, tt).
    - split ; split ; cbn.
      + reflexivity.
      + reflexivity.
      + apply final_bicat_invertible_2cell.
      + apply final_bicat_invertible_2cell.
  Defined.

  (** It is univalent *)
  Definition final_bicat_is_univalent_2_1
    : is_univalent_2_1 final_bicat.
  Proof.
    intros x y p q.
    use isweqimplimpl.
    - intros.
      apply isasetaprop.
      apply isapropunit.
    - apply isasetaprop.
      apply isasetaprop.
      exact isapropunit.
    - simple refine (isaprop_total2 (_ ,, _) (λ η , _ ,, _)).
      + exact isapropunit.
      + apply isaprop_is_invertible_2cell.
  Defined.

  Definition final_bicat_is_univalent_2_0
    : is_univalent_2_0 final_bicat.
  Proof.
    intros x y.
    apply isweqimplimpl.
    - intros.
      induction x, y.
      reflexivity.
    - apply isasetaprop.
      exact isapropunit.
    - simple refine (isaprop_total2 (_ ,, _) (λ η , _ ,, _)).
      + apply isasetaprop.
        exact isapropunit.
      + apply isaprop_left_adjoint_equivalence.
        exact final_bicat_is_univalent_2_1.
  Defined.
End Final_Bicategory.