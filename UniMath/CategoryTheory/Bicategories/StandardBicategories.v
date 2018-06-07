(* =================================================================================== *)
(** * Various examples of bicategories.                                                *)
(* =================================================================================== *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.

Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Initial bicategory.

   Note: UniMath.CategoryTheory.categories.StandardCategories has the definition of
   initial 1-category ([empty_category]).                                              *)
(* ----------------------------------------------------------------------------------- *)

Section Initial_Bicategory.

  Definition initial_1_id_comp_cells : prebicat_1_id_comp_cells
    := tpair (λ C : precategory_data, prebicat_2cell_struct C)
             empty_category
             (λ (a b : empty_category) (f g : a --> b), ∅).

  Definition initial_2_id_comp_struct
    : prebicat_2_id_comp_struct initial_1_id_comp_cells.
  Proof.
    repeat split; exact (λ u : ∅, fromempty u).
  Defined.

  Definition initial_prebicat_data : prebicat_data
    := initial_1_id_comp_cells,, initial_2_id_comp_struct.

  Lemma initial_bicat_laws : prebicat_laws initial_prebicat_data.
  Proof.
    repeat split; exact (λ u : ∅, fromempty u).
  Qed.

  Definition initial_prebicat : prebicat
    := initial_prebicat_data,, initial_bicat_laws.

  Definition cellset_initial_prebicat
    : isaset_cells initial_prebicat
    := λ u : ∅, fromempty u.

  Definition initial_bicat : bicat
    := initial_prebicat,, cellset_initial_prebicat.

End Initial_Bicategory.

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

End Final_Bicategory.
