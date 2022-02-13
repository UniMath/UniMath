(* ----------------------------------------------------------------------------------- *)
(** ** Initial bicategory and proof that it's univalent.

   Note: UniMath.CategoryTheory.categories.StandardCategories has the definition of
   initial 1-category ([empty_category]).                                              *)
(* ----------------------------------------------------------------------------------- *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.AdjointUnique.

Local Open Scope cat.

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

  Definition initial_bicat_invertible_2cell
             {x y : initial_bicat}
             {f g : x --> y}
             (α : f ==> g)
    : is_invertible_2cell α.
  Proof.
    exact (fromempty x).
  Defined.

  Definition initial_bicat_adjoint_equivalence
             {x y : initial_bicat}
             (f : x --> y)
    : left_adjoint_equivalence f.
  Proof.
    exact (fromempty x).
  Defined.

  (** It is univalent *)
  Definition initial_bicat_is_univalent_2_1
    : is_univalent_2_1 initial_bicat.
  Proof.
    intros x.
    exact (fromempty x).
  Defined.

  Definition initial_bicat_is_univalent_2_0
    : is_univalent_2_0 initial_bicat.
  Proof.
    intros x.
    exact (fromempty x).
  Defined.

  Definition initial_bicat_is_univalent_2
    : is_univalent_2 initial_bicat.
  Proof.
    split.
    - exact initial_bicat_is_univalent_2_0.
    - exact initial_bicat_is_univalent_2_1.
  Defined.

End Initial_Bicategory.
