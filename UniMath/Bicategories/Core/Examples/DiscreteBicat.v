(*****************************************************************************

 Discrete bicategories

 Every category gives rise to a discrete bicategory, namely the bicategory
 whose objects and 1-cells are objects and morphisms in the category
 respectively, and whose 2-cells are equalities of morphisms in the category.
 We show that this bicategory is discrete (locally univalent, all 2-cells are
 invertible, and all 2-cells with the same source and target are equal).

 Contents
 1. The discrete bicategory
 2. The discrete bicategory is discrete
 3. Global univalence of the discrete bicategory

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Discreteness.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.

Section CatToBicat.
  Context (C : category).

  (** * 1. The discrete bicategory *)
  Definition cat_to_prebicat_1_id_comp_cells
    : prebicat_1_id_comp_cells.
  Proof.
    simple refine (_ ,, _).
    - exact C.
    - exact (λ x y f g, f = g).
  Defined.

  Definition cat_to_prebicat_2_id_comp_struct
    : prebicat_2_id_comp_struct cat_to_prebicat_1_id_comp_cells.
  Proof.
    repeat split.
    - intros x y f ; cbn.
      apply id_left.
    - intros x y f ; cbn.
      apply id_right.
    - intros x y f ; cbn.
      exact (!(id_left _)).
    - intros x y f ; cbn.
      exact (!(id_right _)).
    - intros w x y z f g h ; cbn.
      apply assoc'.
    - intros w x y z f g h ; cbn.
      apply assoc.
    - intros x y f g h p q ; cbn.
      exact (p @ q).
    - intros x y z f g₁ g₂ p ; cbn.
      exact (maponpaths (λ z, f · z) p).
    - intros x y z f₁ f₂ g p ; cbn.
      exact (maponpaths (λ z, z · g) p).
  Qed.

  Definition cat_to_prebicat_data
    : prebicat_data.
  Proof.
    simple refine (_ ,, _).
    - exact cat_to_prebicat_1_id_comp_cells.
    - exact cat_to_prebicat_2_id_comp_struct.
  Defined.

  Proposition cat_to_prebicat_laws
    : prebicat_laws cat_to_prebicat_data.
  Proof.
    repeat split ; intro ; intros ; apply homset_property.
  Qed.

  Definition cat_to_prebicat
    : prebicat.
  Proof.
    simple refine (_ ,, _).
    - exact cat_to_prebicat_data.
    - exact cat_to_prebicat_laws.
  Defined.

  Definition cat_to_bicat
    : bicat.
  Proof.
    refine (cat_to_prebicat ,, _).
    abstract
      (intros x y f g p q ;
       apply isasetaprop ;
       apply homset_property).
  Defined.

  (** * 2. The discrete bicategory is discrete *)
  Proposition isaprop_2cells_cat_to_bicat
    : isaprop_2cells cat_to_bicat.
  Proof.
    intros x y f g p q.
    apply homset_property.
  Qed.

  Proposition locally_groupoid_cat_to_bicat
    : locally_groupoid cat_to_bicat.
  Proof.
    intros x y f g α.
    refine (!α ,, _ ,, _).
    - apply isaprop_2cells_cat_to_bicat.
    - apply isaprop_2cells_cat_to_bicat.
  Defined.

  Proposition is_univalent_2_1_cat_to_bicat
    : is_univalent_2_1 cat_to_bicat.
  Proof.
    intros x y f g.
    use isweqimplimpl.
    - exact (λ p, pr1 p).
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_invertible_2cell.
      + intros.
        apply homset_property.
  Qed.

  Proposition is_discrete_cat_to_bicat
    : is_discrete_bicat cat_to_bicat.
  Proof.
    repeat split.
    - exact is_univalent_2_1_cat_to_bicat.
    - exact locally_groupoid_cat_to_bicat.
    - exact isaprop_2cells_cat_to_bicat.
  Qed.

  (** * 3. Global univalence of the discrete bicategory *)
  Proposition is_univalent_2_0_cat_to_bicat
              (HC : is_univalent C)
    : is_univalent_2_0 cat_to_bicat.
  Proof.
    use discrete_bicat_univalent_2_0.
    - exact is_discrete_cat_to_bicat.
    - refine (transportf is_univalent _ HC).
      use category_eq.
      apply idpath.
  Qed.
End CatToBicat.
