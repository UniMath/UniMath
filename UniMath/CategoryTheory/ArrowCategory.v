(** * Arrow categories *)

(** ** Contents

  - Definition
  - As a comma category
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.CommaCategories.
Require Import UniMath.CategoryTheory.Adjunctions.

Local Open Scope cat.

(** ** Definition *)

Section Defn.
  Definition arrow_precategory_data (C : precategory) : precategory_data.
  Proof.
    use precategory_data_pair.
    - use precategory_ob_mor_pair.
      + exact (∑ (a : ob C × ob C), dirprod_pr1 a --> dirprod_pr2 a).
      + intros x y.
        (** The commutative square
            <<
              pr1 x   --->   pr1 y
                |             |
                |             |
            pr1 pr2 x ---> pr1 pr2 y
            >>
         *)
        exact (∑ fg : dirprod_pr1 (pr1 x) --> dirprod_pr1 (pr1 y) ×
                      dirprod_pr2 (pr1 x) --> dirprod_pr2 (pr1 y),
              pr2 x · dirprod_pr2 fg = dirprod_pr1 fg · pr2 y).
    - intros x; cbn.
      exists (dirprodpair (identity _) (identity _)).
      exact (id_right _ @ !id_left _).
    - intros x y z f g; cbn in *.
      exists (dirprodpair (dirprod_pr1 (pr1 f) · dirprod_pr1 (pr1 g))
                     (dirprod_pr2 (pr1 f) · dirprod_pr2 (pr1 g))).
      (** Composing commutative squares
          <<
            pr1 x   --->   pr1 y    --->   pr1 z
              |             |                |
              |      f      |        g       |
              |             |                |
          pr1 pr2 x ---> pr1 pr2 y  ---> pr1 pr2 z
          >>
        *)
      cbn.
      refine (assoc _ _ _ @ _).
      refine (maponpaths (fun x => x · _) (pr2 f) @ _).
      refine (_ @ assoc _ _ _).
      refine (_ @ maponpaths _ (pr2 g)).
      apply pathsinv0.
      apply assoc.
  Defined.

  Definition arrow_category (C : category) : category.
  Proof.
    use category_pair.
    - use mk_precategory_one_assoc; [apply (arrow_precategory_data C)|].
      unfold is_precategory_one_assoc.
      split; [split|].
      + intros a b f.
        unfold arrow_precategory_data in *; cbn in *.
        apply subtypeEquality.
        * intro; apply homset_property.
        * apply pathsdirprod; apply id_left.
      + intros a b f.
        unfold arrow_precategory_data in *; cbn in *.
        apply subtypeEquality.
        * intro; apply homset_property.
        * apply pathsdirprod; apply id_right.
      + intros a b c d f g h.
        apply subtypeEquality; [intro; apply homset_property|].
        apply pathsdirprod; apply assoc.
    - intros a b.
      apply isaset_total2.
      + apply isaset_dirprod; apply homset_property.
      + intro.
        apply hlevelntosn.
        apply homset_property.
  Defined.
End Defn.

(** ** As a comma category *)

Definition arrow_category_eq_comma_category (C : category) :
  comma_category (functor_identity C) (functor_identity C)
  = arrow_category C.
Proof.
  apply subtypeEquality.
  - intro.
    do 2 (apply impred; intro).
    apply isapropisaset.
  - use total2_paths_f.
    + cbn.
      use total2_paths_f.
      * reflexivity.
      * apply pathsdirprod.
        -- apply funextsec; intro.
           use total2_paths_f; [reflexivity|].
           apply proofirrelevance, homset_property.
        -- do 5 (apply funextsec; intro).
           use total2_paths_f; [reflexivity|].
           apply proofirrelevance, homset_property.
    + apply proofirrelevance.
      apply isaprop_is_precategory.
      apply (pr2 (arrow_category C)).
Qed.