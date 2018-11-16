(** * Arrow categories

- Definition
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

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
              dirprod_pr1 fg · pr2 y = pr2 x · dirprod_pr2 fg).
    - intros x; cbn.
      exists (dirprodpair (identity _) (identity _)).
      exact (id_left _ @ !id_right _).
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
      refine (!assoc _ _ _ @ _).
      refine (maponpaths _ (pr2 g) @ _).
      refine (_ @ !assoc _ _ _).
      refine (_ @ maponpaths (fun x => x · _) (pr2 f)).
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
