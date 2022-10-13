(** * Arrow categories *)

(** ** Contents

  - Definition
  - As a comma category
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.CommaCategories.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

(** ** Definition *)

Section Defn.
  Definition arrow_precategory_data (C : precategory) : precategory_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
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
      exists (make_dirprod (identity _) (identity _)).
      exact (id_right _ @ !id_left _).
    - intros x y z f g; cbn in *.
      exists (make_dirprod (dirprod_pr1 (pr1 f) · dirprod_pr1 (pr1 g))
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
    use make_category.
    - use make_precategory_one_assoc; [apply (arrow_precategory_data C)|].
      unfold is_precategory_one_assoc.
      split; [split|].
      + intros a b f.
        unfold arrow_precategory_data in *; cbn in *.
        apply subtypePath.
        * intro; apply homset_property.
        * apply pathsdirprod; apply id_left.
      + intros a b f.
        unfold arrow_precategory_data in *; cbn in *.
        apply subtypePath.
        * intro; apply homset_property.
        * apply pathsdirprod; apply id_right.
      + intros a b c d f g h.
        apply subtypePath; [intro; apply homset_property|].
        apply pathsdirprod; apply assoc.
    - intros a b.
      apply isaset_total2.
      + apply isaset_dirprod; apply homset_property.
      + intro.
        apply hlevelntosn.
        apply homset_property.
  Defined.

  Section IsIsoArrow.
    Context {C : category}
            {x y : arrow_category C}
            (f : x --> y)
            (Hf1 : is_z_isomorphism (pr11 f))
            (Hf2 : is_z_isomorphism (pr21 f)).

    Definition inv_arrow
      : y --> x.
    Proof.
      refine ((inv_from_z_iso (_,, Hf1) ,, inv_from_z_iso (_,, Hf2)) ,, _).
      abstract
        (cbn ;
         refine (!_) ;
         use z_iso_inv_on_left ;
         rewrite assoc' ;
         refine (!_) ;
         use z_iso_inv_on_right ;
         cbn ;
         exact (pr2 f)).
    Defined.

    Lemma is_z_iso_arrow_left_inv
      : f · inv_arrow = identity x.
    Proof.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use pathsdirprod ; cbn.
      - exact (z_iso_inv_after_z_iso (make_z_iso' _ Hf1)).
      - exact (z_iso_inv_after_z_iso (make_z_iso' _ Hf2)).
    Qed.

    Lemma is_z_iso_arrow_right_inv
      : inv_arrow · f = identity y.
    Proof.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use pathsdirprod ; cbn.
      - exact (z_iso_after_z_iso_inv (make_z_iso' _ Hf1)).
      - exact (z_iso_after_z_iso_inv (make_z_iso' _ Hf2)).
    Qed.

    Definition is_z_iso_arrow
      : is_z_isomorphism f.
    Proof.
      exists inv_arrow.
      split.
      - exact is_z_iso_arrow_left_inv.
      - exact is_z_iso_arrow_right_inv.
    Defined.
  End IsIsoArrow.
End Defn.

(** ** As a comma category *)
Section ArrowCategoryEquivCommaCategory.
  Context (C : category).

  Definition arrow_category_to_comma_category_data
    : functor_data
        (arrow_category C)
        (comma (functor_identity C) (functor_identity C)).
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - cbn.
      exact (λ f g p, p).
  Defined.

  Definition arrow_category_to_comma_category_is_functor
    : is_functor arrow_category_to_comma_category_data.
  Proof.
    split.
    - intros f.
      cbn.
      refine (maponpaths (λ z, _ ,, z) _).
      apply homset_property.
    - intros f g h p q.
      cbn.
      refine (maponpaths (λ z, _ ,, z) _).
      apply homset_property.
  Qed.

  Definition arrow_category_to_comma_category
    : arrow_category C ⟶ comma (functor_identity C) (functor_identity C).
  Proof.
    use make_functor.
    - exact arrow_category_to_comma_category_data.
    - exact arrow_category_to_comma_category_is_functor.
  Defined.

  Definition comma_category_to_arrow_category_data
    : functor_data (comma (functor_identity C) (functor_identity C)) (arrow_category C).
  Proof.
    use make_functor_data.
    - exact (λ f, f).
    - cbn.
      exact (λ f g p, p).
  Defined.

  Definition comma_category_to_arrow_category_is_functor
    : is_functor comma_category_to_arrow_category_data.
  Proof.
    split.
    - intros f.
      cbn.
      refine (maponpaths (λ z, _ ,, z) _).
      apply homset_property.
    - intros f g h p q.
      cbn.
      refine (maponpaths (λ z, _ ,, z) _).
      apply homset_property.
  Qed.

  Definition comma_category_to_arrow_category
    : comma (functor_identity C) (functor_identity C) ⟶ arrow_category C.
  Proof.
    use make_functor.
    - exact comma_category_to_arrow_category_data.
    - exact comma_category_to_arrow_category_is_functor.
  Defined.

  Definition arrow_category_equiv_comma_category_unit_data
    : nat_trans_data
        (functor_identity (arrow_category C))
        (arrow_category_to_comma_category ∙ comma_category_to_arrow_category).
  Proof.
    cbn.
    refine (λ x, (identity _ ,, identity _) ,, _).
    abstract
      (cbn ;
       rewrite id_left, id_right ;
       apply idpath).
  Defined.

  Definition arrow_category_equiv_comma_category_unit_is_nat_trans
    : is_nat_trans
        _ _
        arrow_category_equiv_comma_category_unit_data.
  Proof.
    intros f g p.
    use subtypePath.
    {
      intro ; apply homset_property.
    }
    cbn.
    use pathsdirprod.
    - rewrite id_left, id_right.
      apply idpath.
    - rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition arrow_category_equiv_comma_category_unit
    : functor_identity _
      ⟹
      arrow_category_to_comma_category ∙ comma_category_to_arrow_category.
  Proof.
    use make_nat_trans.
    - exact arrow_category_equiv_comma_category_unit_data.
    - exact arrow_category_equiv_comma_category_unit_is_nat_trans.
  Defined.

  Definition arrow_category_equiv_comma_category_counit_data
    : nat_trans_data
        (comma_category_to_arrow_category ∙ arrow_category_to_comma_category)
        (functor_identity (comma (functor_identity C) (functor_identity C))).
  Proof.
    cbn.
    refine (λ x, (identity _ ,, identity _) ,, _).
    abstract
      (cbn ;
       rewrite id_left, id_right ;
       apply idpath).
  Defined.

  Definition arrow_category_equiv_comma_category_counit_is_nat_trans
    : is_nat_trans
        _ _
        arrow_category_equiv_comma_category_counit_data.
  Proof.
    intros f g p.
    use subtypePath.
    {
      intro ; apply homset_property.
    }
    cbn.
    use pathsdirprod.
    - rewrite id_left, id_right.
      apply idpath.
    - rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition arrow_category_equiv_comma_category_counit
    : comma_category_to_arrow_category ∙ arrow_category_to_comma_category
      ⟹
      functor_identity (comma (functor_identity C) (functor_identity C)).
  Proof.
    use make_nat_trans.
    - exact arrow_category_equiv_comma_category_counit_data.
    - exact arrow_category_equiv_comma_category_counit_is_nat_trans.
  Defined.

  Definition arrow_category_comma_category_adjunction
    : form_adjunction
        arrow_category_to_comma_category
        comma_category_to_arrow_category
        arrow_category_equiv_comma_category_unit
        arrow_category_equiv_comma_category_counit.
  Proof.
    use make_form_adjunction.
    - intro x.
      use subtypePath.
      {
        intro ; apply homset_property.
      }
      cbn.
      use pathsdirprod.
      + apply id_right.
      + apply id_right.
    - intro x.
      use subtypePath.
      {
        intro ; apply homset_property.
      }
      cbn.
      use pathsdirprod.
      + apply id_right.
      + apply id_right.
  Qed.

  Definition arrow_category_equiv_comma_category
    : adj_equivalence_of_cats arrow_category_to_comma_category.
  Proof.
    use make_adj_equivalence_of_cats.
    - exact comma_category_to_arrow_category.
    - exact arrow_category_equiv_comma_category_unit.
    - exact arrow_category_equiv_comma_category_counit.
    - exact arrow_category_comma_category_adjunction.
    - split.
      + intro ; cbn.
        use is_z_iso_arrow.
        * apply identity_is_z_iso.
        * apply identity_is_z_iso.
      + intro ; cbn.
        use is_z_iso_comma.
        * apply identity_is_z_iso.
        * apply identity_is_z_iso.
  Defined.
End ArrowCategoryEquivCommaCategory.
