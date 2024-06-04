(*****************************************************************************************

 Posetal categories

 Posetal categories, also known as thin categories, are univalent categories for which
 there is at most one morphism between every two objects. Equivalently, one could say that
 a posetal category is a univalent category for which every hom set `x --> y` is a homotopy
 proposition.

 The type of posetal categories is equivalent to the type of posets. For this reason, one
 might wonder why one would look at this notion: after all, why not just use posets? Well,
 it depends on the situation. By using posetal categories, one can very directly reuse all
 of the infrastructure that has been developed for categories. This allows one to very
 concisely define more advanced notions such as quantales: a quantale is a symmetric closed
 monoidal category that is both complete and cocomplete and also a posetal category. With
 that definition in place, we can also reuse everything that has been developed for enriched
 categories, and we obtain the notion of a quantale-enriched set. We can also reuse everything
 that has been developed about enriched profunctors and so on.

 Content
 1. Posetal categories
 2. Every posetal category is a poset
 3. Every poset is a posetal category
 4. Equivalence between posetal categories and posets

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.CategoryEquality.

Local Open Scope cat.

(** * 1. Posetal categories *)
Definition is_poset_category
           (C : univalent_category)
  : UU
  := ∏ (x y : C), isaprop (x --> y).

Proposition isaprop_is_poset_category
            (C : univalent_category)
  : isaprop (is_poset_category C).
Proof.
  do 2 (use impred ; intro).
  apply isapropisaprop.
Qed.

Definition poset_category
  : UU
  := ∑ (C : univalent_category), is_poset_category C.

Definition make_poset_category
           (C : univalent_category)
           (HC : is_poset_category C)
  : poset_category
  := C ,, HC.

Coercion poset_category_to_category
         (C : poset_category)
  : univalent_category
  := pr1 C.

Definition is_poset_poset_category
           (C : poset_category)
  : is_poset_category C
  := pr2 C.

Definition isaset_ob_poset
           (C : poset_category)
  : isaset C.
Proof.
  intros x y.
  use (isofhlevelweqb 1 (make_weq _ (univalent_category_is_univalent C x y))).
  use isaproptotal2.
  - intro.
    apply isaprop_is_z_isomorphism.
  - intros.
    apply is_poset_poset_category.
Qed.

Definition z_iso_poset_category
           {C : poset_category}
           {x y : C}
           (f : x --> y)
           (g : y --> x)
  : z_iso x y.
Proof.
  use make_z_iso.
  - exact f.
  - exact g.
  - split.
    + apply is_poset_poset_category.
    + apply is_poset_poset_category.
Qed.

Definition ob_eq_poset_category
           {C : poset_category}
           {x y : C}
           (f : x --> y)
           (g : y --> x)
  : x = y.
Proof.
  use (isotoid C (univalent_category_is_univalent C)).
  exact (z_iso_poset_category f g).
Defined.

(** * 2. Every posetal category is a poset *)
Definition poset_category_to_poset
           (C : poset_category)
  : Poset.
Proof.
  use make_Poset.
  - use make_hSet.
    + exact C.
    + exact (isaset_ob_poset C).
  - use make_PartialOrder.
    + refine (λ x y, make_hProp (x --> y) _).
      apply is_poset_poset_category.
    + repeat split.
      * abstract
          (intros x y z f g ; cbn in * ;
           exact (f · g)).
      * abstract
          (intro x ; cbn in * ;
           apply identity).
      * abstract
          (intros x y f g ; cbn in * ;
           exact (ob_eq_poset_category f g)).
Defined.

(** * 3. Every poset is a posetal category *)
Section ToPosetCategory.
  Context (P : Poset).

  Definition poset_to_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - use make_precategory_ob_mor.
      + exact P.
      + exact (λ x y, x ≤ y)%poset.
    - use isrefl_posetRelation.
    - use istrans_posetRelation.
  Defined.

  Definition poset_to_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact poset_to_precategory_data.
    - abstract (repeat split ; intro ; intros ; apply propproperty).
  Defined.

  Definition poset_to_category
    : category.
  Proof.
    use make_category.
    - exact poset_to_precategory.
    - abstract
        (intros x y ;
         apply isasetaprop ;
         apply propproperty).
  Defined.

  Proposition is_univalent_poset_to_category
    : is_univalent poset_to_category.
  Proof.
    intros x y.
    use isweqimplimpl.
    - intro f.
      use isantisymm_posetRelation.
      + apply f.
      + exact (inv_from_z_iso f).
    - apply setproperty.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_isomorphism.
      + intros.
        apply propproperty.
  Qed.

  Definition poset_to_univalent_category
    : univalent_category.
  Proof.
    use make_univalent_category.
    - exact poset_to_category.
    - exact is_univalent_poset_to_category.
  Defined.

  Definition poset_to_poset_category
    : poset_category.
  Proof.
    use make_poset_category.
    - exact poset_to_univalent_category.
    - intros x y.
      apply propproperty.
  Defined.
End ToPosetCategory.

(** * 4. Equivalence between posetal categories and posets *)
Definition poset_category_weq_poset_left
           (C : poset_category)
  : poset_to_poset_category (poset_category_to_poset C) = C.
Proof.
  use subtypePath.
  {
    intro.
    use isaprop_is_poset_category.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_is_univalent.
  }
  use subtypePath.
  {
    intro.
    apply isaprop_has_homsets.
  }
  use (invmap (path_precat _ _ (homset_property C))).
  use total2_paths_f.
  - apply idpath.
  - cbn.
    use pathsdirprod.
    + use funextsec ; intro.
      apply (is_poset_poset_category C).
    + repeat (use funextsec ; intro).
      apply (is_poset_poset_category C).
Qed.

Proposition poset_category_weq_poset_right
            (P : Poset)
  : poset_category_to_poset (poset_to_poset_category P) = P.
Proof.
  use total2_paths_f.
  - use total2_paths_f.
    + apply idpath.
    + apply isapropisaset.
  - use subtypePath.
    {
      intro.
      apply isaprop_isPartialOrder.
    }
    etrans.
    {
      apply (@pr1_transportf hSet hrel).
    }
    etrans.
    {
      apply transportf_total2_paths_f.
    }
    cbn.
    apply idpath.
Qed.

Definition poset_category_weq_poset
  : poset_category ≃ Poset.
Proof.
  use weq_iso.
  - exact poset_category_to_poset.
  - exact poset_to_poset_category.
  - exact poset_category_weq_poset_left.
  - exact poset_category_weq_poset_right.
Defined.
