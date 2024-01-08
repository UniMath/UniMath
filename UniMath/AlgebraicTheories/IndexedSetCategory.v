(**************************************************************************************************

  The category of sets indexed by a type

  This file constructs the category of sets, indexed over a type I. The category is equivalent to
  a functor category from a discrete category, but its objects are easier to work with.

  Contents
  1. The definition of the category [indexed_set_cat]
  2. Univalence [is_univalent_indexed_set_cat]
  3. Limits [limits_indexed_set_cat]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Local Open Scope cat.
Local Open Scope weq_scope.

Section IndexedSetCategory.

  Context (I : UU).

(** * 1. The definition of the category *)

  Definition indexed_set_cat
    : category.
  Proof.
    use make_category.
    - use make_precategory.
      + use make_precategory_data.
        * use make_precategory_ob_mor.
          -- exact (I → hSet).
          -- intros X Y.
            exact (∏ i, X i → Y i).
        * intros X i.
          apply idfun.
        * intros X Y Z f g i.
          exact (funcomp (f i) (g i)).
      + abstract now use make_is_precategory_one_assoc.
    - abstract (
        intros X Y;
        apply impred_isaset;
        intro i;
        apply funspace_isaset;
        apply setproperty
      ).
  Defined.

(** * 2. Univalence *)

  Definition indexed_set_cat_id_iso_weq
    (a b : indexed_set_cat)
    : (∏ i, a i = b i) ≃ (∏ i, z_iso (C := HSET) (a i) (b i)).
  Proof.
    use weq_iso.
    - intros H i.
      exact (idtoiso (C := HSET) (H i)).
    - intros H i.
      exact (isotoid _ is_univalent_HSET (H i)).
    - intros H.
      apply funextsec.
      intro i.
      apply (isotoid_idtoiso HSET).
    - intros H.
      apply funextsec.
      intro i.
      apply (idtoiso_isotoid HSET).
  Defined.

  Definition indexed_set_cat_iso_weq
    (a b : indexed_set_cat)
    : (∏ i, z_iso (C := HSET) (a i) (b i)) ≃ (z_iso a b).
  Proof.
    use weq_iso.
    - intro H.
      use make_z_iso.
      + intro.
        exact (z_iso_mor (H i)).
      + intro.
        exact (inv_from_z_iso (H i)).
      + split.
        * apply funextsec.
          intro i.
          exact (z_iso_inv_after_z_iso (H i)).
        * apply funextsec.
          intro i.
          exact (z_iso_after_z_iso_inv (H i)).
    - intros f i.
      use make_z_iso.
      + exact (z_iso_mor f i).
      + exact (inv_from_z_iso f i).
      + split.
        * exact (eqtohomot (z_iso_inv_after_z_iso f) i).
        * exact (eqtohomot (z_iso_after_z_iso_inv f) i).
    - intro f.
      apply funextsec.
      intro i.
      now apply z_iso_eq.
    - intro f.
      now apply z_iso_eq.
  Defined.

  Lemma is_univalent_indexed_set_cat
    : is_univalent indexed_set_cat.
  Proof.
    intros a b.
    use weqhomot.
    - exact (indexed_set_cat_iso_weq _ _ ∘
        indexed_set_cat_id_iso_weq _ _ ∘
        invweq (weqfunextsec _ _ _)).
    - intro e.
      induction e.
      now apply z_iso_eq.
  Defined.

(** * 3. Limits *)

  Local Definition unindex_diagram
    {J : graph}
    (d : diagram J indexed_set_cat)
    (i : I)
    : diagram J HSET.
  Proof.
    use make_diagram.
    - intro u.
      exact (dob d u i).
    - intros u v e.
      exact (dmor d e i).
  Defined.

  Local Definition unindex_cone
    {J : graph}
    {d : diagram J indexed_set_cat}
    {c : indexed_set_cat}
    (cc : cone d c)
    (i : I)
    : cone (unindex_diagram d i) (c i).
  Proof.
    use make_cone.
    - intro v.
      exact (coneOut cc v i).
    - abstract (
        intros u v e;
        apply (eqtohomot (coneOutCommutes cc u v e))
      ).
  Defined.

  Section Limits.

    Context {J : graph}.
    Context (d : diagram J indexed_set_cat).

    Let component_limit
      : ∏ i : I, LimCone (unindex_diagram d i)
      := λ i : I, LimsHSET J (unindex_diagram d i).

    Definition indexed_set_cat_tip
      : indexed_set_cat
      := λ i, (lim (component_limit i)).

    Definition indexed_set_cat_cone
      : cone d indexed_set_cat_tip.
    Proof.
      use make_cone.
      - intros v i.
        exact (limOut (component_limit i) v).
      - abstract (
          intros u v e;
          apply funextsec;
          intro i;
          apply (limOutCommutes (component_limit i))
        ).
    Defined.

    Section IsLimCone.

      Context {c: indexed_set_cat}.
      Context (cc: cone d c).

      Definition indexed_set_cat_arrow
        : indexed_set_cat ⟦ c, indexed_set_cat_tip ⟧
        := λ i, limArrow (component_limit i) (c i) (unindex_cone cc i).

      Lemma indexed_set_cat_is_cone_mor
        : is_cone_mor cc indexed_set_cat_cone indexed_set_cat_arrow.
      Proof.
        intro v.
        apply funextsec.
        intro i.
        exact (limArrowCommutes (component_limit i) (c i) (unindex_cone cc i) v).
      Qed.

      Lemma indexed_set_cat_isaprop_is_cone_mor
        (t : indexed_set_cat ⟦ c, indexed_set_cat_tip ⟧)
        : isaprop (is_cone_mor cc indexed_set_cat_cone t).
      Proof.
        intro.
        apply impred_isaprop.
        intro.
        apply (homset_property indexed_set_cat).
      Qed.

      Lemma indexed_set_cat_arrow_is_unique
        (t : indexed_set_cat ⟦ c, indexed_set_cat_tip ⟧)
        (Ht : is_cone_mor cc indexed_set_cat_cone t)
        : t = indexed_set_cat_arrow.
      Proof.
        apply funextsec.
        intro i.
        exact (limArrowUnique (component_limit i) (c i) (unindex_cone cc i) (t i) (λ v, (eqtohomot (Ht v) i))).
      Qed.

    End IsLimCone.

  End Limits.

  Definition limits_indexed_set_cat
    : Lims indexed_set_cat.
  Proof.
    intros J d.
    use make_LimCone.
    - exact (indexed_set_cat_tip d).
    - apply indexed_set_cat_cone.
    - intros c cc.
      use unique_exists.
      + apply (indexed_set_cat_arrow d cc).
      + apply indexed_set_cat_is_cone_mor.
      + apply indexed_set_cat_isaprop_is_cone_mor.
      + apply indexed_set_cat_arrow_is_unique.
  Defined.

End IndexedSetCategory.
