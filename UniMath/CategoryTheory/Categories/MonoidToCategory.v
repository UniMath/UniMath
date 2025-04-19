(**************************************************************************************************

  Constructing an one-object category from a monoid

  If we have a monoid, we can construct a one-object category from it. This is the one-dimensional
  version of what happens in `Bicategories/MonoidalCategories/MonoidalFromBicategory.v`. In fact,
  this gives a fully faithful functor from monoids to setcategories. Presheaves on such a one-object
  category are equivalent to sets with a right monoid action.

  Contents
  1. The functor from monoids to categories [monoid_to_category]
  1.2. Fully faithful [monoid_to_category_fully_faithful]
  2. The equivalence between presheaves and monoid actions [monoid_presheaf_action_equivalence]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Categories.Monoid.
Require Import UniMath.CategoryTheory.Categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Presheaf.

Require Import UniMath.AlgebraicTheories.FundamentalTheorem.CommonUtilities.MonoidActions.

Local Open Scope cat.
Local Open Scope multmonoid.

Section MonoidToCategory.

(** * 1. The functor from monoids to categories*)

  Section Ob.

    Context (M : monoid).

    Definition monoid_to_category_ob_data
      : precategory_data.
    Proof.
      use make_precategory_data.
      - use make_precategory_ob_mor.
        + exact unit.
        + intros t t'.
          exact M.
      - intro c.
        exact 1.
      - intros a b c m m'.
        exact (m' * m).
    Defined.

    Lemma monoid_to_category_ob_is_precategory
      : is_precategory_one_assoc monoid_to_category_ob_data.
    Proof.
      repeat split.
      - intros a b f.
        apply runax.
      - intros a b f.
        apply lunax.
      - intros t t' t'' t''' f g h.
        apply assocax.
    Qed.

    Definition monoid_to_category_ob_precategory
      : precategory
      := make_precategory_one_assoc
        monoid_to_category_ob_data
        monoid_to_category_ob_is_precategory.

    Lemma monoid_to_category_is_setcategory
      : is_setcategory monoid_to_category_ob_precategory.
    Proof.
      split.
      - apply isasetunit.
      - intros t t'.
        apply setproperty.
    Qed.

    Definition monoid_to_category_ob
      : setcategory
      := monoid_to_category_ob_precategory ,, monoid_to_category_is_setcategory.

  End Ob.

  Section Mor.

    Context {M M' : monoid}.
    Context (f : monoidfun M M').

    Definition monoid_to_category_mor_data
      : functor_data (monoid_to_category_ob M) (monoid_to_category_ob M').
    Proof.
      use make_functor_data.
      - exact (idfun _).
      - intros t t' m.
        exact (f m).
    Defined.

    Lemma monoid_to_category_mor_is_functor
      : is_functor monoid_to_category_mor_data.
    Proof.
      split.
      - intro t.
        apply monoidfununel.
      - intros t t' t'' m m'.
        apply monoidfunmul.
    Qed.

    Definition monoid_to_category_mor
      : monoid_to_category_ob M ⟶ monoid_to_category_ob M'
      := make_functor _ monoid_to_category_mor_is_functor.

  End Mor.

  Definition monoid_to_category_data
    : functor_data monoid_category cat_of_setcategory
    := make_functor_data (C := monoid_category) (C' := cat_of_setcategory)
      monoid_to_category_ob
      (λ _ _, monoid_to_category_mor).

  Lemma monoid_to_category_is_functor
    : is_functor monoid_to_category_data.
  Proof.
    now split;
      repeat intro;
      apply (functor_eq _ _ (homset_property _)).
  Qed.

  Definition monoid_to_category
    : monoid_category ⟶ cat_of_setcategory
    := make_functor
      monoid_to_category_data
      monoid_to_category_is_functor.

(** ** 1.2. Fully faithful *)

  Section FullyFaithful.

    Context (M M' : monoid).

    Section Mor.

      Context (f : monoid_to_category_ob M ⟶ monoid_to_category_ob M').

      Definition functor_to_monoidfun_data
        : M → M'.
      Proof.
        intro m.
        exact (#f (m : monoid_to_category_ob M⟦tt, tt⟧)).
      Defined.

      Lemma functor_to_is_monoidfun
        : ismonoidfun functor_to_monoidfun_data.
      Proof.
        use make_ismonoidfun.
        - intros m m'.
          apply (functor_comp f).
        - apply (functor_id f).
      Qed.

      Definition functor_to_monoidfun
        : monoidfun M M'
        := make_monoidfun functor_to_is_monoidfun.

    End Mor.

    Lemma monoid_to_category_fully_faithful_monoidfun_iso
      (f : monoidfun M M')
      : functor_to_monoidfun (monoid_to_category_mor f) = f.
    Proof.
      now apply monoidfun_paths.
    Qed.

    Lemma monoid_to_category_fully_faithful_functor_iso
      (f : monoid_to_category_ob M ⟶ monoid_to_category_ob M')
      : monoid_to_category_mor (functor_to_monoidfun f) = f.
    Proof.
      apply (functor_eq _ _ (homset_property _)).
      use functor_data_eq.
      - intro t.
        now induction t, (pr1 f tt).
      - intros t t' m.
        do 2 refine (eqtohomot (transportf_const _ _) _ @ _).
        now induction t, t'.
    Qed.

  End FullyFaithful.

  Definition monoid_to_cat_fully_faithful
    : fully_faithful monoid_to_category.
  Proof.
    intros m m'.
    use isweq_iso.
    - apply functor_to_monoidfun.
    - apply monoid_to_category_fully_faithful_monoidfun_iso.
    - apply monoid_to_category_fully_faithful_functor_iso.
  Defined.

  Definition monoid_iso_weq_monoid_category_equiv
    : ∏ (M M' : monoid),
      z_iso (C := monoid_category) M M'
      ≃ z_iso (C := cat_of_setcategory) (monoid_to_category_ob M) (monoid_to_category_ob M')
    := weq_ff_functor_on_z_iso monoid_to_cat_fully_faithful.

End MonoidToCategory.

(** * 2. The equivalence between presheaves and monoid actions *)

Section MonoidCategoryPresheaf.

  Context (M : monoid).

  Definition monoid_presheaf_to_action
    : PreShv (monoid_to_category_ob M) ⟶ monoid_action_cat M.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro P.
        use make_monoid_action.
        * use make_monoid_action_data.
          -- exact ((P : _ ⟶ _) tt).
          -- intros p m.
            exact (# (P : _ ⟶ _) m p).
        * use make_is_monoid_action.
          -- intro x.
            exact (eqtohomot (functor_id P _) _).
          -- intros x m m'.
            exact (eqtohomot (functor_comp P m m') _).
      + intros P P' F.
        use make_monoid_action_morphism.
        * exact ((F : _ ⟹ _) tt).
        * intros x m.
          apply (eqtohomot (nat_trans_ax F _ _ _)).
    - abstract now split;
        repeat intro;
          apply monoid_action_morphism_eq.
  Defined.

  Definition monoid_action_to_presheaf_ob
    (X : monoid_action M)
    : PreShv (monoid_to_category_ob M).
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro.
        exact (X : hSet).
      + intros a b m x.
        exact (action x m).
    - abstract (
        split;
        [ intro t;
          apply funextfun;
          intro x;
          apply action_unel
        | intros t t' t'' m m';
          apply funextfun;
          intro x;
          apply action_op ]
      ).
  Defined.

  Definition monoid_presheaf_action_equivalence
    : adj_equivalence_of_cats monoid_presheaf_to_action.
  Proof.
    use rad_equivalence_of_cats.
    - apply is_univalent_functor_category.
      apply is_univalent_HSET.
    - intros P P'.
      use isweq_iso.
      + intro f.
        use make_nat_trans.
        * intros t.
          induction t.
          exact (f : monoid_action_morphism _ _).
        * abstract (
            intros t t';
            induction t, t';
            intro m;
            apply funextfun;
            intro x;
            apply (mor_action f)
          ).
      + abstract (
          intro f;
          apply nat_trans_eq_alt;
          intro t;
          now induction t
        ).
      + abstract (
          intro f;
          now apply monoid_action_morphism_eq
        ).
    - intro X.
      apply hinhpr.
      exists (monoid_action_to_presheaf_ob X).
      use make_z_iso.
      + apply (identity X).
      + apply (identity X).
      + abstract (
          split;
          now apply monoid_action_morphism_eq
        ).
  Defined.

End MonoidCategoryPresheaf.
