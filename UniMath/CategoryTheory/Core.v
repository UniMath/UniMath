Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.

Local Open Scope cat.

Section Core.
  Context (C : category).

  Definition core_precategory_ob_mor : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact C.
    - exact (λ x y, z_iso x y).
  Defined.

  Definition core_precategory_data : precategory_data.
  Proof.
    use make_precategory_data.
    - exact core_precategory_ob_mor.
    - exact (λ x, identity_z_iso x).
    - exact (λ x y z i₁ i₂, z_iso_comp i₁ i₂).
  Defined.

  Definition core_is_precategory : is_precategory core_precategory_data.
  Proof.
    use make_is_precategory_one_assoc ; intros ; use eq_z_iso ; cbn.
    - apply id_left.
    - apply id_right.
    - apply assoc.
  Qed.

  Definition core_precategory : precategory.
  Proof.
    use make_precategory.
    - exact core_precategory_data.
    - exact core_is_precategory.
  Defined.

  Definition core : category.
  Proof.
    use make_category.
    - exact core_precategory.
    - intros x y ; cbn.
      use isaset_z_iso.
  Defined.

  Definition is_z_iso_core
             {x y : core}
             (f : x --> y)
    : is_z_isomorphism f.
  Proof.
    exists (z_iso_inv_from_z_iso f).
    - abstract
        (split ;
         use eq_z_iso ;
         cbn ;
         [ apply z_iso_inv_after_z_iso | apply z_iso_after_z_iso_inv]).
  Defined.

  Definition is_pregroupoid_core
    : is_pregroupoid core.
  Proof.
    exact @is_z_iso_core.
  Defined.

  Definition core_z_iso_weq
             (x y : C)
    : @z_iso C x y ≃ @z_iso core x y.
  Proof.
    use make_weq.
    - simple refine (λ i, _,,_).
      + exact i.
      + apply is_z_iso_core.
    - use gradth.
      + exact (λ i, pr1 i).
      + abstract
          (intro i ;
           use eq_z_iso ;
           apply idpath).
      + abstract
          (intro i ;
           use eq_z_iso ;
           apply idpath).
  Defined.

  Definition is_univalent_core
             (HC : is_univalent C)
    : is_univalent core.
  Proof.
    intros x y.
    use weqhomot.
    - exact (core_z_iso_weq x y
             ∘ make_weq idtoiso (HC x y))%weq.
    - abstract
        (intro p ;
         induction p ;
         use eq_z_iso ; cbn ;
         apply idpath).
  Defined.

  Definition functor_core_data
    : functor_data core C.
  Proof.
    use make_functor_data.
    - exact (λ x, x).
    - exact (λ x y i, pr1 i).
  Defined.

  Definition functor_core_is_functor
    : is_functor functor_core_data.
  Proof.
    split.
    - intro x ; cbn.
      apply idpath.
    - intros x y z f g ; cbn.
      apply idpath.
  Qed.

  Definition functor_core
    : core ⟶ C.
  Proof.
    use make_functor.
    - exact functor_core_data.
    - exact functor_core_is_functor.
  Defined.

  Definition functor_core_eso
    : essentially_surjective functor_core.
  Proof.
    intro x.
    apply hinhpr.
    refine (x ,, _).
    apply identity_z_iso.
  Defined.

  Definition functor_core_faithful
    : faithful functor_core.
  Proof.
    intros x y f.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath ; [ intro ; apply homset_property | ].
    use eq_z_iso ; cbn.
    exact (pr2 φ₁ @ !(pr2 φ₂)).
  Qed.

  Definition functor_core_full_on_iso
    : full_on_iso functor_core.
  Proof.
    intros x y f ; cbn in *.
    apply hinhpr.
    simple refine (_ ,, _).
    - refine (f ,, _).
      apply is_z_iso_core.
    - abstract
        (use eq_z_iso ; cbn ;
         apply idpath).
  Defined.

  Definition functor_core_pseudomonic
    : pseudomonic functor_core.
  Proof.
    split.
    - exact functor_core_faithful.
    - exact functor_core_full_on_iso.
  Defined.

  Section FactorCore.
    Context {G : groupoid}
            (F : G ⟶ C).

    Definition factor_through_core_data
      : functor_data G core.
    Proof.
      use make_functor_data.
      - exact (λ x, F x).
      - exact (λ x y f,
               functor_on_z_iso
                 F
                 (_ ,, pr2 G _ _ f)).
    Defined.

    Definition factor_through_core_is_functor
      : is_functor factor_through_core_data.
    Proof.
      split ; intro ; intros ; use eq_z_iso ; cbn.
      - apply functor_id.
      - apply functor_comp.
    Qed.

    Definition factor_through_core
      : G ⟶ core.
    Proof.
      use make_functor.
      - exact factor_through_core_data.
      - exact factor_through_core_is_functor.
    Defined.

    Definition factor_through_core_commute
      : factor_through_core ∙ functor_core ⟹ F.
    Proof.
      use make_nat_trans.
      - exact (λ x, identity _).
      - abstract
          (intros x y f ; cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition factor_through_core_commute_z_iso
      : nat_z_iso (factor_through_core ∙ functor_core) F.
    Proof.
      use make_nat_z_iso.
      - exact factor_through_core_commute.
      - intro x.
        apply identity_is_z_iso.
    Defined.
  End FactorCore.

  Section NatIsoToCore.
    Context {G : groupoid}
            {F₁ F₂ : G ⟶ core}
            (α : nat_z_iso
                   (F₁ ∙ functor_core)
                   (F₂ ∙ functor_core)).

    Definition nat_trans_to_core
      : F₁ ⟹ F₂.
    Proof.
      use make_nat_trans.
      - exact (λ x, nat_z_iso_pointwise_z_iso α x).
      - abstract
          (intros x₁ x₂ f ; cbn ;
           use eq_z_iso ; cbn ;
           exact (nat_trans_ax α _ _ f)).
    Defined.

    Definition nat_iso_to_core
      : nat_z_iso F₁ F₂.
    Proof.
      use make_nat_z_iso.
      - exact nat_trans_to_core.
      - intro x.
        apply is_z_iso_core.
    Defined.
  End NatIsoToCore.
End Core.

Definition univalent_core
           (C : univalent_category)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (core C).
  - apply is_univalent_core.
    exact (pr2 C).
Defined.
