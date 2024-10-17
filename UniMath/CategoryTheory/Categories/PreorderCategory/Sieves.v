(**************************************************************************************************

  Sieves in a preorder category

  If we turn a preorder into a category C, a sieve on X : C (a subobject of the Yoneda presheaf of
  X) is equivalent to a collection of objects Y with Y < X (the downset of X), such that if Y is in
  the collection and Z < Y, then Z is also in the collection (the collection is downward closed).

  Contents
  1. The equivalence [po_sieve_weq_subtype]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.GrothendieckToposes.Sieves.
Require Import UniMath.CategoryTheory.Categories.PreorderCategory.Core.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Subobjects.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.OrderTheory.Preorders.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.Categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.slicecat.

Local Open Scope cat.

Section PoCategorySieve.

  Context {X : UU}.
  Context {P : po X}.
  Context {x : X}.

  Lemma isaprop_po_sieve_dom
    (y : X)
    (f : sieve (C := po_category P) x)
    : isaprop (sieve_functor f y : hSet).
  Proof.
    apply invproofirrelevance.
    intros z w.
    apply (invmaponpathsincl _ (presheaf_monic_isincl (Subobject_isM f) _)).
    apply propproperty.
  Qed.

  Definition sieve_to_subtype
    (f : sieve (C := po_category P) x)
    : downward_closed_subtype (subpreorder P (down_type P x)).
  Proof.
    use make_downward_closed_subtype.
    - intro y.
      apply (make_hProp (sieve_functor f (pr1carrier _ y) : hSet)).
      abstract apply isaprop_po_sieve_dom.
    - abstract (
        intros y z;
        exact (# (sieve_functor f) (pr2 z) (pr2 y))
      ).
  Defined.

  Section SubtypeToSieve.

    Context (f : downward_closed_subtype (subpreorder P (down_type P x))).

    Definition subtype_to_functor
      : (po_category P)^op ⟶ SET.
    Proof.
      use make_functor.
      - use make_functor_data.
        + intro y.
          apply (make_hSet (carrier_subtype_weq_contained_subtype _ f y)).
          abstract (
            apply isasetaprop;
            apply propproperty
          ).
        + abstract (
            intros y z Hzy Hyx;
            use tpair;
            [ exact (istrans_po P z y x Hzy (pr1carrier _ Hyx))
            | exact (downward_closed_is_downward_closed _ f (make_carrier _ _ (pr2 Hyx)) (make_carrier _ (make_carrier _ z _) Hzy)) ]
          ).
      - abstract (
          split;
          repeat intro;
          apply funextfun;
          intro;
          apply isaprop_total2
        ).
    Defined.

    Definition subtype_to_nat_trans
      : subtype_to_functor ⟹ yoneda_objects (po_category P) x.
    Proof.
      use make_nat_trans.
      -- intros y Hyx.
        exact (pr1 Hyx).
      -- abstract (
          do 3 intro;
          apply funextfun;
          intro;
          apply propproperty
        ).
    Defined.

    Lemma subtype_to_isMonic
      : isMonic (C := [_, SET]) subtype_to_nat_trans.
    Proof.
      apply is_nat_trans_monic_from_pointwise_monics.
      intro y.
      apply (invmap (MonosAreInjective_HSET _)).
      apply incl_injectivity.
      apply isinclpr1.
      intro Hyx.
      apply propproperty.
    Qed.

  End SubtypeToSieve.

  Definition subtype_to_sieve
    (f : downward_closed_subtype (subpreorder P (down_type P x)))
    : sieve (C := po_category P) x
    := (subtype_to_functor f ,, tt) ,,
      make_Monic ([_, _]) (subtype_to_nat_trans f) (subtype_to_isMonic f).

  Section SieveToSubtypeToSieve.

    Context (f : sieve (C := po_category P) x).

    Definition sieve_to_sieve_nat_trans_data
      : nat_trans_data (sieve_functor (subtype_to_sieve (sieve_to_subtype f))) (sieve_functor f).
    Proof.
      intros y Hy.
      exact (pr2 Hy).
    Defined.

    Definition sieve_to_sieve_is_nat_trans
      : is_nat_trans _ _ sieve_to_sieve_nat_trans_data.
    Proof.
      do 3 intro.
      apply funextfun.
      intro.
      apply isaprop_po_sieve_dom.
    Qed.

    Definition sieve_to_sieve_nat_trans
      : sieve_functor (subtype_to_sieve (sieve_to_subtype f)) ⟹ sieve_functor f
      := make_nat_trans _ _ _ sieve_to_sieve_is_nat_trans.

    Section Inverse.

      Context (y : X).

      Definition sieve_to_sieve_inv
        : SET⟦sieve_functor f y, sieve_functor (subtype_to_sieve (sieve_to_subtype f)) y⟧
        := λ Hfy, (sieve_nat_trans f y Hfy ,, Hfy).

      Lemma sieve_to_sieve_is_inverse
        : is_inverse_in_precat (sieve_to_sieve_nat_trans y) sieve_to_sieve_inv.
      Proof.
        split.
        - apply funextfun.
          intro H.
          apply (maponpaths (λ x, x ,, _)).
          apply propproperty.
        - easy.
      Qed.

      Definition sieve_to_sieve_is_iso
        : is_z_isomorphism (sieve_to_sieve_nat_trans y)
        := make_is_z_isomorphism _ sieve_to_sieve_inv sieve_to_sieve_is_inverse.

    End Inverse.

    Definition sieve_to_sieve_iso
      : z_iso
        (slicecat_ob_object _ _ (subtype_to_sieve (sieve_to_subtype f)))
        (slicecat_ob_object _ _ f).
    Proof.
      apply iso_in_subcategory_of_monics_weq.
      use tpair.
      - exact sieve_to_sieve_nat_trans.
      - apply nat_trafo_z_iso_if_pointwise_z_iso.
        exact sieve_to_sieve_is_iso.
    Defined.

    Lemma sieve_to_sieve_commutes
      : slicecat_ob_morphism _ _ (subtype_to_sieve (sieve_to_subtype f))
      = sieve_to_sieve_iso · slicecat_ob_morphism _ _ f.
    Proof.
      apply Monic_eq.
      apply nat_trans_eq_alt.
      intro y.
      apply funextfun.
      intro H.
      apply propproperty.
    Qed.

    Definition sieve_to_subtype_to_sieve
      : subtype_to_sieve (sieve_to_subtype f) = f.
    Proof.
      use isotoid.
      - apply is_univalent_Subobjectscategory.
        apply is_univalent_functor_category.
        apply is_univalent_HSET.
      - apply slicecat.weq_z_iso.
        use tpair.
        + exact sieve_to_sieve_iso.
        + exact sieve_to_sieve_commutes.
    Qed.

  End SieveToSubtypeToSieve.

  Lemma subtype_to_sieve_to_subtype
    (f : downward_closed_subtype (subpreorder P (down_type P x)))
    : sieve_to_subtype (subtype_to_sieve f) = f.
  Proof.
    use subtypePath.
    {
      intro.
      do 2 (apply impred_isaprop; intro).
      apply propproperty.
    }
    apply hsubtype_univalence.
    intro y.
    split.
    - intro H.
      refine (transportf _ _ (pr2 H)).
      apply propproperty.
    - intro H.
      exact (pr2 y ,, H).
  Qed.

  Definition po_sieve_weq_subtype
    : sieve (C := po_category P) x ≃ downward_closed_subtype (subpreorder P (down_type P x))
    := weq_iso
      sieve_to_subtype
      subtype_to_sieve
      sieve_to_subtype_to_sieve
      subtype_to_sieve_to_subtype.

End PoCategorySieve.
