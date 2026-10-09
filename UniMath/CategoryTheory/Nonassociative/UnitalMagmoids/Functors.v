(********************************************************************************

 Functors of Unital Magmoids

 Author: B. Szilvasy
 January 2026

 Contents:
 1. Preservation of submagmoids

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** Preservation of submagmoids *)

Section preservation.
  Context {C D : unital_premagmoid_data} (F : functor_data C D).
  Hypothesis Hfunctor : is_functor F.

  Definition preserves_submm
    (P : wide_submagmoid_data C)
    (Q : wide_submagmoid_data D)
    : UU
    := ∏ (a b : C) (f : a --> b),
      P _ _ f -> Q _ _ (#F f).

  Lemma isaprop_preserves_submm
    (P : wide_submagmoid_data C)
    (Q : wide_submagmoid_data D)
    : isaprop (preserves_submm P Q).
  Proof.
    do 4 (apply impred_isaprop; intro).
    apply propproperty.
  Qed.

  Definition preserves_submm_intersection
    (P₁ P₂ : wide_submagmoid C)
    (Q₁ Q₂ : wide_submagmoid D)
    (H₁ : preserves_submm P₁ Q₁)
    (H₂ : preserves_submm P₂ Q₂)
    : preserves_submm
        (wide_submagmoid_intersection P₁ P₂)
        (wide_submagmoid_intersection Q₁ Q₂).
  Proof.
    intros a b f [Hf₁ Hf₂].
    split.
    - apply H₁, Hf₁.
    - apply H₂, Hf₂.
  Defined.

  Definition reflects_submm
    (P₁ : wide_submagmoid_data C)
    (P₂ : wide_submagmoid_data D)
    : UU
    := ∏ (a b : C) (f : a --> b),
      P₂ _ _ (#F f) -> P₁ _ _ f.

  Lemma isaprop_reflects_submm
    (P : wide_submagmoid_data C)
    (Q : wide_submagmoid_data D)
    : isaprop (reflects_submm P Q).
  Proof.
    do 4 (apply impred_isaprop; intro).
    apply propproperty.
  Qed.

  Definition reflects_submm_intersection
    (P₁ P₂ : wide_submagmoid C)
    (Q₁ Q₂ : wide_submagmoid D)
    (H₁ : reflects_submm P₁ Q₁)
    (H₂ : reflects_submm P₂ Q₂)
    : reflects_submm
        (wide_submagmoid_intersection P₁ P₂)
        (wide_submagmoid_intersection Q₁ Q₂).
  Proof.
    intros a b f [Hf₁ Hf₂].
    split.
    - apply H₁, Hf₁.
    - apply H₂, Hf₂.
  Defined.

  Definition functor_lift_submm_data
    (P : wide_submagmoid C)
    (Q : wide_submagmoid D)
    (H : preserves_submm P Q)
    : functor_data
        (wide_submagmoid_carrier_data C P)
        (wide_submagmoid_carrier_data D Q).
  Proof.
    use make_functor_data.
    - exact F.
    - intros a b.
      use bandfmap.
      + exact #F.
      + intro f.
        exact (H a b f).
  Defined.

  Lemma functor_lift_submm_is_functor
    (P : wide_submagmoid C)
    (Q : wide_submagmoid D)
    (H : preserves_submm P Q)
    : is_functor (functor_lift_submm_data P Q H).
  Proof.
    split.
    - intro a; apply submm_mor_eq; cbn.
      exact (functor_id (F,,Hfunctor) a).
    - intros a b c f g; apply submm_mor_eq; cbn in f, g |- *.
      exact (functor_comp (F,,Hfunctor) f g).
  Defined.

  Definition functor_lift_submm'
    (P : wide_submagmoid C)
    (Q : wide_submagmoid D)
    (H : preserves_submm P Q)
    : functor
        (wide_submagmoid_carrier_data C P)
        (wide_submagmoid_carrier_data D Q)
    := make_functor _ (functor_lift_submm_is_functor P Q H).

  Lemma functor_lift_submm_fully_faithful
    (P : wide_submagmoid C)
    (Q : wide_submagmoid D)
    (Hff : fully_faithful (F,, Hfunctor))
    (H : preserves_submm P Q)
    (Hinv : reflects_submm P Q)
    : fully_faithful (functor_lift_submm' P Q H).
  Proof.
    intros a b.
    use weqhomot.
    - use weqbandf.
      + apply (weq_from_fully_faithful Hff).
      + intro f; cbn.
        apply weqimplimpl.
        * apply H.
        * apply Hinv.
        * apply propproperty.
        * apply propproperty.
    - easy.
  Defined.

End preservation.

Definition functor_lift_submm
  {C D : unital_premagmoid_data}
  (F : functor C D)
  (P : wide_submagmoid C)
  (Q : wide_submagmoid D)
  (H : preserves_submm F P Q)
  : functor
      (wide_submagmoid_carrier_data C P)
      (wide_submagmoid_carrier_data D Q)
  := make_functor _ (functor_lift_submm_is_functor F (pr2 F) P Q H).

Section preservation_proofs.
  Theorem functor_preserves_subcat_iso
    {C D : unital_magmoid}
    (F : functor C D)
    (P : wide_subcategory C)
    (Q : wide_subcategory D)
    (Hpreserves : preserves_submm F P Q)
    : preserves_submm F
        (isc_subcat_iso P)
        (isc_subcat_iso Q).
  Proof.
    intros a b f Hf; cbn in Hf.
    use make_is_submm_iso'.
    - exact (#F (submm_inv_mor P Hf)).
    - apply Hpreserves, Hf.
    - apply Hpreserves, (submm_mor_property P).
    - apply functor_on_is_inverse_in_precat.
      exact Hf.
  Defined.

  Theorem fully_faithful_reflects_subcat_iso
    {C D : unital_magmoid}
    (F : functor C D)
    (Hff : fully_faithful F)
    (P : wide_subcategory C)
    (Q : wide_subcategory D)
    (Hreflects : reflects_submm F P Q)
    : reflects_submm F
        (isc_subcat_iso P)
        (isc_subcat_iso Q).
  Proof.
    intros a b f Hf; cbn in Hf.
    use make_is_submm_iso'.
    - exact (fully_faithful_inv_hom Hff _ _ (submm_inv_mor Q Hf)).
    - apply Hreflects, Hf.
    - apply Hreflects.
      refine (transportb (λ x, Q _ _ x) _ (submm_mor_property Q (submm_inv_mor Q Hf))).
      apply (homotweqinvweq (weq_from_fully_faithful Hff _ _)).
    - refine (transportf (λ x, is_inverse_in_precat x _) _
                (inv_of_ff_inv_is_inv _ _ F Hff _ _
                   (make_z_iso (#F f) _ Hf))).
      apply (homotinvweqweq (weq_from_fully_faithful Hff _ _)).
  Defined.

  Theorem reflects_linearity_ff
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    : reflects_submm F _l _l.
  Proof.
    red; cbn; intros a b f Hf c d g h.
    apply (weqonpathsincl #F); [apply isinclweq, Hff|].
    rewrite !functor_comp.
    apply assoc'_linear, Hf.
  Qed.

  Theorem reflects_thunkability_ff
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    : reflects_submm F _t _t.
  Proof.
    red; cbn; intros a b f Hf c d g h.
    apply (weqonpathsincl #F); [apply isinclweq, Hff|].
    rewrite !functor_comp.
    apply assoc_thunkable, Hf.
  Qed.

  Theorem reflects_intermediate_ff
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    : reflects_submm F _i _i.
  Proof.
    red; cbn; intros a b f Hf c d g h.
    apply (weqonpathsincl #F); [apply isinclweq, Hff|].
    rewrite !functor_comp.
    apply assoc_intermediate, Hf.
  Qed.

  Theorem reflects_lt_ff
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    : reflects_submm F _lt _lt.
  Proof.
    apply reflects_submm_intersection.
    - apply reflects_linearity_ff, Hff.
    - apply reflects_thunkability_ff, Hff.
  Qed.

  Theorem reflects_lti_ff
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    : reflects_submm F _lti _lti.
  Proof.
    apply reflects_submm_intersection.
    - apply reflects_lt_ff, Hff.
    - apply reflects_intermediate_ff, Hff.
  Qed.

  Theorem reflects_lt_iso_ff
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    : reflects_submm F (isc_subcat_iso _lt) (isc_subcat_iso _lt).
  Proof.
    apply fully_faithful_reflects_subcat_iso.
    - exact Hff.
    - apply reflects_lt_ff, Hff.
  Qed.

  Theorem reflects_lti_iso_ff
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    : reflects_submm F (isc_subcat_iso _lti) (isc_subcat_iso _lti).
  Proof.
    apply fully_faithful_reflects_subcat_iso.
    - exact Hff.
    - apply reflects_lti_ff, Hff.
  Qed.

End preservation_proofs.

Section equivalences.

  Definition submm_fibre
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    (F : functor_data C D)
    (P : wide_submagmoid D) (b : D)
    : UU := ∑ (a : C), submm_iso P (F a) b.

  Definition submm_essentially_surjective
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    (F : functor_data C D)
    (P : wide_submagmoid D)
    : UU := ∏ (b : D), ishinh (submm_fibre F P b).

  Definition submm_split_essentially_surjective
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    (F : functor_data C D)
    (P : wide_submagmoid D)
    : UU := ∏ (b : D), submm_fibre F P b.

  Lemma isaprop_submm_essentially_surjective
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    (F : functor_data C D)
    (P : wide_submagmoid D)
    : isaprop (submm_essentially_surjective F P).
  Proof.
    apply impred_isaprop; intro.
    apply propproperty.
  Qed.

  Coercion submm_split_essentially_surjective_weaken
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    (F : functor_data C D)
    (P : wide_submagmoid D)
    (H : submm_split_essentially_surjective F P)
    : submm_essentially_surjective F P.
  Proof. intro b; apply hinhpr, H. Defined.

  Definition is_submm_weak_equiv
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    (F : functor C D)
    (P : wide_submagmoid D)
    : UU := fully_faithful F × submm_essentially_surjective F P.

  Definition submm_weak_equiv
    (C : unital_premagmoid_data)
    (D : unital_magmoid)
    (P : wide_submagmoid D)
    : UU := ∑ (F : functor C D), is_submm_weak_equiv F P.
  Coercion submm_weak_equiv_functor
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    {P : wide_submagmoid D}
    (F : submm_weak_equiv C D P)
    : functor C D := pr1 F.
  Coercion submm_weak_equiv_property
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    {P : wide_submagmoid D}
    (F : submm_weak_equiv C D P)
    : is_submm_weak_equiv F P := pr2 F.
  Definition make_submm_weak_equiv
    (C : unital_premagmoid_data)
    (D : unital_magmoid)
    (P : wide_submagmoid D)
    (F : functor C D)
    (H : is_submm_weak_equiv F P)
    : submm_weak_equiv C D P
    := F,, H.

  Lemma isaprop_is_submm_weak_equiv
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    (F : functor C D)
    (P : wide_submagmoid D)
    : isaprop (is_submm_weak_equiv F P).
  Proof.
    apply isapropdirprod.
    - apply isaprop_fully_faithful.
    - apply isaprop_submm_essentially_surjective.
  Qed.

  Lemma is_submm_eso_from_weq
    {C D : unital_magmoid}
    (F : functor C D)
    (P : wide_submagmoid D)
    (Hweq : isweq F)
    : submm_split_essentially_surjective F P.
  Proof.
    intro a.
    exists (invmap (make_weq F Hweq) a).
    apply id_to_submm_iso.
    exact (homotweqinvweq (make_weq F Hweq) a).
  Defined.

  Lemma is_submm_weak_equiv_identity
    (D : unital_magmoid)
    (P : wide_submagmoid D)
    : is_submm_weak_equiv (functor_identity D) P.
  Proof.
    split.
    - apply identity_functor_is_fully_faithful.
    - apply submm_split_essentially_surjective_weaken.
      apply is_submm_eso_from_weq, idisweq.
  Defined.

  Definition submm_weak_equiv_identity
    (D : unital_magmoid)
    (P : wide_submagmoid D)
    : submm_weak_equiv D D P.
  Proof.
    use make_submm_weak_equiv.
    - exact (functor_identity D).
    - apply is_submm_weak_equiv_identity.
  Defined.

  Coercion is_submm_weak_equiv_to_fully_faithful
    {C : unital_premagmoid_data} {D : unital_magmoid}
    (F : functor C D) (P : wide_submagmoid D)
    (H : is_submm_weak_equiv F P)
    : fully_faithful F
    := pr1 H.
  Coercion is_submm_weak_equiv_to_submm_eso
    {C : unital_premagmoid_data} {D : unital_magmoid}
    (F : functor C D) (P : wide_submagmoid D)
    (H : is_submm_weak_equiv F P)
    : submm_essentially_surjective F P
    := pr2 H.

  Definition is_submm_strong_equiv
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    (F : functor C D)
    (P : wide_submagmoid D)
    : UU := fully_faithful F × submm_split_essentially_surjective F P.

  Coercion is_submm_strong_equiv_to_fully_faithful
    {C : unital_premagmoid_data} {D : unital_magmoid}
    (F : functor C D) (P : wide_submagmoid D)
    (H : is_submm_strong_equiv F P)
    : fully_faithful F
    := pr1 H.
  Coercion is_submm_strong_equiv_to_submm_eso
    {C : unital_premagmoid_data} {D : unital_magmoid}
    (F : functor C D) (P : wide_submagmoid D)
    (H : is_submm_strong_equiv F P)
    : submm_split_essentially_surjective F P
    := pr2 H.

End equivalences.

Section equivalences.
  Lemma preserves_linearity_lti_equiv
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    (Heso : submm_essentially_surjective F _lti)
    : preserves_submm F _l _l.
  Proof.
    red; cbn; intros a b f Hf c d g h.
    isaprop_goal Hgoal; [apply unital_magmoid_has_homsets|].
    refine (squash_to_prop (Heso c) Hgoal _); intros [c' Hc'].
    refine (squash_to_prop (Heso d) Hgoal _); intros [d' Hd'].
    clear Hgoal.
    pose (h' := Hd' · h · submm_inv_mor _ Hc').
    pose (h'' := fully_faithful_inv_hom Hff _ _ h').
    pose (g' := Hc' · g).
    pose (g'' := fully_faithful_inv_hom Hff _ _ g').
    assert (Hhg' : h' · g' · # F f = h' · (g' · # F f)). {
      rewrite <- (homotweqinvweq (weq_from_fully_faithful Hff _ _) h').
      rewrite <- (homotweqinvweq (weq_from_fully_faithful Hff _ _) g').
      change (#F h'' · #F g'' · # F f = #F h'' · (#F g'' · # F f)).
      rewrite <- !functor_comp.
      apply (maponpaths #F).
      apply assoc'_linear, Hf.
    }
    use (cancel_submm_iso_left_of_associates _lti Hd').
    1,2: apply assoc_intermediate, (submm_mor_property _lti).
    rewrite <- (lti_iso_interpose_inv Hc' h g).
    rewrite <- (lti_iso_interpose_inv Hc' h (g · #F f)).
    subst h' g'.
    rewrite !(assoc_thunkable Hd' (pr21 (submm_mor_property _lti Hd'))).
    rewrite !(assoc_thunkable Hc' (pr21 (submm_mor_property _lti Hc'))).
    exact Hhg'.
  Qed.

  Lemma preserves_thunkability_lti_equiv
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    (Heso : submm_essentially_surjective F _lti)
    : preserves_submm F _t _t.
  Proof.
    red; cbn; intros a b f Hf c d g h.
    isaprop_goal Hgoal; [apply unital_magmoid_has_homsets|].
    refine (squash_to_prop (Heso c) Hgoal _); intros [c' Hc'].
    refine (squash_to_prop (Heso d) Hgoal _); intros [d' Hd'].
    clear Hgoal.
    pose (h' := submm_inv_mor _ Hd' ∘ h ∘ Hc').
    pose (h'' := fully_faithful_inv_hom Hff _ _ h').
    pose (g' := submm_inv_mor _ Hc' ∘ g).
    pose (g'' := fully_faithful_inv_hom Hff _ _ g').
    assert (Hhg' : h' ∘ g' ∘ # F f = h' ∘ (g' ∘ # F f)). {
      rewrite <- (homotweqinvweq (weq_from_fully_faithful Hff _ _) h').
      rewrite <- (homotweqinvweq (weq_from_fully_faithful Hff _ _) g').
      change (#F h'' ∘ #F g'' ∘ # F f = #F h'' ∘ (#F g'' ∘ # F f)).
      rewrite <- !functor_comp.
      apply (maponpaths #F).
      apply assoc_thunkable, Hf.
    }
    use (cancel_submm_iso_right_of_associates _lti (submm_iso_inv _ Hd')).
    1,2: apply assoc'_intermediate, (submm_mor_property _lti).
    rewrite <- (lti_iso_interpose_inv Hc' g h).
    rewrite <- (lti_iso_interpose_inv Hc' (g ∘ #F f) h).
    subst h' g'.
    rewrite !(assoc'_linear (submm_inv_mor _ Hd') (pr11 (submm_mor_property _lti _))).
    rewrite !(assoc'_linear (submm_inv_mor _ Hc') (pr11 (submm_mor_property _lti _))).
    exact Hhg'.
  Qed.

  Lemma preserves_intermediate_lti_equiv
    {C D : unital_magmoid} (F : functor C D)
    (Hff : fully_faithful F)
    (Heso : submm_essentially_surjective F _lti)
    : preserves_submm F _i _i.
  Proof.
    red; cbn; intros a b f Hf c d g h.
    isaprop_goal Hgoal; [apply unital_magmoid_has_homsets|].
    refine (squash_to_prop (Heso c) Hgoal _); intros [c' Hc'].
    refine (squash_to_prop (Heso d) Hgoal _); intros [d' Hd'].
    clear Hgoal.
    pose (h' := h · submm_inv_mor _ Hd').
    pose (h'' := fully_faithful_inv_hom Hff _ _ h').
    pose (g' := Hc' · g).
    pose (g'' := fully_faithful_inv_hom Hff _ _ g').
    assert (Hhg' : g' · # F f · h' = g' · (# F f · h')). {
      rewrite <- (homotweqinvweq (weq_from_fully_faithful Hff _ _) h').
      rewrite <- (homotweqinvweq (weq_from_fully_faithful Hff _ _) g').
      change (#F g'' · #F f · #F h'' = #F g'' · (#F f · #F h'')).
      rewrite <- !functor_comp.
      apply (maponpaths #F).
      apply assoc'_intermediate, Hf.
    }
    use (cancel_submm_iso_left_of_associates _lti Hc').
    1,2: apply assoc_intermediate, (submm_mor_property _lti).
    use (cancel_submm_iso_right_of_associates _lti (submm_iso_inv _ Hd')).
    1,2: apply assoc'_intermediate, (submm_mor_property _lti).
    subst h' g'.
    rewrite !(assoc_thunkable Hc' (pr21 (submm_mor_property _lti Hc'))).
    rewrite !(assoc'_linear (submm_inv_mor _ Hd') (pr11 (submm_mor_property _lti (submm_inv_mor _ Hd')))).
    exact (!Hhg').
  Qed.

End equivalences.
