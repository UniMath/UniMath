(********************************************************************************

 The Equalizing Requirement of an Adjunction

 Author: B. Szilvasy
 January–October 2026

 An adjunction is negative equalizing if the counit [εn] of the adjunction [L ⊣
 R] is an equalizer of [LRεn] and [εLRn], and positive equalizing if the unit
 [ηp] is a coequalizer of [RLηp] and [ηRLp].  These are also known as being of
 "descent type" and "codescent type" respetively.

 We define the equalizing requirement and some of its consequences.  In
 particular, we prove univalence of the oblique and envelope duploids.

 Contents:
 1. Definition of the equalizing requirement
 1.1. Characterizations of the equalizing requirement
 1.2. Consequences about the fixed points of the adjunction
 2. The shift adjunction of a duploid is fully equalizing
 3. Univalence of the envelope and oblique duploids
 3.1. Characterizations in terms of duploids
 3.2. Univalence of the oblique duploid
 3.3. Univalence of the envelope duploid

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.IdentitySystems.RXGraph.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.CategoryRXGraph.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Tactics.

Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.Univalence.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.FromAdjunction.ObliqueMor.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.FromAdjunction.Envelope.
Require Import UniMath.CategoryTheory.Nonassociative.Duploids.FromAdjunction.Oblique.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope oblique_mor.
Local Open Scope duploid.

(** ** Definition of the equalizing requirement *)

Section equalized.
  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  Definition is_negative_equalizing : UU
    := ∏ (n m : N) (f : (R ∙ L) n --> m) (H : #(R ∙ L) (ε n) · f = ε ((R ∙ L) n) · f),
      ∃! (f' : n --> m), ε n · f' = f.

  Lemma isaprop_is_negative_equalizing : isaprop is_negative_equalizing.
  Proof.
    do 4 (apply impred; intro).
    apply isapropiscontr.
  Qed.

  Definition is_positive_equalizing : UU
    := ∏ (p q : P) (f : p --> (L ∙ R) q) (H : f · #(L ∙ R) (η q) = f · η ((L ∙ R) q)),
       ∃! (f' : p --> q), f' · η q = f.

  Lemma isaprop_is_positive_equalizing : isaprop is_positive_equalizing.
  Proof.
    do 4 (apply impred; intro).
    apply isapropiscontr.
  Qed.

  Definition is_fully_equalizing : UU
    := is_negative_equalizing × is_positive_equalizing.
  Definition make_is_fully_equalizing
    (Hnegative : is_negative_equalizing)
    (Hpositive : is_positive_equalizing)
    : is_fully_equalizing := Hnegative,,Hpositive.
  Coercion is_fully_equalizing_to_is_negative_equalizing
    (H : is_fully_equalizing) : is_negative_equalizing := pr1 H.
  Coercion is_fully_equalizing_to_is_positive_equalizing
    (H : is_fully_equalizing) : is_positive_equalizing := pr2 H.

  Local Lemma isInjective_φ_adj {a b} : isInjective (φ_adj (A:=a) (B:=b) θ).
  Proof. apply isweqonpathsincl, isinclweq, adjunction_hom_weq. Qed.
  Local Lemma isInjective_φ_adj_inv {a b} : isInjective (φ_adj_inv (A:=a) (B:=b) θ).
  Proof. apply isweqonpathsincl, isinclweq, (invweq (adjunction_hom_weq _ _ _)). Qed.

  Ltac cancel_φ_adj := apply (Injectivity (φ_adj θ) isInjective_φ_adj).
  Ltac cancel_φ_adj_inv := apply (Injectivity (φ_adj_inv θ) isInjective_φ_adj_inv).

  (** *** Characterizations of the equalizing requirement *)

  Lemma is_negative_equalizing_weq_isweq_oblique_lift_negative
    : (∏ (n m : N), isweq (λ (f : n --> m), oblique_lift_negative θ f))
        ≃ is_negative_equalizing.
  Proof.
    apply weqonsecfibers; intro n.
    apply weqonsecfibers; intro m.
    eapply weqcomp; [apply weqsecovertotal2|].
    eapply weqcomp; [apply (weqonsecbase (X:=N⟦L (R n), m⟧) _
                              (weq_oblique_mor_from_negative θ _ _))|].
    apply weqonsecfibers; intro f.
    apply weqonsecfibers; intro Hf.
    apply weq_iscontrweqf.
    apply (weqbandf (idweq _)).
    intro f'.
    eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
    apply oblique_mor_negative_path_weq.
  Defined.

  Lemma is_negative_equalizing_from_is_epi_and_equation
    (Hepi : ∏ (n : N), isEpi (ε n))
    (Himage : ∏ (n m : N) (f : oblique_mor θ (R n) m) (H : is_oblique_mor_linear θ f),
        ishinh (hfiber (λ g, ε n · g) f♭))
    : is_negative_equalizing.
  Proof.
    intros a b f Hf.
    isaprop_goal Hprop; [apply isapropiscontr|].
    refine (squash_to_prop (Himage _ _ (oblique_mor_from_negative θ f) Hf) Hprop (λ Hfib, _)).
    induction Hfib as [g Hg].
    use (unique_exists g).
    - exact Hg.
    - intro; apply homset_property.
    - intros g' Hg'; cbn in Hg'.
      apply Hepi.
      exact (Hg' @ !Hg).
  Qed.

  Lemma is_negative_equalizing_from_is_epi_and_linear_image
    (Hepi : ∏ (n : N), isEpi (ε n))
    (Himage : ∏ (n m : N) (f : oblique_mor θ (R n) m) (H : is_oblique_mor_linear θ f),
        ishinh (hfiber (#R) f♯))
    : is_negative_equalizing.
  Proof.
    apply (is_negative_equalizing_from_is_epi_and_equation Hepi).
    intros a b f Hf.
    isaprop_goal Hprop; [apply propproperty|].
    refine (squash_to_prop (Himage _ _ f Hf) Hprop (λ Hfib, _)).
    induction Hfib as [g Hg].
    apply hinhpr; exists g.
    change ((oblique_lift_negative θ g)♭ = f♭).
    apply (maponpaths (oblique_mor_negative θ)), oblique_mor_positive_path.
    exact Hg.
  Defined.

  Lemma is_positive_equalizing_weq_isweq_oblique_lift_positive
    : (∏ (p q : P), isweq (λ (f : p --> q), oblique_lift_positive θ f))
        ≃ is_positive_equalizing.
  Proof.
    apply weqonsecfibers; intro p.
    apply weqonsecfibers; intro q.
    eapply weqcomp; [apply weqsecovertotal2|].
    eapply weqcomp; [apply (weqonsecbase (X:=P⟦p, R (L q)⟧) _
                              (weq_oblique_mor_from_positive θ _ _))|].
    apply weqonsecfibers; intro f.
    apply weqonsecfibers; intro Hf.
    apply weq_iscontrweqf.
    apply (weqbandf (idweq _)).
    intro f'.
    eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
    apply oblique_mor_positive_path_weq.
  Defined.

  Lemma is_positive_equalizing_from_is_monic_and_equation
    (Hmonic : ∏ (p : P), isMonic (η p))
    (Himage : ∏ (p q : P) (f : oblique_mor θ p (L q)) (H : is_oblique_mor_thunkable θ f),
        ishinh (hfiber (λ g, g · η q) f♯))
    : is_positive_equalizing.
  Proof.
    intros a b f Hf.
    isaprop_goal Hprop; [apply isapropiscontr|].
    refine (squash_to_prop (Himage _ _ (oblique_mor_from_positive θ f) Hf) Hprop (λ Hfib, _)).
    induction Hfib as [g Hg].
    use (unique_exists g).
    - exact Hg.
    - intro; apply homset_property.
    - intros g' Hg'; cbn in Hg'.
      apply Hmonic.
      exact (Hg' @ !Hg).
  Qed.

  Lemma is_positive_equalizing_from_is_monic_and_thunkable_image
    (Hmonic : ∏ (p : P), isMonic (η p))
    (Himage : ∏ (p q : P) (f : oblique_mor θ p (L q)) (H : is_oblique_mor_thunkable θ f),
        ishinh (hfiber (#L) f♭))
    : is_positive_equalizing.
  Proof.
    apply (is_positive_equalizing_from_is_monic_and_equation Hmonic).
    intros a b f Hf.
    isaprop_goal Hprop; [apply propproperty|].
    refine (squash_to_prop (Himage _ _ f Hf) Hprop (λ Hfib, _)).
    induction Hfib as [g Hg].
    apply hinhpr; exists g.
    change ((oblique_lift_positive θ g)♯ = f♯).
    apply (maponpaths (oblique_mor_positive θ)), oblique_mor_negative_path.
    exact Hg.
  Qed.

  (** *** Consequences about the fixed points of the adjunction *)

  (** Lemmas about the negative fixed point of the adjunction *)
  Section negative_fixed_point.
    Lemma is_epi_counit_from_negative_equalizing
      (Hnegative_eq : is_negative_equalizing) (n : N)
      : isEpi (ε n).
    Proof.
      intros b f g H.
      apply (base_paths (B:=λ f', ε n · f' = ε n · g) (f,,H) (g,,idpath _)).
      eassert (H' : ∃! f' : N⟦n, b⟧, ε n · f' = ε n · g). {
        refine (Hnegative_eq _ _ (ε n · g) _).
        now rewrite !assoc, nat_trans_ax.
      }
      intermediate_path (iscontrpr1 H').
      - apply iscontr_uniqueness.
      - apply pathsinv0, iscontr_uniqueness.
    Qed.

    Lemma is_negative_fixed_point_from_pre_fixed_point
      (Hnegative_eq : is_negative_equalizing)
      (n : N) (Hn : is_negative_pre_fixed_point θ n)
      : is_negative_fixed_point θ n.
    Proof.
      eassert (f' : ∃! f' : N⟦n, (R ∙ L) n⟧, ε n · f' = identity ((R ∙ L) n)). {
        apply Hnegative_eq.
        abstract (rewrite !id_right; exact Hn).
      }
      induction f' as [f' _], f' as [f' Hf'].
      use make_is_z_isomorphism; [|use make_is_inverse_in_precat].
      - exact f'.
      - exact Hf'.
      - abstract (apply (is_epi_counit_from_negative_equalizing Hnegative_eq); fold ε;
                  rewrite assoc; etrans; [apply cancel_postcomposition, Hf'|];
                  now rewrite id_left, id_right).
    Defined.

    Lemma is_negative_fixed_point_to_pre_fixed_point
      (n : N) (Hn : is_negative_fixed_point θ n)
      : is_negative_pre_fixed_point θ n.
    Proof.
      refine (pre_comp_with_z_iso_is_inj
                (_ : is_z_isomorphism (#(R ∙ L) (is_z_isomorphism_mor Hn)))
                _ _ _).
      1: apply functor_on_is_z_isomorphism, is_z_isomorphism_inv.
      intermediate_path (identity ((R ∙ L) n)).
      - rewrite <- functor_comp, <- functor_id.
        apply (maponpaths (#(R ∙ L))).
        apply (is_inverse_in_precat2 Hn).
      - apply pathsinv0.
        refine (nat_trans_ax ε n _ _ @ _).
        apply (is_inverse_in_precat1 Hn).
    Qed.

    (** The negative equalizing requirement makes the negative pre-fixed and
        fixed points coincide *)
    Lemma is_negative_fixed_point_iff_pre_fixed_point
      (Hnegative_eq : is_negative_equalizing) (n : N)
      : is_negative_fixed_point θ n ≃ is_negative_pre_fixed_point θ n.
    Proof.
      apply weqimplimpl.
      - apply is_negative_fixed_point_to_pre_fixed_point.
      - apply (is_negative_fixed_point_from_pre_fixed_point Hnegative_eq).
      - apply isaprop_is_negative_fixed_point.
      - apply isaprop_is_negative_pre_fixed_point.
    Defined.
  End negative_fixed_point.

  (** Lemmas about the positive fixed point of the adjunction *)
  Section positive_fixed_point.
    Lemma is_monic_unit_from_positive_equalizing
      (Hpositive_eq : is_positive_equalizing) (p : P)
      : isMonic (η p).
    Proof.
      intros b f g H.
      apply (base_paths (B:=λ f', f' · η p = g · η p) (f,,H) (g,,idpath _)).
      eassert (H' : ∃! f' : P⟦b, p⟧, f' · η p = g · η p). {
        refine (Hpositive_eq _ _ (g · η p) _).
        now rewrite !assoc', (!nat_trans_ax η _ _ _).
      }
      intermediate_path (iscontrpr1 H').
      - apply iscontr_uniqueness.
      - apply pathsinv0, iscontr_uniqueness.
    Qed.

    Lemma is_positive_fixed_point_from_pre_fixed_point
      (Hpositive_eq : is_positive_equalizing)
      (p : P) (Hp : is_positive_pre_fixed_point θ p)
      : is_positive_fixed_point θ p.
    Proof.
      eassert (f' : ∃! f' : P⟦(L ∙ R) p, p⟧, f' · η p = identity ((L ∙ R) p)). {
        apply Hpositive_eq.
        abstract (rewrite !id_left; exact Hp).
      }
      induction f' as [f' _], f' as [f' Hf'].
      use make_is_z_isomorphism; [|use make_is_inverse_in_precat].
      - exact f'.
      - abstract (apply (is_monic_unit_from_positive_equalizing Hpositive_eq);
                  rewrite assoc';
                  etrans; [apply cancel_precomposition, Hf'|];
                  now rewrite id_right, id_left).
      - exact Hf'.
    Defined.

    Lemma is_positive_fixed_point_to_pre_fixed_point
      (p : P) (Hp : is_positive_fixed_point θ p)
      : is_positive_pre_fixed_point θ p.
    Proof.
      refine (post_comp_with_z_iso_is_inj
                (_ : is_z_isomorphism (#(L ∙ R) (is_z_isomorphism_mor Hp)))
                _ _ _).
      1: apply functor_on_is_z_isomorphism, is_z_isomorphism_inv.
      intermediate_path (identity ((L ∙ R) p)).
      - rewrite <- functor_comp, <- functor_id.
        apply (maponpaths (#(L ∙ R))).
        apply (is_inverse_in_precat1 Hp).
      - refine (_ @ nat_trans_ax η _ p _).
        apply pathsinv0, (is_inverse_in_precat2 Hp).
    Qed.

    (** The positive equalizing requirement makes the positive pre-fixed and
        fixed points coincide *)
    Lemma is_positive_fixed_point_iff_pre_fixed_point
      (Hpositive_eq : is_positive_equalizing) (p : P)
      : is_positive_fixed_point θ p ≃ is_positive_pre_fixed_point θ p.
    Proof.
      apply weqimplimpl.
      - apply is_positive_fixed_point_to_pre_fixed_point.
      - apply (is_positive_fixed_point_from_pre_fixed_point Hpositive_eq).
      - apply isaprop_is_positive_fixed_point.
      - apply isaprop_is_positive_pre_fixed_point.
    Defined.
  End positive_fixed_point.

End equalized.
Arguments is_negative_pre_fixed_point / _.
Arguments is_positive_pre_fixed_point / _.

(** ** The shift adjunction of a duploid is fully equalizing *)

Section shift_is_equalizing.
  Context (D : duploid).
  Let θ := adjunction_neg_l_to_pos_t D.

  Let ε' (a : D) : D⟦⇑⇓a, a⟧ := force ⇓a · unwrap a.
  Let ε_sec (a : D) : D⟦a, ⇑⇓a⟧ := wrap a · delay ⇓a.

  Local Lemma ε'_has_section (a : D)
    : ε_sec a · ε' a = identity a.
  Proof.
    etrans; [apply (assoc'_thunkable (wrap _) ummsolve)|].
    etrans; [apply cancel_precomposition, delay_force_left|].
    apply wrap_unwrap_id.
  Qed.

  Local Lemma ε_sec_natural (a b : D) (f : a --> b)
    : f · ε_sec b = ε_sec a · #⇑(#⇓f).
  Proof.
    subst ε_sec; cbn beta.
    etrans; [|apply (assoc_thunkable (wrap a) ummsolve)].
    etrans; [|apply cancel_precomposition, delay_natural].
    etrans; [|apply (assoc'_thunkable (wrap a) ummsolve)].
    etrans; [|apply cancel_postcomposition, wrap_natural].
    apply (assoc_linear (delay _) ummsolve).
  Qed.

  Local Lemma is_epi_ε' (a : sub_ob D ^⊖)
    : isEpi (adjcounit θ a).
  Proof.
    intros b f g Hfg; cbn in b.
    change (a -->{_lt} b) in f, g.
    apply base_paths in Hfg.
    apply (maponpaths (precomp_with (ε_sec a))) in Hfg.
    change (ε_sec a · (ε' a · f) = ε_sec a · (ε' a · g)) in Hfg.
    apply submm_mor_eq.
    refine (_ @ Hfg @ _).
    - now rewrite (assoc_linear f ummsolve), ε'_has_section, magmoid_id_left.
    - now rewrite (assoc_linear g ummsolve), ε'_has_section, magmoid_id_left.
  Qed.

  Let η' (a : D) : D⟦a, ⇓⇑a⟧ := wrap ⇑a ∘ delay a.
  Let η_ret (a : D) : D⟦⇓⇑a, a⟧ := force a ∘ unwrap ⇑a.

  Local Lemma η'_has_retract (a : D)
    : η_ret a ∘ η' a = identity a.
  Proof.
    etrans; [apply (assoc_linear (force _) ummsolve)|].
    etrans; [apply cancel_postcomposition, wrap_unwrap_right|].
    apply delay_force_id.
  Qed.

  Local Lemma η_ret_natural (a b : D) (f : a <-- b)
    : f ∘ η_ret b = η_ret a ∘ #⇓(#⇑f).
  Proof.
    subst η_ret; cbn beta.
    etrans; [|apply (assoc'_linear (force a) ummsolve)].
    etrans; [|apply cancel_postcomposition, pathsinv0, unwrap_natural].
    etrans; [|apply (assoc_linear (force a) ummsolve)].
    etrans; [|apply cancel_precomposition, pathsinv0, force_natural].
    apply (assoc'_thunkable (unwrap _) ummsolve).
  Qed.

  Local Lemma is_monic_η' (a : sub_ob D ^⊕)
    : isMonic (adjunit θ a).
  Proof.
    intros b f g Hfg; cbn in b.
    change (a <--{_lt} b) in f, g.
    apply base_paths in Hfg.
    apply (maponpaths (postcomp_with (η_ret a))) in Hfg.
    change (η_ret a ∘ (η' a ∘ f) = η_ret a ∘ (η' a ∘ g)) in Hfg.
    apply submm_mor_eq.
    refine (_ @ Hfg @ _).
    - now rewrite (assoc'_thunkable f ummsolve), η'_has_retract, magmoid_id_right.
    - now rewrite (assoc'_thunkable g ummsolve), η'_has_retract, magmoid_id_right.
  Qed.

  Lemma is_negative_equalizing_adjunction_neg_l_to_pos_t
    : is_negative_equalizing θ.
  Proof.
    apply is_negative_equalizing_from_is_epi_and_equation.
    1: apply is_epi_ε'.
    intros n m f Hf; cbn in n, m, f.
    set (f' := ε_sec n · submm_mor_mor f♭ : D⟦n, m⟧).
    assert (Hfb := pr12 f♭ : is_linear (M:=D) (submm_mor_mor f♭)).
    assert (Hf' : ε' n · f' = submm_mor_mor f♭). {
      etrans; [apply (assoc_linear _ Hfb)|].
      etrans; [|apply magmoid_id_left].
      etrans; [|apply cancel_postcomposition, (ε'_has_section _)].
      etrans; [|apply (assoc_linear _ Hfb)].
      apply base_paths in Hf.
      intermediate_path (ε_sec (⇑⇓n) · (#⇑(#⇓(ε' n)) · submm_mor_mor f♭));
        [|refine (maponpaths (λ f, ε_sec _ · f) _); exact Hf].
      etrans; [|apply (assoc'_linear _ Hfb)].
      apply cancel_postcomposition, ε_sec_natural.
    }
    assert (Hlinear : is_linear f'). {
      apply is_linear_of_force_unwrap.
      fold (ε' n).
      refine (Hf' @ _).
      apply pathsinv0.
      subst f' ε_sec; cbn.
      etrans. {
        refine (maponpaths (λ f, force _ · f) _).
        etrans; [refine (maponpaths (λ f, unwrap _ · f) _);
                 apply (assoc'_thunkable (wrap n) ummsolve (delay (⇓n)))|].
        etrans; [apply assoc_linear, (is_linear_compose (delay (⇓n)) (submm_mor_mor f♭)
                                        (is_linear_of_positive (delay ⇓n) ummsolve)
                                        Hfb)|].
        etrans; [apply cancel_postcomposition, unwrap_wrap_id|].
        apply magmoid_id_left.
      }
      etrans; [apply (assoc_linear _ Hfb)|].
      etrans; [apply cancel_postcomposition, force_delay_id|].
      apply magmoid_id_left.
    }
    apply hinhpr.
    use make_hfiber.
    - apply weq_negative_linear_mor.
      exact (make_submm_mor _l f' Hlinear).
    - apply submm_mor_eq, Hf'.
  Qed.

  Lemma is_positive_equalizing_adjunction_neg_l_to_pos_t
    : is_positive_equalizing θ.
  Proof.
    apply is_positive_equalizing_from_is_monic_and_equation.
    1: apply is_monic_η'.
    intros p q f Hf; cbn in p, q, f.
    set (f' := η_ret q ∘ submm_mor_mor f♯ : D⟦p, q⟧).
    assert (Hfs := pr22 f♯ : is_thunkable (M:=D) (submm_mor_mor f♯)).
    assert (Hf' : η' q ∘ f' = submm_mor_mor f♯). {
      etrans; [apply (assoc'_thunkable _ Hfs)|].
      etrans; [|apply magmoid_id_right].
      etrans; [|apply cancel_precomposition, (η'_has_retract _)].
      etrans; [|apply (assoc'_thunkable _ Hfs)].
      apply base_paths in Hf.
      intermediate_path (η_ret (⇓⇑q) ∘ (#⇓(#⇑(η' q)) ∘ submm_mor_mor f♯));
        [|refine (maponpaths (λ f, η_ret _ ∘ f) _); exact Hf].
      etrans; [|apply (assoc_thunkable _ Hfs)].
      etrans; [refine (maponpaths (λ x, submm_mor_mor f♯ · x) _);
               apply η_ret_natural|].
      reflexivity.
    }
    assert (Hthunkable : is_thunkable f'). {
      apply is_thunkable_of_delay_wrap.
      fold (η' q).
      refine (Hf' @ _).
      apply pathsinv0.
      subst f' η_ret; cbn.
      etrans. {
        refine (maponpaths (λ f, wrap _ ∘ f) _).
        etrans; [refine (maponpaths (λ f, delay _ ∘ f) _);
                 apply (assoc_linear (force q) ummsolve (unwrap (⇑q)))|].
        etrans; [apply assoc'_thunkable, (is_thunkable_compose (M:=D) (submm_mor_mor f♯) (unwrap (⇑q))
                                            Hfs
                                            (is_thunkable_of_negative (unwrap ⇑q) ummsolve))|].
        etrans; [apply cancel_precomposition, force_delay_id|].
        apply magmoid_id_right.
      }
      etrans; [apply (assoc'_thunkable _ Hfs)|].
      etrans; [apply cancel_precomposition, unwrap_wrap_id|].
      apply magmoid_id_right.
    }
    apply hinhpr.
    use make_hfiber.
    - apply weq_positive_thunkable_mor.
      exact (make_submm_mor _t f' Hthunkable).
    - apply submm_mor_eq, Hf'.
  Qed.

  Lemma is_fully_equalizing_adjunction_neg_l_to_pos_t
    : is_fully_equalizing θ.
  Proof.
    apply make_is_fully_equalizing.
    - apply is_negative_equalizing_adjunction_neg_l_to_pos_t.
    - apply is_positive_equalizing_adjunction_neg_l_to_pos_t.
  Qed.

End shift_is_equalizing.

(** ** Univalence of the envelope and oblique duploids *)

Section univalence.
  Context {N P : category} (θ : adjunction P N).
  Let L : P ⟶ N := left_functor θ.
  Let R : N ⟶ P := right_functor θ.
  Let η : functor_identity P ⟹ L ∙ R := adjunit θ.
  Let ε : R ∙ L ⟹ functor_identity N := adjcounit θ.

  (** *** Characterizations in terms of duploids

Given an adjunction [L ⊣ R], the following are equivalent:
1. [L ⊣ R] is negative equalizing.
2. [negative_to_oblique_duploid] is [fully_faithful].
3. [negative_to_oblique_duploid] is a [catiso].
4. [negative_to_envelope_duploid] is [fully_faithful].
5. [negative_to_envelope_duploid] is an [adj_equivalence_of_cats].

Dually, the following are equivalent:
A. [L ⊣ R] is positive equalizing.
B. [positive_to_oblique_duploid] is [fully_faithful].
C. [positive_to_oblique_duploid] is a [catiso].
D. [positive_to_envelope_duploid] is [fully_faithful].
E. [positive_to_envelope_duploid] is an [adj_equivalence_of_cats]. *)

  (** 1 <-> 2 *)
  Lemma ff_negative_to_oblique_iff_equ
    : is_negative_equalizing θ ≃ fully_faithful (negative_to_oblique_duploid θ).
  Proof.
    apply invweq.
    eapply weqcomp; [|apply is_negative_equalizing_weq_isweq_oblique_lift_negative].
    apply weqonsecfibers; intro n.
    apply weqonsecfibers; intro m.
    eapply weqcomp. {
      unshelve apply (weqonsecbase (X:=oblique_linear_mor θ n m)).
      apply (weqcomp (weq_oblique_linear_mor_oblique_linear_mor θ n
                        (oblique_ob_of_negative m))).
      exact (@weq_syn_negative_linear_mor (oblique_duploid θ)
               (negative_to_oblique_duploid θ n)
               (negative_to_oblique_duploid θ m)).
    }
    apply weqonsecfibers; intro f.
    apply weq_iscontrweqf.
    apply weqfibtototal; intro f'.
    eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
    eapply weqcomp; [|apply invweq, subtypeInjectivity; intro; apply propproperty].
    exact (idweq _).
  Qed.

  (** 2 <-> 3 *)
  Lemma is_catiso_negative_to_oblique_iff_ff
    : fully_faithful (negative_to_oblique_duploid θ)
        ≃ is_catiso (negative_to_oblique_duploid θ).
  Proof.
    apply dirprod_with_contr_r.
    apply iscontraprop1.
    - apply isapropisweq.
    - apply isweq_on_ob_negative_to_oblique_duploid.
  Qed.

  (** 1 <-> 3 *)
  Lemma is_catiso_negative_to_oblique_iff_equ
    : is_negative_equalizing θ ≃ is_catiso (negative_to_oblique_duploid θ).
  Proof.
    exact (weqcomp ff_negative_to_oblique_iff_equ
             is_catiso_negative_to_oblique_iff_ff).
  Qed.

  (** 1 <-> 4 *)
  Lemma ff_negative_to_envelope_iff_equ
    : is_negative_equalizing θ ≃ fully_faithful (negative_to_envelope_duploid θ).
  Proof.
    apply invweq.
    eapply weqcomp; [|apply is_negative_equalizing_weq_isweq_oblique_lift_negative].
    apply weqonsecfibers; intro n.
    apply weqonsecfibers; intro m.
    eapply weqcomp. {
      unshelve apply (weqonsecbase (X:=oblique_linear_mor θ n m)).
      apply (weqcomp (weq_envelope_linear_mor_oblique_linear_mor θ n
                        (envelope_ob_of_negative θ m))).
      exact (@weq_negative_linear_mor (envelope_duploid θ)
               (negative_to_envelope_duploid θ n)
               (negative_to_envelope_duploid θ m)).
    }
    apply weqonsecfibers; intro f.
    apply weq_iscontrweqf.
    apply weqfibtototal; intro f'.
    eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
    eapply weqcomp; [|apply invweq, subtypeInjectivity; intro; apply propproperty].
    exact (idweq _).
  Qed.

  (** 4 <-> 5 *)
  Lemma adj_equiv_negative_to_envelope_iff_ff
    : fully_faithful (negative_to_envelope_duploid θ)
        <-> adj_equivalence_of_cats (negative_to_envelope_duploid θ).
  Proof.
    split.
    - intro Hff.
      apply rad_equivalence_of_cats'.
      + exact Hff.
      + exact (split_eso_negative_to_envelope_duploid θ).
    - apply fully_faithful_from_equivalence.
  Qed.

  (** A <-> B *)
  Lemma ff_positive_to_oblique_iff_equ
    : is_positive_equalizing θ ≃ fully_faithful (positive_to_oblique_duploid θ).
  Proof.
    apply invweq.
    eapply weqcomp; [|apply is_positive_equalizing_weq_isweq_oblique_lift_positive].
    apply weqonsecfibers; intro p.
    apply weqonsecfibers; intro q.
    eapply weqcomp. {
      unshelve apply (weqonsecbase (X:=oblique_thunkable_mor θ p q)).
      apply (weqcomp (weq_oblique_thunkable_mor_oblique_thunkable_mor θ
                        (oblique_ob_of_positive p) q)).
      exact (@weq_syn_positive_thunkable_mor (oblique_duploid θ)
               (positive_to_oblique_duploid θ p)
               (positive_to_oblique_duploid θ q)).
    }
    apply weqonsecfibers; intro f.
    apply weq_iscontrweqf.
    apply weqfibtototal; intro f'.
    eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
    eapply weqcomp; [|apply invweq, subtypeInjectivity; intro; apply propproperty].
    exact (idweq _).
  Qed.

  (** B <-> C *)
  Lemma is_catiso_positive_to_oblique_iff_ff
    : fully_faithful (positive_to_oblique_duploid θ)
        ≃ is_catiso (positive_to_oblique_duploid θ).
  Proof.
    apply dirprod_with_contr_r.
    apply iscontraprop1.
    - apply isapropisweq.
    - apply isweq_on_ob_positive_to_oblique_duploid.
  Qed.

  (** 1 <-> 3 *)
  Lemma is_catiso_positive_to_oblique_iff_equ
    : is_positive_equalizing θ ≃ is_catiso (positive_to_oblique_duploid θ).
  Proof.
    exact (weqcomp ff_positive_to_oblique_iff_equ
             is_catiso_positive_to_oblique_iff_ff).
  Qed.

  (** 1 <-> 4 *)
  Lemma ff_positive_to_envelope_iff_equ
    : is_positive_equalizing θ ≃ fully_faithful (positive_to_envelope_duploid θ).
  Proof.
    apply invweq.
    eapply weqcomp; [|apply is_positive_equalizing_weq_isweq_oblique_lift_positive].
    apply weqonsecfibers; intro p.
    apply weqonsecfibers; intro q.
    eapply weqcomp. {
      unshelve apply (weqonsecbase (X:=oblique_thunkable_mor θ p q)).
      apply (weqcomp (weq_envelope_thunkable_mor_oblique_thunkable_mor θ
                        (envelope_ob_of_positive θ p) q)).
      exact (@weq_positive_thunkable_mor (envelope_duploid θ)
               (positive_to_envelope_duploid θ p)
               (positive_to_envelope_duploid θ q)).
    }
    apply weqonsecfibers; intro f.
    apply weq_iscontrweqf.
    apply weqfibtototal; intro f'.
    eapply weqcomp; [apply subtypeInjectivity; intro; apply propproperty|].
    eapply weqcomp; [|apply invweq, subtypeInjectivity; intro; apply propproperty].
    exact (idweq _).
  Qed.

  (** 4 <-> 5 *)
  Lemma adj_equiv_positive_to_envelope_iff_ff
    : fully_faithful (positive_to_envelope_duploid θ)
        <-> adj_equivalence_of_cats (positive_to_envelope_duploid θ).
  Proof.
    split.
    - intro Hff.
      apply rad_equivalence_of_cats'.
      + exact Hff.
      + exact (split_eso_positive_to_envelope_duploid θ).
    - apply fully_faithful_from_equivalence.
  Qed.

  (** *** Univalence of the oblique duploid *)

  Lemma is_univalent_oblique_duploid_iff
    (Hequ : is_fully_equalizing θ)
    : (is_univalent P × is_univalent N)
        ≃ is_split_dupl_univalent (oblique_duploid θ).
  Proof.
    apply weqdirprodf.
    - apply is_univalent_catiso_iff.
      exists (positive_to_oblique_duploid θ).
      apply is_catiso_positive_to_oblique_iff_equ, Hequ.
    - apply is_univalent_catiso_iff.
      exists (negative_to_oblique_duploid θ).
      apply is_catiso_negative_to_oblique_iff_equ, Hequ.
  Qed.

  (** *** Univalence of the envelope duploid *)

  Lemma envelope_chosen_negative_ob_eq
    (ua : is_univalent P)
    (a : envelope_ob θ)
    (H : envelope_chosen_negative θ a)
    : a = sub_ob_ob ⇑a.
  Proof.
    induction a as [[[p n] c] Hc].
    cbn in c; change (is_z_isomorphism c♯) in H.
    apply subtypePath'; [|apply propproperty]; cbn; clear Hc.
    assert (Hcross : edges_to_refl (G:=P) (R n) = (p,, make_z_iso' c♯ H)).
    { apply proofirrelevance, is_univalent_to_isaprop_edges_to, ua. }
    apply total2_paths_equiv in Hcross.
    induction Hcross as [Hp Hcross]; cbn in Hp, Hcross.
    induction Hp; cbn in Hcross.
    apply pair_path_in2.
    apply oblique_mor_positive_path; cbn.
    apply (base_paths _ _ (!Hcross)).
  Defined.

  Lemma envelope_chosen_positive_ob_eq
    (ua : is_univalent N)
    (a : envelope_ob θ)
    (H : envelope_chosen_positive θ a)
    : a = sub_ob_ob ⇓a.
  Proof.
    induction a as [[[p n] c] Hc].
    cbn in c; change (is_z_isomorphism c♭) in H.
    apply subtypePath'; [|apply propproperty]; cbn; clear Hc.
    assert (Hcross : edges_from_refl (G:=N) (L p) = (n,, make_z_iso' c♭ H)).
    { apply proofirrelevance, is_univalent_to_isaprop_edges_from, ua. }
    apply total2_paths_equiv in Hcross.
    induction Hcross as [Hp Hcross]; cbn in Hp, Hcross.
    induction Hp; cbn in Hcross.
    apply pair_path_in2.
    apply oblique_mor_negative_path; cbn.
    apply (base_paths _ _ (!Hcross)).
  Defined.

  Lemma envelope_chosen_negative_from_negative
    (Hpositive_eq : is_positive_equalizing θ)
    (a : envelope_ob θ) (H : is_negative a)
    : envelope_chosen_negative θ a.
  Proof.
    apply (squash_to_prop (envelope_ob_to_envelope_polarization θ a)
             (isaprop_envelope_chosen_negative θ a)).
    intro Hchoice.
    induction Hchoice as [Hnegative|Hpositive]; [exact Hnegative|].
    red; rewrite <- oblique_mor_negative_transpose.
    change (is_z_isomorphism (η (π⊕ a) · #R cross(a)♭)).
    apply is_z_isomorphism_comp.
    - apply (is_positive_fixed_point_from_pre_fixed_point θ Hpositive_eq).
      apply is_negative_envelope_downshift_iff_pre_fixed_point.
      change (is_negative (M:=envelope_duploid θ) ⇓a).
      refine (is_negative_of_lt_iso (a:=a) _ H).
      apply lt_iso_downshift_of_positive.
      apply is_positive_of_envelope_chosen_positive, Hpositive.
    - apply (functor_on_is_z_isomorphism R).
      exact Hpositive.
  Qed.

  Lemma envelope_chosen_positive_from_positive
    (Hnegative_eq : is_negative_equalizing θ)
    (a : envelope_ob θ) (H : is_positive a)
    : envelope_chosen_positive θ a.
  Proof.
    apply (squash_to_prop (envelope_ob_to_envelope_polarization θ a)
             (isaprop_envelope_chosen_positive θ a)).
    intro Hchoice.
    induction Hchoice as [Hnegative|Hpositive]; [|exact Hpositive].
    red; rewrite <- oblique_mor_positive_transpose.
    change (is_z_isomorphism (#L cross(a)♯ · ε (π⊖ a))).
    apply is_z_isomorphism_comp.
    - apply (functor_on_is_z_isomorphism L).
      exact Hnegative.
    - apply (is_negative_fixed_point_from_pre_fixed_point θ Hnegative_eq).
      apply is_positive_envelope_upshift_iff_pre_fixed_point.
      change (is_positive (M:=envelope_duploid θ) ⇑a).
      refine (is_positive_of_lt_iso (a:=a) _ H).
      apply submm_iso_inv, lt_iso_upshift_of_negative.
      apply is_negative_of_envelope_chosen_negative, Hnegative.
  Qed.

  Lemma envelope_negative_ob_eq
    (Hpositive_eq : is_positive_equalizing θ)
    (ua : is_univalent P)
    (a : envelope_ob θ) (H : is_negative a)
    : a = sub_ob_ob ⇑a.
  Proof.
    apply (envelope_chosen_negative_ob_eq ua).
    now apply envelope_chosen_negative_from_negative.
  Defined.

  Lemma envelope_positive_ob_eq
    (Hnegative_eq : is_negative_equalizing θ)
    (ua : is_univalent N)
    (a : envelope_ob θ) (H : is_positive a)
    : a = sub_ob_ob ⇓a.
  Proof.
    apply (envelope_chosen_positive_ob_eq ua).
    now apply envelope_chosen_positive_from_positive.
  Defined.

  Lemma isweq_on_ob_negative_to_envelope_duploid
    (Hpositive_eq : is_positive_equalizing θ)
    (ua : is_univalent P)
    : isweq (negative_to_envelope_duploid θ).
  Proof.
    use isweq_iso.
    - intro a; cbn in a.
      exact (π⊖ (sub_ob_ob a : envelope_ob _)).
    - easy.
    - intro a.
      apply subtypePath'; [|apply propproperty].
      apply pathsinv0, (envelope_negative_ob_eq Hpositive_eq ua).
      submagmoid.
  Defined.

  Theorem is_catiso_negative_to_envelope_duploid
    (Hequ : is_fully_equalizing θ)
    (ua : is_univalent P)
    : is_catiso (negative_to_envelope_duploid θ).
  Proof.
    split.
    - apply ff_negative_to_envelope_iff_equ.
      exact (is_fully_equalizing_to_is_negative_equalizing _ Hequ).
    - apply isweq_on_ob_negative_to_envelope_duploid.
      + exact (is_fully_equalizing_to_is_positive_equalizing _ Hequ).
      + exact ua.
  Defined.

  Lemma isweq_on_ob_positive_to_envelope_duploid
    (Hnegative_eq : is_negative_equalizing θ)
    (ua : is_univalent N)
    : isweq (positive_to_envelope_duploid θ).
  Proof.
    use isweq_iso.
    - intro a; cbn in a.
      exact (π⊕ (sub_ob_ob a : envelope_ob _)).
    - easy.
    - intro a.
      apply subtypePath'; [|apply propproperty].
      apply pathsinv0, (envelope_positive_ob_eq Hnegative_eq ua).
      submagmoid.
  Defined.

  Theorem is_catiso_positive_to_envelope_duploid
    (Hequ : is_fully_equalizing θ)
    (ua : is_univalent N)
    : is_catiso (positive_to_envelope_duploid θ).
  Proof.
    split.
    - apply ff_positive_to_envelope_iff_equ.
      exact (is_fully_equalizing_to_is_positive_equalizing _ Hequ).
    - apply isweq_on_ob_positive_to_envelope_duploid.
      + exact (is_fully_equalizing_to_is_negative_equalizing _ Hequ).
      + exact ua.
  Defined.

  Corollary is_univalent_envelope_duploid
    (Hequ : is_fully_equalizing θ)
    (ua₁ : is_univalent P)
    (ua₂ : is_univalent N)
    : is_dupl_univalent (envelope_duploid θ).
  Proof.
    apply is_dupl_univalent_from_polarized.
    - refine (is_univalent_catiso_f P (envelope_duploid θ)⁺ₜ _ ua₁).
      exists (positive_to_envelope_duploid θ).
      apply (is_catiso_positive_to_envelope_duploid Hequ ua₂).
    - refine (is_univalent_catiso_f N (envelope_duploid θ)⁻ₗ _ ua₂).
      exists (negative_to_envelope_duploid θ).
      apply (is_catiso_negative_to_envelope_duploid Hequ ua₁).
  Qed.

End univalence.
