(********************************************************************************

 Univalence of Unital Magmoids

 Author: B. Szilvasy
 October 2026

 We define what it means for a unital magmoid to be univalent: that
 identifications are equivalent to linear-and-thunkable-and-intermediate
 isomorphisms.  We show some properties of equivalences (fully-faithful functors
 which are surjective up to linear-and-thunkable(-and-intermediate) isomorphism)
 between univalent unital magmoids; in particular that they become isomorphisms.

 Contents:
 1. Internal univalence in unital magmoids
 1.1. Definition of univalence
 1.2. Simple consequences of univalence
 2. Weak equivalences to strong equivalences
 2.1 Generically over [wide_subcategory]s
 2.2 Specifically for [lt] and [lti]
 3. Univalent unital magmoids are identified if they are weakly equivalent

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.IdentitySystems.RXGraph.
Require Import UniMath.IdentitySystems.Examples.
Require Import UniMath.IdentitySystems.RXGraphOfRXGraphs.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryRXGraph.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Isos.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.PolarizedSubcategories.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Functors.

Local Open Scope cat.
Local Open Scope unital_magmoid.
Local Open Scope rxgraph.

(** ** Internal univalence in unital magmoids *)

Section internal_univalence.
  Context (M : unital_magmoid) (P : wide_submagmoid M).

  (** *** Definition of univalence *)

  Definition submm_rxgraph : rxgraph.
  Proof.
    use make_rxgraph.
    - exact (ob M).
    - exact (submm_iso P).
    - exact (submm_iso_identity P).
  Defined.

  Definition is_submm_univalent : UU
    := is_univalent submm_rxgraph.

  Definition weq_id_to_submm_iso
    (H : is_submm_univalent) (a b : M)
    : a = b ≃ submm_iso P a b
    := make_weq _ (H a b).

  Definition submm_iso_to_id
    (H : is_submm_univalent)
    {a b : M} (p : submm_iso P a b)
    : a = b
    := invmap (weq_id_to_submm_iso H a b) p.

  Lemma submm_iso_to_id_retract
    (H : is_submm_univalent)
    {a b : M} (p : a = b)
    : submm_iso_to_id H (id_to_submm_iso P p) = p.
  Proof.
    apply (homotinvweqweq (weq_id_to_submm_iso H a b)).
  Qed.

  Lemma submm_iso_to_id_section
    (H : is_submm_univalent)
    {a b : M} (p : submm_iso P a b)
    : id_to_submm_iso P (submm_iso_to_id H p) = p.
  Proof.
    apply (homotweqinvweq (weq_id_to_submm_iso H a b)).
  Qed.

  Lemma submm_isos_from_paths
    (H : is_submm_univalent)
    (a b : M)
    (p : submm_iso P a b)
    : PathPair (B:=λ b, submm_iso P a b)
        (@edges_from_refl submm_rxgraph a)
        (b,, p).
  Proof.
    apply total2_paths_equiv.
    apply (proofirrelevance (edges_from submm_rxgraph a)).
    apply is_univalent_to_isaprop_edges_from, H.
  Qed.

  Lemma submm_isos_to_paths
    (H : is_submm_univalent)
    (a b : M)
    (p : submm_iso P a b)
    : PathPair (B:=λ a, submm_iso P a b)
        (@edges_to_refl submm_rxgraph b)
        (a,, p).
  Proof.
    apply total2_paths_equiv.
    apply (proofirrelevance (edges_to submm_rxgraph b)).
    apply is_univalent_to_isaprop_edges_to, H.
  Qed.

End internal_univalence.

Definition is_um_univalent (M : unital_magmoid) : UU
  := is_submm_univalent M _lti.
Definition univalent_unital_magmoid : UU
  := total2 is_um_univalent.
Coercion univalent_unital_magmoid_to_unital_magmoid
  (M : univalent_unital_magmoid) : unital_magmoid := pr1 M.
Coercion unital_magmoid_univalence
  (M : univalent_unital_magmoid) : is_um_univalent M := pr2 M.
Definition make_univalent_unital_magmoid
  (M : unital_magmoid) (ua : is_um_univalent M)
  : univalent_unital_magmoid
  := M,, ua.

(** *** Simple consequences of univalence **)

Section up_uniqueness.
  Lemma isaprop_linear_isos_from_negative
    {M : unital_magmoid}
    (ua : is_um_univalent M)
    (b : M)
    : isaprop (∑ (a : sub_ob ^⊖), submm_iso _l a b).
  Proof.
    apply invproofirrelevance.
    intros [[a Ha] e] [[a' Ha'] e'].
    transparent assert (ee' : (lti_iso a a')). {
      refine (submm_iso_incl M _l _lti _
                (subcat_iso_compose _ e (submm_iso_inv _ e'))).
      split; (intros f Hf; split; [split|];
              [ exact Hf
              | now apply is_thunkable_of_negative
              | now apply is_intermediate_of_negative ]).
    }
    induction (submm_isos_from_paths M _lti ua _ _ ee') as [Haa' Hee'].
    apply submm_iso_eq_mor in Hee'.
    cbn in Haa', Hee'.
    clear ee'; cbn in *.
    induction Haa'; cbn in Hee'.
    induction (proofirrelevance_hProp (^⊖ a) Ha Ha').
    apply pair_path_in2, (subcat_iso_eq _l).
    apply subcat_iso_eq_from_identity.
    exact (!Hee').
  Qed.

  Lemma isaprop_thunkable_isos_from_positive
    {M : unital_magmoid}
    (ua : is_um_univalent M)
    (b : M)
    : isaprop (∑ (a : sub_ob ^⊕), submm_iso _t a b).
  Proof.
    apply invproofirrelevance.
    intros [[a Ha] e] [[a' Ha'] e'].
    transparent assert (ee' : (lti_iso a a')). {
      refine (submm_iso_incl M _t _lti _
                (subcat_iso_compose _ e (submm_iso_inv _ e'))).
      split; (intros f Hf; split; [split|];
              [ now apply is_linear_of_positive
              | exact Hf
              | now apply is_intermediate_of_positive ]).
    }
    induction (submm_isos_from_paths M _lti ua _ _ ee') as [Haa' Hee'].
    apply submm_iso_eq_mor in Hee'.
    cbn in Haa', Hee'.
    clear ee'; cbn in *.
    induction Haa'; cbn in Hee'.
    induction (proofirrelevance_hProp (^⊕ a) Ha Ha').
    apply pair_path_in2, (subcat_iso_eq _t).
    apply subcat_iso_eq_from_identity.
    exact (!Hee').
  Qed.
End up_uniqueness.

(** ** Weak equivalences to strong equivalences *)

Section upgrade.
  Lemma issurjective_from_submm_eso
    {C : unital_premagmoid_data}
    {D : unital_magmoid}
    (F : functor C D)
    (P : wide_submagmoid D)
    (ua : is_submm_univalent D P)
    (Heso : submm_essentially_surjective F P)
    : issurjective F.
  Proof.
    intro b.
    refine (hinhfun _ (Heso b)).
    apply totalfun; intro a.
    apply submm_iso_to_id, ua.
  Defined.

  (** *** Generically over [wide_subcategory]s *)
  Section generic.
    Context {C D : unital_magmoid}
      (F : functor C D)
      (P₁ : wide_subcategory C)
      (P₂ : wide_subcategory D)
      (ua₁ : is_submm_univalent C P₁)
      (ua₂ : is_submm_univalent D P₂).

    Hypothesis Hreflects
      : reflects_submm F (isc_subcat_iso P₁) (isc_subcat_iso P₂).

    Lemma isaprop_submm_fibre (b : D)
      (HF : fully_faithful F)
      : isaprop (submm_fibre F P₂ b).
    Proof.
      apply invproofirrelevance.
      intros [a e] [a' e'].
      pose (ee' := subcat_iso_compose _ e (submm_iso_inv _ e')).
      transparent assert (ee'inv : (submm_iso P₁ a a')). {
        use make_submm_iso.
        - exact (fully_faithful_inv_hom HF _ _ ee').
        - apply Hreflects.
          refine (transportf (is_submm_iso P₂) _ ee').
          apply pathsinv0, (homotweqinvweq (weq_from_fully_faithful HF a a')).
      }
      induction (submm_isos_from_paths C P₁ ua₁ _ _ ee'inv)
        as [Ha He]; cbn in Ha, He.
      induction Ha; cbn in He.
      apply pair_path_in2, subcat_iso_eq.
      apply subcat_iso_eq_from_identity.
      rewrite <- (functor_id F a).
      apply pathsinv0, (pathsweq1' (weq_from_fully_faithful HF a a)).
      exact (submm_iso_eq_mor _ _ _ He).
    Qed.

    Theorem isaprop_submm_split_essentially_surjective
      (HF : fully_faithful F)
      : isaprop (submm_split_essentially_surjective F P₂).
    Proof.
      apply impred_isaprop; intro.
      apply isaprop_submm_fibre, HF.
    Qed.

    Corollary isaprop_is_submm_strong_equiv
      : isaprop (is_submm_strong_equiv F P₂).
    Proof.
      apply isofhleveltotal2.
      - apply isaprop_fully_faithful.
      - intro HF.
        apply isaprop_submm_split_essentially_surjective, HF.
    Qed.

    Theorem submm_eso_upgrade
      (HF : fully_faithful F)
      (Heso : submm_essentially_surjective F P₂)
      : submm_split_essentially_surjective F P₂.
    Proof.
      intro b.
      refine (hinhprinv (make_hProp _ _) (Heso b)).
      apply isaprop_submm_fibre, HF.
    Defined.

    Corollary weq_submm_eso (HF : fully_faithful F)
      : submm_essentially_surjective F P₂
          ≃ submm_split_essentially_surjective F P₂.
    Proof.
      use weqimplimpl.
      - apply submm_eso_upgrade, HF.
      - apply submm_split_essentially_surjective_weaken.
      - apply isaprop_submm_essentially_surjective.
      - apply isaprop_submm_split_essentially_surjective, HF.
    Defined.

    Corollary submm_weak_equiv_upgrade
      (Hequiv : is_submm_weak_equiv F P₂)
      : is_submm_strong_equiv F P₂.
    Proof.
      split.
      - exact Hequiv.
      - apply submm_eso_upgrade; exact Hequiv.
    Defined.

    Corollary weq_submm_equiv (HF : fully_faithful F)
      : is_submm_weak_equiv F P₂
          ≃ is_submm_strong_equiv F P₂.
    Proof.
      use weqimplimpl.
      - apply submm_weak_equiv_upgrade.
      - intro H; split; exact H.
      - apply isaprop_is_submm_weak_equiv.
      - apply isaprop_is_submm_strong_equiv.
    Defined.

    Theorem isincl_fully_faithful_from_submm_univalent
      (HF : fully_faithful F)
      : isincl F.
    Proof.
      intro b.
      apply (isofhlevelweqb 1 (Y:=submm_fibre F P₂ b)).
      - apply weqfibtototal; intro a.
        exact (weq_id_to_submm_iso _ _ ua₂ (F a) b).
      - apply isaprop_submm_fibre, HF.
    Qed.

    Theorem isweq_submm_weak_equiv
      (HF : is_submm_weak_equiv F P₂)
      : isweq F.
    Proof.
      apply isweqinclandsurj.
      - apply isincl_fully_faithful_from_submm_univalent, HF.
      - eapply issurjective_from_submm_eso.
        + exact ua₂.
        + exact HF.
    Defined.
  End generic.

  (** *** Specifically for [lt] and [lti] *)

  Section lti_fibres.
    Context {C D : unital_magmoid}
      (F : functor C D).
    Hypothesis ualt : is_submm_univalent C _lt.
    Hypothesis ualt₂ : is_submm_univalent D _lt.
    Hypothesis ualti : is_submm_univalent C _lti.
    Hypothesis ualti₂ : is_submm_univalent D _lti.

    (** [lt] *)
    Theorem isaprop_lt_fibre
      (b : D)
      (Hff : fully_faithful F)
      : isaprop (submm_fibre F _lt b).
    Proof.
      apply (isaprop_submm_fibre F _lt _lt ualt
               (reflects_lt_iso_ff F Hff)).
      exact Hff.
    Qed.

    Theorem lt_weak_equiv_upgrade
      (Hequiv : is_submm_weak_equiv F _lt)
      : is_submm_strong_equiv F _lt.
    Proof.
      split.
      - exact Hequiv.
      - apply (submm_eso_upgrade F _lt _lt ualt
                 (reflects_lt_iso_ff F Hequiv)).
        + exact Hequiv.
        + exact Hequiv.
    Defined.

    Theorem isweq_lt_weak_equiv
      (Hequiv : is_submm_weak_equiv F _lt)
      : isweq F.
    Proof.
      apply (isweq_submm_weak_equiv F _lt _lt ualt ualt₂
               (reflects_lt_iso_ff F Hequiv)).
      exact Hequiv.
    Qed.

    Theorem is_catiso_lt_weak_equiv
      (Hequiv : is_submm_weak_equiv F _lt)
      : is_catiso F.
    Proof.
      split.
      - exact Hequiv.
      - apply isweq_lt_weak_equiv, Hequiv.
    Qed.

    (** [lt] *)
    Theorem isaprop_lti_fibre
      (b : D)
      (Hff : fully_faithful F)
      : isaprop (submm_fibre F _lti b).
    Proof.
      apply (isaprop_submm_fibre F _lti _lti ualti
               (reflects_lti_iso_ff F Hff)).
      exact Hff.
    Qed.

    Theorem lti_weak_equiv_upgrade
      (Hequiv : is_submm_weak_equiv F _lti)
      : is_submm_strong_equiv F _lti.
    Proof.
      split.
      - exact Hequiv.
      - apply (submm_eso_upgrade F _lti _lti ualti
                 (reflects_lti_iso_ff F Hequiv)).
        + exact Hequiv.
        + exact Hequiv.
    Defined.

    Theorem isweq_lti_weak_equiv
      (Hequiv : is_submm_weak_equiv F _lti)
      : isweq F.
    Proof.
      apply (isweq_submm_weak_equiv F _lti _lti ualti ualti₂
               (reflects_lti_iso_ff F Hequiv)).
      exact Hequiv.
    Qed.

    Theorem is_catiso_lti_weak_equiv
      (Hequiv : is_submm_weak_equiv F _lti)
      : is_catiso F.
    Proof.
      split.
      - exact Hequiv.
      - apply isweq_lti_weak_equiv, Hequiv.
    Qed.
  End lti_fibres.

End upgrade.

(** ** Univalent unital magmoids are identified if they are weakly equivalent *)

Section external_univalence.

  (* This is not univalent. *)
  Definition unital_premagmoid_rxgraph : rxgraph.
  Proof.
    use make_rxgraph.
    - exact unital_premagmoid.
    - exact catiso.
    - exact identity_catiso.
  Defined.

  Definition unital_magmoid_rxgraph : rxgraph.
  Proof.
    use make_rxgraph.
    - exact unital_magmoid.
    - exact catiso.
    - exact identity_catiso.
  Defined.

  Theorem is_univalent_unital_magmoid_rxgraph
    : is_univalent unital_magmoid_rxgraph.
  Proof.
    use is_univalent_rxgraph_iso_f.
    - exact (sub_rxgraph precategory_data_rxgraph (λ (C : precategory_data),
                 has_homsets C × is_unital_premagmoid C)).
    - use make_rxgraph_iso.
      + use weq_iso.
        * intros [C [H₁ H₂]]; exact ((C,, H₂),, H₁).
        * intros [[C H₂] H₁]; exact (C,, H₁,, H₂).
        * easy.
        * easy.
      + intros C D; cbn.
        exact (idweq _).
      + easy.
    - apply is_univalent_sub_rxgraph.
      + apply is_univalent_precategory_data_rxgraph.
      + intro M.
        apply isaprop_assume_it_is.
        intros [hs H].
        apply isapropdirprod.
        * apply isaprop_has_homsets.
        * apply isaprop_is_unital_premagmoid, hs.
  Qed.

  Theorem weq_is_catiso_is_lti_weak_equiv
    {C D : unital_magmoid}
    (HC : is_um_univalent C)
    (Hd : is_um_univalent D)
    (F : functor C D)
    : is_catiso F ≃ is_submm_weak_equiv F _lti.
  Proof.
    use weqimplimpl.
    - intro HF; split.
      + apply HF.
      + apply submm_split_essentially_surjective_weaken.
        apply (is_submm_eso_from_weq F _lti), HF.
    - intros HF.
      now apply is_catiso_lti_weak_equiv.
    - apply isaprop_is_catiso.
    - apply isaprop_is_submm_weak_equiv.
  Defined.

  Theorem weq_is_catiso_is_lt_weak_equiv
    {C D : unital_magmoid}
    (HC : is_submm_univalent C _lt)
    (Hd : is_submm_univalent D _lt)
    (F : functor C D)
    : is_catiso F ≃ is_submm_weak_equiv F _lt.
  Proof.
    use weqimplimpl.
    - intro HF; split.
      + apply HF.
      + apply submm_split_essentially_surjective_weaken.
        apply (is_submm_eso_from_weq F _lt), HF.
    - intros HF.
      now apply is_catiso_lt_weak_equiv.
    - apply isaprop_is_catiso.
    - apply isaprop_is_submm_weak_equiv.
  Defined.

  Definition univalent_unital_magmoid_rxgraph : rxgraph.
  Proof.
    use make_rxgraph.
    - exact univalent_unital_magmoid.
    - intros C D; exact (submm_weak_equiv C D _lti).
    - intro M; apply submm_weak_equiv_identity.
  Defined.

  Definition is_univalent_univalent_unital_magmoid_rxgraph
    : is_univalent univalent_unital_magmoid_rxgraph.
  Proof.
    apply is_univalent_from_weq.
    intros C D.
    refine (weqcomp
              (@weq_id_to_edge
                 (sub_rxgraph unital_magmoid_rxgraph is_um_univalent)
                 _ C D) _). {
      apply is_univalent_sub_rxgraph.
      - apply is_univalent_unital_magmoid_rxgraph.
      - intro; apply isaprop_is_univalent.
    }
    apply weqfibtototal; intro F.
    apply weq_is_catiso_is_lti_weak_equiv;
      apply unital_magmoid_univalence.
  Qed.

End external_univalence.
