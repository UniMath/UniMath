(********************************************************************************

 Isomorphisms in Unital Magmoids

 Contents:
 1. Inverses in wide submagmoids
 2. Rewriting lemmas of isomorphisms

 Author: B. Szilvasy
 January 2026

 ********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Core.
Require Import UniMath.CategoryTheory.Nonassociative.UnitalMagmoids.Submagmoids.

Local Open Scope cat.
Local Open Scope unital_magmoid.

(** ** Inverses in wide submagmoids, definitions *)

Lemma isaprop_is_inverse_in_precat_of_magmoid
  {M : unital_magmoid} {a b : M} (f : a --> b) (g : a <-- b) : isaprop (is_inverse_in_precat f g).
Proof. apply isapropdirprod; apply unital_magmoid_has_homsets. Qed.
Definition ish_inverse_in_unital_magmoid
  {M : unital_magmoid} {a b : M} (f : a --> b) (g : a <-- b)
  : hProp
  := make_hProp (is_inverse_in_precat f g) (isaprop_is_inverse_in_precat_of_magmoid f g).

Lemma is_inverse_in_precat_identity_of_magmoid {M : unital_magmoid} (a : M)
  : is_inverse_in_precat (identity a) (identity a).
Proof.
  apply make_is_inverse_in_precat;
    apply magmoid_id_left.
Qed.

Section wide_submagmoid_inverses.
  Context {M : unital_magmoid} (P : wide_submagmoid M).

  Definition has_submm_inverse
    {a b : M} (f : a --> b) : UU
    := ∑ (g : b -->{P} a), ish_inverse_in_unital_magmoid f g.

  Lemma isaset_has_submm_inverse
    {a b : M} (f : a --> b)
    : isaset (has_submm_inverse f).
  Proof.
    apply isaset_total2.
    - apply isaset_submm_mor.
    - intro g; apply isasetaprop, propproperty.
  Qed.

  Example weq_has_submm_inverse_is_z_isomorphism
    {a b : M} (f : a -->{P} b)
    : has_submm_inverse f
      ≃ is_z_isomorphism (C:=wide_submagmoid_carrier_data M P) f.
  Proof.
    apply weqfibtototal; intro g.
    apply weqdirprodf.
    - exact (submm_mor_eq (f ·{P} g) (submm_identity P a)).
    - exact (submm_mor_eq (g ·{P} f) (submm_identity P b)).
  Defined.

  Definition submm_inv_mor
    {a b : M} {f : a --> b} (g : has_submm_inverse f)
    : b -->{P} a := pr1 g.
  Coercion has_submm_inverse_is_inverse
    {a b : M} {f : a --> b} (g : has_submm_inverse f)
    : is_inverse_in_precat f (submm_inv_mor g) := pr2 g.

  Definition make_has_submm_inverse
    {a b : M} (f : a --> b) (g : b -->{P} a)
    (Hfg : is_inverse_in_precat f g)
    : has_submm_inverse f
    := g,, Hfg.

  Definition make_has_submm_inverse'
    {a b : M} (f : a --> b) (g : b --> a)
    (Hg : P b a g)
    (Hfg : ish_inverse_in_unital_magmoid f g)
    : has_submm_inverse f
    := make_has_submm_inverse f
         (make_submm_mor P g Hg)
         Hfg.

  Lemma isaprop_has_submm_inverse_from_assoc
    (a b : M) (f : a --> b)
    (H : ∏ (c d : M) (g : c --> a) (h : b --> d),
        P _ _ g -> P _ _ h ->
        (g · f) · h = g · (f · h))
    : isaprop (has_submm_inverse f).
  Proof.
    apply invproofirrelevance; intros g g'.
    apply carrier_eq, submm_mor_eq.
    refine (!magmoid_id_left _ @ _ @ magmoid_id_right _).
    rewrite <- (is_inverse_in_precat1 g).
    rewrite <- (is_inverse_in_precat2 g').
    apply H; apply (submm_mor_property P).
  Qed.

  Definition is_submm_iso
    {a b : M} (f : a --> b)
    := P a b f × has_submm_inverse f.

  Lemma isaset_is_submm_iso
    {a b : M} (f : a --> b)
    : isaset (is_submm_iso f).
  Proof.
    apply isasetdirprod.
    - apply isasetaprop, propproperty.
    - apply isaset_has_submm_inverse.
  Qed.

  Definition is_submm_iso_property
    {a b : M} {f : a --> b} (g : is_submm_iso f)
    : P _ _ f := pr1 g.
  Coercion is_submm_iso_to_has_submm_inverse
    {a b : M} {f : a --> b} (g : is_submm_iso f)
    : has_submm_inverse f
    := pr2 g.

  Definition make_is_submm_iso
    {a b : M} (f : a --> b)
    (Hf : P a b f)
    (g : has_submm_inverse f)
    : is_submm_iso f
    := Hf,, g.

  Definition make_is_submm_iso'
    {a b : M}
    (f : a --> b)
    (g : b --> a)
    (Hf : P a b f)
    (Hg : P b a g)
    (Hfg : is_inverse_in_precat f g)
    : is_submm_iso f.
  Proof.
    use make_is_submm_iso.
    - exact Hf.
    - use make_has_submm_inverse.
      + use make_submm_mor.
        * exact g.
        * exact Hg.
      + exact Hfg.
  Defined.

  Definition is_submm_iso_eq
    {a b : M} (f : a --> b)
    (finv finv' : is_submm_iso f)
    (H : submm_mor_mor (submm_inv_mor finv) = submm_inv_mor finv')
    : finv = finv'.
  Proof.
    apply dirprod_paths.
    - apply propproperty.
    - apply carrier_eq, submm_mor_eq, H.
  Qed.

  Definition submm_iso (a b : M) : UU
    := ∑ (f : a --> b), is_submm_iso f.

  Coercion submm_iso_mor
    {a b : M} (f : submm_iso a b)
    : a -->{P} b
    := make_submm_mor P (pr1 f) (is_submm_iso_property (pr2 f)).
  Coercion submm_iso_has_submm_inverse
    {a b : M} (f : submm_iso a b)
    : has_submm_inverse f := pr2 f.
  Definition submm_iso_plain_mor
    {a b : M} (f : submm_iso a b)
    : a --> b := f.

  Definition make_submm_iso {a b : M}
    (f : a --> b) (H : is_submm_iso f)
    : submm_iso a b
    := f,, H.

  Definition make_submm_iso' {a b : M}
    (f : a -->{P} b) (g : b -->{P} a)
    (Hfg : is_inverse_in_precat f g)
    : submm_iso a b.
  Proof.
    apply (make_submm_iso f).
    apply make_is_submm_iso.
    - exact (submm_mor_property P f).
    - use make_has_submm_inverse.
      + exact g.
      + exact Hfg.
  Defined.

  Definition weq_submm_iso_z_iso (a b : M)
    : submm_iso a b
        ≃ z_iso (C:=wide_submagmoid_carrier_data M P) a b.
  Proof.
    intermediate_weq (∑ (f : a -->{P} b), has_submm_inverse f).
    { apply totalAssociativity. }
    apply weqfibtototal; intro f.
    apply weq_has_submm_inverse_is_z_isomorphism.
  Defined.

  Lemma weq_is_submm_iso_is_z_isomorphism
    {a b : M} (f : a -->{P} b)
    : is_submm_iso f
        ≃ is_z_isomorphism (C:=wide_submagmoid_carrier_data M P) f.
  Proof.
    intermediate_weq (has_submm_inverse f). {
      apply invweq, dirprod_with_contr_l.
      apply iscontraprop1.
      - apply propproperty.
      - exact (submm_mor_property P f).
    }
    exact (weq_has_submm_inverse_is_z_isomorphism f).
  Defined.

  Lemma isaprop_is_submm_iso_from_assoc
    (H : is_assoc_wide_submagmoid P)
    {a b : M} (f : a --> b)
    : isaprop (is_submm_iso f).
  Proof.
    apply isaprop_assume_it_is; intro Hf.
    pose (f' := make_submm_iso f Hf).
    apply (isofhlevelweqb 1 (weq_is_submm_iso_is_z_isomorphism f')).
    apply (isaprop_is_z_isomorphism
             (C:=wide_subcategory_carrier M (P,, H))).
  Qed.

  Lemma isincl_submm_iso_mor
    (H : is_assoc_wide_submagmoid P)
    (a b : M)
    : isincl (@submm_iso_mor a b).
  Proof.
    apply (isinclgwtog (invweq (weq_submm_iso_z_iso a b))
             submm_iso_mor).
    apply isinclpr1; intro f.
    apply (isaprop_is_z_isomorphism
             (C:=wide_subcategory_carrier M (P,, H))).
  Qed.

  Lemma isincl_submm_iso_plain_mor (a b : M)
    (H : ∏ (f : a --> b), isaprop (is_submm_iso f))
    : isincl (@submm_iso_plain_mor a b).
  Proof.
    apply isinclpr1; intro f.
    apply H.
  Defined.

  Lemma isaset_submm_iso (a b : M)
    : isaset (submm_iso a b).
  Proof.
    apply isaset_total2.
    - apply unital_magmoid_has_homsets.
    - intro f.
      apply isaset_is_submm_iso.
  Qed.

  Lemma submm_iso_eq {a b : M}
    (f g : submm_iso a b)
    (H₁ : submm_mor_mor f = g)
    (H₂ : submm_mor_mor (submm_inv_mor f) = submm_inv_mor g)
    : f = g.
  Proof.
    induction f as [f finv].
    induction g as [g ginv].
    cbn in H₁.
    induction H₁.
    apply pair_path_in2.
    apply is_submm_iso_eq, H₂.
  Qed.

  Lemma submm_iso_eq_mor {a b : M}
    (f g : submm_iso a b)
    (H : f = g)
    : submm_mor_mor f = g.
  Proof. exact (maponpaths _ H). Defined.

  Lemma submm_iso_eq_inverse_mor {a b : M}
    (f g : submm_iso a b)
    (H : f = g)
    : submm_mor_mor (submm_inv_mor f) = submm_inv_mor g.
  Proof.
    exact (maponpaths (λ (f : submm_iso a b),
               submm_mor_mor (submm_inv_mor f)) H).
  Defined.

  Definition submm_iso_inv {a b : M}
    (f : submm_iso a b)
    : submm_iso b a.
  Proof.
    use make_submm_iso'.
    - exact (submm_inv_mor f).
    - exact f.
    - apply is_inverse_in_precat_inv.
      exact f.
  Defined.

  Lemma submm_iso_inv_involution {a b : M}
    (f : submm_iso a b)
    : submm_iso_inv (submm_iso_inv f) = f.
  Proof. reflexivity. Defined.

  Lemma isweq_submm_iso_inv (a b : M)
    : isweq (@submm_iso_inv a b).
  Proof.
    use isweq_iso.
    - exact submm_iso_inv.
    - easy.
    - easy.
  Defined.

  Definition weq_submm_iso_inv (a b : M)
    : submm_iso a b ≃ submm_iso b a
    := make_weq _ (isweq_submm_iso_inv a b).

  Lemma has_submm_inverse_identity (a : M)
    : has_submm_inverse (identity a).
  Proof.
    use make_has_submm_inverse.
    - exact (submm_identity P a).
    - apply is_inverse_in_precat_identity_of_magmoid.
  Defined.

  Lemma is_submm_iso_compose {a b c : M}
    (f : a --> b) (g : b --> c)
    (H : is_assoc_wide_submagmoid P)
    (Hf : is_submm_iso f) (Hg : is_submm_iso g)
    : is_submm_iso (f · g).
  Proof.
    pose (f' := make_submm_mor P _ (is_submm_iso_property Hf)).
    pose (g' := make_submm_mor P _ (is_submm_iso_property Hg)).
    apply (invmap (weq_is_submm_iso_is_z_isomorphism (f' ·{P} g'))).
    eapply (is_z_isomorphism_comp (C:=wide_subcategory_carrier M (P,, H))).
    - exact (weq_is_submm_iso_is_z_isomorphism f' Hf).
    - exact (weq_is_submm_iso_is_z_isomorphism g' Hg).
  Defined.

  Lemma is_submm_iso_identity (a : M)
    : is_submm_iso (identity a).
  Proof.
    split.
    - apply wide_submagmoid_identity_holds.
    - apply has_submm_inverse_identity.
  Defined.

  Definition submm_iso_identity (a : M)
    : submm_iso a a.
  Proof.
    use make_submm_iso.
    - exact (submm_identity P a).
    - exact (is_submm_iso_identity a).
  Defined.

  Definition submm_iso_compose {a b c : M}
    (f : submm_iso a b) (g : submm_iso b c)
    (H : is_assoc_wide_submagmoid P)
    : submm_iso a c.
  Proof.
    apply (invmap (weq_submm_iso_z_iso a c)).
    eapply (z_iso_comp (C:=wide_subcategory_carrier M (P,, H))).
    - exact (weq_submm_iso_z_iso a b f).
    - exact (weq_submm_iso_z_iso b c g).
  Defined.

  Definition id_to_submm_iso {a b : M} (p : a = b)
    : submm_iso a b.
  Proof.
    induction p; apply submm_iso_identity.
  Defined.

End wide_submagmoid_inverses.

Section wide_subcat_inverses.
  Context {M : unital_magmoid} (P : wide_subcategory M).

  Definition is_subcat_iso {a b : M} (f : a --> b) : UU := is_submm_iso P f.
  Identity Coercion Id_is_subcat_iso : is_subcat_iso >-> is_submm_iso.

  Definition subcat_iso (a b : M) : UU := submm_iso P a b.
  Identity Coercion Id_subcat_iso : subcat_iso >-> submm_iso.
  Coercion subcat_iso_is_subcat_iso {a b : M}
    (f : subcat_iso a b) : is_subcat_iso f := pr2 f.

  Lemma isaprop_is_subcat_iso {a b : M} (f : a --> b)
    : isaprop (is_subcat_iso f).
  Proof.
    apply isaprop_is_submm_iso_from_assoc.
    apply wide_subcategory_is_assoc.
  Qed.

  Lemma subcat_iso_eq {a b : M}
    (f g : subcat_iso a b)
    : (submm_iso_plain_mor P f = submm_iso_plain_mor P g)
        ≃ f = g.
  Proof.
    apply invweq, (weqonpathsincl (submm_iso_plain_mor P)).
    apply isincl_submm_iso_plain_mor, isaprop_is_subcat_iso.
  Defined.

  Lemma subcat_iso_eq_inv {a b : M}
    (f g : subcat_iso a b)
    : (submm_mor_mor (submm_inv_mor P f) = submm_inv_mor P g)
        ≃ f = g.
  Proof.
    intermediate_weq (submm_iso_inv P f = submm_iso_inv P g).
    - exact (subcat_iso_eq
               (submm_iso_inv P f)
               (submm_iso_inv P g)).
    - apply invweq, weqonpathsincl.
      apply isinclweq, isweq_submm_iso_inv.
  Defined.

  Lemma is_subcat_iso_compose {a b c : M}
    (f : a --> b) (g : b --> c)
    (Hf : is_submm_iso P f) (Hg : is_submm_iso P g)
    : is_submm_iso P (f · g).
  Proof.
    refine (is_submm_iso_compose P f g _ Hf Hg).
    apply wide_subcategory_is_assoc.
  Defined.

  Definition subcat_iso_compose {a b c : M}
    (f : subcat_iso a b) (g : subcat_iso b c)
    : subcat_iso a c.
  Proof.
    apply (submm_iso_compose P f g).
    apply wide_subcategory_is_assoc.
  Defined.

  Definition ish_subcat_iso {a b : M} : hsubtype (a --> b)
    := λ f, make_hProp (is_subcat_iso f) (isaprop_is_subcat_iso f).
  Definition isw_subcat_iso : wide_submagmoid M
    := make_wide_submagmoid' (@ish_subcat_iso)
         (is_submm_iso_identity P) (@is_subcat_iso_compose).
  Definition isc_subcat_iso : wide_subcategory M.
  Proof.
    apply (make_wide_subcategory isw_subcat_iso).
    intros a b c d f g h Hf Hg Hh.
    apply (wide_subcategory_is_assoc P).
    - exact (is_submm_iso_property P Hf).
    - exact (is_submm_iso_property P Hg).
    - exact (is_submm_iso_property P Hh).
  Defined.

End wide_subcat_inverses.

Section inclusions.
  Context (M : unital_magmoid).
  Local Notation "a ≅{ P } b" :=
    (submm_iso P a b)
      (at level 60, no associativity, format "a  ≅{ P }  b").

  Definition submm_includes_at_sym
    (P Q : wide_submagmoid M) (a b : M)
    : UU
    := submm_includes_at P Q a b ×
         submm_includes_at P Q b a.

  Definition submm_includes_to_at_sym
    (P Q : wide_submagmoid M)
    (H : submm_includes P Q)
    (a b : M)
    : submm_includes_at_sym P Q a b.
  Proof. split; apply H. Qed.

  Definition submm_includes_in_to_at_sym
    (R : hsubtype M)
    (P Q : wide_submagmoid M)
    (H : submm_includes_in R P Q)
    (a b : sub_ob R)
    : submm_includes_at_sym P Q a b.
  Proof. split; apply H. Qed.

  Definition has_submm_inverse_incl
    (P Q : wide_submagmoid M)
    {a b : M} (H : submm_includes_at P Q b a)
    (f : a --> b)
    (I : has_submm_inverse P f)
    : has_submm_inverse Q f.
  Proof.
    use make_has_submm_inverse.
    - apply (submm_mor_incl P).
      + apply H.
      + exact (submm_inv_mor P I).
    - exact I.
  Defined.

  Lemma weq_hfiber_bandfmap {X Y : UU}
    (f : X -> Y)
    (P : X -> UU) (Q : Y -> UU)
    (fm : ∏ x, P x -> Q (f x))
    (x : Y) (y : Q x)
    : hfiber (bandfmap f P Q fm) (x,, y)
        ≃ ∑ (h : hfiber f x),
      hfiber (fm (pr1 h))
        (transportb Q (pr2 h) y).
  Proof.
    intermediate_weq (∑ (wz : ∑ x, P x),
                       f (pr1 wz),, fm (pr1 wz) (pr2 wz)
                         ╝ x,, y).
    { apply weqfibtototal; intro.
      apply total2_paths_equiv. }
    use weq_iso.
    - intros [[w z] [Hw Hz]]; cbn in Hw, Hz.
      induction Hw; cbn in Hz.
      exists (make_hfiber f w (idpath (f w))).
      exact (make_hfiber (fm w) z Hz).
    - intros [[w Hw] [z Hz]]; cbn in Hw, Hz.
      induction Hw; cbn in z, Hz.
      exists (w,, z); cbn.
      exists (idpath (f w)).
      exact Hz.
    - intros [[w z] [Hw Hz]]; cbn in Hw, Hz.
      now induction Hw.
    - intros [[w Hw] [z Hz]]; cbn in Hw, Hz.
      now induction Hw.
  Defined.

  Lemma isofhlevelf_bandfmap (n : nat) {X Y : UU}
    (f : X -> Y)
    (P : X -> UU) (Q : Y -> UU)
    (fm : ∏ x, P x -> Q (f x))
    (Hf : isofhlevelf n f)
    (Hfm : ∏ x, isofhlevelf n (fm x))
    : isofhlevelf n (bandfmap f P Q fm).
  Proof.
    intros [x y].
    unfold hfiber, bandfmap; cbn.
    apply (isofhlevelweqb n (weq_hfiber_bandfmap f P Q fm x y)).
    apply isofhleveltotal2.
    - exact (Hf x).
    - intros [w Hw]; cbn.
      induction Hw; cbn.
      exact (Hfm w y).
  Defined.

  Lemma isincl_has_submm_inverse_incl
    (P Q : wide_submagmoid M)
    {a b : M} (H : submm_includes_at P Q b a)
    (f : a --> b)
    : isincl (has_submm_inverse_incl P Q H f).
  Proof.
    use isofhlevelfhomot.
    - use bandfmap.
      + apply (submm_mor_incl P), H.
      + easy.
    - easy.
    - apply isofhlevelf_bandfmap.
      + apply isincl_submm_mor_incl.
      + intros g.
        apply isinclweq, idisweq.
  Qed.

  Definition is_submm_iso_incl
    (P Q : wide_submagmoid M)
    {a b : M}
    (H : submm_includes_at_sym P Q a b)
    (f : a --> b)
    (I : is_submm_iso P f)
    : is_submm_iso Q f.
  Proof.
    use make_is_submm_iso.
    - apply H.
      apply is_submm_iso_property, I.
    - apply (has_submm_inverse_incl P).
      + apply H.
      + exact I.
  Defined.

  Theorem isincl_is_submm_iso_incl (P Q : wide_submagmoid M)
    {a b : M} (H : submm_includes_at_sym P Q a b)
    (f : a --> b)
    : isincl (is_submm_iso_incl P Q H f).
  Proof.
    use isofhlevelfhomot.
    - use bandfmap.
      + apply (pr1 H).
      + intro Hf.
        apply (has_submm_inverse_incl P), (pr2 H).
    - easy.
    - apply isofhlevelf_bandfmap.
      + apply isofhlevelffromXY.
        * apply propproperty.
        * apply isasetaprop, propproperty.
      + intro Hf.
        apply isincl_has_submm_inverse_incl.
  Qed.

  Definition submm_iso_incl
    (P Q : wide_submagmoid M)
    {a b : M}
    (H : submm_includes_at_sym P Q a b)
    : a ≅{P} b -> a ≅{Q} b.
  Proof.
    apply totalfun; intro f.
    apply is_submm_iso_incl, H.
  Defined.

  Theorem isincl_submm_iso_incl (P Q : wide_submagmoid M)
    {a b : M} (H : submm_includes_at_sym P Q a b)
    : isincl (submm_iso_incl P Q H).
  Proof.
    apply isofhlevelf_totalfun.
    apply isincl_is_submm_iso_incl.
  Qed.

  Lemma issurjective_submm_iso_incl (P Q : wide_submagmoid M)
    {a b : M}
    (H : submm_includes_at_sym P Q a b)
    (Hinv : submm_includes_at_sym Q P a b)
    : issurjective (submm_iso_incl P Q H).
  Proof.
    intros f; apply hinhpr.
    use make_hfiber.
    - exact (submm_iso_incl _ _ Hinv f).
    - now apply submm_iso_eq.
  Qed.

  Theorem isweq_submm_iso_incl (P Q : wide_submagmoid M)
    {a b : M}
    (H : submm_includes_at_sym P Q a b)
    (Hinv : submm_includes_at_sym Q P a b)
    : isweq (submm_iso_incl P Q H).
  Proof.
    apply isweqinclandsurj.
    - apply isincl_submm_iso_incl.
    - apply issurjective_submm_iso_incl, Hinv.
  Defined.

  Definition weq_submm_iso_incl (P Q : wide_submagmoid M)
    {a b : M}
    (H : submm_includes_at_sym P Q a b)
    (Hinv : submm_includes_at_sym Q P a b)
    : (a ≅{P} b) ≃ (a ≅{Q} b)
    := make_weq _ (isweq_submm_iso_incl P Q H Hinv).

End inclusions.

Lemma weq_has_trivial_submm_inverse_is_z_isomorphism
  {M : unital_magmoid} {a b : M} (f : a --> b)
  : has_submm_inverse trivial_submm f
      ≃ is_z_isomorphism f.
Proof.
  use weqbandf.
  { apply invweq, weq_make_submm_mor; easy. }
  intro g.
  exact (idweq _).
Defined.

(** ** Rewriting lemmas of isomorphisms *)

Section rewrites.
  Context {M : unital_magmoid}
    (P : wide_submagmoid M).
  Local Notation "a ≅{ P } b" :=
    (submm_iso P a b)
      (at level 60, no associativity, format "a  ≅{ P }  b").

  Definition magmoid_remove_id_left {a b : M}
    (f : a --> a) (g : a --> b)
    (H : f = identity a)
    : f · g = g.
  Proof.
    refine (_ @ magmoid_id_left g).
    apply cancel_postcomposition, H.
  Defined.

  Definition magmoid_remove_id_right {a b : M}
    (f : a <-- a) (g : a <-- b)
    (H : f = identity a)
    : f ∘ g = g.
  Proof.
    refine (_ @ magmoid_id_right g).
    apply cancel_precomposition, H.
  Defined.

  Lemma submm_iso_left_of_thunkable {a b : M}
    (p : a ≅{P} b)
    (H : is_thunkable p)
    {c : M} (f : a --> c)
    : p · (submm_inv_mor P p · f) = f.
  Proof.
    refine (assoc_thunkable _ H _ _ @ _).
    apply magmoid_remove_id_left.
    exact (is_inverse_in_precat1 p).
  Qed.

  Lemma submm_iso_right_of_linear {a b : M}
    (p : b ≅{P} a)
    (H : is_linear p)
    {c : M} (f : a <-- c)
    : p ∘ (submm_inv_mor P p ∘ f) = f.
  Proof.
    refine (assoc'_linear _ H _ _ @ _).
    apply magmoid_remove_id_right.
    exact (is_inverse_in_precat2 p).
  Qed.

  Lemma submm_iso_left_of_intermediate {a b : M}
    (p : b ≅{P} a)
    (H : is_intermediate p)
    {c : M} (f : a --> c)
    : submm_inv_mor P p · (p · f) = f.
  Proof.
    refine (assoc_intermediate _ H _ _ @ _).
    apply magmoid_remove_id_left.
    exact (is_inverse_in_precat2 p).
  Qed.

  Lemma submm_iso_right_of_intermediate {a b : M}
    (p : a ≅{P} b)
    (H : is_intermediate p)
    {c : M} (f : a <-- c)
    : submm_inv_mor P p ∘ (p ∘ f) = f.
  Proof.
    refine (assoc'_intermediate _ H _ _ @ _).
    apply magmoid_remove_id_right.
    exact (is_inverse_in_precat1 p).
  Qed.

  Lemma submm_iso_left_of_inv_thunkable {a b : M}
    (p : b ≅{P} a)
    (H : is_thunkable (submm_inv_mor P p))
    {c : M} (f : a --> c)
    : submm_inv_mor P p · (p · f) = f.
  Proof.
    exact (submm_iso_left_of_thunkable
             (submm_iso_inv P p) H f).
  Qed.

  Lemma submm_iso_right_of_inv_linear {a b : M}
    (p : a ≅{P} b)
    (H : is_linear (submm_inv_mor P p))
    {c : M} (f : a <-- c)
    : submm_inv_mor P p ∘ (p ∘ f) = f.
  Proof.
    exact (submm_iso_right_of_linear
             (submm_iso_inv P p) H f).
  Qed.

  Lemma submm_iso_interpose_of_intermediate {a b : M}
    (p : a ≅{P} b)
    (Hp : is_intermediate p)
    (Hinv : is_intermediate (submm_inv_mor P p))
    {c d : M}
    (f : c --> a)
    (g : a --> d)
    : (f · p) · (submm_inv_mor P p · g) = f · g.
  Proof.
    refine (assoc'_intermediate _ Hp _ _ @ _).
    apply cancel_precomposition.
    refine (assoc_intermediate _ Hinv _ _ @ _).
    apply magmoid_remove_id_left.
    exact (is_inverse_in_precat1 p).
  Qed.

  Lemma submm_iso_interpose_inv_of_intermediate {a b : M}
    (p : b ≅{P} a)
    (Hp : is_intermediate p)
    (Hinv : is_intermediate (submm_inv_mor P p))
    {c d : M}
    (f : c --> a)
    (g : a --> d)
    : (f · submm_inv_mor P p) · (p · g) = f · g.
  Proof.
    exact (submm_iso_interpose_of_intermediate
             (submm_iso_inv P p) Hinv Hp f g).
  Qed.

  Lemma cancel_submm_iso_left_of_associates {a b : M}
    (p : a ≅{P} b)
    {c : M}
    (f g : b --> c)
    (Ha₁ : submm_inv_mor _ p · (p · f) = (submm_inv_mor _ p · p) · f)
    (Ha₂ : submm_inv_mor _ p · (p · g) = (submm_inv_mor _ p · p) · g)
    : p · f = p · g ≃ f = g.
  Proof.
    use weqimplimpl.
    - intros Heq.
      refine (!magmoid_id_left f @ _ @ magmoid_id_left g).
      rewrite <- (is_inverse_in_precat2 p).
      refine (!Ha₁ @ _ @ Ha₂).
      apply cancel_precomposition, Heq.
    - exact (maponpaths (λ x, p · x)).
    - apply unital_magmoid_has_homsets.
    - apply unital_magmoid_has_homsets.
  Qed.

  Lemma cancel_submm_iso_right_of_associates {a b : M}
    (p : b ≅{P} a)
    {c : M}
    (f g : b <-- c)
    (Ha₁ : submm_inv_mor _ p ∘ (p ∘ f) = (submm_inv_mor _ p ∘ p) ∘ f)
    (Ha₂ : submm_inv_mor _ p ∘ (p ∘ g) = (submm_inv_mor _ p ∘ p) ∘ g)
    : p ∘ f = p ∘ g ≃ f = g.
  Proof.
    use weqimplimpl.
    - intros Heq.
      refine (!magmoid_id_right f @ _ @ magmoid_id_right g).
      rewrite <- (is_inverse_in_precat1 p).
      refine (!Ha₁ @ _ @ Ha₂).
      apply cancel_postcomposition, Heq.
    - exact (maponpaths (λ x, p ∘ x)).
    - apply unital_magmoid_has_homsets.
    - apply unital_magmoid_has_homsets.
  Qed.

  Lemma submm_iso_eq_from_identity_and_remove_right {a b : M}
    (p q : a ≅{P} b)
    (Hremove : (p · submm_inv_mor P q) · q = p)
    (H : p · submm_inv_mor _ q = identity a)
    : submm_mor_mor p = q.
  Proof.
    rewrite <- (is_inverse_in_precat1 q) in H.
    apply (cancel_submm_iso_right_of_associates (submm_iso_inv P q)) in H.
    - exact H.
    - etrans; [|apply pathsinv0, magmoid_remove_id_right,
                (is_inverse_in_precat2 q)].
      exact Hremove.
    - etrans.
      + apply magmoid_remove_id_left.
        apply (is_inverse_in_precat1 q).
      + apply pathsinv0, magmoid_remove_id_right.
        apply (is_inverse_in_precat2 q).
  Qed.

End rewrites.

Lemma subcat_iso_eq_from_identity
  {M : unital_magmoid}
  (P : wide_subcategory M)
  {a b : M}
  (p q : submm_iso P a b)
  (H : p · submm_inv_mor _ q = identity a)
  : submm_mor_mor p = q.
Proof.
  apply submm_iso_eq_from_identity_and_remove_right.
  - rewrite <- (wide_subcategory_is_assoc P). {
      apply magmoid_remove_id_right.
      exact (is_inverse_in_precat2 q).
    }
    all: apply (submm_mor_property P).
  - exact H.
Qed.
