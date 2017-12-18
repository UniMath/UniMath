(** * Direct definition of cokernels *)
(** ** Contents
- Definition of cokernel
- Correspondence of cokernels and coequalizers
- Cokernel up to iso
- Cokernel of [Epi] · morphism
- CokernelOut of equal morphisms
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.zero.

Local Open Scope cat.

(** * Definition of cokernels *)
Section def_cokernels.

  Context {C : precategory}.
  Hypothesis hs : has_homsets C.
  Hypothesis Z : Zero C.

  (** Definition and construction of Cokernels *)
  Definition isCokernel {x y z : C} (f : x --> y) (g : y --> z) (H : f · g = (ZeroArrow Z x z)) : UU :=
    ∏ (w : C) (h : y --> w) (H : f · h = ZeroArrow Z x w), ∃! φ : z --> w, g · φ = h.

  Lemma isCokernel_paths  {x y z : C} (f : x --> y) (g : y --> z) (H H' : f · g = (ZeroArrow Z x z))
        (isC : isCokernel f g H) : isCokernel f g H'.
  Proof.
    assert (e : H = H') by apply hs.
    induction e. exact isC.
  Qed.

  Local Lemma mk_isCokernel_uniqueness {x y z : C} (f : x --> y) (g : y --> z)
        (H1 : f · g = ZeroArrow Z x z)
        (H2 : ∏ (w : C) (h : C ⟦ y, w ⟧),
              f · h = ZeroArrow Z x w → ∃! ψ : C ⟦ z, w ⟧, g · ψ = h)
        (w : C) (h : y --> w) (H' : f · h = ZeroArrow Z x w) :
    ∏ y0 : C ⟦ z, w ⟧, g · y0 = h → y0 = pr1 (iscontrpr1 (H2 w h H')).
  Proof.
    intros y0 H. apply (base_paths _ _ ((pr2 (H2 w h H')) (tpair _ y0 H))).
  Qed.

  Definition mk_isCokernel {x y z : C} (f : x --> y) (g : y --> z) (H1 : f · g = ZeroArrow Z x z)
             (H2 : ∏ (w : C) (h : y --> w) (H' : f · h = ZeroArrow Z x w),
                   ∃! ψ : z --> w, g · ψ = h) : isCokernel f g H1.
  Proof.
    unfold isCokernel.
    intros w h H'.
    use unique_exists.
    - exact (pr1 (iscontrpr1 (H2 w h H'))).
    - exact (pr2 (iscontrpr1 (H2 w h H'))).
    - intros y0. apply hs.
    - intros y0 X. exact (base_paths _ _ ((pr2 (H2 w h H')) (tpair _ y0 X))).
  Defined.

  Definition Cokernel {x y : C} (f : x --> y) : UU :=
    ∑ D : (∑ z : ob C, y --> z),
          ∑ (e : f · (pr2 D) = ZeroArrow Z x (pr1 D)), isCokernel f (pr2 D) e.

  Definition mk_Cokernel {x y z : C} (f : x --> y) (g : y --> z) (H : f · g = (ZeroArrow Z x z))
             (isCK : isCokernel f g H) : Cokernel f := ((z,,g),,(H,,isCK)).

  Definition Cokernels : UU := ∏ (x y : C) (f : x --> y), Cokernel f.

  Definition hasCokernels : UU := ∏ (x y : C) (f : x --> y), ishinh (Cokernel f).

  Definition CokernelOb {x y : C} {f : x --> y} (CK : Cokernel f) : ob C := pr1 (pr1 CK).
  Coercion CokernelOb : Cokernel >-> ob.

  Definition CokernelArrow {x y : C} {f : x --> y} (CK : Cokernel f) : C⟦y, CK⟧ := pr2 (pr1 CK).

  Definition CokernelCompZero {x y : C} {f : x --> y} (CK : Cokernel f) :
    f · (CokernelArrow CK) = (ZeroArrow Z x CK) := pr1 (pr2 CK).

  Definition CokernelisCokernel {y z : C} {g : y --> z} (CK : Cokernel g) := pr2 (pr2 CK).

  Definition CokernelOut {y z : C} {g : y --> z} (CK : Cokernel g) (w : C) (h : z --> w)
             (H : g · h = ZeroArrow Z y w) : C⟦CK, w⟧ :=
    pr1 (iscontrpr1 (CokernelisCokernel CK w h H)).

  Definition CokernelCommutes {y z : C} {g : y --> z} (CK : Cokernel g) (w : C) (h : z --> w)
        (H : g · h = ZeroArrow Z y w) : (CokernelArrow CK) · (CokernelOut CK w h H) = h
    := pr2 (iscontrpr1 (CokernelisCokernel CK w h H)).

  Local Lemma CokernelOutUnique {x y z : C} {f : x --> y} {g : y --> z} {H : f · g = ZeroArrow Z x z}
        (isCK : isCokernel f g H) {w : C} {h : y --> w} (H' : f · h = ZeroArrow Z x w) {φ : z --> w}
        (H'' : g · φ = h) :
    φ = (pr1 (pr1 (isCK w h H'))).
  Proof.
    exact (base_paths _ _ (pr2 (isCK w h H') (tpair _ φ H''))).
  Qed.

  Lemma CokernelOutsEq {x y : C} {f : x --> y} (CK : Cokernel f) {w : C} (φ1 φ2 : C⟦CK, w⟧)
        (H' : (CokernelArrow CK) · φ1 = (CokernelArrow CK) · φ2) : φ1 = φ2.
  Proof.
    assert (H1 : f · ((CokernelArrow CK) · φ1) = ZeroArrow Z _ _).
    {
      rewrite assoc. rewrite CokernelCompZero. apply ZeroArrow_comp_left.
    }
    rewrite (CokernelOutUnique (CokernelisCokernel CK) H1 (idpath _)).
    apply pathsinv0.
    set (tmp := pr2 (CokernelisCokernel CK w (CokernelArrow CK · φ1) H1) (tpair _ φ2 (! H'))).
    exact (base_paths _ _ tmp).
  Qed.

  Lemma CokernelOutComp {y z : C} {f : y --> z} (K : Cokernel f) {w w' : C} (h1 : z --> w)
        (h2 : w --> w') (H1 : f · (h1 · h2) = ZeroArrow Z _ _) (H2 : f · h1 = ZeroArrow Z _ _) :
    CokernelOut K w' (h1 · h2) H1 = CokernelOut K w h1 H2 · h2.
  Proof.
    use CokernelOutsEq. rewrite CokernelCommutes. rewrite assoc. rewrite CokernelCommutes.
    apply idpath.
  Qed.

  (** Results on morphisms between Cokernels. *)
  Definition identity_is_CokernelOut {x y : C} {f : x --> y} (CK : Cokernel f) :
    ∑ φ : C⟦CK, CK⟧, (CokernelArrow CK) · φ = (CokernelArrow CK).
  Proof.
    exists (identity CK).
    apply id_right.
  Defined.

  Lemma CokernelEndo_is_identity {x y : C} {f : x --> y} {CK : Cokernel f} (φ : C⟦CK, CK⟧)
        (H : (CokernelArrow CK) · φ = CokernelArrow CK) : identity CK = φ.
  Proof.
    set (H1 := tpair ((fun φ' : C⟦CK, CK⟧ => _ · φ' = _)) φ H).
    assert (H2 : identity_is_CokernelOut CK = H1).
    - apply proofirrelevance.
      apply isapropifcontr.
      apply (CokernelisCokernel CK).
      apply CokernelCompZero.
    - apply (base_paths _ _ H2).
  Qed.

  Definition from_Cokernel_to_Cokernel {x y : C} {f : x --> y} (CK CK': Cokernel f) : C⟦CK, CK'⟧.
  Proof.
    use (CokernelOut CK CK' (CokernelArrow CK')).
    use CokernelCompZero.
  Defined.

  Lemma are_inverses_from_Cokernel_to_Cokernel {y z : C} {g : y --> z} (CK CK': Cokernel g) :
    is_inverse_in_precat (from_Cokernel_to_Cokernel CK CK')
                         (from_Cokernel_to_Cokernel CK' CK).
  Proof.
    split.
    - unfold from_Cokernel_to_Cokernel. apply pathsinv0. use CokernelEndo_is_identity.
      rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes. apply idpath.
    - unfold from_Cokernel_to_Cokernel. apply pathsinv0. use CokernelEndo_is_identity.
      rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes. apply idpath.
  Qed.

  Definition iso_from_Cokernel_to_Cokernel {y z : C} {g : y --> z} (CK CK' : Cokernel g) :
    z_iso CK CK' := mk_z_iso (from_Cokernel_to_Cokernel CK CK') (from_Cokernel_to_Cokernel CK' CK)
                             (are_inverses_from_Cokernel_to_Cokernel CK CK').

  (** Cokernel of the ZeroArrow is given by the identity. *)
  Lemma CokernelOfZeroArrow_isCokernel (x y : C) :
    isCokernel (ZeroArrow Z x y) (identity y) (id_right (ZeroArrow Z x y)).
  Proof.
    use mk_isCokernel.
    intros w h H'.
    use unique_exists.
    - exact h.
    - exact (id_left _).
    - intros y0. apply hs.
    - intros y0 t. cbn in t. rewrite id_left in t. exact t.
  Qed.

  Definition CokernelofZeroArrow (x y : C) : Cokernel (ZeroArrow Z x y) :=
    mk_Cokernel (ZeroArrow Z x y) (identity y) (id_right _) (CokernelOfZeroArrow_isCokernel x y).

  (** Cokernel of identity is given by arrow to zero *)
  Local Lemma CokernelOfIdentity_isCokernel (x : C) :
    isCokernel (identity x) (ZeroArrowTo x)
               (ArrowsToZero C Z x (identity x · ZeroArrowTo x) (ZeroArrow Z x Z)).
  Proof.
    use mk_isCokernel.
    intros w h H'.
    use unique_exists.
    - exact (ZeroArrowFrom w).
    - cbn. rewrite id_left in H'. rewrite H'. apply idpath.
    - intros y. apply hs.
    - intros y X. cbn in X. use ArrowsFromZero.
  Qed.

  Definition CokernelOfIdentity (x : C) : Cokernel (identity x).
  Proof.
    use mk_Cokernel.
    - exact Z.
    - exact (ZeroArrowTo x).
    - use ArrowsToZero.
    - exact (CokernelOfIdentity_isCokernel x).
  Defined.

  (** More generally, the CokernelArrow of the cokernel of the ZeroArrow is an
    isomorphism. *)
  Lemma CokernelofZeroArrow_is_iso {x y : C} (CK : Cokernel (ZeroArrow Z x y)) :
    is_inverse_in_precat (CokernelArrow CK)
                         (from_Cokernel_to_Cokernel CK (CokernelofZeroArrow x y)).
  Proof.
    use mk_is_inverse_in_precat.
    - unfold from_Cokernel_to_Cokernel. rewrite CokernelCommutes. apply idpath.
    - unfold from_Cokernel_to_Cokernel. cbn.
      use CokernelOutsEq. rewrite assoc. rewrite CokernelCommutes.
      rewrite id_left. rewrite id_right. apply idpath.
  Qed.

  Definition CokernelofZeroArrow_iso (x y : C) (CK : Cokernel (ZeroArrow Z x y)) : z_iso y CK :=
    mk_z_iso (CokernelArrow CK) (from_Cokernel_to_Cokernel CK (CokernelofZeroArrow x y))
             (CokernelofZeroArrow_is_iso CK).

  (** It follows that CokernelArrow is an epi. *)
  Lemma CokernelArrowisEpi {y z : C} {g : y --> z} (CK : Cokernel g ) : isEpi (CokernelArrow CK).
  Proof.
    unfold isEpi.
    intros z0 g0 h X.
    use CokernelOutsEq.
    exact X.
  Qed.

  Lemma CokernelsOut_is_iso {x y : C} {f : x --> y} (CK1 CK2 : Cokernel f) :
    is_iso (CokernelOut CK1 CK2 (CokernelArrow CK2) (CokernelCompZero CK2)).
  Proof.
    use is_iso_qinv.
    - use CokernelOut.
      + use CokernelArrow.
      + use CokernelCompZero.
    - split.
      + use CokernelOutsEq. rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes.
        rewrite id_right. apply idpath.
      + use CokernelOutsEq. rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes.
        rewrite id_right. apply idpath.
  Qed.

End def_cokernels.
Arguments CokernelArrow [C] [Z] [x] [y] [f] _.


(** * Correspondence of cokernels and coequalizers *)
Section cokernels_coequalizers.

  Context {C : precategory}.
  Hypothesis hs : has_homsets C.
  Hypothesis Z : Zero C.


  (** ** [Coequalizer] from [Cokernel] *)
  Lemma CokernelCoequalizer_eq {x y : ob C} {f : x --> y} (CK : Cokernel Z f) :
    f · CokernelArrow CK = ZeroArrow Z x y · CokernelArrow CK.
  Proof.
    rewrite ZeroArrow_comp_left. use CokernelCompZero.
  Qed.

  Lemma CokernelCoequalizer_isCokernel {x y : ob C} {f : x --> y} (CK : Cokernel Z f) :
    isCoequalizer f (ZeroArrow Z x y) (CokernelArrow CK) (CokernelCoequalizer_eq CK).
  Proof.
    use mk_isCoequalizer.
    intros w0 h H'.
    use unique_exists.
    - use CokernelOut.
      + exact h.
      + rewrite H'. apply ZeroArrow_comp_left.
    - use CokernelCommutes.
    - intros y0. apply hs.
    - intros y0 X. use CokernelOutsEq. rewrite CokernelCommutes. exact X.
  Qed.

  Definition CokernelCoequalizer {x y : ob C} {f : x --> y} (CK : Cokernel Z f) :
    Coequalizer f (ZeroArrow Z _ _).
  Proof.
    use mk_Coequalizer.
    - exact CK.
    - exact (CokernelArrow CK).
    - exact (CokernelCoequalizer_eq CK).
    - exact (CokernelCoequalizer_isCokernel CK).
  Defined.


  (** ** [Cokernel] from [Coequalizer] *)

  Lemma CoequalizerCokernel_eq {x y : ob C} {f : x --> y} (CE : Coequalizer f (ZeroArrow Z _ _)) :
    f · CoequalizerArrow CE = ZeroArrow Z x CE.
  Proof.
    rewrite <- (ZeroArrow_comp_left _ _ _ _ _ (CoequalizerArrow CE)).
    exact (CoequalizerEqAr CE).
  Qed.

  Lemma CoequalizerCokernel_isCokernel {x y : ob C} {f : x --> y}
        (CE : Coequalizer f (ZeroArrow Z _ _)) :
    isCokernel Z f (CoequalizerArrow CE) (CoequalizerCokernel_eq CE).
  Proof.
    use (mk_isCokernel hs).
    intros w h H'.
    use unique_exists.
    - use CoequalizerOut.
      + exact h.
      + rewrite ZeroArrow_comp_left. exact H'.
    - use CoequalizerCommutes.
    - intros y0. apply hs.
    - intros y0 X. use CoequalizerOutsEq. rewrite CoequalizerCommutes. exact X.
  Qed.

  Definition CoequalizerCokernel {x y : ob C} {f : x --> y} (CE : Coequalizer f (ZeroArrow Z _ _)) :
    Cokernel Z f.
  Proof.
    use mk_Cokernel.
    - exact CE.
    - exact (CoequalizerArrow CE).
    - exact (CoequalizerCokernel_eq CE).
    - exact (CoequalizerCokernel_isCokernel CE).
  Defined.

End cokernels_coequalizers.


(** * Cokernels up to iso*)
Section cokernels_iso.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.


  Lemma Cokernel_up_to_iso_eq {x y z : C} (f : x --> y) (g : y --> z) (CK : Cokernel Z f)
        (h : z_iso CK z) (H : g = (CokernelArrow CK) · h) : f · g = ZeroArrow Z x z.
  Proof.
    induction CK as [t p]. induction t as [t' p']. induction p as [t'' p''].
    unfold isCoequalizer in p''.
    rewrite H.
    rewrite <- (ZeroArrow_comp_left _ _ _ _ _ h).
    rewrite assoc.
    apply cancel_postcomposition.
    apply CokernelCompZero.
  Qed.

  Lemma Cokernel_up_to_iso_isCokernel {x y z : C} (f : x --> y) (g : y --> z) (CK : Cokernel Z f)
        (h : z_iso CK z) (H : g = (CokernelArrow CK) · h) (H'' : f · g = ZeroArrow Z x z) :
    isCokernel Z f g H''.
  Proof.
    use (mk_isCokernel hs).
    intros w h0 H'.
    use unique_exists.
    - exact ((z_iso_inv_mor h) · (CokernelOut Z CK w h0 H')).
    - cbn. rewrite H. rewrite assoc. rewrite <- (assoc _ h).
      rewrite (is_inverse_in_precat1 h).
      rewrite id_right. use CokernelCommutes.
    - intros y0. apply hs.
    - intros y0 X. cbn beta in X.
      use (pre_comp_with_z_iso_is_inj h). rewrite assoc.
      set (tmp := maponpaths (λ gg : _, gg · CokernelOut Z CK w h0 H')
                             (is_inverse_in_precat1 h)). cbn in tmp.
      use (pathscomp0 _ (! tmp)). clear tmp. rewrite id_left.
      use CokernelOutsEq. rewrite CokernelCommutes. rewrite assoc.
      rewrite <- X. apply cancel_postcomposition. rewrite H.
      apply cancel_precomposition. apply idpath.
  Qed.

  Definition Cokernel_up_to_iso {x y z : C} (f : x --> y) (g : y --> z) (CK : Cokernel Z f)
             (h : z_iso CK z) (H : g = (CokernelArrow CK) · h) : Cokernel Z f :=
    mk_Cokernel Z f g (Cokernel_up_to_iso_eq f g CK h H)
                (Cokernel_up_to_iso_isCokernel f g CK h H (Cokernel_up_to_iso_eq f g CK h H)).

  Definition Cokernel_up_to_iso2_eq {x y z : C} (f1 : x --> z) (f2 : y --> z) (h : z_iso y x)
             (H : h · f1 = f2) (CK : Cokernel Z f1) : f2 · CokernelArrow CK = ZeroArrow Z y CK.
  Proof.
    rewrite <- H. rewrite <- assoc. rewrite CokernelCompZero.
    apply ZeroArrow_comp_right.
  Qed.

  Definition Cokernel_up_to_iso2_isCoequalizer {x y z : C} (f1 : x --> z) (f2 : y --> z)
             (h : z_iso y x) (H : h · f1 = f2) (CK : Cokernel Z f1) :
    isCokernel Z f2 (CokernelArrow CK) (Cokernel_up_to_iso2_eq f1 f2 h H CK).
  Proof.
    use (mk_isCokernel hs).
    intros w h0 H'.
    use unique_exists.
    - use CokernelOut.
      + exact h0.
      + rewrite <- H in H'. rewrite <- (ZeroArrow_comp_right _ _ _ _ _ h) in H'.
        rewrite <- assoc in H'. apply (pre_comp_with_z_iso_is_inj h) in H'.
        exact H'.
    - cbn. use CokernelCommutes.
    - intros y0. apply hs.
    - intros y0 X. cbn beta in X. use CokernelOutsEq. rewrite CokernelCommutes.
      exact X.
  Qed.

  Definition Cokernel_up_to_iso2 {x y z : C} (f1 : x --> z) (f2 : y --> z) (h : z_iso y x)
             (H : h · f1 = f2) (CK : Cokernel Z f1) : Cokernel Z f2 :=
    mk_Cokernel Z f2 (CokernelArrow CK) (Cokernel_up_to_iso2_eq f1 f2 h H CK)
                (Cokernel_up_to_iso2_isCoequalizer f1 f2 h H CK).

End cokernels_iso.


(** * Cokernel of epi · morphism *)
(** ** Introduction
   Suppose E : x --> y is an [Epi] and f : y --> z is a morphism. Then cokernel of E · f is
   isomorphic to cokernel of f.
*)
Section cokernels_epis.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.

  Local Lemma CokernelEpiComp_eq1 {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK1 : Cokernel Z (E · f)) (CK2 : Cokernel Z f) :
    E · f · CokernelArrow CK2 = ZeroArrow Z x CK2.
  Proof.
    rewrite <- assoc. rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Definition CokernelEpiComp_mor1 {x y z : C} (E : Epi C x y) (f : y --> z)
             (CK1 : Cokernel Z (E · f)) (CK2 : Cokernel Z f) : C⟦CK1, CK2⟧ :=
    CokernelOut Z CK1 _ (CokernelArrow CK2) (CokernelEpiComp_eq1 E f CK1 CK2).

  Local Lemma CokernelEpiComp_eq2 {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK1 : Cokernel Z (E · f)) (CK2 : Cokernel Z f) :
    f · CokernelArrow CK1 = ZeroArrow Z y CK1.
  Proof.
    use (EpiisEpi C E). rewrite assoc. rewrite ZeroArrow_comp_right. exact (CokernelCompZero Z CK1).
  Qed.

  Definition CokernelEpiComp_mor2 {x y z : C} (E : Epi C x y) (f : y --> z)
             (CK1 : Cokernel Z (E · f)) (CK2 : Cokernel Z f) : C⟦CK2, CK1⟧ :=
    CokernelOut Z CK2 _ (CokernelArrow CK1) (CokernelEpiComp_eq2 E f CK1 CK2).

  Lemma CokernelEpiComp1 {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK1 : Cokernel Z (E · f)) (CK2 : Cokernel Z f) :
    is_iso (CokernelEpiComp_mor1 E f CK1 CK2).
  Proof.
    use is_iso_qinv.
    - exact (CokernelEpiComp_mor2 E f CK1 CK2).
    - split.
      + unfold CokernelEpiComp_mor1. unfold CokernelEpiComp_mor2.
        use CokernelOutsEq.
        rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes.
        apply pathsinv0. apply id_right.
      + unfold CokernelEpiComp_mor1. unfold CokernelEpiComp_mor2.
        use CokernelOutsEq.
        rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes.
        apply pathsinv0. apply id_right.
  Qed.

  Lemma CokernelEpiComp2 {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK1 : Cokernel Z (E · f)) (CK2 : Cokernel Z f) :
    is_iso (CokernelEpiComp_mor2 E f CK1 CK2).
  Proof.
    use is_iso_qinv.
    - exact (CokernelEpiComp_mor1 E f CK1 CK2).
    - split.
      + unfold CokernelEpiComp_mor1. unfold CokernelEpiComp_mor2.
        use CokernelOutsEq.
        rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes.
        apply pathsinv0. apply id_right.
      + unfold CokernelEpiComp_mor1. unfold CokernelEpiComp_mor2.
        use CokernelOutsEq.
        rewrite assoc. rewrite CokernelCommutes. rewrite CokernelCommutes.
        apply pathsinv0. apply id_right.
  Qed.

  Local Lemma CokernelEpiComp_eq {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK : Cokernel Z (E · f)) : f · CokernelArrow CK = ZeroArrow Z y CK.
  Proof.
    use (EpiisEpi C E). rewrite ZeroArrow_comp_right. rewrite assoc.
    use CokernelCompZero.
  Qed.

  Local Lemma CokernelEpiComp_isCoequalizer {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK : Cokernel Z (E · f)) : isCokernel Z f (CokernelArrow CK) (CokernelEpiComp_eq E f CK).
  Proof.
    use mk_isCokernel.
    - exact hs.
    - intros w h H'.
      use unique_exists.
      + use CokernelOut.
        * exact h.
        * rewrite <- (ZeroArrow_comp_right _ _ _ _ _ E). rewrite <- assoc.
          apply cancel_precomposition. exact H'.
      + cbn. rewrite CokernelCommutes. apply idpath.
      + intros y0. apply hs.
      + intros y0 X.
        apply pathsinv0. cbn in X.
        use (EpiisEpi C (mk_Epi _ _ (CokernelArrowisEpi Z CK))). cbn.
        rewrite CokernelCommutes. apply pathsinv0. apply X.
  Qed.

  Definition CokernelEpiComp {x y z : C} (E : Epi C x y) (f : y --> z) (CK : Cokernel Z (E · f)) :
    Cokernel Z f.
  Proof.
    use mk_Cokernel.
    - exact CK.
    - use CokernelArrow.
    - exact (CokernelEpiComp_eq E f CK).
    - exact (CokernelEpiComp_isCoequalizer E f CK).
  Defined.

End cokernels_epis.


(** * CokernelOut of equal, not necessarily definitionally equal, morphisms is iso *)
Section cokernel_out_paths.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.

  Definition CokernelOutPaths_is_iso_mor {x y : C} {f f' : x --> y} (e : f = f')
             (CK1 : Cokernel Z f) (CK2 : Cokernel Z f') : CK1 --> CK2.
  Proof.
    induction e.
    use CokernelOut.
    - use CokernelArrow.
    - use CokernelCompZero.
  Defined.

  Lemma CokernelOutPaths_is_iso {x y : C} {f f' : x --> y} (e : f = f')
        (CK1 : Cokernel Z f) (CK2 : Cokernel Z f') : is_iso (CokernelOutPaths_is_iso_mor e CK1 CK2).
  Proof.
    induction e. apply CokernelsOut_is_iso.
  Qed.

  Local Lemma CokernelPath_eq {x y : C} {f f' : x --> y} (e : f = f') (CK : Cokernel Z f) :
    f' · CokernelArrow CK = ZeroArrow Z x CK.
  Proof.
    induction e. use CokernelCompZero.
  Qed.

  Local Lemma CokernelPath_isCokernel {x y : C} {f f' : x --> y} (e : f = f') (CK : Cokernel Z f) :
    isCokernel Z f' (CokernelArrow CK) (CokernelPath_eq e CK).
  Proof.
    induction e. use CokernelisCokernel.
  Qed.

  (** Constructs a cokernel of f' from a cokernel of f in a natural way *)
  Definition CokernelPath {x y : C} {f f' : x --> y} (e : f = f') (CK : Cokernel Z f) :
    Cokernel Z f'.
  Proof.
    use mk_Cokernel.
    - exact CK.
    - use CokernelArrow.
    - exact (CokernelPath_eq e CK).
    - exact (CokernelPath_isCokernel e CK).
  Defined.

End cokernel_out_paths.
