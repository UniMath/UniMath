(**

Direct implementation of cokernels together with:

- Proof that the cokernel arrow is epi ([CokernelArrowisEpi])

Written by Tomi Pannila.

*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.zero.

(** In this section we define cokernels and show that cokernel arrow is an
  epi. *)
Section def_cokernels.

  Context {C : precategory}.
  Hypothesis Z : Zero C.
  Hypothesis hs : has_homsets C.

  (** This rewrite is used to rewrite an equality f ;; g = ZeroArrow to
     f ;; g = ZeroArrow ;; g. This is because Coequalizers need the latter
     equality. *)
  Lemma CokernelEqRw {x y z : C} {g : x --> y} {f : y --> z} (H : g ;; f = ZeroArrow Z x z) :
    g ;; f = ZeroArrow Z x y ;; f.
  Proof.
    pathvia (ZeroArrow Z x z).
    apply H. apply pathsinv0. apply ZeroArrow_comp_left.
  Defined.

  Lemma CokernelEqRw' {x y z : C} {f : x --> y} {g : y --> z} (H : f ;; g = ZeroArrow Z x y ;; g) :
    f ;; g = ZeroArrow Z x z.
  Proof.
    rewrite ZeroArrow_comp_left in H. exact H.
  Qed.

  (** Definition and construction of Cokernels *)
  Definition isCokernel {x y z : C} (f : y --> z) (g : x --> y) (H : g ;; f = (ZeroArrow Z x z)) : UU :=
    isCoequalizer g (ZeroArrow Z x y) f (CokernelEqRw H).


  Local Lemma mk_isCokernel_uniqueness {x y z : C} (f : x --> y) (g : y --> z)
        (H1 : f ;; g = ZeroArrow Z x z)
        (H2 : Π (w : C) (h : C ⟦ y, w ⟧), f ;; h = ZeroArrow Z x w →
                                          ∃! ψ : C ⟦ z, w ⟧, g ;; ψ = h)
        (w : C) (h : y --> w) (H' : f ;; h = ZeroArrow Z x y ;; h) :
    Π y0 : C ⟦ z, w ⟧, g ;; y0 = h → y0 = pr1 (iscontrpr1 (H2 w h (CokernelEqRw' H'))).
  Proof.
    intros y0 H. apply (base_paths _ _ ((pr2 (H2 w h (CokernelEqRw' H'))) (tpair _ y0 H))).
  Qed.

  Definition mk_isCokernel {x y z : C} (f : x --> y) (g : y --> z) (H1 : f ;; g = ZeroArrow Z x z)
             (H2 : Π (w : C) (h : y --> w) (H' : f ;; h = ZeroArrow Z x w),
                   iscontr (Σ ψ : z --> w, g ;; ψ = h)) : isCokernel g f H1.
  Proof.
    use mk_isCoequalizer.
    intros w h H'.
    use unique_exists.
    - exact (pr1 (iscontrpr1 (H2 w h (CokernelEqRw' H')))).
    - exact (pr2 (iscontrpr1 (H2 w h (CokernelEqRw' H')))).
    - intros y0. apply hs.
    - exact (mk_isCokernel_uniqueness f g H1 H2 w h H').
  Defined.

  Definition Cokernel {y z : C} (g : y --> z) :
    UU := Coequalizer g (ZeroArrow Z y z).

  Definition mk_Cokernel {x y z : C} (f : y --> z) (g : x --> y)
             (H : g ;; f = (ZeroArrow Z x z))
             (isE : isCoequalizer g (ZeroArrow Z x y) f (CokernelEqRw H))
    : Cokernel g.
  Proof.
    use (mk_Coequalizer g (ZeroArrow Z x y) f (CokernelEqRw H)).
    apply isE.
  Defined.

  Definition mk_Cokernel' {x y z : C} (f : x --> y) (g : y --> z) (H : f ;; g = (ZeroArrow Z x z))
             (isE : isCokernel g f H) : Cokernel f :=
    mk_Coequalizer f (ZeroArrow Z x y) g (CokernelEqRw H) isE.

  Definition Cokernels : UU := Π (y z : C) (g : y --> z), Cokernel g.
  Definition hasCokernels : UU := Π (y z : C) (g : y --> z), ishinh (Cokernel g).
  Definition CokernelOb {y z : C} {g : y --> z} (CK : Cokernel g) :
    C := CoequalizerObject CK.
  Coercion CokernelOb : Cokernel >-> ob.
  Definition CokernelArrow {y z : C} {g : y --> z} (CK : Cokernel g) :
    C⟦z, CK⟧ := CoequalizerArrow CK.
  Definition CokernelEqAr {y z : C} {g : y --> z} (CK : Cokernel g) :=
    CoequalizerEqAr CK.
  Definition CokernelOut {y z : C} {g : y --> z} (CK : Cokernel g)
             (w : C) (h : z --> w) (H : g ;; h = ZeroArrow Z y w) :
    C⟦CK, w⟧ := CoequalizerOut CK _ h (CokernelEqRw H).

  (** Commutativity of Cokernels. *)
  Lemma CokernelCommutes {y z : C} {g : y --> z} (CK : Cokernel g)
        (w : C) (h : z --> w) (H : g ;; h = ZeroArrow Z y w) :
    (CokernelArrow CK) ;; (CokernelOut CK w h H) = h.
  Proof.
    apply (CoequalizerCommutes CK).
  Defined.

  Lemma CokernelisCokernel {y z : C} {g : y --> z} (CK : Cokernel g) :
    isCokernel (CokernelArrow CK) g (CokernelEqRw' (CokernelEqAr CK)).
  Proof.
    apply isCoequalizer_Coequalizer.
  Qed.

  (** Two arrows from Cokernel, such that the compositions with CokernelArrow
    are equal, are equal. *)
  Lemma CokernelOutsEq {y z: C} {g : y --> z} (CK : Cokernel g)
        {w : C} (φ1 φ2: C⟦CK, w⟧)
        (H' : (CokernelArrow CK) ;; φ1 = (CokernelArrow CK) ;; φ2) : φ1 = φ2.
  Proof.
    apply (isCoequalizerOutsEq (isCoequalizer_Coequalizer CK) _ _ H').
  Defined.

  Lemma CokernelOutComp {y z : C} {f : y --> z} (K : Cokernel f) {w w' : C}
        (h1 : z --> w) (h2 : w --> w')
        (H1 : f ;; (h1 ;; h2) = ZeroArrow Z _ _) (H2 : f ;; h1 = ZeroArrow Z _ _) :
    CokernelOut K w' (h1 ;; h2) H1 = CokernelOut K w h1 H2 ;; h2.
  Proof.
    apply CoequalizerOutComp.
  Qed.

  (** Results on morphisms between Cokernels. *)
  Definition identity_is_CokernelOut {y z : C} {g : y --> z}
             (CK : Cokernel g) :
    Σ φ : C⟦CK, CK⟧, (CokernelArrow CK) ;; φ = (CokernelArrow CK).
  Proof.
    exists (identity CK).
    apply id_right.
  Defined.

  Lemma CokernelEndo_is_identity {y z : C} {g : y --> z} {CK : Cokernel g}
        (φ : C⟦CK, CK⟧) (H : (CokernelArrow CK) ;; φ = CokernelArrow CK) :
    identity CK = φ.
  Proof.
    set (H1 := tpair ((fun φ' : C⟦CK, CK⟧ => _ ;; φ' = _)) φ H).
    assert (H2 : identity_is_CokernelOut CK = H1).
    - apply proofirrelevance.
      apply isapropifcontr.
      apply (isCoequalizer_Coequalizer CK).
      apply CokernelEqAr.
    - apply (base_paths _ _ H2).
  Defined.

  Definition from_Cokernel_to_Cokernel {y z : C} {g : y --> z}
             (CK CK': Cokernel g) : C⟦CK, CK'⟧.
  Proof.
    apply (CokernelOut CK CK' (CokernelArrow CK')).
    pathvia (ZeroArrow Z y z ;; CokernelArrow CK').
    apply CokernelEqAr.
    apply ZeroArrow_comp_left.
  Defined.

  Lemma are_inverses_from_Cokernel_to_Cokernel {y z : C} {g : y --> z}
        {CK CK': Cokernel g} :
    is_inverse_in_precat (from_Cokernel_to_Cokernel CK CK')
                         (from_Cokernel_to_Cokernel CK' CK).
  Proof.
    split; apply pathsinv0; use CokernelEndo_is_identity;
    unfold from_Cokernel_to_Cokernel; rewrite assoc.
    rewrite (CokernelCommutes CK CK').
    rewrite (CokernelCommutes CK' CK).
    apply idpath.

    rewrite (CokernelCommutes CK' CK).
    rewrite (CokernelCommutes CK CK').
    apply idpath.
  Defined.

  Lemma isiso_from_Cokernel_to_Cokernel {y z : C} {g : y --> z}
        (CK CK' : Cokernel g) :
    is_isomorphism (from_Cokernel_to_Cokernel CK CK').
  Proof.
    apply (is_iso_qinv _ (from_Cokernel_to_Cokernel CK' CK)).
    apply are_inverses_from_Cokernel_to_Cokernel.
  Defined.

  Definition iso_from_Cokernel_to_Cokernel {y z : C} {g : y --> z}
             (CK CK' : Cokernel g) : iso CK CK' :=
    tpair _ _ (isiso_from_Cokernel_to_Cokernel CK CK').


  (** Composing with the CokernelArrow gives the zero arrow. *)
  Lemma CokernelCompZero {y z : C} {g : y --> z} (CK : Cokernel g ) :
    g ;; CokernelArrow CK = ZeroArrow Z y CK.
  Proof.
    unfold CokernelArrow. use (pathscomp0 (CoequalizerEqAr CK)).
    apply ZeroArrow_comp_left.
  Defined.

  (** Cokernel of the ZeroArrow is given by the identity. *)
  Lemma CokernelofZeroArrow (x y : C) : Cokernel (ZeroArrow Z x y).
  Proof.
    use mk_Cokernel.
    apply y. apply (identity y).
    apply id_right.

    use mk_isCoequalizer.
    intros w h H.

    use unique_exists.
    apply h. cbn. apply id_left.
    intros y0. apply hs.
    cbn. intros y0 t. rewrite <- t.
    apply pathsinv0. apply id_left.
  Defined.

  (** More generally, the CokernelArrow of the cokernel of the ZeroArrow is an
    isomorphism. *)
  Lemma CokernelofZeroArrow_iso (x y : C) (CK : Cokernel (ZeroArrow Z x y)) :
    iso y CK.
  Proof.
    exact (iso_from_Cokernel_to_Cokernel (CokernelofZeroArrow x y) CK).
  Defined.

  (** It follows that CokernelArrow is an epi. *)
  Lemma CokernelArrowisEpi {y z : C} {g : y --> z} (CK : Cokernel g ) :
    isEpi (CokernelArrow CK).
  Proof.
    simple refine (CoequalizerArrowisEpi _).
  Defined.

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
Arguments CokernelArrow [C] [Z] [y] [z] [g] _.

(** In the following section we construct a new cokernel from an arrow which is
  equal to cokernelarrow of some cokernel, up to postcomposing with an
  isomorphism *)
Section cokernels_iso.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.


  Definition Cokernel_up_to_iso_eq {x y z : C} (f : x --> y) (g : y --> z)
             (CK : Cokernel Z f) (h : iso CK z)
             (H : g = (CokernelArrow CK) ;; h) :
    f ;; g = ZeroArrow Z x z.
  Proof.
    induction CK as [t p]. induction t as [t' p']. induction p as [t'' p''].
    unfold isCoequalizer in p''.
    rewrite H.
    rewrite <- (ZeroArrow_comp_left _ _ _ _ _ h).
    rewrite assoc.
    apply cancel_postcomposition.
    apply CokernelCompZero.
  Qed.

  Definition Cokernel_up_to_iso_isCoequalizer {x y z : C} (f : x --> y)
             (g : y --> z)
             (CK : Cokernel Z f) (h : iso CK z)
             (H : g = (CokernelArrow CK) ;; h) :
    isCoequalizer f (ZeroArrow Z x y) g
                  (CokernelEqRw Z (Cokernel_up_to_iso_eq f g CK h H)).
  Proof.
    apply mk_isCoequalizer.
    induction CK as [t p]. induction t as [t' p']. induction p as [t'' p''].
    unfold isCoequalizer in p''.
    intros w h0 HH.
    set (tmp := p'' w h0 HH). cbn in tmp. cbn in h.
    induction tmp as [t''' p'''].
    induction t''' as [t'''' p''''].

    use unique_exists.
    exact ((inv_from_iso h) ;; t'''').
    cbn. rewrite <- p''''.
    rewrite assoc. apply cancel_postcomposition.
    cbn in H. rewrite H. rewrite <- assoc.
    rewrite <- id_right. apply cancel_precomposition.
    apply iso_inv_after_iso.

    intros y0. apply hs.
    intros y0 X. cbn in X. cbn in H.
    rewrite H in X.
    rewrite <- assoc in X.
    set (tmp := p''' (tpair _ (h ;; y0) X)).
    apply base_paths in tmp. cbn in tmp.
    rewrite <- tmp. rewrite assoc.
    rewrite iso_after_iso_inv.
    apply pathsinv0. apply id_left.
  Qed.

  Definition Cokernel_up_to_iso {x y z : C} (f : x --> y) (g : y --> z)
             (CK : Cokernel Z f) (h : iso CK z)
             (H : g = (CokernelArrow CK) ;; h) :
    Cokernel Z f
    := (mk_Cokernel Z g _ (Cokernel_up_to_iso_eq f g CK h H)
                    (Cokernel_up_to_iso_isCoequalizer f g CK h H)).

  Definition Cokernel_up_to_iso2_eq {x y z : C} (f1 : x --> z) (f2 : y --> z)
             (h : iso y x) (H : h ;; f1 = f2)
             (CK : Cokernel Z f1) :
    f2 ;; CokernelArrow CK = ZeroArrow Z y CK.
  Proof.
    rewrite <- H. rewrite <- assoc. rewrite CokernelCompZero.
    apply ZeroArrow_comp_right.
  Qed.

  Definition Cokernel_up_to_iso2_isCoequalizer {x y z : C} (f1 : x --> z)
             (f2 : y --> z)
             (h : iso y x) (H : h ;; f1 = f2)
             (CK : Cokernel Z f1) :
    isCoequalizer f2 (ZeroArrow Z y z) (CokernelArrow CK)
                  (CokernelEqRw Z (Cokernel_up_to_iso2_eq f1 f2 h H CK)).
  Proof.
    use mk_isCoequalizer.
    intros w h0 H'.
    rewrite <- H in H'. rewrite <- assoc in H'.
    rewrite ZeroArrow_comp_left in H'.
    rewrite <- (ZeroArrow_comp_right C Z _ _ _ h) in H'.
    apply (maponpaths (fun f : _ => (inv_from_iso h) ;; f)) in H'.
    repeat rewrite assoc in H'.
    repeat rewrite iso_after_iso_inv in H'.
    repeat rewrite id_left in H'.
    apply (unique_exists (CokernelOut Z CK _ _ H')).
    apply (CokernelCommutes Z CK _ _ H').
    intros y0. apply hs.
    intros y0 H''. apply CokernelOutsEq.
    rewrite H''. apply pathsinv0.
    apply CokernelCommutes.
  Qed.

  Definition Cokernel_up_to_iso2 {x y z : C} (f1 : x --> z) (f2 : y --> z)
             (h : iso y x) (H : h ;; f1 = f2)
             (CK : Cokernel Z f1) :
    Cokernel Z f2
    := (mk_Cokernel Z (CokernelArrow CK) _
                    (Cokernel_up_to_iso2_eq f1 f2 h H CK)
                    (Cokernel_up_to_iso2_isCoequalizer f1 f2 h H CK)).

End cokernels_iso.


(** * Cokernel of epi ;; morphism *)
(** ** Introduction
   Suppose E : x --> y is an [Epi] and f : y --> z is a morphism. Then cokernel of E ;; f is
   isomorphic to cokernel of f.
*)
Section cokernels_epis.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.

  Local Lemma CokernelEpiComp_eq1 {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK1 : Cokernel Z (E ;; f)) (CK2 : Cokernel Z f) :
    E ;; f ;; CokernelArrow CK2 = ZeroArrow Z x CK2.
  Proof.
    rewrite <- assoc. rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Definition CokernelEpiComp_mor1 {x y z : C} (E : Epi C x y) (f : y --> z)
             (CK1 : Cokernel Z (E ;; f)) (CK2 : Cokernel Z f) : C⟦CK1, CK2⟧ :=
    CokernelOut Z CK1 _ (CokernelArrow CK2) (CokernelEpiComp_eq1 E f CK1 CK2).

  Local Lemma CokernelEpiComp_eq2 {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK1 : Cokernel Z (E ;; f)) (CK2 : Cokernel Z f) :
    f ;; CokernelArrow CK1 = ZeroArrow Z y CK1.
  Proof.
    use (EpiisEpi C E). rewrite assoc. rewrite ZeroArrow_comp_right. exact (CokernelCompZero Z CK1).
  Qed.

  Definition CokernelEpiComp_mor2 {x y z : C} (E : Epi C x y) (f : y --> z)
             (CK1 : Cokernel Z (E ;; f)) (CK2 : Cokernel Z f) : C⟦CK2, CK1⟧ :=
    CokernelOut Z CK2 _ (CokernelArrow CK1) (CokernelEpiComp_eq2 E f CK1 CK2).

  Lemma CokernelEpiComp1 {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK1 : Cokernel Z (E ;; f)) (CK2 : Cokernel Z f) :
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
        (CK1 : Cokernel Z (E ;; f)) (CK2 : Cokernel Z f) :
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
        (CK : Cokernel Z (E ;; f)) : f ;; CokernelArrow CK = ZeroArrow Z y CK.
  Proof.
    use (EpiisEpi C E). rewrite ZeroArrow_comp_right. rewrite assoc.
    exact (CokernelEqRw' Z (CokernelEqAr Z CK)).
  Qed.

  Local Lemma CokernelEpiComp_isCoequalizer {x y z : C} (E : Epi C x y) (f : y --> z)
        (CK : Cokernel Z (E ;; f)) :
    isCokernel Z (CokernelArrow CK) f (CokernelEpiComp_eq E f CK).
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

  Definition CokernelEpiComp {x y z : C} (E : Epi C x y) (f : y --> z) (CK : Cokernel Z (E ;; f)) :
    Cokernel Z f.
  Proof.
    use mk_Cokernel'.
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
    f' ;; CokernelArrow CK = ZeroArrow Z x CK.
  Proof.
    induction e. use CokernelCompZero.
  Qed.

  Local Lemma CokernelPath_isCokernel {x y : C} {f f' : x --> y} (e : f = f') (CK : Cokernel Z f) :
    isCokernel Z (CokernelArrow CK) f' (CokernelPath_eq e CK).
  Proof.
    induction e. use CokernelisCokernel.
  Qed.

  (** Constructs a cokernel of f' from a cokernel of f in a natural way *)
  Definition CokernelPath {x y : C} {f f' : x --> y} (e : f = f') (CK : Cokernel Z f) :
    Cokernel Z f'.
  Proof.
    use mk_Cokernel'.
    - exact CK.
    - use CokernelArrow.
    - exact (CokernelPath_eq e CK).
    - exact (CokernelPath_isCokernel e CK).
  Defined.

End cokernel_out_paths.
