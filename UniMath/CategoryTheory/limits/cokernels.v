(* direct implementation of cokernels *)
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
  Lemma CokernelEqRw {x y z : C} {g : x --> y} {f : y --> z}
        (H : g ;; f = ZeroArrow _ Z x z) :
    g ;; f = ZeroArrow _ Z x y ;; f.
  Proof.
    pathvia (ZeroArrow _ Z x z).
    apply H. apply pathsinv0. apply ZeroArrow_comp_left.
  Defined.

  (** Definition and construction of Cokernels *)
  Definition Cokernel {y z : C} (g : y --> z) :
    UU := Coequalizer g (ZeroArrow _ Z y z).
  Definition mk_Cokernel {x y z : C} (f : y --> z) (g : x --> y)
             (H : g ;; f = (ZeroArrow _ Z x z))
             (isE : isCoequalizer g (ZeroArrow _ Z x y) f (CokernelEqRw H))
    : Cokernel g.
  Proof.
    use (mk_Coequalizer g (ZeroArrow _ Z x y) f (CokernelEqRw H)).
    apply isE.
  Defined.
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
             (w : C) (h : z --> w) (H : g ;; h = ZeroArrow _ Z y w) :
    C⟦CK, w⟧ := CoequalizerOut CK _ h (CokernelEqRw H).

  (** Commutativity of Cokernels. *)
  Lemma CokernelCommutes {y z : C} {g : y --> z} (CK : Cokernel g)
        (w : C) (h : z --> w) (H : g ;; h = ZeroArrow _ Z y w) :
    (CokernelArrow CK) ;; (CokernelOut CK w h H) = h.
  Proof.
    apply (CoequalizerCommutes CK).
  Defined.

  (** Two arrows from Cokernel, such that the compositions with CokernelArrow
    are equal, are equal. *)
  Lemma CokernelOutsEq {y z: C} {g : y --> z} (CK : Cokernel g)
        {w : C} (φ1 φ2: C⟦CK, w⟧)
        (H' : (CokernelArrow CK) ;; φ1 = (CokernelArrow CK) ;; φ2) : φ1 = φ2.
  Proof.
    apply (isCoequalizerOutsEq (isCoequalizer_Coequalizer CK) _ _ H').
  Defined.

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
    pathvia (ZeroArrow _ Z y z ;; CokernelArrow CK').
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
    g ;; CokernelArrow CK = ZeroArrow C Z y CK.
  Proof.
    unfold CokernelArrow. use (pathscomp0 (CoequalizerEqAr CK)).
    apply ZeroArrow_comp_left.
  Defined.

  (** Cokernel of the ZeroArrow is given by the identity. *)
  Lemma CokernelofZeroArrow (x y : C) : Cokernel (@ZeroArrow C Z x y).
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
  Lemma CokernelofZeroArrow_iso (x y : C) (CK : Cokernel (@ZeroArrow C Z x y)) :
    iso y CK.
  Proof.
    exact (iso_from_Cokernel_to_Cokernel (CokernelofZeroArrow x y) CK).
  Defined.

  (** It follows that CokernelArrow is an epi. *)
  Lemma CokernelArrowisEpi {y z : C} {g : y --> z} (CK : Cokernel g ) :
    isEpi _ (CokernelArrow CK).
  Proof.
    apply CoequalizerArrowisEpi.
  Defined.
End def_cokernels.


(** In the following section we construct a new cokernel from an arrow which is
  equal to cokernelarrow of some cokernel, up to postcomposing with an
  isomorphism *)
Section cokernels_iso.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.


  Definition Cokernel_up_to_iso_eq {x y z : C} (f : x --> y) (g : y --> z)
             (CK : Cokernel Z f) (h : iso CK z)
             (H : g = (CokernelArrow _ CK) ;; h) :
    f ;; g = ZeroArrow C Z x z.
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
             (H : g = (CokernelArrow _ CK) ;; h) :
    isCoequalizer f (ZeroArrow C Z x y) g
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
             (H : g = (CokernelArrow _ CK) ;; h) :
    Cokernel Z f
    := (mk_Cokernel Z g _ (Cokernel_up_to_iso_eq f g CK h H)
                    (Cokernel_up_to_iso_isCoequalizer f g CK h H)).

  Definition Cokernel_up_to_iso2_eq {x y z : C} (f1 : x --> z) (f2 : y --> z)
             (h : iso y x) (H : h ;; f1 = f2)
             (CK : Cokernel Z f1) :
    f2 ;; CokernelArrow Z CK = ZeroArrow C Z y CK.
  Proof.
    rewrite <- H. rewrite <- assoc. rewrite CokernelCompZero.
    apply ZeroArrow_comp_right.
  Qed.


  Definition Cokernel_up_to_iso2_isCoequalizer {x y z : C} (f1 : x --> z)
             (f2 : y --> z)
             (h : iso y x) (H : h ;; f1 = f2)
             (CK : Cokernel Z f1) :
    isCoequalizer f2 (ZeroArrow C Z y z) (CokernelArrow Z CK)
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
    := (mk_Cokernel Z (CokernelArrow Z CK) _
                    (Cokernel_up_to_iso2_eq f1 f2 h H CK)
                    (Cokernel_up_to_iso2_isCoequalizer f1 f2 h H CK)).
End cokernels_iso.
