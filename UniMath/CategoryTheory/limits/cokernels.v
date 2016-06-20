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

  (** This rewrite is used to rewrite an equality f ;; g = ZeroArrow to
     f ;; g = ZeroArrow ;; g. This is because Coequalizers need the latter
     equality. *)
  Lemma CokernelEqRw {x y z : C} {g : x --> y} {f : y --> z}
        (H : g ;; f = ZeroArrow _ Z x z) :
    g ;; f = ZeroArrow _ Z x y ;; f.
  Proof.
    rewrite <- (ZeroArrow_comp_left _ Z x y z f) in H.
    exact H.
  Defined.

  (** Definition and construction of Cokernels *)
  Definition Cokernel {y z : C} (g : y --> z) :=
    Coequalizer g (ZeroArrow _ Z y z).
  Definition mk_Cokernel {x y z : C} (f : y --> z) (g : x --> y)
             (H : g ;; f = (ZeroArrow _ Z x z))
             (isE : isCoequalizer g (ZeroArrow _ Z x y) f (CokernelEqRw H))
    : Cokernel g.
  Proof.
    use (mk_Coequalizer g (ZeroArrow _ Z x y) f (CokernelEqRw H)).
    apply isE.
  Defined.
  Definition Cokernels := forall (y z : C) (g : y --> z), Cokernel g.
  Definition hasCokernels := forall (y z : C) (g : y --> z), ishinh (Cokernel g).
  Definition CokernelOb {y z : C} {g : y --> z} (CK : Cokernel g)
    := CoequalizerObject CK.
  Coercion CokernelOb : Cokernel >-> ob.
  Definition CokernelArrow {y z : C} {g : y --> z} (CK : Cokernel g) :=
    CoequalizerArrow CK.
  Definition CokernelEqAr {y z : C} {g : y --> z} (CK : Cokernel g) :=
    CoequalizerEqAr CK.
  Definition CokernelOut {y z : C} {g : y --> z} (CK : Cokernel g)
             (w : C) (h : z --> w) (H : g ;; h = ZeroArrow _ Z y w) : C⟦CK, w⟧.
  Proof.
    exact (pr1 (pr1 (isCoequalizer_Coequalizer CK w h (CokernelEqRw H)))).
  Defined.

  (** Commutativity of Cokernels. *)
  Lemma CokernelCommutes {y z : C} {g : y --> z} (CK : Cokernel g)
        (w : C) (h : z --> w) (H : g ;; h = ZeroArrow _ Z y w) :
    (CokernelArrow CK) ;; (CokernelOut CK w h H) = h.
  Proof.
    exact (pr2 (pr1 ((isCoequalizer_Coequalizer CK) w h (CokernelEqRw H)))).
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
    rewrite <- (ZeroArrow_comp_left _ Z y z CK' (CokernelArrow CK')).
    apply CokernelEqAr.
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

  (** It follows that CokernelArrow is an epi. *)
  Lemma CokernelArrowisEpi {y z : C} {g : y --> z} (CK : Cokernel g ) :
    isEpi _ (CokernelArrow CK).
  Proof.
    apply CoequalizerArrowisEpi.
  Defined.
End def_cokernels.
