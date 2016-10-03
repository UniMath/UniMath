(**

Direct implementation of kernels together with:

- Proof that the kernel arrow is monic ([KernelArrowisMonic])

Written by Tomi Pannila.

*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.zero.

(** Definition of kernels *)
Section def_kernels.

  Context {C : precategory}.
  Hypothesis Z : Zero C.
  Hypothesis hs : has_homsets C.

  (** This rewrite is used to rewrite an equality f ;; g = ZeroArrow to
     f ;; g = f ;; ZeroArrow. This is because Equalizers need the latter
     equality. *)
  Lemma KernelEqRw {x y z : C} {g : y --> z} {f : x --> y} (H : f ;; g = ZeroArrow Z x z) :
    f ;; g = f ;; ZeroArrow Z y z.
  Proof.
    pathvia (ZeroArrow Z x z).
    apply H. apply pathsinv0. apply ZeroArrow_comp_right.
  Defined.

  (** Definition and construction of Kernels *)
  Definition isKernel {x y z : C} (f : x --> y) (g : y --> z) (H : f ;; g = ZeroArrow Z x z) : UU :=
    isEqualizer g (ZeroArrow Z y z) f (KernelEqRw H).

  Definition Kernel {y z : C} (g : y --> z) : UU := Equalizer g (ZeroArrow Z y z).
  Definition mk_Kernel {x y z : C} (f : x --> y) (g : y --> z) (H : f ;; g = (ZeroArrow Z x z))
             (isE : isEqualizer g (ZeroArrow Z y z) f (KernelEqRw H)) : Kernel g.
  Proof.
    use (mk_Equalizer g (ZeroArrow Z y z) f (KernelEqRw H)).
    apply isE.
  Defined.
  Definition Kernels : UU := Π (y z : C) (g : y --> z), Kernel g.
  Definition hasKernels : UU := Π (y z : C) (g : y --> z), ishinh (Kernel g).
  Definition KernelOb {y z : C} {g : y --> z} (K : Kernel g) :
    C := EqualizerObject K.
  Coercion KernelOb : Kernel >-> ob.
  Definition KernelArrow {y z : C} {g : y --> z} (K : Kernel g) :
    C⟦K, y⟧ := EqualizerArrow K.
  Definition KernelEqAr {y z : C} {g : y --> z} (K : Kernel g)
    : EqualizerArrow K ;; g = EqualizerArrow K ;; (ZeroArrow Z y z)
    := EqualizerEqAr K.
  Definition KernelIn {y z : C} {g : y --> z} (K : Kernel g)
             (w : C) (h : w --> y) (H : h ;; g = ZeroArrow Z w z) :
    C⟦w, K⟧ := EqualizerIn K _ h (KernelEqRw H).

  (** Commutativity of Kernels. *)
  Lemma KernelCommutes {y z : C} {g : y --> z} (K : Kernel g)
        (w : C) (h : w --> y) (H : h ;; g = ZeroArrow Z w z) :
    (KernelIn K w h H) ;; (KernelArrow K) = h.
  Proof.
    apply (EqualizerCommutes K).
  Defined.

  (** Two arrows to Kernel, such that the compositions with KernelArrow
    are equal, are equal. *)
  Lemma KernelInsEq {y z: C} {g : y --> z} (K : Kernel g)
        {w : C} (φ1 φ2: C⟦w, K⟧)
        (H' : φ1 ;; (KernelArrow K) = φ2 ;; (KernelArrow K)) : φ1 = φ2.
  Proof.
    apply (isEqualizerInsEq (isEqualizer_Equalizer K) _ _ H').
  Defined.

  (** Results on morphisms between Kernels. *)
  Definition identity_is_KernelIn {y z : C} {g : y --> z}
             (K : Kernel g) :
    Σ φ : C⟦K, K⟧, φ ;; (KernelArrow K) = (KernelArrow K).
  Proof.
    exists (identity K).
    apply id_left.
  Defined.

  Lemma KernelEndo_is_identity {y z : C} {g : y --> z} {K : Kernel g}
        (φ : C⟦K, K⟧) (H : φ ;; (KernelArrow K) = KernelArrow K) :
    identity K = φ.
  Proof.
    set (H1 := tpair ((fun φ' : C⟦K, K⟧ => φ' ;; _ = _)) φ H).
    assert (H2 : identity_is_KernelIn K = H1).
    - apply proofirrelevance.
      apply isapropifcontr.
      apply (isEqualizer_Equalizer K).
      apply KernelEqAr.
    - apply (base_paths _ _ H2).
  Defined.

  Definition from_Kernel_to_Kernel {y z : C} {g : y --> z}
             (K K': Kernel g) : C⟦K, K'⟧.
  Proof.
    apply (KernelIn K' K (KernelArrow K)).
    pathvia (KernelArrow K ;; ZeroArrow Z y z).
    apply KernelEqAr.
    apply ZeroArrow_comp_right.
  Defined.

  Lemma are_inverses_from_Kernel_to_Kernel {y z : C} {g : y --> z}
        {K K': Kernel g} :
    is_inverse_in_precat (from_Kernel_to_Kernel K K')
                         (from_Kernel_to_Kernel K' K).
  Proof.
    split; apply pathsinv0; use KernelEndo_is_identity;
    rewrite <- assoc; unfold from_Kernel_to_Kernel;
      repeat rewrite KernelCommutes; apply idpath.
  Defined.

  Lemma isiso_from_Kernel_to_Kernel {y z : C} {g : y --> z}
        (K K' : Kernel g) :
    is_isomorphism (from_Kernel_to_Kernel K K').
  Proof.
    apply (is_iso_qinv _ (from_Kernel_to_Kernel K' K)).
    apply are_inverses_from_Kernel_to_Kernel.
  Defined.

  Definition iso_from_Kernel_to_Kernel {y z : C} {g : y --> z}
             (K K' : Kernel g) : iso K K' :=
    tpair _ _ (isiso_from_Kernel_to_Kernel K K').

  (** Composing with the KernelArrow gives the zero arrow. *)
  Lemma KernelCompZero {x y : C} {f : x --> y} (K : Kernel f ) :
    KernelArrow K ;; f = ZeroArrow Z K y.
  Proof.
    unfold KernelArrow. use (pathscomp0 (EqualizerEqAr K)).
    apply ZeroArrow_comp_right.
  Defined.

  (** Kernel of the morphism to zero object is given by identity *)
  Lemma KernelofZeroArrow (x y : C) : Kernel (@ZeroArrow C Z x y).
  Proof.
    use mk_Kernel.
    apply x. apply (identity x).
    apply id_left.

    use mk_isEqualizer.
    intros w h H.

    use unique_exists.
    apply h. cbn. apply id_right.
    intros y0. apply hs.
    cbn. intros y0 t. rewrite <- t.
    apply pathsinv0. apply id_right.
  Defined.

  (** More generally, the KernelArrow of the kernel of the ZeroArrow is an
    isomorphism. *)
  Lemma KernelofZeroArrow_iso (x y : C) (K : Kernel (@ZeroArrow C Z x y)) :
    iso K x.
  Proof.
    exact (iso_from_Kernel_to_Kernel K (KernelofZeroArrow x y)).
  Defined.

  (** It follows that KernelArrow is monic. *)
  Lemma KernelArrowisMonic {y z : C} {g : y --> z} (K : Kernel g ) :
    isMonic (KernelArrow K).
  Proof.
    exact (EqualizerArrowisMonic K).
  Defined.
End def_kernels.
Arguments KernelArrow [C] [Z] [y] [z] [g] _.


(** In the following section we construct a new kernel from an arrow which is
  equal to kernelarrow of some kernel, up to precomposing with an isomorphism *)
Section kernels_iso.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.


  Definition Kernel_up_to_iso_eq {x y z : C} (f : x --> y) (g : y --> z)
             (K : Kernel Z g) (h : iso x K)
             (H : f = h ;; (KernelArrow K)) :
    f ;; g = ZeroArrow Z x z.
  Proof.
    induction K as [t p]. induction t as [t' p']. induction p as [t'' p''].
    unfold isEqualizer in p''.
    rewrite H.
    rewrite <- (ZeroArrow_comp_right _ _ _ _ _ h).
    rewrite <- assoc.
    apply cancel_precomposition.
    apply KernelCompZero.
  Qed.


  Definition Kernel_up_to_iso_isEqualizer {x y z : C} (f : x --> y) (g : y --> z)
             (K : Kernel Z g) (h : iso x K)
             (H : f = h ;; (KernelArrow K)) :
    isEqualizer g (ZeroArrow Z y z) f
                (KernelEqRw Z (Kernel_up_to_iso_eq f g K h H)).
  Proof.
   apply mk_isEqualizer.
    induction K as [t p]. induction t as [t' p']. induction p as [t'' p''].
    unfold isEqualizer in p''.
    intros w h0 HH.
    set (tmp := p'' w h0 HH). cbn in tmp. cbn in h.
    induction tmp as [t''' p'''].
    induction t''' as [t'''' p''''].

    use unique_exists.
    exact (t'''' ;; (inv_from_iso h)).
    cbn. rewrite <- p''''.
    rewrite <- assoc. apply cancel_precomposition.
    cbn in H. rewrite H. rewrite assoc.
    rewrite <- id_left. apply cancel_postcomposition.
    apply iso_after_iso_inv.

    intros y0. apply hs.
    intros y0 X. cbn in X. cbn in H.
    rewrite H in X.
    rewrite assoc in X.
    set (tmp := p''' (tpair _ (y0 ;; h) X)).
    apply base_paths in tmp. cbn in tmp.
    rewrite <- tmp. rewrite <- assoc.
    rewrite iso_inv_after_iso.
    apply pathsinv0. apply id_right.
  Qed.

  Definition Kernel_up_to_iso {x y z : C} (f : x --> y) (g : y --> z)
             (K : Kernel Z g) (h : iso x K)
             (H : f = h ;; (KernelArrow K)) :
    Kernel Z g
    := (mk_Kernel Z f _ (Kernel_up_to_iso_eq f g K h H)
                  (Kernel_up_to_iso_isEqualizer f g K h H)).

  Definition Kernel_up_to_iso2_eq  {x y z : C} (f1 : x --> y) (f2 : x --> z)
             (h : iso y z) (H : f1 ;; h = f2)
             (K : Kernel Z f1) :
    KernelArrow K ;; f2 = ZeroArrow Z K z.
  Proof.
    rewrite <- H. rewrite assoc. rewrite KernelCompZero.
    apply ZeroArrow_comp_left.
  Qed.

  Definition Kernel_up_to_iso2_isEqualizer {x y z : C} (f1 : x --> y)
             (f2 : x --> z)
             (h : iso y z) (H : f1 ;; h = f2)
             (K : Kernel Z f1) :
    isEqualizer f2 (ZeroArrow Z x z) (KernelArrow K)
                (KernelEqRw Z (Kernel_up_to_iso2_eq f1 f2 h H K)).
  Proof.
    use mk_isEqualizer.
    intros w h0 H'.
    rewrite <- H in H'. rewrite assoc in H'.
    rewrite ZeroArrow_comp_right in H'.
    rewrite <- (ZeroArrow_comp_left C Z _ _ _ h) in H'.
    apply (maponpaths (fun f : _ => f ;; (inv_from_iso h))) in H'.
    rewrite <- assoc in H'. rewrite <- (assoc  _ h) in H'.
    repeat rewrite iso_inv_after_iso in H'.
    repeat rewrite id_right in H'.
    apply (unique_exists (KernelIn Z K _ _ H')).
    apply (KernelCommutes Z K _ _ H').
    intros y0. apply hs.
    intros y0 H''. apply KernelInsEq.
    rewrite H''. apply pathsinv0.
    apply KernelCommutes.
  Qed.

  Definition Kernel_up_to_iso2 {x y z : C} (f1 : x --> y) (f2 : x --> z)
             (h : iso y z) (H : f1 ;; h = f2)
             (K : Kernel Z f1) :
    Kernel Z f2
    := (mk_Kernel Z (KernelArrow K) _ (Kernel_up_to_iso2_eq f1 f2 h H K)
                  (Kernel_up_to_iso2_isEqualizer f1 f2 h H K)).
End kernels_iso.
