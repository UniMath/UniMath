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

  Lemma KernelEqRw' {x y z : C} {g : y --> z} {f : x --> y} (H : f ;; g = f ;; ZeroArrow Z y z) :
    f ;; g = ZeroArrow Z x z.
  Proof.
    rewrite ZeroArrow_comp_right in H. exact H.
  Qed.

  (** Definition and construction of Kernels *)
  Definition isKernel {x y z : C} (f : x --> y) (g : y --> z) (H : f ;; g = ZeroArrow Z x z) : UU :=
    isEqualizer g (ZeroArrow Z y z) f (KernelEqRw H).

  Local Lemma mk_isKernel_uniqueness {x y z : C} (f : x --> y) (g : y --> z)
             (H1 : f ;; g = ZeroArrow Z x z)
             (H2 : Π (w : C) (h : w --> y) (H' : h ;; g = ZeroArrow Z w z),
                   iscontr (Σ ψ : w --> x, ψ ;; f = h))
             (w : C) (h : w --> y) (H' : h ;; g = h ;; ZeroArrow Z y z) :
    Π y0 : C ⟦ w, x ⟧, y0 ;; f = h → y0 = pr1 (iscontrpr1 (H2 w h (KernelEqRw' H'))).
  Proof.
    intros y0 H. apply (base_paths _ _ ((pr2 (H2 w h (KernelEqRw' H'))) (tpair _ y0 H))).
  Qed.

  Definition mk_isKernel {x y z : C} (f : x --> y) (g : y --> z) (H1 : f ;; g = ZeroArrow Z x z)
             (H2 : Π (w : C) (h : w --> y) (H' : h ;; g = ZeroArrow Z w z),
                   iscontr (Σ ψ : w --> x, ψ ;; f = h)) : isKernel f g H1.
  Proof.
    use mk_isEqualizer.
    intros w h H'.
    use unique_exists.
    - exact (pr1 (iscontrpr1 (H2 w h (KernelEqRw' H')))).
    - exact (pr2 (iscontrpr1 (H2 w h (KernelEqRw' H')))).
    - intros y0. apply hs.
    - exact (mk_isKernel_uniqueness f g H1 H2 w h H').
  Defined.

  Definition Kernel {y z : C} (g : y --> z) : UU := Equalizer g (ZeroArrow Z y z).
  Definition mk_Kernel {x y z : C} (f : x --> y) (g : y --> z) (H : f ;; g = (ZeroArrow Z x z))
             (isE : isEqualizer g (ZeroArrow Z y z) f (KernelEqRw H)) : Kernel g.
  Proof.
    use (mk_Equalizer g (ZeroArrow Z y z) f (KernelEqRw H)).
    apply isE.
  Defined.

  Definition mk_Kernel' {x y z : C} (f : x --> y) (g : y --> z) (H : f ;; g = (ZeroArrow Z x z))
             (isK : isKernel f g H) : Kernel g :=
    mk_Kernel f g H isK.

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

  Lemma KernelisKernel {y z : C} {g : y --> z} (K : Kernel g) :
    isKernel (KernelArrow K) g (KernelEqRw' (KernelEqAr K)).
  Proof.
    apply isEqualizer_Equalizer.
  Qed.

  (** Two arrows to Kernel, such that the compositions with KernelArrow
    are equal, are equal. *)
  Lemma KernelInsEq {y z: C} {g : y --> z} (K : Kernel g)
        {w : C} (φ1 φ2: C⟦w, K⟧)
        (H' : φ1 ;; (KernelArrow K) = φ2 ;; (KernelArrow K)) : φ1 = φ2.
  Proof.
    apply (isEqualizerInsEq (isEqualizer_Equalizer K) _ _ H').
  Defined.

  Lemma KernelInComp {y z : C} {f : y --> z} (K : Kernel f) {x x' : C}
        (h1 : x --> x') (h2 : x' --> y)
        (H1 : h1 ;; h2 ;; f = ZeroArrow Z _ _) (H2 : h2 ;; f = ZeroArrow Z _ _) :
    KernelIn K x (h1 ;; h2) H1 = h1 ;; KernelIn K x' h2 H2.
  Proof.
    apply EqualizerInComp.
  Qed.

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
  Lemma KernelArrowisMonic {y z : C} {g : y --> z} (K : Kernel g) :
    isMonic (KernelArrow K).
  Proof.
    exact (EqualizerArrowisMonic K).
  Defined.

  Lemma KernelsIn_is_iso {x y : C} {f : x --> y} (K1 K2 : Kernel f) :
    is_iso (KernelIn K1 K2 (KernelArrow K2) (KernelCompZero K2)).
  Proof.
    use is_iso_qinv.
    - use KernelIn.
      + use KernelArrow.
      + use KernelCompZero.
    - split.
      + use KernelInsEq. rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
        rewrite id_left. apply idpath.
      + use KernelInsEq. rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
        rewrite id_left. apply idpath.
  Qed.

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


(** * Kernel of morphism ;; monic *)
(** ** Introduction
   Suppose f : x --> y is a morphism and M : y --> z is a Monic. Then kernel of f ;; M is
   isomorphic to kernel of f.
*)
Section kernels_monics.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.

  Local Lemma KernelCompMonic_eq1 {x y z : C} (f : x --> y) (M : Monic C y z)
        (K1 : Kernel Z (f ;; M)) (K2 : Kernel Z f) :
    KernelArrow K1 ;; f = ZeroArrow Z K1 y.
  Proof.
    use (MonicisMonic C M). rewrite ZeroArrow_comp_left. rewrite <- assoc. use KernelCompZero.
  Qed.

  Definition KernelCompMonic_mor1 {x y z : C} (f : x --> y) (M : Monic C y z)
        (K1 : Kernel Z (f ;; M)) (K2 : Kernel Z f) : C⟦K1, K2⟧ :=
    KernelIn Z K2 _ (KernelArrow K1) (KernelCompMonic_eq1 f M K1 K2).

  Local Lemma KernelCompMonic_eq2 {x y z : C} (f : x --> y) (M : Monic C y z)
        (K1 : Kernel Z (f ;; M)) (K2 : Kernel Z f) : KernelArrow K2 ;; (f ;; M) = ZeroArrow Z K2 z.
  Proof.
    rewrite assoc. rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Definition KernelCompMonic_mor2 {x y z : C} (f : x --> y) (M : Monic C y z)
             (K1 : Kernel Z (f ;; M)) (K2 : Kernel Z f) : C⟦K2, K1⟧ :=
    KernelIn Z K1 _ (KernelArrow K2) (KernelCompMonic_eq2 f M K1 K2).

  Lemma KernelCompMonic1 {x y z : C} (f : x --> y) (M : Monic C y z)
             (K1 : Kernel Z (f ;; M)) (K2 : Kernel Z f) :
    is_iso (KernelCompMonic_mor1 f M K1 K2).
  Proof.
    use is_iso_qinv.
    - exact (KernelCompMonic_mor2 f M K1 K2).
    - split.
      + unfold KernelCompMonic_mor1. unfold KernelCompMonic_mor2.
        use KernelInsEq.
        rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
        apply pathsinv0. apply id_left.
      + unfold KernelCompMonic_mor1. unfold KernelCompMonic_mor2.
        use KernelInsEq.
        rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
        apply pathsinv0. apply id_left.
  Qed.

  Lemma KernelCompMonic2 {x y z : C} (f : x --> y) (M : Monic C y z)
             (K1 : Kernel Z (f ;; M)) (K2 : Kernel Z f) :
    is_iso (KernelCompMonic_mor2 f M K1 K2).
  Proof.
    use is_iso_qinv.
    - exact (KernelCompMonic_mor1 f M K1 K2).
    - split.
      + unfold KernelCompMonic_mor1. unfold KernelCompMonic_mor2.
        use KernelInsEq.
        rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
        apply pathsinv0. apply id_left.
      + unfold KernelCompMonic_mor1. unfold KernelCompMonic_mor2.
        use KernelInsEq.
        rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
        apply pathsinv0. apply id_left.
  Qed.

  Local Lemma KernelCompMonic_eq {x y z : C} (f : x --> y) (M : Monic C y z)
        (K : Kernel Z (f ;; M)) : KernelArrow K ;; f = ZeroArrow Z K y.
  Proof.
    use (MonicisMonic C M). rewrite ZeroArrow_comp_left. rewrite <- assoc. use KernelCompZero.
  Qed.

  Local Lemma KernelCompMonic_isKernel {x y z : C} (f : x --> y) (M : Monic C y z)
        (K : Kernel Z (f ;; M)) :
    isKernel Z (KernelArrow K) f (KernelCompMonic_eq f M K).
  Proof.
    use mk_isKernel.
    - exact hs.
    - intros w h H'.
      use unique_exists.
      + use KernelIn.
        * exact h.
        * rewrite assoc. rewrite <- (ZeroArrow_comp_left _ _ _ _ _ M). apply cancel_postcomposition.
          exact H'.
      + cbn. rewrite KernelCommutes. apply idpath.
      + intros y0. apply hs.
      + intros y0 X.
        apply pathsinv0. cbn in X.
        use (MonicisMonic C (mk_Monic _ _ (KernelArrowisMonic Z K))). cbn.
        rewrite KernelCommutes. apply pathsinv0. apply X.
  Qed.

  Definition KernelCompMonic {x y z : C} (f : x --> y) (M : Monic C y z) (K : Kernel Z (f ;; M)) :
    Kernel Z f.
  Proof.
    use mk_Kernel'.
    - exact K.
    - use KernelArrow.
    - exact (KernelCompMonic_eq f M K).
    - exact (KernelCompMonic_isKernel f M K).
  Defined.

End kernels_monics.


(** * KernelIn of equal, not necessarily definitionally equal, morphisms is iso *)
Section kernel_in_paths.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.

  Definition KernelInPaths_is_iso_mor {x y : C} {f f' : x --> y} (e : f = f')
             (K1 : Kernel Z f) (K2 : Kernel Z f') : K1 --> K2.
  Proof.
    induction e.
    use KernelIn.
    - use KernelArrow.
    - use KernelCompZero.
  Defined.

  Lemma KernelInPaths_is_iso {x y : C} {f f' : x --> y} (e : f = f')
        (K1 : Kernel Z f) (K2 : Kernel Z f') : is_iso (KernelInPaths_is_iso_mor e K1 K2).
  Proof.
    induction e. apply KernelsIn_is_iso.
  Qed.

  Local Lemma KernelPath_eq {x y : C} {f f' : x --> y} (e : f = f') (K : Kernel Z f) :
    KernelArrow K ;; f' = ZeroArrow Z K y.
  Proof.
    induction e. use KernelCompZero.
  Qed.

  Local Lemma KernelPath_isKernel {x y : C} {f f' : x --> y} (e : f = f') (K : Kernel Z f) :
    isKernel Z (KernelArrow K) f' (KernelPath_eq e K).
  Proof.
    induction e. use KernelisKernel.
  Qed.

  (** Constructs a cokernel of f' from a cokernel of f in a natural way *)
  Definition KernelPath {x y : C} {f f' : x --> y} (e : f = f') (K : Kernel Z f) : Kernel Z f'.
  Proof.
    use mk_Kernel'.
    - exact K.
    - use KernelArrow.
    - exact (KernelPath_eq e K).
    - exact (KernelPath_isKernel e K).
  Defined.

End kernel_in_paths.


(** Transports of kernels *)
Section transport_kernels.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.

  Local Lemma transportb_KernelIn_eq {x' x y z : C} (f : x --> y) {g : y --> z} (K : Kernel Z g)
        (e : x' = x) (H : f ;; g = ZeroArrow Z _ _) :
    (transportb (fun x' : ob C => precategory_morphisms x' y) e f) ;; g = ZeroArrow Z _ _.
  Proof.
    induction e. apply H.
  Qed.

  Lemma transportb_KernelIn {x' x y z : C} (f : x --> y) {g : y --> z} (K : Kernel Z g)
        (e : x' = x) (H : f ;; g = ZeroArrow Z _ _) :
    transportb (fun x' : ob C => precategory_morphisms x' K) e (KernelIn Z K _ f H) =
    KernelIn Z K _ (transportb (fun x' : ob C => precategory_morphisms x' y) e f)
             (transportb_KernelIn_eq f K e H).
  Proof.
    induction e. use KernelInsEq. cbn. unfold idfun.
    rewrite KernelCommutes. rewrite KernelCommutes.
    apply idpath.
  Qed.

End transport_kernels.
