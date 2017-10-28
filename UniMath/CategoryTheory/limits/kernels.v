(** * Direct implementation of kernels *)
(** ** Contents
- Definition of [Kernel]
- Correspondence of Kernels and Equalizers
- Kernel up to isomorphism
- Kernel of morphism · [Monic]
- KernelIn of equal morphisms
- Transport of kernels
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.zero.


(** Definition of kernels *)
Section def_kernels.

  Context {C : precategory}.
  Hypothesis hs : has_homsets C.
  Variable Z : Zero C.


  (** Definition and construction of Kernels *)
  Definition isKernel {x y z : C} (f : x --> y) (g : y --> z) (H : f · g = ZeroArrow Z x z) : UU :=
    ∏ (w : C) (h : w --> y) (H : h · g = ZeroArrow Z w z), iscontr (∑ φ : w --> x, φ · f = h).

  Lemma isKernel_paths {x y z : C} (f : x --> y) (g : y --> z) (H H' : f · g = (ZeroArrow Z x z))
        (isK : isKernel f g H) : isKernel f g H'.
  Proof.
    assert (e : H = H') by apply hs.
    induction e. exact isK.
  Qed.

  Definition mk_isKernel {x y z : C} (f : x --> y) (g : y --> z) (H1 : f · g = ZeroArrow Z x z)
             (H2 : ∏ (w : C) (h : w --> y) (H' : h · g = ZeroArrow Z w z),
                   iscontr (∑ ψ : w --> x, ψ · f = h)) : isKernel f g H1.
  Proof.
    unfold isKernel.
    intros w h H.
    use unique_exists.
    - exact (pr1 (iscontrpr1 (H2 w h H))).
    - exact (pr2 (iscontrpr1 (H2 w h H))).
    - intros y0. apply hs.
    - intros y0 X. exact (base_paths _ _ (pr2 (H2 w h H) (tpair _ y0 X))).
  Defined.

  Definition Kernel {y z : C} (g : y --> z) : UU :=
    ∑ D : (∑ x : ob C, x --> y),
          ∑ (e : (pr2 D) · g = ZeroArrow Z (pr1 D) z), isKernel (pr2 D) g e.

  Definition mk_Kernel {x y z : C} (f : x --> y) (g : y --> z) (H : f · g = (ZeroArrow Z x z))
             (isE : isKernel f g H) : Kernel g := ((x,,f),,(H,,isE)).

  Definition Kernels : UU := ∏ (y z : C) (g : y --> z), Kernel g.

  Definition hasKernels : UU := ∏ (y z : C) (g : y --> z), ishinh (Kernel g).

  (** Accessor functions *)
  Definition KernelOb {y z : C} {g : y --> z} (K : Kernel g) : C := pr1 (pr1 K).
  Coercion KernelOb : Kernel >-> ob.

  Definition KernelArrow {y z : C} {g : y --> z} (K : Kernel g) :  C⟦K, y⟧ := pr2 (pr1 K).

  Definition KernelCompZero {y z : C} {g : y --> z} (K : Kernel g) :
    KernelArrow K · g = ZeroArrow Z K z := pr1 (pr2 K).

  Definition KernelisKernel {y z : C} {g : y --> z} (K : Kernel g) :
    isKernel (KernelArrow K) g (KernelCompZero K) := pr2 (pr2 K).

  Definition KernelIn {y z : C} {g : y --> z} (K : Kernel g) (w : C) (h : w --> y)
             (H : h · g = ZeroArrow Z w z) : C⟦w, K⟧ :=
    pr1 (iscontrpr1 ((KernelisKernel K) w h H)).

  Definition KernelCommutes {y z : C} {g : y --> z} (K : Kernel g) (w : C) (h : w --> y)
             (H : h · g = ZeroArrow Z w z) : (KernelIn K w h H) · (KernelArrow K) = h :=
    pr2 (iscontrpr1 ((KernelisKernel K) w h H)).

  Local Lemma KernelInUnique {x y z : C} {f : x --> y} {g : y --> z} {H : f · g = ZeroArrow Z x z}
        (isK : isKernel f g H) {w : C} {h : w --> y} (H' : h · g = ZeroArrow Z w z) {φ : w --> x}
        (H'' : φ · f = h) :
    φ = (pr1 (pr1 (isK w h H'))).
  Proof.
    exact (base_paths _ _ (pr2 (isK w h H') (tpair _ φ H''))).
  Qed.

  Lemma KernelInsEq {y z: C} {g : y --> z} (K : Kernel g) {w : C} (φ1 φ2 : C⟦w, K⟧)
        (H : φ1 · (KernelArrow K) = φ2 · (KernelArrow K)) : φ1 = φ2.
  Proof.
    assert (H1 : φ1 · (KernelArrow K) · g = ZeroArrow Z _ _).
    {
      rewrite <- assoc. rewrite KernelCompZero. apply ZeroArrow_comp_right.
    }
    rewrite (KernelInUnique (KernelisKernel K) H1 (idpath _)).
    apply pathsinv0.
    set (tmp := pr2 (KernelisKernel K w (φ1 · KernelArrow K) H1) (tpair _ φ2 (! H))).
    exact (base_paths _ _ tmp).
  Qed.

  Lemma KernelInComp {y z : C} {f : y --> z} (K : Kernel f) {x x' : C}
        (h1 : x --> x') (h2 : x' --> y)
        (H1 : h1 · h2 · f = ZeroArrow Z _ _) (H2 : h2 · f = ZeroArrow Z _ _) :
    KernelIn K x (h1 · h2) H1 = h1 · KernelIn K x' h2 H2.
  Proof.
    use KernelInsEq. rewrite KernelCommutes. rewrite <- assoc. rewrite KernelCommutes.
    apply idpath.
  Qed.

  (** Results on morphisms between Kernels. *)
  Definition identity_is_KernelIn {y z : C} {g : y --> z} (K : Kernel g) :
    ∑ φ : C⟦K, K⟧, φ · (KernelArrow K) = (KernelArrow K).
  Proof.
    exists (identity K).
    apply id_left.
  Defined.

  Lemma KernelEndo_is_identity {y z : C} {g : y --> z} {K : Kernel g}
        (φ : C⟦K, K⟧) (H : φ · (KernelArrow K) = KernelArrow K) :
    identity K = φ.
  Proof.
    set (H1 := tpair ((fun φ' : C⟦K, K⟧ => φ' · _ = _)) φ H).
    assert (H2 : identity_is_KernelIn K = H1).
    - apply proofirrelevance.
      apply isapropifcontr.
      apply (KernelisKernel K).
      apply KernelCompZero.
    - apply (base_paths _ _ H2).
  Defined.

  Definition from_Kernel_to_Kernel {y z : C} {g : y --> z} (K K': Kernel g) : C⟦K, K'⟧.
  Proof.
    apply (KernelIn K' K (KernelArrow K)). apply KernelCompZero.
  Defined.

  Lemma are_inverses_from_Kernel_to_Kernel {y z : C} {g : y --> z} (K K': Kernel g) :
    is_inverse_in_precat (from_Kernel_to_Kernel K K') (from_Kernel_to_Kernel K' K).
  Proof.
    split.
    - apply pathsinv0. use KernelEndo_is_identity. rewrite <- assoc.
      unfold from_Kernel_to_Kernel. rewrite KernelCommutes.
      rewrite KernelCommutes. apply idpath.
    - apply pathsinv0. use KernelEndo_is_identity. rewrite <- assoc.
      unfold from_Kernel_to_Kernel. rewrite KernelCommutes.
      rewrite KernelCommutes. apply idpath.
  Qed.

  Lemma from_Kernel_to_Kernel_is_iso {y z : C} {g : y --> z} (K K' : Kernel g) :
    is_iso (from_Kernel_to_Kernel K K').
  Proof.
    apply (is_iso_qinv _ (from_Kernel_to_Kernel K' K)).
    apply are_inverses_from_Kernel_to_Kernel.
  Qed.

  Definition iso_from_Kernel_to_Kernel {y z : C} {g : y --> z} (K K' : Kernel g) : z_iso K K' :=
    mk_z_iso (from_Kernel_to_Kernel K K') (from_Kernel_to_Kernel K' K)
             (are_inverses_from_Kernel_to_Kernel K K').

  (** Kernel of the ZeroArrow is given by identity *)
  Local Lemma KernelOfZeroArrow_isKernel (x y : C) :
    isKernel (identity x) (ZeroArrow Z x y) (id_left (ZeroArrow Z x y)).
  Proof.
    use mk_isKernel.
    intros w h H'.
    use unique_exists.
    - exact h.
    - cbn. apply id_right.
    - intros y0. apply hs.
    - intros y0 X. cbn in X. rewrite id_right in X. exact X.
  Qed.

  Definition KernelofZeroArrow (x y : C) : Kernel (@ZeroArrow C Z x y).
  Proof.
    use mk_Kernel.
    - exact x.
    - exact (identity x).
    - use id_left.
    - exact (KernelOfZeroArrow_isKernel x y).
  Defined.

  (** Kernel of identity is given by arrow from zero *)
  Local Lemma KernelOfIdentity_isKernel (x : C) :
    isKernel (ZeroArrowFrom x) (identity x)
             (ArrowsFromZero C Z x (ZeroArrowFrom x · identity x) (ZeroArrow Z Z x)).
  Proof.
    use mk_isKernel.
    intros w h H'.
    use unique_exists.
    - exact (ZeroArrowTo w).
    - cbn. rewrite id_right in H'. rewrite H'. apply idpath.
    - intros y. apply hs.
    - intros y X. cbn in X. use ArrowsToZero.
  Qed.

  Definition KernelOfIdentity (x : C) : Kernel (identity x).
  Proof.
    use mk_Kernel.
    - exact Z.
    - exact (ZeroArrowFrom x).
    - use ArrowsFromZero.
    - exact (KernelOfIdentity_isKernel x).
  Defined.

  (** More generally, the KernelArrow of the kernel of the ZeroArrow is an isomorphism. *)
  Lemma KernelofZeroArrow_is_iso {x y : C} (K : Kernel (ZeroArrow Z x y)) :
    is_inverse_in_precat (KernelArrow K) (from_Kernel_to_Kernel (KernelofZeroArrow x y) K).
  Proof.
    use mk_is_inverse_in_precat.
    - use KernelInsEq. rewrite <- assoc. unfold from_Kernel_to_Kernel. rewrite KernelCommutes.
      rewrite id_left. cbn. rewrite id_right. apply idpath.
    - unfold from_Kernel_to_Kernel. rewrite KernelCommutes. apply idpath.
  Qed.

  Definition KernelofZeroArrow_iso (x y : C) (K : Kernel (@ZeroArrow C Z x y)) : z_iso K x :=
    mk_z_iso (KernelArrow K) (from_Kernel_to_Kernel (KernelofZeroArrow x y) K)
             (KernelofZeroArrow_is_iso K).

  (** It follows that KernelArrow is monic. *)
  Lemma KernelArrowisMonic {y z : C} {g : y --> z} (K : Kernel g) : isMonic (KernelArrow K).
  Proof.
    apply mk_isMonic.
    intros z0 g0 h X.
    use KernelInsEq.
    exact X.
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


(** * Correspondence of kernels and equalizers *)
Section kernel_equalizers.

  Context {C : precategory}.
  Hypothesis hs : has_homsets C.
  Variable Z : Zero C.

  (** ** Equalizer from Kernel *)
  Lemma KernelEqualizer_eq {x y : ob C} {f : x --> y} (K : Kernel Z f) :
    KernelArrow K · f = KernelArrow K · ZeroArrow Z x y.
  Proof.
    rewrite ZeroArrow_comp_right. apply KernelCompZero.
  Qed.

  Lemma KernelEqualizer_isEqualizer {x y : ob C} {f : x --> y} (K : Kernel Z f) :
    isEqualizer f (ZeroArrow Z x y) (KernelArrow K) (KernelEqualizer_eq K).
  Proof.
    use mk_isEqualizer.
    intros w h H'.
    use unique_exists.
    - use KernelIn.
      + exact h.
      + rewrite ZeroArrow_comp_right in H'. exact H'.
    - cbn. use KernelCommutes.
    - intros y0. apply hs.
    - intros y0 X. use KernelInsEq. rewrite KernelCommutes. exact X.
  Qed.

  Definition KernelEqualizer {x y : ob C} {f : x --> y} (K : Kernel Z f) :
    Equalizer f (ZeroArrow Z _ _).
  Proof.
    use mk_Equalizer.
    - exact K.
    - exact (KernelArrow K).
    - exact (KernelEqualizer_eq K).
    - exact (KernelEqualizer_isEqualizer K).
  Defined.

  (** ** Kernel from Equalizer *)
  Lemma EqualizerKernel_eq {x y : ob C} {f : x --> y} (E : Equalizer f (ZeroArrow Z _ _)) :
    EqualizerArrow E · f = ZeroArrow Z E y.
  Proof.
    rewrite <- (ZeroArrow_comp_right _ _ _ _ _ (EqualizerArrow E)).
    exact (EqualizerEqAr E).
  Qed.

  Lemma EqualizerKernel_isKernel {x y : ob C} {f : x --> y} (E : Equalizer f (ZeroArrow Z _ _)) :
    isKernel Z (EqualizerArrow E) f (EqualizerKernel_eq E).
  Proof.
    use (mk_isKernel hs).
    intros w h H'.
    use unique_exists.
    - use EqualizerIn.
      + exact h.
      + rewrite ZeroArrow_comp_right. exact H'.
    - use EqualizerCommutes.
    - intros y0. apply hs.
    - intros y0 X. use EqualizerInsEq. rewrite EqualizerCommutes. exact X.
  Qed.

  Definition EqualizerKernel {x y : ob C} {f : x --> y} (E : Equalizer f (ZeroArrow Z _ _)) :
    Kernel Z f.
  Proof.
    use mk_Kernel.
    - exact E.
    - exact (EqualizerArrow E).
    - exact (EqualizerKernel_eq E).
    - exact (EqualizerKernel_isKernel E).
  Defined.

End kernel_equalizers.


(** * Kernel up to isomorphism *)
Section kernels_iso.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.

  Definition Kernel_up_to_iso_eq {x y z : C} (f : x --> y) (g : y --> z)
             (K : Kernel Z g) (h : z_iso x K) (H : f = h · (KernelArrow K)) :
    f · g = ZeroArrow Z x z.
  Proof.
    induction K as [t p]. induction t as [t' p']. induction p as [t'' p''].
    unfold isEqualizer in p''.
    rewrite H.
    rewrite <- (ZeroArrow_comp_right _ _ _ _ _ h).
    rewrite <- assoc.
    apply cancel_precomposition.
    apply KernelCompZero.
  Qed.

  Lemma Kernel_up_to_iso_isKernel {x y z : C} (f : x --> y) (g : y --> z) (K : Kernel Z g)
        (h : z_iso x K) (H : f = h · (KernelArrow K)) (H'' : f · g = ZeroArrow Z x z) :
    isKernel Z f g H''.
  Proof.
    use (mk_isKernel hs).
    intros w h0 H'.
    use unique_exists.
    - exact (KernelIn Z K w h0 H' · z_iso_inv_mor h).
    - cbn beta. rewrite H. rewrite assoc. rewrite <- (assoc _ _ h).
      cbn. rewrite (is_inverse_in_precat2 h). rewrite id_right.
      apply KernelCommutes.
    - intros y0. apply hs.
    - intros y0 X. cbn beta in X.
      use (post_comp_with_z_iso_is_inj h). rewrite <- assoc.
      use (pathscomp0 _ (! (maponpaths (λ gg : _, KernelIn Z K w h0 H' · gg)
                                       (is_inverse_in_precat2 h)))).
      rewrite id_right. use KernelInsEq. rewrite KernelCommutes. rewrite <- X.
      rewrite <- assoc. apply cancel_precomposition. apply pathsinv0.
      apply H.
  Qed.

  Definition Kernel_up_to_iso {x y z : C} (f : x --> y) (g : y --> z) (K : Kernel Z g)
             (h : z_iso x K) (H : f = h · (KernelArrow K)) : Kernel Z g :=
    mk_Kernel Z f _ (Kernel_up_to_iso_eq f g K h H)
              (Kernel_up_to_iso_isKernel f g K h H (Kernel_up_to_iso_eq f g K h H)).

  Lemma Kernel_up_to_iso2_eq {x y z : C} {f1 : x --> y} {f2 : x --> z} (h : z_iso y z)
        (H : f1 · h = f2) (K : Kernel Z f1) : KernelArrow K · f2 = ZeroArrow Z K z.
  Proof.
    rewrite <- H. rewrite assoc. rewrite KernelCompZero.
    apply ZeroArrow_comp_left.
  Qed.

  Definition Kernel_up_to_iso2_isKernel {x y z : C} (f1 : x --> y) (f2 : x --> z)
             (h : z_iso y z) (H : f1 · h = f2) (K : Kernel Z f1) :
    isKernel Z (KernelArrow K) f2 (Kernel_up_to_iso2_eq h H K).
  Proof.
    use (mk_isKernel hs).
    intros w h0 H'.
    use unique_exists.
    - use KernelIn.
      + exact h0.
      + rewrite <- H in H'. rewrite <- (ZeroArrow_comp_left _ _ _ _ _ h) in H'.
        rewrite assoc in H'. apply (post_comp_with_z_iso_is_inj h) in H'.
        exact H'.
    - cbn. use KernelCommutes.
    - intros y0. apply hs.
    - intros y0 H''. use KernelInsEq.
      rewrite H''. apply pathsinv0.
      apply KernelCommutes.
  Qed.

  Definition Kernel_up_to_iso2 {x y z : C} {f1 : x --> y} {f2 : x --> z} {h : z_iso y z}
             (H : f1 · h = f2) (K : Kernel Z f1) : Kernel Z f2 :=
    mk_Kernel Z (KernelArrow K) _ (Kernel_up_to_iso2_eq h H K)
              (Kernel_up_to_iso2_isKernel f1 f2 h H K).

End kernels_iso.


(** * Kernel of morphism · monic *)
(** ** Introduction
   Suppose f : x --> y is a morphism and M : y --> z is a Monic. Then kernel of f · M is
   isomorphic to kernel of f.
*)
Section kernels_monics.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.

  Local Lemma KernelCompMonic_eq1 {x y z : C} (f : x --> y) (M : Monic C y z)
        (K1 : Kernel Z (f · M)) (K2 : Kernel Z f) :
    KernelArrow K1 · f = ZeroArrow Z K1 y.
  Proof.
    use (MonicisMonic C M). rewrite ZeroArrow_comp_left. rewrite <- assoc. use KernelCompZero.
  Qed.

  Definition KernelCompMonic_mor1 {x y z : C} (f : x --> y) (M : Monic C y z)
        (K1 : Kernel Z (f · M)) (K2 : Kernel Z f) : C⟦K1, K2⟧ :=
    KernelIn Z K2 _ (KernelArrow K1) (KernelCompMonic_eq1 f M K1 K2).

  Local Lemma KernelCompMonic_eq2 {x y z : C} (f : x --> y) (M : Monic C y z)
        (K1 : Kernel Z (f · M)) (K2 : Kernel Z f) : KernelArrow K2 · (f · M) = ZeroArrow Z K2 z.
  Proof.
    rewrite assoc. rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Definition KernelCompMonic_mor2 {x y z : C} (f : x --> y) (M : Monic C y z)
             (K1 : Kernel Z (f · M)) (K2 : Kernel Z f) : C⟦K2, K1⟧ :=
    KernelIn Z K1 _ (KernelArrow K2) (KernelCompMonic_eq2 f M K1 K2).

  Lemma KernelCompMonic1 {x y z : C} (f : x --> y) (M : Monic C y z)
             (K1 : Kernel Z (f · M)) (K2 : Kernel Z f) :
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
             (K1 : Kernel Z (f · M)) (K2 : Kernel Z f) :
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
        (K : Kernel Z (f · M)) : KernelArrow K · f = ZeroArrow Z K y.
  Proof.
    use (MonicisMonic C M). rewrite ZeroArrow_comp_left. rewrite <- assoc. use KernelCompZero.
  Qed.

  Lemma KernelCompMonic_isKernel {x y z : C} (f : x --> y) (M : Monic C y z)
        (K : Kernel Z (f · M)) :
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

  Definition KernelCompMonic {x y z : C} (f : x --> y) (M : Monic C y z) (K : Kernel Z (f · M)) :
    Kernel Z f.
  Proof.
    use mk_Kernel.
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
    KernelArrow K · f' = ZeroArrow Z K y.
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
    use mk_Kernel.
    - exact K.
    - use KernelArrow.
    - exact (KernelPath_eq e K).
    - exact (KernelPath_isKernel e K).
  Defined.

End kernel_in_paths.


(** * Transports of kernels *)
Section transport_kernels.

  Variable C : precategory.
  Variable hs : has_homsets C.
  Variable Z : Zero C.

  Local Lemma transport_source_KernelIn_eq {x' x y z : C} (f : x --> y) {g : y --> z}
        (K : Kernel Z g) (e : x = x') (H : f · g = ZeroArrow Z _ _) :
    (transportf (λ x' : ob C, precategory_morphisms x' y) e f) · g = ZeroArrow Z _ _.
  Proof.
    induction e. apply H.
  Qed.

  Lemma transport_source_KernelIn {x' x y z : C} (f : x --> y) {g : y --> z} (K : Kernel Z g)
        (e : x = x') (H : f · g = ZeroArrow Z _ _) :
    transportf (λ x' : ob C, precategory_morphisms x' K) e (KernelIn Z K _ f H) =
    KernelIn Z K _ (transportf (λ x' : ob C, precategory_morphisms x' y) e f)
             (transport_source_KernelIn_eq f K e H).
  Proof.
    induction e. use KernelInsEq. cbn. unfold idfun.
    rewrite KernelCommutes. rewrite KernelCommutes.
    apply idpath.
  Qed.

End transport_kernels.
