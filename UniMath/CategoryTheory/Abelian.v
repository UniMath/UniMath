(** Definition of abelian categories. *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Section def_abelian.

  (** An abelian category has a zero object, binary (co)products, (co)kernels
    and every monic (resp. epi) is a kernel (resp. cokernel). *)
  Definition AbelianData1 (C : precategory) : UU :=
    Zero C × (BinProducts C) × (BinCoproducts C).

  Definition AbelianData2 (C : precategory) (AD1 : AbelianData1 C) : UU :=
    (Kernels (pr1 AD1)) × (Cokernels (pr1 AD1)).

  Definition isAbelianMonicKernels (C : precategory)
             (AD : AbelianData1 C) : UU :=
    Π (x y : C) (M : Monic C x y),
      (∃ (z : C) (f : y --> z) (H : M ;; f = M ;; (ZeroArrow C (pr1 AD) y z)),
          isEqualizer f (ZeroArrow C (pr1 AD) y z) M H).

  Definition isapropisAbelianMonicKernels (C : precategory)
             (AD1 : AbelianData1 C) :
    isaprop (isAbelianMonicKernels C AD1).
  Proof.
    apply impred_isaprop; intros x.
    apply impred_isaprop; intros y.
    apply impred_isaprop; intros M.
    apply isapropishinh.
  Qed.

  Definition isAbelianEpiCokernels (C : precategory)
             (AD : AbelianData1 C) : UU :=
    (Π (y z : C) (E : Epi C y z),
        (∃ (x : C) (f : x --> y) (H : f ;; E = (ZeroArrow C (pr1 AD) x y) ;; E),
            isCoequalizer f (ZeroArrow C (pr1 AD) x y) E H)).

  Definition isapropisAbelianEpiCokernels (C : precategory)
             (AD1 : AbelianData1 C) :
    isaprop (isAbelianEpiCokernels C AD1).
  Proof.
    apply impred_isaprop; intros x.
    apply impred_isaprop; intros y.
    apply impred_isaprop; intros M.
    apply isapropishinh.
  Qed.

  Definition isAbelian (C : precategory)
              (AD1 : AbelianData1 C) : UU :=
    (isAbelianMonicKernels C AD1) × (isAbelianEpiCokernels C AD1).

  Definition isapropisAbelian (C : precategory) (AD1 : AbelianData1 C) :
    isaprop (isAbelian C AD1).
  Proof.
    apply isapropdirprod.
    apply (isapropisAbelianMonicKernels C AD1).
    apply (isapropisAbelianEpiCokernels C AD1).
  Qed.

  Definition mk_isAbelian (C : precategory) (AD1 : AbelianData1 C)
              (MK : isAbelianMonicKernels C AD1)
              (EC : isAbelianEpiCokernels C AD1) :
    isAbelian C AD1 := (MK,,EC).

  (** Definition of abelian categories *)
  Definition Abelian : UU :=
    Σ A : (Σ C' : (Σ C : precategory, AbelianData1 C),
                  AbelianData2 (pr1 C') (pr2 C')),
          isAbelian (pr1 (pr1 A)) (pr2 (pr1 A)).
  Definition Abelian_precategory (A : Abelian) :
    precategory := pr1 (pr1 (pr1 A)).
  Coercion Abelian_precategory :
    Abelian >-> precategory.

  Definition mk_Abelian (C : precategory)
             (AD1 : AbelianData1 C) (AD2 : AbelianData2 C AD1)
             (H : isAbelian C AD1) :
    Abelian := tpair _ (tpair _ (tpair _ C AD1) AD2) H.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  (** Accessor functions. *)
  Definition Abelian_Zero :
    Zero A := pr1(pr2 (pr1 (pr1 A))).
  Definition Abelian_BinProducts :
    BinProducts A := pr1 (pr2 (pr2 (pr1 (pr1 A)))).
  Definition Abelian_BinCoproducts :
    BinCoproducts A := pr2 (pr2 (pr2 (pr1 (pr1 A)))).
  Definition Abelian_Kernels :
    Kernels Abelian_Zero := pr1 (pr2 (pr1 A)).
  Definition Abelian_Cokernels :
    Cokernels Abelian_Zero := pr2 (pr2 (pr1 A)).
  Definition Abelian_isAbelianMonicKernels
    : isAbelianMonicKernels A (pr2 (pr1 (pr1 A)))
    := pr1 (pr2 A).
  Definition Abelian_isAbelianEpiCokernels
    : isAbelianEpiCokernels A (pr2 (pr1 (pr1 A)))
    := pr2 (pr2 A).


  (** The following definitions construct a kernel from a monic and a cokernel
    from an epi. *)
  Definition Abelian_monic_kernel {x y : A} (M : Monic A x y) :
    ∃ (z : A) (f : y --> z), Kernel Abelian_Zero f.
  Proof.
    set (AMK := Abelian_isAbelianMonicKernels x y M).
    apply AMK. intros X. induction X. induction p. induction p.
    intros P Y. apply Y.
    refine (tpair _ t _). refine (tpair _ t0 _).

    use (mk_Kernel Abelian_Zero M). (* use the monic as the kernel. *)
    rewrite <- (ZeroArrow_comp_right A Abelian_Zero _ _ _ M).
    apply t1. apply p.
  Defined.

  Definition Abelian_epi_cokernel {y z : A} (E : Epi A y z) :
    ∃ (x : A) (f : x --> y), Cokernel Abelian_Zero f.
  Proof.
    set (AEC := Abelian_isAbelianEpiCokernels y z E).
    apply AEC. intros X. induction X. induction p. induction p.
    intros P Y. apply Y.
    refine (tpair _ t _). refine (tpair _ t0 _).

    use (mk_Cokernel Abelian_Zero E). (* use the epi as the cokernel. *)
    rewrite <- (ZeroArrow_comp_left A Abelian_Zero _ _ _ E).
    apply t1. apply p.
  Defined.
End def_abelian.

(** In abelian categories morphisms which are both monic and epi are
  isomorphisms. *)
Section abelian_monic_epi_iso.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  (** If a morphism if a monic and epi, then it is also iso *)
  Lemma Abelian_monic_epi_is_iso {x y : A} {f : x --> y} :
    isMonic A f -> isEpi A f -> is_iso f.
  Proof.
    intros M E.
    set (M1 := mk_Monic A f M).
    set (E1 := mk_Epi A f E).
    set (AMK := Abelian_isAbelianMonicKernels A x y M1).
    set (AEC := Abelian_isAbelianEpiCokernels A x y E1).
    cbn in *. unfold ishinh_UU in *.

    use (squash_to_prop AMK). apply isaprop_is_iso.
    intros X. induction X. induction p. induction p.
    use (squash_to_prop AEC). apply isaprop_is_iso.
    intros Y. induction Y. induction p0. induction p0.

    unfold isEqualizer in p. unfold isCoequalizer in p0.

    (* Here we construct the inverse of f *)
    apply (pr2 E1) in t1.
    set (p' := p y (identity _)).
    set (t'1 := maponpaths (fun h : A⟦y, t⟧ => identity _ ;; h) t1).
    cbn in t'1.
    set (p'' := p' t'1).
    induction p''. induction t5.

    use is_iso_qinv.

    (* The inverse of f. *)
    exact t5.

    (* It remains to show that this is the inverse of f *)
    split.
    apply (pr2 M1). cbn. rewrite <- assoc. rewrite p2.
    rewrite (remove_id_right A _ _ _ (identity x ;; f)).
    apply idpath. apply idpath. apply pathsinv0.
    apply id_left.

    apply p2.
  Defined.

  (** Construction of the iso. *)
  Lemma Abelian_monic_epi_iso {x y : A} {f : x --> y} :
    isMonic A f -> isEpi A f -> iso x y.
  Proof.
    intros iM iE.
    use isopair.
    apply f.
    apply (Abelian_monic_epi_is_iso iM iE).
  Defined.

End abelian_monic_epi_iso.


(** In the following section we prove that an abelian category has pullbacks of
    subobjects. *)
Section abelian_subobject_pullbacks.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  Lemma Abelian_subobjects_isPullback {x y z: A}
        (M1 : Monic A x z) (M2 : Monic A y z) :
    ∃ (a : A) (p1 : a --> x) (p2 : a --> y) (H : p1 ;; M1 = p2 ;; M2),
      isPullback M1 M2 p1 p2 H.
  Proof.
    set (ker1 := Abelian_monic_kernel A M1).
    set (ker2 := Abelian_monic_kernel A M2).
    (* These kernels are constructed in Abelian_monic_kernel in a way that M1
       and M2 are the kernel arrows. But the construction of the kernels is
       forgotten when I apply these. I need coq to remember this construction.
       How do I do it? *)
    unfold Abelian_monic_kernel in ker1. (* Here M1 is shown in the
                                            construction *)
    apply ker1. (* Here the reference to M1 is lost. *)
  Abort.

  Lemma Abelian_quotobject_pushout {x y z: A}
        (E1 : Epi A x y) (E2 : Epi A x z) :
    ∃ (a : A) (i1 : y --> a) (i2 : z --> a) (H : E1 ;; i1 = E2 ;; i2),
      isPushout E1 E2 i1 i2 H.
  Proof.
    (* TODO *)
  Abort.

End abelian_subobject_pullbacks.

(** In the following section we show that equalizers and coequalizers exist in
  abelian categories.  *)
Section abelian_equalizers.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  Lemma Abelian_equalizers {x y : A} (f1 f2 : x --> y) :
    Equalizer f1 f2.
  Proof.
    (* TODO *) (* Needs pullbacks *)
  Abort.

  Lemma Abelian_coequalizer {x y : A} (f1 f2 : x --> y) :
    Coequalizer f1 f2.
  Proof.
    (* TODO *) (* Needs pushouts *)
  Abort.

End abelian_equalizers.

(** In this section we prove that every morphism factors as epi ;; monic *)
Section abelian_factorization.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  (* TODO: Needs some results on pullbacks, equalizers, and strong
     epimorphisms. *)
  Lemma Abelian_factorization {x y z : A} (f : x --> y) :
    ∃ (E : Epi A x z) (M : Monic A z y), f = E ;; M.
  Proof.
    (* TODO *)
  Abort.
End abelian_factorization.

(** In this section we prove that kernels of monomorphisms are given by the
  arrows from zero and cokernels of epimorphisms are given by the arrows to
  zero. *)
Section abelian_monic_kernels.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  (* A kernel of a monic is the arrow from zero. *)
  Definition Abelian_MonicKernelZero {x y : A} (M : Monic A x y) :
    Kernel (Abelian_Zero A) M.
  Proof.
    use mk_Kernel.
    exact (Abelian_Zero A).
    exact (ZeroArrowFrom _).
    apply (ArrowsFromZero).
    use (mk_isEqualizer).
    intros w h X.

    (* Transform X into an equality we need *)
    rewrite ZeroArrow_comp_right in X.
    rewrite <- (ZeroArrow_comp_left _ _ _ x y M) in X.
    apply (pr2 M) in X.

    use unique_exists.
    apply ZeroArrowTo.
    cbn. rewrite X. unfold ZeroArrow. apply idpath.

    intros y0. apply hs.

    intros y0 Y. cbn in Y. apply ArrowsToZero.
  Defined.


  (* A cokernel of an epi is the arrow to zero. *)
  Definition Abelian_EpiCokernelZero {y z : A} (E : Epi A y z) :
    Cokernel (Abelian_Zero A) E.
  Proof.
    use mk_Cokernel.
    exact (Abelian_Zero A).
    exact (ZeroArrowTo _).
    apply (ArrowsToZero).
    use (mk_isCoequalizer).
    intros w h X.

    (* Transform X into an equality we need *)
    rewrite ZeroArrow_comp_left in X.
    rewrite <- (ZeroArrow_comp_right A (Abelian_Zero A) y z w E) in X.
    apply (pr2 E) in X.

    use unique_exists.
    apply ZeroArrowFrom.
    cbn. rewrite X. unfold ZeroArrow. apply idpath.

    intros y0. apply hs.

    intros y0 Y. cbn in Y. apply ArrowsFromZero.
  Defined.
End abelian_monic_kernels.


(** In this section we prove that every monic is the kernel of its cokernel and
  every epi is the cokernel of its kernel. *)
Section abelian_kernel_cokernel.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.


  (** The following definition constructs kernels from monics. *)
  Definition Abelian_MonicToKerneEq {x y : A} (M : Monic A x y) :
    M ;; CokernelArrow (Abelian_Zero A) (Abelian_Cokernels A x y M) =
    ZeroArrow A (Abelian_Zero A) x (Abelian_Cokernels A x y M).
  Proof.
    set (AMK := Abelian_isAbelianMonicKernels A x y M).
    unfold ishinh in AMK. cbn in *. unfold ishinh_UU in AMK.
    unfold isEqualizer in AMK.
    use (squash_to_prop AMK). apply hs.
    intros X.
    apply (CokernelCompZero (Abelian_Zero A) (Abelian_Cokernels A x y M)).
  Qed.

  Definition Abelian_MonicToKernel {x y : A} (M : Monic A x y) :
    Kernel (Abelian_Zero A) (CokernelArrow _ (Abelian_Cokernels A x y M)).
  Proof.
    set (AMK := Abelian_isAbelianMonicKernels A x y M).
    unfold ishinh in AMK. cbn in *. unfold ishinh_UU in AMK.

    use (mk_Kernel _ M). use (squash_to_prop AMK). apply hs.

    intros X. apply (Abelian_MonicToKerneEq M).
    use (squash_to_prop AMK). apply isaprop_isEqualizer.
    intros X. induction X. induction p. induction p. unfold isEqualizer in p.
    use mk_isEqualizer. intros w h X.

    apply p.
    (* Need the factorization result of morphisms in abelian categories to
       prove this *)
  Abort.

  (** The following definition constructs cokernels from epis. *)
  Definition Abelian_EpiToCokernelEq {y z : A} (E : Epi A y z) :
    KernelArrow (Abelian_Zero A) (Abelian_Kernels A y z E) ;; E =
    ZeroArrow A (Abelian_Zero A) (Abelian_Kernels A y z E) z.
  Proof.
    set (AEC := Abelian_isAbelianEpiCokernels A y z E).
    unfold ishinh in AEC. cbn in *. unfold ishinh_UU in AEC.
    unfold isCoequalizer in AEC.
    use (squash_to_prop AEC). apply hs.
    intros X.
    apply (KernelCompZero (Abelian_Zero A) (Abelian_Kernels A y z E)).
  Qed.

  Definition Abelian_EpiToCokernel {y z : A} (E : Epi A y z) :
    Cokernel (Abelian_Zero A) (KernelArrow _ (Abelian_Kernels _ _ _ E)).
  Proof.
    set (AEC := Abelian_isAbelianEpiCokernels A y z E).
    unfold ishinh in AEC. cbn in *. unfold ishinh_UU in AEC.

    use (mk_Cokernel _ E). use (squash_to_prop AEC). apply hs.

    intros X. apply (Abelian_EpiToCokernelEq E).
    use (squash_to_prop AEC). apply isaprop_isCoequalizer.
    intros X. induction X. induction p. induction p.

    use mk_isCoequalizer. intros w0 h X.
    (* Need the factorization result of morphisms in abelian categories to
       prove this. *)
  Abort.

End abelian_kernel_cokernel.
