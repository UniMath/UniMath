(** * Abelian categories *)
(** ** Contents
- Definition of Abelian categories
- If Monic and Epi, then iso
- Pushouts of subobjects and pullbacks of quotient objects
 - Pushouts of subobjects
 - Pullbacks of quotient objects
- Equalizers and Coequalizers
 - Equalizers
 - Coequalizers
- Pullbacks and Pushouts
- Results on Monics and Epis
 - Monic implies Zero kernel
 - Epi implies Zero cokernel
 - Zero kernel implies Monic
 - Zero cokernel implies Epi
- Factorization of morphisms
 - CoIm to Im factorization
 - Epi ;; Monic factorization
- Results on Kernels and Cokernels
 - Monic are Kernels of their Cokernels
 - Epis are Cokernels of their Kernels
*)
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


(** * Definition of Abelian categories *)
Section def_abelian.

  (** An abelian category has a zero object, binary (co)products, (co)kernels
    and every monic (resp. epi) is a kernel (resp. cokernel). *)
  Definition AbelianData1 (C : precategory) : UU :=
    Zero C × (BinProducts C) × (BinCoproducts C).

  Definition AbelianData2 (C : precategory) (AD1 : AbelianData1 C) : UU :=
    (Kernels (pr1 AD1)) × (Cokernels (pr1 AD1)).

  (** This definition contains the data that every monic is a kernel of some
    morphism. *)
  Definition AbelianMonicKernelsData (C : precategory)
             (AD : AbelianData1 C) : UU :=
    Π (x y : C) (M : Monic C x y),
    (Σ D2 : (Σ D1 : (Σ z : C, y --> z),
                    M ;; (pr2 D1) = M ;; (ZeroArrow C (pr1 AD) y (pr1 D1))),
            isEqualizer (pr2 (pr1 D2)) (ZeroArrow C (pr1 AD) y (pr1 (pr1 D2)))
                        M (pr2 D2)).

  (** Accessor functions for AbelianMonicKernelsData. *)
  Definition AMKD_Ob {C : precategory} {AD : AbelianData1 C}
             (AMKD : AbelianMonicKernelsData C AD) (x y : C)
             (M : Monic C x y) : C := pr1 (pr1 (pr1 (AMKD x y M))).
  Definition AMKD_Mor {C : precategory} {AD : AbelianData1 C}
             (AMKD : AbelianMonicKernelsData C AD) (x y : C)
             (M : Monic C x y) :
    C⟦y, (AMKD_Ob AMKD x y M)⟧ := pr2 (pr1 (pr1 (AMKD x y M))).
  Definition AMKD_Eq {C : precategory} {AD : AbelianData1 C}
             (AMKD : AbelianMonicKernelsData C AD) (x y : C)
             (M : Monic C x y) :
    M ;; (AMKD_Mor AMKD x y M)
    = M ;; (ZeroArrow C (pr1 AD) y (AMKD_Ob AMKD x y M))
    := pr2 (pr1 (AMKD x y M)).
  Definition AMKD_isE {C : precategory} {AD : AbelianData1 C}
             (AMKD : AbelianMonicKernelsData C AD) (x y : C)
             (M : Monic C x y) :
    isEqualizer (AMKD_Mor AMKD x y M)
                (ZeroArrow C (pr1 AD) y (AMKD_Ob AMKD x y M))
                M (AMKD_Eq AMKD x y M)
    := pr2 (AMKD x y M).

  (** This definition contains the data that every epi is a cokernel of some
    morphism. *)
  Definition AbelianEpiCokernelsData (C : precategory)
             (AD : AbelianData1 C) : UU :=
    (Π (y z : C) (E : Epi C y z),
     (Σ D2 : (Σ D1 : (Σ x : C, x --> y),
                     (pr2 D1) ;; E = (ZeroArrow C (pr1 AD) (pr1 D1) y) ;; E),
             isCoequalizer (pr2 (pr1 D2))
                           (ZeroArrow C (pr1 AD) (pr1 (pr1 D2)) y)
                           E (pr2 D2))).

  (** Accessor functions for AbelianEpiCokernelsData. *)
  Definition AECD_Ob {C : precategory} {AD : AbelianData1 C}
             (AECD : AbelianEpiCokernelsData C AD) (y z : C)
             (E : Epi C y z) : C := pr1 (pr1 (pr1 (AECD y z E))).
  Definition AECD_Mor {C : precategory} {AD : AbelianData1 C}
             (AECD : AbelianEpiCokernelsData C AD) (y z : C)
             (E : Epi C y z) :
    C⟦(AECD_Ob AECD y z E), y⟧ := pr2 (pr1 (pr1 (AECD y z E))).
  Definition AECD_Eq {C : precategory} {AD : AbelianData1 C}
             (AECD : AbelianEpiCokernelsData C AD) (y z : C)
             (E : Epi C y z) :
    (AECD_Mor AECD y z E) ;; E
    = (ZeroArrow C (pr1 AD) (AECD_Ob AECD y z E) y) ;; E
    := pr2 (pr1 (AECD y z E)).
  Definition AECD_isC {C : precategory} {AD : AbelianData1 C}
             (AECD : AbelianEpiCokernelsData C AD) (y z : C)
             (E : Epi C y z) :
    isCoequalizer (AECD_Mor AECD y z E)
                  (ZeroArrow C (pr1 AD) (AECD_Ob AECD y z E) y)
                  E (AECD_Eq AECD y z E)
    := pr2 (AECD y z E).

  (** Data which contains kernels, cokernels, the data that monics are kernels
    of some morphisms, and the data that epis are cokernels of some
    morphisms. *)
  Definition AbelianData (C : precategory) (AD1 : AbelianData1 C) : UU :=
    (AbelianData2 C AD1)
      × (AbelianMonicKernelsData C AD1)
      × (AbelianEpiCokernelsData C AD1).

  (** Definition of abelian categories. *)
  Definition Abelian_precategory : UU :=
    Σ A : (Σ C : precategory, AbelianData1 C), AbelianData (pr1 A) (pr2 A).
  Definition precategory_of_Abelian_precategory (A : Abelian_precategory) :
    precategory := pr1 (pr1 A).
  Coercion precategory_of_Abelian_precategory :
    Abelian_precategory >-> precategory.

  Definition mk_Abelian (C : precategory) (AD1 : AbelianData1 C)
             (AD : AbelianData C AD1) :
    Abelian_precategory := tpair _ (tpair _ C AD1) AD.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  (** Accessor functions Abelian. *)
  Definition Abelian_Zero :
    Zero A := pr1 (pr2 (pr1 A)).
  Definition Abelian_BinProducts :
    BinProducts A := pr1 (pr2 (pr2 (pr1 A))).
  Definition Abelian_BinCoproducts :
    BinCoproducts A := pr2 (pr2 (pr2 (pr1 A))).
  Definition Abelian_AbelianData1 :
    AbelianData1 A := (pr2 (pr1 A)).
  Definition Abelian_Kernels :
    Kernels Abelian_Zero := pr1 (pr1 (pr2 A)).
  Definition Abelian_Cokernels :
    Cokernels Abelian_Zero := pr2 (pr1 (pr2 A)).
  Definition Abelian_AMKD
    : AbelianMonicKernelsData A (pr2 (pr1 A))
    := pr1 (pr2 (pr2 A)).
  Definition Abelian_AECD
    : AbelianEpiCokernelsData A (pr2 (pr1 A))
    := pr2 (pr2 (pr2 A)).


  (** Hide the following equations behind Qed. *)
  Definition Abelian_monic_kernel_eq {x y : A} (M : Monic A x y) :
    M ;; AMKD_Mor Abelian_AMKD x y M
    = ZeroArrow A Abelian_Zero x (AMKD_Ob Abelian_AMKD x y M).
  Proof.
    rewrite (AMKD_Eq Abelian_AMKD x y M).
    apply ZeroArrow_comp_right.
  Qed.

  Definition Abelian_epi_cokernel_eq {y z : A} (E : Epi A y z) :
    AECD_Mor Abelian_AECD y z E ;; E
    = ZeroArrow A Abelian_Zero (AECD_Ob Abelian_AECD y z E) z.
  Proof.
    rewrite (AECD_Eq Abelian_AECD y z E).
    apply ZeroArrow_comp_left.
  Qed.

  (** The following definitions construct a kernel from a monic and a cokernel
    from an epi. *)
  Definition Abelian_monic_kernel {x y : A} (M : Monic A x y) :
    Kernel Abelian_Zero (AMKD_Mor Abelian_AMKD x y M)
    := mk_Kernel
         Abelian_Zero
         M
         (AMKD_Mor Abelian_AMKD x y M)
         (Abelian_monic_kernel_eq M)
         (AMKD_isE Abelian_AMKD x y M).

  Definition Abelian_epi_cokernel {y z : A} (E : Epi A y z) :
    Cokernel Abelian_Zero (AECD_Mor Abelian_AECD y z E)
    := mk_Cokernel
         Abelian_Zero
         E
         (AECD_Mor Abelian_AECD y z E)
         (Abelian_epi_cokernel_eq E)
         (AECD_isC Abelian_AECD y z E).

  (** The following lemmas verify that the kernel and cokernel arrows are indeed
    the monic M and the epi E. *)
  Lemma Abelian_monic_kernel_arrow_eq {x y : A} (M : Monic A x y) :
    KernelArrow Abelian_Zero (Abelian_monic_kernel M) = M.
  Proof.
    apply idpath.
  Qed.

  Lemma Abelian_epi_cokernel_arrow_eq {x y : A} (E : Epi A x y) :
    CokernelArrow Abelian_Zero (Abelian_epi_cokernel E) = E.
  Proof.
    apply idpath.
  Qed.
End def_abelian.

(** * If Monic and Epi, then iso
  In abelian categories morphisms which are both monic and epi are
  isomorphisms. *)
Section abelian_monic_epi_iso.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  (** If a morphism is a monic and an epi, then it is also an iso. *)
  Lemma Abelian_monic_epi_is_iso {x y : A} {f : x --> y} :
    isMonic A f -> isEpi A f -> is_iso f.
  Proof.
    intros M E.
    set (M1 := mk_Monic A f M).
    set (E1 := mk_Epi A f E).
    set (AMK := Abelian_AMKD A x y M1).
    set (AEC := Abelian_AECD A x y E1).

    induction AMK as [t p]. induction t as [t p0]. induction t as [t p1].
    induction AEC as [t0 p2]. induction t0 as [t0 p3]. induction t0 as [t0 p4].

    unfold isEqualizer in p. unfold isCoequalizer in p2.

    (* Here we construct the inverse of f *)
    cbn in *. apply E in p0.
    set (p' := p y (identity _)).
    set (t'1 := maponpaths (fun h : A⟦y, t⟧ => identity _ ;; h) p0).
    cbn in t'1.
    set (p'' := p' t'1).
    induction p'' as [t1 p5]. induction t1 as [t1 p6].

    use is_iso_qinv.

    (* The inverse of f *)
    exact t1.

    (* It remains to show that this is the inverse of f *)
    split.
    apply (pr2 M1). cbn. rewrite <- assoc. rewrite p6.
    rewrite (remove_id_right A _ _ _ (identity x ;; f)).
    apply idpath. apply idpath. apply pathsinv0.
    apply id_left.

    apply p6.
  Qed.

  (** Construction of the iso. *)
  Lemma Abelian_monic_epi_iso {x y : A} {f : x --> y} :
    isMonic A f -> isEpi A f -> iso x y.
  Proof.
    intros iM iE.
    exact (isopair f (Abelian_monic_epi_is_iso iM iE)).
  Defined.

End abelian_monic_epi_iso.


(** * Pullbacks of subjects and pushouts of quotient objects
  In the following section we prove that an abelian category has pullbacks of
  subobjects and pushouts of quotient objects. *)
Section abelian_subobject_pullbacks.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  (** ** Pullbacks of subobjects *)

  (** Equations we are going to need to construct a Pullback. *)
  Definition Abelian_subobjects_Pullback_eq1 {x y z : A}
             (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (AMKD_Ob (Abelian_AMKD A) x z M1)
                                       (AMKD_Ob (Abelian_AMKD A) y z M2))
             (ker : Kernel (Abelian_Zero A)
                           (BinProductArrow
                              A BinProd
                              (AMKD_Mor (Abelian_AMKD A) x z M1)
                              (AMKD_Mor (Abelian_AMKD A) y z M2))) :
    KernelArrow (Abelian_Zero A) ker ;; AMKD_Mor (Abelian_AMKD A) x z M1 =
    ZeroArrow A (Abelian_Zero A) ker (AMKD_Ob (Abelian_AMKD A) x z M1).
  Proof.
    set (tmp := (BinProductPr1Commutes A _ _ BinProd _
                                       (AMKD_Mor (Abelian_AMKD A) x z M1)
                                       (AMKD_Mor (Abelian_AMKD A) y z M2))).
    apply (maponpaths (fun h : _ => KernelArrow (Abelian_Zero A) ker ;; h))
      in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite assoc. rewrite (KernelCompZero (Abelian_Zero A) ker).
    apply ZeroArrow_comp_left.
  Qed.

  Definition Abelian_subobjects_Pullback_eq2 {x y z : A}
             (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (AMKD_Ob (Abelian_AMKD A) x z M1)
                                       (AMKD_Ob (Abelian_AMKD A) y z M2))
             (ker : Kernel (Abelian_Zero A)
                           (BinProductArrow
                              A BinProd
                              (AMKD_Mor (Abelian_AMKD A) x z M1)
                              (AMKD_Mor (Abelian_AMKD A) y z M2))) :
    KernelArrow (Abelian_Zero A) ker ;; AMKD_Mor (Abelian_AMKD A) y z M2 =
    ZeroArrow A (Abelian_Zero A) ker (AMKD_Ob (Abelian_AMKD A) y z M2).
  Proof.
    set (tmp := (BinProductPr2Commutes A _ _ BinProd _
                                       (AMKD_Mor (Abelian_AMKD A) x z M1)
                                       (AMKD_Mor (Abelian_AMKD A) y z M2))).
    apply (maponpaths (fun h : _ => KernelArrow (Abelian_Zero A) ker ;; h))
      in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite assoc. rewrite (KernelCompZero (Abelian_Zero A) ker).
    apply ZeroArrow_comp_left.
  Qed.

  Definition Abelian_subobjects_Pullback_eq3 {x y z : A}
             (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (AMKD_Ob (Abelian_AMKD A) x z M1)
                                       (AMKD_Ob (Abelian_AMKD A) y z M2))
             (ker : Kernel (Abelian_Zero A)
                           (BinProductArrow
                              A BinProd
                              (AMKD_Mor (Abelian_AMKD A) x z M1)
                              (AMKD_Mor (Abelian_AMKD A) y z M2))) :
    KernelIn (Abelian_Zero A) (Abelian_monic_kernel A M1) ker
             (KernelArrow (Abelian_Zero A) ker)
             (Abelian_subobjects_Pullback_eq1 M1 M2 BinProd ker)
           ;; M1 =
    KernelIn (Abelian_Zero A) (Abelian_monic_kernel A M2) ker
             (KernelArrow (Abelian_Zero A) ker)
             (Abelian_subobjects_Pullback_eq2 M1 M2 BinProd ker)
             ;; M2.
  Proof.
    rewrite (KernelCommutes (Abelian_Zero A) (Abelian_monic_kernel A M1) _
                            (KernelArrow (Abelian_Zero A) ker)).
    rewrite (KernelCommutes (Abelian_Zero A) (Abelian_monic_kernel A M2) _
                            (KernelArrow (Abelian_Zero A) ker)).
    apply idpath.
  Qed.

  Definition Abelian_subobjects_Pullback_isPullback {x y z : A}
             (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (AMKD_Ob (Abelian_AMKD A) x z M1)
                                       (AMKD_Ob (Abelian_AMKD A) y z M2))
             (ker : Kernel (Abelian_Zero A)
                           (BinProductArrow
                              A BinProd
                              (AMKD_Mor (Abelian_AMKD A) x z M1)
                              (AMKD_Mor (Abelian_AMKD A) y z M2))) :
    isPullback M1 M2
               (KernelIn (Abelian_Zero A) (Abelian_monic_kernel A M1) ker
                         (KernelArrow (Abelian_Zero A) ker)
                         (Abelian_subobjects_Pullback_eq1 M1 M2 BinProd ker))
               (KernelIn (Abelian_Zero A) (Abelian_monic_kernel A M2) ker
                         (KernelArrow (Abelian_Zero A) ker)
                         (Abelian_subobjects_Pullback_eq2 M1 M2 BinProd ker))
               (Abelian_subobjects_Pullback_eq3 M1 M2 BinProd ker).
  Proof.
    (* variables *)
    set (ker1 := Abelian_monic_kernel A M1).
    set (ker2 := Abelian_monic_kernel A M2).
    set (ar := BinProductArrow
                 A BinProd
                 (AMKD_Mor (Abelian_AMKD A) x z M1)
                 (AMKD_Mor (Abelian_AMKD A) y z M2)).

    assert (com1 : KernelIn (Abelian_Zero A) ker1 ker
                            (KernelArrow (Abelian_Zero A) ker)
                            (Abelian_subobjects_Pullback_eq1 M1 M2 BinProd ker)
                            ;; M1
                   = KernelArrow (Abelian_Zero A) ker).
    {
      apply (KernelCommutes (Abelian_Zero A) ker1 _
                            (KernelArrow (Abelian_Zero A) ker)).
    }

    assert (com2 : KernelIn (Abelian_Zero A) ker2 ker
                            (KernelArrow (Abelian_Zero A) ker)
                            (Abelian_subobjects_Pullback_eq2 M1 M2 BinProd ker)
                            ;; M2
                   = KernelArrow (Abelian_Zero A) ker).
    {
      apply (KernelCommutes (Abelian_Zero A) ker2 _
                            (KernelArrow (Abelian_Zero A) ker)).
    }

    (* isPullback *)
    use mk_isPullback.
    intros e h k H.

    (* First we show that h ;; M1 ;; ar = ZeroArrow by uniqueness of the
       morphism to product. *)
    assert (e1 : h ;; (KernelArrow (Abelian_Zero A) ker1) ;;
                   (AMKD_Mor (Abelian_AMKD A) x z M1)
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      rewrite <- assoc.
      set (ee1 := KernelCompZero (Abelian_Zero A) ker1). cbn in ee1. cbn.
      rewrite ee1.
      apply ZeroArrow_comp_right.
    }

    assert (e2 : k ;; (KernelArrow (Abelian_Zero A) ker2) ;;
                   (AMKD_Mor (Abelian_AMKD A) y z M2)
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      rewrite <- assoc.
      set (ee2 := KernelCompZero (Abelian_Zero A) ker2). cbn in ee2. cbn.
      rewrite ee2.
      apply ZeroArrow_comp_right.
    }

    cbn in e1, e2.

    assert (e'1 : h ;; M1 ;; (AMKD_Mor (Abelian_AMKD A) y z M2)
                  = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      rewrite H. apply e2.
    }

    assert (e''1 : h ;; M1 ;; ar = ZeroArrow A (Abelian_Zero A) _ _).
    {
      rewrite (BinProductArrowEta A _ _ BinProd e (h ;; M1 ;; ar)).
      use BinProductArrowZero. rewrite <- assoc.
      set (tmp1 := BinProductPr1Commutes A _ _ BinProd _
                                         (AMKD_Mor (Abelian_AMKD A) x z M1)
                                         (AMKD_Mor (Abelian_AMKD A) y z M2)).
      fold ar in tmp1. rewrite tmp1.
      apply e1.

      rewrite <- assoc.
      set (tmp1 := BinProductPr2Commutes A _ _ BinProd _
                                         (AMKD_Mor (Abelian_AMKD A) x z M1)
                                         (AMKD_Mor (Abelian_AMKD A) y z M2)).
      fold ar in tmp1. rewrite tmp1. apply e'1.
    }

    use unique_exists.
    use (KernelIn (Abelian_Zero A) ker e (h ;; M1)).
    apply e''1.
    split.

    use (KernelInsEq (Abelian_Zero A) ker1).
    cbn. rewrite <- assoc.
    set (com'1 := (maponpaths (fun f : _ => KernelIn (Abelian_Zero A)
                                                  ker e (h ;; M1) e''1 ;; f)
                              com1)). cbn in com'1.
    use (pathscomp0 com'1).
    use KernelCommutes.

    use (KernelInsEq (Abelian_Zero A) ker2).
    cbn. rewrite <- assoc.
    set (com'2 := (maponpaths (fun f : _ => KernelIn (Abelian_Zero A)
                                                  ker e (h ;; M1) e''1 ;; f)
                              com2)). cbn in com'2.
    use (pathscomp0 com'2). rewrite <- H.
    use KernelCommutes.

    (* Equality on equalities of morphisms *)
    intros y0. apply isapropdirprod. apply hs. apply hs.

    (* Uniqueness *)
    intros y0 t. cbn in t. induction t as [t p].
    apply (KernelArrowisMonic (Abelian_Zero A) ker).
    rewrite (KernelCommutes (Abelian_Zero A) ker).
    rewrite <- (KernelCommutes (Abelian_Zero A) ker1 ker
                              (KernelArrow (Abelian_Zero A) ker)
                              (Abelian_subobjects_Pullback_eq1 M1 M2 BinProd
                                                               ker)).
    rewrite assoc.
    use (pathscomp0 (maponpaths (fun f : _ => f ;; KernelArrow (Abelian_Zero A)
                                             ker1) t)).
    apply idpath.
  Qed.

  (** Construction of the Pullback of subobjects. *)
  Definition Abelian_subobjects_Pullback {x y z : A}
        (M1 : Monic A x z) (M2 : Monic A y z) :
    Pullback M1 M2.
  Proof.
    (* variables *)
    set (ker1 := Abelian_monic_kernel A M1).
    set (ker2 := Abelian_monic_kernel A M2).
    set (BinProd := Abelian_BinProducts
                      A
                      (AMKD_Ob (Abelian_AMKD A) x z M1)
                      (AMKD_Ob (Abelian_AMKD A) y z M2)).
    set (ar := BinProductArrow
                 A BinProd
                 (AMKD_Mor (Abelian_AMKD A) x z M1)
                 (AMKD_Mor (Abelian_AMKD A) y z M2)).
    set (ker := Abelian_Kernels A _ _ ar).

    (* Construction *)
    use (mk_Pullback
           M1 M2 ker
           (KernelIn (Abelian_Zero A) ker1 ker (KernelArrow (Abelian_Zero A)
                                                            ker)
                     (Abelian_subobjects_Pullback_eq1 M1 M2 BinProd ker))
           (KernelIn (Abelian_Zero A) ker2 ker (KernelArrow (Abelian_Zero A)
                                                            ker)
                     (Abelian_subobjects_Pullback_eq2 M1 M2 BinProd ker))
           (Abelian_subobjects_Pullback_eq3 M1 M2 BinProd ker)
           (Abelian_subobjects_Pullback_isPullback M1 M2 BinProd ker)).
  Defined.


  (** ** Pushouts of quotient objects *)


  (** Equations we are going to need to construct a pushout. *)
  Definition Abelian_quotobjects_Pushout_eq1 {x y z : A}
             (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone
                            A (AECD_Ob (Abelian_AECD A) x y E1)
                            (AECD_Ob (Abelian_AECD A) x z E2))
             (coker : Cokernel (Abelian_Zero A)
                               (BinCoproductArrow
                                  A BinCoprod
                                  (AECD_Mor (Abelian_AECD A) x y E1)
                                  (AECD_Mor (Abelian_AECD A) x z E2))) :
    AECD_Mor (Abelian_AECD A) x y E1 ;; CokernelArrow (Abelian_Zero A) coker =
       ZeroArrow A (Abelian_Zero A) (AECD_Ob (Abelian_AECD A) x y E1) coker.
  Proof.
    set (tmp := (BinCoproductIn1Commutes A _ _ BinCoprod _
                                         (AECD_Mor (Abelian_AECD A) x y E1)
                                         (AECD_Mor (Abelian_AECD A) x z E2))).
    apply (maponpaths (fun h : _ => h ;; CokernelArrow (Abelian_Zero A) coker))
      in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite <- assoc. rewrite (CokernelCompZero (Abelian_Zero A) coker).
    apply ZeroArrow_comp_right.
  Qed.

  Definition Abelian_quotobjects_Pushout_eq2 {x y z : A}
             (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone
                            A (AECD_Ob (Abelian_AECD A) x y E1)
                            (AECD_Ob (Abelian_AECD A) x z E2))
             (coker : Cokernel (Abelian_Zero A)
                               (BinCoproductArrow
                                  A BinCoprod
                                  (AECD_Mor (Abelian_AECD A) x y E1)
                                  (AECD_Mor (Abelian_AECD A) x z E2))) :
    AECD_Mor (Abelian_AECD A) x z E2 ;; CokernelArrow (Abelian_Zero A) coker =
       ZeroArrow A (Abelian_Zero A) (AECD_Ob (Abelian_AECD A) x z E2) coker.
  Proof.
    set (tmp := (BinCoproductIn2Commutes A _ _ BinCoprod _
                                         (AECD_Mor (Abelian_AECD A) x y E1)
                                         (AECD_Mor (Abelian_AECD A) x z E2))).
    apply (maponpaths (fun h : _ => h ;; CokernelArrow (Abelian_Zero A) coker))
      in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite <- assoc. rewrite (CokernelCompZero (Abelian_Zero A) coker).
    apply ZeroArrow_comp_right.
  Qed.

  Definition Abelian_quotobjects_Pushout_eq3 {x y z : A}
             (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone
                            A (AECD_Ob (Abelian_AECD A) x y E1)
                            (AECD_Ob (Abelian_AECD A) x z E2))
             (coker : Cokernel (Abelian_Zero A)
                               (BinCoproductArrow
                                  A BinCoprod
                                  (AECD_Mor (Abelian_AECD A) x y E1)
                                  (AECD_Mor (Abelian_AECD A) x z E2))) :
    E1 ;; CokernelOut (Abelian_Zero A) (Abelian_epi_cokernel A E1) coker
       (CokernelArrow (Abelian_Zero A) coker)
       (Abelian_quotobjects_Pushout_eq1 E1 E2 BinCoprod coker) =
    E2 ;; CokernelOut (Abelian_Zero A) (Abelian_epi_cokernel A E2) coker
       (CokernelArrow (Abelian_Zero A) coker)
       (Abelian_quotobjects_Pushout_eq2 E1 E2 BinCoprod coker).
  Proof.
    rewrite (CokernelCommutes (Abelian_Zero A) (Abelian_epi_cokernel A E1) _
                              (CokernelArrow (Abelian_Zero A) coker)).
    rewrite (CokernelCommutes (Abelian_Zero A) (Abelian_epi_cokernel A E2) _
                              (CokernelArrow (Abelian_Zero A) coker)).
    apply idpath.
  Qed.

  Definition Abelian_quotobjects_Pushout_isPushout {x y z : A}
             (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone
                            A (AECD_Ob (Abelian_AECD A) x y E1)
                            (AECD_Ob (Abelian_AECD A) x z E2))
             (coker : Cokernel (Abelian_Zero A)
                               (BinCoproductArrow
                                  A BinCoprod
                                  (AECD_Mor (Abelian_AECD A) x y E1)
                                  (AECD_Mor (Abelian_AECD A) x z E2))) :
    isPushout E1 E2
              (CokernelOut (Abelian_Zero A) (Abelian_epi_cokernel A E1) coker
                           (CokernelArrow (Abelian_Zero A) coker)
                           (Abelian_quotobjects_Pushout_eq1 E1 E2 BinCoprod
                                                            coker))
              (CokernelOut (Abelian_Zero A) (Abelian_epi_cokernel A E2) coker
                           (CokernelArrow (Abelian_Zero A) coker)
                           (Abelian_quotobjects_Pushout_eq2 E1 E2 BinCoprod
                                                            coker))
              (Abelian_quotobjects_Pushout_eq3 E1 E2 BinCoprod coker).
  Proof.
    (* variables *)
    set (coker1 := Abelian_epi_cokernel A E1).
    set (coker2 := Abelian_epi_cokernel A E2).
    set (ar := BinCoproductArrow
                 A BinCoprod
                 (AECD_Mor (Abelian_AECD A) x y E1)
                 (AECD_Mor (Abelian_AECD A) x z E2)).

    assert (com1 : E1 ;; CokernelOut (Abelian_Zero A) coker1 coker
                      (CokernelArrow (Abelian_Zero A) coker)
                      (Abelian_quotobjects_Pushout_eq1 E1 E2 BinCoprod coker)
                   = CokernelArrow (Abelian_Zero A) coker).
    {
      apply (CokernelCommutes (Abelian_Zero A) coker1 _
                              (CokernelArrow (Abelian_Zero A) coker)).
    }

    assert (com2 : E2 ;; CokernelOut (Abelian_Zero A) coker2 coker
                      (CokernelArrow (Abelian_Zero A) coker)
                      (Abelian_quotobjects_Pushout_eq2 E1 E2 BinCoprod coker)
                   = CokernelArrow (Abelian_Zero A) coker).
    {
      apply (CokernelCommutes (Abelian_Zero A) coker2 _
                              (CokernelArrow (Abelian_Zero A) coker)).
    }

    (* isPushout *)
    use mk_isPushout.
    intros e h k H.

    (* First we show that h ;; M1 ;; ar = ZeroArrow by uniqueness of the
       morphism to product. *)
    assert (e1 : (AECD_Mor (Abelian_AECD A) x y E1)
                   ;; (CokernelArrow (Abelian_Zero A) coker1) ;; h
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      set (ee1 := CokernelCompZero (Abelian_Zero A) coker1). cbn in ee1. cbn.
      rewrite ee1.
      apply ZeroArrow_comp_left.
    }

    assert (e2 : (AECD_Mor (Abelian_AECD A) x z E2)
                   ;; (CokernelArrow (Abelian_Zero A) coker2) ;; k
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      set (ee2 := CokernelCompZero (Abelian_Zero A) coker2). cbn in ee2. cbn.
      rewrite ee2.
      apply ZeroArrow_comp_left.
    }

    cbn in e1, e2.

    assert (e'1 : (AECD_Mor (Abelian_AECD A) x z E2) ;; E1 ;; h =
                  ZeroArrow _ (Abelian_Zero A) _ _).
    {
      rewrite <- assoc. rewrite H. rewrite assoc. apply e2.
    }

    assert (e'2 : (AECD_Mor (Abelian_AECD A) x y E1) ;; E2 ;; k
                  = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      rewrite <- assoc. rewrite <- H. rewrite assoc. apply e1.
    }

    assert (e''1 : ar ;; (E1 ;; h) = ZeroArrow A (Abelian_Zero A) _ _).
    {
      rewrite assoc.
      rewrite (BinCoproductArrowEta A _ _ BinCoprod e (ar ;; E1 ;; h)).
      use BinCoproductArrowZero. rewrite assoc. rewrite assoc.
      set (tmp1 := BinCoproductIn1Commutes A _ _ BinCoprod _
                                           (AECD_Mor (Abelian_AECD A) x y E1)
                                           (AECD_Mor (Abelian_AECD A) x z E2)).
      fold ar in tmp1. rewrite tmp1.
      apply e1.

      rewrite assoc. rewrite assoc.
      set (tmp1 := BinCoproductIn2Commutes A _ _ BinCoprod _
                                           (AECD_Mor (Abelian_AECD A) x y E1)
                                           (AECD_Mor (Abelian_AECD A) x z E2)).
      fold ar in tmp1. rewrite tmp1. apply e'1.
    }

    use unique_exists.
    use (CokernelOut (Abelian_Zero A) coker e (E1 ;; h)).
    apply e''1.
    split.

    use (CokernelOutsEq (Abelian_Zero A) coker1). cbn.
    set (com'1 := (maponpaths (fun f : _ => f ;; CokernelOut (Abelian_Zero A)
                                           coker e (E1 ;; h) e''1)
                              com1)). cbn in com'1.
    rewrite assoc.
    use (pathscomp0 com'1).
    use CokernelCommutes.

    use (CokernelOutsEq (Abelian_Zero A) coker2). cbn.
    set (com'2 := (maponpaths (fun f : _ => f ;; CokernelOut (Abelian_Zero A)
                                           coker e (E1 ;; h) e''1)
                              com2)). cbn in com'2.
    rewrite assoc.
    use (pathscomp0 com'2). rewrite <- H.
    use CokernelCommutes.

    (* Equality on equalities of morphisms *)
    intros y0. apply isapropdirprod. apply hs. apply hs.

    (* Uniqueness *)
    intros y0 t. cbn in t. induction t as [t p].
    apply (CokernelArrowisEpi (Abelian_Zero A) coker).
    rewrite (CokernelCommutes (Abelian_Zero A) coker).
    rewrite <- (CokernelCommutes (Abelian_Zero A) coker1 coker
                                (CokernelArrow (Abelian_Zero A) coker)
                                (Abelian_quotobjects_Pushout_eq1
                                   E1 E2 BinCoprod coker)).
    rewrite <- assoc.
    use (pathscomp0 (maponpaths (fun f : _ => CokernelArrow (Abelian_Zero A)
                                                         coker1 ;; f) t)).
    apply idpath.
  Qed.

  Definition Abelian_quotobjects_Pushout {x y z: A}
        (E1 : Epi A x y) (E2 : Epi A x z) :
    Pushout E1 E2.
  Proof.
    (* variables *)
    set (coker1 := Abelian_epi_cokernel A E1).
    set (coker2 := Abelian_epi_cokernel A E2).
    set (BinCoprod := Abelian_BinCoproducts
                        A
                        (AECD_Ob (Abelian_AECD A) x y E1)
                        (AECD_Ob (Abelian_AECD A) x z E2)).
    set (ar := BinCoproductArrow
                 A BinCoprod
                 (AECD_Mor (Abelian_AECD A) x y E1)
                 (AECD_Mor (Abelian_AECD A) x z E2)).
    set (coker := Abelian_Cokernels A _ _ ar).

    (* construction *)
    use (mk_Pushout
           E1 E2 coker
           (CokernelOut (Abelian_Zero A) coker1 coker
                        (CokernelArrow (Abelian_Zero A) coker)
                        (Abelian_quotobjects_Pushout_eq1 E1 E2 BinCoprod coker))
           (CokernelOut (Abelian_Zero A) coker2 coker
                        (CokernelArrow (Abelian_Zero A) coker)
                        (Abelian_quotobjects_Pushout_eq2 E1 E2 BinCoprod coker))
           (Abelian_quotobjects_Pushout_eq3 E1 E2 BinCoprod coker)
           (Abelian_quotobjects_Pushout_isPushout E1 E2 BinCoprod coker)).
  Defined.

End abelian_subobject_pullbacks.

(** * Equalizers and Coequalizers
  In the following section we show that equalizers and coequalizers exist in
  abelian categories.  *)
Section abelian_equalizers.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  (** ** Equalizers *)

  (** Some results we are going to need to prove existence of Equalizers. *)
  Definition Abelian_Equalizer_isMonic {x y : A} (f: x --> y) :
    isMonic A (BinProductArrow A (Abelian_BinProducts A x y) (identity x) f).
  Proof.
    set (BinProd := Abelian_BinProducts A x y).
    intros z h1 h2 H.
    apply (maponpaths (fun h : _ => h ;; (BinProductPr1 A BinProd))) in H.
    rewrite <- assoc in H. rewrite <- assoc in H.
    set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f).
    rewrite com1 in H.
    rewrite (id_right A _ _ h1) in H. rewrite (id_right A _ _ h2) in H.
    exact H.
  Qed.

  Definition Abelian_Equalizer_Pullback {x y : A} (f1 f2 : x --> y) :
    Pullback (BinProductArrow A (Abelian_BinProducts A x y) (identity x) f1)
             (BinProductArrow A (Abelian_BinProducts A x y) (identity x) f2)
    := Abelian_subobjects_Pullback
         A hs
         (mk_Monic A _ (Abelian_Equalizer_isMonic f1))
         (mk_Monic A _ (Abelian_Equalizer_isMonic f2)).

  Definition Abelian_Equalizer_eq1 {x y : A} (f1 f2 : x --> y) :
    PullbackPr1 (Abelian_Equalizer_Pullback f1 f2)
    = PullbackPr2 (Abelian_Equalizer_Pullback f1 f2).
  Proof.
    set (BinProd := Abelian_BinProducts A x y).
    set (ar1 := BinProductArrow A BinProd (identity x) f1).
    set (ar2 := BinProductArrow A BinProd (identity x) f2).
    set (Pb := Abelian_Equalizer_Pullback f1 f2).

    assert (H1 : ar1 ;; (BinProductPr1 A BinProd) = identity x) by
        apply BinProductPr1Commutes.
    assert (H2 : ar2 ;; (BinProductPr1 A BinProd) = identity x) by
        apply BinProductPr1Commutes.
    use (pathscomp0 (!(id_right A _ _ (PullbackPr1 Pb)))).
    use (pathscomp0 (!(maponpaths (fun h : _ => PullbackPr1 Pb ;; h) H1))).
    use (pathscomp0 _ ((id_right A _ _ (PullbackPr2 Pb)))).
    use (pathscomp0 _ (maponpaths (fun h : _ => PullbackPr2 Pb ;; h) H2)).
    rewrite assoc. rewrite assoc. apply cancel_postcomposition.
    apply PullbackSqrCommutes.
  Qed.

  Definition Abelian_Equalizer_eq2 {x y : A} (f1 f2 : x --> y) :
    PullbackPr1 (Abelian_Equalizer_Pullback f1 f2) ;; f1
    = PullbackPr1 (Abelian_Equalizer_Pullback f1 f2) ;; f2.
  Proof.
    set (BinProd := Abelian_BinProducts A x y).
    set (ar1 := BinProductArrow A BinProd (identity x) f1).
    set (ar2 := BinProductArrow A BinProd (identity x) f2).
    set (H := Abelian_Equalizer_eq1 f1 f2).
    set (Pb := Abelian_Equalizer_Pullback f1 f2).

    assert (H1 : BinProductArrow A BinProd (identity x) f1 ;;
                                 (BinProductPr2 A BinProd) = f1) by
        apply BinProductPr2Commutes.

    assert (H2 : BinProductArrow A BinProd (identity x) f2 ;;
                                 (BinProductPr2 A BinProd) = f2) by
        apply BinProductPr2Commutes.

    rewrite <- H1. rewrite <- H2. rewrite assoc. rewrite assoc.
    apply cancel_postcomposition. unfold BinProd.
    set (X := PullbackSqrCommutes (Abelian_Equalizer_Pullback f1 f2)).
    rewrite <- H in X. apply X.
  Qed.

  Definition Abelian_isEqualizer {x y : A} (f1 f2 : x --> y) :
    isEqualizer f1 f2 (PullbackPr1 (Abelian_Equalizer_Pullback f1 f2))
                (Abelian_Equalizer_eq2 f1 f2).
  Proof.
    set (BinProd := Abelian_BinProducts A x y).
    set (ar1 := BinProductArrow A BinProd (identity x) f1).
    set (ar2 := BinProductArrow A BinProd (identity x) f2).
    set (H := Abelian_Equalizer_eq1 f1 f2).

    apply mk_isEqualizer.
    intros w h HH.

    assert (HH' : h ;; ar1 = BinProductArrow A BinProd h (h ;; f1)).
    {
      apply (BinProductArrowUnique A _ _ BinProd).
      rewrite <- assoc.
      set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f1).
      fold ar1 in com1. rewrite com1. apply id_right.

      rewrite <- assoc.
      set (com2 := BinProductPr2Commutes A _ _ BinProd x (identity x) f1).
      fold ar1 in com2. rewrite com2. apply idpath.
    }

    assert (HH'' : h ;; ar2 = BinProductArrow A BinProd h (h ;; f1)).
    {
      apply (BinProductArrowUnique A _ _ BinProd).
      rewrite <- assoc.
      set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f2).
      fold ar2 in com1. rewrite com1. apply id_right.

      rewrite <- assoc.
      set (com2 := BinProductPr2Commutes A _ _ BinProd x (identity x) f2).
      fold ar2 in com2. rewrite com2. apply pathsinv0. apply HH.
    }

    assert (HH''' : h ;; ar1 = h ;; ar2).
    {
      rewrite HH'. rewrite HH''. apply idpath.
    }

    set (Pbar := PullbackArrow (Abelian_Equalizer_Pullback f1 f2) w h h HH''').

    apply (unique_exists Pbar).
    apply (PullbackArrow_PullbackPr1
             (Abelian_Equalizer_Pullback f1 f2) w h h HH''').
    intros y0. apply hs.
    intros y0 t.

    apply PullbackArrowUnique.
    apply t. rewrite <- H. apply t.
  Qed.

  (** Construction of the equalizer. *)
  Definition Abelian_Equalizer {x y : A} (f1 f2 : x --> y) :
    Equalizer f1 f2
    := mk_Equalizer
         f1 f2 (PullbackPr1 (Abelian_Equalizer_Pullback f1 f2))
         (Abelian_Equalizer_eq2 f1 f2)
         (Abelian_isEqualizer f1 f2).

  Corollary Abelian_Equalizers : @Equalizers A.
  Proof.
    intros X Y f g.
    apply Abelian_Equalizer.
  Defined.

  (** ** Coequalizers *)

  (** Some results we are going to need to prove existence of Coequalizers. *)
  Definition Abelian_Coequalizer_isEpi {x y : A} (f: y --> x) :
    isEpi A (BinCoproductArrow A (Abelian_BinCoproducts A x y) (identity x) f).
  Proof.
    set (BinCoprod := Abelian_BinCoproducts A x y).
    intros z h1 h2 H.
    apply (maponpaths (fun f : _ => (BinCoproductIn1 A BinCoprod) ;; f)) in H.
    rewrite assoc in H. rewrite assoc in H.
    set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f).
    rewrite com1 in H.
    rewrite (id_left A _ _ h1) in H. rewrite (id_left A _ _ h2) in H.
    exact H.
  Qed.

  Definition Abelian_Coequalizer_Pushout {x y : A} (f1 f2 : y --> x) :
    Pushout (BinCoproductArrow A (Abelian_BinCoproducts A x y) (identity x) f1)
            (BinCoproductArrow A (Abelian_BinCoproducts A x y) (identity x) f2)
    := Abelian_quotobjects_Pushout
         A hs
         (mk_Epi A _ (Abelian_Coequalizer_isEpi f1))
         (mk_Epi A _ (Abelian_Coequalizer_isEpi f2)).

  Definition Abelian_Coequalizer_eq1 {x y : A} (f1 f2 : y --> x) :
    PushoutIn1 (Abelian_Coequalizer_Pushout f1 f2)
    = PushoutIn2 (Abelian_Coequalizer_Pushout f1 f2).
  Proof.
    set (BinCoprod := Abelian_BinCoproducts A x y).
    set (ar1 := BinCoproductArrow A BinCoprod (identity x) f1).
    set (ar2 := BinCoproductArrow A BinCoprod (identity x) f2).
    set (Po := Abelian_Coequalizer_Pushout f1 f2).

    assert (H1 : (BinCoproductIn1 A BinCoprod) ;; ar1 = identity x) by
        apply BinCoproductIn1Commutes.
    assert (H2 : (BinCoproductIn1 A BinCoprod) ;; ar2 = identity x) by
        apply BinCoproductIn1Commutes.
    use (pathscomp0 (!(id_left A _ _ (PushoutIn1 Po)))).
    use (pathscomp0 (!(maponpaths (fun h : _ => h ;; PushoutIn1 Po) H1))).
    use (pathscomp0 _ ((id_left A _ _ (PushoutIn2 Po)))).
    use (pathscomp0 _ (maponpaths (fun h : _ => h ;; PushoutIn2 Po) H2)).
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    apply PushoutSqrCommutes.
  Qed.

  Definition Abelian_Coequalizer_eq2 {x y : A} (f1 f2 : y --> x) :
    f1 ;; PushoutIn1 (Abelian_Coequalizer_Pushout f1 f2)
    = f2 ;; PushoutIn1 (Abelian_Coequalizer_Pushout f1 f2).
  Proof.
    set (BinCoprod := Abelian_BinCoproducts A x y).
    set (ar1 := BinCoproductArrow A BinCoprod (identity x) f1).
    set (ar2 := BinCoproductArrow A BinCoprod (identity x) f2).
    set (H := Abelian_Coequalizer_eq1 f1 f2).
    set (Pb := Abelian_Coequalizer_Pushout f1 f2).


    assert (H1 : (BinCoproductIn2 A BinCoprod)
                   ;; BinCoproductArrow A BinCoprod (identity x) f1 = f1) by
        apply BinCoproductIn2Commutes.

    assert (H2 : (BinCoproductIn2 A BinCoprod)
                   ;; BinCoproductArrow A BinCoprod (identity x) f2 = f2) by
        apply BinCoproductIn2Commutes.

    rewrite <- H1. rewrite <- H2. rewrite <- assoc. rewrite <- assoc.
    apply cancel_precomposition. unfold BinCoprod.
    set (X := PushoutSqrCommutes (Abelian_Coequalizer_Pushout f1 f2)).
    rewrite <- H in X. apply X.
  Qed.

  Definition Abelian_isCoequalizer {x y : A} (f1 f2 : y --> x) :
    isCoequalizer f1 f2 (PushoutIn1 (Abelian_Coequalizer_Pushout f1 f2))
                  (Abelian_Coequalizer_eq2 f1 f2).
  Proof.
    set (BinCoprod := Abelian_BinCoproducts A x y).
    set (ar1 := BinCoproductArrow A BinCoprod (identity x) f1).
    set (ar2 := BinCoproductArrow A BinCoprod (identity x) f2).
    set (H := Abelian_Coequalizer_eq1 f1 f2).

    apply mk_isCoequalizer.
    intros w h HH.

    assert (HH' : ar1 ;; h = BinCoproductArrow A BinCoprod h (f1 ;; h)).
    {
      apply (BinCoproductArrowUnique A _ _ BinCoprod).
      rewrite assoc.
      set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f1).
      fold ar1 in com1. rewrite com1. apply id_left.

      rewrite assoc.
      set (com2 := BinCoproductIn2Commutes A _ _ BinCoprod x (identity x) f1).
      fold ar1 in com2. rewrite com2. apply idpath.
    }

    assert (HH'' : ar2 ;; h = BinCoproductArrow A BinCoprod h (f1 ;; h)).
    {
      apply (BinCoproductArrowUnique A _ _ BinCoprod).
      rewrite assoc.
      set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f2).
      fold ar2 in com1. rewrite com1. apply id_left.

      rewrite assoc.
      set (com2 := BinCoproductIn2Commutes A _ _ BinCoprod x (identity x) f2).
      fold ar2 in com2. rewrite com2. apply pathsinv0. apply HH.
    }

    assert (HH''' : ar1 ;; h = ar2 ;; h).
    {
      rewrite HH'. rewrite HH''. apply idpath.
    }

    set (Poar := PushoutArrow (Abelian_Coequalizer_Pushout f1 f2) w h h HH''').

    apply (unique_exists Poar).
    apply (PushoutArrow_PushoutIn1
             (Abelian_Coequalizer_Pushout f1 f2) w h h HH''').
    intros y0. apply hs.
    intros y0 t.

    apply PushoutArrowUnique.
    apply t. rewrite <- H. apply t.
  Qed.

  (** Construction of Coequalizer. *)
  Definition Abelian_Coequalizer {x y : A} (f1 f2 : y --> x) :
    Coequalizer f1 f2
    := mk_Coequalizer
         f1 f2 (PushoutIn1 (Abelian_Coequalizer_Pushout f1 f2))
         (Abelian_Coequalizer_eq2 f1 f2)
         (Abelian_isCoequalizer f1 f2).

  Corollary Abelian_Coequalizers : @Coequalizers A.
  Proof.
    intros X Y f g.
    apply Abelian_Coequalizer.
  Defined.

End abelian_equalizers.

(** * Pushouts and pullbacks
  As a corollary of the above section we get that abelian categories have
  pullbacks and pushouts. *)
Section abelian_pushouts.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  Definition Abelian_Pullbacks : @Pullbacks A.
  Proof.
    apply (@Pullbacks_from_Equalizers_BinProducts A hs).
    apply (Abelian_BinProducts A).
    apply (Abelian_Equalizers A hs).
  Defined.

  Definition Abelian_Pushouts : @Pushouts A.
  Proof.
    apply (@Pushouts_from_Coequalizers_BinCoproducts A hs).
    apply (Abelian_BinCoproducts A).
    apply (Abelian_Coequalizers A hs).
  Defined.

End abelian_pushouts.


(** * Monic kernels and Epi cokernels
  In this section we prove that kernels of monomorphisms are given by the
  arrows from zero and cokernels of epimorphisms are given by the arrows to
  zero. *)
Section abelian_monic_kernels.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  (** ** KernelArrow of Monic = ArrowFromZero *)

  (* Hide isEqualizer behind Qed. *)
  Definition Abelian_MonicKernelZero_isEqualizer {x y : A} (M : Monic A x y) :
    isEqualizer M (ZeroArrow A (Abelian_Zero A) x y) (ZeroArrowFrom x)
                (KernelEqRw (Abelian_Zero A)
                            (ArrowsFromZero
                               A (Abelian_Zero A)
                               y (ZeroArrowFrom x ;; M)
                               (ZeroArrow A (Abelian_Zero A)
                                          (Abelian_Zero A) y))).
  Proof.
    use (mk_isEqualizer).
    intros w h X.

    (* Transform X into an equality we need *)
    rewrite ZeroArrow_comp_right in X.
    rewrite <- (ZeroArrow_comp_left _ _ _ x y M) in X.
    apply (pr2 M) in X.

    use unique_exists.
    apply ZeroArrowTo.

    (* Commutativity *)
    cbn. rewrite X. unfold ZeroArrow. apply idpath.

    (* Equality of equalities of morphisms *)
    intros y0. apply hs.

    (* Uniqueness *)
    intros y0 Y. apply ArrowsToZero.
  Qed.


  (* A kernel of a monic is the arrow from zero. *)
  Definition Abelian_MonicKernelZero {x y : A} (M : Monic A x y) :
    Kernel (Abelian_Zero A) M
    := mk_Kernel
         (Abelian_Zero A)
         (ZeroArrowFrom _)
         M
         (ArrowsFromZero _ _ _ _ _)
         (Abelian_MonicKernelZero_isEqualizer M).

  (** ** CokernelArrow of Epi = ArrowtoZero *)

  (* Hide isCoequalizer behind Qed. *)
  Definition Abelian_EpiCokernelZero_isCoequalizer {y z : A} (E : Epi A y z) :
    isCoequalizer E (ZeroArrow A (Abelian_Zero A) y z) (ZeroArrowTo z)
                  (CokernelEqRw (Abelian_Zero A)
                                (ArrowsToZero
                                   A (Abelian_Zero A)
                                   y (E ;; ZeroArrowTo z)
                                   (ZeroArrow A (Abelian_Zero A)
                                              y (Abelian_Zero A)))).
  Proof.
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
  Qed.

  (* A cokernel of an epi is the arrow to zero. *)
  Definition Abelian_EpiCokernelZero {y z : A} (E : Epi A y z) :
    Cokernel (Abelian_Zero A) E
    := mk_Cokernel
         (Abelian_Zero A)
         (ZeroArrowTo _)
         E
         (ArrowsToZero _ _ _ _ _)
         (Abelian_EpiCokernelZero_isCoequalizer E).

  (** ** KernelArrow = FromZero ⇒ isMonic *)

  (** The following Definitions is used in the next Definition. *)
  Definition Abelian_KernelZeroMonic_cokernel {x y : A} {f1 f2 : x --> y}
             (e : f1 = f2) (CK : Cokernel (Abelian_Zero A) f1) :
    Cokernel (Abelian_Zero A) f2.
  Proof.
    use mk_Cokernel.
    exact CK.
    exact (CokernelArrow (Abelian_Zero A) CK).

    induction e. set (tmp := CokernelEqAr (Abelian_Zero A) CK).
    fold (CokernelArrow (Abelian_Zero A) CK) in tmp.
    use (pathscomp0 tmp). apply ZeroArrow_comp_left.

    induction e. apply (isCoequalizer_Coequalizer CK).
  Defined.

  (** The morphism f is monic if its kernel is zero. *)
  Definition Abelian_KernelZeroisMonic {x y z : A} (f : y --> z)
             (H : ZeroArrow A (Abelian_Zero A) x y ;; f =
                  ZeroArrow A (Abelian_Zero A) x z )
             (isE : isEqualizer
                      f (ZeroArrow A (Abelian_Zero A) _ _)
                      (ZeroArrow A (Abelian_Zero A) _ _)
                      (KernelEqRw (Abelian_Zero A) H)) :
    isMonic A f.
  Proof.
    intros w u v H'.
    set (Coeq := Abelian_Coequalizer A hs u v).
    set (Coeqar := CoequalizerOut Coeq z f H').
    set (Coeqar_epi := CoequalizerArrowEpi Coeq).
    set (Coeq_coker := Abelian_epi_cokernel A Coeqar_epi).
    set (ker := @mk_Kernel A (Abelian_Zero A) _ _ _
                      (ZeroArrow A (Abelian_Zero A) x y) f H isE).

    assert (e0 : CokernelArrow (Abelian_Zero A) Coeq_coker
                 = CoequalizerArrow Coeq).
    {
      apply idpath.
    }

    assert (e1 : f = (CokernelArrow (Abelian_Zero A) Coeq_coker)
                       ;; Coeqar).
    {
      apply pathsinv0. rewrite e0.
      set (XX := CoequalizerCommutes Coeq z f H').
      fold Coeqar in XX.
      apply XX.
    }

    assert (e2 : (AECD_Mor (Abelian_AECD A) _ _ Coeqar_epi) ;; f =
                 ZeroArrow A (Abelian_Zero A) _ _).
    {
      rewrite e1. rewrite assoc.
      rewrite CokernelCompZero.
      apply ZeroArrow_comp_left.
    }

    set (ar := KernelIn (Abelian_Zero A) ker
                        (AECD_Ob (Abelian_AECD A) _ _ Coeqar_epi)
                        (AECD_Mor (Abelian_AECD A) _ _ Coeqar_epi) e2).
    set (com1 := KernelCommutes (Abelian_Zero A) ker
                                (AECD_Ob (Abelian_AECD A) _ _ Coeqar_epi)
                                (AECD_Mor (Abelian_AECD A) _ _ Coeqar_epi) e2).

    assert (e3 : KernelArrow (Abelian_Zero A) ker
                 = ZeroArrow A (Abelian_Zero A) _ _ ).
    {
      apply idpath.
    }

    assert (e4 : AECD_Mor (Abelian_AECD A) y Coeq Coeqar_epi
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      rewrite <- com1. apply ZeroArrow_comp_right.
    }

    assert (e5 : is_iso (CoequalizerArrow Coeq)).
    {
      set (coker2 := Abelian_KernelZeroMonic_cokernel e4 Coeq_coker).
      set (coker2_iso := CokernelofZeroArrow_iso (Abelian_Zero A)
                                                 hs _ y coker2).
      apply (pr2 (coker2_iso)).
    }

    set (isoar := isopair (CoequalizerArrow Coeq) e5).
    set (coeq_eq := CoequalizerEqAr Coeq).
    apply (maponpaths (fun f : _ => f ;; inv_from_iso isoar)) in coeq_eq.
    rewrite <- assoc in coeq_eq. rewrite <- assoc in coeq_eq.
    assert(areq : CoequalizerArrow Coeq = isoar). apply idpath.
    rewrite areq in coeq_eq.
    rewrite (iso_inv_after_iso isoar) in coeq_eq.
    rewrite <- id_right. rewrite <- coeq_eq. apply pathsinv0.
    apply id_right.
  Qed.

  Definition Abelian_KernelZeroMonic {x y z : A} (f : y --> z)
             (H : ZeroArrow A (Abelian_Zero A) x y ;; f =
                  ZeroArrow A (Abelian_Zero A) x z )
             (isE : isEqualizer
                      f (ZeroArrow A (Abelian_Zero A) _ _)
                      (ZeroArrow A (Abelian_Zero A) _ _)
                      (KernelEqRw (Abelian_Zero A) H)) :
    Monic A y z.
  Proof.
    exact (mk_Monic A f (Abelian_KernelZeroisMonic f H isE)).
  Defined.


  (** ** CokernelArrow = ToZero ⇒ isEpi *)

  (** The following Definition is used in the next Definition. *)
  Definition Abelian_CokernelZeroEpi_kernel {x y : A} {f1 f2 : x --> y}
             (e : f1 = f2) (K : Kernel (Abelian_Zero A) f1) :
    Kernel (Abelian_Zero A) f2.
  Proof.
    use mk_Kernel.
    exact K.
    exact (KernelArrow (Abelian_Zero A) K).

    induction e. set (tmp := KernelEqAr (Abelian_Zero A) K).
    fold (KernelArrow (Abelian_Zero A) K) in tmp.
    use (pathscomp0 tmp). apply ZeroArrow_comp_right.

    induction e. apply (isEqualizer_Equalizer K).
  Defined.

  (** The morphism f is monic if its kernel is zero. *)
  Definition Abelian_CokernelZeroisEpi {x y z : A} (f : x --> y)
             (H : f ;; ZeroArrow A (Abelian_Zero A) y z =
                  ZeroArrow A (Abelian_Zero A) x z )
             (isCE : isCoequalizer
                      f (ZeroArrow A (Abelian_Zero A) _ _)
                      (ZeroArrow A (Abelian_Zero A) _ _)
                      (CokernelEqRw (Abelian_Zero A) H)) :
    isEpi A f.
  Proof.
    intros w u v H'.
    set (Eq := Abelian_Equalizer A hs u v).
    set (Eqar := EqualizerIn Eq x f H').
    set (Eqar_monic := EqualizerArrowMonic Eq).
    set (Eq_ker := Abelian_monic_kernel A Eqar_monic).
    set (coker := @mk_Cokernel A (Abelian_Zero A) _ _ _
                      (ZeroArrow A (Abelian_Zero A) y z) f H isCE).

    assert (e0 : KernelArrow (Abelian_Zero A) Eq_ker = EqualizerArrow Eq).
    {
      apply idpath.
    }

    assert (e1 : f = Eqar ;; (KernelArrow (Abelian_Zero A) Eq_ker)).
    {
      apply pathsinv0. rewrite e0.
      set (XX := EqualizerCommutes Eq x f H').
      fold Eqar in XX.
      apply XX.
    }

    assert (e2 : f ;; (AMKD_Mor (Abelian_AMKD A) _ _ Eqar_monic) =
                 ZeroArrow A (Abelian_Zero A) _ _).
    {
      rewrite e1. rewrite <- assoc.
      set (tmp := maponpaths (fun f : _ => Eqar ;; f)
                             (KernelCompZero (Abelian_Zero A) Eq_ker)).
      use (pathscomp0 tmp).
      apply ZeroArrow_comp_right.
    }

    set (ar := CokernelOut (Abelian_Zero A) coker
                           (AMKD_Ob (Abelian_AMKD A) _ _ Eqar_monic)
                           (AMKD_Mor (Abelian_AMKD A) _ _ Eqar_monic) e2).
    set (com1 := CokernelCommutes (Abelian_Zero A) coker
                                  (AMKD_Ob (Abelian_AMKD A) _ _ Eqar_monic)
                                  (AMKD_Mor (Abelian_AMKD A) _ _ Eqar_monic)
                                  e2).

    assert (e3 : CokernelArrow (Abelian_Zero A) coker
                 = ZeroArrow A (Abelian_Zero A) _ _ ).
    {
      apply idpath.
    }

    assert (e4 : AMKD_Mor (Abelian_AMKD A) Eq y Eqar_monic
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      rewrite <- com1. apply ZeroArrow_comp_left.
    }

    assert (e5 : is_iso (EqualizerArrow Eq)).
    {
      set (ker2 := Abelian_CokernelZeroEpi_kernel e4 Eq_ker).
      set (ker2_iso := KernelofZeroArrow_iso (Abelian_Zero A) hs _ _ ker2).
      apply (pr2 (ker2_iso)).
    }

    set (isoar := isopair (EqualizerArrow Eq) e5).
    set (Eq_eq := EqualizerEqAr Eq).
    apply (maponpaths (fun f : _ => inv_from_iso isoar ;; f)) in Eq_eq.
    rewrite assoc in Eq_eq. rewrite assoc in Eq_eq.
    assert(areq : EqualizerArrow Eq = isoar). apply idpath.
    rewrite areq in Eq_eq.
    rewrite (iso_after_iso_inv isoar) in Eq_eq.
    rewrite <- id_left. rewrite <- Eq_eq. apply pathsinv0.
    apply id_left.
  Qed.

  Definition Abelian_CokernelZeroEpi {x y z : A} (f : x --> y)
             (H : f ;; ZeroArrow A (Abelian_Zero A) y z =
                  ZeroArrow A (Abelian_Zero A) x z )
             (isCE : isCoequalizer
                      f (ZeroArrow A (Abelian_Zero A) _ _)
                      (ZeroArrow A (Abelian_Zero A) _ _)
                      (CokernelEqRw (Abelian_Zero A) H)) :
    Epi A x y.
  Proof.
    exact (mk_Epi A f (Abelian_CokernelZeroisEpi f H isCE)).
  Defined.
End abelian_monic_kernels.


(** * Factorization of morphisms
  In this section we prove that every morphism factors as Epi ;; Monic in 2
  canonical ways. To do this we need to prove that the canonical morphism
  CoIm f --> Im f is an isomorphism. *)
Section abelian_factorization.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  (** Definition of coimage and image in abelian categories. *)
  Definition Abelian_Kernel {x y : A} (f : x --> y) :
    Kernel (Abelian_Zero A) f := Abelian_Kernels A x y f.
  Definition Abelian_Cokernel {x y : A} (f : x --> y) :
    Cokernel (Abelian_Zero A) f := Abelian_Cokernels A x y f.
  Definition Abelian_CoIm {x y : A} (f : x --> y) :
    Cokernel (Abelian_Zero A)
             (KernelArrow (Abelian_Zero A) (Abelian_Kernel f))
    := Abelian_Cokernels A _ _ (KernelArrow _ (Abelian_Kernel f)).
  Definition Abelian_Im {x y : A} (f : x --> y) :
    Kernel (Abelian_Zero A)
           (CokernelArrow (Abelian_Zero A) (Abelian_Cokernel f))
    := Abelian_Kernels A _ _ (CokernelArrow _ (Abelian_Cokernel f)).

  (** An equation we are going to use. *)
  Definition Abelian_CoIm_ar_eq {x y : A} (f : x --> y) :
    KernelArrow _ (Abelian_Kernel f) ;; f
    = ZeroArrow _ (Abelian_Zero A)  _ _.
  Proof.
    apply KernelCompZero.
  Qed.

  (** An arrow we are going to need. *)
  Definition Abelian_CoIm_ar {x y : A} (f : x --> y) : A⟦Abelian_CoIm f, y⟧.
  Proof.
    apply (CokernelOut (Abelian_Zero A) (Abelian_CoIm f) y f
                       (Abelian_CoIm_ar_eq f)).
  Defined.

  (** Some equations we are going to need. *)
  Definition Abelian_CoIm_to_Im_eq1 {x y : A} (f : x --> y) :
    CokernelArrow _ (Abelian_CoIm f)
                  ;; Abelian_CoIm_ar f
                  ;; CokernelArrow _ (Abelian_Cokernel f)
    = ZeroArrow _ (Abelian_Zero A) _ _.
  Proof.
    set (tmp := CokernelCommutes (Abelian_Zero A)
                                 (Abelian_CoIm f) y f (Abelian_CoIm_ar_eq f)).
    fold (Abelian_CoIm_ar f) in tmp. rewrite tmp.
    apply CokernelCompZero.
  Qed.

  Definition Abelian_CoIm_to_Im_eq2 {x y : A} (f : x --> y) :
    Abelian_CoIm_ar f ;; CokernelArrow _ (Abelian_Cokernel f)
    = ZeroArrow _ (Abelian_Zero A) _ _.
  Proof.
    set (isE := CokernelArrowisEpi (Abelian_Zero A) (Abelian_CoIm f)).
    set (e1 := Abelian_CoIm_to_Im_eq1 f).
    rewrite <- assoc in e1.
    rewrite <- (ZeroArrow_comp_right A (Abelian_Zero A) _ _ _
                                    (CokernelArrow (Abelian_Zero A)
                                                   (Abelian_CoIm f)))
      in e1.
    apply isE in e1. exact e1.
  Qed.

  (** In this definition we construct the canonical morphism from the coimage
    of f to the image of f. *)
  Definition Abelian_CoIm_to_Im {x y : A} (f : x --> y) :
    A⟦Abelian_CoIm f, Abelian_Im f⟧
    := (KernelIn (Abelian_Zero A) (Abelian_Im f) (Abelian_CoIm f)
                 (Abelian_CoIm_ar f) (Abelian_CoIm_to_Im_eq2 f)).

  (** The above morphism gives a way to factorize the morphism f as a composite
    of three morphisms. *)
  Definition Abelian_CoIm_to_Im_eq {x y : A} (f : x --> y) :
    f = (CokernelArrow _ (Abelian_CoIm f))
          ;; (Abelian_CoIm_to_Im f)
          ;; (KernelArrow _ (Abelian_Im f)).
  Proof.
    unfold Abelian_CoIm_to_Im.
    set (com0 := CokernelCommutes (Abelian_Zero A) (Abelian_CoIm f) y f
                                  (Abelian_CoIm_ar_eq f)).
    apply pathsinv0 in com0.
    use (pathscomp0 com0).
    rewrite <- assoc. apply cancel_precomposition.

    set (com1 := KernelCommutes (Abelian_Zero A) (Abelian_Im f)
                                (Abelian_CoIm f) (Abelian_CoIm_ar f)
                                (Abelian_CoIm_to_Im_eq2 f)).
    apply pathsinv0 in com1.
    use (pathscomp0 com1).
    apply idpath.
  Qed.

  (** Here we show that the canonical morphism CoIm f --> Im f is an
    isomorphism. *)
  Lemma Abelian_CoIm_to_Im_is_iso {x y : A} (f : x --> y) :
    is_iso (Abelian_CoIm_to_Im f).
  Proof.
    (* It suffices to show that this morphism is monic and epi. *)
    use Abelian_monic_epi_is_iso.

    (* isMonic *)
    use (isMonic_postcomp A _ (KernelArrow _ (Abelian_Im f))).
    intros z g1 g2 H.
    set (q := Abelian_Coequalizer A hs g1 g2).
    set (ar := Abelian_CoIm_to_Im f ;; KernelArrow
                                  (Abelian_Zero A) (Abelian_Im f)).
    set (ar1 := CoequalizerOut q _ ar).
    set (com1 := CoequalizerCommutes q _ _ H).
    assert (isE : isEpi A ((CokernelArrow _ (Abelian_CoIm f))
                             ;; (CoequalizerArrow q))).
    {
      apply isEpi_comp.
      apply CokernelArrowisEpi.
      apply CoequalizerArrowisEpi.
    }

    set (E := mk_Epi A ((CokernelArrow _ (Abelian_CoIm f))
                          ;; (CoequalizerArrow q)) isE).
    set (coker := Abelian_epi_cokernel A E).

    assert (e0 : (AECD_Mor (Abelian_AECD A) _ _ E)
                   ;; ((CokernelArrow _ (Abelian_CoIm f))
                         ;; (CoequalizerArrow q))
                 = ZeroArrow _ (Abelian_Zero A) _ (Abelian_epi_cokernel A E)).
    {
      set (tmp := CokernelCompZero (Abelian_Zero A) (Abelian_epi_cokernel A E)).
      rewrite <- tmp.
      apply cancel_precomposition.
      unfold E. apply idpath.
    }

    assert (e : (AECD_Mor (Abelian_AECD A) _ _ E) ;; f
                = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      set (tmp := Abelian_CoIm_to_Im_eq f).
      apply (maponpaths (fun f : _ => AECD_Mor (Abelian_AECD A) x q E ;; f))
        in tmp.
      use (pathscomp0 tmp).
      rewrite <- assoc.
      rewrite <- com1.


      rewrite assoc. rewrite assoc.
      set (tmpar1 := Abelian_CoIm_to_Im f ;; KernelArrow (Abelian_Zero A)
                                        (Abelian_Im f)).
      set (tmpar2 := CoequalizerOut q y tmpar1 H).
      rewrite <- (ZeroArrow_comp_left A (Abelian_Zero A) _ _ _ tmpar2).
      apply cancel_postcomposition.
      rewrite <- assoc.

      rewrite e0. apply idpath.
    }

    set (l := KernelIn (Abelian_Zero A) (Abelian_Kernel f) _ _ e).

    assert (e1 : (AECD_Mor (Abelian_AECD A) x q E)
                   ;; (CokernelArrow _ (Abelian_CoIm f)) =
                 ZeroArrow _ (Abelian_Zero A) _ _).
    {
      set (tmp := KernelCommutes (Abelian_Zero A) (Abelian_Kernel f) _ _ e).
      rewrite <- tmp.
      fold l.
      rewrite <- (ZeroArrow_comp_right A (Abelian_Zero A) _ _ _ l).
      rewrite <- assoc.
      apply cancel_precomposition.
      unfold Abelian_CoIm.
      apply CokernelCompZero.
    }

    set (ar2 := CokernelOut (Abelian_Zero A) coker _ _ e1).
    set (com2 := CokernelCommutes (Abelian_Zero A) coker _ _ e1).
    assert (e2 : CokernelArrow (Abelian_Zero A) (Abelian_CoIm f)
                               ;; (CoequalizerArrow q) ;;
                               (CokernelOut (Abelian_Zero A) coker _ _ e1)
                 = CokernelArrow (Abelian_Zero A) (Abelian_CoIm f)).
    {
      apply com2.
    }

    assert (e3 : (CoequalizerArrow q) ;; (CokernelOut (Abelian_Zero A) coker
                                                      (Abelian_CoIm f) _ e1)
                 = identity _).
    {
      set (isE1 := CokernelArrowisEpi (Abelian_Zero A) (Abelian_CoIm f)).
      unfold isEpi in isE1.
      apply isE1. rewrite assoc.
      rewrite id_right.
      apply e2.
    }

    assert (e4 : isMonic A (CoequalizerArrow q)).
    {
      apply (isMonic_postcomp A _ (CokernelOut (Abelian_Zero A) coker
                                               (Abelian_CoIm f) _ e1)).
      set (tmp := @identity_isMonic A (Abelian_CoIm f)).
      rewrite <- e3 in tmp.
      apply tmp.
    }

    set (coeqeq := CoequalizerEqAr q).
    apply e4 in coeqeq.
    apply coeqeq.

    (* isEpi *)
    use (isEpi_precomp A (CokernelArrow _ (Abelian_CoIm f)) _).
    intros z g1 g2 H.
    set (q := Abelian_Equalizer A hs g1 g2).
    set (ar := CokernelArrow (Abelian_Zero A) (Abelian_CoIm f)
                             ;; Abelian_CoIm_to_Im f).
    set (ar1 := EqualizerIn q _ ar).
    set (com1 := EqualizerCommutes q _ _ H).
    assert (isE : isMonic A ((EqualizerArrow q)
                               ;; (KernelArrow _ (Abelian_Im f)))).
    {
      apply isMonic_comp.
      apply EqualizerArrowisMonic.
      apply KernelArrowisMonic.
    }

    set (M := mk_Monic A ((EqualizerArrow q)
                            ;; (KernelArrow _ (Abelian_Im f))) isE).
    set (ker := Abelian_monic_kernel A M).

    assert (e0 : (EqualizerArrow q) ;; (KernelArrow _ (Abelian_Im f))
                                    ;; (AMKD_Mor (Abelian_AMKD A) _ _ M)
                 = ZeroArrow _ (Abelian_Zero A) (Abelian_monic_kernel A M) _).
    {
      set (tmp := KernelCompZero (Abelian_Zero A) (Abelian_monic_kernel A M)).
      rewrite <- tmp.
      apply cancel_postcomposition.
      unfold M. apply idpath.
    }

    assert (e : f ;; (AMKD_Mor (Abelian_AMKD A) _ _ M)
                = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      set (tmp := Abelian_CoIm_to_Im_eq f).
      apply (maponpaths (fun f : _ => f ;; AMKD_Mor (Abelian_AMKD A) q y M))
        in tmp.
      use (pathscomp0 tmp).
      rewrite <- com1.

      set (tmpar1 := CokernelArrow (Abelian_Zero A) (Abelian_CoIm f)
                                   ;; Abelian_CoIm_to_Im f).
      set (tmpar2 := EqualizerIn q x tmpar1 H).
      rewrite <- (ZeroArrow_comp_right A (Abelian_Zero A) _ _ _ tmpar2).
      rewrite <- assoc. rewrite <- assoc.
      apply cancel_precomposition.
      rewrite assoc.

      rewrite e0. apply idpath.
    }

    set (l := CokernelOut (Abelian_Zero A) (Abelian_Cokernel f) _ _ e).

    assert (e1 : (KernelArrow _ (Abelian_Im f))
                   ;; (AMKD_Mor (Abelian_AMKD A) q y M)
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    {
      set (tmp := CokernelCommutes (Abelian_Zero A) (Abelian_Cokernel f) _ _ e).
      rewrite <- tmp.
      fold l.
      rewrite <- (ZeroArrow_comp_left A (Abelian_Zero A) _ _ _ l).
      rewrite assoc.
      apply cancel_postcomposition.
      unfold Abelian_Im.
      apply KernelCompZero.
    }

    set (ar2 := KernelIn (Abelian_Zero A) ker _ _ e1).
    set (com2 := KernelCommutes (Abelian_Zero A) ker _ _ e1).
    assert (e2 : (KernelIn (Abelian_Zero A) ker _ _ e1)
                   ;; (EqualizerArrow q)
                   ;; KernelArrow (Abelian_Zero A) (Abelian_Im f)
                 = KernelArrow (Abelian_Zero A) (Abelian_Im f)).
    {
      rewrite <- com2. rewrite <- assoc.
      apply cancel_precomposition. unfold ker.
      apply idpath.
    }

    assert (e3 : (KernelIn (Abelian_Zero A) ker (Abelian_Im f) _ e1)
                   ;; (EqualizerArrow q)
                 = identity _).
    {
      set (isM1 := KernelArrowisMonic (Abelian_Zero A) (Abelian_Im f)).
      unfold isMonic in isM1.
      apply isM1.
      rewrite id_left.
      apply e2.
    }

    assert (e4 : isEpi A (EqualizerArrow q)).
    {
      apply (isEpi_precomp A (KernelIn (Abelian_Zero A) ker
                                       (Abelian_Im f) _ e1)).
      set (tmp := @identity_isEpi A (Abelian_Im f)).
      rewrite <- e3 in tmp.
      apply tmp.
    }

    set (eqeq := EqualizerEqAr q).
    apply e4 in eqeq.
    apply eqeq.
  Qed.

  (** Since an isomorphism is both a monic and an epi, there are two canonical
    ways to compose f as epi ;; monic by interpreting the isomorphism as a
    monic or an epi. We define both of these factorizations. *)

  (** In the first case we interpret the isomorphism as an epi. *)
  Definition Abelian_factorization1_is_epi {x y : A} (f : x --> y) :
    isEpi A (CokernelArrow _ (Abelian_CoIm f) ;; Abelian_CoIm_to_Im f).
  Proof.
    apply isEpi_comp.
    apply CokernelArrowisEpi.
    apply (iso_isEpi A _ (Abelian_CoIm_to_Im_is_iso f)).
  Qed.

  Definition Abelian_factorization1_epi {x y : A} (f : x --> y) :
    Epi A x (Abelian_Im f).
  Proof.
    use mk_Epi.
    exact (CokernelArrow _ (Abelian_CoIm f) ;; Abelian_CoIm_to_Im f).
    apply Abelian_factorization1_is_epi.
  Defined.

  Definition Abelian_factorization1_monic {x y : A} (f : x --> y) :
    Monic A (Abelian_Im f) y.
  Proof.
    use mk_Monic.
    exact (KernelArrow _ (Abelian_Im f)).
    apply KernelArrowisMonic.
  Defined.

  Definition Abelian_factorization1 {x y : A} (f : x --> y) :
    f = (Abelian_factorization1_epi f) ;; (Abelian_factorization1_monic f).
  Proof.
    use (pathscomp0 (Abelian_CoIm_to_Im_eq f)).
    apply idpath.
  Qed.

  (** In the second case we interpret the isomorphism as a monic.  *)
  Definition Abelian_factorization2_is_monic {x y : A} (f : x --> y) :
    isMonic A (Abelian_CoIm_to_Im f ;; (KernelArrow _ (Abelian_Im f))).
  Proof.
    apply isMonic_comp.
    apply (iso_isMonic A _ (Abelian_CoIm_to_Im_is_iso f)).
    apply KernelArrowisMonic.
  Qed.

  Definition Abelian_factorization2_monic {x y : A} (f : x --> y) :
    Monic A (Abelian_CoIm f) y.
  Proof.
    use mk_Monic.
    exact (Abelian_CoIm_to_Im f ;; (KernelArrow _ (Abelian_Im f))).
    apply Abelian_factorization2_is_monic.
  Defined.

  Definition Abelian_factorization2_epi {x y : A} (f : x --> y) :
    Epi A x (Abelian_CoIm f).
  Proof.
    use mk_Epi.
    exact (CokernelArrow _ (Abelian_CoIm f)).
    apply CokernelArrowisEpi.
  Defined.

  Definition Abelian_factorization2 {x y : A} (f : x --> y) :
    f = (Abelian_factorization2_epi f) ;; (Abelian_factorization2_monic f).
  Proof.
    use (pathscomp0 (Abelian_CoIm_to_Im_eq f)).
    rewrite <- assoc.
    apply idpath.
  Qed.
End abelian_factorization.


(** * Monics are kernels of cokernels and Epis are cokernels of kernels
  In this section we prove that every monic is the kernel of its cokernel and
  every epi is the cokernel of its kernel. *)
Section abelian_kernel_cokernel.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  (** ** Monic is the kernel of its cokernel *)

  Definition Abelian_MonicToKernel_isMonic {x y : A} (M : Monic A x y) :
    isMonic A (Abelian_factorization1_epi A hs M).
  Proof.
    apply (isMonic_postcomp A _ (Abelian_factorization1_monic A M)).
    rewrite <- (Abelian_factorization1 A hs M).
    apply (pr2 M).
  Qed.

  Definition Abelian_MonicToKernel_is_iso {x y : A} (M : Monic A x y) :
    is_iso (Abelian_factorization1_epi A hs M).
  Proof.
    apply Abelian_monic_epi_is_iso.
    apply (Abelian_MonicToKernel_isMonic M).
    apply Abelian_factorization1_is_epi.
    apply hs.
  Qed.

  (** Monic is a kernel of its cokernel. *)
  Definition Abelian_MonicToKernel {x y : A} (M : Monic A x y) :
    Kernel (Abelian_Zero A) (CokernelArrow _ (Abelian_Cokernel A M))
    := Kernel_up_to_iso
         A hs (Abelian_Zero A) M
         (CokernelArrow _ (Abelian_Cokernel A M))
         (Abelian_Im A M)
         (isopair (Abelian_factorization1_epi A hs M)
                  (Abelian_MonicToKernel_is_iso M))
         (Abelian_factorization1 A hs M).

  (** The following verifies that the monic M is indeed the KernelArrow. *)
  Lemma Abelian_MonicToKernel_eq {x y : A} (M : Monic A x y) :
    KernelArrow (Abelian_Zero A) (Abelian_MonicToKernel M) = M.
  Proof.
    apply idpath.
  Defined.

  (** This generalizes the above by using any Cokernel. *)
  Definition Abelian_MonicToKernel' {x y : A} (M : Monic A x y)
    (CK : Cokernel (Abelian_Zero A) M) :
    Kernel (Abelian_Zero A) (CokernelArrow _ CK)
    := (Kernel_up_to_iso2
          A hs (Abelian_Zero A)
          (CokernelArrow _ (Abelian_Cokernel A M))
          (CokernelArrow _ CK)
          (iso_from_Cokernel_to_Cokernel (Abelian_Zero A)
                                         (Abelian_Cokernel A M) CK)
          (CokernelCommutes _ _ _ _ _)
          (Abelian_MonicToKernel M)).

  (** The following verifies that the monic M is indeed the KernelArrow of the
    generalization. *)
  Lemma Abelian_MonicToKernel_eq' {x y : A} (M : Monic A x y)
        (CK : Cokernel (Abelian_Zero A) M):
    KernelArrow (Abelian_Zero A) (Abelian_MonicToKernel' M CK) = M.
  Proof.
    apply idpath.
  Defined.

  (** ** Epi is the cokernel of its kernel *)

  Definition Abelian_EpiToCokernel_isEpi {x y : A} (E : Epi A x y) :
    isEpi A (Abelian_factorization2_monic A hs E).
  Proof.
    apply (isEpi_precomp A (Abelian_factorization2_epi A E)).
    rewrite <- (Abelian_factorization2 A hs E).
    apply (pr2 E).
  Qed.

  Definition Abelian_EpiToCokernel_is_iso {x y : A} (E : Epi A x y) :
    is_iso (Abelian_factorization2_monic A hs E).
  Proof.
    apply Abelian_monic_epi_is_iso.
    apply Abelian_factorization2_is_monic.
    apply hs.
    apply (Abelian_EpiToCokernel_isEpi E).
  Qed.

  (** Epi is a cokernel of its kernel. *)
  Definition Abelian_EpiToCokernel {x y : A} (E : Epi A x y) :
    Cokernel (Abelian_Zero A) (KernelArrow _ (Abelian_Kernel A E))
    := Cokernel_up_to_iso
         A hs (Abelian_Zero A)
         (KernelArrow _ (Abelian_Kernel A E))
         E
         (Abelian_CoIm A E)
         (isopair (Abelian_factorization2_monic A hs E)
                  (Abelian_EpiToCokernel_is_iso E))
         (Abelian_factorization2 A hs E).

  (** The following verifies that the epi E is indeed the CokernelArrow. *)
  Lemma Abelian_EpiToCokernel_eq {x y : A} (E : Epi A x y) :
    CokernelArrow (Abelian_Zero A) (Abelian_EpiToCokernel E) = E.
  Proof.
    apply idpath.
  Defined.

  (** This generalizes the above by using any Kernel. *)
  Definition Abelian_EpiToCokernel' {x y : A} (E : Epi A x y)
    (K : Kernel (Abelian_Zero A) E) :
    Cokernel (Abelian_Zero A) (KernelArrow _ K)
    := (Cokernel_up_to_iso2
          A hs (Abelian_Zero A)
          (KernelArrow _ (Abelian_Kernel A E))
          (KernelArrow _ K)
          (iso_from_Kernel_to_Kernel (Abelian_Zero A)
                                     K (Abelian_Kernel A E))
          (KernelCommutes _ _ _ _ _)
          (Abelian_EpiToCokernel E)).

  (** The following verifies that the epi E is indeed the CokernelArrow of the
    generalization. *)
  Lemma Abelian_EpiToCokernel_eq' {x y : A} (E : Epi A x y)
        (K : Kernel (Abelian_Zero A) E):
    CokernelArrow (Abelian_Zero A) (Abelian_EpiToCokernel' E K) = E.
  Proof.
    apply idpath.
  Defined.
End abelian_kernel_cokernel.
