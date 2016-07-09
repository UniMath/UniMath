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
  Definition Abelian : UU :=
    Σ A : (Σ C : precategory, AbelianData1 C), AbelianData (pr1 A) (pr2 A).
  Definition Abelian_precategory (A : Abelian) :
    precategory := pr1 (pr1 A).
  Coercion Abelian_precategory :
    Abelian >-> precategory.

  Definition mk_Abelian (C : precategory) (AD1 : AbelianData1 C)
             (AD : AbelianData C AD1) :
    Abelian := tpair _ (tpair _ C AD1) AD.

  Variable A : Abelian.
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


  (** The following definitions construct a kernel from a monic and a cokernel
    from an epi. *)
  Definition Abelian_monic_kernel {x y : A} (M : Monic A x y) :
    Kernel Abelian_Zero (AMKD_Mor Abelian_AMKD x y M).
  Proof.
    use (mk_Kernel Abelian_Zero M).
    rewrite (AMKD_Eq Abelian_AMKD x y M).
    apply ZeroArrow_comp_right.
    apply (AMKD_isE Abelian_AMKD x y M).
  Defined.

  Definition Abelian_epi_cokernel {y z : A} (E : Epi A y z) :
    Cokernel Abelian_Zero (AECD_Mor Abelian_AECD y z E).
  Proof.
    use (mk_Cokernel Abelian_Zero E).
    rewrite (AECD_Eq Abelian_AECD y z E).
    apply ZeroArrow_comp_left.
    apply (AECD_isC Abelian_AECD y z E).
  Defined.

  (** The following lemmas verify that the kernel and cokernel arrows are indeed
    the monic M and the epi E. *)
  Lemma Abelian_monic_kernel_eq {x y : A} (M : Monic A x y) :
    KernelArrow Abelian_Zero (Abelian_monic_kernel M) = M.
  Proof.
    apply idpath.
  Qed.

  Lemma Abelian_epi_cokernel_eq {x y : A} (E : Epi A x y) :
    CokernelArrow Abelian_Zero (Abelian_epi_cokernel E) = E.
  Proof.
    apply idpath.
  Qed.
End def_abelian.

(** In abelian categories morphisms which are both monic and epi are
  isomorphisms. *)
Section abelian_monic_epi_iso.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  (** If a morphism if a monic and an epi, then it is also an iso. *)
  Lemma Abelian_monic_epi_is_iso {x y : A} {f : x --> y} :
    isMonic A f -> isEpi A f -> is_iso f.
  Proof.

    intros M E.
    set (M1 := mk_Monic A f M).
    set (E1 := mk_Epi A f E).
    set (AMK := Abelian_AMKD A x y M1).
    set (AEC := Abelian_AECD A x y E1).

    induction AMK. induction t. induction t.
    induction AEC. induction t0. induction t0.

    unfold isEqualizer in p. unfold isCoequalizer in p2.

    (* Here we construct the inverse of f *)
    cbn in *. apply E in p0.
    set (p' := p y (identity _)).
    set (t'1 := maponpaths (fun h : A⟦y, t⟧ => identity _ ;; h) p0).
    cbn in t'1.
    set (p'' := p' t'1).
    induction p''. induction t1.

    use is_iso_qinv.

    (* The inverse of f. *)
    exact t1.

    (* It remains to show that this is the inverse of f *)
    split.
    apply (pr2 M1). cbn. rewrite <- assoc. rewrite p6.
    rewrite (remove_id_right A _ _ _ (identity x ;; f)).
    apply idpath. apply idpath. apply pathsinv0.
    apply id_left.

    apply p6.
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
    subobjects and pushouts of quotient objects. *)
Section abelian_subobject_pullbacks.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  Definition Abelian_subobjects_Pullback {x y z: A}
        (M1 : Monic A x z) (M2 : Monic A y z) :
    Pullback M1 M2.
  Proof.
    (* Some variables we are going to use. *)
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


    (* Equalities of morphisms we are going to need. *)
    assert (H1 : KernelArrow (Abelian_Zero A) ker
                             ;; (AMKD_Mor (Abelian_AMKD A) x z M1)
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite <- (BinProductPr1Commutes A _ _ BinProd _
                                     (AMKD_Mor (Abelian_AMKD A) x z M1)
                                     (AMKD_Mor (Abelian_AMKD A) y z M2)).
    rewrite assoc. fold ar. rewrite (KernelCompZero (Abelian_Zero A) ker).
    apply ZeroArrow_comp_left.

    assert (H2 : KernelArrow (Abelian_Zero A) ker
                             ;; (AMKD_Mor (Abelian_AMKD A) y z M2)
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite <- (BinProductPr2Commutes A _ _ BinProd _
                                     (AMKD_Mor (Abelian_AMKD A) x z M1)
                                     (AMKD_Mor (Abelian_AMKD A) y z M2)).
    rewrite assoc. fold ar. rewrite (KernelCompZero (Abelian_Zero A) ker).
    apply ZeroArrow_comp_left.

    assert (com1 : KernelIn (Abelian_Zero A) ker1 ker
                            (KernelArrow (Abelian_Zero A) ker) H1 ;; M1
                   = KernelArrow (Abelian_Zero A) ker).
    apply (KernelCommutes (Abelian_Zero A) ker1 _
                          (KernelArrow (Abelian_Zero A) ker)).

    assert (com2 : KernelIn (Abelian_Zero A) ker2 ker
                            (KernelArrow (Abelian_Zero A) ker) H2 ;; M2
                   = KernelArrow (Abelian_Zero A) ker).
    apply (KernelCommutes (Abelian_Zero A) ker2 _
                          (KernelArrow (Abelian_Zero A) ker)).

    use mk_Pullback.

    (* Pullback object *)
    apply ker.

    (* The arrow pr1 *)
    use (KernelIn (Abelian_Zero A) ker1 ker (KernelArrow (Abelian_Zero A) ker)).
    apply H1.

    (* The arrow pr2 *)
    use (KernelIn (Abelian_Zero A) ker2 ker (KernelArrow (Abelian_Zero A) ker)).
    apply H2.

    (* Commutativity of the arrows pr1 and pr2 *)
    rewrite (KernelCommutes (Abelian_Zero A) ker1 _
                            (KernelArrow (Abelian_Zero A) ker)).
    rewrite (KernelCommutes (Abelian_Zero A) ker2 _
                            (KernelArrow (Abelian_Zero A) ker)).
    apply idpath.

    (* isPullback. *)
    use mk_isPullback.
    intros e h k H.

    (* First we show that h ;; M1 ;; ar = ZeroArrow by uniqueness of the
       morphism to product. *)
    assert (e1 : h ;; (KernelArrow (Abelian_Zero A) ker1) ;;
                   (AMKD_Mor (Abelian_AMKD A) x z M1)
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite <- assoc.
    set (ee1 := KernelCompZero (Abelian_Zero A) ker1). cbn in ee1. cbn.
    rewrite ee1.
    apply ZeroArrow_comp_right.

    assert (e2 : k ;; (KernelArrow (Abelian_Zero A) ker2) ;;
                   (AMKD_Mor (Abelian_AMKD A) y z M2)
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite <- assoc.
    set (ee2 := KernelCompZero (Abelian_Zero A) ker2). cbn in ee2. cbn.
    rewrite ee2.
    apply ZeroArrow_comp_right.

    cbn in e1, e2.

    assert (e'1 : h ;; M1 ;; (AMKD_Mor (Abelian_AMKD A) y z M2)
                  = ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite H. apply e2.

    assert (e'2 : k ;; M2 ;; (AMKD_Mor (Abelian_AMKD A) x z M1)
                  = ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite <- H. apply e1.

    assert (e''1 : h ;; M1 ;; ar = ZeroArrow A (Abelian_Zero A) _ _).
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

    assert (e''2 : k ;; M2 ;; ar = ZeroArrow A (Abelian_Zero A) _ _).
    rewrite (BinProductArrowEta A _ _ BinProd e (k ;; M2 ;; ar)).
    use BinProductArrowZero. rewrite <- assoc.
    set (tmp1 := BinProductPr1Commutes A _ _ BinProd _
                                       (AMKD_Mor (Abelian_AMKD A) x z M1)
                                       (AMKD_Mor (Abelian_AMKD A) y z M2)).
    fold ar in tmp1. rewrite tmp1.
    apply e'2.

    rewrite <- assoc.
    set (tmp1 := BinProductPr2Commutes A _ _ BinProd _
                                       (AMKD_Mor (Abelian_AMKD A) x z M1)
                                       (AMKD_Mor (Abelian_AMKD A) y z M2)).
    fold ar in tmp1. rewrite tmp1. apply e2.

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
    intros y0 t. cbn in t. induction t.
    apply (KernelArrowisMonic (Abelian_Zero A) ker).
    rewrite (KernelCommutes (Abelian_Zero A) ker).
    rewrite <- (KernelCommutes (Abelian_Zero A) ker1 ker
                              (KernelArrow (Abelian_Zero A) ker) H1).
    rewrite assoc.
    use (pathscomp0 (maponpaths (fun f : _ => f ;; KernelArrow (Abelian_Zero A)
                                             ker1) t)).
    apply idpath.
  Defined.

  Definition Abelian_quotobject_pushout {x y z: A}
        (E1 : Epi A x y) (E2 : Epi A x z) :
    Pushout E1 E2.
  Proof.
    (* Some variables we are going to use. *)
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


    (* Equalities of morphisms we are going to need. *)
    assert (H1 : (AECD_Mor (Abelian_AECD A) x y E1)
                   ;; CokernelArrow (Abelian_Zero A) coker
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite <- (BinCoproductIn1Commutes A _ _ BinCoprod _
                                       (AECD_Mor (Abelian_AECD A) x y E1)
                                       (AECD_Mor (Abelian_AECD A) x z E2)).
    rewrite <- assoc. fold ar.
    rewrite (CokernelCompZero (Abelian_Zero A) coker).
    apply ZeroArrow_comp_right.

    assert (H2 : (AECD_Mor (Abelian_AECD A) x z E2)
                   ;; CokernelArrow (Abelian_Zero A) coker
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite <- (BinCoproductIn2Commutes A _ _ BinCoprod _
                                       (AECD_Mor (Abelian_AECD A) x y E1)
                                       (AECD_Mor (Abelian_AECD A) x z E2)).
    rewrite <- assoc. fold ar.
    rewrite (CokernelCompZero (Abelian_Zero A) coker).
    apply ZeroArrow_comp_right.

    assert (com1 : E1 ;; CokernelOut (Abelian_Zero A) coker1 coker
                      (CokernelArrow (Abelian_Zero A) coker) H1
                   = CokernelArrow (Abelian_Zero A) coker).
    apply (CokernelCommutes (Abelian_Zero A) coker1 _
                            (CokernelArrow (Abelian_Zero A) coker)).

    assert (com2 : E2 ;; CokernelOut (Abelian_Zero A) coker2 coker
                      (CokernelArrow (Abelian_Zero A) coker) H2
                   = CokernelArrow (Abelian_Zero A) coker).
    apply (CokernelCommutes (Abelian_Zero A) coker2 _
                            (CokernelArrow (Abelian_Zero A) coker)).

    use mk_Pushout.

    (* Pushout object *)
    apply coker.

    (* The arrow pr1 *)
    use (CokernelOut (Abelian_Zero A) coker1 coker
                     (CokernelArrow (Abelian_Zero A) coker)).
    apply H1.

    (* The arrow pr2 *)
    use (CokernelOut (Abelian_Zero A) coker2 coker
                     (CokernelArrow (Abelian_Zero A) coker)).
    apply H2.

    (* Commutativity of the arrows pr1 and pr2 *)
    rewrite (CokernelCommutes (Abelian_Zero A) coker1 _
                              (CokernelArrow (Abelian_Zero A) coker)).
    rewrite (CokernelCommutes (Abelian_Zero A) coker2 _
                              (CokernelArrow (Abelian_Zero A) coker)).
    apply idpath.

    (* isPushout. *)
    use mk_isPushout.
    intros e h k H.

    (* First we show that h ;; M1 ;; ar = ZeroArrow by uniqueness of the
       morphism to product. *)
    assert (e1 : (AECD_Mor (Abelian_AECD A) x y E1)
                   ;; (CokernelArrow (Abelian_Zero A) coker1) ;; h
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    set (ee1 := CokernelCompZero (Abelian_Zero A) coker1). cbn in ee1. cbn.
    rewrite ee1.
    apply ZeroArrow_comp_left.

    assert (e2 : (AECD_Mor (Abelian_AECD A) x z E2)
                   ;; (CokernelArrow (Abelian_Zero A) coker2) ;; k
                 = ZeroArrow _ (Abelian_Zero A) _ _).
    set (ee2 := CokernelCompZero (Abelian_Zero A) coker2). cbn in ee2. cbn.
    rewrite ee2.
    apply ZeroArrow_comp_left.

    cbn in e1, e2.

    assert (e'1 : (AECD_Mor (Abelian_AECD A) x z E2) ;; E1 ;; h =
                  ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite <- assoc. rewrite H. rewrite assoc. apply e2.

    assert (e'2 : (AECD_Mor (Abelian_AECD A) x y E1) ;; E2 ;; k
                  = ZeroArrow _ (Abelian_Zero A) _ _).
    rewrite <- assoc. rewrite <- H. rewrite assoc. apply e1.

    assert (e''1 : ar ;; (E1 ;; h) = ZeroArrow A (Abelian_Zero A) _ _).
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

    assert (e''2 : ar ;; (E2 ;; k) = ZeroArrow A (Abelian_Zero A) _ _).
    rewrite assoc.
    rewrite (BinCoproductArrowEta A _ _ BinCoprod e (ar ;; E2 ;; k)).
    use BinCoproductArrowZero. rewrite assoc. rewrite assoc.
    set (tmp1 := BinCoproductIn1Commutes A _ _ BinCoprod _
                                       (AECD_Mor (Abelian_AECD A) x y E1)
                                       (AECD_Mor (Abelian_AECD A) x z E2)).
    fold ar in tmp1. rewrite tmp1.
    apply e'2.

    rewrite assoc. rewrite assoc.
    set (tmp1 := BinCoproductIn2Commutes A _ _ BinCoprod _
                                         (AECD_Mor (Abelian_AECD A) x y E1)
                                         (AECD_Mor (Abelian_AECD A) x z E2)).
    fold ar in tmp1. rewrite tmp1. apply e2.

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
    intros y0 t. cbn in t. induction t.
    apply (CokernelArrowisEpi (Abelian_Zero A) coker).
    rewrite (CokernelCommutes (Abelian_Zero A) coker).
    rewrite <- (CokernelCommutes (Abelian_Zero A) coker1 coker
                                (CokernelArrow (Abelian_Zero A) coker) H1).
    rewrite <- assoc.
    use (pathscomp0 (maponpaths (fun f : _ => CokernelArrow (Abelian_Zero A)
                                                         coker1 ;; f) t)).
    apply idpath.
  Defined.

End abelian_subobject_pullbacks.

(** In the following section we show that equalizers and coequalizers exist in
  abelian categories.  *)
Section abelian_equalizers.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  Lemma Abelian_Equalizers {x y : A} (f1 f2 : x --> y) :
    Equalizer f1 f2.
  Proof.
    set (BinProd := Abelian_BinProducts A x y).
    set (ar1 := BinProductArrow A BinProd (identity x) f1).
    set (ar2 := BinProductArrow A BinProd (identity x) f2).

    assert (isM1 : isMonic A ar1).
    {
      intros z h1 h2 H.
      apply (maponpaths (fun f : _ => f ;; (BinProductPr1 A BinProd))) in H.
      rewrite <- assoc in H. rewrite <- assoc in H.
      set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f1).
      fold ar1 in com1. rewrite com1 in H.
      rewrite (id_right A _ _ h1) in H. rewrite (id_right A _ _ h2) in H.
      exact H.
    }

    assert (isM2 : isMonic A ar2).
    {
      intros z h1 h2 H.
      apply (maponpaths (fun f : _ => f ;; (BinProductPr1 A BinProd))) in H.
      rewrite <- assoc in H. rewrite <- assoc in H.
      set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f2).
      fold ar2 in com1. rewrite com1 in H.
      rewrite (id_right A _ _ h1) in H. rewrite (id_right A _ _ h2) in H.
      exact H.
    }

    set (M1 := mk_Monic A ar1 isM1).
    set (M2 := mk_Monic A ar2 isM2).

    set (Pb := Abelian_subobjects_Pullback A hs M1 M2).

    assert (H : PullbackPr1 Pb = PullbackPr2 Pb).
    {
      assert (H1 : ar1 ;; (BinProductPr1 A BinProd) = identity x) by
          apply BinProductPr1Commutes.
      assert (H2 : ar2 ;; (BinProductPr1 A BinProd) = identity x) by
          apply BinProductPr1Commutes.
      rewrite <- (id_right A _ _ (PullbackPr1 Pb)). rewrite <- H1.
      rewrite <- (id_right A _ _ (PullbackPr2 Pb)). rewrite <- H2.
      rewrite assoc. rewrite assoc. apply cancel_postcomposition.
      apply PullbackSqrCommutes.
    }

    assert (H1 : BinProductArrow A BinProd (identity x) f1 ;;
                                 (BinProductPr2 A BinProd) = f1) by
        apply BinProductPr2Commutes.

    assert (H2 : BinProductArrow A BinProd (identity x) f2 ;;
                                 (BinProductPr2 A BinProd) = f2) by
        apply BinProductPr2Commutes.

    use mk_Equalizer.
    apply Pb.
    apply (PullbackPr1 Pb).
    rewrite <- H1. rewrite <- H2. rewrite assoc. rewrite assoc.
    apply cancel_postcomposition.
    set (XX := PullbackSqrCommutes Pb). rewrite <- H in XX.
    unfold M1 in XX. unfold M2 in XX. apply XX.

    (* isEqualizer *)
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

    set (Pbar := PullbackArrow Pb w h h HH''').

    apply (unique_exists Pbar).
    apply (PullbackArrow_PullbackPr1 Pb w h h HH''').
    intros y0. apply hs.
    intros y0 t.

    apply PullbackArrowUnique.
    apply t. rewrite <- H. apply t.
  Defined.

  Lemma Abelian_Coequalizers {x y : A} (f1 f2 : y --> x) :
    Coequalizer f1 f2.
  Proof.
    set (BinCoprod := Abelian_BinCoproducts A x y).
    set (ar1 := BinCoproductArrow A BinCoprod (identity x) f1).
    set (ar2 := BinCoproductArrow A BinCoprod (identity x) f2).

    assert (isE1 : isEpi A ar1).
    {
      intros z h1 h2 H.
      apply (maponpaths (fun f : _ => (BinCoproductIn1 A BinCoprod) ;; f)) in H.
      rewrite assoc in H. rewrite assoc in H.
      set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f1).
      fold ar1 in com1. rewrite com1 in H.
      rewrite (id_left A _ _ h1) in H. rewrite (id_left A _ _ h2) in H.
      exact H.
    }

    assert (isE2 : isEpi A ar2).
    {
      intros z h1 h2 H.
      apply (maponpaths (fun f : _ => (BinCoproductIn1 A BinCoprod) ;; f)) in H.
      rewrite assoc in H. rewrite assoc in H.
      set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f2).
      fold ar2 in com1. rewrite com1 in H.
      rewrite (id_left A _ _ h1) in H. rewrite (id_left A _ _ h2) in H.
      exact H.
    }

    set (E1 := mk_Epi A ar1 isE1).
    set (E2 := mk_Epi A ar2 isE2).

    set (Po := Abelian_quotobject_pushout A hs E1 E2).

    assert (H : PushoutIn1 Po = PushoutIn2 Po).
    {
      assert (H1 : (BinCoproductIn1 A BinCoprod) ;; ar1 = identity x) by
          apply BinCoproductIn1Commutes.
      assert (H2 : (BinCoproductIn1 A BinCoprod) ;; ar2 = identity x) by
          apply BinCoproductIn1Commutes.
      rewrite <- (id_left A _ _ (PushoutIn1 Po)). rewrite <- H1.
      rewrite <- (id_left A _ _ (PushoutIn2 Po)). rewrite <- H2.
      rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
      apply PushoutSqrCommutes.
    }

    assert (H1 : (BinCoproductIn2 A BinCoprod)
                   ;; BinCoproductArrow A BinCoprod (identity x) f1 = f1) by
        apply BinCoproductIn2Commutes.

    assert (H2 : (BinCoproductIn2 A BinCoprod)
                   ;; BinCoproductArrow A BinCoprod (identity x) f2 = f2) by
        apply BinCoproductIn2Commutes.

    use mk_Coequalizer.
    apply Po.
    apply (PushoutIn1 Po).
    rewrite <- H1. rewrite <- H2.
    rewrite <- assoc. rewrite <- assoc.
    apply cancel_precomposition.
    set (XX := PushoutSqrCommutes Po). rewrite <- H in XX.
    unfold E1 in XX. unfold E2 in XX. apply XX.

    (* isCoequalizer *)
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

    set (Poar := PushoutArrow Po w h h HH''').

    apply (unique_exists Poar).
    apply (PushoutArrow_PushoutIn1 Po w h h HH''').
    intros y0. apply hs.
    intros y0 t.

    apply PushoutArrowUnique.
    apply t. rewrite <- H. apply t.
  Defined.

End abelian_equalizers.

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

(** In this section we prove that every morphism factors as epi ;; monic in 2
  canonical ways. To do this we need to prove that the canonical morphism
  CoIm f --> Im f is an isomorphism. *)
Section abelian_factorization.

  Variable A : Abelian.
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
    A⟦Abelian_CoIm f, Abelian_Im f⟧.
  Proof.
    exact (KernelIn  (Abelian_Zero A) (Abelian_Im f) (Abelian_CoIm f)
                     (Abelian_CoIm_ar f) (Abelian_CoIm_to_Im_eq2 f)).
  Defined.

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
    set (q := Abelian_Coequalizers A hs g1 g2).
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
    set (q := Abelian_Equalizers A hs g1 g2).
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


(** In this section we prove that every monic is the kernel of its cokernel and
  every epi is the cokernel of its kernel. *)
Section abelian_kernel_cokernel.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  (** First, we show that every monic is a kernel of its cokernel. *)
  Definition Abelian_MonicToKernel {x y : A} (M : Monic A x y) :
    Kernel (Abelian_Zero A) (CokernelArrow _ (Abelian_Cokernel A M)).
  Proof.
    set (ker := Abelian_Im A M).
    set (tmp := Abelian_factorization1 A hs M).

    assert (isM : isMonic A (Abelian_factorization1_epi A hs M)).
    {
      apply (isMonic_postcomp A _ (Abelian_factorization1_monic A M)).
      rewrite <- tmp.
      apply (pr2 M).
    }

    assert (isI : is_iso (Abelian_factorization1_epi A hs M)).
    {
      apply Abelian_monic_epi_is_iso.
      apply isM.
      apply Abelian_factorization1_is_epi.
      apply hs.
    }

    set (h := isopair (Abelian_factorization1_epi A hs M) isI).

    (* The following general result constructs the kernel *)
    apply (Kernel_up_to_iso A hs (Abelian_Zero A) M
                            (CokernelArrow _ (Abelian_Cokernel A M)) ker h tmp).
  Defined.

  (** The following verifies that the monic M is indeed the KernelArrow. *)
  Lemma Abelian_MonicToKernel_eq {x y : A} (M : Monic A x y) :
    KernelArrow (Abelian_Zero A) (Abelian_MonicToKernel M) = M.
  Proof.
    apply idpath.
  Defined.

  (** Next, we show that every epi is a cokernel of its kernel. *)
  Definition Abelian_EpiToCokernel {x y : A} (E : Epi A x y) :
    Cokernel (Abelian_Zero A) (KernelArrow _ (Abelian_Kernel A E)).
  Proof.
    set (coker := Abelian_CoIm A E).
    set (tmp := Abelian_factorization2 A hs E).

    assert (isE : isEpi A (Abelian_factorization2_monic A hs E)).
    {
      apply (isEpi_precomp A (Abelian_factorization2_epi A E)).
      rewrite <- tmp.
      apply (pr2 E).
    }

    assert (isI : is_iso (Abelian_factorization2_monic A hs E)).
    {
      apply Abelian_monic_epi_is_iso.
      apply Abelian_factorization2_is_monic.
      apply hs.
      apply isE.
    }

    set (h := isopair (Abelian_factorization2_monic A hs E) isI).

    (* The following general result constructs the cokernel *)
    apply (Cokernel_up_to_iso A hs (Abelian_Zero A)
                              (KernelArrow _ (Abelian_Kernel A E)) E
                              coker h tmp).
  Defined.

  (** The following verifies that the epi E is indeed the CokernelArrow. *)
  Lemma Abelian_EpiToCokernel_eq {x y : A} (E : Epi A x y) :
    CokernelArrow (Abelian_Zero A) (Abelian_EpiToCokernel E) = E.
  Proof.
    apply idpath.
  Defined.
End abelian_kernel_cokernel.
