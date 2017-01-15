(** * Abelian categories *)
(** ** Contents
- Definition of Abelian categories
- If Monic and Epi, then iso
- Pushouts of monics and pullbacks of epis
 - Pushouts of monics
 - Pullbacks of epis
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
- Opposite of an abelian category is abelian
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.Opp.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.precategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.


(** * Definition of Abelian categories *)
Section def_abelian.

  (** An abelian category has a zero object, binary (co)products, (co)kernels and every monic
      (resp. epi) is a kernel (resp. cokernel). *)
  Definition Data1 (C : precategory) : UU := Zero C × (BinProducts C) × (BinCoproducts C).

  Definition mk_Data1 {C : precategory} (H1 : Zero C) (H2 : BinProducts C) (H3 : BinCoproducts C) :
    Data1 C := (H1,,(H2,,H3)).

  Definition Data1_Zero {C : precategory} (D : Data1 C) : Zero C := dirprod_pr1 D.

  Definition Data2 (C : precategory) (AD1 : Data1 C) : UU :=
    (Kernels (pr1 AD1)) × (Cokernels (pr1 AD1)).

  Definition mk_Data2 {C : precategory} (AD1 : Data1 C) (H1 : Kernels (Data1_Zero AD1))
             (H2 : Cokernels (Data1_Zero AD1)) : Data2 C AD1 := (H1,,H2).

  (** This definition contains the data that every monic is a kernel of some morphism. *)
  Definition AbelianMonicKernelsData (C : precategory) (AD : Data1 C) : UU :=
    Π (x y : C) (M : Monic C x y),
    (Σ D2 : (Σ D1 : (Σ z : C, y --> z), M ;; (pr2 D1) = ZeroArrow (pr1 AD) x (pr1 D1)),
            isKernel (Data1_Zero AD) M (pr2 (pr1 D2)) (pr2 D2)).

  Definition mk_AbelianMonicKernelsData {C : precategory} (AD1 : Data1 C)
             (H : Π (x y : C) (M : Monic C x y),
                  (Σ D2 : (Σ D1 : (Σ z : C, y --> z), M ;; (pr2 D1) = ZeroArrow (pr1 AD1) x (pr1 D1)),
                          isKernel (Data1_Zero AD1) M (pr2 (pr1 D2)) (pr2 D2))) :
    AbelianMonicKernelsData C AD1 := H.

  (** Accessor functions for AbelianMonicKernelsData. *)
  Definition AMKD_Ob {C : precategory} {AD : Data1 C} (AMKD : AbelianMonicKernelsData C AD)
             (x y : C) (M : Monic C x y) : C := pr1 (pr1 (pr1 (AMKD x y M))).

  Definition AMKD_Mor {C : precategory} {AD : Data1 C} (AMKD : AbelianMonicKernelsData C AD)
             (x y : C) (M : Monic C x y) : C⟦y, (AMKD_Ob AMKD x y M)⟧ :=
    pr2 (pr1 (pr1 (AMKD x y M))).

  Definition AMKD_Eq {C : precategory} {AD : Data1 C} (AMKD : AbelianMonicKernelsData C AD)
             (x y : C) (M : Monic C x y) :
    M ;; (AMKD_Mor AMKD x y M) = ZeroArrow (pr1 AD) x (AMKD_Ob AMKD x y M) :=
    pr2 (pr1 (AMKD x y M)).

  Definition AMKD_isK {C : precategory} {AD : Data1 C} (AMKD : AbelianMonicKernelsData C AD)
             (x y : C) (M : Monic C x y) :
    isKernel (Data1_Zero AD) M (AMKD_Mor AMKD x y M) (AMKD_Eq AMKD x y M) := pr2 (AMKD x y M).

  (** This definition contains the data that every epi is a cokernel of some
      morphism. *)
  Definition AbelianEpiCokernelsData (C : precategory) (AD : Data1 C) : UU :=
    (Π (y z : C) (E : Epi C y z),
     (Σ D2 : (Σ D1 : (Σ x : C, x --> y), (pr2 D1) ;; E = ZeroArrow (pr1 AD) (pr1 D1) z),
             isCokernel (Data1_Zero AD) (pr2 (pr1 D2)) E (pr2 D2))).

   Definition mk_AbelianEpiCokernelsData {C : precategory} (AD1 : Data1 C)
              (H : (Π (y z : C) (E : Epi C y z),
                    (Σ D2 : (Σ D1 : (Σ x : C, x --> y),
                                   (pr2 D1) ;; E = ZeroArrow (pr1 AD1) (pr1 D1) z),
                            isCokernel (Data1_Zero AD1) (pr2 (pr1 D2)) E (pr2 D2)))) :
     AbelianEpiCokernelsData C AD1 := H.

  (** Accessor functions for AbelianEpiCokernelsData. *)
  Definition AECD_Ob {C : precategory} {AD : Data1 C} (AECD : AbelianEpiCokernelsData C AD)
             (y z : C) (E : Epi C y z) : C := pr1 (pr1 (pr1 (AECD y z E))).

  Definition AECD_Mor {C : precategory} {AD : Data1 C} (AECD : AbelianEpiCokernelsData C AD)
             (y z : C) (E : Epi C y z) : C⟦(AECD_Ob AECD y z E), y⟧ := pr2 (pr1 (pr1 (AECD y z E))).

  Definition AECD_Eq {C : precategory} {AD : Data1 C} (AECD : AbelianEpiCokernelsData C AD)
             (y z : C) (E : Epi C y z) :
    (AECD_Mor AECD y z E) ;; E = ZeroArrow (pr1 AD) (AECD_Ob AECD y z E) z :=
    pr2 (pr1 (AECD y z E)).

  Definition AECD_isC {C : precategory} {AD : Data1 C} (AECD : AbelianEpiCokernelsData C AD)
             (y z : C) (E : Epi C y z) :
    isCokernel (Data1_Zero AD) (AECD_Mor AECD y z E) E (AECD_Eq AECD y z E) := pr2 (AECD y z E).

  (** Data which contains kernels, cokernels, the data that monics are kernels of some morphisms,
      and the data that epis are cokernels of some morphisms. *)
  Definition AbelianData (C : precategory) (AD1 : Data1 C) : UU :=
    (Data2 C AD1) × (AbelianMonicKernelsData C AD1) × (AbelianEpiCokernelsData C AD1).

  Definition mk_AbelianData {C : precategory} {AD1 : Data1 C} (H1 : Data2 C AD1)
             (H2 : AbelianMonicKernelsData C AD1) (H3 : AbelianEpiCokernelsData C AD1) :
    AbelianData C AD1 := (H1,,(H2,,H3)).

  (** Definition of abelian categories. *)
  Definition AbelianPreCat : UU := Σ A : (Σ C : precategory, Data1 C), AbelianData (pr1 A) (pr2 A).

  Definition precategory_of_AbelianPreCat (A : AbelianPreCat) : precategory := pr1 (pr1 A).
  Coercion precategory_of_AbelianPreCat : AbelianPreCat >-> precategory.

  Definition mk_Abelian (C : precategory) (AD1 : Data1 C) (AD : AbelianData C AD1) :
    AbelianPreCat := tpair _ (tpair _ C AD1) AD.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  (** Accessor functions Abelian. *)
  Definition to_Zero : Zero A := pr1 (pr2 (pr1 A)).

  Definition to_BinProducts : BinProducts A := pr1 (pr2 (pr2 (pr1 A))).

  Definition to_BinCoproducts : BinCoproducts A := pr2 (pr2 (pr2 (pr1 A))).

  Definition to_Data1 : Data1 A := (pr2 (pr1 A)).

  Definition to_Kernels : Kernels to_Zero := pr1 (pr1 (pr2 A)).

  Definition to_Cokernels : Cokernels to_Zero := pr2 (pr1 (pr2 A)).

  Definition to_Data2 : Data2 A to_Data1 := pr1 (pr2 A).

  Definition to_AMKD : AbelianMonicKernelsData A (pr2 (pr1 A)) := pr1 (pr2 (pr2 A)).

  Definition to_AECD : AbelianEpiCokernelsData A (pr2 (pr1 A)) := pr2 (pr2 (pr2 A)).

  (** The following definitions construct a kernel from a monic and a cokernel
    from an epi. *)
  Definition monic_kernel {x y : A} (M : Monic A x y) :
    Kernel to_Zero (AMKD_Mor to_AMKD x y M) := mk_Kernel to_Zero _ _ _ (AMKD_isK to_AMKD x y M).

  Definition epi_cokernel {y z : A} (E : Epi A y z) :
    Cokernel to_Zero (AECD_Mor to_AECD y z E) := mk_Cokernel to_Zero _ _ _ (AECD_isC to_AECD y z E).

  (** The following lemmas verify that the kernel and cokernel arrows are indeed
    the monic M and the epi E. *)
  Lemma monic_kernel_arrow_eq {x y : A} (M : Monic A x y) : KernelArrow (monic_kernel M) = M.
  Proof.
    apply idpath.
  Qed.

  Lemma epi_cokernel_arrow_eq {x y : A} (E : Epi A x y) : CokernelArrow (epi_cokernel E) = E.
  Proof.
    apply idpath.
  Qed.
End def_abelian.
Arguments to_Zero [A].

Bind Scope abelian_precat_scope with precategory.
Notation "0" := Zero : abelian_precat.
Delimit Scope abelian_precat_scope with precategory.

(** * If Monic and Epi, then iso
  In abelian categories morphisms which are both monic and epi are
  isomorphisms. *)
Section abelian_monic_epi_iso.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  Local Lemma monic_epi_is_iso_eq {x y : A} {f : x --> y} (iM : isMonic f) (iE : isEpi f) :
    identity y ;; AMKD_Mor (to_AMKD A) x y (mk_Monic _ _ iM) =
    ZeroArrow to_Zero y (AMKD_Ob (to_AMKD A) x y (mk_Monic _ _ iM)).
  Proof.
    set (E1 := mk_Epi A f iE).
    set (AEC := to_AECD A x y E1).
    set (AMK := to_AMKD A x y (mk_Monic _ _ iM)).
    set (p0 := pr2 (pr1 AMK)). cbn in p0.
    rewrite <- (ZeroArrow_comp_right _ _ _ _ _ f) in p0. apply iE in p0.
    set (t'1 := maponpaths (fun h : A⟦y, _⟧ => identity _ ;; h) p0). cbn in t'1.
    rewrite ZeroArrow_comp_right in t'1. exact t'1.
  Qed.

  Lemma monic_epi_is_iso_inverses {x y : A} {f : x --> y} (iM : isMonic f) (iE : isEpi f) :
    is_inverse_in_precat
      f (KernelIn to_Zero (monic_kernel A (mk_Monic A f iM)) y (identity y)
                  (monic_epi_is_iso_eq iM iE)).
  Proof.
    use mk_is_inverse_in_precat.
    - apply iM. cbn. rewrite <- assoc.
      rewrite (KernelCommutes to_Zero (monic_kernel A (mk_Monic A f iM))).
      rewrite id_right. rewrite id_left.
      apply idpath.
    - exact (KernelCommutes to_Zero (monic_kernel A (mk_Monic A f iM)) _ _ _).
  Qed.

  (** If a morphism is a monic and an epi, then it is an isomorphism. *)
  Lemma monic_epi_is_iso {x y : A} {f : x --> y} : isMonic f -> isEpi f -> is_z_isomorphism f.
  Proof.
    intros iM iE.
    use mk_is_z_isomorphism.
    - exact (KernelIn to_Zero (monic_kernel A (mk_Monic _ _ iM)) y (identity y)
                      (monic_epi_is_iso_eq iM iE)).
    - exact (monic_epi_is_iso_inverses iM iE).
  Defined.

  (** Construction of the iso. *)
  Lemma monic_epi_z_iso {x y : A} {f : x --> y} : isMonic f -> isEpi f -> z_iso x y.
  Proof.
    intros iM iE.
    use mk_z_iso.
    - exact f.
    - exact (KernelIn to_Zero (monic_kernel A (mk_Monic _ _ iM)) y (identity y)
                      (monic_epi_is_iso_eq iM iE)).
    - exact (monic_epi_is_iso_inverses iM iE).
  Defined.

End abelian_monic_epi_iso.


(** * Pullbacks of monics and pushouts of epis
  In the following section we prove that an abelian category has pullbacks of
  monics and pushouts of epis. *)
Section abelian_monic_pullbacks.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  (** ** Pullbacks of monics *)

  Local Lemma monics_Pullback_eq1 {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (AMKD_Ob (to_AMKD A) x z M1) (AMKD_Ob (to_AMKD A) y z M2))
             (ker : Kernel to_Zero (BinProductArrow A BinProd (AMKD_Mor (to_AMKD A) x z M1)
                                                   (AMKD_Mor (to_AMKD A) y z M2))) :
    KernelArrow ker ;; AMKD_Mor (to_AMKD A) x z M1 = ZeroArrow to_Zero _ _.
  Proof.
    set (tmp := (BinProductPr1Commutes A _ _ BinProd _ (AMKD_Mor (to_AMKD A) x z M1)
                                       (AMKD_Mor (to_AMKD A) y z M2))).
    apply (maponpaths (fun h : _ => KernelArrow ker ;; h)) in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite assoc. rewrite (KernelCompZero to_Zero ker).
    apply ZeroArrow_comp_left.
  Qed.

  Local Lemma monics_Pullback_eq2 {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (AMKD_Ob (to_AMKD A) x z M1) (AMKD_Ob (to_AMKD A) y z M2))
             (ker : Kernel to_Zero (BinProductArrow A BinProd (AMKD_Mor (to_AMKD A) x z M1)
                                                   (AMKD_Mor (to_AMKD A) y z M2))) :
    KernelArrow ker ;; AMKD_Mor (to_AMKD A) y z M2 = ZeroArrow to_Zero _ _.
  Proof.
    set (tmp := (BinProductPr2Commutes A _ _ BinProd _ (AMKD_Mor (to_AMKD A) x z M1)
                                       (AMKD_Mor (to_AMKD A) y z M2))).
    apply (maponpaths (fun h : _ => KernelArrow ker ;; h)) in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite assoc. rewrite (KernelCompZero to_Zero ker).
    apply ZeroArrow_comp_left.
  Qed.

  Local Lemma monics_Pullback_eq3 {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z)
        (BinProd : BinProductCone A (AMKD_Ob (to_AMKD A) x z M1) (AMKD_Ob (to_AMKD A) y z M2))
        (ker : Kernel to_Zero (BinProductArrow A BinProd (AMKD_Mor (to_AMKD A) x z M1)
                                            (AMKD_Mor (to_AMKD A) y z M2))) :
    KernelIn to_Zero (monic_kernel A M1) ker (KernelArrow ker)
             (monics_Pullback_eq1 M1 M2 BinProd ker) ;; M1 =
    KernelIn to_Zero (monic_kernel A M2) ker (KernelArrow ker)
             (monics_Pullback_eq2 M1 M2 BinProd ker) ;; M2.
  Proof.
    rewrite (KernelCommutes to_Zero (monic_kernel A M1) _ (KernelArrow ker)).
    rewrite (KernelCommutes to_Zero (monic_kernel A M2) _ (KernelArrow ker)).
    apply idpath.
  Qed.

  Local Lemma monics_Pullback_isPullback {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (AMKD_Ob (to_AMKD A) x z M1) (AMKD_Ob (to_AMKD A) y z M2))
             (ker : Kernel to_Zero (BinProductArrow A BinProd (AMKD_Mor (to_AMKD A) x z M1)
                                                 (AMKD_Mor (to_AMKD A) y z M2))) :
    isPullback M1 M2 (KernelIn to_Zero (monic_kernel A M1) ker (KernelArrow ker)
                               (monics_Pullback_eq1 M1 M2 BinProd ker))
               (KernelIn to_Zero (monic_kernel A M2) ker (KernelArrow ker)
                         (monics_Pullback_eq2 M1 M2 BinProd ker))
               (monics_Pullback_eq3 M1 M2 BinProd ker).
  Proof.
    (* variables *)
    set (ker1 := monic_kernel A M1).
    set (ker2 := monic_kernel A M2).
    set (ar := BinProductArrow A BinProd (AMKD_Mor (to_AMKD A) x z M1)
                               (AMKD_Mor (to_AMKD A) y z M2)).
    assert (com1 : KernelIn to_Zero ker1 ker (KernelArrow ker)
                            (monics_Pullback_eq1 M1 M2 BinProd ker) ;; M1 = KernelArrow ker).
    {
      apply (KernelCommutes to_Zero ker1 _ (KernelArrow ker)).
    }
    assert (com2 : KernelIn to_Zero ker2 ker (KernelArrow ker)
                            (monics_Pullback_eq2 M1 M2 BinProd ker) ;; M2 = KernelArrow ker).
    {
      apply (KernelCommutes to_Zero ker2 _ (KernelArrow ker)).
    }
    (* isPullback *)
    use mk_isPullback.
    intros e h k H.
    (* First we show that h ;; M1 ;; ar = ZeroArrow by uniqueness of the morphism to product. *)
    assert (e1 : h ;; (KernelArrow ker1) ;; (AMKD_Mor (to_AMKD A) x z M1) = ZeroArrow to_Zero _ _).
    {
      rewrite <- assoc.
      set (ee1 := KernelCompZero to_Zero ker1). cbn in ee1. cbn. rewrite ee1.
      apply ZeroArrow_comp_right.
    }
    assert (e2 : k ;; (KernelArrow ker2) ;; (AMKD_Mor (to_AMKD A) y z M2) = ZeroArrow to_Zero _ _).
    {
      rewrite <- assoc.
      set (ee2 := KernelCompZero to_Zero ker2). cbn in ee2. cbn. rewrite ee2.
      apply ZeroArrow_comp_right.
    }
    cbn in e1, e2.
    assert (e'1 : h ;; M1 ;; (AMKD_Mor (to_AMKD A) y z M2) = ZeroArrow to_Zero _ _).
    {
      rewrite H. apply e2.
    }
    assert (e''1 : h ;; M1 ;; ar = ZeroArrow to_Zero _ _).
    {
      rewrite (BinProductArrowEta A _ _ BinProd e (h ;; M1 ;; ar)).
      use BinProductArrowZero.
      - rewrite <- assoc.
        set (tmp1 := BinProductPr1Commutes A _ _ BinProd _ (AMKD_Mor (to_AMKD A) x z M1)
                                           (AMKD_Mor (to_AMKD A) y z M2)).
        fold ar in tmp1. rewrite tmp1. apply e1.
      - rewrite <- assoc.
        set (tmp1 := BinProductPr2Commutes A _ _ BinProd _ (AMKD_Mor (to_AMKD A) x z M1)
                                         (AMKD_Mor (to_AMKD A) y z M2)).
        fold ar in tmp1. rewrite tmp1. apply e'1.
    }
    use unique_exists.
    (* The arrow *)
    - use (KernelIn to_Zero ker e (h ;; M1)). apply e''1.
    (* commutativity *)
    - split.
      + use (KernelInsEq to_Zero ker1).  cbn. rewrite <- assoc.
        set (com'1 := (maponpaths (fun f : _ => KernelIn to_Zero ker e (h ;; M1) e''1 ;; f) com1)).
        cbn in com'1. use (pathscomp0 com'1). use KernelCommutes.
      + use (KernelInsEq to_Zero ker2). cbn. rewrite <- assoc.
        set (com'2 := (maponpaths (fun f : _ => KernelIn to_Zero ker e (h ;; M1) e''1 ;; f) com2)).
        cbn in com'2. use (pathscomp0 com'2). rewrite <- H. use KernelCommutes.
    (* Equality of equalities of morphisms *)
    - intros y0. apply isapropdirprod.
      + apply hs.
      + apply hs.
    (* Uniqueness *)
    - intros y0 t. cbn in t. induction t as [t p].
      apply (KernelArrowisMonic to_Zero ker).
      rewrite (KernelCommutes to_Zero ker).
      rewrite <- (KernelCommutes to_Zero ker1 ker _ (monics_Pullback_eq1 M1 M2 BinProd ker)).
      rewrite assoc. use (pathscomp0 (maponpaths (fun f : _ => f ;; KernelArrow ker1) t)).
      apply idpath.
  Qed.

  (** Construction of the Pullback of monics. *)
  Definition monics_Pullback {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z) : Pullback M1 M2.
  Proof.
    set (ker1 := monic_kernel A M1).
    set (ker2 := monic_kernel A M2).
    set (BinProd := to_BinProducts A (AMKD_Ob (to_AMKD A) x z M1) (AMKD_Ob (to_AMKD A) y z M2)).
    set (ar := BinProductArrow A BinProd (AMKD_Mor (to_AMKD A) x z M1)
                               (AMKD_Mor (to_AMKD A) y z M2)).
    set (ker := to_Kernels A _ _ ar).
    use (mk_Pullback M1 M2 ker
           (KernelIn to_Zero ker1 ker (KernelArrow ker) (monics_Pullback_eq1 M1 M2 BinProd ker))
           (KernelIn to_Zero ker2 ker (KernelArrow ker) (monics_Pullback_eq2 M1 M2 BinProd ker))
           (monics_Pullback_eq3 M1 M2 BinProd ker) (monics_Pullback_isPullback M1 M2 BinProd ker)).
  Defined.


  (** ** Pushouts of epis *)

  Definition epis_Pushout_eq1 {x y z : A} (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone A (AECD_Ob (to_AECD A) x y E1)
                                             (AECD_Ob (to_AECD A) x z E2))
             (coker : Cokernel to_Zero (BinCoproductArrow A BinCoprod (AECD_Mor (to_AECD A) x y E1)
                                                         (AECD_Mor (to_AECD A) x z E2))) :
    AECD_Mor (to_AECD A) x y E1 ;; CokernelArrow coker =
    ZeroArrow to_Zero (AECD_Ob (to_AECD A) x y E1) coker.
  Proof.
    set (tmp := (BinCoproductIn1Commutes A _ _ BinCoprod _ (AECD_Mor (to_AECD A) x y E1)
                                         (AECD_Mor (to_AECD A) x z E2))).
    apply (maponpaths (fun h : _ => h ;; CokernelArrow coker)) in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite <- assoc. rewrite (CokernelCompZero to_Zero coker).
    apply ZeroArrow_comp_right.
  Qed.

  Definition epis_Pushout_eq2 {x y z : A} (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone A (AECD_Ob (to_AECD A) x y E1)
                                             (AECD_Ob (to_AECD A) x z E2))
             (coker : Cokernel to_Zero (BinCoproductArrow A BinCoprod (AECD_Mor (to_AECD A) x y E1)
                                                         (AECD_Mor (to_AECD A) x z E2))) :
    AECD_Mor (to_AECD A) x z E2 ;; CokernelArrow coker =
    ZeroArrow to_Zero (AECD_Ob (to_AECD A) x z E2) coker.
  Proof.
    set (tmp := (BinCoproductIn2Commutes A _ _ BinCoprod _ (AECD_Mor (to_AECD A) x y E1)
                                         (AECD_Mor (to_AECD A) x z E2))).
    apply (maponpaths (fun h : _ => h ;; CokernelArrow coker)) in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite <- assoc. rewrite (CokernelCompZero to_Zero coker).
    apply ZeroArrow_comp_right.
  Qed.

  Definition epis_Pushout_eq3 {x y z : A} (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone A (AECD_Ob (to_AECD A) x y E1)
                                             (AECD_Ob (to_AECD A) x z E2))
             (coker : Cokernel to_Zero (BinCoproductArrow A BinCoprod (AECD_Mor (to_AECD A) x y E1)
                                                         (AECD_Mor (to_AECD A) x z E2))) :
    E1 ;; (CokernelOut to_Zero (epi_cokernel A E1) coker (CokernelArrow coker)
                       (epis_Pushout_eq1 E1 E2 BinCoprod coker)) =
    E2 ;; (CokernelOut to_Zero (epi_cokernel A E2) coker (CokernelArrow coker)
                       (epis_Pushout_eq2 E1 E2 BinCoprod coker)).
  Proof.
    rewrite (CokernelCommutes to_Zero (epi_cokernel A E1) _ (CokernelArrow coker)).
    rewrite (CokernelCommutes to_Zero (epi_cokernel A E2) _ (CokernelArrow coker)).
    apply idpath.
  Qed.

  Definition epis_Pushout_isPushout {x y z : A} (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone A (AECD_Ob (to_AECD A) x y E1)
                                             (AECD_Ob (to_AECD A) x z E2))
             (coker : Cokernel to_Zero (BinCoproductArrow A BinCoprod (AECD_Mor (to_AECD A) x y E1)
                                                         (AECD_Mor (to_AECD A) x z E2))) :
    isPushout E1 E2 (CokernelOut to_Zero (epi_cokernel A E1) coker (CokernelArrow coker)
                                 (epis_Pushout_eq1 E1 E2 BinCoprod coker))
              (CokernelOut to_Zero (epi_cokernel A E2) coker (CokernelArrow coker)
                           (epis_Pushout_eq2 E1 E2 BinCoprod coker))
              (epis_Pushout_eq3 E1 E2 BinCoprod coker).
  Proof.
    set (coker1 := epi_cokernel A E1).
    set (coker2 := epi_cokernel A E2).
    set (ar := BinCoproductArrow A BinCoprod (AECD_Mor (to_AECD A) x y E1)
                                 (AECD_Mor (to_AECD A) x z E2)).
    assert (com1 : E1 ;; (CokernelOut to_Zero coker1 coker (CokernelArrow coker)
                                      (epis_Pushout_eq1 E1 E2 BinCoprod coker)) =
                   CokernelArrow coker).
    {
      apply (CokernelCommutes to_Zero coker1 _ (CokernelArrow coker)).
    }
    assert (com2 : E2 ;; (CokernelOut to_Zero coker2 coker (CokernelArrow coker)
                                      (epis_Pushout_eq2 E1 E2 BinCoprod coker)) =
                   CokernelArrow coker).
    {
      apply (CokernelCommutes to_Zero coker2 _ (CokernelArrow coker)).
    }
    (* isPushout *)
    use mk_isPushout.
    intros e h k H.
    (* First we show that h ;; M1 ;; ar = ZeroArrow by uniqueness of the morphism to product. *)
    assert (e1 : (AECD_Mor (to_AECD A) x y E1) ;; (CokernelArrow coker1) ;; h =
                 ZeroArrow to_Zero _ _).
    {
      set (ee1 := CokernelCompZero to_Zero coker1). cbn in ee1. cbn. rewrite ee1.
      apply ZeroArrow_comp_left.
    }
    assert (e2 : (AECD_Mor (to_AECD A) x z E2) ;; (CokernelArrow coker2) ;; k =
                 ZeroArrow to_Zero _ _).
    {
      set (ee2 := CokernelCompZero to_Zero coker2). cbn in ee2. cbn. rewrite ee2.
      apply ZeroArrow_comp_left.
    }
    cbn in e1, e2.
    assert (e'1 : (AECD_Mor (to_AECD A) x z E2) ;; E1 ;; h = ZeroArrow to_Zero _ _).
    {
      rewrite <- assoc. rewrite H. rewrite assoc. apply e2.
    }
    assert (e'2 : (AECD_Mor (to_AECD A) x y E1) ;; E2 ;; k = ZeroArrow to_Zero _ _).
    {
      rewrite <- assoc. rewrite <- H. rewrite assoc. apply e1.
    }
    assert (e''1 : ar ;; (E1 ;; h) = ZeroArrow to_Zero _ _).
    {
      rewrite assoc. rewrite (BinCoproductArrowEta A _ _ BinCoprod e (ar ;; E1 ;; h)).
      use BinCoproductArrowZero.
      - rewrite assoc. rewrite assoc.
        set (tmp1 := BinCoproductIn1Commutes A _ _ BinCoprod _ (AECD_Mor (to_AECD A) x y E1)
                                             (AECD_Mor (to_AECD A) x z E2)).
        fold ar in tmp1. rewrite tmp1. apply e1.
      - rewrite assoc. rewrite assoc.
        set (tmp1 := BinCoproductIn2Commutes A _ _ BinCoprod _ (AECD_Mor (to_AECD A) x y E1)
                                             (AECD_Mor (to_AECD A) x z E2)).
        fold ar in tmp1. rewrite tmp1. apply e'1.
    }
    use unique_exists.
    (* The arrow *)
    - use (CokernelOut to_Zero coker e (E1 ;; h)). apply e''1.
    (* Commutativity *)
    - split.
      + use (CokernelOutsEq to_Zero coker1). cbn.
        set (com'1 := maponpaths (fun f : _ => f ;; CokernelOut to_Zero coker e (E1 ;; h) e''1) com1).
        cbn in com'1. rewrite assoc. use (pathscomp0 com'1).
        use CokernelCommutes.
      + use (CokernelOutsEq to_Zero coker2). cbn.
        set (com'2 := maponpaths (fun f : _ => f ;; CokernelOut to_Zero coker e (E1 ;; h) e''1) com2).
        cbn in com'2. rewrite assoc. use (pathscomp0 com'2). rewrite <- H.
        use CokernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y0. apply isapropdirprod.
      + apply hs.
      + apply hs.
    (* Uniqueness *)
    - intros y0 t. cbn in t. induction t as [t p].
      apply (CokernelArrowisEpi to_Zero coker).
      rewrite (CokernelCommutes to_Zero coker).
      rewrite <- (CokernelCommutes to_Zero coker1 coker _ (epis_Pushout_eq1 E1 E2 BinCoprod coker)).
      rewrite <- assoc. use (pathscomp0 (maponpaths (fun f : _ => CokernelArrow coker1 ;; f) t)).
      apply idpath.
  Qed.

  Definition epis_Pushout {x y z: A} (E1 : Epi A x y) (E2 : Epi A x z) : Pushout E1 E2.
  Proof.
    set (coker1 := epi_cokernel A E1).
    set (coker2 := epi_cokernel A E2).
    set (BinCoprod := to_BinCoproducts A (AECD_Ob (to_AECD A) x y E1) (AECD_Ob (to_AECD A) x z E2)).
    set (ar := BinCoproductArrow A BinCoprod (AECD_Mor (to_AECD A) x y E1)
                                 (AECD_Mor (to_AECD A) x z E2)).
    set (coker := to_Cokernels A _ _ ar).
    use (mk_Pushout E1 E2 coker
                    (CokernelOut to_Zero coker1 coker (CokernelArrow coker)
                                 (epis_Pushout_eq1 E1 E2 BinCoprod coker))
                    (CokernelOut to_Zero coker2 coker (CokernelArrow coker)
                                 (epis_Pushout_eq2 E1 E2 BinCoprod coker))
                    (epis_Pushout_eq3 E1 E2 BinCoprod coker)
                    (epis_Pushout_isPushout E1 E2 BinCoprod coker)).
  Defined.

End abelian_monic_pullbacks.

(** * Equalizers and Coequalizers
  In the following section we show that equalizers and coequalizers exist in
  abelian categories.  *)
Section abelian_equalizers.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.


  (** ** Equalizers *)

  Definition Equalizer_isMonic {x y : A} (f : x --> y) :
    isMonic (BinProductArrow A (to_BinProducts A x y) (identity x) f).
  Proof.
    set (BinProd := to_BinProducts A x y).
    intros z h1 h2 H.
    apply (maponpaths (fun h : _ => h ;; (BinProductPr1 A BinProd))) in H.
    rewrite <- assoc in H. rewrite <- assoc in H.
    set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f).
    rewrite com1 in H.
    rewrite (id_right h1) in H. rewrite (id_right h2) in H.
    exact H.
  Qed.

  Definition Equalizer_Pullback {x y : A} (f1 f2 : x --> y) :
    Pullback (BinProductArrow A (to_BinProducts A x y) (identity x) f1)
             (BinProductArrow A (to_BinProducts A x y) (identity x) f2) :=
    monics_Pullback A hs (mk_Monic A _ (Equalizer_isMonic f1))
                    (mk_Monic A _ (Equalizer_isMonic f2)).

  Definition Equalizer_eq1 {x y : A} (f1 f2 : x --> y) :
    PullbackPr1 (Equalizer_Pullback f1 f2) = PullbackPr2 (Equalizer_Pullback f1 f2).
  Proof.
    set (BinProd := to_BinProducts A x y).
    set (ar1 := BinProductArrow A BinProd (identity x) f1).
    set (ar2 := BinProductArrow A BinProd (identity x) f2).
    set (Pb := Equalizer_Pullback f1 f2).
    assert (H1 : ar1 ;; (BinProductPr1 A BinProd) = identity x) by apply BinProductPr1Commutes.
    assert (H2 : ar2 ;; (BinProductPr1 A BinProd) = identity x) by apply BinProductPr1Commutes.
    use (pathscomp0 (!(id_right (PullbackPr1 Pb)))).
    use (pathscomp0 (!(maponpaths (fun h : _ => PullbackPr1 Pb ;; h) H1))).
    use (pathscomp0 _ ((id_right (PullbackPr2 Pb)))).
    use (pathscomp0 _ (maponpaths (fun h : _ => PullbackPr2 Pb ;; h) H2)).
    rewrite assoc. rewrite assoc. apply cancel_postcomposition.
    apply PullbackSqrCommutes.
  Qed.

  Definition Equalizer_eq2 {x y : A} (f1 f2 : x --> y) :
    PullbackPr1 (Equalizer_Pullback f1 f2) ;; f1 = PullbackPr1 (Equalizer_Pullback f1 f2) ;; f2.
  Proof.
    set (BinProd := to_BinProducts A x y).
    set (ar1 := BinProductArrow A BinProd (identity x) f1).
    set (ar2 := BinProductArrow A BinProd (identity x) f2).
    set (H := Equalizer_eq1 f1 f2).
    set (Pb := Equalizer_Pullback f1 f2).
    assert (H1 : BinProductArrow A BinProd (identity x) f1 ;; (BinProductPr2 A BinProd) = f1) by
        apply BinProductPr2Commutes.
    assert (H2 : BinProductArrow A BinProd (identity x) f2 ;; (BinProductPr2 A BinProd) = f2) by
        apply BinProductPr2Commutes.
    rewrite <- H1. rewrite <- H2. rewrite assoc. rewrite assoc.
    apply cancel_postcomposition. unfold BinProd.
    set (X := PullbackSqrCommutes (Equalizer_Pullback f1 f2)).
    rewrite <- H in X. apply X.
  Qed.

  Definition isEqualizer {x y : A} (f1 f2 : x --> y) :
    isEqualizer f1 f2 (PullbackPr1 (Equalizer_Pullback f1 f2)) (Equalizer_eq2 f1 f2).
  Proof.
    set (BinProd := to_BinProducts A x y).
    set (ar1 := BinProductArrow A BinProd (identity x) f1).
    set (ar2 := BinProductArrow A BinProd (identity x) f2).
    set (H := Equalizer_eq1 f1 f2).
    use mk_isEqualizer.
    intros w h HH.
    assert (HH' : h ;; ar1 = BinProductArrow A BinProd h (h ;; f1)).
    {
      apply (BinProductArrowUnique A _ _ BinProd).
      - rewrite <- assoc.
        set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f1).
        fold ar1 in com1. rewrite com1. apply id_right.
      - rewrite <- assoc.
        set (com2 := BinProductPr2Commutes A _ _ BinProd x (identity x) f1).
        fold ar1 in com2. rewrite com2. apply idpath.
    }
    assert (HH'' : h ;; ar2 = BinProductArrow A BinProd h (h ;; f1)).
    {
      apply (BinProductArrowUnique A _ _ BinProd).
      - rewrite <- assoc.
        set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f2).
        fold ar2 in com1. rewrite com1. apply id_right.
      - rewrite <- assoc.
        set (com2 := BinProductPr2Commutes A _ _ BinProd x (identity x) f2).
        fold ar2 in com2. rewrite com2. apply pathsinv0. apply HH.
    }
    assert (HH''' : h ;; ar1 = h ;; ar2).
    {
      rewrite HH'. rewrite HH''. apply idpath.
    }
    use unique_exists.
    (* The arrow *)
    - exact (PullbackArrow (Equalizer_Pullback f1 f2) w h h HH''').
    (* Commutativity *)
    - apply (PullbackArrow_PullbackPr1 (Equalizer_Pullback f1 f2) w h h HH''').
    (* Equality on equalities of morphisms *)
    - intros y0. apply hs.
    (* Uniqueness *)
    - intros y0 t. apply PullbackArrowUnique.
      + apply t.
      + rewrite <- H. apply t.
  Qed.

  (** Construction of the equalizer. *)
  Definition Equalizer {x y : A} (f1 f2 : x --> y) : Equalizer f1 f2 :=
    mk_Equalizer f1 f2 (PullbackPr1 (Equalizer_Pullback f1 f2)) (Equalizer_eq2 f1 f2)
                 (isEqualizer f1 f2).

  Corollary Equalizers : @Equalizers A.
  Proof.
    intros X Y f g.
    apply Equalizer.
  Defined.


  (** ** Coequalizers *)

  (** Some results we are going to need to prove existence of Coequalizers. *)
  Definition Coequalizer_isEpi {x y : A} (f : y --> x) :
    isEpi (BinCoproductArrow A (to_BinCoproducts A x y) (identity x) f).
  Proof.
    set (BinCoprod := to_BinCoproducts A x y).
    intros z h1 h2 H.
    apply (maponpaths (fun f : _ => (BinCoproductIn1 A BinCoprod) ;; f)) in H.
    rewrite assoc in H. rewrite assoc in H.
    set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f).
    rewrite com1 in H. clear com1.
    rewrite (id_left h1) in H. rewrite (id_left h2) in H.
    exact H.
  Qed.

  Definition Coequalizer_Pushout {x y : A} (f1 f2 : y --> x) :
    Pushout (BinCoproductArrow A (to_BinCoproducts A x y) (identity x) f1)
            (BinCoproductArrow A (to_BinCoproducts A x y) (identity x) f2) :=
    epis_Pushout A hs (mk_Epi A _ (Coequalizer_isEpi f1)) (mk_Epi A _ (Coequalizer_isEpi f2)).

  Definition Coequalizer_eq1 {x y : A} (f1 f2 : y --> x) :
    PushoutIn1 (Coequalizer_Pushout f1 f2) = PushoutIn2 (Coequalizer_Pushout f1 f2).
  Proof.
    set (BinCoprod := to_BinCoproducts A x y).
    set (ar1 := BinCoproductArrow A BinCoprod (identity x) f1).
    set (ar2 := BinCoproductArrow A BinCoprod (identity x) f2).
    set (Po := Coequalizer_Pushout f1 f2).
    assert (H1 : (BinCoproductIn1 A BinCoprod) ;; ar1 = identity x) by
        apply BinCoproductIn1Commutes.
    assert (H2 : (BinCoproductIn1 A BinCoprod) ;; ar2 = identity x) by
        apply BinCoproductIn1Commutes.
    use (pathscomp0 (!(id_left (PushoutIn1 Po)))).
    use (pathscomp0 (!(maponpaths (fun h : _ => h ;; PushoutIn1 Po) H1))).
    use (pathscomp0 _ ((id_left (PushoutIn2 Po)))).
    use (pathscomp0 _ (maponpaths (fun h : _ => h ;; PushoutIn2 Po) H2)).
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    apply PushoutSqrCommutes.
  Qed.

  Definition Coequalizer_eq2 {x y : A} (f1 f2 : y --> x) :
    f1 ;; PushoutIn1 (Coequalizer_Pushout f1 f2) = f2 ;; PushoutIn1 (Coequalizer_Pushout f1 f2).
  Proof.
    set (BinCoprod := to_BinCoproducts A x y).
    set (ar1 := BinCoproductArrow A BinCoprod (identity x) f1).
    set (ar2 := BinCoproductArrow A BinCoprod (identity x) f2).
    set (H := Coequalizer_eq1 f1 f2).
    set (Pb := Coequalizer_Pushout f1 f2).
    rewrite <- (BinCoproductIn2Commutes A _ _ BinCoprod _ (identity x) f1).
    rewrite <- (BinCoproductIn2Commutes A _ _ BinCoprod _ (identity x) f2).
    repeat rewrite <- assoc. apply cancel_precomposition.
    set (X := PushoutSqrCommutes (Coequalizer_Pushout f1 f2)).
    rewrite <- H in X. apply X.
  Qed.

  Definition isCoequalizer {x y : A} (f1 f2 : y --> x) :
    isCoequalizer f1 f2 (PushoutIn1 (Coequalizer_Pushout f1 f2)) (Coequalizer_eq2 f1 f2).
  Proof.
    set (BinCoprod := to_BinCoproducts A x y).
    set (ar1 := BinCoproductArrow A BinCoprod (identity x) f1).
    set (ar2 := BinCoproductArrow A BinCoprod (identity x) f2).
    set (H := Coequalizer_eq1 f1 f2).
    use mk_isCoequalizer.
    intros w h HH.
    assert (HH' : ar1 ;; h = BinCoproductArrow A BinCoprod h (f1 ;; h)).
    {
      use (BinCoproductArrowUnique A _ _ BinCoprod).
      - rewrite assoc.
        set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f1).
        fold ar1 in com1. rewrite com1. apply id_left.
      - rewrite assoc.
        set (com2 := BinCoproductIn2Commutes A _ _ BinCoprod x (identity x) f1).
        fold ar1 in com2. rewrite com2. apply idpath.
    }
    assert (HH'' : ar2 ;; h = BinCoproductArrow A BinCoprod h (f1 ;; h)).
    {
      apply (BinCoproductArrowUnique A _ _ BinCoprod).
      - rewrite assoc.
        set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f2).
        fold ar2 in com1. rewrite com1. apply id_left.
      - rewrite assoc.
        set (com2 := BinCoproductIn2Commutes A _ _ BinCoprod x (identity x) f2).
        fold ar2 in com2. rewrite com2. apply pathsinv0. apply HH.
    }
    assert (HH''' : ar1 ;; h = ar2 ;; h).
    {
      rewrite HH'. rewrite HH''. apply idpath.
    }
    use unique_exists.
    (* The arrow *)
    - exact (PushoutArrow (Coequalizer_Pushout f1 f2) w h h HH''').
    (* commutativity *)
    - apply (PushoutArrow_PushoutIn1 (Coequalizer_Pushout f1 f2) w h h HH''').
    (* Equality of equality of morphisms *)
    - intros y0. apply hs.
    (* Uniqueness *)
    - intros y0 t. apply PushoutArrowUnique.
      + apply t.
      + rewrite <- H. apply t.
  Qed.

  (** Construction of Coequalizer. *)
  Definition Coequalizer {x y : A} (f1 f2 : y --> x) :
    Coequalizer f1 f2 := mk_Coequalizer f1 f2 (PushoutIn1 (Coequalizer_Pushout f1 f2))
                                        (Coequalizer_eq2 f1 f2) (isCoequalizer f1 f2).

  Corollary Coequalizers : @Coequalizers A.
  Proof.
    intros X Y f g.
    apply Coequalizer.
  Defined.

End abelian_equalizers.


(** * Pushouts and pullbacks
  As a corollary of the above section we get that abelian categories have
  pullbacks and pushouts. *)
Section abelian_pushouts.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  Definition Pullbacks : @Pullbacks A.
  Proof.
    apply (@Pullbacks_from_Equalizers_BinProducts A hs).
    apply (to_BinProducts A).
    apply (Equalizers A hs).
  Defined.

  Definition Pushouts : @Pushouts A.
  Proof.
    apply (@Pushouts_from_Coequalizers_BinCoproducts A hs).
    apply (to_BinCoproducts A).
    apply (Coequalizers A hs).
  Defined.

End abelian_pushouts.


(** * Monic kernels and Epi cokernels
  In this section we prove that kernels of monomorphisms are given by the
  arrows from zero and cokernels of epimorphisms are given by the arrows to
  zero. *)
Section abelian_monic_kernels.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.


  (** ** KernelArrow of Monic = ArrowFromZero *)

  Definition MonicKernelZero_isKernel {x y : A} (M : Monic A x y) :
    isKernel to_Zero (ZeroArrowFrom x) M
             (ArrowsFromZero A to_Zero y (ZeroArrowFrom x ;; M) (ZeroArrow to_Zero _ _)).
  Proof.
    use (mk_isKernel hs).
    intros w h X. rewrite <- (ZeroArrow_comp_left _ _ _ _ _ M) in X.
    apply (MonicisMonic _ M) in X.
    use unique_exists.
    (* The arrow *)
    - exact (ZeroArrow to_Zero _ _).
    (* Commutativity *)
    - cbn. rewrite X. apply ZeroArrow_comp_left.
    (* Equality of equalities of morphisms *)
    - intros y0. apply hs.
    (* Uniqueness *)
    - intros y0 Y. apply ArrowsToZero.
  Qed.

  (* A kernel of a monic is the arrow from zero. *)
  Definition MonicKernelZero {x y : A} (M : Monic A x y) : Kernel to_Zero M :=
    mk_Kernel to_Zero (ZeroArrowFrom _) M _ (MonicKernelZero_isKernel M).


  (** ** CokernelArrow of Epi = Arrowto_Zero *)

  (* Hide isCoequalizer behind Qed. *)
  Definition EpiCokernelZero_isCokernel {y z : A} (E : Epi A y z) :
    isCokernel to_Zero E (ZeroArrowTo z)
             (ArrowsToZero A to_Zero y (E ;; ZeroArrowTo z) (ZeroArrow to_Zero y to_Zero)).
  Proof.
    use (mk_isCokernel hs).
    intros w h X. rewrite <- (ZeroArrow_comp_right A to_Zero y z w E) in X.
    apply (EpiisEpi _ E) in X.
    use unique_exists.
    (* The arrow *)
    - exact (ZeroArrow to_Zero _ _).
    (* Commutativity *)
    - cbn. rewrite X. apply ZeroArrow_comp_right.
    (* Equality of equalities of morphisms *)
    - intros y0. apply hs.
    (* Uniqueness *)
    - intros y0 Y. apply ArrowsFromZero.
  Qed.

  (* A cokernel of an epi is the arrow to zero. *)
  Definition EpiCokernelZero {y z : A} (E : Epi A y z) : Cokernel to_Zero E :=
    mk_Cokernel to_Zero E (ZeroArrowTo z) _ (EpiCokernelZero_isCokernel E).


  (** ** KernelArrow = FromZero ⇒ isMonic *)

  (** The following Definitions is used in the next Definition. *)
  Local Definition KernelZeroMonic_cokernel {x y : A} {f1 f2 : x --> y} (e : f1 = f2)
        (CK : Cokernel to_Zero f1) : Cokernel to_Zero f2.
  Proof.
    use mk_Cokernel.
    - exact CK.
    - exact (CokernelArrow CK).
    - induction e. apply CokernelCompZero.
    - induction e. apply (CokernelisCokernel _ CK).
  Defined.

  (** The morphism f is monic if its kernel is zero. *)
  Lemma KernelZeroisMonic {x y z : A} (f : y --> z)
        (H : ZeroArrow to_Zero x y ;; f = ZeroArrow to_Zero x z )
        (isK : isKernel to_Zero (ZeroArrow to_Zero _ _) f H) : isMonic f.
  Proof.
    intros w u v H'.
    set (Coeq := Coequalizer A hs u v).
    set (Coeqar := CoequalizerOut Coeq z f H').
    set (Coeqar_epi := CoequalizerArrowEpi Coeq).
    set (Coeq_coker := epi_cokernel A Coeqar_epi).
    set (ker := @mk_Kernel A to_Zero _ _ _ (ZeroArrow to_Zero x y) f H isK).
    assert (e0 : CokernelArrow Coeq_coker = CoequalizerArrow Coeq).
    {
      apply idpath.
    }
    assert (e1 : f = (CokernelArrow Coeq_coker) ;; Coeqar).
    {
      apply pathsinv0. rewrite e0.
      set (XX := CoequalizerCommutes Coeq z f H').
      fold Coeqar in XX.
      apply XX.
    }
    assert (e2 : (AECD_Mor (to_AECD A) _ _ Coeqar_epi) ;; f = ZeroArrow to_Zero _ _).
    {
      rewrite e1. rewrite assoc.
      rewrite CokernelCompZero.
      apply ZeroArrow_comp_left.
    }
    set (ar := KernelIn to_Zero ker (AECD_Ob (to_AECD A) _ _ Coeqar_epi)
                        (AECD_Mor (to_AECD A) _ _ Coeqar_epi) e2).
    set (com1 := KernelCommutes to_Zero ker (AECD_Ob (to_AECD A) _ _ Coeqar_epi)
                                (AECD_Mor (to_AECD A) _ _ Coeqar_epi) e2).
    assert (e3 : KernelArrow ker = ZeroArrow to_Zero _ _ ).
    {
      apply idpath.
    }
    assert (e4 : AECD_Mor (to_AECD A) y Coeq Coeqar_epi = ZeroArrow to_Zero _ _).
    {
      rewrite <- com1. apply ZeroArrow_comp_right.
    }
    assert (e5 : is_iso (CoequalizerArrow Coeq)).
    {
      set (coker2 := KernelZeroMonic_cokernel e4 Coeq_coker).
      apply (is_iso_qinv _ _ (CokernelofZeroArrow_is_iso hs to_Zero coker2)).
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

  Definition KernelZeroMonic {x y z : A} (f : y --> z)
             (H : ZeroArrow to_Zero x y ;; f = ZeroArrow to_Zero x z )
             (isK : isKernel to_Zero (ZeroArrow to_Zero _ _) f H) : Monic A y z.
  Proof.
    exact (mk_Monic A f (KernelZeroisMonic f H isK)).
  Defined.


  (** ** CokernelArrow = ToZero ⇒ isEpi *)

  (** The following Definition is used in the next Definition. *)
  Local Definition CokernelZeroEpi_kernel {x y : A} {f1 f2 : x --> y} (e : f1 = f2)
        (K : Kernel to_Zero f1) : Kernel to_Zero f2.
  Proof.
    use mk_Kernel.
    - exact K.
    - exact (KernelArrow K).
    - induction e. apply KernelCompZero.
    - induction e. apply (KernelisKernel to_Zero K).
  Defined.

  (** The morphism f is monic if its kernel is zero. *)
  Lemma CokernelZeroisEpi {x y z : A} (f : x --> y)
             (H : f ;; ZeroArrow to_Zero y z = ZeroArrow to_Zero x z )
             (isCK : isCokernel to_Zero f (ZeroArrow to_Zero _ _) H) : isEpi f.
  Proof.
    intros w u v H'.
    set (Eq := Equalizer A hs u v).
    set (Eqar := EqualizerIn Eq x f H').
    set (Eqar_monic := EqualizerArrowMonic Eq).
    set (Eq_ker := monic_kernel A Eqar_monic).
    set (coker := @mk_Cokernel A to_Zero _ _ _ f (ZeroArrow to_Zero y z) H isCK).
    assert (e0 : KernelArrow Eq_ker = EqualizerArrow Eq).
    {
      apply idpath.
    }
    assert (e1 : f = Eqar ;; (KernelArrow Eq_ker)).
    {
      apply pathsinv0. rewrite e0.
      set (XX := EqualizerCommutes Eq x f H').
      fold Eqar in XX.
      apply XX.
    }
    assert (e2 : f ;; (AMKD_Mor (to_AMKD A) _ _ Eqar_monic) = ZeroArrow to_Zero _ _).
    {
      rewrite e1. rewrite <- assoc.
      set (tmp := maponpaths (fun f : _ => Eqar ;; f) (KernelCompZero to_Zero Eq_ker)).
      use (pathscomp0 tmp).
      apply ZeroArrow_comp_right.
    }
    set (ar := CokernelOut to_Zero coker (AMKD_Ob (to_AMKD A) _ _ Eqar_monic)
                           (AMKD_Mor (to_AMKD A) _ _ Eqar_monic) e2).
    set (com1 := CokernelCommutes to_Zero coker (AMKD_Ob (to_AMKD A) _ _ Eqar_monic)
                                  (AMKD_Mor (to_AMKD A) _ _ Eqar_monic) e2).
    assert (e3 : CokernelArrow coker = ZeroArrow to_Zero _ _ ).
    {
      apply idpath.
    }
    assert (e4 : AMKD_Mor (to_AMKD A) Eq y Eqar_monic = ZeroArrow to_Zero _ _).
    {
      rewrite <- com1. apply ZeroArrow_comp_left.
    }
    assert (e5 : is_iso (EqualizerArrow Eq)).
    {
      set (ker2 := CokernelZeroEpi_kernel e4 Eq_ker).
      apply (is_iso_qinv _ _ (KernelofZeroArrow_is_iso hs to_Zero ker2)).
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

  Definition CokernelZeroEpi {x y z : A} (f : x --> y)
             (H : f ;; ZeroArrow to_Zero y z = ZeroArrow to_Zero x z)
             (isCK : isCokernel to_Zero f (ZeroArrow to_Zero _ _) H) : Epi A x y.
  Proof.
    exact (mk_Epi A f (CokernelZeroisEpi f H isCK)).
  Defined.

End abelian_monic_kernels.


(** * Factorization of morphisms
  In this section we prove that every morphism factors as Epi ;; Monic in 2
  canonical ways. To do this we need to prove that the canonical morphism
  CoIm f --> Im f is an isomorphism. *)
Section abelian_factorization.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  (** Definition of coimage and image in abelian categories. *)
  Definition Kernel {x y : A} (f : x --> y) : kernels.Kernel to_Zero f := to_Kernels A x y f.

  Definition Cokernel {x y : A} (f : x --> y) : Cokernel to_Zero f := to_Cokernels A x y f.

  Definition CoImage {x y : A} (f : x --> y) : cokernels.Cokernel to_Zero (KernelArrow (Kernel f)) :=
    to_Cokernels A _ _ (KernelArrow (Kernel f)).

  Definition Image {x y : A} (f : x --> y) : kernels.Kernel to_Zero (CokernelArrow (Cokernel f)) :=
    to_Kernels A _ _ (CokernelArrow (Cokernel f)).

  (** An equation we are going to use. *)
  Lemma CoIm_ar_eq {x y : A} (f : x --> y) : KernelArrow (Kernel f) ;; f  = ZeroArrow to_Zero  _ _.
  Proof.
    apply KernelCompZero.
  Qed.

  (** An arrow we are going to need. *)
  Definition CoIm_ar {x y : A} (f : x --> y) : A⟦CoImage f, y⟧.
  Proof.
    apply (CokernelOut to_Zero (CoImage f) y f (CoIm_ar_eq f)).
  Defined.

  (** Some equations we are going to need. *)
  Definition CoIm_to_Im_eq1 {x y : A} (f : x --> y) :
    CokernelArrow (CoImage f) ;; CoIm_ar f ;; CokernelArrow (Cokernel f) = ZeroArrow to_Zero _ _.
  Proof.
    set (tmp := CokernelCommutes to_Zero (CoImage f) y f (CoIm_ar_eq f)).
    fold (CoIm_ar f) in tmp. rewrite tmp.
    apply CokernelCompZero.
  Qed.

  Definition CoIm_to_Im_eq2 {x y : A} (f : x --> y) :
    CoIm_ar f ;; CokernelArrow (Cokernel f) = ZeroArrow to_Zero _ _.
  Proof.
    set (isE := CokernelArrowisEpi to_Zero (CoImage f)).
    set (e1 := CoIm_to_Im_eq1 f).
    rewrite <- assoc in e1.
    rewrite <- (ZeroArrow_comp_right A to_Zero _ _ _ (CokernelArrow (CoImage f))) in e1.
    apply isE in e1. exact e1.
  Qed.

  (** In this definition we construct the canonical morphism from the coimage
      of f to the image of f. *)
  Definition CoIm_to_Im {x y : A} (f : x --> y) :
    A⟦CoImage f, Image f⟧ := KernelIn to_Zero (Image f) (CoImage f) (CoIm_ar f) (CoIm_to_Im_eq2 f).

  (** The above morphism gives a way to factorize the morphism f as a composite
    of three morphisms. *)
  Definition CoIm_to_Im_eq {x y : A} (f : x --> y) :
    f = (CokernelArrow (CoImage f)) ;; (CoIm_to_Im f) ;; (KernelArrow (Image f)).
  Proof.
    unfold CoIm_to_Im.
    (* Commutativity of cokernel *)
    set (com0 := CokernelCommutes to_Zero (CoImage f) y f (CoIm_ar_eq f)).
    apply pathsinv0 in com0. use (pathscomp0 com0).
    (* Cancel precomposition *)
    rewrite <- assoc. apply cancel_precomposition.
    (* Commutativity of kernel *)
    set (com1 := KernelCommutes to_Zero (Image f) (CoImage f) (CoIm_ar f) (CoIm_to_Im_eq2 f)).
    apply pathsinv0 in com1. use (pathscomp0 com1).
    (* idpath *)
    apply idpath.
  Qed.

  (** Here we show that the canonical morphism CoIm f --> Im f is an
    isomorphism. *)
  Lemma CoIm_to_Im_is_iso {x y : A} (f : x --> y) : is_z_isomorphism (CoIm_to_Im f).
  Proof.
    (* It suffices to show that this morphism is monic and epi. *)
    use monic_epi_is_iso.
    (* isMonic *)
    - use (isMonic_postcomp A _ (KernelArrow (Image f))).
      intros z g1 g2 H.
      set (q := Coequalizer A hs g1 g2).
      set (ar := CoIm_to_Im f ;; KernelArrow (Image f)).
      set (ar1 := CoequalizerOut q _ ar).
      set (com1 := CoequalizerCommutes q _ _ H).
      assert (isE : isEpi ((CokernelArrow (CoImage f)) ;; (CoequalizerArrow q))).
      {
        apply isEpi_comp.
        apply CokernelArrowisEpi.
        apply CoequalizerArrowisEpi.
      }
      set (E := mk_Epi A ((CokernelArrow (CoImage f)) ;; (CoequalizerArrow q)) isE).
      set (coker := epi_cokernel A E).
      assert (e0 : (AECD_Mor (to_AECD A) _ _ E) ;; ((CokernelArrow (CoImage f))
                                                     ;; (CoequalizerArrow q)) =
                   ZeroArrow to_Zero _ (epi_cokernel A E)).
      {
        set (tmp := CokernelCompZero to_Zero (epi_cokernel A E)).
        rewrite <- tmp.
        apply cancel_precomposition.
        unfold E. apply idpath.
      }
      assert (e : (AECD_Mor (to_AECD A) _ _ E) ;; f = ZeroArrow to_Zero _ _).
      {
        (* Use CoImage Image equation *)
        set (tmp := CoIm_to_Im_eq f).
        apply (maponpaths (fun f : _ => AECD_Mor (to_AECD A) x q E ;; f)) in tmp.
        use (pathscomp0 tmp).
        (* rewrite com1 *)
        rewrite <- assoc. rewrite <- com1.
        (* cancel postcompostion and use e0 *)
        rewrite assoc. rewrite assoc.
        set (tmpar1 := CoIm_to_Im f ;; KernelArrow (Image f)).
        set (tmpar2 := CoequalizerOut q y tmpar1 H).
        rewrite <- (ZeroArrow_comp_left A to_Zero _ _ _ tmpar2).
        apply cancel_postcomposition.
        rewrite <- assoc.
        rewrite e0. apply idpath.
      }
      set (l := KernelIn to_Zero (Kernel f) _ _ e).
      assert (e1 : (AECD_Mor (to_AECD A) x q E) ;; (CokernelArrow (CoImage f)) =
                   ZeroArrow to_Zero _ _).
      {
        set (tmp := KernelCommutes to_Zero (Kernel f) _ _ e).
        rewrite <- tmp.
        fold l.
        rewrite <- (ZeroArrow_comp_right A to_Zero _ _ _ l).
        rewrite <- assoc.
        apply cancel_precomposition.
        unfold CoImage.
        apply CokernelCompZero.
      }
      set (ar2 := CokernelOut to_Zero coker _ _ e1).
      set (com2 := CokernelCommutes to_Zero coker _ _ e1).
      assert (e2 : CokernelArrow (CoImage f) ;; (CoequalizerArrow q) ;;
                                 (CokernelOut to_Zero coker _ _ e1)  = CokernelArrow (CoImage f)).
      {
        apply com2.
      }
      assert (e3 : (CoequalizerArrow q) ;; (CokernelOut to_Zero coker (CoImage f) _ e1)  =
                   identity _).
      {
        set (isE1 := CokernelArrowisEpi to_Zero (CoImage f)).
        unfold isEpi in isE1.
        apply isE1. rewrite assoc.
        rewrite id_right.
        apply e2.
      }
      assert (e4 : isMonic (CoequalizerArrow q)).
      {
        apply (isMonic_postcomp A _ (CokernelOut to_Zero coker (CoImage f) _ e1)).
        set (tmp := @identity_isMonic A (CoImage f)).
        rewrite <- e3 in tmp.
        apply tmp.
      }
      set (coeqeq := CoequalizerEqAr q).
      apply e4 in coeqeq.
      apply coeqeq.
    (* isEpi *)
    - use (isEpi_precomp A (CokernelArrow (CoImage f)) _).
      intros z g1 g2 H.
      set (q := Equalizer A hs g1 g2).
      set (ar := CokernelArrow (CoImage f) ;; CoIm_to_Im f).
      set (ar1 := EqualizerIn q _ ar).
      set (com1 := EqualizerCommutes q _ _ H).
      assert (isE : isMonic ((EqualizerArrow q) ;; (KernelArrow (Image f)))).
      {
        apply isMonic_comp.
        apply EqualizerArrowisMonic.
        apply KernelArrowisMonic.
      }
      set (M := mk_Monic A ((EqualizerArrow q) ;; (KernelArrow (Image f))) isE).
      set (ker := monic_kernel A M).
      assert (e0 : (EqualizerArrow q) ;; (KernelArrow (Image f)) ;; (AMKD_Mor (to_AMKD A) _ _ M) =
                   ZeroArrow to_Zero (monic_kernel A M) _).
      {
        use (pathscomp0 _ (KernelCompZero to_Zero (monic_kernel A M))).
        apply cancel_precomposition. apply idpath.
      }
      assert (e : f ;; (AMKD_Mor (to_AMKD A) _ _ M) = ZeroArrow to_Zero _ _).
      {
        (* Use CoImage Image equation *)
        set (tmp := CoIm_to_Im_eq f).
        apply (maponpaths (fun f : _ => f ;; AMKD_Mor (to_AMKD A) q y M)) in tmp.
        use (pathscomp0 tmp).
        (* rewrite com1 *)
        rewrite <- com1.
        (* cancel precomposition and rewrite e0 *)
        set (tmpar1 := CokernelArrow (CoImage f) ;; CoIm_to_Im f).
        set (tmpar2 := EqualizerIn q x tmpar1 H).
        rewrite <- (ZeroArrow_comp_right A to_Zero _ _ _ tmpar2).
        rewrite <- assoc. rewrite <- assoc.
        apply cancel_precomposition.
        rewrite assoc.
        rewrite e0. apply idpath.
      }
      set (l := CokernelOut to_Zero (Cokernel f) _ _ e).
      assert (e1 : (KernelArrow (Image f)) ;; (AMKD_Mor (to_AMKD A) q y M) = ZeroArrow to_Zero _ _).
      {
        set (tmp := CokernelCommutes to_Zero (Cokernel f) _ _ e).
        rewrite <- tmp.
        fold l.
        rewrite <- (ZeroArrow_comp_left A to_Zero _ _ _ l).
        rewrite assoc.
        apply cancel_postcomposition.
        unfold Image.
        apply KernelCompZero.
      }
      set (ar2 := KernelIn to_Zero ker _ _ e1).
      set (com2 := KernelCommutes to_Zero ker _ _ e1).
      assert (e2 : (KernelIn to_Zero ker _ _ e1) ;; (EqualizerArrow q) ;; KernelArrow (Image f) =
                   KernelArrow (Image f)).
      {
        rewrite <- com2. rewrite <- assoc.
        apply cancel_precomposition. unfold ker.
        apply idpath.
      }
      assert (e3 : (KernelIn to_Zero ker (Image f) _ e1) ;; (EqualizerArrow q)  = identity _).
      {
        set (isM1 := KernelArrowisMonic to_Zero (Image f)).
        unfold isMonic in isM1.
        apply isM1.
        rewrite id_left.
        apply e2.
      }
      assert (e4 : isEpi (EqualizerArrow q)).
      {
        apply (isEpi_precomp A (KernelIn to_Zero ker (Image f) _ e1)).
        set (tmp := @identity_isEpi A (Image f)).
        rewrite <- e3 in tmp.
        apply tmp.
      }
      set (eqeq := EqualizerEqAr q).
      apply e4 in eqeq.
      apply eqeq.
  Qed.

  (** Since an isomorphism is both a monic and an epi, there are two canonical ways to compose f as
      epi ;; monic by interpreting the isomorphism as a monic or an epi. We define both of these
      factorizations. *)

  (** In the first case we interpret the isomorphism as an epi. *)
  Lemma factorization1_is_epi {x y : A} (f : x --> y) :
    isEpi (CokernelArrow (CoImage f) ;; CoIm_to_Im f).
  Proof.
    apply isEpi_comp.
    apply CokernelArrowisEpi.
    apply (is_iso_isEpi A _ (CoIm_to_Im_is_iso f)).
  Qed.

  Definition factorization1_epi {x y : A} (f : x --> y) : Epi A x (Image f).
  Proof.
    use mk_Epi.
    exact (CokernelArrow (CoImage f) ;; CoIm_to_Im f).
    apply factorization1_is_epi.
  Defined.

  Definition factorization1_monic {x y : A} (f : x --> y) : Monic A (Image f) y.
  Proof.
    use mk_Monic.
    exact (KernelArrow (Image f)).
    apply KernelArrowisMonic.
  Defined.

  Lemma factorization1 {x y : A} (f : x --> y) :
    f = (factorization1_epi f) ;; (factorization1_monic f).
  Proof.
    use (pathscomp0 (CoIm_to_Im_eq f)).
    apply idpath.
  Qed.

  (** In the second case we interpret the isomorphism as a monic.  *)
  Lemma factorization2_is_monic {x y : A} (f : x --> y) :
    isMonic (CoIm_to_Im f ;; (KernelArrow (Image f))).
  Proof.
    apply isMonic_comp.
    apply (is_iso_isMonic A _ (CoIm_to_Im_is_iso f)).
    apply KernelArrowisMonic.
  Qed.

  Definition factorization2_monic {x y : A} (f : x --> y) : Monic A (CoImage f) y.
  Proof.
    use mk_Monic.
    exact (CoIm_to_Im f ;; (KernelArrow (Image f))).
    apply factorization2_is_monic.
  Defined.

  Definition factorization2_epi {x y : A} (f : x --> y) : Epi A x (CoImage f).
  Proof.
    use mk_Epi.
    exact (CokernelArrow (CoImage f)).
    apply CokernelArrowisEpi.
  Defined.

  Definition factorization2 {x y : A} (f : x --> y) :
    f = (factorization2_epi f) ;; (factorization2_monic f).
  Proof.
    use (pathscomp0 (CoIm_to_Im_eq f)).
    rewrite <- assoc.
    apply idpath.
  Qed.

End abelian_factorization.
Arguments factorization1 [A] _ [x] [y] _.
Arguments factorization1_is_epi [A] _ [x] [y] _ _ _ _ _.
Arguments factorization2 [A] _ [x] [y] _.
Arguments factorization2_is_monic [A] _ [x] [y] _ _ _ _ _.
Arguments CoIm_to_Im [A] [x] [y] _.
Arguments Kernel [A] [x] [y] _.
Arguments Cokernel [A] [x] [y] _.
Arguments Image [A] [x] [y] _.
Arguments CoImage [A] [x] [y] _.


(** * Monics are kernels of cokernels and Epis are cokernels of kernels
  In this section we prove that every monic is the kernel of its cokernel and
  every epi is the cokernel of its kernel. *)
Section abelian_kernel_cokernel.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  (** ** Monic is the kernel of its cokernel *)

  Lemma MonicToKernel_isMonic {x y : A} (M : Monic A x y) : isMonic (factorization1_epi A hs M).
  Proof.
    apply (isMonic_postcomp A _ (factorization1_monic A M)).
    rewrite <- (factorization1 hs M).
    apply (pr2 M).
  Qed.

  Lemma MonicToKernel_is_iso {x y : A} (M : Monic A x y) :
    is_z_isomorphism (factorization1_epi A hs M).
  Proof.
    apply monic_epi_is_iso.
    apply (MonicToKernel_isMonic M).
    apply factorization1_is_epi.
    apply hs.
  Qed.

  (** Monic is a kernel of its cokernel. *)
  Definition MonicToKernel {x y : A} (M : Monic A x y) :
    kernels.Kernel to_Zero (CokernelArrow (Cokernel M)) :=
    Kernel_up_to_iso A hs to_Zero M (CokernelArrow (Cokernel M)) (Image M)
                     (mk_z_iso (factorization1_epi A hs M) _ (MonicToKernel_is_iso M))
                     (factorization1 hs M).

  (** The following verifies that the monic M is indeed the KernelArrow. *)
  Lemma MonicToKernel_eq {x y : A} (M : Monic A x y) : KernelArrow (MonicToKernel M) = M.
  Proof.
    apply idpath.
  Qed.

  (** This generalizes the above by using any Cokernel. *)
  Definition MonicToKernel' {x y : A} (M : Monic A x y) (CK : cokernels.Cokernel to_Zero M) :
    kernels.Kernel to_Zero (CokernelArrow CK) :=
    @Kernel_up_to_iso2 A hs to_Zero _ _ _ (CokernelArrow (Cokernel M)) (CokernelArrow CK)
                      (iso_from_Cokernel_to_Cokernel to_Zero (Cokernel M) CK)
                      (CokernelCommutes _ _ _ _ _) (MonicToKernel M).

  (** The following verifies that the monic M is indeed the KernelArrow of the
    generalization. *)
  Lemma MonicToKernel_eq' {x y : A} (M : Monic A x y) (CK : cokernels.Cokernel to_Zero M) :
    KernelArrow (MonicToKernel' M CK) = M.
  Proof.
    apply idpath.
  Qed.

  (** ** Epi is the cokernel of its kernel *)

  Lemma EpiToCokernel_isEpi {x y : A} (E : Epi A x y) : isEpi (factorization2_monic A hs E).
  Proof.
    apply (isEpi_precomp A (factorization2_epi A E)).
    rewrite <- (factorization2 hs E).
    apply (pr2 E).
  Qed.

  Lemma EpiToCokernel_is_iso {x y : A} (E : Epi A x y) :
    is_z_isomorphism (factorization2_monic A hs E).
  Proof.
    apply monic_epi_is_iso.
    apply factorization2_is_monic.
    apply hs.
    apply (EpiToCokernel_isEpi E).
  Qed.

  (** Epi is a cokernel of its kernel. *)
  Definition EpiToCokernel {x y : A} (E : Epi A x y) :
    cokernels.Cokernel to_Zero (KernelArrow (Kernel E)) :=
    Cokernel_up_to_iso A hs to_Zero (KernelArrow (Kernel E)) E (CoImage E)
                       (mk_z_iso (factorization2_monic A hs E) _ (EpiToCokernel_is_iso E))
                       (factorization2 hs E).

  (** The following verifies that the epi E is indeed the CokernelArrow. *)
  Lemma EpiToCokernel_eq {x y : A} (E : Epi A x y) : CokernelArrow (EpiToCokernel E) = E.
  Proof.
    apply idpath.
  Qed.

  (** This generalizes the above by using any Kernel. *)
  Definition EpiToCokernel' {x y : A} (E : Epi A x y) (K : kernels.Kernel to_Zero E) :
    cokernels.Cokernel to_Zero (KernelArrow K) :=
    Cokernel_up_to_iso2 A hs to_Zero (KernelArrow (Kernel E)) (KernelArrow K)
                        (iso_from_Kernel_to_Kernel to_Zero K (Kernel E))
                        (KernelCommutes _ _ _ _ _) (EpiToCokernel E).

  (** The following verifies that the epi E is indeed the CokernelArrow of the
    generalization. *)
  Lemma EpiToCokernel_eq' {x y : A} (E : Epi A x y) (K : kernels.Kernel to_Zero E) :
    CokernelArrow (EpiToCokernel' E K) = E.
  Proof.
    apply idpath.
  Qed.

End abelian_kernel_cokernel.


(** * Opposite category is abelian *)
Section opp_abelian.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

  Definition AbelianData1_opp (AD1 : Data1 C) : @Data1 C^op.
  Proof.
    use mk_Data1.
    - exact (Zero_opp C (pr1 AD1)).
    - exact (BinCoproducts_opp C (pr2 (pr2 AD1))).
    - exact (BinProducts_opp C (pr1 (pr2 AD1))).
  Defined.

  Definition AbelianData2_opp {AD1 : Data1 C} (AD2 : Data2 C AD1) :
    @Data2 C^op (AbelianData1_opp AD1).
  Proof.
    use mk_Data2.
    - exact (Cokernels_opp C hs (pr1 AD1) (pr2 AD2)).
    - exact (Kernels_opp C hs (pr1 AD1) (pr1 AD2)).
  Defined.

  Local Opaque ZeroArrow.
  Lemma AbelianMonicKernelsData_opp_eq {AD1 : Data1 C} (AMKD : AbelianMonicKernelsData C AD1)
        (y z : C^op) (E : Epi (opp_precat C) y z) :
    @compose C _ _ _ E (AMKD_Mor AMKD z y (opp_Epi C E))
    = @ZeroArrow (opp_precat C) (Zero_opp C (Data1_Zero AD1)) _ _.
  Proof.
    rewrite <- ZeroArrow_opp.
    set (tmp := AMKD_Eq AMKD z y (opp_Epi C E)).
    cbn in tmp. rewrite tmp. clear tmp.
    apply ZerosArrowEq.
  Qed.

  Lemma AbelianMonicKernelsData_opp_isCokernel {AD1 : Data1 C}
        (AMKD : AbelianMonicKernelsData C AD1) (y z : C^op) (E : Epi (opp_precat C) y z) :
    isCokernel (Zero_opp C (pr1 AD1)) (AMKD_Mor AMKD z y (opp_Epi C E)) E
               (AbelianMonicKernelsData_opp_eq AMKD y z E).
  Proof.
    use (isCokernel_opp _ hs).
    - exact (Data1_Zero AD1).
    - exact (AMKD_Eq AMKD z y (opp_Epi C E)).
    - exact (AMKD_isK AMKD _ _ (opp_Epi C E)).
  Qed.

  Definition AbelianMonicKernelsData_opp {AD1 : Data1 C} (AMKD : AbelianMonicKernelsData C AD1) :
    AbelianEpiCokernelsData (C^op) (AbelianData1_opp AD1).
  Proof.
    use mk_AbelianEpiCokernelsData.
    intros y z E.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (AMKD_Ob AMKD z y (opp_Epi C E)).
        * exact (AMKD_Mor AMKD z y (opp_Epi C E)).
      + exact (AbelianMonicKernelsData_opp_eq AMKD y z E).
    - exact (AbelianMonicKernelsData_opp_isCokernel AMKD y z E).
  Defined.


  Lemma AbelianEpiCokernelsData_opp_eq {AD1 : Data1 C} (AECD : AbelianEpiCokernelsData C AD1)
        (y z : C^op) (M : Monic (opp_precat C) y z) :
    AECD_Mor AECD z y (opp_Monic C M) ;; M =
    ZeroArrow (Zero_opp C (pr1 AD1)) y (AECD_Ob AECD z y (opp_Monic C M)).
  Proof.
    rewrite <- ZeroArrow_opp. apply (AECD_Eq AECD z y (opp_Monic C M)).
  Qed.

  Lemma AbelianEpiCokernelsData_opp_isKernel {AD1 : Data1 C}
        (AECD : AbelianEpiCokernelsData C AD1) (y z : C^op) (M : Monic (opp_precat C) y z) :
    isKernel (Zero_opp C (pr1 AD1)) M (AECD_Mor AECD z y (opp_Monic C M))
             (AbelianEpiCokernelsData_opp_eq AECD y z M).
  Proof.
    use (isKernel_opp _ hs).
    - exact (Data1_Zero AD1).
    - exact (AECD_Eq AECD _ _ (opp_Monic C M)).
    - exact (AECD_isC AECD _ _ (opp_Monic C M)).
  Qed.

  Definition AbelianEpiCokernelsData_opp {AD1 : Data1 C} (AECD : AbelianEpiCokernelsData C AD1) :
    AbelianMonicKernelsData (C^op) (AbelianData1_opp AD1).
  Proof.
    use mk_AbelianMonicKernelsData.
    intros y z M.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (AECD_Ob AECD z y (opp_Monic C M) : ob C^op).
        * exact (AECD_Mor AECD z y (opp_Monic C M) : C^op⟦z, _⟧).
      + exact (AbelianEpiCokernelsData_opp_eq AECD y z M).
    - exact (AbelianEpiCokernelsData_opp_isKernel AECD y z M).
  Defined.

  Definition AbelianData_opp {AD1 : Data1 C} (AD : AbelianData C AD1) :
    AbelianData (C^op) (AbelianData1_opp AD1).
  Proof.
    use mk_AbelianData.
    - exact (AbelianData2_opp (pr1 AD)).
    - exact (AbelianEpiCokernelsData_opp (pr2 (pr2 AD))).
    - exact (AbelianMonicKernelsData_opp (pr1 (pr2 AD))).
  Defined.

  (* Need to remove C from context *)
End opp_abelian.
Section opp_abelian'.

  Definition Abelian_opp (A : AbelianPreCat) (hs : has_homsets A) : AbelianPreCat.
  Proof.
    use mk_Abelian.
    - exact (opp_precat (pr1 (pr1 A))).
    - exact (AbelianData1_opp _ (pr2 (pr1 A))).
    - exact (AbelianData_opp _ hs (pr2 A)).
  Defined.

  Lemma has_homsets_Abelian_opp {A : AbelianPreCat} (hs : has_homsets A) :
    has_homsets (Abelian_opp A hs).
  Proof.
    exact (has_homsets_opp hs).
  Qed.

End opp_abelian'.
