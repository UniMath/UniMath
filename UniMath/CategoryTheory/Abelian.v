(** * Abelian categories *)
(** ** Contents
- Definition of Abelian categories
- isMonic f -> isEpi f -> is_z_isomorphism f
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
- Monic is kernel of any cokernel of it, Epi is cokernel of any kernel of it
- A Abelian -> A^op Abelian
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
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
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.


(** * Definition of Abelian categories
   Abelian category is a [precategory] which has
   - A zero object
   - Binary products and binary coproducts
   - Kernels and cokernels
   - Every monic is kernel of its cokernel and every epi is cokernel of its kernel
*)
Section def_abelian.

  (** ** Data1
     - Zero
     - Binary direct products
     - Binary direct coproducts
   *)

  Definition Data1 (C : precategory) : UU := Zero C × (BinProducts C) × (BinCoproducts C).

  Definition mk_Data1 {C : precategory} (H1 : Zero C) (H2 : BinProducts C) (H3 : BinCoproducts C) :
    Data1 C := (H1,,(H2,,H3)).

  Definition to_Zero {C : precategory} (D : Data1 C) : Zero C := dirprod_pr1 D.

  Definition to_BinProducts {C : precategory} (D : Data1 C) : BinProducts C :=
    dirprod_pr1 (dirprod_pr2 D).

  Definition to_BinCoproducts {C : precategory} (D : Data1 C) : BinCoproducts C :=
    dirprod_pr2 (dirprod_pr2 D).

  (** ** Data2
     - Kernels
     - Cokernels
   *)

  Definition Data2 (C : precategory) (D1 : Data1 C) : UU :=
    (Kernels (to_Zero D1)) × (Cokernels (to_Zero D1)).

  Definition mk_Data2 {C : precategory} (D1 : Data1 C) (H1 : Kernels (to_Zero D1))
             (H2 : Cokernels (to_Zero D1)) : Data2 C D1 := dirprodpair H1 H2.

  Definition to_Kernels {C : precategory} {D1 : Data1 C} (D2 : Data2 C D1) :
    Kernels (to_Zero D1) := dirprod_pr1 D2.

  Definition to_Cokernels {C : precategory} {D1 : Data1 C} (D2 : Data2 C D1) :
    Cokernels (to_Zero D1) := dirprod_pr2 D2.

  (** ** Every monic is kernel of its cokernel *)

  Definition MonicsAreKernels (C : precategory) (D1 : Data1 C) (D2 : Data2 C D1) : UU :=
    ∏ (x y : C) (M : Monic C x y),
    isKernel (pr1 D1) M (CokernelArrow (to_Cokernels D2 x y M))
             (CokernelCompZero (to_Zero D1) (to_Cokernels D2 x y M)).

  Definition mk_MonicsAreKernels {C : precategory} (D1 : Data1 C) (D2 : Data2 C D1)
             (H : ∏ (x y : C) (M : Monic C x y),
                  isKernel (pr1 D1) M (CokernelArrow (to_Cokernels D2 x y M))
                           (CokernelCompZero (to_Zero D1) (to_Cokernels D2 x y M))) :
    MonicsAreKernels C D1 D2 := H.

  (** ** Every epi is a cokernel of its kernel *)

  Definition EpisAreCokernels (C : precategory) (D1 : Data1 C) (D2 : Data2 C D1) : UU :=
    ∏ (x y : C) (E : Epi C x y),
    isCokernel (pr1 D1) (KernelArrow (to_Kernels D2 x y E)) E
               (KernelCompZero (to_Zero D1) (to_Kernels D2 x y E)).

  Definition mk_EpisAreCokernels {C : precategory} (D1 : Data1 C) (D2 : Data2 C D1)
             (H : ∏ (x y : C) (E : Epi C x y),
                  isCokernel (pr1 D1) (KernelArrow (to_Kernels D2 x y E)) E
                             (KernelCompZero (to_Zero D1) (to_Kernels D2 x y E))) :
    EpisAreCokernels C D1 D2 := H.

  (** ** AbelianData
     - Data2
     - MonicsAreKernels
     - EpisAreCokernels
   *)

  Definition AbelianData (C : precategory) (D1 : Data1 C) : UU :=
    ∑ D2 : Data2 C D1, (MonicsAreKernels C D1 D2) × (EpisAreCokernels C D1 D2).

  Definition mk_AbelianData {C : precategory} {D1 : Data1 C} (D2 : Data2 C D1)
             (H1 : MonicsAreKernels C D1 D2) (H2 : EpisAreCokernels C D1 D2) :
    AbelianData C D1 := tpair _ D2 (dirprodpair H1 H2).

  (** ** Abelian categories *)

  Definition AbelianPreCat : UU := ∑ A : (∑ C : precategory, Data1 C), AbelianData (pr1 A) (pr2 A).

  Definition precategory_of_AbelianPreCat (A : AbelianPreCat) : precategory := pr1 (pr1 A).
  Coercion precategory_of_AbelianPreCat : AbelianPreCat >-> precategory.

  Definition mk_Abelian (C : precategory) (AD1 : Data1 C) (AD : AbelianData C AD1) :
    AbelianPreCat := tpair _ (tpair _ C AD1) AD.

  Definition to_Data1 (A : AbelianPreCat) : Data1 A := pr2 (pr1 A).
  Coercion to_Data1 : AbelianPreCat >-> Data1.

  Definition to_Data2 (A : AbelianPreCat) : Data2 A (to_Data1 A) := pr1 (pr2 A).
  Coercion to_Data2 : AbelianPreCat >-> Data2.

  Definition to_MonicsAreKernels (A : AbelianPreCat) :
    MonicsAreKernels A (to_Data1 A) (to_Data2 A) := dirprod_pr1 (pr2 (pr2 A)).

  Definition to_EpisAreCokernels (A : AbelianPreCat) :
    EpisAreCokernels A (to_Data1 A) (to_Data2 A) := dirprod_pr2 (pr2 (pr2 A)).

  Definition MonicToKernel {A : AbelianPreCat} {x y : A} (M : Monic A x y) :
    Kernel (to_Zero A) (CokernelArrow (to_Cokernels A x y M)) :=
    mk_Kernel (to_Zero A) _ _ _ (to_MonicsAreKernels A x y M).

  Definition EpiToCokernel {A : AbelianPreCat} {x y : A} (E : Epi A x y) :
    Cokernel (to_Zero A) (KernelArrow (to_Kernels A x y E)) :=
    mk_Cokernel (to_Zero A) _ _ _ (to_EpisAreCokernels A x y E).

End def_abelian.
Arguments to_Zero [C].

Bind Scope abelian_precat_scope with precategory.
Notation "0" := Zero : abelian_precat.
Delimit Scope abelian_precat_scope with precategory.

(** * isMonic f -> isEpi f -> is_z_isomorphism f
  In abelian categories morphisms which are both monic and epi are isomorphisms [monic_epi_is_iso].
*)
Section abelian_monic_epi_iso.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  Local Lemma monic_epi_is_iso_eq {x y : A} {f : x --> y} (iM : isMonic f) (iE : isEpi f) :
    identity y · (CokernelArrow (to_Cokernels A x y (mk_Monic _ _ iM))) =
    ZeroArrow (to_Zero A) y (to_Cokernels A x y (mk_Monic _ _ iM)).
  Proof.
    rewrite id_left. apply iE.
    set (p0 := KernelCompZero _ (MonicToKernel (mk_Monic _ _ iM))).
    rewrite <- (ZeroArrow_comp_right _ _ _ _ _ f) in p0.
    exact p0.
  Qed.

  Lemma monic_epi_is_iso_inverses {x y : A} {f : x --> y} (iM : isMonic f) (iE : isEpi f) :
    is_inverse_in_precat
      f (KernelIn (to_Zero A) (MonicToKernel (mk_Monic A f iM)) y (identity y)
                  (monic_epi_is_iso_eq iM iE)).
  Proof.
    use mk_is_inverse_in_precat.
    - apply iM. cbn. rewrite <- assoc.
      rewrite (KernelCommutes (to_Zero A) (MonicToKernel (mk_Monic A f iM))).
      rewrite id_right. rewrite id_left.
      apply idpath.
    - exact (KernelCommutes (to_Zero A) (MonicToKernel (mk_Monic A f iM)) _ _ _).
  Qed.

  Lemma monic_epi_is_iso {x y : A} {f : x --> y} : isMonic f -> isEpi f -> is_z_isomorphism f.
  Proof.
    intros iM iE.
    use mk_is_z_isomorphism.
    - exact (KernelIn (to_Zero A) (MonicToKernel (mk_Monic _ _ iM)) y (identity y)
                      (monic_epi_is_iso_eq iM iE)).
    - exact (monic_epi_is_iso_inverses iM iE).
  Defined.

  Lemma monic_epi_z_iso {x y : A} {f : x --> y} : isMonic f -> isEpi f -> z_iso x y.
  Proof.
    intros iM iE.
    use mk_z_iso.
    - exact f.
    - exact (KernelIn (to_Zero A) (MonicToKernel (mk_Monic _ _ iM)) y (identity y)
                      (monic_epi_is_iso_eq iM iE)).
    - exact (monic_epi_is_iso_inverses iM iE).
  Defined.

End abelian_monic_epi_iso.


(** * Pullbacks of monics and pushouts of epis
  In the following section we prove that an abelian category has pullbacks of monics and pushouts of
  epis.
*)
Section abelian_monic_pullbacks.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  (** ** Pullbacks of monics *)

  Local Lemma monics_Pullback_eq1 {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (to_Cokernels A x z M1) (to_Cokernels A y z M2))
             (ker : Kernel (to_Zero A)
                           (BinProductArrow A BinProd (CokernelArrow (to_Cokernels A x z M1))
                                            (CokernelArrow (to_Cokernels A y z M2)))) :
    KernelArrow ker · (CokernelArrow (to_Cokernels A x z M1)) = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (tmp := BinProductPr1Commutes
                  A _ _ BinProd _ (CokernelArrow (to_Cokernels A x z M1))
                  (CokernelArrow (to_Cokernels A y z M2))).
    apply (maponpaths (λ h : _, KernelArrow ker · h)) in tmp.
    apply (pathscomp0 (!tmp)). clear tmp.
    rewrite assoc. rewrite (KernelCompZero (to_Zero A) ker).
    apply ZeroArrow_comp_left.
  Qed.

  Local Lemma monics_Pullback_eq2 {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (to_Cokernels A x z M1) (to_Cokernels A y z M2))
             (ker : Kernel (to_Zero A) (BinProductArrow
                                      A BinProd (CokernelArrow (to_Cokernels A x z M1))
                                      (CokernelArrow (to_Cokernels A y z M2)))) :
    KernelArrow ker · (CokernelArrow (to_Cokernels A y z M2)) = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (tmp := BinProductPr2Commutes
                  A _ _ BinProd _ (CokernelArrow (to_Cokernels A x z M1))
                  (CokernelArrow (to_Cokernels A y z M2))).
    apply (maponpaths (λ h : _, KernelArrow ker · h)) in tmp.
    apply (pathscomp0 (!tmp)). clear tmp.
    rewrite assoc. rewrite (KernelCompZero (to_Zero A) ker).
    apply ZeroArrow_comp_left.
  Qed.

  Local Lemma monics_Pullback_eq3 {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z)
        (BinProd : BinProductCone A (to_Cokernels A x z M1) (to_Cokernels A y z M2))
        (ker : Kernel (to_Zero A)
                      (BinProductArrow
                         A BinProd (CokernelArrow (to_Cokernels A x z M1))
                         (CokernelArrow (to_Cokernels A y z M2)))) :
    KernelIn (to_Zero A) (MonicToKernel M1) ker (KernelArrow ker)
             (monics_Pullback_eq1 M1 M2 BinProd ker) · M1 =
    KernelIn (to_Zero A) (MonicToKernel M2) ker (KernelArrow ker)
             (monics_Pullback_eq2 M1 M2 BinProd ker) · M2.
  Proof.
    rewrite (KernelCommutes (to_Zero A) (MonicToKernel M1) _ (KernelArrow ker)).
    rewrite (KernelCommutes (to_Zero A) (MonicToKernel M2) _ (KernelArrow ker)).
    apply idpath.
  Qed.

  Local Lemma monics_Pullback_isPullback {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z)
             (BinProd : BinProductCone A (to_Cokernels A x z M1) (to_Cokernels A y z M2))
             (ker : Kernel (to_Zero A) (BinProductArrow
                                          A BinProd (CokernelArrow (to_Cokernels A x z M1))
                                          (CokernelArrow (to_Cokernels A y z M2)))) :
    isPullback M1 M2 (KernelIn (to_Zero A) (MonicToKernel M1) ker (KernelArrow ker)
                               (monics_Pullback_eq1 M1 M2 BinProd ker))
               (KernelIn (to_Zero A) (MonicToKernel M2) ker (KernelArrow ker)
                         (monics_Pullback_eq2 M1 M2 BinProd ker))
               (monics_Pullback_eq3 M1 M2 BinProd ker).
  Proof.
    (* variables *)
    set (ker1 := MonicToKernel M1).
    set (ker2 := MonicToKernel M2).
    set (ar := BinProductArrow A BinProd (CokernelArrow (to_Cokernels A x z M1))
                               (CokernelArrow (to_Cokernels A y z M2))).
    assert (com1 : KernelIn (to_Zero A) ker1 ker (KernelArrow ker)
                            (monics_Pullback_eq1 M1 M2 BinProd ker) · M1 = KernelArrow ker).
    {
      apply (KernelCommutes (to_Zero A) ker1 _ (KernelArrow ker)).
    }
    assert (com2 : KernelIn (to_Zero A) ker2 ker (KernelArrow ker)
                            (monics_Pullback_eq2 M1 M2 BinProd ker) · M2 = KernelArrow ker).
    {
      apply (KernelCommutes (to_Zero A) ker2 _ (KernelArrow ker)).
    }
    (* isPullback *)
    use mk_isPullback.
    intros e h k H.
    (* First we show that h · M1 · ar = ZeroArrow by uniqueness of the morphism to product. *)
    assert (e1 : h · (KernelArrow ker1) · (CokernelArrow (to_Cokernels A x z M1)) =
                 ZeroArrow (to_Zero A) _ _).
    {
      rewrite <- assoc.
      set (ee1 := KernelCompZero (to_Zero A) ker1). cbn in ee1. cbn. rewrite ee1.
      apply ZeroArrow_comp_right.
    }
    assert (e2 : k · (KernelArrow ker2) · (CokernelArrow (to_Cokernels A y z M2)) =
                 ZeroArrow (to_Zero A) _ _).
    {
      rewrite <- assoc.
      set (ee2 := KernelCompZero (to_Zero A) ker2). cbn in ee2. cbn. rewrite ee2.
      apply ZeroArrow_comp_right.
    }
    cbn in e1, e2.
    assert (e'1 : h · M1 · (CokernelArrow (to_Cokernels A y z M2)) = ZeroArrow (to_Zero A) _ _).
    {
      rewrite H. apply e2.
    }
    assert (e''1 : h · M1 · ar = ZeroArrow (to_Zero A) _ _).
    {
      rewrite (BinProductArrowEta A _ _ BinProd e (h · M1 · ar)).
      use BinProductArrowZero.
      - rewrite <- assoc.
        set (tmp1 := BinProductPr1Commutes
                       A _ _ BinProd _ (CokernelArrow (to_Cokernels A x z M1))
                       (CokernelArrow (to_Cokernels A y z M2))).
        fold ar in tmp1. rewrite tmp1. apply e1.
      - rewrite <- assoc.
        set (tmp1 := BinProductPr2Commutes
                       A _ _ BinProd _ (CokernelArrow (to_Cokernels A x z M1))
                       (CokernelArrow (to_Cokernels A y z M2))).
        fold ar in tmp1. rewrite tmp1. apply e'1.
    }
    use unique_exists.
    (* The arrow *)
    - use (KernelIn (to_Zero A) ker e (h · M1)). apply e''1.
    (* commutativity *)
    - split.
      + use (KernelInsEq (to_Zero A) ker1).  cbn. rewrite <- assoc.
        set (com'1 := maponpaths (λ f : _, KernelIn (to_Zero A) ker e (h · M1) e''1 · f) com1).
        cbn in com'1. use (pathscomp0 com'1). use KernelCommutes.
      + use (KernelInsEq (to_Zero A) ker2). cbn. rewrite <- assoc.
        set (com'2 := maponpaths (λ f : _, KernelIn (to_Zero A) ker e (h · M1) e''1 · f) com2).
        cbn in com'2. use (pathscomp0 com'2). rewrite <- H. use KernelCommutes.
    (* Equality of equalities of morphisms *)
    - intros y0. apply isapropdirprod.
      + apply hs.
      + apply hs.
    (* Uniqueness *)
    - intros y0 t. cbn in t. induction t as [t p].
      apply (KernelArrowisMonic (to_Zero A) ker).
      rewrite (KernelCommutes (to_Zero A) ker).
      rewrite <- (KernelCommutes (to_Zero A) ker1 ker _ (monics_Pullback_eq1 M1 M2 BinProd ker)).
      rewrite assoc. use (pathscomp0 (maponpaths (λ f : _, f · KernelArrow ker1) t)).
      apply idpath.
  Qed.

  (** Construction of the Pullback of monics. *)
  Definition monics_Pullback {x y z : A} (M1 : Monic A x z) (M2 : Monic A y z) : Pullback M1 M2.
  Proof.
    set (ker1 := MonicToKernel M1).
    set (ker2 := MonicToKernel M2).
    set (BinProd := to_BinProducts A (to_Cokernels A x z M1) (to_Cokernels A y z M2)).
    set (ar := BinProductArrow A BinProd (CokernelArrow (to_Cokernels A x z M1))
                               (CokernelArrow (to_Cokernels A y z M2))).
    set (ker := to_Kernels A _ _ ar).
    use (mk_Pullback M1 M2 ker
           (KernelIn (to_Zero A) ker1 ker (KernelArrow ker) (monics_Pullback_eq1 M1 M2 BinProd ker))
           (KernelIn (to_Zero A) ker2 ker (KernelArrow ker) (monics_Pullback_eq2 M1 M2 BinProd ker))
           (monics_Pullback_eq3 M1 M2 BinProd ker) (monics_Pullback_isPullback M1 M2 BinProd ker)).
  Defined.


  (** ** Pushouts of epis *)

  Definition epis_Pushout_eq1 {x y z : A} (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone
                            A (to_Kernels A x y E1) (to_Kernels A x z E2))
             (coker : Cokernel (to_Zero A) (BinCoproductArrow
                                          A BinCoprod (KernelArrow (to_Kernels A x y E1))
                                          (KernelArrow (to_Kernels A x z E2))))  :
    (KernelArrow (to_Kernels A x y E1)) · CokernelArrow coker =
    ZeroArrow (to_Zero A) (to_Kernels A x y E1) coker.
  Proof.
    set (tmp := BinCoproductIn1Commutes
                  A _ _ BinCoprod _ (KernelArrow (to_Kernels A x y E1))
                  (KernelArrow (to_Kernels A x z E2))).
    apply (maponpaths (λ h : _, h · CokernelArrow coker)) in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite <- assoc. rewrite (CokernelCompZero (to_Zero A) coker).
    apply ZeroArrow_comp_right.
  Qed.

  Definition epis_Pushout_eq2 {x y z : A} (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone
                            A (to_Kernels A x y E1) (to_Kernels A x z E2))
             (coker : Cokernel (to_Zero A) (BinCoproductArrow
                                          A BinCoprod (KernelArrow (to_Kernels A x y E1))
                                          (KernelArrow (to_Kernels A x z E2)))) :
    (KernelArrow (to_Kernels A x z E2)) · CokernelArrow coker =
    ZeroArrow (to_Zero A) (to_Kernels A x z E2) coker.
  Proof.
    set (tmp := BinCoproductIn2Commutes
                  A _ _ BinCoprod _ (KernelArrow (to_Kernels A x y E1))
                  (KernelArrow (to_Kernels A x z E2))).
    apply (maponpaths (λ h : _, h · CokernelArrow coker)) in tmp.
    apply (pathscomp0 (!tmp)).
    rewrite <- assoc. rewrite (CokernelCompZero (to_Zero A) coker).
    apply ZeroArrow_comp_right.
  Qed.

  Definition epis_Pushout_eq3 {x y z : A} (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone
                            A (to_Kernels A x y E1) (to_Kernels A x z E2))
             (coker : Cokernel (to_Zero A) (BinCoproductArrow
                                          A BinCoprod (KernelArrow (to_Kernels A x y E1))
                                          (KernelArrow (to_Kernels A x z E2)))) :
    E1 · (CokernelOut (to_Zero A) (EpiToCokernel E1) coker (CokernelArrow coker)
                       (epis_Pushout_eq1 E1 E2 BinCoprod coker)) =
    E2 · (CokernelOut (to_Zero A) (EpiToCokernel E2) coker (CokernelArrow coker)
                       (epis_Pushout_eq2 E1 E2 BinCoprod coker)).
  Proof.
    rewrite (CokernelCommutes (to_Zero A) (EpiToCokernel E1) _ (CokernelArrow coker)).
    rewrite (CokernelCommutes (to_Zero A) (EpiToCokernel E2) _ (CokernelArrow coker)).
    apply idpath.
  Qed.

  Definition epis_Pushout_isPushout {x y z : A} (E1 : Epi A x y) (E2 : Epi A x z)
             (BinCoprod : BinCoproductCocone
                            A (to_Kernels A x y E1) (to_Kernels A x z E2))
             (coker : Cokernel (to_Zero A) (BinCoproductArrow
                                          A BinCoprod (KernelArrow (to_Kernels A x y E1))
                                          (KernelArrow (to_Kernels A x z E2)))) :
    isPushout E1 E2 (CokernelOut (to_Zero A) (EpiToCokernel E1) coker (CokernelArrow coker)
                                 (epis_Pushout_eq1 E1 E2 BinCoprod coker))
              (CokernelOut (to_Zero A) (EpiToCokernel E2) coker (CokernelArrow coker)
                           (epis_Pushout_eq2 E1 E2 BinCoprod coker))
              (epis_Pushout_eq3 E1 E2 BinCoprod coker).
  Proof.
    set (coker1 := EpiToCokernel E1).
    set (coker2 := EpiToCokernel E2).
    set (ar := BinCoproductArrow
                 A BinCoprod (KernelArrow (to_Kernels A x y E1))
                 (KernelArrow (to_Kernels A x z E2))).
    assert (com1 : E1 · (CokernelOut (to_Zero A) coker1 coker (CokernelArrow coker)
                                      (epis_Pushout_eq1 E1 E2 BinCoprod coker)) =
                   CokernelArrow coker).
    {
      apply (CokernelCommutes (to_Zero A) coker1 _ (CokernelArrow coker)).
    }
    assert (com2 : E2 · (CokernelOut (to_Zero A) coker2 coker (CokernelArrow coker)
                                      (epis_Pushout_eq2 E1 E2 BinCoprod coker)) =
                   CokernelArrow coker).
    {
      apply (CokernelCommutes (to_Zero A) coker2 _ (CokernelArrow coker)).
    }
    (* isPushout *)
    use mk_isPushout.
    intros e h k H.
    (* First we show that h · M1 · ar = ZeroArrow by uniqueness of the morphism to product. *)
    assert (e1 : (KernelArrow (to_Kernels A x y E1)) · (CokernelArrow coker1) · h =
                 ZeroArrow (to_Zero A) _ _).
    {
      set (ee1 := CokernelCompZero (to_Zero A) coker1). cbn in ee1. cbn. rewrite ee1.
      apply ZeroArrow_comp_left.
    }
    assert (e2 : (KernelArrow (to_Kernels A x z E2)) · (CokernelArrow coker2) · k =
                 ZeroArrow (to_Zero A) _ _).
    {
      set (ee2 := CokernelCompZero (to_Zero A) coker2). cbn in ee2. cbn. rewrite ee2.
      apply ZeroArrow_comp_left.
    }
    cbn in e1, e2.
    assert (e'1 : (KernelArrow (to_Kernels A x z E2)) · E1 · h = ZeroArrow (to_Zero A) _ _).
    {
      rewrite <- assoc. rewrite H. rewrite assoc. apply e2.
    }
    assert (e'2 : (KernelArrow (to_Kernels A x y E1)) · E2 · k = ZeroArrow (to_Zero A) _ _).
    {
      rewrite <- assoc. rewrite <- H. rewrite assoc. apply e1.
    }
    assert (e''1 : ar · (E1 · h) = ZeroArrow (to_Zero A) _ _).
    {
      rewrite assoc. rewrite (BinCoproductArrowEta A _ _ BinCoprod e (ar · E1 · h)).
      use BinCoproductArrowZero.
      - rewrite assoc. rewrite assoc.
        set (tmp1 := BinCoproductIn1Commutes
                       A _ _ BinCoprod _ (KernelArrow (to_Kernels A x y E1))
                       (KernelArrow (to_Kernels A x z E2))).
        fold ar in tmp1. rewrite tmp1. apply e1.
      - rewrite assoc. rewrite assoc.
        set (tmp1 := BinCoproductIn2Commutes
                       A _ _ BinCoprod _ (KernelArrow (to_Kernels A x y E1))
                       (KernelArrow (to_Kernels A x z E2))).
        fold ar in tmp1. rewrite tmp1. apply e'1.
    }
    use unique_exists.
    (* The arrow *)
    - use (CokernelOut (to_Zero A) coker e (E1 · h)). apply e''1.
    (* Commutativity *)
    - split.
      + use (CokernelOutsEq (to_Zero A) coker1). cbn.
        set (com'1 := maponpaths
                        (λ f : _, f · CokernelOut (to_Zero A) coker e (E1 · h) e''1) com1).
        cbn in com'1. rewrite assoc. use (pathscomp0 com'1).
        use CokernelCommutes.
      + use (CokernelOutsEq (to_Zero A) coker2). cbn.
        set (com'2 := maponpaths
                        (λ f : _, f · CokernelOut (to_Zero A) coker e (E1 · h) e''1) com2).
        cbn in com'2. rewrite assoc. use (pathscomp0 com'2). rewrite <- H.
        use CokernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y0. apply isapropdirprod.
      + apply hs.
      + apply hs.
    (* Uniqueness *)
    - intros y0 t. cbn in t. induction t as [t p].
      apply (CokernelArrowisEpi (to_Zero A) coker).
      rewrite (CokernelCommutes (to_Zero A) coker).
      rewrite <- (CokernelCommutes
                   (to_Zero A) coker1 coker _ (epis_Pushout_eq1 E1 E2 BinCoprod coker)).
      rewrite <- assoc. use (pathscomp0 (maponpaths (λ f : _, CokernelArrow coker1 · f) t)).
      apply idpath.
  Qed.

  Definition epis_Pushout {x y z: A} (E1 : Epi A x y) (E2 : Epi A x z) : Pushout E1 E2.
  Proof.
    set (coker1 := EpiToCokernel E1).
    set (coker2 := EpiToCokernel E2).
    set (BinCoprod := to_BinCoproducts A (to_Kernels A x y E1) (to_Kernels A x z E2)).
    set (ar := BinCoproductArrow A BinCoprod (KernelArrow (to_Kernels A x y E1))
                                 (KernelArrow (to_Kernels A x z E2))).
    set (coker := to_Cokernels A _ _ ar).
    use (mk_Pushout E1 E2 coker
                    (CokernelOut (to_Zero A) coker1 coker (CokernelArrow coker)
                                 (epis_Pushout_eq1 E1 E2 BinCoprod coker))
                    (CokernelOut (to_Zero A) coker2 coker (CokernelArrow coker)
                                 (epis_Pushout_eq2 E1 E2 BinCoprod coker))
                    (epis_Pushout_eq3 E1 E2 BinCoprod coker)
                    (epis_Pushout_isPushout E1 E2 BinCoprod coker)).
  Defined.

End abelian_monic_pullbacks.

(** * Equalizers and Coequalizers
  In the following section we show that equalizers and coequalizers exist in abelian categories.
*)
Section abelian_equalizers.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.


  (** ** Equalizers *)

  Definition Equalizer_isMonic {x y : A} (f : x --> y) :
    isMonic (BinProductArrow A (to_BinProducts A x y) (identity x) f).
  Proof.
    set (BinProd := to_BinProducts A x y).
    intros z h1 h2 H.
    apply (maponpaths (λ h : _, h · (BinProductPr1 A BinProd))) in H.
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
    assert (H1 : ar1 · (BinProductPr1 A BinProd) = identity x) by apply BinProductPr1Commutes.
    assert (H2 : ar2 · (BinProductPr1 A BinProd) = identity x) by apply BinProductPr1Commutes.
    use (pathscomp0 (! (id_right (PullbackPr1 Pb)))).
    use (pathscomp0 (! (maponpaths (λ h : _, PullbackPr1 Pb · h) H1))).
    use (pathscomp0 _ ((id_right (PullbackPr2 Pb)))).
    use (pathscomp0 _ (maponpaths (λ h : _, PullbackPr2 Pb · h) H2)).
    rewrite assoc. rewrite assoc. apply cancel_postcomposition.
    apply PullbackSqrCommutes.
  Qed.

  Definition Equalizer_eq2 {x y : A} (f1 f2 : x --> y) :
    PullbackPr1 (Equalizer_Pullback f1 f2) · f1 = PullbackPr1 (Equalizer_Pullback f1 f2) · f2.
  Proof.
    set (BinProd := to_BinProducts A x y).
    set (ar1 := BinProductArrow A BinProd (identity x) f1).
    set (ar2 := BinProductArrow A BinProd (identity x) f2).
    set (H := Equalizer_eq1 f1 f2).
    set (Pb := Equalizer_Pullback f1 f2).
    assert (H1 : BinProductArrow A BinProd (identity x) f1 · (BinProductPr2 A BinProd) = f1) by
        apply BinProductPr2Commutes.
    assert (H2 : BinProductArrow A BinProd (identity x) f2 · (BinProductPr2 A BinProd) = f2) by
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
    assert (HH' : h · ar1 = BinProductArrow A BinProd h (h · f1)).
    {
      apply (BinProductArrowUnique A _ _ BinProd).
      - rewrite <- assoc.
        set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f1).
        fold ar1 in com1. rewrite com1. apply id_right.
      - rewrite <- assoc.
        set (com2 := BinProductPr2Commutes A _ _ BinProd x (identity x) f1).
        fold ar1 in com2. rewrite com2. apply idpath.
    }
    assert (HH'' : h · ar2 = BinProductArrow A BinProd h (h · f1)).
    {
      apply (BinProductArrowUnique A _ _ BinProd).
      - rewrite <- assoc.
        set (com1 := BinProductPr1Commutes A _ _ BinProd x (identity x) f2).
        fold ar2 in com1. rewrite com1. apply id_right.
      - rewrite <- assoc.
        set (com2 := BinProductPr2Commutes A _ _ BinProd x (identity x) f2).
        fold ar2 in com2. rewrite com2. apply pathsinv0. apply HH.
    }
    assert (HH''' : h · ar1 = h · ar2).
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

  Definition Equalizer {x y : A} (f1 f2 : x --> y) : Equalizer f1 f2 :=
    mk_Equalizer f1 f2 (PullbackPr1 (Equalizer_Pullback f1 f2)) (Equalizer_eq2 f1 f2)
                 (isEqualizer f1 f2).

  Corollary Equalizers : @Equalizers A.
  Proof.
    intros X Y f g.
    apply Equalizer.
  Defined.


  (** ** Coequalizers *)

  Definition Coequalizer_isEpi {x y : A} (f : y --> x) :
    isEpi (BinCoproductArrow A (to_BinCoproducts A x y) (identity x) f).
  Proof.
    set (BinCoprod := to_BinCoproducts A x y).
    intros z h1 h2 H.
    apply (maponpaths (λ f : _, (BinCoproductIn1 A BinCoprod) · f)) in H.
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
    assert (H1 : (BinCoproductIn1 A BinCoprod) · ar1 = identity x) by
        apply BinCoproductIn1Commutes.
    assert (H2 : (BinCoproductIn1 A BinCoprod) · ar2 = identity x) by
        apply BinCoproductIn1Commutes.
    use (pathscomp0 (!(id_left (PushoutIn1 Po)))).
    use (pathscomp0 (!(maponpaths (λ h : _, h · PushoutIn1 Po) H1))).
    use (pathscomp0 _ ((id_left (PushoutIn2 Po)))).
    use (pathscomp0 _ (maponpaths (λ h : _, h · PushoutIn2 Po) H2)).
    rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
    apply PushoutSqrCommutes.
  Qed.

  Definition Coequalizer_eq2 {x y : A} (f1 f2 : y --> x) :
    f1 · PushoutIn1 (Coequalizer_Pushout f1 f2) = f2 · PushoutIn1 (Coequalizer_Pushout f1 f2).
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
    assert (HH' : ar1 · h = BinCoproductArrow A BinCoprod h (f1 · h)).
    {
      use (BinCoproductArrowUnique A _ _ BinCoprod).
      - rewrite assoc.
        set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f1).
        fold ar1 in com1. rewrite com1. apply id_left.
      - rewrite assoc.
        set (com2 := BinCoproductIn2Commutes A _ _ BinCoprod x (identity x) f1).
        fold ar1 in com2. rewrite com2. apply idpath.
    }
    assert (HH'' : ar2 · h = BinCoproductArrow A BinCoprod h (f1 · h)).
    {
      apply (BinCoproductArrowUnique A _ _ BinCoprod).
      - rewrite assoc.
        set (com1 := BinCoproductIn1Commutes A _ _ BinCoprod x (identity x) f2).
        fold ar2 in com1. rewrite com1. apply id_left.
      - rewrite assoc.
        set (com2 := BinCoproductIn2Commutes A _ _ BinCoprod x (identity x) f2).
        fold ar2 in com2. rewrite com2. apply pathsinv0. apply HH.
    }
    assert (HH''' : ar1 · h = ar2 · h).
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
  Abelian categories have pullbacks and pushouts.
*)
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
  In this section we prove that kernels of monomorphisms are given by the arrows from zero and
  cokernels of epimorphisms are given by the arrows to zero.
*)
Section abelian_MonicToKernels.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.


  (** ** KernelArrow of Monic x --> y = (to_Zero A) --> x *)

  Definition MonicKernelZero_isKernel {x y : A} (M : Monic A x y) :
  isKernel (to_Zero A) (ZeroArrowFrom x) M
           (ArrowsFromZero A (to_Zero A) y (ZeroArrowFrom x · M) (ZeroArrow (to_Zero A) _ _)).
  Proof.
    use (mk_isKernel hs).
    intros w h X. rewrite <- (ZeroArrow_comp_left _ _ _ _ _ M) in X.
    apply (MonicisMonic _ M) in X.
    use unique_exists.
    (* The arrow *)
    - exact (ZeroArrow (to_Zero A) _ _).
    (* Commutativity *)
    - cbn. rewrite X. apply ZeroArrow_comp_left.
    (* Equality of equalities of morphisms *)
    - intros y0. apply hs.
    (* Uniqueness *)
    - intros y0 Y. apply ArrowsToZero.
  Qed.

  (* A kernel of a monic is the arrow from zero. *)
  Definition MonicKernelZero {x y : A} (M : Monic A x y) : Kernel (to_Zero A) M :=
    mk_Kernel (to_Zero A) (ZeroArrowFrom _) M _ (MonicKernelZero_isKernel M).


  (** ** CokernelArrow of Epi x --> y = y --> (to_Zero A) *)

  Definition EpiCokernelZero_isCokernel {y z : A} (E : Epi A y z) :
    isCokernel (to_Zero A) E (ZeroArrowTo z)
               (ArrowsToZero A (to_Zero A) y (E · ZeroArrowTo z)
                             (ZeroArrow (to_Zero A) y (to_Zero A))).
  Proof.
    use (mk_isCokernel hs).
    intros w h X. rewrite <- (ZeroArrow_comp_right A (to_Zero A) y z w E) in X.
    apply (EpiisEpi _ E) in X.
    use unique_exists.
    (* The arrow *)
    - exact (ZeroArrow (to_Zero A) _ _).
    (* Commutativity *)
    - cbn. rewrite X. apply ZeroArrow_comp_right.
    (* Equality of equalities of morphisms *)
    - intros y0. apply hs.
    (* Uniqueness *)
    - intros y0 Y. apply ArrowsFromZero.
  Qed.

  (* A cokernel of an epi is the arrow to zero. *)
  Definition EpiCokernelZero {y z : A} (E : Epi A y z) : Cokernel (to_Zero A) E :=
    mk_Cokernel (to_Zero A) E (ZeroArrowTo z) _ (EpiCokernelZero_isCokernel E).


  (** ** KernelArrow = FromZero ⇒ isMonic *)

  (** The following Definitions is used in the next Definition. *)
  Local Definition KernelZeroMonic_cokernel {x y : A} {f1 f2 : x --> y} (e : f1 = f2)
        (CK : Cokernel (to_Zero A) f1) : Cokernel (to_Zero A) f2.
  Proof.
    use mk_Cokernel.
    - exact CK.
    - exact (CokernelArrow CK).
    - induction e. apply CokernelCompZero.
    - induction e. apply (CokernelisCokernel _ CK).
  Defined.

  (** The morphism f is monic if its kernel is zero. *)
  Lemma KernelZeroisMonic {x y z : A} (f : y --> z)
        (H : ZeroArrow (to_Zero A) x y · f = ZeroArrow (to_Zero A) x z )
        (isK : isKernel (to_Zero A) (ZeroArrow (to_Zero A) _ _) f H) : isMonic f.
  Proof.
    intros w u v H'.
    set (Coeq := Coequalizer A hs u v).
    set (Coeqar := CoequalizerOut Coeq z f H').
    set (Coeqar_epi := CoequalizerArrowEpi Coeq).
    set (Coeq_coker := EpiToCokernel Coeqar_epi).
    set (ker := @mk_Kernel A (to_Zero A) _ _ _ (ZeroArrow (to_Zero A) x y) f H isK).
    assert (e0 : CokernelArrow Coeq_coker = CoequalizerArrow Coeq).
    {
      apply idpath.
    }
    assert (e1 : f = (CokernelArrow Coeq_coker) · Coeqar).
    {
      apply pathsinv0. rewrite e0.
      set (XX := CoequalizerCommutes Coeq z f H').
      fold Coeqar in XX.
      apply XX.
    }
    assert (e2 : (KernelArrow (to_Kernels A _ _ Coeqar_epi)) · f = ZeroArrow (to_Zero A) _ _).
    {
      rewrite e1. rewrite assoc.
      rewrite CokernelCompZero.
      apply ZeroArrow_comp_left.
    }
    set (ar := KernelIn (to_Zero A) ker (to_Kernels A _ _ Coeqar_epi)
                        (KernelArrow (to_Kernels A _ _ Coeqar_epi))).
    set (com1 := KernelCommutes (to_Zero A) ker (to_Kernels A _ _ Coeqar_epi)
                                (KernelArrow (to_Kernels A _ _ Coeqar_epi)) e2).
    assert (e3 : KernelArrow ker = ZeroArrow (to_Zero A) _ _ ).
    {
      apply idpath.
    }
    assert (e4 : (KernelArrow (to_Kernels A _ _ Coeqar_epi)) = ZeroArrow (to_Zero A) _ _).
    {
      rewrite <- com1. apply ZeroArrow_comp_right.
    }
    assert (e5 : is_iso (CoequalizerArrow Coeq)).
    {
      set (coker2 := KernelZeroMonic_cokernel e4 Coeq_coker).
      apply (is_iso_qinv _ _ (CokernelofZeroArrow_is_iso hs (to_Zero A) coker2)).
    }
    set (isoar := isopair (CoequalizerArrow Coeq) e5).
    set (coeq_eq := CoequalizerEqAr Coeq).
    apply (maponpaths (λ f : _, f · inv_from_iso isoar)) in coeq_eq.
    rewrite <- assoc in coeq_eq. rewrite <- assoc in coeq_eq.
    assert(areq : CoequalizerArrow Coeq = isoar). apply idpath.
    rewrite areq in coeq_eq.
    rewrite (iso_inv_after_iso isoar) in coeq_eq.
    rewrite <- id_right. rewrite <- coeq_eq. apply pathsinv0.
    apply id_right.
  Qed.

  Definition KernelZeroMonic {x y z : A} (f : y --> z)
             (H : ZeroArrow (to_Zero A) x y · f = ZeroArrow (to_Zero A) x z )
             (isK : isKernel (to_Zero A) (ZeroArrow (to_Zero A) _ _) f H) : Monic A y z.
  Proof.
    exact (mk_Monic A f (KernelZeroisMonic f H isK)).
  Defined.


  (** ** CokernelArrow = ToZero ⇒ isEpi *)

  (** The following Definition is used in the next Definition. *)
  Local Definition CokernelZeroEpi_kernel {x y : A} {f1 f2 : x --> y} (e : f1 = f2)
        (K : Kernel (to_Zero A) f1) : Kernel (to_Zero A) f2.
  Proof.
    use mk_Kernel.
    - exact K.
    - exact (KernelArrow K).
    - induction e. apply KernelCompZero.
    - induction e. apply (KernelisKernel (to_Zero A) K).
  Defined.

  (** The morphism f is monic if its kernel is zero. *)
  Lemma CokernelZeroisEpi {x y z : A} (f : x --> y)
             (H : f · ZeroArrow (to_Zero A) y z = ZeroArrow (to_Zero A) x z )
             (isCK : isCokernel (to_Zero A) f (ZeroArrow (to_Zero A) _ _) H) : isEpi f.
  Proof.
    intros w u v H'.
    set (Eq := Equalizer A hs u v).
    set (Eqar := EqualizerIn Eq x f H').
    set (Eqar_monic := EqualizerArrowMonic Eq).
    set (Eq_ker := MonicToKernel Eqar_monic).
    set (coker := @mk_Cokernel A (to_Zero A) _ _ _ f (ZeroArrow (to_Zero A) y z) H isCK).
    assert (e0 : KernelArrow Eq_ker = EqualizerArrow Eq).
    {
      apply idpath.
    }
    assert (e1 : f = Eqar · (KernelArrow Eq_ker)).
    {
      apply pathsinv0. rewrite e0.
      set (XX := EqualizerCommutes Eq x f H').
      fold Eqar in XX.
      apply XX.
    }
    assert (e2 : f · (CokernelArrow (to_Cokernels A _ _ Eqar_monic)) = ZeroArrow (to_Zero A) _ _).
    {
      rewrite e1. rewrite <- assoc.
      set (tmp := maponpaths (λ f : _, Eqar · f) (KernelCompZero (to_Zero A) Eq_ker)).
      use (pathscomp0 tmp).
      apply ZeroArrow_comp_right.
    }
    set (ar := CokernelOut (to_Zero A) coker (to_Cokernels A _ _ Eqar_monic)
                           (CokernelArrow (to_Cokernels A _ _ Eqar_monic)) e2).
    set (com1 := CokernelCommutes (to_Zero A) coker (to_Cokernels A _ _ Eqar_monic)
                                  (CokernelArrow (to_Cokernels A _ _ Eqar_monic)) e2).
    assert (e3 : CokernelArrow coker = ZeroArrow (to_Zero A) _ _ ).
    {
      apply idpath.
    }
    assert (e4 : (CokernelArrow (to_Cokernels A _ _ Eqar_monic)) = ZeroArrow (to_Zero A) _ _).
    {
      rewrite <- com1. apply ZeroArrow_comp_left.
    }
    assert (e5 : is_iso (EqualizerArrow Eq)).
    {
      set (ker2 := CokernelZeroEpi_kernel e4 Eq_ker).
      apply (is_iso_qinv _ _ (KernelofZeroArrow_is_iso hs (to_Zero A) ker2)).
    }
    set (isoar := isopair (EqualizerArrow Eq) e5).
    set (Eq_eq := EqualizerEqAr Eq).
    apply (maponpaths (λ f : _, inv_from_iso isoar · f)) in Eq_eq.
    rewrite assoc in Eq_eq. rewrite assoc in Eq_eq.
    assert(areq : EqualizerArrow Eq = isoar). apply idpath.
    rewrite areq in Eq_eq.
    rewrite (iso_after_iso_inv isoar) in Eq_eq.
    rewrite <- id_left. rewrite <- Eq_eq. apply pathsinv0.
    apply id_left.
  Qed.

  Definition CokernelZeroEpi {x y z : A} (f : x --> y)
             (H : f · ZeroArrow (to_Zero A) y z = ZeroArrow (to_Zero A) x z)
             (isCK : isCokernel (to_Zero A) f (ZeroArrow (to_Zero A) _ _) H) : Epi A x y.
  Proof.
    exact (mk_Epi A f (CokernelZeroisEpi f H isCK)).
  Defined.

End abelian_MonicToKernels.


(** * Factorization of morphisms
  In this section we prove that every morphism factors as Epi · Monic in 2 canonical ways. To do
  this we need to prove that the canonical morphism CoIm f --> Im f is an isomorphism.
*)
Section abelian_factorization.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  (** ** Kernels, Cokernels, CoImage, and Image *)

  Definition Kernel {x y : A} (f : x --> y) : kernels.Kernel (to_Zero A) f := to_Kernels A x y f.

  Definition Cokernel {x y : A} (f : x --> y) : Cokernel (to_Zero A) f := to_Cokernels A x y f.

  Definition CoImage {x y : A} (f : x --> y) :
    cokernels.Cokernel (to_Zero A) (KernelArrow (Kernel f)) :=
    to_Cokernels A _ _ (KernelArrow (Kernel f)).

  Definition Image {x y : A} (f : x --> y) :
    kernels.Kernel (to_Zero A) (CokernelArrow (Cokernel f)) :=
    to_Kernels A _ _ (CokernelArrow (Cokernel f)).

  (** ** Construction of the morphism CoIm f --> Im f *)

  Lemma CoIm_ar_eq {x y : A} (f : x --> y) :
    KernelArrow (Kernel f) · f  = ZeroArrow (to_Zero A) _ _.
  Proof.
    apply KernelCompZero.
  Qed.

  Definition CoIm_ar {x y : A} (f : x --> y) : A⟦CoImage f, y⟧.
  Proof.
    apply (CokernelOut (to_Zero A) (CoImage f) y f (CoIm_ar_eq f)).
  Defined.

  Definition CoIm_to_Im_eq1 {x y : A} (f : x --> y) :
    CokernelArrow (CoImage f) · CoIm_ar f · CokernelArrow (Cokernel f) = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (tmp := CokernelCommutes (to_Zero A) (CoImage f) y f (CoIm_ar_eq f)).
    fold (CoIm_ar f) in tmp. rewrite tmp.
    apply CokernelCompZero.
  Qed.

  Definition CoIm_to_Im_eq2 {x y : A} (f : x --> y) :
    CoIm_ar f · CokernelArrow (Cokernel f) = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (isE := CokernelArrowisEpi (to_Zero A) (CoImage f)).
    set (e1 := CoIm_to_Im_eq1 f).
    rewrite <- assoc in e1.
    rewrite <- (ZeroArrow_comp_right A (to_Zero A) _ _ _ (CokernelArrow (CoImage f))) in e1.
    apply isE in e1. exact e1.
  Qed.

  Definition CoIm_to_Im {x y : A} (f : x --> y) :
    A⟦CoImage f, Image f⟧ :=
    KernelIn (to_Zero A) (Image f) (CoImage f) (CoIm_ar f) (CoIm_to_Im_eq2 f).

  (** ** f = (x --> CoIm f) · (CoIm f --> Im f) · (Im f --> y) *)
  Definition CoIm_to_Im_eq {x y : A} (f : x --> y) :
    f = (CokernelArrow (CoImage f)) · (CoIm_to_Im f) · (KernelArrow (Image f)).
  Proof.
    unfold CoIm_to_Im.
    (* Commutativity of cokernel *)
    set (com0 := CokernelCommutes (to_Zero A) (CoImage f) y f (CoIm_ar_eq f)).
    apply pathsinv0 in com0. use (pathscomp0 com0).
    (* Cancel precomposition *)
    rewrite <- assoc. apply cancel_precomposition.
    (* Commutativity of kernel *)
    set (com1 := KernelCommutes (to_Zero A) (Image f) (CoImage f) (CoIm_ar f) (CoIm_to_Im_eq2 f)).
    apply pathsinv0 in com1. use (pathscomp0 com1).
    (* idpath *)
    apply idpath.
  Qed.

  (** ** CoIm f --> Im f is an isomorphism. *)
  Lemma CoIm_to_Im_is_iso {x y : A} (f : x --> y) : is_z_isomorphism (CoIm_to_Im f).
  Proof.
    (* It suffices to show that this morphism is monic and epi. *)
    use monic_epi_is_iso.
    (* isMonic *)
    - use (isMonic_postcomp A _ (KernelArrow (Image f))).
      intros z g1 g2 H.
      set (q := Coequalizer A hs g1 g2).
      set (ar := CoIm_to_Im f · KernelArrow (Image f)).
      set (ar1 := CoequalizerOut q _ ar).
      set (com1 := CoequalizerCommutes q _ _ H).
      assert (isE : isEpi ((CokernelArrow (CoImage f)) · (CoequalizerArrow q))).
      {
        apply isEpi_comp.
        apply CokernelArrowisEpi.
        apply CoequalizerArrowisEpi.
      }
      set (E := mk_Epi A ((CokernelArrow (CoImage f)) · (CoequalizerArrow q)) isE).
      set (coker := EpiToCokernel E).
      assert (e0 : (KernelArrow (to_Kernels A _ _ E))
                     · ((CokernelArrow (CoImage f)) · (CoequalizerArrow q)) =
                   ZeroArrow (to_Zero A) _ (EpiToCokernel E)).
      {
        set (tmp := CokernelCompZero (to_Zero A) (EpiToCokernel E)).
        rewrite <- tmp.
        apply cancel_precomposition.
        unfold E. apply idpath.
      }
      assert (e : (KernelArrow (to_Kernels A _ _ E)) · f = ZeroArrow (to_Zero A) _ _).
      {
        (* Use CoImage Image equation *)
        set (tmp := CoIm_to_Im_eq f).
        apply (maponpaths (λ f : _, (KernelArrow (to_Kernels A _ _ E)) · f)) in tmp.
        use (pathscomp0 tmp).
        (* rewrite com1 *)
        rewrite <- assoc. rewrite <- com1.
        (* cancel postcompostion and use e0 *)
        rewrite assoc. rewrite assoc.
        set (tmpar1 := CoIm_to_Im f · KernelArrow (Image f)).
        set (tmpar2 := CoequalizerOut q y tmpar1 H).
        rewrite <- (ZeroArrow_comp_left A (to_Zero A) _ _ _ tmpar2).
        apply cancel_postcomposition.
        rewrite <- assoc.
        rewrite e0. apply idpath.
      }
      set (l := KernelIn (to_Zero A) (Kernel f) _ _ e).
      assert (e1 : (KernelArrow (to_Kernels A _ _ E)) · (CokernelArrow (CoImage f)) =
                   ZeroArrow (to_Zero A) _ _).
      {
        set (tmp := KernelCommutes (to_Zero A) (Kernel f) _ _ e).
        rewrite <- tmp.
        fold l.
        rewrite <- (ZeroArrow_comp_right A (to_Zero A) _ _ _ l).
        rewrite <- assoc.
        apply cancel_precomposition.
        unfold CoImage.
        apply CokernelCompZero.
      }
      set (ar2 := CokernelOut (to_Zero A) coker _ _ e1).
      set (com2 := CokernelCommutes (to_Zero A) coker _ _ e1).
      assert (e2 : CokernelArrow (CoImage f) · (CoequalizerArrow q) ·
                                 (CokernelOut (to_Zero A) coker _ _ e1) =
                   CokernelArrow (CoImage f)).
      {
        apply com2.
      }
      assert (e3 : (CoequalizerArrow q) · (CokernelOut (to_Zero A) coker (CoImage f) _ e1) =
                   identity _).
      {
        set (isE1 := CokernelArrowisEpi (to_Zero A) (CoImage f)).
        unfold isEpi in isE1.
        apply isE1. rewrite assoc.
        rewrite id_right.
        apply e2.
      }
      assert (e4 : isMonic (CoequalizerArrow q)).
      {
        apply (isMonic_postcomp A _ (CokernelOut (to_Zero A) coker (CoImage f) _ e1)).
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
      set (ar := CokernelArrow (CoImage f) · CoIm_to_Im f).
      set (ar1 := EqualizerIn q _ ar).
      set (com1 := EqualizerCommutes q _ _ H).
      assert (isE : isMonic ((EqualizerArrow q) · (KernelArrow (Image f)))).
      {
        apply isMonic_comp.
        apply EqualizerArrowisMonic.
        apply KernelArrowisMonic.
      }
      set (M := mk_Monic A ((EqualizerArrow q) · (KernelArrow (Image f))) isE).
      set (ker := MonicToKernel M).
      assert (e0 : (EqualizerArrow q)
                     · (KernelArrow (Image f)) · (CokernelArrow (to_Cokernels A _ _ M)) =
                   ZeroArrow (to_Zero A) (MonicToKernel M) _).
      {
        use (pathscomp0 _ (KernelCompZero (to_Zero A) (MonicToKernel M))).
        apply cancel_precomposition. apply idpath.
      }
      assert (e : f · (CokernelArrow (to_Cokernels A _ _ M)) = ZeroArrow (to_Zero A) _ _).
      {
        (* Use CoImage Image equation *)
        set (tmp := CoIm_to_Im_eq f).
        apply (maponpaths (λ f : _, f · (CokernelArrow (to_Cokernels A _ _ M)))) in tmp.
        use (pathscomp0 tmp).
        (* rewrite com1 *)
        rewrite <- com1.
        (* cancel precomposition and rewrite e0 *)
        set (tmpar1 := CokernelArrow (CoImage f) · CoIm_to_Im f).
        set (tmpar2 := EqualizerIn q x tmpar1 H).
        rewrite <- (ZeroArrow_comp_right A (to_Zero A) _ _ _ tmpar2).
        rewrite <- assoc. rewrite <- assoc.
        apply cancel_precomposition.
        rewrite assoc.
        rewrite e0. apply idpath.
      }
      set (l := CokernelOut (to_Zero A) (Cokernel f) _ _ e).
      assert (e1 : (KernelArrow (Image f)) · (CokernelArrow (to_Cokernels A _ _ M)) =
                   ZeroArrow (to_Zero A) _ _).
      {
        set (tmp := CokernelCommutes (to_Zero A) (Cokernel f) _ _ e).
        rewrite <- tmp.
        fold l.
        rewrite <- (ZeroArrow_comp_left A (to_Zero A) _ _ _ l).
        rewrite assoc.
        apply cancel_postcomposition.
        unfold Image.
        apply KernelCompZero.
      }
      set (ar2 := KernelIn (to_Zero A) ker _ _ e1).
      set (com2 := KernelCommutes (to_Zero A) ker _ _ e1).
      assert (e2 : (KernelIn (to_Zero A) ker _ _ e1) · (EqualizerArrow q) · KernelArrow (Image f) =
                   KernelArrow (Image f)).
      {
        rewrite <- com2. rewrite <- assoc.
        apply cancel_precomposition. unfold ker.
        apply idpath.
      }
      assert (e3 : (KernelIn (to_Zero A) ker (Image f) _ e1) · (EqualizerArrow q)  = identity _).
      {
        set (isM1 := KernelArrowisMonic (to_Zero A) (Image f)).
        unfold isMonic in isM1.
        apply isM1.
        rewrite id_left.
        apply e2.
      }
      assert (e4 : isEpi (EqualizerArrow q)).
      {
        apply (isEpi_precomp A (KernelIn (to_Zero A) ker (Image f) _ e1)).
        set (tmp := @identity_isEpi A (Image f)).
        rewrite <- e3 in tmp.
        apply tmp.
      }
      set (eqeq := EqualizerEqAr q).
      apply e4 in eqeq.
      apply eqeq.
  Qed.

  (** ** f = Epi ((x --> CoIm f) · (CoIm f --> Im f)) · Monic (Im f --> y) *)

  Lemma factorization1_is_epi {x y : A} (f : x --> y) :
    isEpi (CokernelArrow (CoImage f) · CoIm_to_Im f).
  Proof.
    apply isEpi_comp.
    apply CokernelArrowisEpi.
    apply (is_iso_isEpi A _ (CoIm_to_Im_is_iso f)).
  Qed.

  Definition factorization1_epi {x y : A} (f : x --> y) : Epi A x (Image f).
  Proof.
    use mk_Epi.
    exact (CokernelArrow (CoImage f) · CoIm_to_Im f).
    apply factorization1_is_epi.
  Defined.

  Definition factorization1_monic {x y : A} (f : x --> y) : Monic A (Image f) y.
  Proof.
    use mk_Monic.
    exact (KernelArrow (Image f)).
    apply KernelArrowisMonic.
  Defined.

  Lemma factorization1 {x y : A} (f : x --> y) :
    f = (factorization1_epi f) · (factorization1_monic f).
  Proof.
    use (pathscomp0 (CoIm_to_Im_eq f)).
    apply idpath.
  Qed.

  (** ** f = Epi ((x --> CoIm f)) · Monic ((CoIm f --> Im f) · (Im f --> y)) *)

  Lemma factorization2_is_monic {x y : A} (f : x --> y) :
    isMonic (CoIm_to_Im f · (KernelArrow (Image f))).
  Proof.
    apply isMonic_comp.
    apply (is_iso_isMonic A _ (CoIm_to_Im_is_iso f)).
    apply KernelArrowisMonic.
  Qed.

  Definition factorization2_monic {x y : A} (f : x --> y) : Monic A (CoImage f) y.
  Proof.
    use mk_Monic.
    exact (CoIm_to_Im f · (KernelArrow (Image f))).
    apply factorization2_is_monic.
  Defined.

  Definition factorization2_epi {x y : A} (f : x --> y) : Epi A x (CoImage f).
  Proof.
    use mk_Epi.
    exact (CokernelArrow (CoImage f)).
    apply CokernelArrowisEpi.
  Defined.

  Definition factorization2 {x y : A} (f : x --> y) :
    f = (factorization2_epi f) · (factorization2_monic f).
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


Section abelian_kernel_cokernel.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  Definition MonicToKernel' {x y : A} (M : Monic A x y) (CK : cokernels.Cokernel (to_Zero A) M) :
    kernels.Kernel (to_Zero A) (CokernelArrow CK) :=
    @Kernel_up_to_iso2 A hs (to_Zero A) _ _ _ (CokernelArrow (Cokernel M)) (CokernelArrow CK)
                       (iso_from_Cokernel_to_Cokernel (to_Zero A) (Cokernel M) CK)
                       (CokernelCommutes _ _ _ _ _) (MonicToKernel M).

  Definition EpiToCokernel' {x y : A} (E : Epi A x y) (K : kernels.Kernel (to_Zero A) E) :
    cokernels.Cokernel (to_Zero A) (KernelArrow K) :=
    Cokernel_up_to_iso2 A hs (to_Zero A) (KernelArrow (Kernel E)) (KernelArrow K)
                        (iso_from_Kernel_to_Kernel (to_Zero A) K (Kernel E))
                        (KernelCommutes _ _ _ _ _) (EpiToCokernel E).

End abelian_kernel_cokernel.


(** * A Abelian -> A^op Abelian, [Abelian_opp] *)
Section opp_abelian.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

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

  Lemma MonicsAreKernels_opp_eq {D1 : Data1 C} {D2 : Data2 C D1}
        (AMKD : MonicsAreKernels C D1 D2) (y z : C^op) (E : Epi (opp_precat C) y z) :
    @compose C _ _ _ E (CokernelArrow ((to_Cokernels D2) z y (opp_Epi C E)))
    = @ZeroArrow (opp_precat C) (Zero_opp C (to_Zero D1)) _ _.
  Proof.
    rewrite <- ZeroArrow_opp.
    set (tmp := KernelCompZero (to_Zero D1) (mk_Kernel _ _ _ _ (AMKD z y (opp_Epi C E)))).
    cbn in tmp. cbn. rewrite tmp. clear tmp.
    apply ZerosArrowEq.
  Qed.

  Lemma MonicsAreKernels_opp_isCokernel {D1 : Data1 C} {D2 : Data2 C D1}
        (AMKD : MonicsAreKernels C D1 D2) (y z : C^op) (E : Epi (opp_precat C) y z) :
    isCokernel (Zero_opp C (pr1 D1)) (CokernelArrow (pr2 D2 z y (opp_Epi C E))) E
               (MonicsAreKernels_opp_eq AMKD y z E).
  Proof.
    use (isCokernel_opp _ hs).
    - exact (to_Zero D1).
    - exact (CokernelCompZero _ (to_Cokernels D2 z y (opp_Epi C E))).
    - exact (AMKD _ _ (opp_Epi C E)).
  Qed.

  Definition MonicsAreKernels_opp {D1 : Data1 C} {D2 : Data2 C D1}
             (AMKD : MonicsAreKernels C D1 D2) :
    EpisAreCokernels (C^op) (AbelianData1_opp D1) (AbelianData2_opp D2).
  Proof.
    use mk_EpisAreCokernels.
    intros y z E.
    exact (MonicsAreKernels_opp_isCokernel AMKD y z E).
  Defined.

  Lemma EpisAreCokernels_opp_eq {D1 : Data1 C} {D2 : Data2 C D1}
        (AECD : EpisAreCokernels C D1 D2) (y z : C^op)
        (M : Monic (opp_precat C) y z) :
    (KernelArrow (pr1 D2 z y (opp_Monic C M))) · M =
    ZeroArrow (Zero_opp C (to_Zero D1)) y (to_Kernels D2 z y (opp_Monic C M)).
  Proof.
    rewrite <- ZeroArrow_opp.
    apply (KernelCompZero (to_Zero D1) (to_Kernels D2 z y (opp_Monic C M))).
  Qed.

  Lemma EpisAreCokernels_opp_isKernel {D1 : Data1 C} {D2 : Data2 C D1}
        (AECD : EpisAreCokernels C D1 D2) (y z : C^op) (M : Monic (opp_precat C) y z) :
    isKernel (Zero_opp C (to_Zero D1)) M (KernelArrow (to_Kernels D2 z y (opp_Monic C M)))
             (EpisAreCokernels_opp_eq AECD y z M).
  Proof.
    use (isKernel_opp _ hs).
    - exact (to_Zero D1).
    - exact (KernelCompZero _ (to_Kernels D2 z y (opp_Monic C M))).
    - exact (AECD _ _ (opp_Monic C M)).
  Qed.

  Definition EpisAreCokernels_opp {D1 : Data1 C} {D2 : Data2 C D1}
             (AECD : EpisAreCokernels C D1 D2) :
    MonicsAreKernels (C^op) (AbelianData1_opp D1) (AbelianData2_opp D2).
  Proof.
    use mk_MonicsAreKernels.
    intros y z M.
    exact (EpisAreCokernels_opp_isKernel AECD y z M).
  Defined.

  Definition AbelianData_opp {AD1 : Data1 C} (AD : AbelianData C AD1) :
    AbelianData (C^op) (AbelianData1_opp AD1).
  Proof.
    use mk_AbelianData.
    - exact (AbelianData2_opp (pr1 AD)).
    - exact (EpisAreCokernels_opp (pr2 (pr2 AD))).
    - exact (MonicsAreKernels_opp (pr1 (pr2 AD))).
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
