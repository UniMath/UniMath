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
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Section def_abelian.

  (** An abelian category has a zero object, binary (co)products, (co)kernels
    and every monic (resp. epi) is a kernel (resp. cokernel). *)
  Definition AbelianData (C : precategory) : UU := Zero C.

  Definition isAbelianMonicKernels (C : precategory)
             (AD : AbelianData C) : UU :=
    ∀ (x y : C) (M : Monic C x y),
      (∃ (z : C) (f : y --> z) (H : M ;; f = M ;; (ZeroArrow C AD y z)),
          isEqualizer f (ZeroArrow C AD y z) M H).

  Definition isAbelianEpiCokernels (C : precategory)
             (AD : AbelianData C) : UU :=
    (∀ (y z : C) (E : Epi C y z),
        (∃ (x : C) (f : x --> y) (H : f ;; E = (ZeroArrow C AD x y) ;; E),
            isCoequalizer f (ZeroArrow C AD x y) E H)).


  Definition isAbelian (C : precategory)
              (AD : AbelianData C) : UU :=
     (BinProducts C) × (BinCoproducts C)
                     × (Kernels AD) × (Cokernels AD)
                     × (isAbelianMonicKernels C AD)
                     × (isAbelianEpiCokernels C AD).

  Definition mk_isAbelian (C : precategory) (AD : AbelianData C)
              (BPr : BinProducts C) (BCPr : BinCoproducts C)
              (K : Kernels AD) (Ck : Cokernels AD)
              (MK : isAbelianMonicKernels C AD)
              (EC : isAbelianEpiCokernels C AD) :
    isAbelian C AD.
  Proof.
    exact (BPr,,(BCPr,,(K,,(Ck,,(MK,,EC))))).
  Defined.

  (** Definition of abelian categories *)
  Definition Abelian : UU :=
    Σ A : (Σ C : precategory, AbelianData C),
          isAbelian (pr1 A) (pr2 A).
  Definition Abelian_precategory (A : Abelian) :
    precategory := pr1 (pr1 A).
  Coercion Abelian_precategory :
    Abelian >-> precategory.

  Definition mk_Abelian (C : precategory)
             (AD : AbelianData C) (H : isAbelian C AD) : Abelian.
  Proof.
    exact (tpair _ (tpair _ C AD) H).
  Defined.

  Variable A : Abelian.
  Hypothesis hs : has_homsets A.

  (** Accessor functions. *)
  Definition Abelian_Zero :
    Zero A := (pr2 (pr1 A)).
  Definition Abelian_Products :
    BinProducts A := pr1 (pr2 A).
  Definition Abelian_BinCoproducts :
    BinCoproducts A := pr1 (pr2 (pr2 A)).
  Definition Abelian_Kernels :
    Kernels Abelian_Zero := pr1 (pr2 (pr2 (pr2 A))).
  Definition Abelian_Cokernels :
    Cokernels Abelian_Zero := pr1 (pr2 (pr2 (pr2 (pr2 A)))).
  Definition Abelian_isAbelianMonicKernels
    : isAbelianMonicKernels A (pr2 (pr1 A))
    := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 A))))).
  Definition Abelian_isAbelianEpiCokernels
    : isAbelianEpiCokernels A (pr2 (pr1 A))
    := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 A))))).


  (** The following definition constructs kernels from monics. *)
  Definition Abelian_MonicToKernel {x y : A} (M : Monic A x y) :
    Kernel Abelian_Zero (CokernelArrow _ (Abelian_Cokernels _ _ M)).
  Proof.
    set (AMK := Abelian_isAbelianMonicKernels x y M).
    unfold ishinh in AMK. cbn in *. unfold ishinh_UU in AMK.

    use mk_Kernel.
    exact x. exact (MonicArrow _ M).
    (* Here the goal should be hProp to be able to apply AMK. *)
  Abort.

  (** The following definition constructs cokernels from epis. *)
  Definition Abelian_EpiToCokernel {y z : A} (E : Epi A y z) :
    Cokernel Abelian_Zero (KernelArrow _ (Abelian_Kernels _ _ E)).
  Proof.
    set (AEC := Abelian_isAbelianEpiCokernels y z E).
    unfold ishinh in AEC. cbn in *. unfold ishinh_UU in AEC.

    use mk_Cokernel.
    exact z. exact (EpiArrow _ E).
    (* Here the goal should be hProp to be able to apply AEC. *)
  Abort.

End def_abelian.
