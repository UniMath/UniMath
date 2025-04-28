(**

  The Univalent Category of Abelian Groups

  This file shows properties of the category of abelian groups, which is defined in Magma.v. For
  example, it shows that the category is univalent.

  The category has an additive structure. The trivial abelian group is its zero object, with the
  zero arrows given by 0(x) = 0. Pointwise addition (f + g)(x) = f x + g x gives a binary operation
  on the morphisms and the direct product of abelian groups gives a direct sum.

  The category has kernels and cokernels, with the cokernel of f: A → B given by B / Im f.

  In this category, one can formulate more directly what it means to be a kernel: for morphisms
  f : X → Y and g : Y → Z, if f · g = 0, if f is monic and if the fiber above any element in Y that
  maps to 0 : Z is inhabited, X is the kernel of g.

  Contents
  1. The univalent category of abelian groups [abelian_group_univalent_category]
  2. The additive structure
  2.1. The abelian group structure on homsets [abgr_WithAbGrops]
  2.2. The preadditive structure [abgr_PreAdditive]
  2.3. The zero object [abgr_Zero]
  2.4. Direct sums [abgr_isBinDirectSum]
  2.5. The additive structure [abgr_Additive]
  3. Kernels and Cokernels
  3.1. Kernels [abgr_Kernels]
  3.2. Cokernels [abgr_Cokernels]
  4. Monics are inclusions and Epis are surjections
  4.1. Epis are surjections [abgr_epi_issurjective]
  4.2. Monics are inclusions [abgr_monic_isInjective]
  5. Monics are kernels of their cokernels and epis are cokernels of their kernels
  5.1. Monics are Kernels [abgr_monic_kernel]
  5.2. Epis are Cokernels [abgr_epi_cokernel]
  6. The category of abelian groups is an abelian category [abgr_Abelian]
  7. An elementwise criterion for isKernel [abgr_isKernel_Criteria]

 *)
Require Import UniMath.Foundations.All.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Monoids.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.

Require Import UniMath.CategoryTheory.Limits.Zero.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Kernels.
Require Import UniMath.CategoryTheory.Limits.Cokernels.
Require Import UniMath.CategoryTheory.Limits.BinDirectSums.

Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.Product.

Require Import UniMath.CategoryTheory.Categories.Magma.
Require Import UniMath.CategoryTheory.Categories.Group.

Local Open Scope cat.
Local Open Scope addmonoid.
Local Open Scope abgr.

(** * 1. The univalent category of abelian groups *)

Definition is_univalent_abelian_group_disp_cat
  : is_univalent_disp abelian_group_disp_cat
  := dirprod_disp_cat_is_univalent _ _
    is_univalent_group_disp_cat
    is_univalent_abelian_magma_disp_cat.

Definition is_univalent_abelian_group_category
  : is_univalent abelian_group_category
  := is_univalent_total_category
    is_univalent_magma_category
    is_univalent_abelian_group_disp_cat.

Definition abelian_group_univalent_category
  : univalent_category
  := make_univalent_category abelian_group_category is_univalent_abelian_group_category.

(** * 2. The additive structure *)
(** ** 2.1. The abelian group structure on homsets *)

Definition abgr_WithBinOpsData : precategoryWithBinOpsData abelian_group_category.
Proof.
  exact @abgrshombinop.
Defined.

Definition abgr_WithBinOps : precategoryWithBinOps :=
  make_precategoryWithBinOps abelian_group_category abgr_WithBinOpsData.

Definition abgr_WithAbGrops : categoryWithAbgrops.
Proof.
  use make_categoryWithAbgrops.
  - exact abgr_WithBinOps.
  - apply make_categoryWithAbgropsData.
    exact @abgrshomabgr_isabgrop.
Defined.

(** ** 2.2. The preadditive structure *)

Definition abgr_isPreAdditive : isPreAdditive abgr_WithAbGrops.
Proof.
  apply make_isPreAdditive.
  (* Precomposition with morphism is linear *)
  - intros X Y Z f.
    apply make_ismonoidfun.
    + apply make_isbinopfun. intros g h. apply abelian_group_morphism_eq. intros x. reflexivity.
    + apply abelian_group_morphism_eq. intros x. reflexivity.
  (* Postcomposition with morphism is linear *)
  - intros X Y Z f.
    apply make_ismonoidfun.
    + apply make_isbinopfun. intros g h. apply abelian_group_morphism_eq. intros x.
      refine (monoidfunmul (f : abelian_group_morphism _ _) _ _ @ _).
      reflexivity.
    + apply abelian_group_morphism_eq. intros x. exact (monoidfununel (f : abelian_group_morphism _ _)).
Qed.

Definition abgr_PreAdditive : PreAdditive :=
  make_PreAdditive abgr_WithAbGrops abgr_isPreAdditive.

(** ** 2.3. The zero object *)

Section def_abgr_zero.

  Lemma isconnectedfromunitabgr (a : abelian_group_category) (t : abelian_group_morphism unitabgr a):
    t = unel_abelian_group_morphism unitabgr (a : abgr).
  Proof.
    apply abelian_group_morphism_eq. intros x.
    refine (_ @ monoidfununel t). apply maponpaths. apply isProofIrrelevantUnit.
  Qed.

  Lemma isconnectedtounitabgr (a : abelian_group_category) (t : abelian_group_morphism a unitabgr):
    t = unel_abelian_group_morphism a unitabgr.
  Proof.
    apply abelian_group_morphism_eq. intros x. apply isProofIrrelevantUnit.
  Qed.

  Definition abgr_isZero : isZero unitabgr.
  Proof.
    apply make_isZero.
    - intros a. use make_iscontr.
      + exact (unel_abelian_group_morphism _ a).
      + intros t. exact (isconnectedfromunitabgr a t).
    - intros a. use make_iscontr.
      + exact (unel_abelian_group_morphism a _).
      + intros t. exact (isconnectedtounitabgr a t).
  Defined.

  Definition abgr_Zero : Zero abelian_group_category := make_Zero unitabgr abgr_isZero.

  Lemma abgr_Zero_arrow_comp (A B : abgr) :
    ZeroArrow abgr_Zero A B = unel_abelian_group_morphism A B.
  Proof.
    apply abelian_group_morphism_eq. intros x. reflexivity.
  Qed.

End def_abgr_zero.

(** ** 2.4. Direct sums *)

Section DirectSums.

  Lemma abgr_DirectSumPr1_isbinopfun (A B : abgr) :
    isbinopfun (λ X : abgrdirprod A B, dirprod_pr1 X).
  Proof.
    intros x x'. reflexivity.
  Qed.

  Definition abgr_DirectSumPr1 (A B : abgr) : abelian_group_category⟦abgrdirprod A B, A⟧ :=
    make_abelian_group_morphism _ (abgr_DirectSumPr1_isbinopfun A B).

  Lemma abgr_DirectSumPr2_isbinopfun (A B : abgr) :
    isbinopfun (λ X : abgrdirprod A B, dirprod_pr2 X).
  Proof.
    intros x x'. reflexivity.
  Qed.

  Definition abgr_DirectSumPr2 (A B : abgr) : abelian_group_category⟦abgrdirprod A B, B⟧ :=
    make_abelian_group_morphism _ (abgr_DirectSumPr2_isbinopfun A B).

  Lemma abgr_DirectSumIn1_isbinopfun (A B : abgr) :
    isbinopfun (Y := abgrdirprod A B) (λ a, make_dirprod a 0).
  Proof.
    intros x x'.
    apply dirprod_paths.
      + reflexivity.
      + symmetry. apply (runax B).
  Qed.

  Definition abgr_DirectSumIn1 (A B : abgr) : abelian_group_category⟦A, abgrdirprod A B⟧ :=
    make_abelian_group_morphism _ (abgr_DirectSumIn1_isbinopfun A B).

  Lemma abgr_DirectSumIn2_isbinopfun (A B : abgr) :
    isbinopfun (Y := abgrdirprod A B) (λ b, make_dirprod 0 b).
  Proof.
    intros x x'. apply dirprod_paths.
    + symmetry. apply (runax A).
    + reflexivity.
  Qed.

  Definition abgr_DirectSumIn2 (A B : abgr) : abelian_group_category⟦B, abgrdirprod A B⟧ :=
    make_abelian_group_morphism _ (abgr_DirectSumIn2_isbinopfun A B).

  Lemma abgr_DirectSumIdIn1 (A B : abgr) :
    abgr_DirectSumIn1 A B · abgr_DirectSumPr1 A B = identity A.
  Proof.
    apply abelian_group_morphism_eq. intros x. reflexivity.
  Qed.

  Lemma abgr_DirectSumIdIn2 (A B : abgr) :
    abgr_DirectSumIn2 A B · abgr_DirectSumPr2 A B = identity B.
  Proof.
    apply abelian_group_morphism_eq. intros x. reflexivity.
  Qed.

  Lemma abgr_DirectSumUnel1 (A B : abgr) :
    abgr_DirectSumIn1 A B · abgr_DirectSumPr2 A B = @to_unel abgr_PreAdditive A B.
  Proof.
    apply abelian_group_morphism_eq. intros x. reflexivity.
  Qed.

  Lemma abgr_DirectSumUnel2 (A B : abgr) :
    abgr_DirectSumIn2 A B · abgr_DirectSumPr1 A B = @to_unel abgr_PreAdditive B A.
  Proof.
    apply abelian_group_morphism_eq. intros x. reflexivity.
  Qed.

  Lemma abgr_DirectSumId (A B : abgr) :
    abgrshombinop
      (abgr_DirectSumPr1 A B · abgr_DirectSumIn1 A B)
      (abgr_DirectSumPr2 A B · abgr_DirectSumIn2 A B) =
    identity_abelian_group_morphism (abgrdirprod A B).
  Proof.
    apply abelian_group_morphism_eq. intros x. apply dirprod_paths.
    - apply (runax A).
    - apply (lunax B).
  Qed.

  Lemma abgr_isBinDirectSum (X Y : abgr) :
    isBinDirectSum (A := abgr_PreAdditive)
      (abgr_DirectSumIn1 X Y) (abgr_DirectSumIn2 X Y)
      (abgr_DirectSumPr1 X Y) (abgr_DirectSumPr2 X Y).
  Proof.
    apply make_isBinDirectSum.
    - exact (abgr_DirectSumIdIn1 X Y).
    - exact (abgr_DirectSumIdIn2 X Y).
    - exact (abgr_DirectSumUnel1 X Y).
    - exact (abgr_DirectSumUnel2 X Y).
    - exact (abgr_DirectSumId X Y).
  Defined.

End DirectSums.

(** ** 2.5. The additive structure *)

Definition abgr_AdditiveStructure : AdditiveStructure abgr_PreAdditive.
Proof.
  apply make_AdditiveStructure.
  - exact abgr_Zero.
  - apply make_BinDirectSums. intros X Y. use make_BinDirectSum.
    + exact (abgrdirprod X Y).
    + exact (abgr_DirectSumIn1 X Y).
    + exact (abgr_DirectSumIn2 X Y).
    + exact (abgr_DirectSumPr1 X Y).
    + exact (abgr_DirectSumPr2 X Y).
    + exact (abgr_isBinDirectSum X Y).
Defined.

Definition abgr_Additive : CategoryWithAdditiveStructure := make_Additive abgr_PreAdditive abgr_AdditiveStructure.

(** * 3. Kernels and Cokernels *)
(** ** 3.1. Kernels *)

Section Kernels.

  Context {A B : abgr}.
  Context (f : abelian_group_morphism A B).

  Definition abgr_Kernel_abelian_group_morphism
    : abelian_group_category⟦carrierofasubabgr (abgr_Kernel_subabgr f), A⟧
    := binopfun_to_abelian_group_morphism (X := abgr_Kernel_subabgr f) (make_binopfun _ (abgr_Kernel_abelian_group_morphism_isbinopfun f)).

  (** *** Composition Kernel f --> X --> Y is the zero arrow *)

  Definition abgr_Kernel_eq :
    abgr_Kernel_abelian_group_morphism · f = ZeroArrow abgr_Zero (carrierofasubabgr (abgr_Kernel_subabgr f)) B.
  Proof.
    apply abelian_group_morphism_eq.
    intro x.
    apply (pr2 x).
  Qed.

  (** *** KernelIn morphism *)

  Section UniversalProperty.

    Context {C : abelian_group_category}.
    Context (h : abelian_group_morphism C A).
    Context (H : h · f = ZeroArrow abgr_Zero C B).

    Lemma abgr_KernelArrowIn_map_property
              (c : (C : abgr)) :
      (f (h c) = 0).
    Proof.
      exact (abelian_group_morphism_eq H c).
    Qed.

    Definition abgr_KernelArrowIn_map
               (c : (C : abgr)) : abgr_Kernel_subabgr f.
    Proof.
      use tpair.
      - exact (h c).
      - exact (abgr_KernelArrowIn_map_property c).
    Defined.

    Lemma abgr_KernelArrowIn_isbinopfun :
      isbinopfun (Y := abgr_Kernel_subabgr f) abgr_KernelArrowIn_map.
    Proof.
      apply make_isbinopfun.
      apply make_isbinopfun. intros x x'. use total2_paths_f.
      + exact (binopfunisbinopfun (h : abelian_group_morphism (C : abgr) (A : abgr)) x x').
      + apply proofirrelevance. apply propproperty.
    Qed.

    Definition abgr_KernelArrowIn :
      abelian_group_category⟦C, carrierofasubabgr (abgr_Kernel_subabgr f)⟧.
    Proof.
      use make_abelian_group_morphism.
      - exact abgr_KernelArrowIn_map.
      - exact abgr_KernelArrowIn_isbinopfun.
    Defined.

    (** *** Kernels *)

    Definition abgr_Kernel_isKernel_KernelArrrow :
      ∑ ψ : abelian_group_category ⟦C, carrierofasubabgr (abgr_Kernel_subabgr f)⟧,
            ψ · abgr_Kernel_abelian_group_morphism = h.
    Proof.
      use tpair.
      - exact abgr_KernelArrowIn.
      - apply abelian_group_morphism_eq. intros x. reflexivity.
    Defined.

    Definition abgr_Kernel_isKernel_uniqueness
              (t : ∑ (t1 : abelian_group_category ⟦C, carrierofasubabgr (abgr_Kernel_subabgr f)⟧),
                    t1 · abgr_Kernel_abelian_group_morphism = h) :
      t = abgr_Kernel_isKernel_KernelArrrow.
    Proof.
      apply subtypePath.
      {
        intro.
        apply homset_property.
      }
      apply abelian_group_morphism_eq. intros x.
      apply subtypePath.
      {
        intro.
        apply propproperty.
      }
      exact (abelian_group_morphism_eq (pr2 t) x).
    Qed.

  End UniversalProperty.

  Definition abgr_Kernel_isKernel :
    isKernel abgr_Zero abgr_Kernel_abelian_group_morphism f abgr_Kernel_eq.
  Proof.
    apply make_isKernel.
    - intros w h H'.
      use make_iscontr.
      + exact (abgr_Kernel_isKernel_KernelArrrow h H').
      + intros t. exact (abgr_Kernel_isKernel_uniqueness h H' t).
  Defined.

  Definition abgr_Kernel :
    Kernel abgr_Zero f :=
    make_Kernel (abgr_Zero) abgr_Kernel_abelian_group_morphism f abgr_Kernel_eq abgr_Kernel_isKernel.

End Kernels.

Corollary abgr_Kernels : Kernels abgr_Zero.
Proof.
  intros A B f. exact (abgr_Kernel f).
Defined.

(** ** 3.2. Cokernels *)

Section Cokernels.

  (** *** Subgroup gives an equivalence relation. *)

  Context {A B : abgr}.
  Context (f : abelian_group_morphism A B).

  Definition abgr_Cokernel_eqrel_istrans :
    istrans (λ b1 b2 : B, ∃ a : A, f a = b1 - b2).
  Proof.
    intros x1 x2 x3 y1 y2.
    refine (hinhuniv _ y1). intros y1'.
    refine (hinhuniv _ y2). intros y2'.
    apply hinhpr.
    use tpair.
    - exact (pr1 y1' + pr1 y2').
    - apply (pathscomp0 (binopfunisbinopfun f (pr1 y1') (pr1 y2'))).
      rewrite (pr2 y1'). rewrite (pr2 y2').
      rewrite <- assocax. rewrite (assocax _ _ _ x2). rewrite (grlinvax B). rewrite (runax B).
      reflexivity.
  Qed.

  Definition abgr_Cokernel_eqrel_isrefl :
    isrefl (λ b1 b2 : B, ∃ a : A, f a = b1 - b2).
  Proof.
    intros x1 P X. apply X. clear P X.
    use tpair.
    - exact 0.
    - cbn. rewrite (grrinvax B). apply (monoidfununel f).
  Qed.

  Definition abgr_Cokernel_eqrel_issymm :
    issymm (λ b1 b2 : B, ∃ a : A, f a = b1 - b2).
  Proof.
    intros x1 x2 x3.
    refine (hinhuniv _ x3). intros x3'.
    intros P X. apply X. clear P X.
    use tpair.
    - exact (-pr1 x3').
    - refine (group_morphism_inv f (pr1 x3') @ _).
      rewrite (pr2 x3'). rewrite grinvop. apply two_arg_paths.
      + apply grinvinv.
      + reflexivity.
  Qed.

  Definition abgr_Cokernel_eqrel : eqrel B :=
    eqrelconstr (λ b1 b2, ∃ a, f a = b1 - b2)
                 abgr_Cokernel_eqrel_istrans abgr_Cokernel_eqrel_isrefl
                 abgr_Cokernel_eqrel_issymm.

  (** *** Construction of the quotient abelian group Y/(Im f) *)

  Definition abgr_Cokernel_abgr_isbinoprel :
    isbinophrel (λ b1 b2 : B, ∃ a : A, f a = b1 - b2).
  Proof.
    apply isbinophrelif.
    - exact (commax B).
    - intros x1 x2 x3 y1. refine (hinhuniv _ y1). intros y1'. apply hinhpr.
      use tpair.
      + exact (pr1 y1').
      + apply (pathscomp0 (pr2 y1')). rewrite grinvop.
        rewrite (commax B x3). rewrite (assocax B). rewrite (commax B x3).
        rewrite (assocax B). rewrite (grlinvax B x3). rewrite (runax B). reflexivity.
  Qed.

  Definition abgr_Cokernel_abgr : abgr :=
    abgrquot (make_binopeqrel abgr_Cokernel_eqrel abgr_Cokernel_abgr_isbinoprel).

  (** *** The canonical morphism Y --> Y/(Im f) *)

  Lemma abgr_CokernelArrow_isbinopfun :
    isbinopfun (Y := abgr_Cokernel_abgr) (setquotpr abgr_Cokernel_eqrel).
  Proof.
    intros x x'. reflexivity.
  Qed.

  Definition abgr_CokernelArrow :
    abelian_group_morphism B abgr_Cokernel_abgr.
  Proof.
    use make_abelian_group_morphism.
    - exact (setquotpr abgr_Cokernel_eqrel).
    - exact abgr_CokernelArrow_isbinopfun.
  Defined.

  (** *** CokernelOut *)

  Lemma abgr_Cokernel_abelian_group_morphism_issurjective :
    issurjective abgr_CokernelArrow.
  Proof.
    apply issurjsetquotpr.
  Qed.

  Definition abgr_Cokernel_eq :
    f · abgr_CokernelArrow = ZeroArrow abgr_Zero A abgr_Cokernel_abgr.
  Proof.
    apply abelian_group_morphism_eq. intros a.
    apply (iscompsetquotpr abgr_Cokernel_eqrel).
    apply hinhpr.
    use tpair.
    - exact a.
    - apply (pathscomp0 (pathsinv0 (runax B (f a)))).
      apply two_arg_paths.
      + reflexivity.
      + apply pathsinv0. apply (grinvunel B).
  Qed.

  Section UniversalProperty.

    Context {C : abgr}.
    Context (h : abelian_group_morphism B C).
    Context (H : f · h = ZeroArrow abgr_Zero A C).

    Definition abgr_CokernelArrowOutUniv_iscomprelfun :
      iscomprelfun (λ b1 b2 : B, ∃ a : A, f a = b1 - b2)
                  h.
    Proof.
      intros x x' X.
      apply (squash_to_prop X (setproperty (C : abgr) (h x) (h x'))). intros X'.
      apply (grrcan (abgrtogr C) (h (-x'))).
      refine (_ @ (binopfunisbinopfun h x' (-x'))).
      refine (_ @ ! maponpaths (λ xx : (B : abgr), h xx) (grrinvax (B : abgr) x')).
      refine (_ @ ! monoidfununel h).
      refine (_ @ abelian_group_morphism_eq H _).
      refine (! binopfunisbinopfun h x (-x') @ _).
      apply (maponpaths h). exact (!pr2 X').
    Qed.

    Definition abgr_CokernelOut_map :
      abgr_Cokernel_abgr → C :=
      setquotuniv (λ b1 b2 : B, ∃ a : A, f a = b1 - b2)
                  C h abgr_CokernelArrowOutUniv_iscomprelfun.

    Definition abgr_CokernelOut_isbinopfun :
      isbinopfun abgr_CokernelOut_map.
    Proof.
      exact (isbinopfun_twooutof3b _ _
              abgr_Cokernel_abelian_group_morphism_issurjective
              (binopfunisbinopfun h)
              (binopfunisbinopfun abgr_CokernelArrow)).
    Qed.

    Definition abgr_CokernelOut : abelian_group_morphism abgr_Cokernel_abgr C :=
      make_abelian_group_morphism _ abgr_CokernelOut_isbinopfun.

    Lemma abgr_CokernelOut_Comm :
      composite_abelian_group_morphism abgr_CokernelArrow abgr_CokernelOut = h.
    Proof.
      apply abelian_group_morphism_eq. intros x. reflexivity.
    Qed.

    Definition make_abgr_CokernelOut :
      ∑ ψ : abelian_group_category⟦abgr_Cokernel_abgr, C⟧, abgr_CokernelArrow · ψ = h.
    Proof.
      use tpair.
      - exact abgr_CokernelOut.
      - exact abgr_CokernelOut_Comm.
    Defined.

    (** *** Cokernels *)

    Lemma abgr_isCokernel_uniquenss
          (t : ∑ ψ : abelian_group_category ⟦abgr_Cokernel_abgr, C⟧, abgr_CokernelArrow · ψ = h) :
      t = make_abgr_CokernelOut.
    Proof.
      apply subtypePath.
      {
        intro.
        apply homset_property.
      }
      apply abelian_group_morphism_eq. intros x.
      apply (squash_to_prop (abgr_Cokernel_abelian_group_morphism_issurjective x) (setproperty C _ _)).
      intros hf. rewrite <- (hfiberpr2 _ _ hf).
      exact (abelian_group_morphism_eq (pr2 t) _).
    Qed.

  End UniversalProperty.

  Definition abgr_isCokernel :
    isCokernel abgr_Zero f abgr_CokernelArrow abgr_Cokernel_eq.
  Proof.
    apply make_isCokernel.
    - intros C h H. use make_iscontr.
      + exact (make_abgr_CokernelOut h H).
      + intros t. exact (abgr_isCokernel_uniquenss h H t).
  Defined.

  Definition abgr_Cokernel : Cokernel abgr_Zero f :=
    make_Cokernel abgr_Zero f abgr_CokernelArrow abgr_Cokernel_eq abgr_isCokernel.

End Cokernels.

Corollary abgr_Cokernels : Cokernels abgr_Zero.
Proof.
  intros A B f. exact (abgr_Cokernel f).
Defined.

(** * 4. Monics are inclusions and Epis are surjections *)

Section abgr_monics_and_epis.

(** ** 4.1. Epis are surjections *)

  Context {A B : abgr}.
  Context (f : abelian_group_morphism A B).

  Definition abgr_epi_hfiber_inhabited
    (isE : isEpi f)
    (b : B)
    (H : setquotpr (abgr_Cokernel_eqrel f) b = setquotpr (abgr_Cokernel_eqrel f) 0)
    : ∥ hfiber f b ∥.
  Proof.
    set (tmp := weqpathsinsetquot (abgr_Cokernel_eqrel f) b 0).
    refine (hinhuniv _ ((invweq tmp) H)). intros Y. apply hinhpr. induction Y as [t p].
    rewrite grinvunel in p. rewrite (runax B) in p.
    exact (make_hfiber f t p).
  Qed.

  Definition abgr_epi_issurjective (isE : isEpi f) :
    issurjective f.
  Proof.
    intros x. apply abgr_epi_hfiber_inhabited.
    - exact isE.
    - set (tmp := isE (abgr_Cokernel_abgr f) (abgr_CokernelArrow f)
                      (unel_abelian_group_morphism B (abgr_Cokernel_abgr f))).
      assert (H : f · abgr_CokernelArrow f = f · unel_abelian_group_morphism B (abgr_Cokernel_abgr f)).
      {
        rewrite abgr_Cokernel_eq.
        rewrite <- abgr_Zero_arrow_comp.
        rewrite ZeroArrow_comp_right.
        reflexivity.
      }
      exact (abelian_group_morphism_eq (tmp H) x).
  Qed.

(** ** 4.2. Monics are inclusions *)

  Lemma nat_nat_prod_abgr_abelian_group_morphism_eq (a1 a2 : A) (H : f a1 = f a2)
    : composite_abelian_monoid_morphism (nat_nat_prod_abmonoid_abelian_monoid_morphism a1) (abelian_group_to_monoid_morphism f)
    = composite_abelian_monoid_morphism (nat_nat_prod_abmonoid_abelian_monoid_morphism a2) (abelian_group_to_monoid_morphism f).
  Proof.
    apply abelian_monoid_morphism_eq. intros x. induction x as [x1 x2]. cbn.
    unfold nataddabmonoid_nataddabmonoid_to_monoid_fun.
    unfold nat_nat_to_monoid_fun. cbn -[nat_to_monoid_fun].
    refine (binopfunisbinopfun f _ _ @ _).
    refine (_ @ (! (binopfunisbinopfun f _ _))). cbn.
    change (pr1binopfun _ _ (pr1 f)) with (f : _ → _).
    rewrite (abelian_group_morphism_nat_to_monoid_fun f a1 x1).
    rewrite (abelian_group_morphism_nat_to_monoid_fun f a2 x1).
    rewrite (abelian_group_morphism_nat_to_monoid_fun f (-a1) x2).
    rewrite (abelian_group_morphism_nat_to_monoid_fun f (-a2) x2).
    apply two_arg_paths.
    - induction H. reflexivity.
    - assert (e : f (-a1) = f (-a2)). {
        apply (grlcan _ (f a1)).
        refine (! binopfunisbinopfun f a1 (-a1) @ _).
        refine (maponpaths f (grrinvax A a1) @ _).
        rewrite H.
        refine (_ @ binopfunisbinopfun f a2 (-a2)).
        refine (_ @ !maponpaths f (grrinvax A a2)).
        reflexivity.
      }
      induction e. reflexivity.
  Qed.

  Lemma abgr_abelian_group_morphism_precomp {X Y Z : abmonoid}
    (f1 f2 : abelian_monoid_morphism Y Z)
    (g : abelian_monoid_morphism X Y) (H : issurjective g)
    : g · f1 = g · f2 -> f1 = f2.
  Proof.
    intros e. apply abelian_monoid_morphism_eq. intros x.
    apply (squash_to_prop (H x) (setproperty Z _ _)). intros hf.
    rewrite <- (hfiberpr2 _ _ hf).
    exact (abelian_monoid_morphism_eq e (hfiberpr1 _ _ hf)).
  Qed.

  Lemma hz_abgr_fun_monoifun_paths (a1 a2 : A) (H : f a1 = f a2) (x : hzaddabgr)
    : f (hz_abgr_fun_abelian_group_morphism a1 x) = f (hz_abgr_fun_abelian_group_morphism a2 x).
  Proof.
    refine (abelian_monoid_morphism_eq (abgr_abelian_group_morphism_precomp
           (composite_abelian_monoid_morphism (abelian_group_to_monoid_morphism (hz_abgr_fun_abelian_group_morphism a1)) (abelian_group_to_monoid_morphism f))
           (composite_abelian_monoid_morphism (abelian_group_to_monoid_morphism (hz_abgr_fun_abelian_group_morphism a2)) (abelian_group_to_monoid_morphism f))
           hz_abmonoid_abelian_monoid_morphism _ _) x).
    - apply issurjsetquotpr.
    - rewrite !assoc, !abgr_natnat_hz_X_comm.
      exact (nat_nat_prod_abgr_abelian_group_morphism_eq a1 a2 H).
  Qed.

  Definition abgr_monic_isincl (isM : isMonic f) :
    isincl f.
  Proof.
    intros b h1 h2.
    use make_iscontr.
    - use subtypePath.
      {
        intro.
        apply setproperty.
      }
      apply (grrcan A 0). apply (grrcan A 0).
      refine (abelian_group_morphism_eq
        (isM hzaddabgr (hz_abgr_fun_abelian_group_morphism (pr1 h1))
                      (hz_abgr_fun_abelian_group_morphism (pr1 h2)) _) hzone).
      apply abelian_group_morphism_eq.
      apply (hz_abgr_fun_monoifun_paths _ _ (hfiberpr2 _ _ h1 @ ! hfiberpr2 _ _ h2)).
    - intros t. apply proofirrelevance. apply isaset_hfiber.
      + apply setproperty.
      + apply setproperty.
  Qed.

  Definition abgr_monic_isInjective (isM : isMonic f) :
    isInjective f.
  Proof.
    exact (isweqonpathsincl f (abgr_monic_isincl isM)).
  Qed.

  Lemma abgr_monic_paths (isM : isMonic f) (a1 a2 : A) :
    f a1 = f a2 -> a1 = a2.
  Proof.
    exact (invweq (make_weq _ (abgr_monic_isInjective isM a1 a2))).
  Qed.

End abgr_monics_and_epis.

Lemma abgr_abelian_group_morphism_postcomp {A B C : abgr} (f1 f2 : abelian_group_morphism A B) (g : abelian_group_morphism B C)
      (isM : isMonic (g : abelian_group_category⟦B, C⟧)) :
  monoidfuncomp f1 g = monoidfuncomp f2 g -> f1 = f2.
Proof.
  intros e. apply abelian_group_morphism_eq. intros x.
  apply (invmap (make_weq _ (abgr_monic_isInjective g isM (f1 x) (f2 x)))).
  exact (monoidfun_eq e x).
Qed.

(** * 5. Monics are kernels of their cokernels and epis are cokernels of their kernels *)
(** ** 5.1. Monics are Kernels *)

Section Monics.

  Context {A B : abgr}.
  Context (f : abelian_group_morphism A B).
  Context (isM : isMonic f).

  Definition abgr_monic_kernel_in_hfiber_iscontr {C : abgr} (h : abelian_group_morphism C B)
    (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f)) (c : C) :
    iscontr (hfiber f (h c)).
  Proof.
    apply (squash_to_prop
           ((invweq (weqpathsinsetquot (abgr_Cokernel_eqrel f) (h c) 0))
              (abelian_group_morphism_eq H c)) (isapropiscontr _)).
    intros hf.
    use make_iscontr.
    - use make_hfiber.
      + exact (pr1 hf).
      + apply (pathscomp0 (pr2 hf)). rewrite grinvunel. apply (runax B).
    - intros t. apply subtypePath.
      {
        intro.
        apply setproperty.
      }
      apply (invmap (make_weq _ (abgr_monic_isInjective f isM (pr1 t) (pr1 hf)))).
      apply (pathscomp0 (hfiberpr2 _ _ t)). use (pathscomp0 _ (! (pr2 hf))).
      rewrite grinvunel. rewrite runax. reflexivity.
  Qed.

  Lemma abgr_monic_kernel_in_hfiber_mult_eq {C : abgr} (x x' : C) (h : abelian_group_morphism C B) (X : hfiber f (h x)) (X0 : hfiber f (h x')) :
    f (pr1 X + pr1 X0) = h (x + x').
  Proof.
    rewrite !monoidfunmul.
    rewrite (pr2 X).
    rewrite (pr2 X0).
    reflexivity.
  Qed.

  Definition abgr_monic_kernel_in_hfiber_mult
              {C : abgr} (x x' : C) (h : abelian_group_morphism C B) :
    hfiber f (h x) -> hfiber f (h x')
    -> hfiber f (h (x + x')).
  Proof.
    intros X X0.
    exact (make_hfiber f (pr1 X + pr1 X0)
                      (abgr_monic_kernel_in_hfiber_mult_eq x x' h X X0)).
  Defined.

  Lemma abgr_monic_kernel_in_hfiber_unel_eq {C : abgr}
        (h : abelian_group_morphism C B) : f 0 = h 0.
  Proof.
    now rewrite !monoidfununel.
  Qed.

  Definition abgr_monic_kernel_in_hfiber_unel (w : abgr)
             (h : abelian_group_morphism w B) : hfiber f (h 0) :=
    make_hfiber f 0 (abgr_monic_kernel_in_hfiber_unel_eq h).

  Definition abgr_monic_kernel_in
             (w : abgr) (h: abelian_group_category⟦w, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero _ _) : w -> A.
  Proof.
    intros x.
    exact (hfiberpr1 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr h H x))).
  Defined.

  Definition abgr_monic_kernel_in_isbinopfun (w : abgr) (h: abelian_group_morphism w B)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero _ _) :
    isbinopfun (abgr_monic_kernel_in w h H).
  Proof.
    apply make_isbinopfun. intros x x'.
    set (t := abgr_monic_kernel_in_hfiber_iscontr h H x).
    set (tmp := abgr_monic_kernel_in_hfiber_mult
                  x x' h
                  (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr h H x))
                  (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr h H x'))).
    change (abgr_monic_kernel_in _ _ _ _ + _) with (hfiberpr1 _ _ tmp).
    unfold abgr_monic_kernel_in.
    apply (invmap (make_weq _ (abgr_monic_isInjective f isM _ _))).
    refine (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr
                                                  h H (x + x'))) @ _).
    exact (!hfiberpr2 _ _ tmp).
  Qed.

  Definition abgr_monic_kernel_in_abelian_group_morphism
             (w : abgr) (h: abelian_group_category⟦w, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero _ _) :
    abelian_group_morphism w A := make_abelian_group_morphism _ (abgr_monic_kernel_in_isbinopfun w h H).

  Definition abgr_monic_Kernel_eq :
    f · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero A (abgr_Cokernel f).
  Proof.
    apply CokernelCompZero.
  Qed.

  Lemma abgr_monic_Kernel_isKernel_comm {C : abgr}
        (h : abelian_group_morphism C B)
        (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f)):
    abgr_monic_kernel_in_abelian_group_morphism C h H · f = h.
  Proof.
    apply abelian_group_morphism_eq. intros x.
    exact (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr h H x))).
  Qed.

  Definition make_abgr_monic_Kernel_isKernel {C : abgr}
             (h : abelian_group_category⟦C, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f)) :
    ∑ ψ : abelian_group_category ⟦C, A⟧, ψ · f = h.
  Proof.
    use tpair.
    - exact (abgr_monic_kernel_in_abelian_group_morphism C h H).
    - exact (abgr_monic_Kernel_isKernel_comm h H).
  Defined.

  Definition abgr_monic_Kernel_isKernel_uniqueness {C : abgr}
             (h : abelian_group_category⟦C, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f))
             (t : ∑ ψ : abelian_group_category ⟦C, A⟧, ψ · f = h) :
    t = make_abgr_monic_Kernel_isKernel h H.
  Proof.
    apply subtypePath.
    {
      intro.
      apply homset_property.
    }
    apply abelian_group_morphism_eq. intros x.
    apply (invmap (make_weq _ (abgr_monic_isInjective _ isM _ _))).
    refine (abelian_group_morphism_eq (hfiberpr2 _ _ t) x @ _).
    symmetry.
    exact (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr h H x))).
  Qed.

  Definition abgr_monic_Kernel_isKernel :
    isKernel abgr_Zero f (CokernelArrow (abgr_Cokernel f))
             (CokernelCompZero abgr_Zero (abgr_Cokernel f)).
  Proof.
    apply make_isKernel.
    - intros w h H.
      use make_iscontr.
      + exact (make_abgr_monic_Kernel_isKernel h H).
      + exact (abgr_monic_Kernel_isKernel_uniqueness h H).
  Defined.

  Definition abgr_monic_kernel :
    Kernel abgr_Zero (CokernelArrow (abgr_Cokernel f)) :=
    make_Kernel abgr_Zero f (CokernelArrow (abgr_Cokernel f)) (abgr_monic_Kernel_eq)
              (abgr_monic_Kernel_isKernel).

  Lemma abgr_monic_kernel_comp :
    KernelArrow (abgr_monic_kernel) = f.
  Proof.
    reflexivity.
  Qed.

End Monics.

(** ** 5.2. Epis are Cokernels *)

Section Epis.

  Context {A B : abgr}.
  Context (f : abelian_group_morphism A B).
  Context (isE : isEpi f).

  Definition abgr_epi_cokernel_out_kernel_hsubtype (a : A)
             (H : f a = 0) : abgr_kernel_hsubtype f.
  Proof.
    exact (a,, H).
  Defined.

  Lemma abgr_epi_cokernel_out_data_eq {C : abgr}
    (h : abelian_group_morphism A C)
    (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C) :
    ∏ x : abgr_kernel_hsubtype f, h (pr1carrier (abgr_kernel_hsubtype f) x) = 0.
  Proof.
    intro x.
    exact (abelian_group_morphism_eq H x).
  Qed.

  Lemma abgr_epi_cokernel_out_data_hfibers_to_unel (b : B)
        (hfib1 hfib2 : hfiber f b) :
    f (pr1 hfib1 - pr1 hfib2) = 0.
  Proof.
    rewrite monoidfunmul.
    apply (grrcan (abgrtogr B) (f (pr1 hfib2))).
    rewrite (assocax B). rewrite <- monoidfunmul.
    rewrite (grlinvax A). rewrite monoidfununel.
    rewrite (runax B). rewrite (lunax B).
    rewrite (pr2 hfib1). rewrite (pr2 hfib2).
    reflexivity.
  Qed.

  Lemma abgr_epi_cokernel_out_data_hfiber_eq {C : abgr}
        (h : abelian_group_morphism A C)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) (b : B)
        (X : hfiber f b) : ∏ hfib : hfiber f b, h (pr1 hfib) = h (pr1 X).
  Proof.
    intros hfib.
    apply (grrcan C (- h (pr1 X))).
    rewrite (grrinvax C).
    set (e1 := abgr_epi_cokernel_out_data_hfibers_to_unel b hfib X).
    set (tmp1 := ! (group_morphism_inv h (hfiberpr1 _ _ X))). cbn in tmp1.
    refine (maponpaths (λ k, (h (pr1 hfib) + k)) tmp1 @ _).
    rewrite <- (monoidfunmul h).
    set (tmp2 := abgr_epi_cokernel_out_data_eq h H).
    set (tmp3 := abgr_epi_cokernel_out_kernel_hsubtype
                   (pr1 hfib - pr1 X) e1).
    set (tmp4 := tmp2 tmp3). cbn in tmp4. exact tmp4.
  Qed.

  Lemma abgr_epi_CokernelOut_iscontr {C : abgr}
        (h : abelian_group_morphism A C)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) (b : B) :
    iscontr (∑ x : C, ∏ (hfib : hfiber f b), h (pr1 hfib) = x).
  Proof.
    apply (squash_to_prop (abgr_epi_issurjective f isE b) (isapropiscontr _)).
    intros X. use make_iscontr.
    - use tpair.
      + exact (h (pr1 X)).
      + exact (abgr_epi_cokernel_out_data_hfiber_eq h H b X).
    - intros t. apply subtypePath.
      {
        intro.
        apply impred.
        intros t0.
        apply (setproperty C).
      }
      exact (! ((pr2 t) X)).
  Defined.

  Definition abgr_epi_CokernelOut_mult_eq {C : abgr} (b1 b2 : B)
             (h : abelian_group_morphism A C)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _)
             (X : ∑ x : C, ∏ hfib : hfiber f b1, h (pr1 hfib) = x)
             (X0 : ∑ x : C, ∏ hfib : hfiber f b2, h (pr1 hfib) = x) :
    ∏ hfib : hfiber f (b1 + b2), h (pr1 hfib) = pr1 X + pr1 X0.
  Proof.
    intros hfib.
    apply (squash_to_prop (abgr_epi_issurjective f isE b1) (setproperty C _ _)). intros X1.
    apply (squash_to_prop (abgr_epi_issurjective f isE b2) (setproperty C _ _)). intros X2.
    rewrite <- ((pr2 X) X1). rewrite <- ((pr2 X0) X2). rewrite <- monoidfunmul.
    exact (abgr_epi_cokernel_out_data_hfiber_eq
             h H (b1 + b2) (hfiberbinop (f : abelian_group_morphism _ _) b1 b2 X1 X2) hfib).
  Qed.

  Definition abgr_epi_cokernel_out_data_mult {C : abgr} (b1 b2 : B)
             (h : abelian_group_morphism A C)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    (∑ x : C, ∏ (hfib : hfiber f b1), h (pr1 hfib) = x) ->
    (∑ x : C, ∏ (hfib : hfiber f b2), h (pr1 hfib) = x) ->
    (∑ x : C, ∏ (hfib : hfiber f (b1 + b2)), h (pr1 hfib) = x).
  Proof.
    intros X X0.
    exact (pr1 X + pr1 X0 ,, abgr_epi_CokernelOut_mult_eq b1 b2 h H X X0).
  Defined.

  Definition abgr_epi_cokernel_out_data_unel_eq {C : abgr}
             (h : abelian_group_morphism A C)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    ∏ hfib : hfiber f 0, h (pr1 hfib) = 0.
  Proof.
    intros hfib.
    set (hfib_unel := make_hfiber f 0 (monoidfununel f)).
    rewrite (abgr_epi_cokernel_out_data_hfiber_eq h H 0 hfib_unel hfib).
    exact (monoidfununel h).
  Qed.

  Definition abgr_epi_cokernel_out_data_unel {C : abgr}
             (h : abelian_group_morphism A C)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    ( ∑ x : C, ∏ (hfib : hfiber f 0),  h (pr1 hfib) = x) :=
    tpair _ 0 (abgr_epi_cokernel_out_data_unel_eq h H).

  Lemma abgr_epi_cokernel_out_isbinopfun {C : abgr} (h : abelian_group_morphism A C)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    isbinopfun (λ b : B, (pr1 (iscontrpr1 (abgr_epi_CokernelOut_iscontr h H b)))).
  Proof.
    apply make_isbinopfun. intros x x'.
    set (HH0 := abgr_epi_cokernel_out_data_mult
                  x x' h H
                  (iscontrpr1 (abgr_epi_CokernelOut_iscontr h H x))
                  (iscontrpr1 (abgr_epi_CokernelOut_iscontr h H x'))).
    assert (HH : iscontrpr1 (abgr_epi_CokernelOut_iscontr h H (x + x')) = HH0).
    {
      set (tmp := abgr_epi_CokernelOut_iscontr h H (x + x')).
      rewrite (pr2 tmp). apply pathsinv0. rewrite (pr2 tmp).
      reflexivity.
    }
    exact (base_paths _ _ HH).
  Qed.

  Definition abgr_epi_cokernel_out_abelian_group_morphism {C : abgr} (h : abelian_group_morphism A C)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    abelian_group_morphism B C := make_abelian_group_morphism _ (abgr_epi_cokernel_out_isbinopfun h H).

  Definition abgr_epi_cokernel_eq :
    KernelArrow (abgr_Kernel f) · f = ZeroArrow abgr_Zero _ _.
  Proof.
    apply KernelCompZero.
  Qed.

  Lemma abgr_epi_cokernel_isCokernel_comm {C : abgr} (h : abelian_group_morphism A C)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C) :
    f · abgr_epi_cokernel_out_abelian_group_morphism h H = h.
  Proof.
    apply abelian_group_morphism_eq.
    intros x. apply pathsinv0.
    exact (pr2 (iscontrpr1 (abgr_epi_CokernelOut_iscontr h H (f x)))
               (make_hfiber f x (idpath _))).
  Qed.

  Definition make_abgr_epi_cokernel_isCokernel {C : abgr} (h : abelian_group_morphism A C)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C) :
    ∑ ψ : abelian_group_category ⟦B, C⟧, f · ψ = h.
  Proof.
    use tpair.
    - exact (abgr_epi_cokernel_out_abelian_group_morphism h H).
    - exact (abgr_epi_cokernel_isCokernel_comm h H).
  Defined.

  Lemma abgr_epi_cokernel_isCokernel_uniqueness {C : abgr} (h : abelian_group_morphism A C)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C)
        (t : ∑ ψ : abelian_group_category ⟦B, C⟧, f · ψ = h) :
    t = make_abgr_epi_cokernel_isCokernel h H.
  Proof.
    apply subtypePath.
    {
      intro.
      apply homset_property.
    }
    apply isE. apply (pathscomp0 (pr2 t)). apply abelian_group_morphism_eq. intros x.
    exact (pr2 (iscontrpr1 (abgr_epi_CokernelOut_iscontr h H (f x)))
               (make_hfiber f x (idpath _))).
  Qed.

  Definition abgr_epi_cokernel_isCokernel :
    isCokernel abgr_Zero (KernelArrow (abgr_Kernel f)) f (abgr_epi_cokernel_eq).
  Proof.
    apply make_isCokernel.
    - intros w h H. use make_iscontr.
      + exact (make_abgr_epi_cokernel_isCokernel h H).
      + intros t. exact (abgr_epi_cokernel_isCokernel_uniqueness h H t).
  Defined.

  Definition abgr_epi_cokernel :
    Cokernel abgr_Zero (KernelArrow (abgr_Kernel f)) :=
    make_Cokernel abgr_Zero (KernelArrow (abgr_Kernel f)) f _ (abgr_epi_cokernel_isCokernel).

  Definition abgr_epi_cokernel_comp :
    CokernelArrow (abgr_epi_cokernel) = f.
  Proof.
    reflexivity.
  Qed.

End Epis.

(** * 6. The category of abelian groups is an abelian category *)

Definition abgr_Abelian : AbelianPreCat.
Proof.
  set (BinDS := to_BinDirectSums abgr_Additive).
  use (make_Abelian abelian_group_category).
  - apply make_Data1.
    + exact abgr_Zero.
    + intros X Y. exact (BinDirectSum_BinProduct abgr_Additive (BinDS X Y)).
    + intros X Y. exact (BinDirectSum_BinCoproduct abgr_Additive (BinDS X Y)).
  - use make_AbelianData.
    + apply make_Data2.
      * intros A B f. exact (abgr_Kernel f).
      * intros A B f. exact (abgr_Cokernel f).
    + apply make_MonicsAreKernels.
      intros x y M.
      exact (KernelisKernel abgr_Zero (abgr_monic_kernel _ (MonicisMonic abelian_group_category M))).
    + apply make_EpisAreCokernels.
      intros x y E.
      exact (CokernelisCokernel abgr_Zero (abgr_epi_cokernel _ (EpiisEpi abelian_group_category E))).
Defined.

(** * 7. An elementwise criterion for isKernel *)

Section KernelCriterion.

  Context {X Y Z : abgr}.
  Context (f : abelian_group_morphism X Y).
  Context (g : abelian_group_morphism Y Z).
  Context (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _).
  Context (H : ∏ (D : hfiber g 0), ∥ hfiber f (pr1 D) ∥).
  Context (isM : isMonic f).

  Local Opaque ZeroArrow.

  Section UniversalProperty.

    Context {W : abgr}.
    Context (h : abelian_group_morphism W Y).
    Context (H' : h · g = ZeroArrow (to_Zero abgr_Abelian) W Z).

    Definition abgr_isKernel_iscontr
      (w' : W)
      : iscontr (hfiber f (h w')).
    Proof.
      rewrite <- (@PreAdditive_unel_zero abgr_PreAdditive) in H'.
      unfold to_unel in H'.
      set (e := abelian_group_morphism_eq H' w').
      set (H'' := H (h w' ,, e)).
      apply (squash_to_prop H'' (isapropiscontr _)). intros HH.
      induction HH as [H1 H2].
      use tpair.
      - use tpair.
        + exact H1.
        + exact H2.
      - intros T. induction T as [T1 T2].
        apply subtypePath.
        {
          intro.
          apply setproperty.
        }
        apply (abgr_monic_paths f isM T1 H1).
        rewrite H2. rewrite T2. reflexivity.
    Qed.

    Lemma abgr_isKernel_Criteria_isbinopfun
      : isbinopfun (λ w' : (W : abgr), pr1 (iscontrpr1 (abgr_isKernel_iscontr w'))).
    Proof.
      intros x y. apply (abgr_monic_paths f isM).
      refine (_ @ ! binopfunisbinopfun (f : abelian_group_morphism _ _) _ _).
      refine (pr2 (iscontrpr1 (abgr_isKernel_iscontr (x + y))) @ _).
      refine (binopfunisbinopfun (h : abelian_group_morphism _ _) _ _ @ _).
      apply pathsinv0.
      use two_arg_paths.
      + exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr x))).
      + exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr y))).
    Qed.

    Lemma abgr_isKernel_Criteria_comm
      : make_abelian_group_morphism _ abgr_isKernel_Criteria_isbinopfun · f = h.
    Proof.
      apply abelian_group_morphism_eq. intros x.
      exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr x))).
    Qed.

    Definition make_abgr_isKernel_Criteria :
      ∑ ψ : abgr_Abelian ⟦W, X⟧, ψ · f = h
      := _ ,, abgr_isKernel_Criteria_comm.

    Lemma abgr_isKernel_Criteria_uniqueness
          (t : ∑ ψ : abgr_Abelian ⟦W, X⟧, ψ · f = h) :
      t = make_abgr_isKernel_Criteria.
    Proof.
      apply subtypePath.
      {
        intro.
        apply homset_property.
      }
      apply abelian_group_morphism_eq. intros x.
      apply (abgr_monic_paths f isM).
      refine (abelian_group_morphism_eq (pr2 t) x @ !_).
      exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr x))).
    Qed.

  End UniversalProperty.

  Definition abgr_isKernel_Criteria : isKernel (to_Zero abgr_Abelian) f g ZA.
  Proof.
    apply make_isKernel.
    - intros w h H'. use make_iscontr.
      + exact (make_abgr_isKernel_Criteria h H').
      + intros t. exact (abgr_isKernel_Criteria_uniqueness h H' t).
  Defined.

End KernelCriterion.
