(** * Category of abelian groups *)
(** ** Contents
- Precategory of abelian groups
- Category of abelian groups
- Zero object and Zero arrow
 - Zero object
 - Zero arrow
- Category of abelian groups is preadditive
- Category of abelian groups is additive
- Kernels and Cokernels
 - Kernels
 - Cokernels
- Monics are inclusions and Epis are surjections
 - Epis are surjections
 - Monics are inclusions
- Monics are kernels of their cokernels and epis are cokernels of their kernels
 - Monics are Kernels
 - Epis are Cokernels
- The category of abelian groups is an abelian category
- Corollaries to additive categories
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.Monoids.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.Categories.Magma.
Require Import UniMath.CategoryTheory.Categories.Group.

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

Local Open Scope cat.


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

(** * Zero object and Zero arrow
   - Zero object is the abelian group which consists of one element, the unit element.
   - The unique morphism to zero object maps every element to the unit element.
   - The unique morphism from the zero object maps unit to unit.
   - The unique morphisms which factors through zero object maps every element to the unit
     element.
   - Computations on zero object
 *)
Section def_abgr_zero.

  (** ** Zero in abelian category *)

  Lemma isconnectedfromunitabgr (a : abelian_group_category) (t : abelian_group_morphism unitabgr a):
    t = unel_abelian_group_morphism unitabgr (a : abgr).
  Proof.
    apply abelian_group_morphism_eq, funextfun. intros x.
    refine (_ @ monoidfununel t). apply maponpaths. apply isProofIrrelevantUnit.
  Qed.

  Lemma isconnectedtounitabgr (a : abelian_group_category) (t : abelian_group_morphism a unitabgr):
    t = unel_abelian_group_morphism a unitabgr.
  Proof.
    apply abelian_group_morphism_eq, funextfun. intros x. apply isProofIrrelevantUnit.
  Qed.

  Definition abgr_isZero : @isZero abelian_group_category unitabgr.
  Proof.
    apply make_isZero.
    - intros a. use make_iscontr.
      + exact (unel_abelian_group_morphism _ a).
      + intros t. exact (isconnectedfromunitabgr a t).
    - intros a. use make_iscontr.
      + exact (unel_abelian_group_morphism a _).
      + intros t. exact (isconnectedtounitabgr a t).
  Defined.

  Definition abgr_Zero : Zero abelian_group_category := @make_Zero abelian_group_category unitabgr abgr_isZero.


  (** ** Computations on zero object *)

  Lemma abgr_Zero_comp : ZeroObject (abgr_Zero) = unitabgr.
  Proof.
    reflexivity.
  Qed.

  Lemma abgr_Zero_from_comp (A : abgr) :
    @ZeroArrowFrom abelian_group_category abgr_Zero A = unel_abelian_group_morphism unitabgr A.
  Proof.
    reflexivity.
  Qed.

  Lemma abgr_Zero_to_comp (A : abgr) :
    @ZeroArrowTo abelian_group_category abgr_Zero A = unel_abelian_group_morphism A unitabgr.
  Proof.
    reflexivity.
  Qed.

  Lemma abgr_Zero_arrow_comp (A B : abgr) :
    @ZeroArrow abelian_group_category abgr_Zero A B = unel_abelian_group_morphism A B.
  Proof.
    apply abelian_group_morphism_eq, funextfun. intros x. reflexivity.
  Qed.

End def_abgr_zero.


(** * Preadditive structure on the category of abelian groups
   - Binary operation on homsets.
   - Abelian group structure on homsets
   - PreAdditive structure on the category of abelian groups
*)
Section abgr_preadditive.

  (** ** Binary operations on homsets
      Let f, g : X --> Y be morphisms in the category of abelian groups. Then f + g is defined to be
      the morphism (f + g) x = (f x) + (g x). This gives [precategoryWithBinOps] structure on the
      category.
  *)

  Definition abgr_WithBinOpsData : precategoryWithBinOpsData abelian_group_category.
  Proof.
    intros X Y. exact (@abgrshombinop (X : abgr) (Y : abgr)).
  Defined.

  Definition abgr_WithBinOps : precategoryWithBinOps :=
    make_precategoryWithBinOps abelian_group_category abgr_WithBinOpsData.

  (** ** [categoryWithAbgrops] structure on the category of abelian groups *)

  Definition abgr_WithAbGrops : categoryWithAbgrops.
  Proof.
    use make_categoryWithAbgrops.
    - exact abgr_WithBinOps.
    - apply make_categoryWithAbgropsData.
      intros X Y. exact (@abgrshomabgr_isabgrop X Y).
  Defined.

  (** ** [PreAdditive] structure on the category of abelian groups *)

  Definition abgr_isPreAdditive : isPreAdditive abgr_WithAbGrops.
  Proof.
    apply make_isPreAdditive.
    (* Precomposition with morphism is linear *)
    - intros X Y Z f.
      apply make_ismonoidfun.
      + apply make_isbinopfun. intros g h. apply abelian_group_morphism_eq, funextfun. intros x. reflexivity.
      + apply abelian_group_morphism_eq, funextfun. intros x. reflexivity.
    (* Postcomposition with morphism is linear *)
    - intros X Y Z f.
      apply make_ismonoidfun.
      + apply make_isbinopfun. intros g h. apply abelian_group_morphism_eq. apply funextfun. intros x.
        refine (monoidfunmul (f : abelian_group_morphism _ _) _ _ @ _).
        reflexivity.
      + apply abelian_group_morphism_eq. apply funextfun. intros x. exact (monoidfununel (f : abelian_group_morphism _ _)).
  Qed.

  Definition abgr_PreAdditive : PreAdditive :=
    make_PreAdditive abgr_WithAbGrops abgr_isPreAdditive.

End abgr_preadditive.


(** * Additive structure on the category of abelian groups
   - Direct sums
   - Additive category structure
 *)
Section abgr_additive.

  (** ** Direct sums
     Direct sum of X and Y is given by the direct product abelian group X × Y. The inclusions
     and projections are given by
     - In1 :  x ↦ (x, 0)
     - In2 :  y ↦ (0, y)
     - Pr1 :  (x, y) ↦ x
     - Pr2 :  (x, y) ↦ y
   *)

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
    @isbinopfun A (abgrdirprod A B) (λ a : A, make_dirprod a (unel B)).
  Proof.
    intros x x'.
    apply dirprod_paths.
      + reflexivity.
      + symmetry. apply (runax B).
  Qed.

  Definition abgr_DirectSumIn1 (A B : abgr) : abelian_group_category⟦A, abgrdirprod A B⟧ :=
    make_abelian_group_morphism _ (abgr_DirectSumIn1_isbinopfun A B).

  Lemma abgr_DirectSumIn2_isbinopfun (A B : abgr) :
    @isbinopfun B (abgrdirprod A B) (λ b : B, make_dirprod (unel A) b).
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
    apply abelian_group_morphism_eq. apply funextfun. intros x. reflexivity.
  Qed.

  Lemma abgr_DirectSumIdIn2 (A B : abgr) :
    abgr_DirectSumIn2 A B · abgr_DirectSumPr2 A B = identity B.
  Proof.
    apply abelian_group_morphism_eq. apply funextfun. intros x. reflexivity.
  Qed.

  Lemma abgr_DirectSumUnel1 (A B : abgr) :
    abgr_DirectSumIn1 A B · abgr_DirectSumPr2 A B = @to_unel abgr_PreAdditive A B.
  Proof.
    apply abelian_group_morphism_eq. apply funextfun. intros x. reflexivity.
  Qed.

  Lemma abgr_DirectSumUnel2 (A B : abgr) :
    abgr_DirectSumIn2 A B · abgr_DirectSumPr1 A B = @to_unel abgr_PreAdditive B A.
  Proof.
    apply abelian_group_morphism_eq. apply funextfun. intros x. reflexivity.
  Qed.

  Lemma abgr_DirectSumId (A B : abgr) :
    @abgrshombinop
      (abgrdirprod A B) (abgrdirprod A B)
      (abgr_DirectSumPr1 A B · abgr_DirectSumIn1 A B)
      (abgr_DirectSumPr2 A B · abgr_DirectSumIn2 A B) =
    identity_abelian_group_morphism (abgrdirprod A B).
  Proof.
    apply abelian_group_morphism_eq, funextfun. intros x. apply dirprod_paths.
    - apply (runax A).
    - apply (lunax B).
  Qed.

  Lemma abgr_isBinDirectSum (X Y : abgr) :
    @isBinDirectSum
      abgr_PreAdditive X Y (abgrdirprod X Y) (abgr_DirectSumIn1 X Y) (abgr_DirectSumIn2 X Y)
      (abgr_DirectSumPr1 X Y) (abgr_DirectSumPr2 X Y).
  Proof.
    apply make_isBinDirectSum.
    - exact (abgr_DirectSumIdIn1 X Y).
    - exact (abgr_DirectSumIdIn2 X Y).
    - exact (abgr_DirectSumUnel1 X Y).
    - exact (abgr_DirectSumUnel2 X Y).
    - exact (abgr_DirectSumId X Y).
  Defined.

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

End abgr_additive.


(** * Kernels and Cokernels
   - Kernels in the category of abelian groups
   - Cokernels in the category of abelian groups
 *)
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
    apply funextfun; intro x.
    apply (pr2 x).
  Qed.

  (** *** KernelIn morphism *)

  Section UniversalProperty.

    Context {C : abelian_group_category}.
    Context (h : abelian_group_morphism C A).
    Context (H : h · f = ZeroArrow abgr_Zero C B).

    Lemma abgr_KernelArrowIn_map_property
              (c : (C : abgr)) :
      (f (h c) = 1%multmonoid).
    Proof.
      exact (maponpaths (λ (f : abelian_group_morphism _ _), f c) H).
    Qed.

    Definition abgr_KernelArrowIn_map
               (c : (C : abgr)) : abgr_Kernel_subabgr f.
    Proof.
      use tpair.
      - exact (h c).
      - exact (abgr_KernelArrowIn_map_property c).
    Defined.

    Lemma abgr_KernelArrowIn_isbinopfun :
      @isbinopfun (C : abgr) (@abgr_Kernel_subabgr A B f) abgr_KernelArrowIn_map.
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
      - apply abelian_group_morphism_eq, funextfun. intros x. reflexivity.
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
      apply abelian_group_morphism_eq, funextfun. intros x.
      apply subtypePath.
      {
        intro.
        apply propproperty.
      }
      exact (maponpaths (λ (f : abelian_group_morphism _ _), f x) (pr2 t)).
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

  (** ** Cokernels
     - Let f : X --> Y be a morphism of abelian groups. A cokernel for f is given by the quotient
       quotient group Y/(Im f) together with the canonical morphism Y --> Y/(Im f).
   *)

Section Cokernels.

  (** *** Subgroup gives an equivalence relation. *)

  Context {A B : abgr}.
  Context (f : abelian_group_morphism A B).

  Definition abgr_Cokernel_eqrel_istrans :
    istrans (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    intros x1 x2 x3 y1 y2.
    refine (hinhuniv _ y1). intros y1'.
    refine (hinhuniv _ y2). intros y2'.
    apply hinhpr.
    use tpair.
    - exact (@op A (pr1 y1') (pr1 y2')).
    - apply (pathscomp0 (binopfunisbinopfun f (pr1 y1') (pr1 y2'))).
      rewrite (pr2 y1'). rewrite (pr2 y2').
      rewrite <- assocax. rewrite (assocax _ _ _ x2). rewrite (grlinvax B). rewrite (runax B).
      reflexivity.
  Qed.

  Definition abgr_Cokernel_eqrel_isrefl :
    isrefl (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    intros x1 P X. apply X. clear P X.
    use tpair.
    - exact (unel A).
    - cbn. rewrite (grrinvax B). apply (monoidfununel f).
  Qed.

  Definition abgr_Cokernel_eqrel_issymm :
    issymm (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
  Proof.
    intros x1 x2 x3.
    refine (hinhuniv _ x3). intros x3'.
    intros P X. apply X. clear P X.
    use tpair.
    - exact (grinv A (pr1 x3')).
    - refine (group_morphism_inv f (pr1 x3') @ _).
      rewrite (pr2 x3'). rewrite grinvop. apply two_arg_paths.
      + apply grinvinv.
      + reflexivity.
  Qed.

  Definition abgr_Cokernel_eqrel : eqrel B :=
    @eqrelconstr B (λ b1 : B, λ b2 : B, ∃ a : A, (f a) = (op b1 (grinv B b2)))
                 abgr_Cokernel_eqrel_istrans abgr_Cokernel_eqrel_isrefl
                 abgr_Cokernel_eqrel_issymm.

  (** *** Construction of the quotient abelian group Y/(Im f) *)

  Definition abgr_Cokernel_abgr_isbinoprel :
    isbinophrel (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv B b2)%multmonoid).
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
    @abgrquot B (make_binopeqrel abgr_Cokernel_eqrel abgr_Cokernel_abgr_isbinoprel).

  (** *** The canonical morphism Y --> Y/(Im f) *)

  Lemma abgr_CokernelArrow_isbinopfun :
    @isbinopfun B abgr_Cokernel_abgr (setquotpr abgr_Cokernel_eqrel).
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
    apply abelian_group_morphism_eq. apply funextfun. intros a.
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
      iscomprelfun (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv (abgrtogr B) b2)%multmonoid)
                  h.
    Proof.
      intros x x' X.
      apply (squash_to_prop X (setproperty (C : abgr) (h x) (h x'))). intros X'.
      apply (grrcan (abgrtogr C) ((h) (grinv (abgrtogr B) x'))).
      refine (_ @ (binopfunisbinopfun
                          (h : abelian_group_morphism (B : abgr) (C : abgr)) x' (grinv (B : abgr) x'))).
      refine (_ @ (! maponpaths (λ xx : (B : abgr), h xx) (grrinvax (B : abgr) x'))).
      refine (_ @ (! (monoidfununel h))).
      refine (_ @ maponpaths (λ (f : abelian_group_morphism _ _), f _) H).
      refine ((! (binopfunisbinopfun
                            (h : abelian_group_morphism (B : abgr) (C : abgr)) x (grinv (B : abgr) x'))) @ _).
      apply (maponpaths h). exact (!pr2 X').
    Qed.

    Definition abgr_CokernelOut_map :
      abgr_Cokernel_abgr → C :=
      setquotuniv (λ b1 b2 : B, ∃ a : A, f a = (b1 * grinv (abgrtogr B) b2)%multmonoid)
                  C h abgr_CokernelArrowOutUniv_iscomprelfun.

    Definition abgr_CokernelOut_isbinopfun :
      @isbinopfun abgr_Cokernel_abgr C abgr_CokernelOut_map.
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
      apply abelian_group_morphism_eq. apply funextfun. intros x. reflexivity.
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
      apply abelian_group_morphism_eq. apply funextfun. intros x.
      apply (squash_to_prop (abgr_Cokernel_abelian_group_morphism_issurjective x) (setproperty C _ _)).
      intros hf. rewrite <- (hfiberpr2 _ _ hf).
      exact (maponpaths (λ (f : abelian_group_morphism _ _), f _) (pr2 t)).
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


(** * Monics are injective and epis are surjective
   - Epis are surjective
   - Monics are injective
*)
Section abgr_monics_and_epis.

  (** ** Epis *)

  Definition abgr_epi_hfiber_inhabited
             {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isE : isEpi f) (b : B)
             (H : setquotpr (abgr_Cokernel_eqrel f) b =
                  setquotpr (abgr_Cokernel_eqrel f) 1%multmonoid) : ∥ hfiber (pr1 f) b ∥.
  Proof.
    set (tmp := weqpathsinsetquot (abgr_Cokernel_eqrel f) b (unel _)).
    apply (hinhuniv _ ((invweq tmp) H)). intros Y. apply hinhpr. induction Y as [t p].
    rewrite grinvunel in p. rewrite (runax B) in p.
    exact (make_hfiber (pr1 f) t p).
  Qed.

  Definition abgr_epi_issurjective {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isE : isEpi f) :
    issurjective (pr1 f).
  Proof.
    intros x. apply abgr_epi_hfiber_inhabited.
    - exact isE.
    - set (tmp := isE (abgr_Cokernel_abgr f) (abgr_CokernelArrow f)
                      (unelabgrfun B (abgr_Cokernel_abgr f))).
      assert (H : f · abgr_CokernelArrow f = f · unelabgrfun B (abgr_Cokernel_abgr f)).
      {
        rewrite abgr_Cokernel_eq.
        rewrite <- abgr_Zero_arrow_comp.
        rewrite ZeroArrow_comp_right.
        reflexivity.
      }
      exact (toforallpaths _ _ _ (base_paths _ _ (tmp H)) x).
  Qed.


  (** ** Monics *)

  Lemma nat_nat_prod_abgr_abelian_group_morphism_eq {A B : abgr} (a1 a2 : A) (f : abelian_group_morphism A B)
        (H : f a1 = f a2) : monoidfuncomp (nat_nat_prod_abmonoid_abelian_group_morphism a1) f =
                            monoidfuncomp (nat_nat_prod_abmonoid_abelian_group_morphism a2) f.
  Proof.
    apply abelian_group_morphism_eq. apply funextfun. intros x. induction x as [x1 x2]. cbn.
    unfold nataddabmonoid_nataddabmonoid_to_monoid_fun.
    unfold nat_nat_to_monoid_fun. Opaque nat_to_monoid_fun. cbn.
    apply (pathscomp0 (binopfunisbinopfun f _ _)).
    apply (pathscomp0 _ (! (binopfunisbinopfun f _ _))). cbn.
    rewrite (abelian_group_morphism_nat_to_monoid_fun f a1 x1).
    rewrite (abelian_group_morphism_nat_to_monoid_fun f a2 x1).
    rewrite (abelian_group_morphism_nat_to_monoid_fun f (grinv A a1) x2).
    rewrite (abelian_group_morphism_nat_to_monoid_fun f (grinv A a2) x2).
    apply two_arg_paths.
    - induction H. reflexivity.
    - assert (e : f (grinv A a1) = f (grinv A a2)). {
        apply (@grlcan B _ _ (pr1 f a1)).
        apply (pathscomp0 (! binopfunisbinopfun f a1 (grinv A a1))).
        apply (pathscomp0 (maponpaths (pr1 f) (grrinvax A a1))).
        cbn in H. rewrite H.
        apply (pathscomp0 _ (binopfunisbinopfun f a2 (grinv A a2))).
        apply (pathscomp0 _ (! (maponpaths (pr1 f) (grrinvax A a2)))).
        reflexivity.
      }
      induction e. reflexivity.
  Qed.
  Transparent nat_to_monoid_fun.

  Lemma abgr_abelian_group_morphism_precomp {A :abmonoid} {B C : abgr} (f1 f2 : abelian_group_morphism B C)
        (g : abelian_group_morphism A B) (H : issurjective (pr1 g)) :
    monoidfuncomp g f1 = monoidfuncomp g f2 -> f1 = f2.
  Proof.
    intros e. apply abelian_group_morphism_eq. apply funextfun. intros x.
    apply (squash_to_prop (H x) (setproperty C _ _)). intros hf.
    rewrite <- (hfiberpr2 _ _ hf).
    exact (toforallpaths _ _ _ (base_paths _ _ e) (hfiberpr1 _ _ hf)).
  Qed.

  Lemma hz_abgr_fun_monoifun_paths {A B : abgr} (a1 a2 : A) (f : abelian_group_morphism A B) (H : f a1 = f a2) :
    monoidfuncomp (hz_abgr_fun_abelian_group_morphism a1) f = monoidfuncomp (hz_abgr_fun_abelian_group_morphism a2) f.
  Proof.
    apply (@abgr_abelian_group_morphism_precomp
           (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig))
           hzaddabgr B
           (monoidfuncomp (hz_abgr_fun_abelian_group_morphism a1) f)
           (monoidfuncomp (hz_abgr_fun_abelian_group_morphism a2) f)
           hz_abmonoid_abelian_group_morphism).
    - apply issurjsetquotpr.
    - rewrite monoidfunassoc. rewrite monoidfunassoc.
      rewrite abgr_natnat_hz_X_comm. rewrite abgr_natnat_hz_X_comm.
      exact (nat_nat_prod_abgr_abelian_group_morphism_eq a1 a2 f H).
  Qed.

  Definition abgr_monic_isincl {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isM : isMonic f) :
    isincl (pr1 f).
  Proof.
    intros b h1 h2.
    use make_iscontr.
    - apply total2_paths_f.
      + set (e := hfiberpr2 _ _ h1 @ (! hfiberpr2 _ _ h2)).
        set (tmp := isM hzaddabgr (hz_abgr_fun_abelian_group_morphism (h1))
                        (hz_abgr_fun_abelian_group_morphism (h2))
                        (hz_abgr_fun_monoifun_paths (h1) (h2) f e)).
        set (e' := toforallpaths _ _ _ (base_paths _ _ tmp) hzone).
        apply (grrcan A (unel A)). apply (grrcan A (unel A)). exact e'.
      + apply proofirrelevance. apply (setproperty B).
    - intros t. apply proofirrelevance. apply isaset_hfiber.
      + apply setproperty.
      + apply setproperty.
  Qed.

  Definition abgr_monic_isInjective {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isM : isMonic f) :
    isInjective (pr1 f).
  Proof.
    exact (isweqonpathsincl (pr1 f) (abgr_monic_isincl f isM)).
  Qed.

  Lemma abgr_monic_paths {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isM : isMonic f) (a1 a2 : A) :
    pr1 f a1 = pr1 f a2 -> a1 = a2.
  Proof.
    exact (invweq (make_weq _ (abgr_monic_isInjective f isM a1 a2))).
  Qed.

  Lemma abgr_abelian_group_morphism_postcomp {A B C : abgr} (f1 f2 : abelian_group_morphism A B) (g : abelian_group_morphism B C)
        (isM : isMonic (g : abelian_group_category⟦B, C⟧)) :
    monoidfuncomp f1 g = monoidfuncomp f2 g -> f1 = f2.
  Proof.
    intros e. apply abelian_group_morphism_eq. apply funextfun. intros x.
    apply (invmap (make_weq _ (abgr_monic_isInjective g isM (pr1 f1 x) (pr1 f2 x)))).
    exact (toforallpaths _ _ _ (base_paths _ _ e) x).
  Qed.

End abgr_monics_and_epis.


(** * Monics are kernels of their cokernels and epis are cokernels of their kernels *)
Section abgr_monic_kernels_epi_cokernels.


  (** ** Monics are kernels of their cokernels *)

  Definition abgr_monic_kernel_in_hfiber_iscontr {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
             (isM : isMonic f) (h : abelian_group_category⟦C, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) =
                  ZeroArrow abgr_Zero C (abgr_Cokernel f)) (c : C) :
    iscontr (hfiber (pr1 f) (h c)).
  Proof.
    apply (squash_to_prop
           ((invweq (weqpathsinsetquot (abgr_Cokernel_eqrel f) (h c) (unel _)))
              (toforallpaths _ _ _ (base_paths _ _ H) c)) (isapropiscontr _)).
    intros hf.
    use make_iscontr.
    - apply make_hfiber.
      + exact (pr1 hf).
      + apply (pathscomp0 (pr2 hf)). rewrite grinvunel. apply (runax B).
    - intros t. apply total2_paths_f.
      + apply (invmap (make_weq _ (abgr_monic_isInjective f isM (pr1 t) (pr1 hf)))).
        apply (pathscomp0 (hfiberpr2 _ _ t)). apply (pathscomp0 _ (! (pr2 hf))).
        rewrite grinvunel. rewrite runax. reflexivity.
      + apply proofirrelevance. apply (setproperty B).
  Qed.

  Lemma abgr_monic_kernel_in_hfiber_mult_eq {A B : abgr} (f : abelian_group_category⟦A, B⟧)
        (w : abgr) (x x' : w) (h : abelian_group_category⟦w, B⟧) (X : hfiber (pr1 f) (pr1 h x))
        (X0 : hfiber (pr1 f) (pr1 h x')) :
    pr1 f (pr1 X * pr1 X0)%multmonoid = pr1 h (x * x')%multmonoid.
  Proof.
    rewrite (pr1 (pr2 f)).
    rewrite (pr2 X).
    rewrite (pr2 X0).
    rewrite (pr1 (pr2 h)).
    reflexivity.
  Qed.

  Definition abgr_monic_kernel_in_hfiber_mult {A B : abgr} (f : abelian_group_category⟦A, B⟧)
             (w : abgr) (x x' : w) (h : abelian_group_category⟦w, B⟧) :
    hfiber (pr1 f) (pr1 h x) -> hfiber (pr1 f) (pr1 h x')
    -> hfiber (pr1 f) (pr1 h (x * x')%multmonoid).
  Proof.
    intros X X0.
    exact (make_hfiber (pr1 f) ((pr1 X) * (pr1 X0))%multmonoid
                      (abgr_monic_kernel_in_hfiber_mult_eq f w x x' h X X0)).
  Defined.

  Lemma abgr_monic_kernel_in_hfiber_unel_eq {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
        (h : abelian_group_category⟦C, B⟧) : pr1 f 1%multmonoid = pr1 h 1%multmonoid.
  Proof.
    rewrite (pr2 (pr2 h)). apply (pr2 (pr2 f)).
  Qed.

  Definition abgr_monic_kernel_in_hfiber_unel {A B : abgr} (f : abelian_group_category⟦A, B⟧) (w : abgr)
             (h : abelian_group_category⟦w, B⟧) : hfiber (pr1 f) (pr1 h 1%multmonoid) :=
    make_hfiber (pr1 f) 1%multmonoid (abgr_monic_kernel_in_hfiber_unel_eq f h).

  Definition abgr_monic_kernel_in {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isM : isMonic f)
             (w : abgr) (h: abelian_group_category⟦w, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero _ _) : w -> A.
  Proof.
    intros x.
    exact (hfiberpr1 _ _ (iscontrpr1 (@abgr_monic_kernel_in_hfiber_iscontr A B w f isM h H x))).
  Defined.

  Definition abgr_monic_kernel_in_isbinopfun {A B : abgr} (f : abelian_group_category⟦A, B⟧)
             (isM : isMonic f) (w : abgr) (h: abelian_group_category⟦w, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero _ _) :
    isbinopfun (abgr_monic_kernel_in f isM w h H).
  Proof.
    apply make_isbinopfun.
    - apply make_isbinopfun. intros x x'.
      set (t := abgr_monic_kernel_in_hfiber_iscontr f isM h H x).
      set (tmp := abgr_monic_kernel_in_hfiber_mult
                    f w x x' h
                    (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H x))
                    (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H x'))).
      apply pathscomp0.
      + exact (hfiberpr1 _ _ tmp).
      + unfold abgr_monic_kernel_in.
        apply (invmap (make_weq _ (abgr_monic_isInjective f isM _ _))).
        apply (pathscomp0 (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr
                                                      f isM h H (x * x')%multmonoid)))).
        apply pathsinv0.
        exact (hfiberpr2 _ _ tmp).
      + reflexivity.
    - assert (e : iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H 1%multmonoid)
                  = (abgr_monic_kernel_in_hfiber_unel f w h)).
      {
        apply total2_paths_f.
        - apply (invmap (make_weq _ (abgr_monic_isInjective f isM _ _))).
          apply (pathscomp0 (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr
                                                        f isM h H 1%multmonoid)))).
          apply pathsinv0.
          exact (hfiberpr2 _ _ (abgr_monic_kernel_in_hfiber_unel f w h)).
        - apply proofirrelevance. apply setproperty.
      }
      exact (base_paths _ _ e).
  Qed.

  Definition abgr_monic_kernel_in_abelian_group_morphism {A B : abgr} (f : abelian_group_category⟦A, B⟧)
             (isM : isMonic f) (w : abgr) (h: abelian_group_category⟦w, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero _ _) :
    abelian_group_morphism w A := make_abelian_group_morphism _ (abgr_monic_kernel_in_isbinopfun f isM w h H).

  Definition abgr_monic_Kernel_eq {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isM : isMonic f) :
    f · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero A (abgr_Cokernel f).
  Proof.
    apply CokernelCompZero.
  Qed.

  Lemma abgr_monic_Kernel_isKernel_comm {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
        (isM : isMonic f) (h : abelian_group_category⟦C, B⟧)
        (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f)):
    monoidfuncomp (abgr_monic_kernel_in_abelian_group_morphism f isM C h H) f = h.
  Proof.
    apply abelian_group_morphism_eq. apply funextfun. intros x.
    exact (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H x))).
  Qed.

  Definition make_abgr_monic_Kernel_isKernel {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
             (isM : isMonic f) (h : abelian_group_category⟦C, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f)) :
    ∑ ψ : abelian_group_category ⟦C, A⟧, ψ · f = h.
  Proof.
    apply tpair.
    - exact (abgr_monic_kernel_in_abelian_group_morphism f isM C h H).
    - exact (abgr_monic_Kernel_isKernel_comm f isM h H).
  Defined.

  Definition abgr_monic_Kernel_isKernel_uniqueness {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
             (isM : isMonic f) (h : abelian_group_category⟦C, B⟧)
             (H : h · CokernelArrow (abgr_Cokernel f) = ZeroArrow abgr_Zero C (abgr_Cokernel f))
             (t : ∑ ψ : abelian_group_category ⟦C, A⟧, ψ · f = h) :
    t = make_abgr_monic_Kernel_isKernel f isM h H.
  Proof.
    apply total2_paths_f.
    - apply abelian_group_morphism_eq. apply funextfun. intros x.
      apply (invmap (make_weq _ (abgr_monic_isInjective f isM _ _))).
      apply (pathscomp0 (toforallpaths _ _ _ (base_paths _ _ (pr2 t)) x)).
      apply pathsinv0.
      exact (hfiberpr2 _ _ (iscontrpr1 (abgr_monic_kernel_in_hfiber_iscontr f isM h H x))).
    - apply proofirrelevance. apply setproperty.
  Qed.

  Definition abgr_monic_Kernel_isKernel {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isM : isMonic f) :
    isKernel abgr_Zero f (CokernelArrow (abgr_Cokernel f))
             (CokernelCompZero abgr_Zero (abgr_Cokernel f)).
  Proof.
    apply make_isKernel.
    - intros w h H.
      use make_iscontr.
      + exact (make_abgr_monic_Kernel_isKernel f isM h H).
      + exact (abgr_monic_Kernel_isKernel_uniqueness f isM h H).
  Defined.

  Definition abgr_monic_kernel {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isM : isMonic f) :
    Kernel abgr_Zero (CokernelArrow (abgr_Cokernel f)) :=
    make_Kernel abgr_Zero f (CokernelArrow (abgr_Cokernel f)) (abgr_monic_Kernel_eq f isM)
              (abgr_monic_Kernel_isKernel f isM).

  Lemma abgr_monic_kernel_comp {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isM : isMonic f) :
    KernelArrow (abgr_monic_kernel f isM) = f.
  Proof.
    reflexivity.
  Qed.


  (** ** Epis are cokernels of their kernels *)

  Definition abgr_epi_cokernel_out_kernel_hsubtype {A B : abgr}
             (f : abelian_group_category⟦A, B⟧) (a : A)
             (H : pr1 f a = 1%multmonoid) : abgr_kernel_hsubtype f.
  Proof.
    exact (a,, H).
  Defined.

  Lemma abgr_epi_cokernel_out_data_eq {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
        (isE : isEpi f) (h : abelian_group_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C) :
    ∏ x : abgr_kernel_hsubtype f, pr1 h (pr1carrier (abgr_kernel_hsubtype f) x) = 1%multmonoid.
  Proof.
    exact (toforallpaths _ _ _ (base_paths _ _ H)).
  Qed.

  Lemma abgr_epi_cokernel_out_data_hfibers_to_unel {A B : abgr} (f : abelian_group_category⟦A, B⟧) (b : B)
        (hfib1 hfib2 : hfiber (pr1 f) b) :
    (pr1 f) ((pr1 hfib1) * (grinv A (pr1 hfib2)))%multmonoid = unel B.
  Proof.
    rewrite (pr1 (pr2 f)).
    apply (grrcan (abgrtogr B) (pr1 f (pr1 hfib2))).
    rewrite (assocax B). rewrite <- (pr1 (pr2 f)).
    rewrite (grlinvax A). rewrite (pr2 (pr2 f)).
    rewrite (runax B). rewrite (lunax B).
    rewrite (pr2 hfib1). rewrite (pr2 hfib2).
    reflexivity.
  Qed.

  Lemma abgr_epi_cokernel_out_data_hfiber_eq {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
        (isE : isEpi f) (h : abelian_group_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) (b : B)
        (X : hfiber (pr1 f) b) : ∏ hfib : hfiber (pr1 f) b, pr1 h (pr1 hfib) = pr1 h (pr1 X).
  Proof.
    intros hfib.
    apply (grrcan C (grinv (abgrtogr C) (pr1 h (pr1 X)))).
    rewrite (grrinvax C).
    set (e1 := abgr_epi_cokernel_out_data_hfibers_to_unel f b hfib X).
    set (tmp1 := ! (monoidfuninvtoinv h (hfiberpr1 _ _ X))). cbn in tmp1.
    apply (pathscomp0 (maponpaths (λ k : _, ((pr1 h (pr1 hfib)) * k)%multmonoid) tmp1)).
    rewrite <- (pr1 (pr2 h)).
    set (tmp2 := abgr_epi_cokernel_out_data_eq f isE h H).
    set (tmp3 := abgr_epi_cokernel_out_kernel_hsubtype
                   f (pr1 hfib * grinv A (pr1 X))%multmonoid e1).
    set (tmp4 := tmp2 tmp3). cbn in tmp4. exact tmp4.
  Qed.

  Lemma abgr_epi_CokernelOut_iscontr {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
        (isE : isEpi f) (h : abelian_group_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) (b : B) :
    iscontr (∑ x : C, ∏ (hfib : hfiber (pr1 f) b), pr1 h (pr1 hfib) = x).
  Proof.
    apply (squash_to_prop (abgr_epi_issurjective f isE b) (isapropiscontr _)).
    intros X. use make_iscontr.
    - apply tpair.
      + exact (pr1 h (pr1 X)).
      + exact (abgr_epi_cokernel_out_data_hfiber_eq f isE h H b X).
    - intros t. apply total2_paths_f.
      + exact (! ((pr2 t) X)).
      + apply proofirrelevance. apply impred. intros t0. apply (setproperty C).
  Defined.

  Definition abgr_epi_CokernelOut_mult_eq {A B C : abgr} (b1 b2 : B)
             (f : abelian_group_category⟦A, B⟧) (isE : isEpi f) (h : abelian_group_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _)
             (X : ∑ x : C, ∏ hfib : hfiber (pr1 f) b1, pr1 h (pr1 hfib) = x)
             (X0 : ∑ x : C, ∏ hfib : hfiber (pr1 f) b2, pr1 h (pr1 hfib) = x) :
    ∏ hfib : hfiber (pr1 f) (b1 * b2)%multmonoid, pr1 h (pr1 hfib) = (pr1 X * pr1 X0)%multmonoid.
  Proof.
    intros hfib.
    apply (squash_to_prop (abgr_epi_issurjective f isE b1) (setproperty C _ _)). intros X1.
    apply (squash_to_prop (abgr_epi_issurjective f isE b2) (setproperty C _ _)). intros X2.
    rewrite <- ((pr2 X) X1). rewrite <- ((pr2 X0) X2). rewrite <- (pr1 (pr2 h)).
    exact (abgr_epi_cokernel_out_data_hfiber_eq
             f isE h H (b1 * b2)%multmonoid (hfiberbinop (f : abelian_group_morphism _ _) b1 b2 X1 X2) hfib).
  Qed.

  Definition abgr_epi_cokernel_out_data_mult {A B C : abgr} (b1 b2 : B)
             (f : abelian_group_category⟦A, B⟧) (isE : isEpi f) (h : abelian_group_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    (∑ x : C, ∏ (hfib : hfiber (pr1 f) b1), pr1 h (pr1 hfib) = x) ->
    (∑ x : C, ∏ (hfib : hfiber (pr1 f) b2), pr1 h (pr1 hfib) = x) ->
    (∑ x : C, ∏ (hfib : hfiber (pr1 f) (b1 * b2)%multmonoid), pr1 h (pr1 hfib) = x).
  Proof.
    intros X X0.
    exact (tpair _ ((pr1 X) * (pr1 X0))%multmonoid
                 (abgr_epi_CokernelOut_mult_eq b1 b2 f isE h H X X0)).
  Defined.

  Definition abgr_epi_cokernel_out_data_unel_eq {A B C : abgr}
             (f : abelian_group_category⟦A, B⟧) (isE : isEpi f) (h : abelian_group_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    ∏ hfib : hfiber (pr1 f) 1%multmonoid, pr1 h (pr1 hfib) = 1%multmonoid.
  Proof.
    intros hfib.
    set (hfib_unel := make_hfiber (pr1 f) 1%multmonoid (pr2 (pr2 f))).
    rewrite (abgr_epi_cokernel_out_data_hfiber_eq f isE h H 1%multmonoid hfib_unel hfib).
    exact (monoidfununel h).
  Qed.

  Definition abgr_epi_cokernel_out_data_unel {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
             (isE : isEpi f) (h : abelian_group_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    ( ∑ x : C, ∏ (hfib : hfiber (pr1 f) 1%multmonoid),  pr1 h (pr1 hfib) = x) :=
    tpair _ 1%multmonoid (abgr_epi_cokernel_out_data_unel_eq f isE h H).

  Lemma abgr_epi_cokernel_out_isbinopfun {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
        (isE : isEpi f) (h : abelian_group_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    isbinopfun (λ b : B, (pr1 (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H b)))).
  Proof.
    apply make_isbinopfun.
    - apply make_isbinopfun. intros x x'.
      set (HH0 := abgr_epi_cokernel_out_data_mult
                    x x' f isE h H
                    (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H x))
                    (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H x'))).
      assert (HH : iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H (x * x')%multmonoid) = HH0).
      {
        set (tmp := abgr_epi_CokernelOut_iscontr f isE h H (x * x')%multmonoid).
        rewrite (pr2 tmp). apply pathsinv0. rewrite (pr2 tmp).
        reflexivity.
      }
      exact (base_paths _ _ HH).
    - assert (HH : iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H 1%multmonoid)
                   = abgr_epi_cokernel_out_data_unel f isE h H).
      {
        rewrite (pr2 (abgr_epi_CokernelOut_iscontr f isE h H 1%multmonoid)).
        apply pathsinv0.
        rewrite (pr2 (abgr_epi_CokernelOut_iscontr f isE h H 1%multmonoid)).
        reflexivity.
      }
      exact (base_paths _ _ HH).
  Qed.

  Definition abgr_epi_cokernel_out_abelian_group_morphism {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
             (isE : isEpi f) (h : abelian_group_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero _ _) :
    abelian_group_morphism B C := make_abelian_group_morphism _ (abgr_epi_cokernel_out_isbinopfun f isE h H).

  Definition abgr_epi_cokernel_eq {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isE : isEpi f) :
    KernelArrow (abgr_Kernel f) · f = ZeroArrow abgr_Zero _ _.
  Proof.
    apply KernelCompZero.
  Qed.

  Lemma abgr_epi_cokernel_isCokernel_comm {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
             (isE : isEpi f)  (h : abelian_group_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C) :
    f · abgr_epi_cokernel_out_abelian_group_morphism f isE h H = h.
  Proof.
    apply total2_paths_f.
    - apply funextfun. intros x. apply pathsinv0.
      exact (pr2 (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H (pr1 f x)))
                 (@make_hfiber _ _ (pr1 f) (pr1 f x) x (idpath _))).
    - apply proofirrelevance. apply isapropisbinopfun.
  Qed.

  Definition make_abgr_epi_cokernel_isCokernel {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
             (isE : isEpi f)  (h : abelian_group_category⟦A, C⟧)
             (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C) :
    ∑ ψ : abelian_group_category ⟦B, C⟧, f · ψ = h.
  Proof.
    apply tpair.
    - exact (abgr_epi_cokernel_out_abelian_group_morphism f isE h H).
    - exact (abgr_epi_cokernel_isCokernel_comm f isE h H).
  Defined.

  Lemma abgr_epi_cokernel_isCokernel_uniqueness {A B C : abgr} (f : abelian_group_category⟦A, B⟧)
        (isE : isEpi f)  (h : abelian_group_category⟦A, C⟧)
        (H : KernelArrow (abgr_Kernel f) · h = ZeroArrow abgr_Zero (abgr_Kernel f) C)
        (t : ∑ ψ : abelian_group_category ⟦B, C⟧, f · ψ = h) :
    t = make_abgr_epi_cokernel_isCokernel f isE h H.
  Proof.
    apply total2_paths_f.
    - apply isE. apply (pathscomp0 (pr2 t)). apply abelian_group_morphism_eq. apply funextfun. intros x.
      exact (pr2 (iscontrpr1 (abgr_epi_CokernelOut_iscontr f isE h H (pr1 f x)))
                 (@make_hfiber _ _ (pr1 f) (pr1 f x) x (idpath _))).
    - apply proofirrelevance. apply setproperty.
  Qed.

  Definition abgr_epi_cokernel_isCokernel {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isE : isEpi f) :
    isCokernel abgr_Zero (KernelArrow (abgr_Kernel f)) f (abgr_epi_cokernel_eq f isE).
  Proof.
    apply make_isCokernel.
    - intros w h H. use make_iscontr.
      + exact (make_abgr_epi_cokernel_isCokernel f isE h H).
      + intros t. exact (abgr_epi_cokernel_isCokernel_uniqueness f isE h H t).
  Defined.

  Definition abgr_epi_cokernel {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isE : isEpi f) :
    Cokernel abgr_Zero (KernelArrow (abgr_Kernel f)) :=
    make_Cokernel abgr_Zero (KernelArrow (abgr_Kernel f)) f _ (abgr_epi_cokernel_isCokernel f isE).

  Definition abgr_epi_cokernel_comp {A B : abgr} (f : abelian_group_category⟦A, B⟧) (isE : isEpi f) :
    CokernelArrow (abgr_epi_cokernel f isE) = f.
  Proof.
    reflexivity.
  Qed.

End abgr_monic_kernels_epi_cokernels.


(** * Category of abelian groups is an abelian category *)
Section abgr_abelian.

  Definition abgr_Abelian : AbelianPreCat.
  Proof.
    set (BinDS := to_BinDirectSums abgr_Additive).
    apply (make_Abelian abelian_group_category).
    - apply make_Data1.
      + exact abgr_Zero.
      + intros X Y. exact (BinDirectSum_BinProduct abgr_Additive (BinDS X Y)).
      + intros X Y. exact (BinDirectSum_BinCoproduct abgr_Additive (BinDS X Y)).
    - apply make_AbelianData.
      + apply make_Data2.
        * intros A B f. exact (abgr_Kernel f).
        * intros A B f. exact (abgr_Cokernel f).
      + apply make_MonicsAreKernels.
        intros x y M.
        exact (KernelisKernel abgr_Zero (abgr_monic_kernel M (MonicisMonic abelian_group_category M))).
      + apply make_EpisAreCokernels.
        intros x y E.
        exact (CokernelisCokernel abgr_Zero (abgr_epi_cokernel E (EpiisEpi abelian_group_category E))).
  Defined.

End abgr_abelian.


(** * Corollaries to additive categories
   In an additive category the homsets are abelian groups and pre- and postcompositions are
   morphisms of abelian groups. In this section we prove the following lemmas about additive
   categories using the theory of abelian groups developed above
   - A morphism φ in an additive category which gives isomorphisms (φ · _) and (_ · φ) is an
     isomorphism, [abgr_Additive_premor_postmor_is_iso].
   - A criteria of being a kernel in the category of abelian groups which applys only elements
     of abelian groups, [abgr_isKernel_Criteria].
*)
Section abgr_corollaries.

  (** ** Isomorphism criteria *)

  (** *** (_ · ZeroArrow) = ZeroArrow = (ZeroArrow · _) *)

  Lemma AdditiveZeroArrow_postmor_Abelian {Add : CategoryWithAdditiveStructure} (x y z : Add) :
    to_postmor_abelian_group_morphism Add x y z (ZeroArrow (Additive.to_Zero Add) y z) =
    ZeroArrow (to_Zero abgr_Abelian) (@to_abgr Add x y) (@to_abgr Add x z).
  Proof.
    rewrite <- PreAdditive_unel_zero.
    apply abelian_group_morphism_eq. apply funextfun. intros f. exact (to_premor_unel Add z f).
  Qed.

  Lemma AdditiveZeroArrow_premor_Abelian {Add : CategoryWithAdditiveStructure} (x y z : Add) :
    to_premor_abelian_group_morphism Add x y z (ZeroArrow (Additive.to_Zero Add) x y) =
    ZeroArrow (to_Zero abgr_Abelian) (@to_abgr Add y z) (@to_abgr Add x z).
  Proof.
    rewrite <- PreAdditive_unel_zero.
    apply abelian_group_morphism_eq. apply funextfun. intros f. exact (to_postmor_unel Add x f).
  Qed.

  (** *** f isomorphism ⇒ (f · _) isomorphism *)

  Local Lemma abgr_Additive_is_iso_premor_inverses {Add : CategoryWithAdditiveStructure} (x y z : Add) {f : x --> y}
        (H : is_z_isomorphism f) :
    is_inverse_in_precat ((to_premor_abelian_group_morphism Add x y z f) : abgr_Abelian⟦_, _⟧)
                         (to_premor_abelian_group_morphism Add y x z (is_z_isomorphism_mor H)).
  Proof.
    apply make_is_inverse_in_precat.
    - apply abelian_group_morphism_eq. apply funextfun.
      intros x0. cbn. unfold to_premor. rewrite assoc.
      rewrite (is_inverse_in_precat2 H). apply id_left.
    - apply abelian_group_morphism_eq. apply funextfun.
      intros x0. cbn. unfold to_premor. rewrite assoc.
      rewrite (is_inverse_in_precat1 H). apply id_left.
  Qed.

  Lemma abgr_Additive_is_iso_premor {Add : CategoryWithAdditiveStructure} (x y z : Add) {f : x --> y}
        (H : is_z_isomorphism f) :
    @is_z_isomorphism abgr_Abelian _ _ (to_premor_abelian_group_morphism Add x y z f).
  Proof.
    apply make_is_z_isomorphism.
    - exact (to_premor_abelian_group_morphism Add _ _ z (is_z_isomorphism_mor H)).
    - exact (abgr_Additive_is_iso_premor_inverses _ _ z H).
  Defined.

  (** *** f isomorphism ⇒ (_ · f) isomorphism *)

  Local Lemma abgr_Additive_is_iso_postmor_inverses {Add : CategoryWithAdditiveStructure} (x y z : Add) {f : y --> z}
        (H : is_z_isomorphism f) :
    is_inverse_in_precat ((to_postmor_abelian_group_morphism Add x y z f) : abgr_Abelian⟦_, _⟧)
                         (to_postmor_abelian_group_morphism Add x z y (is_z_isomorphism_mor H)).
  Proof.
    apply make_is_inverse_in_precat.
    - apply abelian_group_morphism_eq. apply funextfun.
      intros x0. cbn. unfold to_postmor. rewrite <- assoc.
      rewrite (is_inverse_in_precat1 H). apply id_right.
    - apply abelian_group_morphism_eq. apply funextfun.
      intros x0. cbn. unfold to_postmor. rewrite <- assoc.
      rewrite (is_inverse_in_precat2 H). apply id_right.
  Qed.

  Lemma abgr_Additive_is_iso_postmor {Add : CategoryWithAdditiveStructure} (x y z : Add) {f : y --> z}
        (H : is_z_isomorphism f) :
    @is_z_isomorphism abgr_Abelian _ _ (to_postmor_abelian_group_morphism Add x y z f).
  Proof.
    apply make_is_z_isomorphism.
    - exact (to_postmor_abelian_group_morphism Add x _ _ (is_z_isomorphism_mor H)).
    - exact (abgr_Additive_is_iso_postmor_inverses x _ _ H).
  Defined.

  (** *** Pre- and postcomposition with f is an isomorphism ⇒ f isomorphism *)

  Local Lemma abgr_Additive_premor_postmor_is_iso_inverses {Add : CategoryWithAdditiveStructure} (x y : Add)
        {f : x --> y}
        (H1 : @is_z_isomorphism abgr_Abelian _ _ (to_premor_abelian_group_morphism Add x y x f))
        (H2 : @is_z_isomorphism abgr_Abelian _ _ (to_postmor_abelian_group_morphism Add y x y f)) :
    is_inverse_in_precat f ((is_z_isomorphism_mor H1 : abelian_group_morphism (to_abgr x x) (to_abgr y x))
                              (identity x : to_abgr x x)).
  Proof.
    set (mor1 := ((is_z_isomorphism_mor H1) : (abelian_group_morphism (to_abgr x x) (to_abgr y x)))
                   ((identity x) : to_abgr x x)).
    set (mor2 := ((is_z_isomorphism_mor H2) : (abelian_group_morphism (to_abgr y y) (to_abgr y x)))
                   ((identity y) : to_abgr y y)).
    assert (Hx : f · mor1 = identity x).
    {
      exact (toforallpaths _ _ _ (base_paths _ _ (is_inverse_in_precat2 H1)) (identity x)).
    }
    assert (Hy : mor2 · f = identity y).
    {
      exact (toforallpaths _ _ _ (base_paths _ _ (is_inverse_in_precat2 H2)) (identity y)).
    }
    assert (H : mor1 = mor2).
    {
      rewrite <- (id_right mor2).
      rewrite <- Hx.
      rewrite assoc.
      rewrite Hy.
      rewrite id_left.
      reflexivity.
    }
    apply make_is_inverse_in_precat.
    - exact Hx.
    - rewrite H. exact Hy.
  Qed.

  Lemma abgr_Additive_premor_postmor_is_iso {Add : CategoryWithAdditiveStructure} (x y : Add) {f : x --> y}
        (H1 : @is_z_isomorphism abgr_Abelian _ _ (to_premor_abelian_group_morphism Add x y x f))
        (H2 : @is_z_isomorphism abgr_Abelian _ _ (to_postmor_abelian_group_morphism Add y x y f)) :
    is_z_isomorphism f.
  Proof.
    apply make_is_z_isomorphism.
    - exact (((is_z_isomorphism_mor H1) : (abelian_group_morphism (to_abgr x x) (to_abgr y x)))
               ((identity x) : to_abgr x x)).
    - exact (abgr_Additive_premor_postmor_is_iso_inverses _ _ H1 H2).
  Defined.


  (** ** A criteria for isKernel which applys only the elements in the abelian group. *)

  Local Opaque ZeroArrow.

  Definition abgr_isKernel_iscontr {X Y Z W : abgr_Abelian} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = @ZeroArrow abgr_Abelian (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic abgr_Abelian _ _ f) (h : W --> Y)
             (H' : h · g = @ZeroArrow abgr_Abelian (to_Zero abgr_Abelian) W Z) (w' : pr1 W) :
    iscontr (∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = pr1 h w').
  Proof.
    cbn in H'. rewrite <- (@PreAdditive_unel_zero (abgr_PreAdditive)) in H'.
    unfold to_unel in H'.
    set (e := toforallpaths _ _ _ (base_paths _ _ H') w').
    set (H'' := H (tpair _ (pr1 h w') e)).
    apply (squash_to_prop H'' (isapropiscontr _)). intros HH.
    induction HH as [H1 H2]. cbn in H2.
    apply tpair.
    - apply tpair.
      + exact H1.
      + exact H2.
    - cbn. intros T. induction T as [T1 T2].
      apply total2_paths_f.
      + apply (abgr_monic_paths f isM T1 H1). cbn in H2. cbn.
        rewrite H2. rewrite T2. reflexivity.
      + apply proofirrelevance. apply setproperty.
  Qed.

  Lemma abgr_isKernel_Criteria_isbinopfun {X Y Z W : abelian_group_category} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D)∥)
             (isM : @isMonic abelian_group_category _ _ f) (h : abgr_Abelian ⟦W, Y⟧)
             (H' : h · g = ZeroArrow (to_Zero abgr_Abelian) W Z) :
    isbinopfun (λ w' : (W : abgr), pr1 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' w'))).
  Proof.
    apply make_isbinopfun.
    - apply make_isbinopfun. intros x y. apply (abgr_monic_paths f isM).
      apply (pathscomp0 _ (! binopfunisbinopfun (f : abelian_group_morphism _ _) _ _)).
      apply (pathscomp0 (pr2 (iscontrpr1 (abgr_isKernel_iscontr
                                          f g ZA H isM h H' ((x * y)%multmonoid))))).
      apply (pathscomp0 (binopfunisbinopfun (h : abelian_group_morphism _ _) _ _)).
      apply pathsinv0.
      apply two_arg_paths.
      + exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' (x%multmonoid)))).
      + exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' (y%multmonoid)))).
    - apply (abgr_monic_paths f isM).
      apply (pathscomp0 (pr2 (iscontrpr1 (abgr_isKernel_iscontr
                                          f g ZA H isM h H' (unel (W : abgr)))))).
      apply (pathscomp0 (monoidfununel h)). exact (! monoidfununel f).
  Qed.

  Lemma abgr_isKernel_Criteria_comm {X Y Z W : abelian_group_category} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic abelian_group_category _ _ f) (h : abgr_Abelian ⟦W, Y⟧)
             (H' : h · g = ZeroArrow (to_Zero abgr_Abelian) W Z) :
    monoidfuncomp (make_abelian_group_morphism _ (abgr_isKernel_Criteria_isbinopfun f g ZA H isM h H')) f = h.
  Proof.
    apply abelian_group_morphism_eq. apply funextfun. intros x.
    exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' (x%multmonoid)))).
  Qed.

  Definition make_abgr_isKernel_Criteria {X Y Z W : abelian_group_category} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic abelian_group_category _ _ f) (h : abgr_Abelian ⟦W, Y⟧)
             (H' : h · g = ZeroArrow (to_Zero abgr_Abelian) W Z) :
    ∑ ψ : abgr_Abelian ⟦W, X⟧, ψ · f = h.
  Proof.
    apply tpair.
    - apply make_abelian_group_morphism _.
      + intros w'. exact (pr1 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' w'))).
      + exact (abgr_isKernel_Criteria_isbinopfun f g ZA H isM h H').
    - exact (abgr_isKernel_Criteria_comm f g ZA H isM h H').
  Defined.

  Lemma abgr_isKernel_Criteria_uniqueness {X Y Z W : abelian_group_category} (f : X --> Y) (g : Y --> Z)
        (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
        (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
             ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
        (isM : @isMonic abelian_group_category _ _ f) (h : abgr_Abelian ⟦W, Y⟧)
        (H' : h · g = ZeroArrow (to_Zero abgr_Abelian) W Z)
        (t : ∑ ψ : abgr_Abelian ⟦W, X⟧, ψ · f = h) :
    t = make_abgr_isKernel_Criteria f g ZA H isM h H'.
  Proof.
    apply total2_paths_f.
    - apply abelian_group_morphism_eq. apply funextfun. intros x.
      apply (abgr_monic_paths f isM).
      apply (pathscomp0 (toforallpaths _ _ _ (base_paths _ _ (pr2 t)) x)). apply pathsinv0.
      exact (pr2 (iscontrpr1 (abgr_isKernel_iscontr f g ZA H isM h H' (x%multmonoid)))).
    - apply proofirrelevance. apply setproperty.
  Qed.

  Definition abgr_isKernel_Criteria {X Y Z : abelian_group_category} (f : X --> Y) (g : Y --> Z)
             (ZA : f · g = ZeroArrow (to_Zero abgr_Abelian) _ _)
             (H : ∏ (D : (∑ y : pr1 Y, pr1 g y = 1%multmonoid)),
                  ∥ ∑ (x : abgrtogr X), monoidfuntobinopfun _ _ f x = (pr1 D) ∥)
             (isM : @isMonic abelian_group_category _ _ f) : isKernel (to_Zero abgr_Abelian) f g ZA.
  Proof.
    apply make_isKernel.
    - intros w h H'. use make_iscontr.
      + exact (make_abgr_isKernel_Criteria f g ZA H isM h H').
      + intros t. exact (abgr_isKernel_Criteria_uniqueness f g ZA H isM h H' t).
  Defined.

End abgr_corollaries.
