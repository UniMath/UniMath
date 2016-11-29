(** * The category of complexes over an additive category *)
(** ** Contents
 - Definition of complexes [def_complexes]
   - Complexes and morphisms between complexes
   - Direct sum of complexes
   - Construction of some complexes from objects
 - The precategory of complexes over an additive precategory [complexes_precategory]
 - The precategory of complexes over an additive precategory is an additive category,
   [complexes_additive]
 - Precategory of complexes over an abelian category is abelian [complexes_abelian]
 - Homotopies and construction of K(A), the naive homotopy category
 - Translation functor
*)
Require Import UniMath.Foundations.Basics.UnivalenceAxiom.
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.BinaryOperations.
Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.
Require Import UniMath.Foundations.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.
Require Import UniMath.CategoryTheory.AdditiveFunctors.


Open Scope hz_scope.
Local Opaque hz isdecrelhzeq hzplus iscommrngops.

(** * Definition of complexes *)
(** ** Introduction
   A complex consists of an objects C_i, for every integer i, and a morphism C_i --> C_{i+1} for
   every i, such that composition of two such morphisms is the zero morphism. One visualizes
   complexes as
                            ... --> C_{i-1} --> C_i --> C_{i+1} --> ...
   A morphism of complexes from a complex C to a complex D is a collection of morphisms C_i --> D_i
   for every integer i, such that for every i the following diagram is commutative
                                 C_i --> C_{i+1}
                                  |        |
                                 D_i --> D_{i+1}

   Composition of morphisms is defined as pointwise composition. It is easy to check that this forms
   a morphisms of complexes. Identity morphism is indexwise identity.

   A direct sum of complexes is given by taking pointwise direct sum of the underlying objects.
   The morphisms between the objects in direct sum complex is given by the following formula
                 Pr1 ;; (C_i --> C_{i+1]) ;; In1 + Pr2 ;; (D_i --> D_{i+1}) ;; In2
   To show that this defines a direct sum in the category of complexes is straightforward. The zero
   complex is given by zero objects and zero morphisms.
*)
Section def_complexes.

  (** ** Basics of complexes *)

  Variable A : Additive.

  (** Complex *)
  Definition Complex : UU :=
    Σ D' : (Σ D : (Π i : hz, ob A), (Π i : hz, A⟦D i, D (hzplus i 1)⟧)),
           Π i : hz, (pr2 D' i) ;; (pr2 D' (hzplus i 1)) = ZeroArrow (Additive.to_Zero A) _ _.

  Definition mk_Complex (D : Π i : hz, ob A) (D' : Π i : hz, A⟦D i, D (hzplus i 1)⟧)
             (D'' : Π i : hz, (D' i) ;; (D' (hzplus i 1)) = ZeroArrow (Additive.to_Zero A) _ _) :
    Complex := ((D,,D'),,D'').

  (** Accessor functions *)
  Definition Complex_Funclass (C : Complex) : hz -> ob A := pr1 (pr1 C).
  Coercion Complex_Funclass : Complex >-> Funclass.

  Definition Diff (C : Complex) (i : hz) : A⟦C i, C (hzplus i 1)⟧ := pr2 (pr1 C) i.

  Definition CEq (C : Complex) (i : hz) :
    (Diff C i) ;; (Diff C (hzplus i 1)) = ZeroArrow (Additive.to_Zero A) _ _ := pr2 C i.

  (** Zero Complex *)
  Definition ZeroComplex : Complex.
  Proof.
    use mk_Complex.
    - intros i. exact (Additive.to_Zero A).
    - intros i. exact (ZeroArrow (Additive.to_Zero A) _ _).
    - intros i. apply ZeroArrowEq.
  Defined.

  (** Direct sum of two complexes *)
  Local Lemma DirectSumComplex_comm {C1 C2 : Complex} (i : hz) :
    let B1 := to_BinDirectSums A (C1 i) (C2 i) in
    let B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1)) in
    let B3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1 + 1)) in
    (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2)
      ;; (BinDirectSumIndAr A (Diff C1 (i + 1)) (Diff C2 (i + 1)) B2 B3) =
    ZeroArrow (Additive.to_Zero A) B1 B3.
  Proof.
    cbn.
    rewrite BinDirectSumIndArComp.
    unfold BinDirectSumIndAr.
    rewrite (CEq C1 i). rewrite ZeroArrow_comp_right.
    rewrite (CEq C2 i). rewrite ZeroArrow_comp_right.
    apply pathsinv0.
    use ToBinDirectSumUnique.
    - apply ZeroArrow_comp_left.
    - apply ZeroArrow_comp_left.
  Qed.

  Definition DirectSumComplex (C1 C2 : Complex) : Complex.
  Proof.
    use mk_Complex.
    - intros i. exact (to_BinDirectSums A (C1 i) (C2 i)).
    - intros i. exact (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) _ _).
    - intros i. exact (DirectSumComplex_comm i).
  Defined.

  (** Morphism of complexes *)
  Definition Morphism (C1 C2 : Complex) : UU :=
    Σ D : (Π i : hz, A⟦C1 i, C2 i⟧), Π i : hz, (D i) ;; (Diff C2 i) = (Diff C1 i) ;; (D (i + 1)).

  Definition mk_Morphism (C1 C2 : Complex) (Mors : Π i : hz, A⟦C1 i, C2 i⟧)
             (Comm : Π i : hz, (Mors i) ;; (Diff C2 i) = (Diff C1 i) ;; (Mors (i + 1))) :
    Morphism C1 C2 := tpair _ Mors Comm.

  (** Accessor functions *)
  Definition MMor {C1 C2 : Complex} (M : Morphism C1 C2) (i : hz) : A⟦C1 i, C2 i⟧ :=
    pr1 M i.

  Definition MComm {C1 C2 : Complex} (M : Morphism C1 C2) (i : hz) :
    (MMor M i) ;; (Diff C2 i) = (Diff C1 i) ;; (MMor M (i + 1)) := pr2 M i.

  (** A lemma to show that two morphisms are the same *)
  Lemma MorphismEq {C1 C2 : Complex} (M1 M2 : Morphism C1 C2)
        (H : Π i : hz, MMor M1 i = MMor M2 i) : M1 = M2.
  Proof.
    use total2_paths.
    - use funextsec. intros i. exact (H i).
    - use proofirrelevance. apply impred_isaprop. intros t. apply to_has_homsets.
  Qed.

  Lemma MorphismEq' {C1 C2 : Complex} (M1 M2 : Morphism C1 C2) (H : M1 = M2) :
    Π i : hz, MMor M1 i = MMor M2 i.
  Proof.
    induction H.
    intros i.
    apply idpath.
  Qed.

  (** The collection of morphism between two complexes is a set *)
  Lemma Morphisms_isaset (C1 C2 : Complex) : isaset (Morphism C1 C2).
  Proof.
    apply isaset_total2.
    - apply impred_isaset.
      intros t. apply to_has_homsets.
    - intros x. apply impred_isaset.
      intros t. apply isasetaprop. apply to_has_homsets.
  Qed.

  Definition Morphisms_hSet (C1 C2 : Complex) : hSet := hSetpair _ (Morphisms_isaset C1 C2).

  (** Identity Morphism *)
  Local Lemma IdMorComm (C1 : Complex) (i : hz) :
    (identity (C1 i)) ;; (Diff C1 i) = (Diff C1 i) ;; (identity (C1 (i + 1))).
  Proof.
    rewrite id_left.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition IdMor (C1 : Complex) : Morphism C1 C1.
  Proof.
    use mk_Morphism.
    - intros i. exact (identity _).
    - intros i. exact (IdMorComm C1 i).
  Defined.

  (** Morphisms from and to Zero complex *)
  Local Lemma MorphismFromZero_comm (C : Complex) (i : hz) :
    (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (C i)) ;; (Diff C i) =
    (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (Additive.to_Zero A))
      ;; (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (C (i + 1))).
  Proof.
    rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left.
    apply idpath.
  Qed.

  Definition MorphismFromZero (C : Complex) : Morphism ZeroComplex C.
  Proof.
    use mk_Morphism.
    - intros i. exact (ZeroArrow (Additive.to_Zero A) _ _).
    - intros i. exact (MorphismFromZero_comm C i).
  Defined.

  Local Lemma MorphismToZero_comm (C : Complex) (i : hz) :
    (ZeroArrow (Additive.to_Zero A) (C i) (Additive.to_Zero A))
      ;; (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (Additive.to_Zero A)) =
    (Diff C i) ;; ZeroArrow (Additive.to_Zero A) (C (i + 1)) (Additive.to_Zero A).
  Proof.
    rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_right.
    apply idpath.
  Qed.

  Definition MorphismToZero (C : Complex) : Morphism C ZeroComplex.
  Proof.
    use mk_Morphism.
    - intros i. exact (ZeroArrow (Additive.to_Zero A) _ _).
    - intros i. exact (MorphismToZero_comm C i).
  Defined.

  (** Composition of morphisms *)
  Local Lemma MorphismCompComm {C1 C2 C3 : Complex} (M1 : Morphism C1 C2) (M2 : Morphism C2 C3)
        (i : hz) :
    (MMor M1 i) ;; (MMor M2 i) ;; (Diff C3 i) =
    (Diff C1 i) ;; (MMor M1 (i + 1) ;; MMor M2 (i + 1)).
  Proof.
    rewrite assoc.
    rewrite <- (MComm M1).
    rewrite <- assoc. rewrite <- assoc.
    apply cancel_precomposition.
    exact (MComm M2 i).
  Qed.

  Definition MorphismComp {C1 C2 C3 : Complex} (M1 : Morphism C1 C2) (M2 : Morphism C2 C3) :
    Morphism C1 C3.
  Proof.
    use mk_Morphism.
    - intros i. exact ((MMor M1 i) ;; (MMor M2 i)).
    - intros i. exact (MorphismCompComm M1 M2 i).
  Defined.

  (** ZeroMorphism as the composite of to zero and from zero *)
  Definition ComplexZeroMorphism (C1 C2 : Complex) : Morphism C1 C2 :=
    MorphismComp (MorphismToZero C1) (MorphismFromZero C2).

  (** ** Direct sums *)

  (** Inclusions and projections from the DirectSumComplex *)
  Local Lemma DirectSumComplexIn1_comm (C1 C2 : Complex) (i : hz) :
    let B1 := to_BinDirectSums A (C1 i) (C2 i) in
    let B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1)) in
    (to_In1 A B1) ;; (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) =
    (Diff C1 i) ;; (to_In1 A B2).
  Proof.
    cbn.
    set (B1 := to_BinDirectSums A (C1 i) (C2 i)).
    set (B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1))).
    rewrite BinDirectSumIndArEq1.
    unfold BinDirectSumIndArFormula.
    rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn1 A B1). rewrite (to_Unel1 A B1).
    rewrite id_left. rewrite to_postmor_unel'. rewrite to_postmor_unel'.
    rewrite to_runax'. apply idpath.
  Qed.

  Definition DirectSumComplexIn1 (C1 C2 : Complex) : Morphism C1 (DirectSumComplex C1 C2).
  Proof.
    use mk_Morphism.
    - intros i. exact (to_In1 A (to_BinDirectSums A (C1 i) (C2 i))).
    - intros i. exact (DirectSumComplexIn1_comm C1 C2 i).
  Defined.

  Local Lemma DirectSumComplexIn2_comm (C1 C2 : Complex) (i : hz) :
    let B1 := to_BinDirectSums A (C1 i) (C2 i) in
    let B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1)) in
    (to_In2 A B1) ;; (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) =
    (Diff C2 i) ;; (to_In2 A B2).
  Proof.
    cbn.
    set (B1 := to_BinDirectSums A (C1 i) (C2 i)).
    set (B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1))).
    rewrite BinDirectSumIndArEq1.
    unfold BinDirectSumIndArFormula.
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite (to_IdIn2 A B1). rewrite (to_Unel2 A B1).
    rewrite id_left. rewrite to_postmor_unel'. rewrite to_postmor_unel'.
    rewrite to_lunax'. apply idpath.
  Qed.

  Definition DirectSumComplexIn2 (C1 C2 : Complex) : Morphism C2 (DirectSumComplex C1 C2).
  Proof.
    use mk_Morphism.
    - intros i. exact (to_In2 A (to_BinDirectSums A (C1 i) (C2 i))).
    - intros i. exact (DirectSumComplexIn2_comm C1 C2 i).
  Defined.

  Local Lemma DirectSumComplexPr1_comm (C1 C2 : Complex) (i : hz) :
    let B1 := to_BinDirectSums A (C1 i) (C2 i) in
    let B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1)) in
    (to_Pr1 A B1) ;; (Diff C1 i) =
    (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) ;; (to_Pr1 A B2).
  Proof.
    cbn.
    set (B1 := to_BinDirectSums A (C1 i) (C2 i)).
    set (B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1))).
    rewrite BinDirectSumIndArEq1.
    unfold BinDirectSumIndArFormula.
    rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn1 A B2). rewrite (to_Unel2 A B2).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_premor_unel'.
    rewrite to_runax'. apply idpath.
  Qed.

  Definition DirectSumComplexPr1 (C1 C2 : Complex) : Morphism (DirectSumComplex C1 C2) C1.
  Proof.
    use mk_Morphism.
    - intros i. exact (to_Pr1 A (to_BinDirectSums A (C1 i) (C2 i))).
    - intros i. exact (DirectSumComplexPr1_comm C1 C2 i).
  Defined.

  Local Lemma DirectSumComplexPr2_comm (C1 C2 : Complex) (i : hz) :
    let B1 := to_BinDirectSums A (C1 i) (C2 i) in
    let B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1)) in
    (to_Pr2 A B1) ;; (Diff C2 i) =
    (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) ;; (to_Pr2 A B2).
  Proof.
    cbn.
    set (B1 := to_BinDirectSums A (C1 i) (C2 i)).
    set (B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1))).
    rewrite BinDirectSumIndArEq1.
    unfold BinDirectSumIndArFormula.
    rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn2 A B2). rewrite (to_Unel1 A B2).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_premor_unel'.
    rewrite to_lunax'. apply idpath.
  Qed.

  Definition DirectSumComplexPr2 (C1 C2 : Complex) : Morphism (DirectSumComplex C1 C2) C2.
  Proof.
    use mk_Morphism.
    - intros i. exact (to_Pr2 A (to_BinDirectSums A (C1 i) (C2 i))).
    - intros i. exact (DirectSumComplexPr2_comm C1 C2 i).
  Defined.

  (** The equations for composing in1, in2, pr1, and pr2. *)
  Lemma DirectSumIdIn1 (C1 C2 : Complex) :
    IdMor C1 = MorphismComp (DirectSumComplexIn1 C1 C2) (DirectSumComplexPr1 C1 C2).
  Proof.
    use MorphismEq.
    intros i. cbn.
    set (B := to_BinDirectSums A (C1 i) (C2 i)).
    rewrite (to_IdIn1 A B).
    apply idpath.
  Qed.

  Lemma DirectSumIdIn2 (C1 C2 : Complex) :
    IdMor C2 = MorphismComp (DirectSumComplexIn2 C1 C2) (DirectSumComplexPr2 C1 C2).
  Proof.
    use MorphismEq.
    intros i. cbn.
    set (B := to_BinDirectSums A (C1 i) (C2 i)).
    rewrite (to_IdIn2 A B).
    apply idpath.
  Qed.

  Lemma DirectSumUnit1 (C1 C2 : Complex) :
    MorphismComp (DirectSumComplexIn1 C1 C2) (DirectSumComplexPr2 C1 C2) =
    ComplexZeroMorphism C1 C2.
  Proof.
    use MorphismEq.
    intros i. cbn.
    set (B := to_BinDirectSums A (C1 i) (C2 i)).
    rewrite (to_Unel1 A B).
    rewrite ZeroArrow_comp_left.
    apply PreAdditive_unel_zero.
  Qed.

  Lemma DirectSumUnit2 (C1 C2 : Complex) :
    MorphismComp (DirectSumComplexIn2 C1 C2) (DirectSumComplexPr1 C1 C2) =
    ComplexZeroMorphism C2 C1.
  Proof.
    use MorphismEq.
    intros i. cbn.
    set (B := to_BinDirectSums A (C1 i) (C2 i)).
    rewrite (to_Unel2 A B).
    rewrite ZeroArrow_comp_left.
    apply PreAdditive_unel_zero.
  Qed.

  (** Additition of morphisms is pointwise addition *)
  Local Lemma MorphismOpComm {C1 C2 : Complex} (M1 M2 : Morphism C1 C2)  (i : hz) :
    (to_binop (C1 i) (C2 i) (MMor M1 i) (MMor M2 i)) ;; (Diff C2 i) =
    (Diff C1 i) ;; (to_binop (C1 (i + 1)) (C2 (i + 1)) (MMor M1 (i + 1)) (MMor M2 (i + 1))).
  Proof.
    rewrite to_postmor_linear'. rewrite to_premor_linear'.
    rewrite (MComm M1 i). rewrite (MComm M2 i). apply idpath.
  Qed.

  Definition MorphismOp {C1 C2 : Complex} (M1 M2 : Morphism C1 C2) : Morphism C1 C2.
  Proof.
    use mk_Morphism.
    - intros i. exact (to_binop _ _ (MMor M1 i) (MMor M2 i)).
    - intros i. exact (MorphismOpComm M1 M2 i).
  Defined.

  Lemma MorphismOp_isassoc (C1 C2 : Complex) : @isassoc (Morphisms_hSet C1 C2) MorphismOp.
  Proof.
    intros M1 M2 M3.
    use MorphismEq.
    intros i. cbn.
    apply (assocax (to_abgrop (C1 i) (C2 i))).
  Qed.

  Lemma MorphismZeroComm (C1 C2 : Complex) (i : hz) :
    (ZeroArrow (Additive.to_Zero A) (C1 i) (C2 i)) ;; (Diff C2 i) =
    (Diff C1 i) ;; (ZeroArrow (Additive.to_Zero A) (C1 (i + 1)) (C2 (i + 1))).
  Proof.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Definition MorphismZero (C1 C2 : Complex) : Morphism C1 C2.
  Proof.
    use mk_Morphism.
    - intros i. exact (ZeroArrow (Additive.to_Zero A) _ _).
    - intros i. exact (MorphismZeroComm C1 C2 i).
  Defined.

  Lemma MorphismOp_isunit (C1 C2 : Complex) :
    @isunit (Morphisms_hSet C1 C2) MorphismOp (MorphismZero C1 C2).
  Proof.
    split.
    - intros M.
      use MorphismEq.
      intros i. cbn. rewrite <- PreAdditive_unel_zero.
      rewrite to_lunax'. apply idpath.
    - intros M.
      use MorphismEq.
      intros i. cbn. rewrite <- PreAdditive_unel_zero.
      rewrite to_runax'. apply idpath.
  Qed.

  Local Lemma MorphismOp_inv_comm {C1 C2 : Complex} (M : Morphism C1 C2) (i : hz) :
    (to_inv (C1 i) (C2 i) (MMor M i)) ;; (Diff C2 i) =
    (Diff C1 i) ;; (to_inv (C1 (i + 1)) (C2 (i + 1)) (MMor M (i + 1))).
  Proof.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invrcomp.
    apply PreAdditive_cancel_inv.
    rewrite inv_inv_eq.
    rewrite inv_inv_eq.
    exact (MComm M i).
  Qed.

  Definition MorphismOp_inv {C1 C2 : Complex} (M : Morphism C1 C2) : Morphism C1 C2.
  Proof.
    use mk_Morphism.
    - intros i. exact (to_inv (C1 i) (C2 i) (MMor M i)).
    - intros i. exact (MorphismOp_inv_comm M i).
  Defined.

  Lemma MorphismOp_isinv (C1 C2 : Complex) :
    @isinv (Morphisms_hSet C1 C2) MorphismOp (MorphismZero C1 C2) MorphismOp_inv.
  Proof.
    split.
    - intros H.
      use MorphismEq.
      intros i. cbn.
      rewrite (linvax A (MMor H i)).
      apply PreAdditive_unel_zero.
    - intros H.
      use MorphismEq.
      intros i. cbn.
      rewrite (rinvax A (MMor H i)).
      apply PreAdditive_unel_zero.
  Qed.

  Definition MorphismOp_iscomm (C1 C2 : Complex) : @iscomm (Morphisms_hSet C1 C2) MorphismOp.
  Proof.
    intros M1 M2.
    use MorphismEq.
    intros i. cbn.
    apply (commax (to_abgrop (C1 i) (C2 i)) (MMor M1 i) (MMor M2 i)).
  Qed.

  Definition MorphismOp_isabgrop (C1 C2 : Complex) : @isabgrop (Morphisms_hSet C1 C2) MorphismOp.
  Proof.
    split.
    - use isgroppair.
      + split.
        * exact (MorphismOp_isassoc C1 C2).
        * use isunitalpair.
          -- exact (MorphismZero C1 C2).
          -- exact (MorphismOp_isunit C1 C2).
      + use tpair.
        * exact MorphismOp_inv.
        * exact (MorphismOp_isinv C1 C2).
    - exact (MorphismOp_iscomm C1 C2).
  Defined.

  (** pr1 ;; in1 + pr2 ;; in2 = id *)
  Lemma DirectSumId (C1 C2 : Complex) :
    MorphismOp (MorphismComp (DirectSumComplexPr1 C1 C2) (DirectSumComplexIn1 C1 C2))
               (MorphismComp (DirectSumComplexPr2 C1 C2) (DirectSumComplexIn2 C1 C2)) =
    IdMor (DirectSumComplex C1 C2).
  Proof.
    use MorphismEq.
    intros i. cbn.
    set (B := to_BinDirectSums A (C1 i) (C2 i)).
    apply (to_BinOpId A B).
  Qed.

  (** The unique morphisms in and out of BinDirectSum *)
  Local Lemma DirectSumMorOut_comm {C1 C2 D : Complex} (f : Morphism C1 D) (g : Morphism C2 D)
        (i : hz) :
    let B1 := to_BinDirectSums A (C1 i) (C2 i) in
    let B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1)) in
    (FromBinDirectSum A B1 (MMor f i) (MMor g i)) ;; (Diff D i) =
    (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2)
      ;; (FromBinDirectSum A B2 (MMor f (i + 1)) (MMor g (i + 1))).
  Proof.
    cbn.
    set (B1 := to_BinDirectSums A (C1 i) (C2 i)).
    set (B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1))).
    rewrite BinDirectSumIndArEq1.
    unfold BinDirectSumIndArFormula. cbn.
    rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite BinDirectSumIn1Commutes.
    rewrite BinDirectSumIn2Commutes.
    rewrite <- (MComm f i).
    rewrite <- (MComm g i).
    rewrite assoc. rewrite assoc.
    rewrite <- to_postmor_linear'.
    apply cancel_postcomposition.
    rewrite <- FromBinDirectSumFormulaUnique.
    unfold FromBinDirectSumFormula.
    apply idpath.
  Qed.

  Definition DirectSumMorOut {C1 C2 D : Complex} (f : Morphism C1 D) (g : Morphism C2 D) :
    Morphism (DirectSumComplex C1 C2) D.
  Proof.
    use mk_Morphism.
    - intros i. exact (FromBinDirectSum A _ (MMor f i) (MMor g i)).
    - intros i. exact (DirectSumMorOut_comm f g i).
  Defined.

  Local Lemma DirectSumMorIn_comm {C1 C2 D : Complex} (f : Morphism D C1) (g : Morphism D C2)
        (i : hz) :
    let B1 := to_BinDirectSums A (C1 i) (C2 i) in
    let B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1)) in
    (ToBinDirectSum A B1 (MMor f i) (MMor g i))
      ;; (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) =
    (Diff D i) ;; (ToBinDirectSum A B2 (MMor f (i + 1)) (MMor g (i + 1))).
  Proof.
    intros B1 B2.
    rewrite BinDirectSumIndArEq1.
    unfold BinDirectSumIndArFormula.
    rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite BinDirectSumPr1Commutes.
    rewrite BinDirectSumPr2Commutes.
    rewrite (MComm f i).
    rewrite (MComm g i).
    rewrite <- assoc. rewrite <- assoc.
    rewrite <- to_premor_linear'.
    apply cancel_precomposition.
    rewrite <- ToBinDirectSumFormulaUnique.
    unfold ToBinDirectSumFormula.
    apply idpath.
  Qed.

  Definition DirectSumMorIn {C1 C2 D : Complex} (f : Morphism D C1) (g : Morphism D C2) :
    Morphism D (DirectSumComplex C1 C2).
  Proof.
    use mk_Morphism.
    - intros i. exact (ToBinDirectSum A _ (MMor f i) (MMor g i)).
    - intros i. exact (DirectSumMorIn_comm f g i).
  Defined.


  (** ** Construction of a complexes with one object *)
  (** ... -> 0 -> X -> 0 -> ... *)

  Definition ComplexFromObject_obs (X : ob A) (i : hz) : hz -> A.
  Proof.
    intros i0.
    induction (isdecrelhzeq i i0) as [e | n].
    - exact X.
    - exact (Additive.to_Zero A).
  Defined.

  Definition ComplexFromObject_mors (X : ob A) (i : hz) :
    Π i0 : hz, A ⟦ComplexFromObject_obs X i i0, ComplexFromObject_obs X i (i0 + 1)⟧.
  Proof.
    intros i0.
    unfold ComplexFromObject_obs. unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    - induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      + apply (fromempty (hzeqeisi e e')).
      + apply (ZeroArrow (Additive.to_Zero A)).
    - induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      + apply (ZeroArrow (Additive.to_Zero A)).
      + apply (ZeroArrow (Additive.to_Zero A)).
  Defined.

  Local Lemma ComplexFromObject_comm (X : ob A) (i : hz) :
    Π i0 : hz, (ComplexFromObject_mors X i i0) ;; (ComplexFromObject_mors X i (i0 + 1)) =
               ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros i0.
    unfold ComplexFromObject_obs. unfold ComplexFromObject_mors. unfold coprod_rect. cbn.
    induction (isdecrelhzeq i i0) as [e | n].
    + induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      * apply (fromempty (hzeqeisi e e')).
      * apply ZeroArrow_comp_left.
    + induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      * apply ZeroArrow_comp_left.
      * apply ZeroArrow_comp_left.
  Qed.

  Definition ComplexFromObject (X : ob A) (i : hz) : Complex.
  Proof.
    use mk_Complex.
    - exact (ComplexFromObject_obs X i).
    - exact (ComplexFromObject_mors X i).
    - exact (ComplexFromObject_comm X i).
  Defined.

  (** A morphisms in A induces a morphisms of ComplexFromObjects *)
  Definition ObjectMorToComplexMor_mors {a b : ob A} (f : a --> b) (i : hz) :
    Π i0 : hz, A ⟦(ComplexFromObject a i) i0, (ComplexFromObject b i) i0⟧.
  Proof.
    intros i0.
    unfold ComplexFromObject. cbn. unfold ComplexFromObject_obs. cbn. unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    - exact f.
    - apply (ZeroArrow (Additive.to_Zero A)).
  Defined.

  Local Lemma ObjectMorToComplexMor_comm {a b : ob A} (f : a --> b) (i : hz) :
    Π i0 : hz, (ObjectMorToComplexMor_mors f i i0) ;; (Diff (ComplexFromObject b i) i0) =
               (Diff (ComplexFromObject a i) i0) ;; (ObjectMorToComplexMor_mors f i (i0 + 1)).
  Proof.
    intros i0.
    unfold ComplexFromObject. unfold ComplexFromObject_mors. unfold ComplexFromObject_obs. cbn.
    unfold ObjectMorToComplexMor_mors. cbn. unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    - induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      + apply (fromempty (hzeqeisi e e')).
      + rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_right.
    - induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      + rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. apply idpath.
      + rewrite ZeroArrow_comp_left. apply idpath.
  Qed.

  Definition ObjectMorToComplexMor {a b : ob A} (f : a --> b) (i : hz) :
    Morphism (ComplexFromObject a i) (ComplexFromObject b i).
  Proof.
    use mk_Morphism.
    - exact (ObjectMorToComplexMor_mors f i).
    - exact (ObjectMorToComplexMor_comm f i).
  Defined.


  (** ** Construction of a complex with 2 nonzero objects and morphisms to and from it *)

  Definition Complex2FromObject_obs (a : ob A) (i : hz) : hz -> ob A.
  Proof.
    intros i0.
    induction (isdecrelhzeq i i0) as [e | n].
    - exact a.
    - induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      + exact a.
      + exact (Additive.to_Zero A).
  Defined.

  Definition Complex2FromObject_mors (a : ob A) (i : hz) :
    Π i0 : hz, A ⟦Complex2FromObject_obs a i i0, Complex2FromObject_obs a i (i0 + 1)⟧.
  Proof.
    intros i0. unfold Complex2FromObject_obs. cbn. unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    + induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      * apply (fromempty (hzeqeisi e e')).
      * induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e'' | n''].
        -- apply identity.
        -- apply fromempty. apply n''. induction e. apply idpath.
    + induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      * induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        -- apply fromempty. cbn in e'. rewrite <- e' in e''. apply (hzeqissi e'').
        -- induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e''' | n'''].
           ++ cbn in e'. rewrite e' in e'''.
              apply (fromempty (hzeqisi e''')).
           ++ apply (ZeroArrow (Additive.to_Zero A)).
      * induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        -- apply (ZeroArrow (Additive.to_Zero A)).
        -- induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e''' | n'''].
           ++ apply fromempty. apply n. apply (hzplusrcan _ _ 1). apply e'''.
           ++ apply (ZeroArrow (Additive.to_Zero A)).
  Defined.

  Local Lemma Complex2FromObject_comm (a : ob A) (i : hz) :
    Π i0 : hz, (Complex2FromObject_mors a i i0) ;; (Complex2FromObject_mors a i (i0 + 1)) =
               ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros i0.
    unfold Complex2FromObject_obs. unfold Complex2FromObject_mors. unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    - induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      + apply (fromempty (hzeqeisi e e')).
      + induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e'' | n''].
        * rewrite id_left.
          induction (isdecrelhzeq i (i0 + 1 + 1)) as [e''' | n'''].
          -- apply (fromempty (hzeqeissi e e''')).
          -- induction (isdecrelhzeq (i + 1) (i0 + 1 + 1)) as [e'''' | n''''].
             ++ apply (fromempty (hzeqeisi e'' e'''')).
             ++ apply idpath.
        * apply fromempty. apply n''. cbn. cbn in e. rewrite e. apply idpath.
    - induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      + induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        * apply (fromempty (hzeqsnmnsm e' e'')).
        * induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e''' | n'''].
          -- apply (fromempty (hzeqeisi e' e''')).
          -- induction (isdecrelhzeq i (i0 + 1 + 1)) as [e'''' | n''''].
             ++ apply ZeroArrow_comp_left.
             ++ induction (isdecrelhzeq (i + 1) (i0 + 1 + 1)) as [e5 | n5].
                ** apply (fromempty (hzeqeissi e' e5)).
                ** apply ZeroArrow_comp_left.
      + induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        * induction (isdecrelhzeq i (i0 + 1 + 1)) as [e3 | n3].
          -- apply (fromempty (hzeqeisi e'' e3)).
          -- induction (isdecrelhzeq (i + 1) (i0 + 1 + 1)) as [e4 | n4].
             ++ apply ZeroArrow_comp_left.
             ++ apply fromempty. apply n4. cbn in e''. rewrite e''. apply idpath.
        * induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e3 | n3].
          -- apply fromempty. apply n. apply (hzplusrcan _ _ 1). apply e3.
          -- induction (isdecrelhzeq i (i0 + 1 + 1)) as [e4 | n4].
             ++ apply ZeroArrow_comp_left.
             ++ induction (isdecrelhzeq (i + 1) (i0 + 1 + 1)) as [e5 | n5].
                ** apply fromempty. apply n''. apply (hzplusrcan _ _ 1). apply e5.
                ** apply ZeroArrow_comp_left.
  Qed.

  (** This constructs the complex ... --> 0 --> X -Id-> X --> 0 --> ... *)
  Definition Complex2FromObject (a : ob A) (i : hz) : Complex.
  Proof.
    use mk_Complex.
    - exact (Complex2FromObject_obs a i).
    - exact (Complex2FromObject_mors a i).
    - exact (Complex2FromObject_comm a i).
  Defined.

  (** *** Morphism from Complex2FromObject to complex *)

  Definition FromComplex2FromObject_mors {a : ob A} {C : Complex} {i : hz} (f : a --> (C i)) :
    Π i0 : hz, A ⟦(Complex2FromObject a i) i0, C i0⟧.
  Proof.
    intros i0.
    unfold Complex2FromObject. unfold Complex2FromObject_obs. unfold Complex2FromObject_mors. cbn.
    unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    + induction e. exact f.
    + induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      * induction e'. exact (f ;; (Diff C i)).
      * apply (ZeroArrow (Additive.to_Zero A)).
  Defined.

  Local Lemma FromComplex2FromObject_comm {a : ob A} {C : Complex} {i : hz} (f : a --> (C i)) :
    Π i0 : hz, (FromComplex2FromObject_mors f i0) ;; (Diff C i0) =
               (Diff (Complex2FromObject a i) i0) ;; (FromComplex2FromObject_mors f (i0 + 1)).
  Proof.
    intros i0.
    unfold Complex2FromObject. unfold Complex2FromObject_obs. unfold Complex2FromObject_mors.
    unfold FromComplex2FromObject_mors. cbn. unfold coprod_rect. cbn.
    unfold paths_rect. cbn.
    induction (isdecrelhzeq i i0) as [e | n].
    + induction e.
      induction (isdecrelhzeq i (i + 1)) as [e' | n'].
      * apply (fromempty (hzeqisi e')).
      * induction (isdecrelhzeq (i + 1) (i + 1)) as [e'' | n''].
        -- rewrite id_left.
           rewrite (pr1 (isasethz (i + 1) (i + 1) e'' (idpath (i + 1)))).
           apply idpath.
        -- apply (fromempty (n'' (idpath (i + 1)))).
    + induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      * induction e'. cbn.
        induction (isdecrelhzeq i (i + 1 + 1)) as [e'' | n''].
        -- apply (fromempty (hzeqissi e'')).
        -- induction (isdecrelhzeq (i + 1) (i + 1 + 1)) as [e''' | n'''].
           ++ apply (fromempty (hzeqisi e''')).
           ++ rewrite <- assoc. rewrite (CEq C i). rewrite ZeroArrow_comp_left.
              apply ZeroArrow_comp_right.
      * induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        -- rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. apply idpath.
        -- induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e''' | n'''].
           ++ apply (fromempty (n (hzplusrcan i i0 1 e'''))).
           ++ rewrite ZeroArrow_comp_right. apply ZeroArrow_comp_left.
  Qed.

  Definition FromComplex2FromObject {a : ob A} {C : Complex} {i : hz} (f : a --> (C i)) :
    Morphism (Complex2FromObject a i) C.
  Proof.
    use mk_Morphism.
    - exact (FromComplex2FromObject_mors f).
    - exact (FromComplex2FromObject_comm f).
  Defined.

  Lemma FromComplex2FromObject_Eq1 {a : ob A} {C : Complex} {i : hz} (i0 : hz) (g : a --> (C i)) :
    FromComplex2FromObject_mors g i0 = MMor (FromComplex2FromObject g) i0.
  Proof.
    apply idpath.
  Qed.

  (** *** Morphism from complex to Complex2FromObject *)

  Definition ToComplex2FromObject_mors {a : ob A} {C : Complex} {i : hz} (f : (C i) --> a) :
    Π i0 : hz, A ⟦C i0, (Complex2FromObject a (i - 1)) i0⟧.
  Proof.
    intros i0. unfold Complex2FromObject. unfold Complex2FromObject_obs. cbn. unfold coprod_rect.
    induction (isdecrelhzeq (i - 1) i0) as [e | n].
    - induction (isdecrelhzeq i (i - 1 + 1)) as [e' | n'].
      + eapply compose.
        * induction e. exact (Diff C (i - 1)).
        * induction e'. exact f.
      + apply fromempty. apply n'. apply pathsinv0. apply (hzrminusplus i 1).
    - induction (isdecrelhzeq (i - 1 + 1) i0) as [e' | n'].
      + induction e'.
        induction (isdecrelhzeq i (i - 1 + 1)) as [e'' | n''].
        * induction e''. exact f.
        * apply fromempty. apply n''. apply (hzrminusplus' i 1).
      + apply (ZeroArrow (Additive.to_Zero A)).
  Defined.

  Local Lemma ToComplex2FromObject_comm {a : ob A} {C : Complex} {i : hz} (f : (C i) --> a) :
    Π i0 : hz, (ToComplex2FromObject_mors f i0) ;; (Diff (Complex2FromObject a (i - 1)) i0) =
               (Diff C i0) ;; (ToComplex2FromObject_mors f (i0 + 1)).
  Proof.
    intros i0.
    unfold Complex2FromObject. unfold Complex2FromObject_obs. unfold Complex2FromObject_mors.
    unfold ToComplex2FromObject_mors. unfold coprod_rect. unfold paths_rect. cbn.
    induction (isdecrelhzeq (i - 1) i0) as [e | n].
    - induction e.
      induction (isdecrelhzeq (i - 1 + 1) i) as [e' | n'].
      + induction e'.
        induction (isdecrelhzeq (i - 1)  (i - 1 + 1)) as [e'' | n''].
        * apply fromempty. apply (hzeqisi e'').
        * induction (isdecrelhzeq i (i - 1 + 1)) as [e''' | n'''].
          -- rewrite isdecrelhzeqi. rewrite id_right.
             apply cancel_precomposition. induction e'''.
             exact (idpath f).
          -- apply fromempty. apply n'''. apply (hzrminusplus' i 1).
      + induction (isdecrelhzeq (i - 1)  (i - 1 + 1)) as [e'' | n''].
        * apply fromempty. apply (hzeqisi e'').
        * induction (isdecrelhzeq i (i - 1 + 1)) as [e''' | n'''].
          -- rewrite isdecrelhzeqi. rewrite id_right.
             apply cancel_precomposition.
             induction e'''.
             exact (idpath f).
          -- apply fromempty. apply n'''. apply (hzrminusplus' i 1).
    - induction (isdecrelhzeq (i - 1 + 1) i0) as [e' | n'].
      + induction e'.
        induction (isdecrelhzeq i (i - 1 + 1)) as [e'' | n''].
        * induction (isdecrelhzeq (i - 1) (i - 1 + 1 + 1)) as [e''' | n'''].
          -- apply fromempty. apply (hzeqissi e''').
          -- induction (isdecrelhzeq (i - 1 + 1) (i - 1 + 1 + 1)) as [e'''' | n''''].
             ++ apply fromempty. apply (hzeqisi e'''').
             ++ rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
                apply idpath.
        * apply (fromempty (n'' (hzrminusplus' i 1))).
      + induction (isdecrelhzeq (i - 1) (i0 + 1)) as [e'' | n''].
        * induction (isdecrelhzeq i (i - 1 + 1)) as [e''' | n'''].
          -- rewrite assoc. rewrite ZeroArrow_comp_right.
             set (mor := match e''' in (_ = y) return (A ⟦ C y, a ⟧) with
                      | idpath _ => f
                      end).
             rewrite <- (ZeroArrow_comp_left _ _ _ _ _ mor). unfold mor. clear mor.
             apply cancel_postcomposition. rewrite e''. apply (! (CEq C i0)).
          -- apply fromempty. apply n'''. apply (hzrminusplus' i 1).
        * induction (isdecrelhzeq (i - 1 + 1) (i0 + 1)) as [e''' | n'''].
          -- apply (fromempty (n (hzplusrcan (i - 1) i0 1 e'''))).
          -- rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
             apply idpath.
  Qed.

  Definition ToComplex2FromObject {a : ob A} {C : Complex} {i : hz} (f : (C i) --> a) :
    Morphism C (Complex2FromObject a (i - 1)).
  Proof.
    use mk_Morphism.
    - exact (ToComplex2FromObject_mors f).
    - exact (ToComplex2FromObject_comm f).
  Defined.

  Lemma ToComplex2FromObject_Eq1 {a : ob A} {C : Complex} {i : hz} (i0 : hz) (g : (C i) --> a) :
    ToComplex2FromObject_mors g i0 = MMor (ToComplex2FromObject g) i0.
  Proof.
    apply idpath.
  Qed.

End def_complexes.
Arguments Diff [A] _ _.
Arguments ZeroComplex [A].
Arguments Morphism [A] _ _.
Arguments MorphismEq [A] [C1] [C2] _ _ _.
Arguments MorphismFromZero [A] _.
Arguments MorphismToZero [A] _.
Arguments MMor [A] [C1] [C2] _ _.
Arguments MComm [A] [C1] [C2] _ _.
Arguments IdMor [A] _.
Arguments MorphismComp [A] [C1] [C2] [C3] _ _.


(** * The category of complexes *)
(** ** Introduction
   We construct the category of complexes where the objects are complexes, [Complex], and morphisms
   are  morphisms between complexes, [Morphism]. Also, we show that a monic (resp. epi) in this
   category is indexwise monic (resp. epi), [ComplexMonicIndexMonic] (resp. [ComplexEpiIndexEpi]).
   To show that a morphism of complexes is an isomorphism, it is enough to show that the morphism
   is indexwise isomorphism, [ComplexIsoIndexIso].
*)
Section complexes_precat.

  Variable A : Additive.

  (** ** Construction of the category of complexes *)

  Definition ComplexPreCat_ob_mor : precategory_ob_mor :=
    tpair (fun ob : UU => ob -> ob -> UU) (Complex A) (fun C1 C2 : Complex A => Morphism C1 C2).

  Definition ComplexPreCat_data : precategory_data :=
    precategory_data_pair
      ComplexPreCat_ob_mor (fun (C : Complex A) => IdMor C)
      (fun (C1 C2 C3 : Complex A) (M1 : Morphism C1 C2) (M2 : Morphism C2 C3) => MorphismComp M1 M2).

  Lemma is_precategory_ComplexPreCat_data : is_precategory ComplexPreCat_data.
  Proof.
    split.
    - split.
      + intros a b f.
        use MorphismEq.
        intros i. cbn.
        apply id_left.
      + intros a b f.
        use MorphismEq.
        intros i. cbn.
        apply id_right.
    - intros a b c d f g h.
      use MorphismEq.
      intros i. cbn.
      apply assoc.
  Qed.

  Definition ComplexPreCat : precategory := tpair _ _ is_precategory_ComplexPreCat_data.

  Lemma has_homsets_ComplexPreCat : has_homsets ComplexPreCat.
  Proof.
    intros C1 C2. cbn.
    apply isaset_total2.
    - apply impred_isaset.
      intros t. apply to_has_homsets.
    - intros x. apply impred_isaset.
      intros t. apply isasetaprop. apply to_has_homsets.
  Qed.


  (** ** Monic of complexes is indexwise monic *)

  Local Lemma ComplexMonicIndexMonic_eq {C1 C2 : Complex A} (M : Monic ComplexPreCat C1 C2) (i : hz)
        {a : A} (g h : A ⟦a, C1 i⟧)
        (H : g ;; (MMor (MonicArrow _ M) i) = h ;; (MMor (MonicArrow _ M) i)) :
    FromComplex2FromObject_mors A g i = FromComplex2FromObject_mors A h i.
  Proof.
    use (pathscomp0 (FromComplex2FromObject_Eq1 A i g)).
    use (pathscomp0 _ (! (FromComplex2FromObject_Eq1 A i h))).
    use MorphismEq'.
    use (MonicisMonic ComplexPreCat M). cbn.
    use MorphismEq.
    intros i0. cbn.
    unfold FromComplex2FromObject_mors. unfold coprod_rect. unfold Complex2FromObject_obs. cbn.
    induction (isdecrelhzeq i i0) as [T | F].
    - induction T. exact H.
    - induction (isdecrelhzeq (i + 1) i0) as [T' | F'].
      + induction T'. cbn. rewrite <- assoc. rewrite <- assoc. rewrite <- MComm.
        rewrite assoc. rewrite assoc. apply cancel_postcomposition.
        exact H.
      + apply idpath.
  Qed.

  Lemma ComplexMonicIndexMonic {C1 C2 : Complex A} (M : Monic ComplexPreCat C1 C2) :
    Π i : hz, isMonic (@MMor A C1 C2 (MonicArrow _ M) i).
  Proof.
    intros i a g h H.
    set (tmp := ComplexMonicIndexMonic_eq M i g h H).
    unfold FromComplex2FromObject_mors in tmp. cbn in tmp.
    unfold coprod_rect in tmp. unfold Complex2FromObject_obs in tmp.
    unfold paths_rect in tmp. cbn in tmp.
    rewrite (isdecrelhzeqi i) in tmp.
    exact tmp.
  Qed.


  (** ** Epi of complexes is indexwise epi *)

  Local Lemma ComplexEpiIndexEpi_eq {C1 C2 : Complex A} (E : Epi ComplexPreCat C1 C2) (i : hz)
        {a : A} (g h : A ⟦C2 i, a⟧)
        (H : (MMor (EpiArrow _ E) i) ;; g = (MMor (EpiArrow _ E) i) ;; h) :
    ToComplex2FromObject_mors A g i = ToComplex2FromObject_mors A h i.
  Proof.
    use (pathscomp0 (ToComplex2FromObject_Eq1 A i g)).
    use (pathscomp0 _ (! (ToComplex2FromObject_Eq1 A i h))).
    use MorphismEq'.
    use (EpiisEpi ComplexPreCat E). cbn.
    use MorphismEq.
    intros i0. cbn.
    unfold ToComplex2FromObject_mors. unfold coprod_rect. unfold Complex2FromObject_obs. cbn.
    induction (isdecrelhzeq (i - 1) i0) as [T | F].
    - induction T.
      induction (isdecrelhzeq i (i - 1 + 1)) as [e' | n'].
      + unfold paths_rect. rewrite assoc. rewrite assoc.
        rewrite (MComm (EpiArrow _ E)). rewrite <- assoc. rewrite <- assoc.
        apply cancel_precomposition. induction e'. exact H.
      + apply (fromempty (n' (! hzrminusplus i 1))).
    - induction (isdecrelhzeq (i - 1 + 1) i0) as [e' | n'].
      + unfold paths_rect. induction e'.
        induction (isdecrelhzeq i (i - 1 + 1)) as [e'' | n''].
        * induction e''. apply H.
        * apply (fromempty (n'' (hzrminusplus' i 1))).
      + apply idpath.
  Qed.

  Lemma ComplexEpiIndexEpi {C1 C2 : Complex A} (E : Epi ComplexPreCat C1 C2) :
    Π i : hz, isEpi (@MMor A C1 C2 (EpiArrow _ E) i).
  Proof.
    intros i a g h H.
    set (tmp := ComplexEpiIndexEpi_eq E i g h H).
    unfold ToComplex2FromObject_mors in tmp. cbn in tmp.
    unfold coprod_rect in tmp. unfold Complex2FromObject_obs in tmp.
    unfold paths_rect in tmp. cbn in tmp.
    rewrite (isdecrelhzeqminusplus i) in tmp.
    rewrite (isdecrelhzeqminusplus' i) in tmp.
    rewrite (isdecrelhzeqpii i) in tmp.
    induction (hzrminusplus i 1).
    induction (hzrminusplus' i 1).
    exact tmp.
  Qed.


  (** ** An morphism in complexes is an isomorphism if it is so indexwise *)

  Lemma ComplexIsoIndexIso {C1 C2 : Complex A} (f : ComplexPreCat⟦C1, C2⟧)
        (H : Π (i : hz), is_iso (MMor f i)) : is_iso f.
  Proof.
    use is_iso_qinv.
    - use mk_Morphism.
      + intros i. exact (iso_inv_from_is_iso _ (H i)).
      + intros i. cbn.
        use (post_comp_with_iso_is_inj _ _ _ _ (H (i + 1))).
        use (pre_comp_with_iso_is_inj _ _ _ _ _ (H i)).
        assert (e0 : MMor f i ;; inv_from_iso (MMor f i,, H i) = identity _).
        {
          apply (iso_inv_after_iso (isopair _ (H i))).
        }
        rewrite assoc. rewrite assoc. rewrite e0. rewrite id_left.
        rewrite <- (MComm f i). apply cancel_precomposition.
        assert (e1 : inv_from_iso (MMor f (i + 1),, H (i + 1)) ;; MMor f (i + 1) = identity _).
        {
          apply (iso_after_iso_inv (isopair _ (H (i + 1)))).
        }
        rewrite <- assoc. rewrite e1. rewrite id_right. apply idpath.
    - split.
      + use MorphismEq. intros i. cbn. apply (iso_inv_after_iso (isopair _ (H i))).
      + use MorphismEq. intros i. cbn. apply (iso_after_iso_inv (isopair _ (H i))).
  Qed.

End complexes_precat.


(** * The category of complexes over Additive is Additive *)
(** ** Introduction
   We show that the category of complexes over an additive category is an additive category.
   Addition of morphisms is given by indexwise addition, [MorphismOp], [ZeroComplex] is a zero
   object, which is shown to be zero in [ComplexPreCat_isZero], and binary direct sums are
   given by [DirectSumComplex]. [ComplexPreCat_Additive] is the main result.
*)
Section complexes_additive.

  Variable A : Additive.

  Definition ComplexPreCat_PrecategoryWithBinOps : PrecategoryWithBinOps.
  Proof.
    use mk_PrecategoryWithBinOps.
    - exact (ComplexPreCat A).
    - intros x y. exact (MorphismOp A).
  Defined.

  Definition ComplexPreCat_PrecategoryWithAbgrops : PrecategoryWithAbgrops.
  Proof.
    use mk_PrecategoryWithAbgrops.
    - exact ComplexPreCat_PrecategoryWithBinOps.
    - exact (has_homsets_ComplexPreCat A).
    - intros x y. exact (MorphismOp_isabgrop A x y).
  Defined.

  Lemma ComplexPreCat_isPreAdditive : isPreAdditive ComplexPreCat_PrecategoryWithAbgrops.
  Proof.
    split.
    - intros x y z f.
      split.
      + intros g h.
        use MorphismEq.
        intros i.
        apply to_premor_linear'.
      + use MorphismEq.
        intros i. cbn.
        apply ZeroArrow_comp_right.
    - intros x y z f.
      split.
      + intros g h.
        use MorphismEq.
        intros i.
        apply to_postmor_linear'.
      + use MorphismEq.
        intros i. cbn.
        apply ZeroArrow_comp_left.
  Qed.

  Lemma ComplexPreCat_PreAdditive : PreAdditive.
  Proof.
    use mk_PreAdditive.
    - exact ComplexPreCat_PrecategoryWithAbgrops.
    - exact ComplexPreCat_isPreAdditive.
  Defined.

  Lemma ComplexPreCat_isZero : isZero ComplexPreCat_PreAdditive ZeroComplex.
  Proof.
    split.
    - intros C.
      use tpair.
      + exact (MorphismFromZero C).
      + cbn. intros t.
        use MorphismEq.
        intros i. cbn.
        apply ArrowsFromZero.
    - intros C.
      use tpair.
      + exact (MorphismToZero C).
      + cbn. intros t.
        use MorphismEq.
        intros i. cbn.
        apply ArrowsToZero.
  Qed.

  Lemma ComplexPreCat_isBinCoproductCocone (C1 C2 : Complex A) :
    isBinCoproductCocone ComplexPreCat_PreAdditive C1 C2 (DirectSumComplex A C1 C2)
                         (DirectSumComplexIn1 A C1 C2) (DirectSumComplexIn2 A C1 C2).
  Proof.
    use mk_isBinCoproductCocone.
    - apply has_homsets_ComplexPreCat.
    - intros D f g.
      use unique_exists.
      + exact (DirectSumMorOut A f g).
      (* Commutativity *)
      + split.
        * use MorphismEq.
          intros i. cbn.
          apply BinDirectSumIn1Commutes.
        * use MorphismEq.
          intros i. cbn.
          apply BinDirectSumIn2Commutes.
      + intros y. apply isapropdirprod.
        * apply has_homsets_ComplexPreCat.
        * apply has_homsets_ComplexPreCat.
      + intros y T. cbn beta in T.
        use MorphismEq.
        intros i. cbn.
        use FromBinDirectSumUnique.
        * rewrite <- (pr1 T). apply idpath.
        * rewrite <- (pr2 T). apply idpath.
  Qed.

  Lemma ComplexPreCat_isBinProductCone (C1 C2 : Complex A) :
    isBinProductCone ComplexPreCat_PreAdditive C1 C2 (DirectSumComplex A C1 C2)
                     (DirectSumComplexPr1 A C1 C2) (DirectSumComplexPr2 A C1 C2).
  Proof.
    use mk_isBinProductCone.
    - apply has_homsets_ComplexPreCat.
    - intros D f g.
      use unique_exists.
      + exact (DirectSumMorIn A f g).
      (* Commutativity *)
      + split.
        * use MorphismEq.
          intros i. cbn.
          apply BinDirectSumPr1Commutes.
        * use MorphismEq.
          intros i. cbn.
          apply BinDirectSumPr2Commutes.
      + intros y. apply isapropdirprod.
        * apply has_homsets_ComplexPreCat.
        * apply has_homsets_ComplexPreCat.
      + intros y T. cbn beta in T.
        use MorphismEq.
        intros i. cbn.
        use ToBinDirectSumUnique.
        * rewrite <- (pr1 T). apply idpath.
        * rewrite <- (pr2 T). apply idpath.
  Qed.

  Lemma ComplexPreCat_ZeroEq (C1 C2 : Complex A) :
    ComplexZeroMorphism A C1 C2 = MorphismZero A C1 C2.
  Proof.
    use MorphismEq.
    intros i. cbn.
    apply ZeroArrow_comp_left.
  Qed.

  Lemma ComplexPreCat_isBinDirectSumCone (C1 C2 : Complex A) :
    isBinDirectSumCone
      ComplexPreCat_PreAdditive C1 C2 (DirectSumComplex A C1 C2) (DirectSumComplexIn1 A C1 C2)
      (DirectSumComplexIn2 A C1 C2) (DirectSumComplexPr1 A C1 C2) (DirectSumComplexPr2 A C1 C2).
  Proof.
    use mk_isBinDirectSumCone.
    - exact (ComplexPreCat_isBinCoproductCocone C1 C2).
    - exact (ComplexPreCat_isBinProductCone C1 C2).
    - apply (! (DirectSumIdIn1 A C1 C2)).
    - apply (! (DirectSumIdIn2 A C1 C2)).
    - cbn. rewrite (DirectSumUnit1 A C1 C2). apply ComplexPreCat_ZeroEq.
    - cbn. rewrite (DirectSumUnit2 A C1 C2). apply ComplexPreCat_ZeroEq.
    - apply (DirectSumId A C1 C2).
  Qed.

  (** The category of complexes over an additive category is additive *)
  Definition ComplexPreCat_Additive : Additive.
  Proof.
    use mk_Additive.
    - exact ComplexPreCat_PreAdditive.
    - use mk_isAdditive.
      + use mk_Zero.
        * exact ZeroComplex.
        * exact ComplexPreCat_isZero.
      + intros C1 C2.
        use (mk_BinDirectSumCone ComplexPreCat_PreAdditive).
        * exact (DirectSumComplex A C1 C2).
        * exact (DirectSumComplexIn1 A C1 C2).
        * exact (DirectSumComplexIn2 A C1 C2).
        * exact (DirectSumComplexPr1 A C1 C2).
        * exact (DirectSumComplexPr2 A C1 C2).
        * exact (ComplexPreCat_isBinDirectSumCone C1 C2).
  Defined.

End complexes_additive.


(** * Complexes over Abelian is Abelian *)
(** ** Introduction
   We show that the category of complexes, [ComplexPreCat_Additive], over an abelian category A,
   more precisely [AbelianToAdditive A hs], is an abelian category, [ComplexPreCat_AbelianPreCat].
   Kernels and cokernels are given by taking kernels and cokernels indexwise. Since monics and epis
   in [ComplexPreCat_Additive] are indexwise monics and epis, by [ComplexMonicIndexMonic] and
   [ComplexEpiIndexEpi], we can use the fact that A is abelian to show that every monic is a kernel
   of some morphism in [ComplexPreCat_Additive] and every epi is a cokernel of some morphism in
   [ComplexPreCat_Additive].
*)
Section complexes_abelian.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.

  (** ** Kernels in Complexes over Abelian *)
  (** *** Construction of the kernel object *)

  Local Lemma ComplexPreCat_Kernel_moreq {Y Z : Complex (AbelianToAdditive A hs)} (g : Morphism Y Z)
        (i : hz) : (KernelArrow (Kernel (MMor g i))) ;; (Diff Y i) ;; (MMor g (i + 1)) =
                   ZeroArrow (@to_Zero A) (Kernel (MMor g i)) (Z (i + 1)).
  Proof.
    rewrite <- assoc. cbn. set (tmp := MComm g i). cbn in tmp. rewrite <- tmp. clear tmp.
    rewrite assoc. rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Local Lemma ComplexPreCat_Kernel_comp {Y Z : Complex (AbelianToAdditive A hs)} (g : Morphism Y Z)
        (i : hz) :
    (KernelIn (@to_Zero A) (Kernel (MMor g (i + 1))) (Kernel (MMor g i))
              ((KernelArrow (Kernel (MMor g i))) ;; (Diff Y i))
              (ComplexPreCat_Kernel_moreq g i))
      ;; (KernelIn (@to_Zero A) (Kernel (MMor g (i + 1 + 1))) (Kernel (MMor g (i + 1)))
                   ((KernelArrow (Kernel (MMor g (i + 1)))) ;; (Diff Y (i + 1)))
                   (ComplexPreCat_Kernel_moreq g (i + 1))) =
    ZeroArrow (@to_Zero A) (Kernel (MMor g i)) (Kernel (MMor g (i + 1 + 1))).
  Proof.
    apply KernelArrowisMonic. rewrite ZeroArrow_comp_left.
    rewrite <- assoc. rewrite KernelCommutes. rewrite assoc. rewrite KernelCommutes.
    rewrite <- assoc. set (tmp := CEq _ Y i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Definition ComplexPreCat_Kernel {Y Z : Complex (AbelianToAdditive A hs)} (g : Morphism Y Z) :
    ComplexPreCat (AbelianToAdditive A hs).
  Proof.
    use mk_Complex.
    - intros i. exact (Kernel (MMor g i)).
    - intros i. cbn. use KernelIn.
      + exact (KernelArrow (Kernel (MMor g i)) ;; Diff Y i).
      + exact (ComplexPreCat_Kernel_moreq g i).
    - intros i. exact (ComplexPreCat_Kernel_comp g i).
  Defined.

  (** *** Construction of the KernelArrow *)
  Definition ComplexPreCat_KernelArrow {Y Z : Complex (AbelianToAdditive A hs)}
             (g : Morphism Y Z) : Morphism (ComplexPreCat_Kernel g) Y.
  Proof.
    use mk_Morphism.
    - intros i. use KernelArrow.
    - intros i. exact (! (KernelCommutes _ _ _ _ _)).
  Defined.


  (** *** isEqualizer  *)
  Local Lemma ComplexPreCat_Kernels_comp {X Y : Complex (AbelianToAdditive A hs)}
        (g : Morphism X Y) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    MorphismComp (ComplexPreCat_KernelArrow g) g =
    MorphismComp (ZeroArrowTo (ComplexPreCat_Kernel g)) (@ZeroArrowFrom _ Z Y).
  Proof.
    use MorphismEq.
    intros i. cbn. rewrite KernelCompZero. apply pathsinv0. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexPreCat_KernelIn_comp {X Y w : Complex (AbelianToAdditive A hs)} (g : Morphism X Y)
    (h : Morphism w X) (i : hz) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    MorphismComp h g = ZeroArrow Z w Y ->
    (MMor h i) ;; (MMor g i) = ZeroArrow to_Zero (w i) (Y i).
  Proof.
    intros Z H.
    set (tmp := MorphismEq' _ (MorphismComp h g) (ZeroArrow Z _ _) H i). cbn in tmp.
    cbn. rewrite tmp. clear tmp. apply ZeroArrowEq.
  Qed.

  Definition ComplexPreCat_KernelIn {X Y w : Complex (AbelianToAdditive A hs)} (g : Morphism X Y)
    (h : Morphism w X) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    MorphismComp h g = ZeroArrow Z w Y ->
    (ComplexPreCat (AbelianToAdditive A hs)) ⟦w, ComplexPreCat_Kernel g⟧.
  Proof.
    cbn.
    set (Z := @mk_Zero (ComplexPreCat (AbelianToAdditive A hs))
                       ZeroComplex (ComplexPreCat_isZero (AbelianToAdditive A hs))).
    intros H.
    use mk_Morphism.
    - intros i. cbn. use KernelIn.
      + exact (MMor h i).
      + apply (ComplexPreCat_KernelIn_comp g h i H).
    - intros i. cbn.
      apply KernelArrowisMonic.
      rewrite <- assoc. rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
      rewrite assoc. rewrite KernelCommutes.
      apply (MComm h i).
  Defined.

  Local Lemma ComplexPreCat_Kernels_isEqualizer {X Y : Complex (AbelianToAdditive A hs)}
        (g : Morphism X Y) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    @equalizers.isEqualizer
      (ComplexPreCat (AbelianToAdditive A hs)) _ _ _
      g (MorphismComp (@ZeroArrowTo _ Z X) (@ZeroArrowFrom _ Z Y)) (ComplexPreCat_KernelArrow g)
      (KernelEqRw Z (ComplexPreCat_Kernels_comp g)).
  Proof.
    cbn. set (Z := @mk_Zero (ComplexPreCat (AbelianToAdditive A hs))
                            ZeroComplex (ComplexPreCat_isZero (AbelianToAdditive A hs))).
    use mk_isEqualizer.
    intros w h H'. rewrite (@ZeroArrow_comp_right _ Z) in H'.
    use unique_exists.
    - exact (ComplexPreCat_KernelIn g h H').
    - cbn. use MorphismEq. intros i. use KernelCommutes.
    - intros y. apply has_homsets_ComplexPreCat.
    - intros y T. cbn beta in T.
      use MorphismEq.
      intros i. cbn.
      apply KernelArrowisMonic.
      rewrite KernelCommutes.
      apply (MorphismEq' _ _ _ T i).
  Qed.

  (** *** Kernels *)
  Definition ComplexPreCat_Kernels :
    Kernels (@mk_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))
                      ZeroComplex (ComplexPreCat_isZero (AbelianToAdditive A hs))).
  Proof.
    intros X Y f. cbn in *.
    use mk_Kernel.
    (* Kernel complex *)
    - exact (ComplexPreCat_Kernel f).
    (* Kernel arrow *)
    - exact (ComplexPreCat_KernelArrow f).
    (* Composition KernelArrow ;; g = ZeroArrow *)
    - exact (ComplexPreCat_Kernels_comp f).
    (* isEqualizer property *)
    - exact (ComplexPreCat_Kernels_isEqualizer f).
  Defined.


  (** ** Cokernels in Complexes over Abelian *)

  (** *** Cokernel complex *)
  Local Lemma ComplexPreCat_Cokernel_comm {Y Z : Complex (AbelianToAdditive A hs)}
        (g : Morphism Y Z) (i : hz) :
    (MMor g i) ;; ((Diff Z i) ;; (CokernelArrow (Cokernel (MMor g (i + 1))))) =
    ZeroArrow (@to_Zero A) (Y i) (Cokernel (MMor g (i + 1))).
  Proof.
    rewrite assoc. cbn. set (tmp := MComm g i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Local Lemma ComplexPreCat_Cokernel_comp {Y Z : Complex (AbelianToAdditive A hs)}
        (g : Morphism Y Z) (i : hz) :
    (CokernelOut (@to_Zero A) (Cokernel (MMor g i)) (Cokernel (MMor g (i + 1)))
                 ((Diff Z i) ;; (CokernelArrow (Cokernel (MMor g (i + 1)))))
                 (ComplexPreCat_Cokernel_comm g i))
      ;; (CokernelOut (@to_Zero A) (Cokernel (MMor g (i + 1))) (Cokernel (MMor g (i + 1 + 1)))
                      ((Diff Z (i + 1)) ;; (CokernelArrow (Cokernel (MMor g (i + 1 + 1)))))
                      (ComplexPreCat_Cokernel_comm g (i + 1))) =
    ZeroArrow (@to_Zero A) (Cokernel (MMor g i)) (Cokernel (MMor g (i + 1 + 1))).
  Proof.
    apply CokernelArrowisEpi. rewrite ZeroArrow_comp_right.
    rewrite assoc. rewrite CokernelCommutes. rewrite <- assoc. rewrite CokernelCommutes.
    rewrite assoc. set (tmp := CEq _ Z i). cbn in tmp. cbn. rewrite tmp. clear tmp.
    rewrite ZeroArrow_comp_left. apply idpath.
  Qed.

  Definition ComplexPreCat_Cokernel {Y Z : Complex (AbelianToAdditive A hs)} (g : Morphism Y Z) :
    ComplexPreCat (AbelianToAdditive A hs).
  Proof.
    use mk_Complex.
    - intros i. exact (Cokernel (MMor g i)).
    - intros i. cbn. use CokernelOut.
      + exact ((Diff Z i) ;; (CokernelArrow (Cokernel (MMor g (i + 1))))).
      + exact (ComplexPreCat_Cokernel_comm g i).
    - intros i. exact (ComplexPreCat_Cokernel_comp g i).
  Defined.

  (** *** CokernelArrow *)
  Definition ComplexPreCat_CokernelArrow {Y Z : Complex (AbelianToAdditive A hs)}
             (g : Morphism Y Z) : Morphism Z (ComplexPreCat_Cokernel g).
  Proof.
    use mk_Morphism.
    - intros i. use CokernelArrow.
    - intros i. use CokernelCommutes.
  Defined.

  (** *** Cokernel *)
  Local Lemma ComplexPreCat_CokernelCompZero {Y Z w : Complex (AbelianToAdditive A hs)}
        (g : (ComplexPreCat (AbelianToAdditive A hs))⟦Y, Z⟧)
        (h : (ComplexPreCat (AbelianToAdditive A hs))⟦Z, w⟧)
        (i : hz) :
    let Z0 := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    g ;; h = ZeroArrow Z0 Y w ->
    (MMor g i) ;; (MMor h i) = ZeroArrow (@to_Zero A) (Y i) (w i).
  Proof.
    intros Z0. cbn. intros H. set (tmp := MorphismEq' _ (g ;; h) _ H i). cbn in tmp.
    rewrite tmp. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexPreCat_Cokernels_Eq {Y Z w : Complex (AbelianToAdditive A hs)}
        (g : (ComplexPreCat (AbelianToAdditive A hs))⟦Y, Z⟧)
        (h : (ComplexPreCat (AbelianToAdditive A hs))⟦Z, w⟧)
        (H : g ;; h =
             ZeroArrow (Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))) Y w)
        (i : hz) :
    (CokernelOut (@to_Zero A) (Cokernel (MMor g i)) (w i) (MMor h i)
                 (ComplexPreCat_CokernelCompZero g h i H)) ;; (Diff w i) =
    (CokernelOut (@to_Zero A) (Cokernel (MMor g i)) (Cokernel (MMor g (i + 1)))
                 ((Diff Z i) ;; (CokernelArrow (Cokernel (MMor g (i + 1)))))
                 (ComplexPreCat_Cokernel_comm g i))
      ;; (CokernelOut (@to_Zero A) (Cokernel (MMor g (i + 1)))
                      (w (i + 1)) (MMor h (i + 1))
                      (ComplexPreCat_CokernelCompZero g h (i + 1) H)).
  Proof.
    apply CokernelArrowisEpi.
    rewrite assoc. rewrite assoc. rewrite CokernelCommutes.
    rewrite CokernelCommutes. rewrite <- assoc. rewrite CokernelCommutes.
    apply (MComm h i).
  Qed.

  Local Lemma ComplexPreCat_Cokernels_Comp {Y Z : Complex (AbelianToAdditive A hs)}
        (g : (ComplexPreCat (AbelianToAdditive A hs))⟦Y, Z⟧) :
    let Z0 := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    MorphismComp g (ComplexPreCat_CokernelArrow g) =
    MorphismComp (@ZeroArrowTo _ Z0 Y) (@ZeroArrowFrom _ Z0 (ComplexPreCat_Cokernel g)).
  Proof.
    use MorphismEq.
    intros i. cbn. rewrite CokernelCompZero. apply pathsinv0. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexPreCat_Cokernels_isCoequalizer {Y Z : Complex (AbelianToAdditive A hs)}
        (g : (ComplexPreCat (AbelianToAdditive A hs))⟦Y, Z⟧) :
    let Z0 := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    coequalizers.isCoequalizer
      g (MorphismComp (@ZeroArrowTo _ Z0 Y) (@ZeroArrowFrom _ Z0 Z))
      (ComplexPreCat_CokernelArrow g) (CokernelEqRw Z0 (ComplexPreCat_Cokernels_Comp g)).
  Proof.
    intros Z0.
    use mk_isCoequalizer.
    intros w h H'. rewrite (@ZeroArrow_comp_left _ Z0) in H'.
    use unique_exists.
    - use mk_Morphism.
      + intros i. cbn. use CokernelOut.
        * exact (MMor h i).
        * exact (ComplexPreCat_CokernelCompZero g h i H').
      + intros i. cbn. use ComplexPreCat_Cokernels_Eq.
    - cbn. use MorphismEq. intros i. use CokernelCommutes.
    - intros y. apply has_homsets_ComplexPreCat.
    - intros y T. cbn beta in T.
      use MorphismEq.
      intros i. cbn.
      apply CokernelArrowisEpi.
      rewrite CokernelCommutes.
      set (tmp := MorphismEq' _ _ _ T i). cbn in tmp.
      exact tmp.
  Qed.

  Definition ComplexPreCat_Cokernels :
    Cokernels (Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))).
  Proof.
    intros Y Z g. cbn in *.
    use mk_Cokernel.
    (* Cokernel *)
    - exact (ComplexPreCat_Cokernel g).
    (* CokernelArrow *)
    - exact(ComplexPreCat_CokernelArrow g).
    (* Composition is zero *)
    - exact (ComplexPreCat_Cokernels_Comp g).
    (* isCoequalizer *)
    - exact (ComplexPreCat_Cokernels_isCoequalizer g).
  Defined.


  (** ** Monics are kernels *)

  (** *** Kernel complex from Monic *)
  Local Lemma ComplexPreCat_Monic_Kernel_Complex_comm
    {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (M : Monic (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) (i : hz) :
    (MMor (MonicArrow _ M) i)
      ;; ((Diff y i) ;; (CokernelArrow (Cokernel (MMor (MonicArrow _ M) (i + 1))))) =
    ZeroArrow (@to_Zero A) _ (Cokernel (MMor (MonicArrow _ M) (i + 1))).
  Proof.
    rewrite assoc. rewrite (MComm (MonicArrow _ M)). rewrite <- assoc.
    rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Local Lemma ComplexPreCat_Monic_Kernel_Complex_comp
    {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (M : Monic (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) (i : hz) :
    (CokernelOut to_Zero (Cokernel (MMor (MonicArrow _ M) i))
                 (Cokernel (MMor (MonicArrow _ M) (i + 1)))
                 ((Diff y i) ;; (CokernelArrow (Cokernel (MMor (MonicArrow _ M) (i + 1)))))
                 (ComplexPreCat_Monic_Kernel_Complex_comm M i))
      ;; (CokernelOut to_Zero (Cokernel (MMor (MonicArrow _ M) (i + 1)))
                      (Cokernel (MMor (MonicArrow _ M) (i + 1 + 1)))
                      ((Diff y (i + 1))
                         ;; (CokernelArrow (Cokernel (MMor (MonicArrow _ M) (i + 1 + 1)))))
                      (ComplexPreCat_Monic_Kernel_Complex_comm M (i + 1))) =
    ZeroArrow
      to_Zero (Cokernel (MMor (MonicArrow _ M) i)) (Cokernel (MMor (MonicArrow _ M) (i + 1 + 1))).
  Proof.
    apply CokernelArrowisEpi. rewrite assoc. rewrite CokernelCommutes.
    rewrite <- assoc. rewrite CokernelCommutes. rewrite assoc.
    cbn. set (tmp := CEq _ y i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_right.
    apply idpath.
  Qed.

  Definition ComplexPreCat_Monic_Kernel_Complex
    {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (M : Monic (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) :
    ComplexPreCat_Additive (AbelianToAdditive A hs).
  Proof.
    use mk_Complex.
    - intros i. exact (Cokernel (@MMor _ x y (MonicArrow _ M) i)).
    - intros i. cbn. use CokernelOut.
      + exact ((Diff y i) ;; (CokernelArrow (Cokernel (@MMor _ x y (MonicArrow _ M) (i + 1))))).
      + use ComplexPreCat_Monic_Kernel_Complex_comm.
    - intros i. cbn. exact (ComplexPreCat_Monic_Kernel_Complex_comp M i).
  Defined.

  (** *** The morphisms which has Monic M as the kernel  *)
  Definition KernelMorphism {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
             (M : Monic (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) :
    Morphism y (ComplexPreCat_Monic_Kernel_Complex M).
  Proof.
    use mk_Morphism.
    - intros i. apply CokernelArrow.
    - intros i. use CokernelCommutes.
  Defined.

  (** *** KernelIn *)
  Local Lemma KernelMorphism_eq {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    MorphismComp (MonicArrow _ M) (KernelMorphism M) =
    MorphismComp (MonicArrow _ M)
                 (MorphismComp
                    (@ZeroArrowTo (ComplexPreCat (AbelianToAdditive A hs)) Z y)
                    (@ZeroArrowFrom (ComplexPreCat (AbelianToAdditive A hs)) Z
                                    (@ComplexPreCat_Monic_Kernel_Complex x y M))).
  Proof.
    intros Z.
    use MorphismEq.
    intros i. cbn. rewrite CokernelCompZero.
    rewrite assoc. apply pathsinv0. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexMonicKernelInComm {x y : Complex (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
        {w : ComplexPreCat (AbelianToAdditive A hs)}
        (h : (ComplexPreCat (AbelianToAdditive A hs))⟦w, y⟧)
        (H : let Z := @Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
             h ;; (KernelMorphism M) =
             h ;; (MorphismComp (@ZeroArrowTo _ Z y)
                                (@ZeroArrowFrom _ Z (@ComplexPreCat_Monic_Kernel_Complex x y M))))
        (i : hz) :
    (MMor h i) ;; (CokernelArrow (Cokernel (MMor (MonicArrow _ M) i))) =
    ZeroArrow (@to_Zero A) _ (Cokernel (MMor (MonicArrow _ M) i)).
  Proof.
    set (H' := MorphismEq' _ _ _ H i). cbn in H'. cbn. rewrite H'.
    rewrite assoc. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexMonicKernelIn_Complex_Comm {x y w : Complex (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
        (h : (ComplexPreCat (AbelianToAdditive A hs))⟦w, y⟧) (i : hz)
        (H : let Z := @Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
             h ;; KernelMorphism M =
             h ;; (MorphismComp (@ZeroArrowTo _ Z y)
                                (@ZeroArrowFrom _ Z (@ComplexPreCat_Monic_Kernel_Complex x y M)))) :
    (KernelIn
       to_Zero
       (MonicToKernel A hs (mk_Monic A (MMor (MonicArrow _ M) i) ((ComplexMonicIndexMonic _ M) i)))
       (w i) (MMor h i) (ComplexMonicKernelInComm M h H i)) ;; (Diff x i) =
    (Diff w i)
      ;; (KernelIn
            to_Zero
            (MonicToKernel A hs (mk_Monic A (MMor (MonicArrow _ M) (i + 1))
                                          ((ComplexMonicIndexMonic _ M) (i + 1))))
            (w (i + 1)) (MMor h (i + 1)) (ComplexMonicKernelInComm M h H (i + 1))).
  Proof.
    set (isM := ComplexMonicIndexMonic _ M).
    set (ker := MonicToKernel A hs (mk_Monic _ _ (isM (i + 1)))).
    cbn in *. apply (KernelArrowisMonic _ ker).
    rewrite <- assoc. rewrite <- assoc. fold ker.
    rewrite (KernelCommutes _ ker). cbn. use (pathscomp0 _ (MComm h i)).
    set (tmp := MComm (MonicArrow _ M) i). cbn in tmp. rewrite <- tmp. clear tmp.
    rewrite assoc. apply cancel_postcomposition.
    apply (KernelCommutes _ (MonicToKernel A hs (mk_Monic A _ (isM i))) (w i) (MMor h i)).
  Qed.

  Definition ComplexMonicKernelIn {x y : Complex (AbelianToAdditive A hs)}
             (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
             {w : ComplexPreCat (AbelianToAdditive A hs)}
             (h : (ComplexPreCat (AbelianToAdditive A hs))⟦w, y⟧) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    h ;; (KernelMorphism M) =
    h ;; (MorphismComp (@ZeroArrowTo _ Z y)
                       (@ZeroArrowFrom _ Z (ComplexPreCat_Monic_Kernel_Complex M))) ->
    (ComplexPreCat (AbelianToAdditive A hs))⟦w, x⟧.
  Proof.
    intros Z H'.
    set (isM := ComplexMonicIndexMonic _ M).
    use mk_Morphism.
    - intros i.
      exact (KernelIn to_Zero (MonicToKernel A hs (mk_Monic _ _ (isM i))) _ (MMor h i)
                      (ComplexMonicKernelInComm M h H' i)).
    - intros i. exact (ComplexMonicKernelIn_Complex_Comm M h i H').
  Defined.

  (** *** MonicKernelsData *)

  Definition ComplexPreCatAbelianMonicKernelsData_isEqualizer
             {x y : Complex (AbelianToAdditive A hs)}
             (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    @equalizers.isEqualizer
      (ComplexPreCat (AbelianToAdditive A hs)) _ _ _ (KernelMorphism M)
      (MorphismComp (@ZeroArrowTo _ Z y) (ZeroArrowFrom (ComplexPreCat_Monic_Kernel_Complex M))) M
      (KernelMorphism_eq M).
  Proof.
    intros Z.
    set (isM := ComplexMonicIndexMonic _ M).
    use mk_isEqualizer.
    intros w h H'.
    use unique_exists.
    - apply (ComplexMonicKernelIn M h H').
    - cbn. use MorphismEq.
      intros i. cbn.
      apply (KernelCommutes _ (MonicToKernel A hs (mk_Monic A _ (isM i))) _ (MMor h i)).
    - intros y0. apply has_homsets_ComplexPreCat.
    - intros y0 T. cbn in T.
      use MorphismEq.
      intros i. apply (isM i).
      set (tmp :=  MorphismEq' _ _ _ T i). cbn in tmp. cbn. rewrite tmp.
      apply pathsinv0. clear tmp.
      apply (KernelCommutes _ (MonicToKernel A hs (mk_Monic A _ (isM i))) _ (MMor h i)).
  Qed.

  Definition ComplexPreCatAbelianMonicKernelsData :
    let Add := ComplexPreCat_Additive (AbelianToAdditive A hs) in
    AbelianMonicKernelsData
      Add ((Additive.to_Zero Add)
             ,, (Additive.to_BinProducts Add),, (Additive.to_BinCoproducts Add)).
  Proof.
    intros Add x y M.
    set (isM := ComplexMonicIndexMonic _ M).
    use tpair.
    - use tpair.
      + use tpair.
        * exact (ComplexPreCat_Monic_Kernel_Complex M).
        * exact (KernelMorphism M).
      + exact (KernelMorphism_eq M).
    - exact (ComplexPreCatAbelianMonicKernelsData_isEqualizer M).
  Defined.


  (** ** Epis are Cokernels *)

  Local Lemma ComplexPreCat_Epi_Cokernel_Complex_comm
        {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) (i : hz) :
    (KernelArrow (Kernel (MMor (EpiArrow _ E) i))) ;; (Diff x i) ;; (MMor (EpiArrow _ E) (i + 1)) =
    ZeroArrow (@to_Zero A) (Kernel (MMor (EpiArrow _ E) i)) _.
  Proof.
    rewrite <- assoc. rewrite <- (MComm (EpiArrow _ E)). rewrite assoc.
    rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Local Lemma ComplexPreCat_Epi_Cokernel_Complex_comp
        {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) (i : hz) :
    (KernelIn to_Zero (Kernel (MMor (EpiArrow _ E) (i + 1))) (Kernel (MMor (EpiArrow _ E) i))
              ((KernelArrow (Kernel (MMor (EpiArrow _ E) i))) ;; (Diff x i))
              (ComplexPreCat_Epi_Cokernel_Complex_comm E i))
      ;; (KernelIn to_Zero (Kernel (MMor (EpiArrow _ E) (i + 1 + 1)))
                   (Kernel (MMor (EpiArrow _ E) (i + 1)))
                   ((KernelArrow (Kernel (MMor (EpiArrow _ E) (i + 1)))) ;; (Diff x (i + 1)))
                   (ComplexPreCat_Epi_Cokernel_Complex_comm E (i + 1))) =
    ZeroArrow to_Zero (Kernel (MMor (EpiArrow _ E) i)) (Kernel (MMor (EpiArrow _ E) (i + 1 + 1))).
  Proof.
    apply KernelArrowisMonic. rewrite <- assoc. rewrite KernelCommutes.
    rewrite assoc. rewrite KernelCommutes. rewrite <- assoc.
    cbn. set (tmp := CEq _ x i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply idpath.
  Qed.

  Definition ComplexPreCat_Epi_Cokernel_Complex
             {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
             (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) :
    ComplexPreCat_Additive (AbelianToAdditive A hs).
  Proof.
    use mk_Complex.
    - intros i.
      exact (Kernel (@MMor _ x y (EpiArrow _ E) i)).
    - intros i. cbn. use KernelIn.
      + exact ((KernelArrow (Kernel (@MMor _ x y (EpiArrow _ E) i))) ;; (Diff x i)).
      + apply ComplexPreCat_Epi_Cokernel_Complex_comm.
    - intros i. exact (ComplexPreCat_Epi_Cokernel_Complex_comp E i).
  Defined.

  (** This is the morphism which has E as cokernel *)
  Definition CokernelMorphism {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
             (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) :
    Morphism (ComplexPreCat_Epi_Cokernel_Complex E) x.
  Proof.
    use mk_Morphism.
    - intros i. cbn. use KernelArrow.
    - intros i. cbn. exact (! (KernelCommutes _ _ _ _ _)).
  Defined.

  Definition CokernelMorphism_eq {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
             (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    MorphismComp (CokernelMorphism E) (EpiArrow _ E) =
    MorphismComp (MorphismComp (@ZeroArrowTo _ Z (ComplexPreCat_Epi_Cokernel_Complex E))
                               (@ZeroArrowFrom _ Z x)) (EpiArrow _ E).
  Proof.
    use MorphismEq.
    intros i. cbn. rewrite KernelCompZero.
    rewrite <- assoc. apply pathsinv0. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexPreCatCokernelOut_comp
    {x y w0 : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y)
    (h : (ComplexPreCat (AbelianToAdditive A hs))⟦x, w0⟧)
    (H : let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
         MorphismComp
           (MorphismComp
              (@ZeroArrowTo _ Z (ComplexPreCat_Epi_Cokernel_Complex E))
              (@ZeroArrowFrom _ Z x)) h = MorphismComp (@CokernelMorphism x y E) h) (i : hz) :
    KernelArrow (Kernel (MMor (EpiArrow _ E) i)) ;; MMor h i =
    ZeroArrow (@to_Zero A) (Kernel (MMor (EpiArrow _ E) i)) _.
  Proof.
    set (H' := MorphismEq' _ _ _ H i). cbn in H'. cbn. rewrite <- H'.
    rewrite <- assoc. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexPreCatCokernelOut_comm
    {x y w0 : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y) (i : hz)
    (h : (ComplexPreCat (AbelianToAdditive A hs))⟦x, w0⟧)
    (H : let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
         MorphismComp
           (MorphismComp
              (@ZeroArrowTo _ Z (ComplexPreCat_Epi_Cokernel_Complex E)) (@ZeroArrowFrom _ Z x)) h =
         MorphismComp (@CokernelMorphism x y E) h) :
    let isE := ComplexEpiIndexEpi _ E in
    (CokernelOut to_Zero
                 (EpiToCokernel A hs (mk_Epi A (MMor (EpiArrow _ E) i) (isE i))) _ (MMor h i)
                 (ComplexPreCatCokernelOut_comp E h H i)) ;; (Diff w0 i) =
    (Diff y i)
      ;; (CokernelOut to_Zero
                      (EpiToCokernel A hs (mk_Epi A (MMor (EpiArrow _ E) (i + 1)) (isE (i + 1))))
                      _ (MMor h (i + 1)) (ComplexPreCatCokernelOut_comp E h H (i + 1))).
  Proof.
    intros isE.
    apply pathsinv0.
    set (coker := EpiToCokernel A hs (mk_Epi _ _ (isE i))).
    apply (CokernelArrowisEpi _ coker). rewrite assoc. rewrite assoc. rewrite CokernelCommutes.
    use (pathscomp0 _ (! (MComm h i))). cbn.
    set (tmp := MComm (EpiArrow _ E) i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite <- assoc. apply cancel_precomposition.
    apply (CokernelCommutes _ (EpiToCokernel A hs (mk_Epi A _ (isE (i + 1))))).
  Qed.

  Definition ComplexPreCatCokernelOut
    {x y z : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y)
    (h : (ComplexPreCat (AbelianToAdditive A hs))⟦x, z⟧)
    (H : let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
         MorphismComp
           (MorphismComp
              (@ZeroArrowTo _ Z (ComplexPreCat_Epi_Cokernel_Complex E)) (@ZeroArrowFrom _ Z x)) h =
         MorphismComp (@CokernelMorphism x y E) h) :
    (ComplexPreCat (AbelianToAdditive A hs))⟦y, z⟧.
  Proof.
    set (isE := ComplexEpiIndexEpi _ E).
    use mk_Morphism.
    - intros i. exact (CokernelOut
                         (@to_Zero A) (EpiToCokernel A hs (mk_Epi _ _ (isE i))) _ (MMor h i)
                         (ComplexPreCatCokernelOut_comp E h H i)).
    - intros i. exact (ComplexPreCatCokernelOut_comm E i h H).
  Defined.

  (** *** EpisCokernelsData *)

  Local Lemma ComplexPreCatAbelianEpiCokernelsData_isCoequalizer
        {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) :
    let Add := ComplexPreCat_Additive (AbelianToAdditive A hs) in
    @coequalizers.isCoequalizer Add _ _ _ (CokernelMorphism E)
      (MorphismComp (ZeroArrowTo (ComplexPreCat_Epi_Cokernel_Complex E)) (ZeroArrowFrom x)) E
      (CokernelMorphism_eq E).
  Proof.
    intros Add.
    set (isE := ComplexEpiIndexEpi (AbelianToAdditive A hs) E).
    use mk_isCoequalizer.
    intros w0 h H'.
    use unique_exists.
    - apply (ComplexPreCatCokernelOut E h (! H')).
    - cbn. use MorphismEq.
      intros i. cbn.
      apply (CokernelCommutes _ (EpiToCokernel A hs (mk_Epi A _ (isE i))) _ (MMor h i)).
    - intros y0. apply has_homsets_ComplexPreCat.
    - intros y0 T. cbn in T.
      use MorphismEq.
      intros i. apply (isE i).
      set (tmp :=  MorphismEq' _ _ _ T i). cbn in tmp. cbn. rewrite tmp.
      apply pathsinv0. clear tmp.
      apply (CokernelCommutes _ (EpiToCokernel A hs (mk_Epi A _ (isE i))) _ (MMor h i)).
  Qed.

  Definition ComplexPreCatAbelianEpiCokernelsData :
    let Add := ComplexPreCat_Additive (AbelianToAdditive A hs) in
    AbelianEpiCokernelsData
      Add ((Additive.to_Zero Add)
             ,, (Additive.to_BinProducts Add),, (Additive.to_BinCoproducts Add)).
  Proof.
    intros Add x y E.
    set (isE := ComplexEpiIndexEpi _ E).
    use tpair.
    - use tpair.
      + use tpair.
        * exact (ComplexPreCat_Epi_Cokernel_Complex E).
        * exact (CokernelMorphism E).
      + exact (CokernelMorphism_eq E).
    - exact (ComplexPreCatAbelianEpiCokernelsData_isCoequalizer E).
  Defined.


  (** ** Complexes over Abelian is Abelian *)

  Definition ComplexPreCat_AbelianPreCat : AbelianPreCat.
  Proof.
    use mk_Abelian.
    - exact (ComplexPreCat_Additive (AbelianToAdditive A hs)).
    - split.
      + exact (Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))).
      + split.
        * exact (Additive.to_BinProducts (ComplexPreCat_Additive (AbelianToAdditive A hs))).
        * exact (Additive.to_BinCoproducts (ComplexPreCat_Additive (AbelianToAdditive A hs))).
    - split.
      + split.
        * cbn. exact ComplexPreCat_Kernels.
        * cbn. exact ComplexPreCat_Cokernels.
      + split.
        * exact ComplexPreCatAbelianMonicKernelsData.
        * exact ComplexPreCatAbelianEpiCokernelsData.
  Defined.

  Lemma has_homsets_ComplexPreCat_AbelianPreCat : has_homsets ComplexPreCat_AbelianPreCat.
  Proof.
    apply has_homsets_ComplexPreCat.
  Qed.

End complexes_abelian.


(** * Transposition of differentials *)
Section transport_diffs.

  Variable A : Additive.

  Lemma transport_Diff (C : Complex A) (i : hz) :
    transportb (λ x' : A, A ⟦ x', C (i + 1) ⟧) (maponpaths C (hzrplusminus i 1)) (Diff C i) =
    transportf (precategory_morphisms (C (i + 1 - 1))) (maponpaths C (hzrminusplus (i + 1) 1))
               (Diff C (i + 1 - 1)).
  Proof.
    unfold transportb. rewrite <- functtransportf.
    rewrite <- maponpathsinv0. rewrite <- functtransportf.
    use transportf_path.
    - exact (C (i + 1 - 1 + 1)).
    - exact (maponpaths C (! hzrminusplus (i + 1) 1)).
    - rewrite <- functtransportf. rewrite <- functtransportf.
      rewrite transport_f_f. rewrite pathsinv0r. cbn. unfold idfun.
      use (pathscomp0 _ (@transport_section hz _ (Diff C) i (i + 1 - 1) (! (hzrplusminus i 1)))).
      (* Split the right hand side to two transports *)
      rewrite (@transportf_mor' hz A). unfold transportb. rewrite pathsinv0inv0.
      rewrite functtransportf.
      (* Here only the equations of the first transportfs are different! *)
      use transportf_paths.
      assert (e5 : maponpaths C (! hzrminusplus (i + 1) 1) =
                   maponpaths (C ∘ (λ x' : pr1 hz, x' + 1)) (! hzrplusminus i 1)).
      {
        use (pathscomp0 _ (maponpathscomp (λ x' : pr1 hz, x' + 1) C (! hzrplusminus i 1))).
        apply maponpaths. apply isasethz.
      }
      use (pathscomp0 e5). clear e5. induction (! hzrplusminus i 1). apply idpath.
  Qed.

End transport_diffs.


(** * Homotopies of complexes and K(A), the naive homotopy category of A. *)
(** ** Introduction
   We define homotopy of complexes and the naive homotopy category K(A). A homotopy χ from complex
   X to a complex Y is a family of morphisms χ^i : X^i --> Y^{i-1}. Note that a homotopy χ induces
   a morphism of complexes h : X --> Y by setting
                      # h^i = χ^i ;; d^{i-1}_Y + d^i_X ;; χ^{i+1}. #
                      $ h^i = χ^i ;; d^{i-1}_Y + d^i_X ;; χ^{i+1}. $
   The subset of morphisms in Mor(X, Y) which have a path to a morphism of the form h form an
   abelian subgroup of Mor(X, Y). Also, if f : Z_1 --> X and g : Y --> Z_2 are morphisms of
   complexes, then f ;; h and h ;; g have paths to morphisms induced by homotopies. These are given
   (f^i ;; χ^i) and (χ^i ;; g^{i-1}), respectively.

   These are the properties that are enough to form the quotient category of C(A) using
   [QuotPrecategory_Additive]. We call the resulting category the naive homotopy category of A, and
   denote it by K(A). The objects of K(A) are objects of C(A) and Mor_{K(A)}(X, Y) =
   Mor_{C(A)}(X, Y) / (the subgroup of morphisms coming from homotopies, [ComplexHomotSubgrp]).

   Homotopies are defined in [ComplexHomot]. The induced morphisms of a homotopy is constructed in
   [ComplexHomotMorphism]. The subgroup of morphisms coming from homotopies is defined in
   [ComplexHomotSubgrp]. Pre- and postcomposition of morphisms coming from homotopies are morphisms
   coming from homotopies are proven in [ComplexHomotSubgrop_comp_right] and
   [ComplexHomotSubgrop_comp_left]. The naive homotopy category K(A) is constructed in
   [ComplexHomot_Additive].
*)
Section complexes_homotopies.

  Variable A : Additive.

  Definition ComplexHomot (C1 C2 : Complex A) : UU := Π (i : hz), A⟦C1 i, C2 (i - 1)⟧.

  (** This lemma shows that the squares of the morphism map, defined by the homotopy H, commute. *)
  Local Lemma ComplexHomotMorphism_comm {C1 C2 : Complex A} (H : ComplexHomot C1 C2) (i : hz) :
    to_binop (C1 i) (C2 i)
             (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                         (H i ;; Diff C2 (i - 1)))
             (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrplusminus i 1))
                         (Diff C1 i ;; H (i + 1))) ;;
             Diff C2 i =
    Diff C1 i ;; to_binop (C1 (i + 1)) (C2 (i + 1))
         (transportf (precategory_morphisms (C1 (i + 1))) (maponpaths C2 (hzrminusplus (i + 1) 1))
                     (H (i + 1) ;; Diff C2 (i + 1 - 1)))
         (transportf (precategory_morphisms (C1 (i + 1))) (maponpaths C2 (hzrplusminus (i + 1) 1))
                     (Diff C1 (i + 1) ;; H (i + 1 + 1))).
  Proof.
    (* First we get rid of the ZeroArrows *)
    rewrite to_postmor_linear'. rewrite to_premor_linear'.
    assert (e0 : (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                             (H i ;; Diff C2 (i - 1)) ;;
                             Diff C2 i) = ZeroArrow (Additive.to_Zero A) _ _).
    {
      induction (hzrminusplus i 1). cbn. unfold idfun. rewrite <- assoc.
      rewrite (@CEq A C2 (i - 1)). apply ZeroArrow_comp_right.
    }
    rewrite e0. clear e0.
    assert (e1 : (Diff C1 i ;; transportf (precategory_morphisms (C1 (i + 1)))
                       (maponpaths C2 (hzrplusminus (i + 1) 1)) (Diff C1 (i + 1) ;; H (i + 1 + 1)))
                 = ZeroArrow (Additive.to_Zero A) _ _).
    {
      rewrite <- transportf_postcompose. rewrite assoc. rewrite (@CEq A C1 i).
      rewrite ZeroArrow_comp_left. apply transportf_ZeroArrow.
    }
    rewrite e1. clear e1.
    rewrite <- PreAdditive_unel_zero. rewrite to_lunax'. rewrite to_runax'.
    (* Here the idea is to apply cancel_precomposition *)
    rewrite transportf_postcompose. rewrite <- assoc. apply cancel_precomposition.
    (* Other application of cancel_precomposition *)
    rewrite transport_compose. rewrite transportf_postcompose. apply cancel_precomposition.
    (* Start to solve the transport stuff *)
    rewrite <- functtransportf. rewrite <- functtransportb. unfold transportb.
    use (transportf_path _ _ (maponpaths C2 (hzrminusplus' (i + 1) 1))).
    rewrite <- functtransportf. rewrite <- functtransportf. rewrite transport_f_f.
    assert (e2 : (hzrminusplus (i + 1) 1 @ hzrminusplus' (i + 1) 1) = idpath _)
      by apply isasethz.
    rewrite e2. clear e2. cbn. unfold idfun.
    use (pathscomp0 _ (@transport_section hz _ (Diff C2) i (i + 1 - 1) (! (hzrplusminus i 1)))).
    assert (e3 : (! hzrplusminus i 1) = hzrplusminus' i 1) by apply isasethz.
    cbn. cbn in e3. rewrite e3. clear e3.
    (* Split the right hand side to two transports *)
    rewrite (@transportf_mor' hz A). unfold transportb. rewrite pathsinv0inv0.
    rewrite functtransportf. cbn.
    (* Here only the equations of the first transportfs are different! *)
    use transportf_paths.
    assert (e5 : maponpaths C2 (hzrminusplus' (i + 1) 1) =
                 maponpaths (C2 ∘ (λ x' : pr1 hz, x' + 1)) (hzrplusminus' i 1)).
    {
      use (pathscomp0 _ (maponpathscomp (λ x' : pr1 hz, x' + 1) C2 (hzrplusminus' i 1))).
      apply maponpaths. apply isasethz.
    }
    use (pathscomp0 e5). clear e5. induction (hzrplusminus' i 1). apply idpath.
  Qed.

  (** Every homotopy H of complexes induces a morphisms of complexes. The morphisms is defined by
      taking the map C1 i --> C2 i to be the sum
                         (H i) ;; (Diff C2 (i - 1)) + (Diff C1 i) ;; (H (i + 1)).
      Note that we need to use transportf because the targets are not definitionally equal. The
      target of the first is C2 (i - 1 + 1) and the second target is C2 (i + 1 - 1). We transport
      these to C2 i. *)
  Definition ComplexHomotMorphism {C1 C2 : Complex A} (H : ComplexHomot C1 C2) : Morphism C1 C2.
  Proof.
    use mk_Morphism.
    - intros i.
      use to_binop.
      + exact (transportf _ (maponpaths C2 (hzrminusplus i 1)) ((H i) ;; (Diff C2 (i - 1)))).
      + exact (transportf _ (maponpaths C2 (hzrplusminus i 1)) ((Diff C1 i) ;; (H (i + 1)))).
    - intros i. exact (ComplexHomotMorphism_comm H i).
  Defined.

  (** For all complexes C1 and C2, we define a subset of C1 --> C2 to consist of all the morphisms
      which have a path to a morphism induced by a homotopy H by [ComplexHomotMorphism]. Our goal is
      to show that this subset is an abelian subgroup, and thus we can form the quotient group. *)
  Definition ComplexHomotSubset (C1 C2 : Complex A) :
    @hsubtypes ((ComplexPreCat_Additive A)⟦C1, C2⟧) :=
    (fun (f : ((ComplexPreCat_Additive A)⟦C1, C2⟧)) =>
       ∃ (H : ComplexHomot C1 C2), ComplexHomotMorphism H = f).

  Local Lemma grinvop (Y : gr) :
    Π y1 y2 : Y, grinv Y (@op Y y1 y2) = @op Y (grinv Y y2) (grinv Y y1).
  Proof.
    intros y1 y2.
    apply (grrcan Y y1).
    rewrite (assocax Y). rewrite (grlinvax Y). rewrite (runax Y).
    apply (grrcan Y y2).
    rewrite (grlinvax Y). rewrite (assocax Y). rewrite (grlinvax Y).
    apply idpath.
  Qed.

  (** This lemma shows that the subset [ComplexHomotSubset] satisfies the axioms of a subgroup. *)
  Lemma ComplexHomotisSubgrop (C1 C2 : Complex A) :
    @issubgr (@to_abgrop (ComplexPreCat_Additive A) C1 C2) (ComplexHomotSubset C1 C2).
  Proof.
    use tpair.
    - use tpair.
      + intros f g P X. induction f as [f1 f2]. induction g as [g1 g2].
        use (squash_to_prop f2). apply propproperty. intros f3.
        use (squash_to_prop g2). apply propproperty. intros g3.
        induction f3 as [f3 f4]. induction g3 as [g3 g4].
        apply X. clear P X. cbn.
        use tpair.
        * intros i.
          use to_binop.
          -- exact (f3 i).
          -- exact (g3 i).
        * cbn.
          rewrite <- f4. rewrite <- g4.
          use MorphismEq.
          intros i. cbn.
          rewrite to_postmor_linear'.
          rewrite to_premor_linear'.
          assert (e0 : (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrplusminus i 1))
                                   (to_binop (C1 i) (C2 (i + 1 - 1)) (Diff C1 i ;; f3 (i + 1))
                                             (Diff C1 i ;; g3 (i + 1)))) =
                       to_binop (C1 i) (C2 i)
                                (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrplusminus i 1))
                                            (Diff C1 i ;; f3 (i + 1)))
                                (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrplusminus i 1))
                                            (Diff C1 i ;; g3 (i + 1)))).
          {
            induction (hzrplusminus i 1). apply idpath.
          }
          cbn in e0. rewrite e0. clear e0.
          assert (e1 : (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                                   (to_binop (C1 i) (C2 (i - 1 + 1)) (f3 i ;; Diff C2 (i - 1))
                                             (g3 i ;; Diff C2 (i - 1)))) =
                       to_binop (C1 i) (C2 i)
                                (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrminusplus i 1))
                                            (f3 i ;; Diff C2 (i - 1)))
                                (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrminusplus i 1))
                                            (g3 i ;; Diff C2 (i - 1)))).
          {
            induction (hzrminusplus i 1). apply idpath.
          }
          cbn in e1. rewrite e1. clear e1.
          set (tmp := @assocax (@to_abgrop A (C1 i) (C2 i))). cbn in tmp.
          rewrite tmp. rewrite tmp. apply maponpaths.
          rewrite <- tmp. rewrite <- tmp.
          set (tmp' := @commax (@to_abgrop A (C1 i) (C2 i))). cbn in tmp'.
          rewrite tmp'.
          rewrite (tmp' _ (transportf (precategory_morphisms (C1 i))
                                      (maponpaths C2 (hzrplusminus i 1))
                                      (Diff C1 i ;; g3 (i + 1)))).
          apply maponpaths.
          apply tmp'.
      (* ZeroMorphisms *)
      + cbn. intros P X. apply X. clear X P.
        use tpair.
        * intros i. exact (ZeroArrow (Additive.to_Zero A) _ _).
        * cbn. use MorphismEq. intros i. cbn. rewrite ZeroArrow_comp_left.
          rewrite transportf_ZeroArrow.
          rewrite ZeroArrow_comp_right. rewrite transportf_ZeroArrow.
          rewrite <- PreAdditive_unel_zero. rewrite to_lunax'. apply idpath.
    - intros f H. use (squash_to_prop H). apply propproperty. intros H'. clear H.
      induction H' as [homot eq]. intros P X. apply X. clear P X.
      use tpair.
      + intros i. exact (grinv (to_abgrop (C1 i) (C2 (i - 1))) (homot i)).
      + cbn. rewrite <- eq. use MorphismEq. intros i. cbn.
        set (tmp := @PreAdditive_invrcomp A _ _ _ (Diff C1 i) (homot (i + 1))).
        unfold to_inv in tmp. cbn in tmp. cbn. rewrite <- tmp. clear tmp.
        assert (e0 : (transportf (precategory_morphisms (C1 i))
                                 (maponpaths C2 (hzrplusminus i 1))
                                 (grinv (to_abgrop (C1 i) (C2 (i + 1 - 1)))
                                        (Diff C1 i ;; homot (i + 1)))) =
                     to_inv _ _ (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrplusminus i 1))
                                            (Diff C1 i ;; homot (i + 1)))).
        {
          unfold to_inv. cbn. induction (hzrplusminus i 1). apply idpath.
        }
        cbn in e0. rewrite e0. clear e0.
        assert (e1 : (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                                 (grinv (to_abgrop (C1 i) (C2 (i - 1)))
                                        (homot i) ;; Diff C2 (i - 1))) =
                     to_inv _ _ (transportf (precategory_morphisms (C1 i))
                                            (maponpaths C2 (hzrminusplus i 1))
                                            (homot i ;; Diff C2 (i - 1)))).
        {
          unfold to_inv. cbn. induction (hzrminusplus i 1). cbn. unfold idfun.
          set (tmp := @PreAdditive_invlcomp A (C1 i) (C2 (i - 1)) (C2 (i - 1 + 1))
                                            (homot i) (Diff C2 (i - 1))).
          apply pathsinv0. unfold to_inv in tmp.
          apply tmp.
        }
        cbn in e1. rewrite e1. clear e1.
        set (tmp' := @commax (@to_abgrop A (C1 i) (C2 i))). cbn in tmp'. rewrite tmp'. clear tmp'.
        set (tmp := @grinvop (@to_abgrop A (C1 i) (C2 i))). cbn in tmp. unfold to_inv.
        apply pathsinv0.
        apply tmp.
  Qed.

  Definition ComplexHomotSubgrp (C1 C2 : Complex A) :
    @subabgrs (@to_abgrop (ComplexPreCat_Additive A) C1 C2).
  Proof.
    use subgrconstr.
    - exact (ComplexHomotSubset C1 C2).
    - exact (ComplexHomotisSubgrop C1 C2).
  Defined.

  (** Pre- and postcomposition with morphisms in ComplexHomotSubset is in ComplexHomotSubset. *)
  Lemma ComplexHomotSubgrop_comp_left (C1 : Complex A) {C2 C3 : Complex A}
        (f : ((ComplexPreCat_Additive A)⟦C2, C3⟧)) (H : ComplexHomotSubset C2 C3 f) :
    Π (g : ((ComplexPreCat_Additive A)⟦C1, C2⟧)), ComplexHomotSubset C1 C3 (g ;; f).
  Proof.
    intros g P X.
    use (squash_to_prop H). apply propproperty. intros HH.
    apply X. clear P X.
    induction HH as [homot eq].
    use tpair.
    - intros i. exact ((MMor g i) ;; (homot i)).
    - cbn. rewrite <- eq. use MorphismEq. intros i. cbn. rewrite assoc.
      rewrite <- (MComm g i). rewrite transportf_postcompose. rewrite transportf_postcompose.
      rewrite <- assoc. rewrite <- assoc. rewrite <- to_premor_linear'.
      rewrite <- transportf_postcompose. rewrite <- transportf_postcompose.
      apply idpath.
  Qed.

  Lemma ComplexHomotSubgrop_comp_right {C1 C2 : Complex A} (C3 : Complex A)
        (f : ((ComplexPreCat_Additive A)⟦C1, C2⟧)) (H : ComplexHomotSubset C1 C2 f) :
    Π (g : ((ComplexPreCat_Additive A)⟦C2, C3⟧)), ComplexHomotSubset C1 C3 (f ;; g).
  Proof.
    intros g P X.
    use (squash_to_prop H). apply propproperty. intros HH.
    apply X. clear P X.
    induction HH as [homot eq].
    use tpair.
    - intros i. exact ((homot i) ;; (MMor g (i - 1))).
    - cbn. rewrite <- eq. use MorphismEq. intros i. cbn. rewrite <- assoc.
      rewrite (MComm g (i - 1)). rewrite assoc. rewrite assoc.
      assert (e0 : (transportf (precategory_morphisms (C1 i)) (maponpaths C3 (hzrminusplus i 1))
                               (homot i ;; Diff C2 (i - 1) ;; MMor g (i - 1 + 1))) =
                   (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                               (homot i ;; Diff C2 (i - 1))) ;; (MMor g i)).
      {
        induction (hzrminusplus i 1). apply idpath.
      }
      cbn in e0. rewrite e0. clear e0.
      assert (e1 : (transportf (precategory_morphisms (C1 i)) (maponpaths C3 (hzrplusminus i 1))
                               (Diff C1 i ;; homot (i + 1) ;; MMor g (i + 1 - 1))) =
                   (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrplusminus i 1))
                               (Diff C1 i ;; homot (i + 1))) ;; (MMor g i)).
      {
        induction (hzrplusminus i 1). apply idpath.
      }
      cbn in e1. rewrite e1. clear e1.
      rewrite <- to_postmor_linear'. apply idpath.
  Qed.


  (** ** Naive homotopy category
     We know that the homotopies from C1 to C2 form an abelian subgroup of the abelian group of all
     morphisms from C1 to C2, by [ComplexHomotSubgrp]. We also know that composition of a morphism
     with a morphism coming from a homotopy, is a morphism which comes from a homotopy, by
     [ComplexHomotSubgrop_comp_left] and [ComplexHomotSubgrop_comp_right]. This is enough to
     invoke our abstract construction QuotPrecategory_Additive, to construct the naive homotopy
     category. *)
  Local Lemma ComplexHomot_Additive_Comp :
    PreAdditiveComps (ComplexPreCat_Additive A)
                     (λ C1 C2 : ComplexPreCat_Additive A, ComplexHomotSubgrp C1 C2).
  Proof.
    intros C1 C2. split.
    - intros C3 f H g.
      apply ComplexHomotSubgrop_comp_right. apply H.
    - intros C3 f g H.
      apply ComplexHomotSubgrop_comp_left. apply H.
  Qed.

  (** Here we construct K(A). *)
  Definition ComplexHomot_Additive : Additive.
  Proof.
    use QuotPrecategory_Additive.
    - exact (ComplexPreCat_Additive A).
    - intros C1 C2. exact (ComplexHomotSubgrp C1 C2).
    - exact (ComplexHomot_Additive_Comp).
  Defined.

  Lemma has_homsets_ComplexHomot_Additive : has_homsets ComplexHomot_Additive.
  Proof.
    apply to_has_homsets.
  Qed.

  Lemma ComplexHomot_Mor_issurj {c d : ComplexHomot_Additive} (f : ComplexHomot_Additive⟦c, d⟧) :
    ∥ hfiber (setquotpr (binopeqrel_subgr_eqrel (ComplexHomotSubgrp c d))) f ∥.
  Proof.
    use issurjsetquotpr.
  Qed.

  Definition ComplexHomotFunctor : AdditiveFunctor (ComplexPreCat_Additive A) ComplexHomot_Additive.
  Proof.
    apply QuotPrecategoryAdditiveFunctor.
  Defined.

  Lemma ComplexHomotFunctor_issurj {C1 C2 : ComplexPreCat_Additive A} (f : ComplexHomot_Additive⟦C1, C2⟧) :
    ∥ hfiber (# ComplexHomotFunctor) f ∥.
  Proof.
    apply ComplexHomot_Mor_issurj.
  Qed.

End complexes_homotopies.


(** * Translation funtor for C(A) and for K(A) *)
(** ** Introduction
   We define the translation functor T : C(A) -> C(A), which sends a complex (i ↦ X^i) to
   (i ↦ X^{i+1}). On morphisms, T maps f to -f.
*)
Section translation_functor.

  Variable A : Additive.

  Local Lemma TranslationFunctor_comp (C : Complex A) (i : hz) :
    (to_inv (C (i + 1)) (C (i + 1 + 1)) (Diff C (i + 1)))
      ;; (to_inv (C (i + 1 + 1)) (C (i + 1 + 1 + 1)) (Diff C (i + 1 + 1))) =
  ZeroArrow (Additive.to_Zero A) (C (i + 1)) (C (i + 1 + 1 + 1)).
  Proof.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite inv_inv_eq. apply (CEq A C (i + 1)).
  Qed.

  Local Lemma TranslationFunctor_comm (C1 C2 : Complex A) (f : Morphism C1 C2) (i : hz) :
    MMor f (i + 1) ;; to_inv (C2 (i + 1)) (C2 (i + 1 + 1)) (Diff C2 (i + 1)) =
    to_inv (C1 (i + 1)) (C1 (i + 1 + 1)) (Diff C1 (i + 1)) ;; MMor f (i + 1 + 1).
  Proof.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    apply maponpaths. apply (MComm f (i + 1)).
  Qed.

  (* Why Defined. does not terminate? *)
  Definition TranslationFunctor_data :
    functor_data (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use tpair.
    - cbn. intros C.
      use mk_Complex.
      + intros i. exact (C (i + 1)).
      + intros i. exact (to_inv (C (i + 1)) (C (i + 1 + 1)) (Diff C (i + 1))).
      + intros i. exact (TranslationFunctor_comp C i).
    - cbn. intros C1 C2 f.
      use mk_Morphism.
      + intros i. cbn. exact (MMor f (i + 1)).
      + intros i. cbn. exact (TranslationFunctor_comm C1 C2 f i).
        (* Show Proof. This shows the proof term as explained in 7.3.1.3 of reference manual.
                       The proof term looks ok to me.  *)
  Abort. (* Defined. *)

  (* This is ok *)
  Local Definition test_complex (C : Complex A) : Complex A :=
    mk_Complex A (λ i : hz, C (i + 1))
               (λ i : hz, to_inv (C (i + 1)) (C (i + 1 + 1)) (Diff C (i + 1)))
               (λ i : hz, TranslationFunctor_comp C i).

  (* This hangs *)
  (* Definition test_morphism (C1 C2 : Complex A) (f : Morphism C1 C2) : Morphism C1 C2 :=
    mk_Morphism
      A
      (mk_Complex A (λ i : pr1 hz, C1 (i + 1))
                  (λ i : pr1 hz, to_inv (C1 (i + 1)) (C1 (i + 1 + 1)) (Diff C1 (i + 1)))
                  (λ i : pr1 hz, TranslationFunctor_comp C1 i))
      (mk_Complex A (λ i : pr1 hz, C2 (i + 1))
                  (λ i : pr1 hz, to_inv (C2 (i + 1)) (C2 (i + 1 + 1)) (Diff C2 (i + 1)))
                  (λ i : pr1 hz, TranslationFunctor_comp C2 i)) (λ i : hz, MMor f (i + 1))
      (λ i : hz, TranslationFunctor_comm C1 C2 f i). *)

  (* These hang too *)
  (*
  Lemma test_conv (C : Complex A) (i : hz) :
    Diff (test_complex C) i = to_inv (C (i + 1)) (C (i + 1 + 1)) (Diff C (i + 1)).

  Lemma test_conv' (C : Complex A) (i : hz) :
    to_inv (C (i + 1)) (C (i + 1 + 1)) (Diff C (i + 1)) = Diff (test_complex C) i.
   *)

End translation_functor.

Local Transparent hz isdecrelhzeq hzplus iscommrngops.
Close Scope hz_scope.
