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
  - Translation functor C(A) -> C(A)
  - Translation functor K(A) -> K(A)
 - Mapping cone
 - Mapping cylinder
 - Let f : X -> Y be a morphism of complexes, then Y is isomorphic to Cyl(f) in K(A)
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

Require Import UniMath.CategoryTheory.precategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.
Require Import UniMath.CategoryTheory.AdditiveFunctors.


Unset Kernel Term Sharing.

Open Scope hz_scope.
Local Opaque hz isdecrelhzeq hzplus iscommrngops ZeroArrow.

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
    Σ D' : (Σ D : (Π i : hz, ob A), (Π i : hz, A⟦D i, D (i + 1)⟧)),
           Π i : hz, (pr2 D' i) ;; (pr2 D' (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.

  Definition mk_Complex (D : Π i : hz, ob A) (D' : Π i : hz, A⟦D i, D (i + 1)⟧)
             (D'' : Π i : hz, (D' i) ;; (D' (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _) :
    Complex := ((D,,D'),,D'').

  (** Accessor functions *)
  Definition Complex_Funclass (C : Complex) : hz -> ob A := pr1 (pr1 C).
  Coercion Complex_Funclass : Complex >-> Funclass.

  Definition Diff (C : Complex) (i : hz) : A⟦C i, C (i + 1)⟧ := pr2 (pr1 C) i.

  Definition DSq (C : Complex) (i : hz) :
    (Diff C i) ;; (Diff C (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _ := pr2 C i.

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
    rewrite (DSq C1 i). rewrite ZeroArrow_comp_right.
    rewrite (DSq C2 i). rewrite ZeroArrow_comp_right.
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
  Definition MMor {C1 C2 : Complex} (M : Morphism C1 C2) (i : hz) : A⟦C1 i, C2 i⟧ := pr1 M i.
  Coercion MMor : Morphism >-> Funclass.

  Definition MComm {C1 C2 : Complex} (M : Morphism C1 C2) (i : hz) :
    (M i) ;; (Diff C2 i) = (Diff C1 i) ;; (M (i + 1)) := pr2 M i.

  (** A lemma to show that two morphisms are the same *)
  Lemma MorphismEq {C1 C2 : Complex} (M1 M2 : Morphism C1 C2) (H : Π i : hz, M1 i = M2 i) : M1 = M2.
  Proof.
    use total2_paths.
    - use funextsec. intros i. exact (H i).
    - use proofirrelevance. apply impred_isaprop. intros t. apply to_has_homsets.
  Qed.

  Lemma MorphismEq' {C1 C2 : Complex} (M1 M2 : Morphism C1 C2) (H : M1 = M2) :
    Π i : hz, M1 i = M2 i.
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
        (i : hz) : (M1 i) ;; (M2 i) ;; (Diff C3 i) = (Diff C1 i) ;; (M1 (i + 1) ;; M2 (i + 1)).
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
    - intros i. exact ((M1 i) ;; (M2 i)).
    - intros i. exact (MorphismCompComm M1 M2 i).
  Defined.

  (** ZeroMorphism as the composite of to zero and from zero *)
  Local Lemma ZeroMorphism_comm (C1 C2 : Complex) (i : hz) :
    ZeroArrow (Additive.to_Zero A) (C1 i) (C2 i) ;; Diff C2 i =
    Diff C1 i ;; ZeroArrow (Additive.to_Zero A) (C1 (i + 1)) (C2 (i + 1)).
  Proof.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Definition ZeroMorphism (C1 C2 : Complex) : Morphism C1 C2.
  Proof.
    use mk_Morphism.
    - intros i. exact (ZeroArrow (Additive.to_Zero A) _ _).
    - intros i. exact (ZeroMorphism_comm C1 C2 i).
  Defined.

  Lemma ZeroMorphism_eq (C1 C2 : Complex) :
    ZeroMorphism C1 C2 = MorphismComp (MorphismToZero C1) (MorphismFromZero C2).
  Proof.
    use MorphismEq. intros i. apply pathsinv0. apply ZeroArrowEq.
  Qed.

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
    MorphismComp (DirectSumComplexIn1 C1 C2) (DirectSumComplexPr2 C1 C2) = ZeroMorphism C1 C2.
  Proof.
    use MorphismEq.
    intros i. cbn.
    set (B := to_BinDirectSums A (C1 i) (C2 i)).
    rewrite (to_Unel1 A B).
    apply PreAdditive_unel_zero.
  Qed.

  Lemma DirectSumUnit2 (C1 C2 : Complex) :
    MorphismComp (DirectSumComplexIn2 C1 C2) (DirectSumComplexPr1 C1 C2) = ZeroMorphism C2 C1.
  Proof.
    use MorphismEq.
    intros i. cbn.
    set (B := to_BinDirectSums A (C1 i) (C2 i)).
    rewrite (to_Unel2 A B).
    apply PreAdditive_unel_zero.
  Qed.

  (** Additition of morphisms is pointwise addition *)
  Local Lemma MorphismOpComm {C1 C2 : Complex} (M1 M2 : Morphism C1 C2)  (i : hz) :
    (to_binop (C1 i) (C2 i) (M1 i) (M2 i)) ;; (Diff C2 i) =
    (Diff C1 i) ;; (to_binop (C1 (i + 1)) (C2 (i + 1)) (M1 (i + 1)) (M2 (i + 1))).
  Proof.
    rewrite to_postmor_linear'. rewrite to_premor_linear'.
    rewrite (MComm M1 i). rewrite (MComm M2 i). apply idpath.
  Qed.

  Definition MorphismOp {C1 C2 : Complex} (M1 M2 : Morphism C1 C2) : Morphism C1 C2.
  Proof.
    use mk_Morphism.
    - intros i. exact (to_binop _ _ (M1 i) (M2 i)).
    - intros i. exact (MorphismOpComm M1 M2 i).
  Defined.

  Lemma MorphismOp_isassoc (C1 C2 : Complex) : @isassoc (Morphisms_hSet C1 C2) MorphismOp.
  Proof.
    intros M1 M2 M3.
    use MorphismEq.
    intros i. cbn.
    apply (assocax (to_abgrop (C1 i) (C2 i))).
  Qed.

  Lemma MorphismOp_isunit (C1 C2 : Complex) :
    @isunit (Morphisms_hSet C1 C2) MorphismOp (ZeroMorphism C1 C2).
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
    (to_inv (M i)) ;; (Diff C2 i) = (Diff C1 i) ;; (to_inv (M (i + 1))).
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
    - intros i. exact (to_inv (M i)).
    - intros i. exact (MorphismOp_inv_comm M i).
  Defined.

  Lemma MorphismOp_isinv (C1 C2 : Complex) :
    @isinv (Morphisms_hSet C1 C2) MorphismOp (ZeroMorphism C1 C2) MorphismOp_inv.
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
          -- exact (ZeroMorphism C1 C2).
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
    (FromBinDirectSum A B1 (f i) (g i)) ;; (Diff D i) =
    (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2)
      ;; (FromBinDirectSum A B2 (f (i + 1)) (g (i + 1))).
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
    - intros i. exact (FromBinDirectSum A _ (f i) (g i)).
    - intros i. exact (DirectSumMorOut_comm f g i).
  Defined.

  Local Lemma DirectSumMorIn_comm {C1 C2 D : Complex} (f : Morphism D C1) (g : Morphism D C2)
        (i : hz) :
    let B1 := to_BinDirectSums A (C1 i) (C2 i) in
    let B2 := to_BinDirectSums A (C1 (i + 1)) (C2 (i + 1)) in
    (ToBinDirectSum A B1 (f i) (g i))
      ;; (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) =
    (Diff D i) ;; (ToBinDirectSum A B2 (f (i + 1)) (g (i + 1))).
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
    - intros i. exact (ToBinDirectSum A _ (f i) (g i)).
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
           ++ rewrite <- assoc. rewrite (DSq C i). rewrite ZeroArrow_comp_left.
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
    FromComplex2FromObject_mors g i0 = (FromComplex2FromObject g) i0.
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
             apply cancel_postcomposition. rewrite e''. apply (! (DSq C i0)).
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
    ToComplex2FromObject_mors g i0 = (ToComplex2FromObject g) i0.
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

  Definition ComplexPreCat_precategoryWithBinOps : precategoryWithBinOps.
  Proof.
    use mk_precategoryWithBinOps.
    - exact (ComplexPreCat A).
    - intros x y. exact (MorphismOp A).
  Defined.

  Definition ComplexPreCat_PrecategoryWithAbgrops : PrecategoryWithAbgrops.
  Proof.
    use mk_PrecategoryWithAbgrops.
    - exact ComplexPreCat_precategoryWithBinOps.
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
  Defined.
  Opaque ComplexPreCat_isZero.

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
    - cbn. rewrite (DirectSumUnit1 A C1 C2). apply idpath.
    - cbn. rewrite (DirectSumUnit2 A C1 C2). apply idpath.
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

  Local Transparent ZeroArrow.
  Lemma ComplexPreCat_ZeroArrow_ZeroMorphism (C1 C2 : ob ComplexPreCat_Additive) :
    ZeroMorphism A C1 C2 = ZeroArrow (Additive.to_Zero ComplexPreCat_Additive)  _ _.
  Proof.
    use MorphismEq.
    - intros i. cbn. apply pathsinv0. apply ZeroArrowEq.
  Qed.
  Local Opaque ZeroArrow.

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
        (i : hz) : (KernelArrow (Kernel (g i))) ;; (Diff Y i) ;; (g (i + 1)) =
                   ZeroArrow (@to_Zero A) (Kernel (g i)) (Z (i + 1)).
  Proof.
    rewrite <- assoc. cbn. set (tmp := MComm g i). cbn in tmp. rewrite <- tmp. clear tmp.
    rewrite assoc. rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Local Lemma ComplexPreCat_Kernel_comp {Y Z : Complex (AbelianToAdditive A hs)} (g : Morphism Y Z)
        (i : hz) :
    (KernelIn (@to_Zero A) (Kernel (g (i + 1))) (Kernel (g i))
              ((KernelArrow (Kernel (g i))) ;; (Diff Y i))
              (ComplexPreCat_Kernel_moreq g i))
      ;; (KernelIn (@to_Zero A) (Kernel (g (i + 1 + 1))) (Kernel (g (i + 1)))
                   ((KernelArrow (Kernel (g (i + 1)))) ;; (Diff Y (i + 1)))
                   (ComplexPreCat_Kernel_moreq g (i + 1))) =
    ZeroArrow (@to_Zero A) (Kernel (g i)) (Kernel (g (i + 1 + 1))).
  Proof.
    apply KernelArrowisMonic. rewrite ZeroArrow_comp_left.
    rewrite <- assoc. rewrite KernelCommutes. rewrite assoc. rewrite KernelCommutes.
    rewrite <- assoc. set (tmp := DSq _ Y i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Definition ComplexPreCat_Kernel {Y Z : Complex (AbelianToAdditive A hs)} (g : Morphism Y Z) :
    ComplexPreCat (AbelianToAdditive A hs).
  Proof.
    use mk_Complex.
    - intros i. exact (Kernel (g i)).
    - intros i. cbn. use KernelIn.
      + exact (KernelArrow (Kernel (g i)) ;; Diff Y i).
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
    (h i) ;; (g i) = ZeroArrow to_Zero (w i) (Y i).
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
      + exact (h i).
      + apply (ComplexPreCat_KernelIn_comp g h i H).
    - intros i. cbn.
      apply KernelArrowisMonic.
      rewrite <- assoc. rewrite <- assoc. rewrite KernelCommutes. rewrite KernelCommutes.
      rewrite assoc. rewrite KernelCommutes.
      apply (MComm h i).
  Defined.

  Local Lemma ComplexPreCat_Kernels_isKernel {X Y : Complex (AbelianToAdditive A hs)}
        (g : Morphism X Y) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    @isKernel (ComplexPreCat (AbelianToAdditive A hs)) _ _ _ _
              (ComplexPreCat_KernelArrow g) g (ComplexPreCat_Kernels_comp g).
  Proof.
    intros Z.
    use (mk_isKernel (has_homsets_ComplexPreCat (AbelianToAdditive A hs))).
    intros w h H'.
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
    - exact (ComplexPreCat_Kernels_isKernel f).
  Defined.


  (** ** Cokernels in Complexes over Abelian *)

  (** *** Cokernel complex *)
  Local Lemma ComplexPreCat_Cokernel_comm {Y Z : Complex (AbelianToAdditive A hs)}
        (g : Morphism Y Z) (i : hz) :
    (g i) ;; ((Diff Z i) ;; (CokernelArrow (Cokernel (g (i + 1))))) =
    ZeroArrow (@to_Zero A) (Y i) (Cokernel (g (i + 1))).
  Proof.
    rewrite assoc. cbn. set (tmp := MComm g i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Local Lemma ComplexPreCat_Cokernel_comp {Y Z : Complex (AbelianToAdditive A hs)}
        (g : Morphism Y Z) (i : hz) :
    (CokernelOut (@to_Zero A) (Cokernel (g i)) (Cokernel (g (i + 1)))
                 ((Diff Z i) ;; (CokernelArrow (Cokernel (g (i + 1)))))
                 (ComplexPreCat_Cokernel_comm g i))
      ;; (CokernelOut (@to_Zero A) (Cokernel (g (i + 1))) (Cokernel (g (i + 1 + 1)))
                      ((Diff Z (i + 1)) ;; (CokernelArrow (Cokernel (g (i + 1 + 1)))))
                      (ComplexPreCat_Cokernel_comm g (i + 1))) =
    ZeroArrow (@to_Zero A) (Cokernel (g i)) (Cokernel (g (i + 1 + 1))).
  Proof.
    apply CokernelArrowisEpi. rewrite ZeroArrow_comp_right.
    rewrite assoc. rewrite CokernelCommutes. rewrite <- assoc. rewrite CokernelCommutes.
    rewrite assoc. set (tmp := DSq _ Z i). cbn in tmp. cbn. rewrite tmp. clear tmp.
    rewrite ZeroArrow_comp_left. apply idpath.
  Qed.

  Definition ComplexPreCat_Cokernel {Y Z : Complex (AbelianToAdditive A hs)} (g : Morphism Y Z) :
    ComplexPreCat (AbelianToAdditive A hs).
  Proof.
    use mk_Complex.
    - intros i. exact (Cokernel (g i)).
    - intros i. cbn. use CokernelOut.
      + exact ((Diff Z i) ;; (CokernelArrow (Cokernel (g (i + 1))))).
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
    g ;; h = ZeroArrow Z0 Y w -> (MMor g i) ;; (MMor h i) = ZeroArrow (@to_Zero A) (Y i) (w i).
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

  Local Lemma ComplexPreCat_Cokernels_isCokernel {Y Z : Complex (AbelianToAdditive A hs)}
        (g : (ComplexPreCat (AbelianToAdditive A hs))⟦Y, Z⟧) :
    let Z0 := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    isCokernel _ g (ComplexPreCat_CokernelArrow g) (ComplexPreCat_Cokernels_Comp g).
  Proof.
    intros Z0.
    use (mk_isCokernel (has_homsets_ComplexPreCat (AbelianToAdditive A hs))).
    intros w h H'.
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
    - exact (ComplexPreCat_Cokernels_isCokernel g).
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
    cbn. set (tmp := DSq _ y i). cbn in tmp. rewrite tmp. clear tmp.
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
    MorphismComp (MonicArrow _ M) (KernelMorphism M) = ZeroMorphism _ _ _.
  Proof.
    intros Z.
    use MorphismEq.
    intros i. cbn. rewrite CokernelCompZero. apply idpath.
  Qed.

  Local Lemma ComplexMonicKernelInComm {x y : Complex (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
        {w : ComplexPreCat (AbelianToAdditive A hs)}
        (h : (ComplexPreCat (AbelianToAdditive A hs))⟦w, y⟧)
        (H : let Z := @Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
             h ;; (KernelMorphism M) = ZeroArrow Z _ _)
        (i : hz) :
    (MMor h i) ;; (CokernelArrow (Cokernel (MMor (MonicArrow _ M) i))) =
    ZeroArrow (@to_Zero A) _ (Cokernel (MMor (MonicArrow _ M) i)).
  Proof.
    set (H' := MorphismEq' _ _ _ H i). cbn in H'. cbn. rewrite H'.
    apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexMonicKernelIn_Complex_Comm {x y w : Complex (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
        (h : (ComplexPreCat (AbelianToAdditive A hs))⟦w, y⟧) (i : hz)
        (H : let Z := @Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
             h ;; KernelMorphism M = ZeroArrow Z _ _) :
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
    h ;; (KernelMorphism M) = ZeroArrow Z _ _  ->
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

  Local Lemma KernelMorphism_eq' {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    M ;; KernelMorphism M = ZeroArrow Z x (ComplexPreCat_Monic_Kernel_Complex M).
  Proof.
    intros Z. cbn. rewrite KernelMorphism_eq. apply ComplexPreCat_ZeroArrow_ZeroMorphism.
  Qed.

  Definition ComplexPreCatAbelianMonicKernelsData_isKernel
             {x y : Complex (AbelianToAdditive A hs)}
             (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    @isKernel (ComplexPreCat (AbelianToAdditive A hs)) _ _ _ _ M (KernelMorphism M)
              (KernelMorphism_eq' M).
  Proof.
    intros Z.
    set (isM := ComplexMonicIndexMonic _ M).
    use (mk_isKernel (has_homsets_ComplexPreCat (AbelianToAdditive A hs))).
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
    intros Add.
    use mk_AbelianMonicKernelsData.
    intros x y M.
    set (isM := ComplexMonicIndexMonic _ M).
    use tpair.
    - use tpair.
      + use tpair.
        * exact (ComplexPreCat_Monic_Kernel_Complex M).
        * exact (KernelMorphism M).
      + cbn. exact (KernelMorphism_eq' M).
    - exact (ComplexPreCatAbelianMonicKernelsData_isKernel M).
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
    cbn. set (tmp := DSq _ x i). cbn in tmp. rewrite tmp. clear tmp.
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
    MorphismComp (CokernelMorphism E) (EpiArrow _ E) = ZeroMorphism _ _ _.
  Proof.
    use MorphismEq.
    intros i. cbn. rewrite KernelCompZero. apply idpath.
  Qed.

  Local Lemma ComplexPreCatCokernelOut_comp
    {x y w0 : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y)
    (h : (ComplexPreCat (AbelianToAdditive A hs))⟦x, w0⟧)
    (H : let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
         ZeroArrow Z _ _  = MorphismComp (@CokernelMorphism x y E) h) (i : hz) :
    KernelArrow (Kernel (MMor (EpiArrow _ E) i)) ;; MMor h i =
    ZeroArrow (@to_Zero A) (Kernel (MMor (EpiArrow _ E) i)) _.
  Proof.
    set (H' := MorphismEq' _ _ _ H i). cbn in H'. cbn. rewrite <- H'.
    apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexPreCatCokernelOut_comm
    {x y w0 : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y) (i : hz)
    (h : (ComplexPreCat (AbelianToAdditive A hs))⟦x, w0⟧)
    (H : let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
         ZeroArrow Z _ _ = MorphismComp (@CokernelMorphism x y E) h) :
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
         ZeroArrow Z _ _  = MorphismComp (@CokernelMorphism x y E) h) :
    (ComplexPreCat (AbelianToAdditive A hs))⟦y, z⟧.
  Proof.
    cbn in H.
    set (isE := ComplexEpiIndexEpi _ E).
    use mk_Morphism.
    - intros i. exact (CokernelOut
                         (@to_Zero A) (EpiToCokernel A hs (mk_Epi _ _ (isE i))) _ (MMor h i)
                         (ComplexPreCatCokernelOut_comp E h H i)).
    - intros i. exact (ComplexPreCatCokernelOut_comm E i h H).
  Defined.

  (** *** EpisCokernelsData *)

  Local Lemma CokernelMorphism_eq' {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    (CokernelMorphism E : (ComplexPreCat (AbelianToAdditive A hs))⟦_, _⟧) ;; E =
    ZeroArrow Z (ComplexPreCat_Epi_Cokernel_Complex E) y.
  Proof.
    intros Z. cbn. rewrite CokernelMorphism_eq. apply ComplexPreCat_ZeroArrow_ZeroMorphism.
  Qed.

  Local Lemma ComplexPreCatAbelianEpiCokernelsData_isCoequalizer
        {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) :
    let Add := ComplexPreCat_Additive (AbelianToAdditive A hs) in
    @isCokernel Add _ _ _ _ (CokernelMorphism E) E (CokernelMorphism_eq' E).
  Proof.
    intros Add.
    set (isE := ComplexEpiIndexEpi (AbelianToAdditive A hs) E).
    use (mk_isCokernel (has_homsets_ComplexPreCat (AbelianToAdditive A hs))).
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
      + exact (CokernelMorphism_eq' E).
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

Section transport_section'.

  Variable C : precategory.

  Lemma transport_mor_b_f (f : hz -> ob C) (n : hz) (H : Π (i : hz), C⟦f i, f (i + n)⟧) (i i' : hz)
        (e1 : i = i') :
    H i' = transportb (fun (x : ob C) => C⟦x, f (i' + n)⟧) (maponpaths f (! e1))
                      (transportf (precategory_morphisms (f i))
                                  (maponpaths f (hzplusradd i i' n e1)) (H i)).
  Proof.
    induction e1. apply idpath.
  Qed.

  Lemma transport_mor_f_b (f : hz -> ob C) (n : hz) (H : Π (i : hz), C⟦f i, f (i + n)⟧) (i i' : hz)
        (e1 : i = i') :
    H i' = transportf (precategory_morphisms (f i'))
                      (maponpaths f (hzplusradd i i' n e1))
                      (transportb (fun (x : ob C) => C⟦x, f (i + n)⟧) (maponpaths f (! e1)) (H i)).
  Proof.
    induction e1. apply idpath.
  Qed.

  Lemma transport_section' (f : hz -> ob C) (n : hz) (H : Π (i : hz), C⟦f i, f (i + n)⟧) (i i' : hz)
    (e1 : i = i') :
    transportf (precategory_morphisms (f i)) (maponpaths f (hzplusradd i i' n e1)) (H i) =
    transportb (fun (x : ob C) => C⟦x, f (i' + n)⟧) (maponpaths f e1) (H i').
  Proof.
    induction e1. apply idpath.
  Qed.

  Lemma transport_section'' (f : hz -> ob C) (n : hz) (H : Π (i : hz), C⟦f (i + n), f i⟧) (i i' : hz)
    (e1 : i + n = i' + n) (e2 : i = i') :
    transportf (precategory_morphisms (f (i + n))) (maponpaths f e2) (H i) =
    transportb (fun (x : ob C) => C⟦x, f i'⟧) (maponpaths f e1) (H i').
  Proof.
    induction e2. assert (e : e1 = idpath _) by apply isasethz. rewrite e. clear e. apply idpath.
  Qed.

  Lemma transport_double_section (f f' : hz -> ob C) (H : Π (i : hz), C⟦f i, f' i⟧)
        (i i' : hz) (e : i = i') :
    transportf (precategory_morphisms (f i)) (maponpaths f' e) (H i) =
    transportb (fun (x : ob C) => C⟦x, f' i'⟧) (maponpaths f e) (H i').
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_double_section_f_b (f f' : hz -> ob C) (H : Π (i : hz), C⟦f i, f' i⟧)
        (i i' : hz) (e : i = i') :
    H i' = transportf (precategory_morphisms (f i')) (maponpaths f' e)
                      (transportb (fun (x : ob C) => C⟦x, f' i⟧) (maponpaths f (! e)) (H i)).
  Proof.
    induction e. apply idpath.
  Qed.

End transport_section'.


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
      rewrite (@DSq A C2 (i - 1)). apply ZeroArrow_comp_right.
    }
    rewrite e0. clear e0.
    assert (e1 : (Diff C1 i ;; transportf (precategory_morphisms (C1 (i + 1)))
                       (maponpaths C2 (hzrplusminus (i + 1) 1)) (Diff C1 (i + 1) ;; H (i + 1 + 1)))
                 = ZeroArrow (Additive.to_Zero A) _ _).
    {
      rewrite <- transportf_postcompose. rewrite assoc. rewrite (@DSq A C1 i).
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
                     to_inv (transportf (precategory_morphisms (C1 i))
                                        (maponpaths C2 (hzrplusminus i 1))
                                        (Diff C1 i ;; homot (i + 1)))).
        {
          unfold to_inv. cbn. induction (hzrplusminus i 1). apply idpath.
        }
        cbn in e0. rewrite e0. clear e0.
        assert (e1 : (transportf (precategory_morphisms (C1 i)) (maponpaths C2 (hzrminusplus i 1))
                                 (grinv (to_abgrop (C1 i) (C2 (i - 1)))
                                        (homot i) ;; Diff C2 (i - 1))) =
                     to_inv (transportf (precategory_morphisms (C1 i))
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

  Lemma ComplexHomotFunctor_issurj {C1 C2 : ComplexPreCat_Additive A}
        (f : ComplexHomot_Additive⟦C1, C2⟧) : ∥ hfiber (# ComplexHomotFunctor) f ∥.
  Proof.
    apply ComplexHomot_Mor_issurj.
  Qed.

  Lemma ComplexHomotFunctor_rel_mor {C1 C2 : ComplexPreCat_Additive A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : subgrhrel (ComplexHomotSubgrp C1 C2) f g) :
    # ComplexHomotFunctor f = # ComplexHomotFunctor g.
  Proof.
    apply abgrquotpr_rel_image. apply H.
  Qed.

  Lemma ComplexHomotFunctor_rel_mor' {C1 C2 : ComplexPreCat_Additive A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : ComplexHomot C1 C2)
        (H' : to_binop _ _ f (to_inv g) = ComplexHomotMorphism H) :
    # ComplexHomotFunctor f = # ComplexHomotFunctor g.
  Proof.
    apply ComplexHomotFunctor_rel_mor.
    intros P X. apply X. clear X P. use tpair.
    - cbn. use tpair.
      + exact (ComplexHomotMorphism H).
      + intros P X. apply X. clear P X. use tpair.
        * exact H.
        * apply idpath.
    - cbn. apply pathsinv0. apply H'.
  Qed.

  Lemma ComplexHomotFunctor_mor_rel {C1 C2 : ComplexPreCat_Additive A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (H : # ComplexHomotFunctor f = # ComplexHomotFunctor g) :
    subgrhrel (ComplexHomotSubgrp C1 C2) f g.
  Proof.
    use (@abgrquotpr_rel_paths _ (binopeqrel_subgr_eqrel (ComplexHomotSubgrp C1 C2))).
    apply H.
  Qed.

End complexes_homotopies.


(** * Translation funtor for C(A) and for K(A) *)
(** ** Introduction
We define the translation functor T : C(A) -> C(A) for complexes, and a translation functor
T' : K(A) -> K(A). The functor T' is constructed so that we have the following commutative
diagram
                            C(A) ---T---> C(A)
                             |             |
                            K(A) ---T'--> K(A)
Here the vertical functors are given by [ComplexHomotFunctor]. The functor T sends a complex
      # ... -> X^{i-1} --(d^{i-1})--> X^i --(d^i)--> X^{i+1} -> ... #
      $ ... -> X^{i-1} --(d^{i-1})--> X^i --(d^i)--> X^{i+1} -> ... $
to the complex
      # ... -> X^i --(-d^i)--> X^{i+1} --(-d^{i+1})--> X^{i+2} -> ... #
      $ ... -> X^i --(-d^i)--> X^{i+1} --(-d^{i+1})--> X^{i+2} -> ... $
More precicely, on objects # X^i ↦ X^{i+1} # $ X^i ↦ X^{i+1} $ and differentials
# d^i_X ↦ -d^{i+1}_X # $ d^i_X ↦ -d^{i+1}_X $. A morphism f : X -> Y is mapped by
# f^i ↦ f^{i+1} # $ f^i ↦ f^{i+1} $. We also construct the inverse translation T^{-1} which is the
unique functor such that T ∘ T^{-1} = id and T^{-1} ∘ T = id (This has not been proven yet!).
All the functors T, T^{-1}, and T' are additive.

The functor T : C(A) -> C(A) is constructed in [TranslationFunctor]. It is shown to be additive in
[TranslationFunctor_Additive]. In [TranslationFunctorPreservesHomotopies] we show that T preserves
homotopies, that is if f is homotopic to g, then T(f) is homotopic to T(g). In
[InvTranslationFunctor] we construct T^{-1}.
*)
Section translation_functor.

  Variable A : Additive.


  (** ** Translation functor for C(A) *)

  Local Lemma TranslationFunctor_comp (C : Complex A) (i : hz) :
    (to_inv (Diff C (i + 1))) ;; (to_inv (Diff C (i + 1 + 1))) =
    ZeroArrow (Additive.to_Zero A) (C (i + 1)) (C (i + 1 + 1 + 1)).
  Proof.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite inv_inv_eq. apply (DSq A C (i + 1)).
  Qed.

  Definition TranslationComplex (C : Complex A) : Complex A.
  Proof.
    use mk_Complex.
    - intros i. exact (C (i + 1)).
    - intros i. exact (to_inv (Diff C (i + 1))).
    - intros i. exact (TranslationFunctor_comp C i).
  Defined.

  Definition pr11_TranslationComplex (C : Complex A) := pr1( pr1(TranslationComplex C)).
  Definition DiffTranslationComplex (C : Complex A) (i : hz) :
    A⟦ pr11_TranslationComplex C i, pr11_TranslationComplex C (i + 1) ⟧ := to_inv (Diff C (i + 1)).

  Lemma DiffTranslationComplex_comp (C : Complex A) (i : hz) :
    (DiffTranslationComplex C i) ;; (DiffTranslationComplex C (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    exact (TranslationFunctor_comp C i).
  Qed.

  Definition TranslationMorphism_mor {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    A⟦pr11_TranslationComplex C1 i, pr11_TranslationComplex C2 i⟧ := f (i + 1).

  Local Lemma TranslationFunctor_comm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (TranslationMorphism_mor f i) ;; (DiffTranslationComplex C2 i) =
    (DiffTranslationComplex C1 i) ;; (TranslationMorphism_mor f (i + 1)).
  Proof.
    unfold DiffTranslationComplex.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    apply maponpaths. apply (MComm f (i + 1)).
  Qed.

  Definition TranslationMorphism (C1 C2 : Complex A) (f : Morphism C1 C2) :
    Morphism (TranslationComplex C1) (TranslationComplex C2) :=
    mk_Morphism
      A (TranslationComplex C1) (TranslationComplex C2)
      (λ i : hz, TranslationMorphism_mor f i) (λ i : hz, TranslationFunctor_comm f i).

  Definition TranslationFunctor_data :
    functor_data (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_functor_data.
    - intros C. exact (TranslationComplex C).
    - intros C1 C2 f. exact (TranslationMorphism C1 C2 f).
  Defined.

  Lemma TranslationFunctor_isfunctor : is_functor TranslationFunctor_data.
  Proof.
    split.
    - intros C. cbn. use MorphismEq. intros i. cbn. apply idpath.
    - intros C1 C2 C3 f g. cbn. use MorphismEq. intros i. cbn. apply idpath.
  Qed.

  Definition TranslationFunctor :
    functor (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_functor.
    - exact TranslationFunctor_data.
    - exact TranslationFunctor_isfunctor.
  Defined.

  Definition TranslationFunctor_isAdditive : isAdditiveFunctor TranslationFunctor.
  Proof.
    use mk_isAdditiveFunctor.
    intros C1 C2.
    split.
    - intros f g. cbn. use MorphismEq. intros i. cbn. apply idpath.
    - cbn. use MorphismEq. intros i. apply idpath.
  Qed.

  Definition TranslationFunctor_Additive :
    AdditiveFunctor (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_AdditiveFunctor.
    - exact TranslationFunctor.
    - exact TranslationFunctor_isAdditive.
  Defined.

  (** *** Translation functor preserves homotopies *)
  Definition TranslationHomot {C1 C2 : Complex A} (H : ComplexHomot A C1 C2) :
    ComplexHomot A (TranslationComplex C1) (TranslationComplex C2).
  Proof.
    intros i.
    exact (transportf (precategory_morphisms (C1 (i + 1)))
                      (maponpaths C2 (hzrplusminus i 1 @ ! hzrminusplus i 1))
                      (to_inv (H (i + 1)))).
  Defined.

  Lemma TranslationFunctorHomotopies {C1 C2 : Complex A} (H : ComplexHomot A C1 C2) :
    ComplexHomotMorphism A (TranslationHomot H) =
    TranslationMorphism C1 C2 (ComplexHomotMorphism A H).
  Proof.
    unfold TranslationHomot. cbn. use MorphismEq. intros i. cbn.
    induction (hzrminusplus i 1). cbn. rewrite pathscomp0rid. cbn. unfold idfun.
    rewrite <- PreAdditive_invrcomp. rewrite <- transportf_to_inv.
    rewrite PreAdditive_invlcomp. rewrite inv_inv_eq.
    rewrite <- transportf_to_inv. rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite inv_inv_eq.
    assert (e : (maponpaths (λ i0 : pr1 hz, C2 (i0 + 1)) (hzrplusminus (i - 1 + 1) 1)) =
                (maponpaths C2 (maponpaths (fun (i0 : hz) => i0 + 1) (hzrplusminus (i - 1 + 1) 1)))).
    {
      induction (hzrplusminus (i - 1 + 1) 1). apply idpath.
    }
    cbn in e. rewrite e. clear e.
    assert (e1 : (transportf (precategory_morphisms (C1 (i - 1 + 1 + 1)))
                             (maponpaths C2 (maponpaths (λ i0 : pr1 hz, i0 + 1)
                                                        (hzrplusminus (i - 1 + 1) 1)))
                             ((Diff C1 (i - 1 + 1 + 1))
                                ;; (transportf
                                      (precategory_morphisms (C1 (i - 1 + 1 + 1 + 1)))
                                      (maponpaths C2
                                                  (hzrplusminus (i - 1 + 1 + 1) 1 @
                                                                ! hzrminusplus (i - 1 + 1 + 1) 1))
                                      (H (i - 1 + 1 + 1 + 1)))) =
                  (transportf (precategory_morphisms (C1 (i - 1 + 1 + 1)))
                              (maponpaths C2 (hzrplusminus (i - 1 + 1 + 1) 1))
                              (Diff C1 (i - 1 + 1 + 1) ;; H (i - 1 + 1 + 1 + 1))))).
    {
      rewrite transportf_postcompose. rewrite transport_f_f. rewrite <- maponpathscomp0.
      set (tmp := ((hzrplusminus (i - 1 + 1 + 1) 1
                                 @ ! hzrminusplus (i - 1 + 1 + 1) 1)
                     @ maponpaths (λ i0 : pr1 hz, i0 + 1) (hzrplusminus (i - 1 + 1) 1))).
      assert (ee : tmp = (hzrplusminus (i - 1 + 1 + 1) 1)) by apply isasethz.
      unfold tmp in ee. cbn in ee. unfold tmp. cbn. rewrite ee. clear ee. clear tmp.
      induction (hzrplusminus (i - 1 + 1 + 1) 1). cbn. unfold idfun. apply idpath.
    }
    cbn in e1. rewrite e1. clear e1. use to_lrw.

    set (tmp := @transport_mor_b_f A C2 1 (Diff C2) _ _ (hzrplusminus (i - 1 + 1) 1)).
    rewrite tmp. clear tmp. rewrite maponpathsinv0. rewrite transport_compose'.
    rewrite transportf_postcompose. apply cancel_precomposition.
    apply transportf_paths. apply maponpaths. apply isasethz.
  Qed.

  Lemma TranslationFunctorPreservesHomotopies {C1 C2 : Complex A}
        (f g : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (H : subgrhrel (ComplexHomotSubgrp A C1 C2) f g) :
    subgrhrel (ComplexHomotSubgrp A _ _) (TranslationMorphism C1 C2 f)
              (TranslationMorphism C1 C2 g).
  Proof.
    use (squash_to_prop H). apply propproperty. intros H'. clear H.
    induction H' as [H1 H2]. induction H1 as [H11 H12]. cbn in H11.
    use (squash_to_prop H12). apply propproperty. intros H. cbn in H2.
    induction H as [HH1 HH2].
    intros P X. apply X. clear X P.
    use tpair.
    - use tpair. cbn. exact (TranslationMorphism _ _ H11).
      intros P X. apply X. clear X P.
      use tpair.
      + exact (TranslationHomot HH1).
      + cbn. rewrite TranslationFunctorHomotopies. rewrite HH2. apply idpath.
    - cbn. rewrite H2.
      set (tmp := @AdditiveFunctorLinear (ComplexPreCat_Additive A) (ComplexPreCat_Additive A)
                                         TranslationFunctor_Additive C1 C2 f (to_inv g)).
      cbn in tmp.
      rewrite tmp. clear tmp. apply maponpaths.
      set (tmp := @AdditiveFunctorInv (ComplexPreCat_Additive A) (ComplexPreCat_Additive A)
                                      TranslationFunctor_Additive C1 C2 g). cbn in tmp.
      exact tmp.
  Qed.

  (** *** Inverse of the translation functor functor *)

  Local Lemma InvTranslationFunctor_comp (C : Complex A) (i : hz) :
    (transportf (precategory_morphisms (C (i - 1)))
                (maponpaths C (hzrminusplus i 1 @ ! hzrplusminus i 1))
                (to_inv (Diff C (i - 1))))
      ;; (transportf (precategory_morphisms (C (i + 1 - 1)))
                     (maponpaths C (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1))
                     (to_inv (Diff C (i + 1 - 1)))) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    induction (hzrminusplus (i + 1) 1 @ ! hzrplusminus (i + 1) 1).
    induction (hzrminusplus i 1 @ ! hzrplusminus i 1). cbn. unfold idfun.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp.
    rewrite inv_inv_eq. apply DSq.
  Qed.

  Definition InvTranslationComplex (C : Complex A) : Complex A.
  Proof.
    use mk_Complex.
    - intros i. exact (C (i - 1)).
    - intros i. exact (transportf
                         (precategory_morphisms (C (i - 1)))
                         (maponpaths C ((hzrminusplus i 1) @ (! hzrplusminus i 1)))
                         (to_inv (Diff C (i - 1)))).
    - intros i. exact (InvTranslationFunctor_comp C i).
  Defined.

  Definition pr11_InvTranslationComplex (C : Complex A) := pr1( pr1(InvTranslationComplex C)).
  Definition DiffInvTranslationComplex (C : Complex A) (i : hz) :
    A⟦ pr11_InvTranslationComplex C i, pr11_InvTranslationComplex C (i + 1) ⟧ :=
    transportf
      (precategory_morphisms (C (i - 1)))
      (maponpaths C ((hzrminusplus i 1) @ (! hzrplusminus i 1)))
      (to_inv (Diff C (i - 1))).

  Lemma DiffInvTranslationComplex_comp (C : Complex A) (i : hz) :
    (DiffInvTranslationComplex C i) ;; (DiffInvTranslationComplex C (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    exact (InvTranslationFunctor_comp C i).
  Qed.

  Definition InvTranslationMorphism_mor {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    A⟦pr11_InvTranslationComplex C1 i, pr11_InvTranslationComplex C2 i⟧ := f (i - 1).

  Local Lemma InvTranslationFunctor_comm {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (InvTranslationMorphism_mor f i) ;; (DiffInvTranslationComplex C2 i) =
    (DiffInvTranslationComplex C1 i) ;; (InvTranslationMorphism_mor f (i + 1)).
  Proof.
    unfold DiffInvTranslationComplex. rewrite <- transportf_postcompose.
    unfold InvTranslationMorphism_mor. cbn. rewrite <- PreAdditive_invrcomp.
    rewrite (MComm f (i - 1)). rewrite PreAdditive_invlcomp.
    rewrite transportf_postcompose.
    use transportf_path.
    - exact (C2 i).
    - exact (maponpaths C2 (hzrplusminus i 1)).
    - rewrite transportf_postcompose. rewrite transport_f_f. rewrite <- maponpathscomp0.
      rewrite <- path_assoc. rewrite pathsinv0l. rewrite pathscomp0rid.
      induction (hzrminusplus i 1). cbn. unfold idfun.
      rewrite transportf_postcompose.
      set (tmp := transport_double_section A C1 C2 (MMor f) _ _ (hzrplusminus (i - 1 + 1) 1)).
      cbn. cbn in tmp. rewrite tmp. clear tmp.
      rewrite <- (transport_compose' _ _ (maponpaths C1 (! hzrplusminus (i - 1 + 1) 1))).
      apply cancel_precomposition. rewrite <- maponpathsinv0. rewrite pathsinv0inv0.
      apply idpath.
  Qed.

  Definition InvTranslationMorphism (C1 C2 : Complex A) (f : Morphism C1 C2) :
    Morphism (InvTranslationComplex C1) (InvTranslationComplex C2) :=
    mk_Morphism
      A (InvTranslationComplex C1) (InvTranslationComplex C2)
      (λ i : hz, InvTranslationMorphism_mor f i) (λ i : hz, InvTranslationFunctor_comm f i).

  Definition InvTranslationFunctor_data :
    functor_data (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_functor_data.
    - intros C. exact (InvTranslationComplex C).
    - intros C1 C2 f. exact (InvTranslationMorphism C1 C2 f).
  Defined.

  Lemma InvTranslationFunctor_isfunctor : is_functor InvTranslationFunctor_data.
  Proof.
    split.
    - intros C. cbn. use MorphismEq. intros i. cbn. apply idpath.
    - intros C1 C2 C3 f g. cbn. use MorphismEq. intros i. cbn. apply idpath.
  Qed.

  Definition InvTranslationFunctor :
    functor (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_functor.
    - exact InvTranslationFunctor_data.
    - exact InvTranslationFunctor_isfunctor.
  Defined.

  Definition InvTranslationFunctor_isAdditive : isAdditiveFunctor InvTranslationFunctor.
  Proof.
    use mk_isAdditiveFunctor.
    intros C1 C2.
    split.
    - intros f g. cbn. use MorphismEq. intros i. cbn. apply idpath.
    - cbn. use MorphismEq. intros i. apply idpath.
  Qed.

  Definition InvTranslationFunctor_Additive :
    AdditiveFunctor (ComplexPreCat_Additive A) (ComplexPreCat_Additive A).
  Proof.
    use mk_AdditiveFunctor.
    - exact InvTranslationFunctor.
    - exact InvTranslationFunctor_isAdditive.
  Defined.

  (** TODO : Translation is an isomorphism with inverse the inverse translation. *)


  (** ** Translation functor for K(A) *)

  (** *** Image for the translation functor *)

  Definition TranslationFunctorHIm {C1 C2 : ComplexHomot_Additive A}
             (f : (ComplexHomot_Additive A)⟦C1, C2⟧) : UU :=
    Σ (h : (ComplexHomot_Additive A)⟦TranslationComplex C1, TranslationComplex C2⟧),
    Π (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : # (ComplexHomotFunctor A) f' = f),
    h = # (ComplexHomotFunctor A) (# TranslationFunctor f').


  Definition TranslationFunctorHImMor {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧} (h : TranslationFunctorHIm f) :
    (ComplexHomot_Additive A)⟦TranslationComplex C1, TranslationComplex C2⟧ := pr1 h.

  Definition TranslationFunctorHImEq {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧} (h : TranslationFunctorHIm f)
             (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H : # (ComplexHomotFunctor A) f' = f) :
    TranslationFunctorHImMor h = # (ComplexHomotFunctor A) (# TranslationFunctor f') := pr2 h f' H.

  Definition mk_TranslationFunctorHIm {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧}
             (h : (ComplexHomot_Additive A)⟦TranslationComplex C1, TranslationComplex C2⟧)
             (HH : Π (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧)
                     (H : # (ComplexHomotFunctor A) f' = f),
                   h = # (ComplexHomotFunctor A) (# TranslationFunctor f')) :
    TranslationFunctorHIm f := tpair _ h HH.

  Lemma TranslationFunctorHImEquality {C1 C2 : ComplexHomot_Additive A}
             {f : (ComplexHomot_Additive A)⟦C1, C2⟧} (h h' : TranslationFunctorHIm f)
             (e : TranslationFunctorHImMor h = TranslationFunctorHImMor h') : h = h'.
  Proof.
    use total2_paths.
    - exact e.
    - apply proofirrelevance. apply impred_isaprop. intros t0.
      apply impred_isaprop. intros H0. apply has_homsets_ComplexHomot_Additive.
  Qed.


  (** *** Construction of the functor *)

  Lemma TranslationFunctor_eq {C1 C2 : ComplexHomot_Additive A}
        (f : (ComplexHomot_Additive A)⟦C1, C2⟧) (H : hfiber # (ComplexHomotFunctor A) f)
        (f' : (ComplexPreCat_Additive A)⟦C1, C2⟧) (H' : # (ComplexHomotFunctor A) f' = f) :
    # (ComplexHomotFunctor A) (# TranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f H)) =
    # (ComplexHomotFunctor A) (# TranslationFunctor f').
  Proof.
    use ComplexHomotFunctor_rel_mor.
    use TranslationFunctorPreservesHomotopies.
    use ComplexHomotFunctor_mor_rel.
    rewrite H'. apply hfiberpr2.
  Qed.

  Definition TranslationFunctorH_Mor {C1 C2 : ComplexHomot_Additive A}
             (f : (ComplexHomot_Additive A)⟦C1, C2⟧) : iscontr (TranslationFunctorHIm f).
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
    apply isapropiscontr. intros H.
    use iscontrpair.
    - use mk_TranslationFunctorHIm.
      + exact (# (ComplexHomotFunctor A) (# (TranslationFunctor) (hfiberpr1 _ _ H))).
      + intros f' H'. exact (TranslationFunctor_eq f H f' H').
    - intros t. use TranslationFunctorHImEquality.
      use TranslationFunctorHImEq.
      exact (hfiberpr2 _ _ H).
  Qed.

  Definition TranslationFunctorH_data :
    functor_data (ComplexHomot_Additive A) (ComplexHomot_Additive A).
  Proof.
    use mk_functor_data.
    - intros C. exact (TranslationComplex C).
    - intros C1 C2 f. exact (TranslationFunctorHImMor (iscontrpr1 (TranslationFunctorH_Mor f))).
  Defined.

  Lemma TranslationFunctorH_Mor_Id : functor_idax TranslationFunctorH_data.
  Proof.
    intros C.
    use (pathscomp0 (TranslationFunctorHImEq
                       (iscontrpr1 (TranslationFunctorH_Mor (identity C)))
                       (identity _)
                       (functor_id (ComplexHomotFunctor A) _))).
    rewrite functor_id. rewrite functor_id. apply idpath.
  Qed.

  Lemma TranslationFunctorH_Mor_Comp {C1 C2 C3 : ComplexHomot_Additive A}
             (f : (ComplexHomot_Additive A)⟦C1, C2⟧) (g : (ComplexHomot_Additive A)⟦C2, C3⟧) :
    (TranslationFunctorHImMor (iscontrpr1 (TranslationFunctorH_Mor (f ;; g)))) =
    (TranslationFunctorHImMor (iscontrpr1 (TranslationFunctorH_Mor f)))
      ;; (TranslationFunctorHImMor (iscontrpr1 (TranslationFunctorH_Mor g))) .
  Proof.
    use (squash_to_prop (ComplexHomotFunctor_issurj A f)).
    apply has_homsets_ComplexHomot_Additive. intros f'.
    use (squash_to_prop (ComplexHomotFunctor_issurj A g)).
    apply has_homsets_ComplexHomot_Additive. intros g'.
    rewrite (TranslationFunctorHImEq (iscontrpr1 (TranslationFunctorH_Mor f)) _ (hfiberpr2 _ _ f')).
    rewrite (TranslationFunctorHImEq (iscontrpr1 (TranslationFunctorH_Mor g)) _ (hfiberpr2 _ _ g')).
    set (tmp := functor_comp (ComplexHomotFunctor A) _ _ _
                             (# TranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) f f'))
                             (# TranslationFunctor (hfiberpr1 # (ComplexHomotFunctor A) g g'))).
    use (pathscomp0 _ tmp). clear tmp.
    set (tmp := functor_comp TranslationFunctor _ _ _ (hfiberpr1 _ _ f') (hfiberpr1 _ _ g')).
    apply (maponpaths (# (ComplexHomotFunctor A))) in tmp.
    use (pathscomp0 _ tmp). clear tmp.
    use (TranslationFunctorHImEq (iscontrpr1 (TranslationFunctorH_Mor (f ;; g)))).
    rewrite functor_comp. rewrite (hfiberpr2 _ _ f'). rewrite (hfiberpr2 _ _ g'). apply idpath.
  Qed.

  Definition TranslationFunctorH_is_functor : is_functor TranslationFunctorH_data.
  Proof.
    split.
    - exact TranslationFunctorH_Mor_Id.
    - intros C1 C2 C3 f g. exact (TranslationFunctorH_Mor_Comp f g).
  Qed.

  Definition TranslationFunctorH :
    functor (ComplexHomot_Additive A) (ComplexHomot_Additive A).
  Proof.
    use mk_functor.
    - exact TranslationFunctorH_data.
    - exact TranslationFunctorH_is_functor.
  Defined.

  (* TODO : Generalize the translation functor construction! Similar code was used in
     CohomologyComplex.v to construct the cohomology functor for K(A). *)

  (* TODO : Translation inverse for K(A) *)

End translation_functor.


(** * Mapping cone *)
(** ** Introduction
In this section we construct the mapping cone, which is a complex, of a morphism f : C_1 -> C_2
of complexes. We denote mapping cone of f by Cone(f). The objects of mapping cone are given
by T C_1^i ⊕ C_2^i. The ith differential of Cone(f) is given by
         #  - p_1 ;; d^{i+1}_X ;; i_1 - i_2 ;; f^{i+1} ;; p_1 + p_2 ;; d^i_Y ;; i_2 #
         $  - p_1 ;; d^{i+1}_X ;; i_1 - i_2 ;; f^{i+1} ;; p_1 + p_2 ;; d^i_Y ;; i_2 $

We split the definition of the ith differential into a sum of 3 morphisms. These are constructed in
[MappingConeDiff1], [MappingConeDiff3], and [MappingConeDiff3], and correspond the morphisms of the
above formula, respectively. In [MappingConeDiff] we construct the differential. In
[MappingCone_comp] we show that composition of two consecutive differentials is 0. The complex
Cone(f) is constructed in [MappingCone].
*)
Section mapping_cone.

  Variable A : Additive.


  (**  # - (p_1 ;; d^{i+1}_{C_1} ;; i_1) # *)
  Definition MappingConeDiff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1 DS2.
    use compose.
    - exact (pr11_TranslationComplex A C1 i).
    - exact (to_Pr1 A DS1).
    - use compose.
      + exact (pr11_TranslationComplex A C1 (i + 1)).
      + exact (DiffTranslationComplex A C1 i).
      + exact (to_In1 A DS2).
  Defined.

  (**  # - (p_1 ;; f (i + 1) ;; i_2) # *)
  Definition MappingConeDiff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1 DS2.
    use compose.
    - exact (pr11_TranslationComplex A C1 i).
    - exact (to_Pr1 A DS1).
    - use compose.
      + exact (C2 (i + 1)).
      + exact (f (i + 1)).
      + exact (to_In2 A DS2).
  Defined.

  (** # p2 ;; d^i_[C_2} ;; i2 # *)
  Definition MappingConeDiff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1 DS2.
    use compose.
    - exact (C2 i).
    - exact (to_Pr2 A DS1).
    - use compose.
      + exact (C2 (i + 1)).
      + exact (Diff C2 i).
      + exact (to_In2 A DS2).
  Defined.

  Definition MappingConeDiff {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1 DS2.
    use to_binop.
    - exact (MappingConeDiff1 f i).
    - use to_binop.
      +  exact (MappingConeDiff2 f i).
      +  exact (MappingConeDiff3 f i).
  Defined.

  Lemma MappingCone_Diff1_Diff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff1 f i) ;; (MappingConeDiff1 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff1. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_IdIn1 A DS2). rewrite id_right.
    rewrite <- (assoc _ _ (DiffTranslationComplex A C1 (i + 1))).
    rewrite (DiffTranslationComplex_comp A C1 i).
    rewrite ZeroArrow_comp_right. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff1_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff1 f i) ;; (MappingConeDiff3 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff1. unfold MappingConeDiff3. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A DS2)).
    rewrite (to_Unel1 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff2_Diff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    let DS3 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1 + 1)) (C2 (i + 1 + 1)) in
    (MappingConeDiff2 f i) ;; (MappingConeDiff1 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2 DS3. unfold MappingConeDiff2. unfold MappingConeDiff1.
    fold DS1. fold DS2. fold DS3.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_Unel2 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

   Lemma MappingCone_Diff2_Diff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff2 f i) ;; (MappingConeDiff2 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff2. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_Unel2 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff3_Diff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff3 f i) ;; (MappingConeDiff1 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff3. unfold MappingConeDiff1. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_Unel2 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff3_Diff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    (MappingConeDiff3 f i) ;; (MappingConeDiff2 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingConeDiff3. unfold MappingConeDiff2. fold DS1. fold DS2.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A DS2)).
    rewrite (to_Unel2 A DS2). rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_Diff3_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    let DS3 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1 + 1)) (C2 (i + 1 + 1)) in
    (MappingConeDiff3 f i) ;; (MappingConeDiff3 f (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2 DS3. unfold MappingConeDiff3. fold DS1. fold DS2. fold DS3.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A DS2)).
    rewrite (to_IdIn2 A DS2). rewrite id_right. rewrite <- (assoc _ _ (Diff C2 (i + 1))).
    rewrite (DSq A C2 i). rewrite ZeroArrow_comp_right. apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCone_comp {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A ((pr11_TranslationComplex A C1) i) (C2 i) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1)) (C2 (i + 1)) in
    let DS2 := to_BinDirectSums A ((pr11_TranslationComplex A C1) (i + 1 + 1)) (C2 (i + 1 + 1)) in
    (to_binop _ _ (MappingConeDiff1 f i)
              (to_binop _ _ (MappingConeDiff2 f i) (MappingConeDiff3 f i)))
      ;; (to_binop _ _ (MappingConeDiff1 f (i + 1))
                   (to_binop _ _ (MappingConeDiff2 f (i + 1)) (MappingConeDiff3 f (i + 1)))) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2 DS3. fold DS1. fold DS2. fold DS3.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_premor_linear'.
    set (D11 := MappingCone_Diff1_Diff1 f i). fold DS1 in D11. fold DS3 in D11. cbn in D11.
    rewrite to_premor_linear'.
    set (D13 := MappingCone_Diff1_Diff3 f i). fold DS1 in D13. fold DS2 in D13. fold DS3 in D13.
    cbn in D13.
    rewrite to_premor_linear'.
    set (D21 := MappingCone_Diff2_Diff1 f i). fold DS1 in D21. fold DS2 in D21. fold DS3 in D21.
    cbn in D21.
    rewrite to_premor_linear'.
    set (D22 := MappingCone_Diff2_Diff2 f i). fold DS1 in D22. fold DS2 in D22. fold DS3 in D22.
    cbn in D22.
    rewrite to_premor_linear'.
    set (D31 := MappingCone_Diff3_Diff1 f i). fold DS1 in D31. fold DS2 in D31. fold DS3 in D31.
    cbn in D31.
    rewrite to_premor_linear'.
    set (D32 := MappingCone_Diff3_Diff2 f i). fold DS1 in D32. fold DS2 in D32. fold DS3 in D32.
    cbn in D32.
    set (D33 := MappingCone_Diff3_Diff3 f i). fold DS1 in D33. fold DS2 in D33. fold DS3 in D33.
    cbn in D33.
    set (tmp := to_binop
                  DS1 DS3
                  (to_binop DS1 DS3 (MappingConeDiff2 f i ;; MappingConeDiff1 f (i + 1))
                            (to_binop DS1 DS3 (MappingConeDiff2 f i ;; MappingConeDiff2 f (i + 1))
                                      (MappingConeDiff2 f i ;; MappingConeDiff3 f (i + 1))))
                  (to_binop DS1 DS3 (MappingConeDiff3 f i ;; MappingConeDiff1 f (i + 1))
                            (to_binop DS1 DS3 (MappingConeDiff3 f i ;; MappingConeDiff2 f (i + 1))
                                      (MappingConeDiff3 f i ;; MappingConeDiff3 f (i + 1))))).
    use pathscomp0.
    - exact (to_binop DS1 DS3 (MappingConeDiff1 f i ;; MappingConeDiff2 f (i + 1)) tmp).
    - use to_lrw.
      rewrite <- to_lunax'. rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
      cbn. rewrite <- D11. apply maponpaths.
      rewrite <- to_runax'. rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
      apply maponpaths. exact D13.
    - unfold tmp. clear tmp.
      set (tmp := to_binop DS1 DS3 (MappingConeDiff3 f i ;; MappingConeDiff1 f (i + 1))
                           (to_binop DS1 DS3 (MappingConeDiff3 f i ;; MappingConeDiff2 f (i + 1))
                                     (MappingConeDiff3 f i ;; MappingConeDiff3 f (i + 1)))).
      use pathscomp0.
      + exact (to_binop DS1 DS3 (MappingConeDiff1 f i ;; MappingConeDiff2 f (i + 1))
                        (to_binop DS1 DS3 (MappingConeDiff2 f i ;; MappingConeDiff3 f (i + 1))
                                  tmp)).
      + use to_rrw. use to_lrw.
        rewrite <- to_lunax'. rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
        cbn. rewrite <- D21. apply maponpaths.
        rewrite <- to_lunax'. rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
        use to_lrw. exact D22.
      + unfold tmp. use pathscomp0.
        * exact (to_binop DS1 DS3 (MappingConeDiff1 f i ;; MappingConeDiff2 f (i + 1))
                          (MappingConeDiff2 f i ;; MappingConeDiff3 f (i + 1))).
        * apply maponpaths.
          rewrite <- to_runax'. rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
          cbn. rewrite <- D33. use to_rrw.
          rewrite <- to_lunax'. rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
          cbn. rewrite <- D31. apply maponpaths.
          rewrite <- to_lunax'. rewrite (PreAdditive_unel_zero _ (Additive.to_Zero A)).
          cbn. rewrite <- D32. apply idpath.
        * unfold MappingConeDiff1. unfold MappingConeDiff2. unfold MappingConeDiff3.
          fold DS1. fold DS2. fold DS3. rewrite assoc. rewrite assoc. rewrite assoc.
          rewrite <- (assoc _ _ (to_Pr1 A DS2)). rewrite (to_IdIn1 A DS2). rewrite id_right.
          rewrite assoc. rewrite assoc. rewrite assoc.
          rewrite <- (assoc _ _ (to_Pr2 A DS2)). rewrite (to_IdIn2 A DS2). rewrite id_right.
          rewrite <- to_postmor_linear'. rewrite <- (ZeroArrow_comp_left _ _ _ _ _ (to_In2 A DS3)).
          apply cancel_postcomposition. rewrite <- assoc. rewrite <- assoc.
          rewrite <- to_premor_linear'. rewrite <- (ZeroArrow_comp_right _ _ _ _ _ (to_Pr1 A DS1)).
          apply cancel_precomposition. cbn. rewrite (MComm f (i + 1)).
          rewrite <- to_postmor_linear'.
          rewrite <- (ZeroArrow_comp_left _ _ _ _ _ (f (i + 1 + 1))).
          apply cancel_postcomposition. use to_linvax'.
  Qed.

  Definition MappingCone {C1 C2 : Complex A} (f : Morphism C1 C2) : Complex A.
  Proof.
    use mk_Complex.
    - intros i. exact (to_BinDirectSums A (TranslationComplex A C1 i) (C2 i)).
    - intros i. exact (MappingConeDiff f i).
    - intros i. exact (MappingCone_comp f i).
  Defined.

End mapping_cone.


(** * Mapping cylinder *)
(** ** Introduction
In this section we construct the mapping cylinder, which is a complex, of a morphism f : C_1 -> C_2
of complexes. We denote mapping cylinder of f by Cyl(f). The objects of mapping cylinder are given
by C_1^i ⊕ Cone(f)^i. The ith differential of Cyl(f) is given by
         #  p_1 ;; d^i_X ;; i_1 - p_2 ;; p1 ;; i_1 + p_2 ;; d^i_C(f) ;; i_2 #

Here d^i_C(F) is the ith differential of the mapping cone of f, see section [mapping_cone].
We split the definition of the ith differential into a sum of 3 morphisms. These are constructed in
[MappingCylinderDiff1], [MappingCylinderDiff3], and [MappingCylinderDiff3], and correspond the
morphisms of the above formula, respectively. In [MappingCylinderDiff] we construct the differential.
In [MappingCylinder_comp] we show that composition of two consecutive differentials is 0. The
complex Cyl(f) is constructed in [MappingCylinder].
*)
Section mapping_cylinder.

  Variable A : Additive.

  (**  # p_1 ;; d^i_X ;; i_1 # *)
  Definition MappingCylinderDiff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1' := to_BinDirectSums A (pr11_TranslationComplex A C1 i) (C2 i) in
    let DS1 := to_BinDirectSums A (C1 i) DS1' in
    let DS2' := to_BinDirectSums A (pr11_TranslationComplex A C1 (i + 1)) (C2 (i + 1)) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) DS2' in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1' DS1 DS2' DS2.
    use compose.
    - exact (C1 i).
    - exact (to_Pr1 A DS1).
    - use compose.
      + exact (C1 (i + 1)).
      + exact (Diff C1 i).
      + exact (to_In1 A DS2).
  Defined.

  (**  # p_2 ;; (- p1) ;; i_1 # *)
  Definition MappingCylinderDiff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1' := to_BinDirectSums A (pr11_TranslationComplex A C1 i) (C2 i) in
    let DS1 := to_BinDirectSums A (C1 i) DS1' in
    let DS2' := to_BinDirectSums A (pr11_TranslationComplex A C1 (i + 1)) (C2 (i + 1)) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) DS2' in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1' DS1 DS2' DS2.
    use compose.
    - exact (DS1').
    - exact (to_Pr2 A DS1).
    - use compose.
      + exact ((pr11_TranslationComplex A C1) i).
      + exact (to_inv (to_Pr1 A DS1')).
      + exact (to_In1 A DS2).
  Defined.

  (** p_2 ;; d^i_C(f) ;; i_2 *)
  Definition MappingCylinderDiff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1' := to_BinDirectSums A (pr11_TranslationComplex A C1 i) (C2 i) in
    let DS1 := to_BinDirectSums A (C1 i) DS1' in
    let DS2' := to_BinDirectSums A (pr11_TranslationComplex A C1 (i + 1)) (C2 (i + 1)) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) DS2' in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1' DS1 DS2' DS2.
    use compose.
    - exact DS1'.
    - exact (to_Pr2 A DS1).
    - use compose.
      + exact DS2'.
      + exact (MappingConeDiff A f i).
      + exact (to_In2 A DS2).
  Defined.

  Definition MappingCylinderDiff {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1' := to_BinDirectSums A (pr11_TranslationComplex A C1 i) (C2 i) in
    let DS1 := to_BinDirectSums A (C1 i) DS1' in
    let DS2' := to_BinDirectSums A (pr11_TranslationComplex A C1 (i + 1)) (C2 (i + 1)) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) DS2' in
    A ⟦ DS1, DS2 ⟧.
  Proof.
    intros DS1 DS2.
    use to_binop.
    - exact (MappingCylinderDiff1 f i).
    - use to_binop.
      +  exact (MappingCylinderDiff2 f i).
      +  exact (MappingCylinderDiff3 f i).
  Defined.

  Lemma MappingCylinder_Diff1_Diff1 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    let DS1 := to_BinDirectSums A (C1 i) (MappingCone A f i) in
    let DS2 := to_BinDirectSums A (C1 (i + 1)) (MappingCone A f i) in
    (MappingCylinderDiff1 f i) ;; (MappingCylinderDiff1 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros DS1 DS2. unfold MappingCylinderDiff1. unfold MappingCylinderDiff2. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr1 A _)).
    set (DS3 := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_IdIn1 A DS3). rewrite id_right. rewrite <- (assoc _ _ (Diff C1 (i + 1))).
    rewrite (DSq A C1 i). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply idpath.
  Qed.

  Lemma MappingCylinder_Diff1_Diff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff1 f i) ;; (MappingCylinderDiff2 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff1. unfold MappingCylinderDiff2. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_Unel1' DS). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCylinder_Diff1_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff1 f i) ;; (MappingCylinderDiff3 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff1. unfold MappingCylinderDiff3. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_Unel1' DS). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCylinder_Diff2_Diff2 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff2 f i) ;; (MappingCylinderDiff2 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff2. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_Unel1' DS). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply ZeroArrow_comp_left.
  Qed.

  Lemma MappingCylinder_Diff2_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff2 f i) ;; (MappingCylinderDiff3 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_Unel1' DS). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    apply ZeroArrow_comp_left.
  Qed.

  Lemma MapingCylinder_Diff3_Diff3 {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    (MappingCylinderDiff3 f i) ;; (MappingCylinderDiff3 f (i + 1)) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff3. cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite <- (assoc _ _ (to_Pr2 A _)).
    set (DS := to_BinDirectSums A (C1 (i + 1)) (to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1)))).
    rewrite (to_IdIn2 A DS). rewrite id_right. rewrite <- (assoc _ (MappingConeDiff A f i)).
    set (tmp := DSq A (MappingCone A f) i). cbn in tmp. cbn. rewrite tmp. clear tmp.
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. apply idpath.
  Qed.

  Lemma MappingCylinder_comp {C1 C2 : Complex A} (f : Morphism C1 C2) (i : hz) :
    MappingCylinderDiff f i ;; MappingCylinderDiff f (i + 1) =
    ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    unfold MappingCylinderDiff. cbn.
    set (D11 := MappingCylinder_Diff1_Diff1 f i).
    set (D12 := MappingCylinder_Diff1_Diff2 f i).
    set (D13 := MappingCylinder_Diff1_Diff3 f i).
    set (D22 := MappingCylinder_Diff2_Diff2 f i).
    set (D23 := MappingCylinder_Diff2_Diff3 f i).
    set (D33 := MapingCylinder_Diff3_Diff3 f i).
    rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    cbn. cbn in D11. rewrite D11. cbn in D12. rewrite D12. cbn in D13. rewrite D13.
    cbn in D22. rewrite D22. cbn in D23. rewrite D23. cbn in D33. rewrite D33.
    rewrite to_lunax''. rewrite to_lunax''. rewrite to_runax''. rewrite to_runax''.
    rewrite to_lunax''. rewrite to_runax''.
    unfold MappingCylinderDiff1. unfold MappingCylinderDiff2. unfold MappingCylinderDiff3.
    cbn. clear D11 D12 D13 D22 D23 D33.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS1' := to_BinDirectSums A (C1 i) DS1).
    set (DS2 := to_BinDirectSums A (C1 (i + 1 + 1 + 1)) (C2 (i + 1 + 1))).
    set (DS2' := to_BinDirectSums A (C1 (i + 1 + 1)) DS2).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS3' := to_BinDirectSums A (C1 (i + 1)) DS3). cbn.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- (assoc _ _ (to_Pr1 A DS3')). rewrite (to_IdIn1 A DS3'). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr1 A DS3')). rewrite (to_Unel2' DS3').
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    rewrite <- (assoc _ _ (to_Pr2 A DS3')). rewrite (to_IdIn2 A DS3').
    rewrite id_right. rewrite to_binop_inv_inv.
    apply cancel_inv. rewrite inv_inv_eq. rewrite to_inv_zero.
    rewrite <- to_postmor_linear'.
    rewrite <- (ZeroArrow_comp_left _ _ _ _ _ (to_In1 A DS2')). apply cancel_postcomposition.
    rewrite <- assoc. rewrite <- assoc. rewrite <- to_premor_linear'.
    rewrite <- (ZeroArrow_comp_right _ _ _ _ _ (to_Pr2 A DS1')). apply cancel_precomposition.
    unfold MappingConeDiff.
    unfold MappingConeDiff1. unfold MappingConeDiff2. unfold MappingConeDiff3.
    cbn in *. fold DS1 DS1' DS2 DS2' DS3 DS3'. unfold DiffTranslationComplex.
    rewrite assoc. rewrite assoc. rewrite <- PreAdditive_invrcomp.
    rewrite to_postmor_linear'. rewrite <- (assoc _ _ (to_Pr1 A DS3)).
    rewrite (to_IdIn1 A DS3). rewrite id_right. cbn.
    rewrite to_postmor_linear'. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS3)). rewrite <- (assoc _ _ (to_Pr1 A DS3)).
    rewrite (to_Unel2' DS3). rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right.
    rewrite to_runax''. rewrite to_runax''. rewrite (@to_rinvax' A (Additive.to_Zero A)).
    apply idpath.
  Qed.

  Definition MappingCylinder {C1 C2 : Complex A} (f : Morphism C1 C2) : Complex A.
  Proof.
    use mk_Complex.
    - intros i. exact (to_BinDirectSums
                         A (C1 i) (to_BinDirectSums A (pr11_TranslationComplex A C1 i) (C2 i))).
    - intros i. exact (MappingCylinderDiff f i).
    - intros i. cbn beta. exact (MappingCylinder_comp f i).
  Defined.

End mapping_cylinder.


(** * Let f : X -> Y, then Y is isomorphic to Cyl(f) in K(A) *)
(** ** Introduction
We show that in K(A) Y and Cyl(f) are isomorphic. The isomorphism is given by the morphisms
α := i_2 ;; i_2 and β := p_1 ;; f + p_2 ;; p_2. We have α ;; β = id in C(A), but
β ;; α ≠ id_{Cyl(f)} in C(A). We define a homotopy by χ^i := p_1 ;; i_1 ;; i_2 : Cyl(f)^i -->
Cyl(f)^{i-1}. We show that
       # id_{Cyl(f)} - β ;; α = χ^i ;; d^{i-1}_{Cyl(f)} + d^i_{Cyl(f)} ;; χ^{i-1} #
       $ id_{Cyl(f)} - β ;; α = χ^i ;; d^{i-1}_{Cyl(f)} + d^i_{Cyl(f)} ;; χ^{i-1} $  ( * )
This means that β ;; α = id_{Cyl(f)} in K(A) by the definition of homotopy of morphisms.
Hence Y and C(f) are isomorphic.

The morphisms α and β are defined in [MappingCylinderMor1_mor] and [MappingCylinderMor2_mor].
The equality α ;; β = id is proven in [MappingCylinderIso_eq1]. The homotopy χ is constructed
in [MappingCylinderIsoHomot]. The equality ( * ) is proven in 4 steps. These steps are
[MappingCylinderIsoHomot_eq1], [MappingCylinderIsoHomot_eq2], [MappingCylinderIsoHomot_eq3],
and [MappingCylinderIsoHomot_eq4]. The equality β ;; α = id is proved in [MappingCylinderIso_eq2].
The fact that Y and Cyl(f) are isomorphic in K(A) is proved in [MappingCylinderIso].
*)
Section mapping_cylinder_KA_iso.

  Variable A : Additive.


  Definition MappingCylinderMor1_mor {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
             (i : hz) : A ⟦ C2 i, (MappingCylinder A f) i ⟧.
  Proof.
    unfold MappingCylinder. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    use compose.
    - exact DS1.
    - use (to_In2 A DS1).
    - use (to_In2 A DS2).
  Defined.

  Lemma MappingCylinderMor1_comm {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    MappingCylinderMor1_mor f i ;; Diff (MappingCylinder A f) i =
    Diff C2 i ;; MappingCylinderMor1_mor f (i + 1).
  Proof.
    unfold MappingCylinderMor1_mor. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS4 := to_BinDirectSums A (C1 (i + 1)) DS3). rewrite assoc.
    unfold MappingCylinderDiff. unfold MappingCylinderDiff1.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3.
    cbn. fold DS1 DS2 DS3 DS4. rewrite to_premor_linear'. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS2)). rewrite (to_Unel2' DS2).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. rewrite to_premor_linear'. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS2)). rewrite (to_IdIn2 A DS2).
    rewrite id_right. rewrite <- PreAdditive_invrcomp.
    rewrite (to_Unel2' DS1). rewrite to_inv_zero. rewrite ZeroArrow_comp_left.
    rewrite to_lunax''. apply cancel_postcomposition.
    unfold MappingConeDiff. unfold MappingConeDiff1.
    unfold MappingConeDiff2. unfold MappingConeDiff3.
    cbn. fold DS1 DS2 DS3 DS4. rewrite to_premor_linear'. rewrite assoc.
    rewrite (to_Unel2' DS1). rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite to_premor_linear'. rewrite assoc. rewrite (to_Unel2' DS1).
    rewrite ZeroArrow_comp_left. rewrite to_lunax''. rewrite assoc.
    rewrite (to_IdIn2 A DS1). rewrite id_left. apply idpath.
  Qed.

  Definition MappingCylinderMor1 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (ComplexPreCat_Additive A)⟦(ComplexHomotFunctor A C2),
                              (ComplexHomotFunctor A (MappingCylinder A f))⟧.
  Proof.
    cbn. use mk_Morphism.
    - intros i. exact (MappingCylinderMor1_mor f i).
    - intros i. exact (MappingCylinderMor1_comm f i).
  Defined.

  Definition MappingCylinderMor2_mor {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
             (i : hz) : A ⟦ (MappingCylinder A f) i, C2 i ⟧.
  Proof.
    unfold MappingCylinder. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    use to_binop.
    - use compose.
      + exact (C1 i).
      + use (to_Pr1 A DS2).
        + exact (MMor f i).
    - use compose.
      + exact DS1.
      + use (to_Pr2 A DS2).
      + use (to_Pr2 A DS1).
  Defined.

  Lemma MappingCylinderMor2_comm {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    MappingCylinderMor2_mor f i ;; Diff C2 i =
    Diff (MappingCylinder A f) i ;; MappingCylinderMor2_mor f (i + 1).
  Proof.
    unfold MappingCylinderMor2_mor. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS4 := to_BinDirectSums A (C1 (i + 1)) DS3).
    unfold MappingCylinderDiff. unfold MappingCylinderDiff1.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3.
    cbn. fold DS1 DS2 DS3 DS4. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite to_postmor_linear'. rewrite to_premor_linear'. rewrite to_premor_linear'.
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite (to_Unel1' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite (to_Unel1' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite to_runax''.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_Unel2' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite (to_IdIn2 A DS4). rewrite id_right.
    rewrite <- assoc. rewrite (MComm f i). rewrite assoc. use to_rrw.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. rewrite <- to_premor_linear'.
    apply cancel_precomposition.
    unfold MappingConeDiff. unfold MappingConeDiff1.
    unfold MappingConeDiff2. unfold MappingConeDiff3.
    cbn. fold DS1 DS2 DS3 DS4. rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite (to_Unel1' DS3).
    rewrite ZeroArrow_comp_right. rewrite to_lunax''.
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite (to_IdIn2 A DS3). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr2 A DS3)). rewrite (to_IdIn2 A DS3). rewrite id_right.
    rewrite <- PreAdditive_invlcomp. rewrite <- to_assoc.
    rewrite (@to_linvax' A (Additive.to_Zero A)). rewrite to_lunax''. apply idpath.
  Qed.

  Definition MappingCylinderMor2 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (ComplexPreCat_Additive A)⟦(ComplexHomotFunctor A (MappingCylinder A f)),
                               (ComplexHomotFunctor A C2)⟧.
  Proof.
    cbn. use mk_Morphism.
    - intros i. exact (MappingCylinderMor2_mor f i).
    - intros i. exact (MappingCylinderMor2_comm f i).
  Defined.

  Lemma MappingCylinderIso_eq1' {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (MappingCylinderMor1 f) ;; (MappingCylinderMor2 f) = identity _.
  Proof.
    use MorphismEq. intros i. cbn. unfold MappingCylinderMor1_mor.
    unfold MappingCylinderMor2_mor. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    rewrite to_premor_linear'. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS2)). rewrite (to_Unel2' DS2).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr2 A DS2)). rewrite (to_IdIn2 A DS2). rewrite id_right.
    rewrite (to_IdIn2 A DS1). apply idpath.
  Qed.

  Lemma MappingCylinderIso_eq1 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (# (ComplexHomotFunctor A) (MappingCylinderMor1 f))
      ;; (# (ComplexHomotFunctor A) (MappingCylinderMor2 f)) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite MappingCylinderIso_eq1'. rewrite functor_id.
    apply idpath.
  Qed.

  Lemma MappingCylinderIsoHomot {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    ComplexHomot A (MappingCylinder A f) (MappingCylinder A f).
  Proof.
    intros i. unfold MappingCylinder. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))).
    set (DS4 := to_BinDirectSums A (C1 (i - 1)) DS3).
    use compose.
    - exact (C1 i).
    - exact (to_Pr1 A DS2).
    - use compose.
      + exact DS3.
      + exact (transportb (fun x' : ob A => precategory_morphisms x' DS3)
                          (maponpaths C1 (! hzrminusplus i 1)) (to_In1 A DS3)).
      + exact (to_inv (to_In2 A DS4)).
  Defined.

  Definition MappingCylinderIsoHomot_mor1 {C1 C2 : Complex A}
             (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) (i : hz) :
    A⟦(MappingCylinder A f) i, (MappingCylinder A f) i⟧.
  Proof.
    cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    use to_binop.
    - use compose.
      + exact (C1 i).
      + exact (to_Pr1 A DS2).
      + exact (to_In1 A DS2).
    - use to_binop.
      + use compose.
        * exact (C1 i).
        * exact (to_Pr1 A DS2).
        * use compose.
          -- exact (C1 (i + 1)).
          -- exact (Diff C1 i).
          -- use compose.
             ++ exact DS1.
             ++ exact (to_In1 A DS1).
             ++ exact (to_In2 A DS2).
      + use compose.
        * exact (C1 i).
        * exact (to_Pr1 A DS2).
        * use compose.
          -- exact (C2 i).
          -- exact (to_inv (MMor f i)).
          -- use compose.
             ++ exact DS1.
             ++ exact (to_In2 A DS1).
             ++ exact (to_In2 A DS2).
  Defined.

  Lemma MappingCylinderIsoHomot_eq1 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    (transportf (precategory_morphisms
                   (to_BinDirectSums A (C1 i) (to_BinDirectSums A (C1 (i + 1)) (C2 i))))
                (maponpaths (λ (i0 : hz),
                             BinDirectSumConeOb
                               A (to_BinDirectSums
                                    A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                            (hzrminusplus i 1))
                (MappingCylinderIsoHomot f i ;; MappingCylinderDiff A f (i - 1))) =
    MappingCylinderIsoHomot_mor1 f i.
  Proof.
    cbn. rewrite transportf_postcompose.
    unfold MappingCylinderIsoHomot. unfold MappingCylinderIsoHomot_mor1. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i - 1 + 1)) (C2 (i - 1))).
    set (DS4 := to_BinDirectSums A (C1 (i - 1)) DS3).
    set (DS5 := to_BinDirectSums A (C1 (i - 1 + 1 + 1)) (C2 (i - 1 + 1))).
    set (DS6 := to_BinDirectSums A (C1 (i - 1 + 1)) DS5). cbn.
    rewrite <- assoc. rewrite <- assoc. rewrite <- to_premor_linear'. rewrite <- to_premor_linear'.
    apply cancel_precomposition. rewrite <- transportf_postcompose.
    rewrite assoc. rewrite assoc. rewrite <- to_postmor_linear'.
    rewrite <- transportf_postcompose. rewrite <- transportb_precompose.
    (* Unfold MappingCylinderDiff *)
    unfold MappingCylinderDiff. unfold MappingCylinderDiff1.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3. cbn.
    fold DS1 DS2 DS3 DS4 DS5 DS6. cbn. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    (* simplify *)
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invrcomp.
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc.
    rewrite <- PreAdditive_invlcomp. rewrite <- (assoc _ _ (to_Pr1 A DS4)).
    rewrite (to_Unel2' DS4). rewrite ZeroArrow_comp_right. rewrite to_inv_zero.
    rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. rewrite to_lunax''.
    rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invrcomp. rewrite assoc.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp.
    rewrite <- (assoc _ _ (to_Pr2 A DS4)). rewrite (to_IdIn2 A DS4). rewrite id_right.
    rewrite inv_inv_eq.
    (* Unfold MappingConeDiff *)
    unfold MappingConeDiff. unfold MappingConeDiff1.
    unfold MappingConeDiff2. unfold MappingConeDiff3. cbn.
    fold DS1 DS2 DS3 DS4 DS5 DS6. cbn. rewrite to_premor_linear'.
    rewrite assoc. rewrite to_premor_linear'. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc.
    rewrite (to_IdIn1 A DS3). rewrite id_left. rewrite id_left.
    rewrite (to_Unel1' DS3). rewrite id_left. rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_left. rewrite to_runax''.
    unfold DiffTranslationComplex. cbn.
    (* rewrite transports *)
    rewrite <- transportb_to_binop. rewrite <- transportf_to_binop. rewrite <- transportb_to_inv.
    rewrite <- transportf_to_inv. cbn. rewrite to_postmor_linear'. rewrite <- transportb_to_binop.
    rewrite <- transportf_to_binop.
    (* The first terms of to_binop are equal, cancel them *)
    assert (e1 : (transportf
                    (precategory_morphisms (C1 i))
                    (maponpaths
                       (λ (i0 : pr1 hz),
                        BinDirectSumConeOb
                          A (to_BinDirectSums
                               A (C1 i0)
                               (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                       (hzrminusplus i 1))
                    (transportb (λ x' : A, A ⟦ x', DS6 ⟧) (maponpaths C1 (! hzrminusplus i 1))
                                (to_In1 A DS6))) = (to_In1 A DS2)).
    {
      cbn. unfold DS2, DS1, DS6, DS5.
      set (tmp := fun (i0 : hz) =>
                    BinDirectSumConeOb
                      A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))).
      set (tmp'' := (fun (i0 : hz) =>
                       to_In1 A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                              (C2 i0))))).
      set (tmp' := @transport_hz_double_section_f_b A C1 tmp tmp'' _ _ (hzrminusplus i 1)).
      unfold tmp'' in tmp'.
      rewrite tmp'. unfold tmp. apply idpath.
    }
    cbn in e1. cbn. rewrite <- e1. clear e1. use to_rrw.
    (* The first term of to_binop are equal, cancel them *)
    rewrite <- to_binop_inv_inv. rewrite transportf_to_inv. rewrite transportb_to_inv.
    rewrite <- PreAdditive_invlcomp. rewrite <- PreAdditive_invlcomp. rewrite inv_inv_eq.
    rewrite transportf_to_inv. rewrite transportb_to_inv. rewrite PreAdditive_invlcomp.
    rewrite PreAdditive_invlcomp. rewrite to_postmor_linear'.
    assert (e1 : (transportf (precategory_morphisms (C1 i))
                             (maponpaths
                                (λ (i0 : pr1 hz),
                                 BinDirectSumConeOb
                                   A (to_BinDirectSums
                                        A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0))))
                                (hzrminusplus i 1))
                             (transportb (λ x' : A, A ⟦ x', DS6 ⟧)
                                         (maponpaths C1 (! hzrminusplus i 1))
                                         (Diff C1 (i - 1 + 1) ;; to_In1 A DS5 ;; to_In2 A DS6))) =
                 (Diff C1 i ;; to_In1 A DS1 ;; to_In2 A DS2)).
    {
      cbn. unfold DS2, DS1, DS6, DS5.
      set (tmp := fun i0 : hz => BinDirectSumConeOb
                                A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                (C2 i0)))).
      set (tmp'' := (fun (i0 : hz) =>
                       (Diff C1 i0)
                         ;; (to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                         ;; (to_In2 A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                    (C2 i0)))))).
      set (tmp' := @transport_hz_double_section_f_b A C1 tmp tmp'' _ _ (hzrminusplus i 1)).
      unfold tmp'' in tmp'.
      rewrite tmp'. unfold tmp. apply idpath.
    }
    rewrite <- e1. clear e1. use to_rrw.
    (* Solve the rest *)
    cbn. unfold DS2, DS1, DS6, DS5.
    set (tmp := fun i0 : hz => BinDirectSumConeOb
                              A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                              (C2 i0)))).
    set (tmp'' := (fun (i0 : hz) =>
                     (to_inv (MMor f i0))
                       ;; (to_In2 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                       ;; (to_In2 A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                  (C2 i0)))))).
    set (tmp' := @transport_hz_double_section_f_b A C1 tmp tmp'' _ _ (hzrminusplus i 1)).
    unfold tmp'' in tmp'.
    rewrite tmp'. unfold tmp. apply idpath.
  Qed.

  Definition MappingCylinderIsoHomot_mor2 {C1 C2 : Complex A}
             (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) (i : hz) :
    A⟦(MappingCylinder A f) i, (MappingCylinder A f) i⟧.
  Proof.
    cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    use to_binop.
    - use compose.
      + exact (C1 i).
      + exact (to_Pr1 A DS2).
      + use compose.
        * exact (C1 (i + 1)).
        * exact (to_inv (Diff C1 i)).
        * use compose.
          -- exact DS1.
          -- exact (to_In1 A DS1).
          -- exact (to_In2 A DS2).
    - use compose.
      + exact DS1.
      + exact (to_Pr2 A DS2).
      + use compose.
        * exact (C1 (i + 1)).
        * exact (to_Pr1 A DS1).
        * use compose.
          -- exact DS1.
          -- exact (to_In1 A DS1).
          -- exact (to_In2 A DS2).
  Defined.

  Lemma MappyngCylinderIsoHomot_eq2 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    (transportf (precategory_morphisms
                   (to_BinDirectSums A (C1 i) (to_BinDirectSums A (C1 (i + 1)) (C2 i))))
                (maponpaths (λ (i0 : pr1 hz),
                             BinDirectSumConeOb
                               A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                               (C2 i0))))
                            (hzrplusminus i 1))
                (MappingCylinderDiff A f i ;; MappingCylinderIsoHomot f (i + 1))) =
    MappingCylinderIsoHomot_mor2 f i.
  Proof.
    cbn. unfold MappingCylinderIsoHomot. unfold MappingCylinderIsoHomot_mor2. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    set (DS3 := to_BinDirectSums A (C1 (i + 1 + 1)) (C2 (i + 1))).
    set (DS4 := to_BinDirectSums A (C1 (i + 1)) DS3).
    set (DS5 := to_BinDirectSums A (C1 (i + 1 - 1 + 1)) (C2 (i + 1 - 1))).
    set (DS6 := to_BinDirectSums A (C1 (i + 1 - 1)) DS5). cbn.
    unfold MappingCylinderDiff. unfold MappingCylinderDiff1.
    unfold MappingCylinderDiff2. unfold MappingCylinderDiff3. cbn.
    fold DS1 DS2 DS3 DS4 DS5 DS6. cbn.
    rewrite to_postmor_linear'. rewrite to_postmor_linear'. rewrite <- transportf_to_binop.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_IdIn1 A DS4). rewrite id_right.
    rewrite <- (assoc _ _ (to_Pr1 A DS4)). rewrite (to_Unel2' DS4).
    rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left.
    rewrite to_runax''.
    (* The first terms of to_binop are equal, cancel them *)
    assert (e1 : (transportf (precategory_morphisms DS2)
                             (maponpaths
                                (λ (i0 : pr1 hz),
                                 BinDirectSumConeOb
                                   A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                   (C2 i0))))
                                (hzrplusminus i 1))
                             (to_Pr1 A DS2 ;; Diff C1 i ;; transportb (λ x' : A, A ⟦ x', DS5 ⟧)
                                     (maponpaths C1 (! hzrminusplus (i + 1) 1))
                                     (to_In1 A DS5) ;; to_inv (to_In2 A DS6))) =
                 ((to_Pr1 A DS2) ;; (to_inv (Diff C1 i)) ;; (to_In1 A DS1) ;; (to_In2 A DS2))).
    {
      rewrite transportf_postcompose. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
      rewrite <- assoc. apply cancel_precomposition.
      rewrite <- PreAdditive_invlcomp. rewrite PreAdditive_invrcomp. apply cancel_precomposition.
      rewrite <- transportf_postcompose. rewrite <- transportb_precompose.
      rewrite <- PreAdditive_invrcomp.
      unfold DS2, DS1, DS6, DS5.
      set (tmp := fun i0 : hz => BinDirectSumConeOb
                                A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                                (C2 i0)))).
      set (tmp'' := (fun i0 : hz =>
                       (to_inv ((to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                                  ;; (to_In2 A (to_BinDirectSums
                                                  A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                              (C2 i0)))))))).
      set (tmp' := @transport_hz_double_section_f_b
                     A (fun i0 : hz => C1 (i0 + 1)) tmp tmp'' _ _ (hzrplusminus i 1)).
      unfold tmp'' in tmp'. rewrite tmp'. unfold tmp. apply maponpaths.
      assert (e2 : maponpaths C1 (! hzrminusplus (i + 1) 1) =
                   maponpaths (λ i0 : hz, C1 (i0 + 1)) (! hzrplusminus i 1)).
      {
        assert (e3 : maponpaths (λ i0 : hz, C1 (i0 + 1)) (! hzrplusminus i 1) =
                     maponpaths C1 (maponpaths (fun i0 : hz => i0 + 1) (! hzrplusminus i 1))).
        {
          induction (hzrplusminus i 1). apply idpath.
        }
        rewrite e3. clear e3. apply maponpaths. apply isasethz.
      }
      rewrite <- e2. apply idpath.
    }
    cbn in e1. cbn. rewrite <- e1. clear e1. use to_rrw.
    (* Use similar technique as above *)
    rewrite transportf_postcompose. rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    rewrite <- assoc. apply cancel_precomposition.
    rewrite <- PreAdditive_invlcomp. rewrite PreAdditive_invrcomp. apply cancel_precomposition.
    rewrite <- transportf_postcompose. rewrite <- transportb_precompose.
    rewrite <- PreAdditive_invrcomp.
    unfold DS2, DS1, DS6, DS5. rewrite transportf_to_inv. rewrite transportb_to_inv.
    rewrite inv_inv_eq.
    set (tmp := fun i0 : hz => BinDirectSumConeOb
                              A (to_BinDirectSums A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1))
                                                                              (C2 i0)))).
    set (tmp'' := (fun i0 : hz =>
                     (to_In1 A (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))
                       ;; (to_In2 A (to_BinDirectSums
                                       A (C1 i0) (to_BinDirectSums A (C1 (i0 + 1)) (C2 i0)))))).
    set (tmp' := @transport_hz_double_section_f_b
                   A (fun i0 : hz => C1 (i0 + 1)) tmp tmp'' _ _ (hzrplusminus i 1)).
    unfold tmp'' in tmp'.
    rewrite tmp'. unfold tmp. apply maponpaths.
    assert (e2 : maponpaths C1 (! hzrminusplus (i + 1) 1) =
                 maponpaths (λ i0 : hz, C1 (i0 + 1)) (! hzrplusminus i 1)).
    {
      assert (e3 : maponpaths (λ i0 : hz, C1 (i0 + 1)) (! hzrplusminus i 1) =
                   maponpaths C1 (maponpaths (fun i0 : hz => i0 + 1) (! hzrplusminus i 1))).
      {
        induction (hzrplusminus i 1). apply idpath.
        }
        rewrite e3. clear e3. apply maponpaths. apply isasethz.
    }
    rewrite <- e2. apply idpath.
  Qed.

  Lemma MappingCylinderisoHomot_eq3 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧)
        (i : hz) :
    let DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i) in
    let DS2 := to_BinDirectSums A (C1 i) DS1 in
    to_binop DS2 DS2
             (to_binop DS2 DS2 (to_Pr1 A DS2 ;; to_In1 A DS2)
                       (to_Pr2 A DS2 ;; to_Pr1 A DS1 ;; to_In1 A DS1 ;; to_In2 A DS2))
             (to_inv (to_Pr1 A DS2 ;; MMor f i ;; to_In2 A DS1 ;; to_In2 A DS2)) =
    to_binop DS2 DS2 (MappingCylinderIsoHomot_mor1 f i) (MappingCylinderIsoHomot_mor2 f i).
  Proof.
    intros DS1 DS2.
    unfold MappingCylinderIsoHomot_mor1. unfold MappingCylinderIsoHomot_mor2.
    cbn. fold DS1 DS2. cbn. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite to_assoc. rewrite to_assoc. use to_rrw. rewrite to_commax'.
    rewrite (to_commax'
               _ _ ((to_Pr1 A DS2) ;; (to_inv (MMor f i)) ;; (to_In2 A DS1) ;; (to_In2 A DS2))).
    rewrite to_assoc. rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. use to_rrw. rewrite <- to_assoc.
    rewrite <- PreAdditive_invrcomp. rewrite <- PreAdditive_invlcomp.
    rewrite <- PreAdditive_invlcomp. rewrite (@to_rinvax' A (Additive.to_Zero A)).
    rewrite to_lunax''. apply idpath.
  Qed.

  Lemma MappingCylinderIsoHomot_eq {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    to_binop _ _ (identity _) (to_inv (MappingCylinderMor2 f ;; MappingCylinderMor1 f)) =
    ComplexHomotMorphism A (MappingCylinderIsoHomot f).
  Proof.
    use MorphismEq. intros i. cbn.
    unfold MappingCylinderMor1_mor. unfold MappingCylinderMor2_mor. cbn.
    set (DS1 := to_BinDirectSums A (C1 (i + 1)) (C2 i)).
    set (DS2 := to_BinDirectSums A (C1 i) DS1).
    rewrite to_postmor_linear'. rewrite <- to_binop_inv_inv.
    rewrite <- (to_BinOpId A DS2).
    assert (e : to_Pr2 A DS2 ;; to_In2 A DS2 = to_Pr2 A DS2 ;; identity _ ;; to_In2 A DS2).
    {
      rewrite id_right. apply idpath.
    }
    rewrite e. clear e. rewrite <- (to_BinOpId A DS1). rewrite to_premor_linear'.
    rewrite to_postmor_linear'. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite to_assoc. rewrite to_assoc.
    rewrite (to_commax'
               _ (to_inv (to_Pr1 A DS2 ;; MMor f i ;; to_In2 A DS1 ;; to_In2 A DS2))).
    rewrite <- (to_assoc
                 _ _ _ (to_inv (to_Pr1 A DS2 ;; MMor f i ;; to_In2 A DS1 ;; to_In2 A DS2))).
    rewrite (@to_rinvax' A (Additive.to_Zero A)). rewrite to_lunax''. rewrite <- to_assoc.
    use (pathscomp0 (MappingCylinderisoHomot_eq3 f i)).
    rewrite <- (MappingCylinderIsoHomot_eq1 f i). rewrite <- (MappyngCylinderIsoHomot_eq2 f i).
    unfold DS2. unfold DS1. apply idpath.
  Qed.

  Lemma MappingCylinderIso_eq2 {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    (# (ComplexHomotFunctor A) (MappingCylinderMor2 f))
      ;; (# (ComplexHomotFunctor A) (MappingCylinderMor1 f)) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite <- functor_id. apply pathsinv0.
    use ComplexHomotFunctor_rel_mor'.
    - exact (MappingCylinderIsoHomot f).
    - exact (MappingCylinderIsoHomot_eq f).
  Qed.

  Definition MappingCylinderIso {C1 C2 : Complex A} (f : (ComplexPreCat_Additive A)⟦C1, C2⟧) :
    iso (ComplexHomotFunctor A C2) (ComplexHomotFunctor A (MappingCylinder A f)).
  Proof.
    use tpair.
    - exact (# (ComplexHomotFunctor A) (MappingCylinderMor1 f)).
    - use is_iso_qinv.
      + exact (# (ComplexHomotFunctor A) (MappingCylinderMor2 f)).
      + split.
        * exact (MappingCylinderIso_eq1 f).
        * exact (MappingCylinderIso_eq2 f).
  Qed.

End mapping_cylinder_KA_iso.

Local Transparent hz isdecrelhzeq hzplus iscommrngops ZeroArrow.
Close Scope hz_scope.
