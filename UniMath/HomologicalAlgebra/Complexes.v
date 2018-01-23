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
- Useful transports for complexes
*)

Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.

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

Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.


Unset Kernel Term Sharing.

Open Scope hz_scope.
Opaque hz isdecrelhzeq hzplus hzminus hzone hzzero iscommrngops ZeroArrow.

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
                 Pr1 · (C_i --> C_{i+1]) · In1 + Pr2 · (D_i --> D_{i+1}) · In2
   To show that this defines a direct sum in the category of complexes is straightforward. The zero
   complex is given by zero objects and zero morphisms.
*)
Section def_complexes.

  (** ** Basics of complexes *)

  Variable A : Additive.

  (** Complex *)
  Definition Complex : UU :=
    ∑ D' : (∑ D : (∏ i : hz, ob A), (∏ i : hz, A⟦D i, D (i + 1)⟧)),
           ∏ i : hz, (pr2 D' i) · (pr2 D' (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _.

  Definition mk_Complex (D : ∏ i : hz, ob A) (D' : ∏ i : hz, A⟦D i, D (i + 1)⟧)
             (D'' : ∏ i : hz, (D' i) · (D' (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _) :
    Complex := ((D,,D'),,D'').

  (** Accessor functions *)
  Definition Complex_Funclass (C : Complex) : hz -> ob A := pr1 (pr1 C).
  Coercion Complex_Funclass : Complex >-> Funclass.

  Definition Diff (C : Complex) (i : hz) : A⟦C i, C (i + 1)⟧ := pr2 (pr1 C) i.

  Definition DSq (C : Complex) (i : hz) :
    (Diff C i) · (Diff C (i + 1)) = ZeroArrow (Additive.to_Zero A) _ _ := pr2 C i.

  Lemma ComplexEq' (C1 C2 : Complex) (H : ∏ (i : hz), C1 i = C2 i)
        (H1 : ∏ (i : hz),
              transportf (λ x : A, C2 i --> x) (H (i + 1))
                         (transportf (λ x : A, x --> C1 (i + 1)) (H i) (Diff C1 i)) =
              Diff C2 i) :
    transportf (λ x : hz → A, ∏ i : hz, A ⟦ x i, x (i + 1) ⟧)
               (funextfun C1 C2 (λ i : hz, H i)) (Diff C1) =
    Diff C2.
  Proof.
    use funextsec. intros i.
    assert (e : transportf (λ x : hz → A, ∏ i0 : hz, A ⟦ x i0, x (i0 + 1) ⟧)
                           (funextfun C1 C2 (λ i0 : hz, H i0))
                           (Diff C1) i =
                transportf (λ x : hz → A, A ⟦ x i, x (i + 1) ⟧)
                           (funextfun C1 C2 (λ i0 : hz, H i0))
                           (Diff C1 i)).
    {
      induction (funextfun C1 C2 (λ i0 : hz, H i0)).
      apply idpath.
    }
    rewrite e. clear e.
    rewrite transport_mor_funextfun.
    rewrite transport_source_funextfun. rewrite transport_target_funextfun.
    exact (H1 i).
  Qed.

  Lemma ComplexEq'' (C1 C2 : Complex) (H : ∏ (i : hz), C1 i = C2 i)
        (H1 : ∏ (i : hz),
              transportf (λ x : A, C2 i --> x) (H (i + 1))
                         (transportf (λ x : A, x --> C1 (i + 1)) (H i) (Diff C1 i)) =
              Diff C2 i) :
    transportf
      (λ x : ∑ D : hz → A, ∏ i : hz, A ⟦ D i, D (i + 1) ⟧,
                                 ∏ i : hz, pr2 x i · pr2 x (i + 1) =
                                           ZeroArrow (Additive.to_Zero A) _ _)
      (total2_paths_f (funextfun C1 C2 (λ i : hz, H i))
                    (ComplexEq' C1 C2 H H1)) (DSq C1) = DSq C2.
  Proof.
    apply proofirrelevance. apply impred_isaprop. intros t. apply to_has_homsets.
  Qed.

  Lemma ComplexEq (C1 C2 : Complex) (H : ∏ (i : hz), C1 i = C2 i)
        (H1 : ∏ (i : hz),
              transportf (λ x : A, C2 i --> x) (H (i + 1))
                         (transportf (λ x : A, x --> C1 (i + 1)) (H i) (Diff C1 i)) =
              Diff C2 i) : C1 = C2.
  Proof.
    use total2_paths_f.
    - use total2_paths_f.
      + use funextfun. intros i. exact (H i).
      + exact (ComplexEq' C1 C2 H H1).
    - exact (ComplexEq'' C1 C2 H H1).
  Defined.

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
      · (BinDirectSumIndAr A (Diff C1 (i + 1)) (Diff C2 (i + 1)) B2 B3) =
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
    ∑ D : (∏ i : hz, A⟦C1 i, C2 i⟧), ∏ i : hz, (D i) · (Diff C2 i) = (Diff C1 i) · (D (i + 1)).

  Definition mk_Morphism (C1 C2 : Complex) (Mors : ∏ i : hz, A⟦C1 i, C2 i⟧)
             (Comm : ∏ i : hz, (Mors i) · (Diff C2 i) = (Diff C1 i) · (Mors (i + 1))) :
    Morphism C1 C2 := tpair _ Mors Comm.

  (** Accessor functions *)
  Definition MMor {C1 C2 : Complex} (M : Morphism C1 C2) (i : hz) : A⟦C1 i, C2 i⟧ := pr1 M i.
  Coercion MMor : Morphism >-> Funclass.

  Definition MComm {C1 C2 : Complex} (M : Morphism C1 C2) (i : hz) :
    (M i) · (Diff C2 i) = (Diff C1 i) · (M (i + 1)) := pr2 M i.

  (** A lemma to show that two morphisms are the same *)
  Lemma MorphismEq {C1 C2 : Complex} (M1 M2 : Morphism C1 C2) (H : ∏ i : hz, M1 i = M2 i) :
    M1 = M2.
  Proof.
    use total2_paths_f.
    - use funextsec. intros i. exact (H i).
    - use proofirrelevance. apply impred_isaprop. intros t. apply to_has_homsets.
  Qed.

  Lemma MorphismEq' {C1 C2 : Complex} (M1 M2 : Morphism C1 C2) (H : M1 = M2) :
    ∏ i : hz, M1 i = M2 i.
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
    (identity (C1 i)) · (Diff C1 i) = (Diff C1 i) · (identity (C1 (i + 1))).
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
    (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (C i)) · (Diff C i) =
    (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (Additive.to_Zero A))
      · (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (C (i + 1))).
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
      · (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (Additive.to_Zero A)) =
    (Diff C i) · ZeroArrow (Additive.to_Zero A) (C (i + 1)) (Additive.to_Zero A).
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
        (i : hz) : (M1 i) · (M2 i) · (Diff C3 i) = (Diff C1 i) · (M1 (i + 1) · M2 (i + 1)).
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
    - intros i. exact ((M1 i) · (M2 i)).
    - intros i. exact (MorphismCompComm M1 M2 i).
  Defined.

  (** ZeroMorphism as the composite of to zero and from zero *)
  Local Lemma ZeroMorphism_comm (C1 C2 : Complex) (i : hz) :
    ZeroArrow (Additive.to_Zero A) (C1 i) (C2 i) · Diff C2 i =
    Diff C1 i · ZeroArrow (Additive.to_Zero A) (C1 (i + 1)) (C2 (i + 1)).
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
    (to_In1 A B1) · (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) =
    (Diff C1 i) · (to_In1 A B2).
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
    (to_In2 A B1) · (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) =
    (Diff C2 i) · (to_In2 A B2).
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
    (to_Pr1 A B1) · (Diff C1 i) =
    (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) · (to_Pr1 A B2).
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
    (to_Pr2 A B1) · (Diff C2 i) =
    (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) · (to_Pr2 A B2).
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
    (to_binop (C1 i) (C2 i) (M1 i) (M2 i)) · (Diff C2 i) =
    (Diff C1 i) · (to_binop (C1 (i + 1)) (C2 (i + 1)) (M1 (i + 1)) (M2 (i + 1))).
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
    (to_inv (M i)) · (Diff C2 i) = (Diff C1 i) · (to_inv (M (i + 1))).
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

  (** pr1 · in1 + pr2 · in2 = id *)
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
    (FromBinDirectSum A B1 (f i) (g i)) · (Diff D i) =
    (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2)
      · (FromBinDirectSum A B2 (f (i + 1)) (g (i + 1))).
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
      · (BinDirectSumIndAr A (Diff C1 i) (Diff C2 i) B1 B2) =
    (Diff D i) · (ToBinDirectSum A B2 (f (i + 1)) (g (i + 1))).
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


(** * Transport of morphisms indexed by integers *)
Section transport_section'.

  Variable C : precategory.

  Lemma transport_hz_source_target (f : hz -> ob C) (n : hz) (H : ∏ (i : hz), C⟦f i, f (i + n)⟧)
        (i i' : hz) (e1 : i = i') :
    H i' = transportf (λ (x : ob C), C⟦x, f (i' + n)⟧) (maponpaths f e1)
                      (transportf (precategory_morphisms (f i))
                                  (maponpaths f (hzplusradd i i' n e1)) (H i)).
  Proof.
    induction e1. apply idpath.
  Qed.

  Lemma transport_hz_target_source (f : hz -> ob C) (n : hz) (H : ∏ (i : hz), C⟦f i, f (i + n)⟧)
        (i i' : hz) (e1 : i = i') :
    H i' = transportf (precategory_morphisms (f i'))
                      (maponpaths f (hzplusradd i i' n e1))
                      (transportf (λ (x : ob C), C⟦x, f (i + n)⟧) (maponpaths f e1) (H i)).
  Proof.
    induction e1. apply idpath.
  Qed.

  Lemma transport_hz_section (f : hz -> ob C) (n : hz) (H : ∏ (i : hz), C⟦f i, f (i + n)⟧)
        (i i' : hz) (e1 : i = i') :
    transportf (precategory_morphisms (f i)) (maponpaths f (hzplusradd i i' n e1)) (H i) =
    transportf (λ (x : ob C), C⟦x, f (i' + n)⟧) (maponpaths f (! e1)) (H i').
  Proof.
    induction e1. apply idpath.
  Qed.

  Lemma transport_hz_section' (f : hz -> ob C) (n : hz) (H : ∏ (i : hz), C⟦f (i + n), f i⟧)
        (i i' : hz) (e1 : i + n = i' + n) (e2 : i = i') :
    transportf (precategory_morphisms (f (i + n))) (maponpaths f e2) (H i) =
    transportf (λ (x : ob C), C⟦x, f i'⟧) (maponpaths f (! e1)) (H i').
  Proof.
    induction e2. assert (e : e1 = idpath _) by apply isasethz. rewrite e. clear e. apply idpath.
  Qed.

  Lemma transport_hz_double_section (f f' : hz -> ob C) (H : ∏ (i : hz), C⟦f i, f' i⟧)
        (i i' : hz) (e : i = i') :
    transportf (precategory_morphisms (f i)) (maponpaths f' e) (H i) =
    transportf (λ (x : ob C), C⟦x, f' i'⟧) (maponpaths f (! e)) (H i').
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_double_section_source_target (f f' : hz -> ob C) (H : ∏ (i : hz), C⟦f i, f' i⟧)
        (i i' : hz) (e : i = i') :
    H i' = transportf (precategory_morphisms (f i')) (maponpaths f' e)
                      (transportf (λ (x : ob C), C⟦x, f' i⟧) (maponpaths f e) (H i)).
  Proof.
    induction e. apply idpath.
  Qed.

End transport_section'.


Section acyclic_complexes.

  Variable A : Additive.

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
    ∏ i0 : hz, A ⟦ComplexFromObject_obs X i i0, ComplexFromObject_obs X i (i0 + 1)⟧.
  Proof.
    intros i0.
    exact (ZeroArrow (Additive.to_Zero A) (ComplexFromObject_obs X i i0)
                     (ComplexFromObject_obs X i (i0 + 1))).
  Defined.

  Local Lemma ComplexFromObject_comm (X : ob A) (i : hz) :
    ∏ i0 : hz, (ComplexFromObject_mors X i i0) · (ComplexFromObject_mors X i (i0 + 1)) =
               ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros i0. apply ZeroArrow_comp_left.
  Qed.

  Definition ComplexFromObject (X : ob A) (i : hz) : Complex A.
  Proof.
    use mk_Complex.
    - exact (ComplexFromObject_obs X i).
    - exact (ComplexFromObject_mors X i).
    - exact (ComplexFromObject_comm X i).
  Defined.

  (** A morphism in A induces a morphisms of ComplexFromObjects *)
  Definition ObjectMorToComplexMor_mors {a b : ob A} (f : a --> b) (i : hz) :
    ∏ i0 : hz, A ⟦(ComplexFromObject a i) i0, (ComplexFromObject b i) i0⟧.
  Proof.
    intros i0.
    unfold ComplexFromObject. cbn. unfold ComplexFromObject_obs. cbn. unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    - exact f.
    - apply (ZeroArrow (Additive.to_Zero A)).
  Defined.

  Local Lemma ObjectMorToComplexMor_comm {a b : ob A} (f : a --> b) (i : hz) :
    ∏ i0 : hz, (ObjectMorToComplexMor_mors f i i0) · (Diff (ComplexFromObject b i) i0) =
               (Diff (ComplexFromObject a i) i0) · (ObjectMorToComplexMor_mors f i (i0 + 1)).
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


  (** ** Construction of a complex with a given object in two adjacent positions *)


  (** *** Construction of the complex ... --> 0 --> X -Id-> X --> 0 --> ... *)

  Definition AcyclicComplexFromObject_obs (a : ob A) (i : hz) : hz -> ob A.
  Proof.
    intros i0.
    induction (isdecrelhzeq i i0) as [e | n].
    - exact a.
    - induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      + exact a.
      + exact (Additive.to_Zero A).
  Defined.

  Definition AcyclicComplexFromObject_mors (a : ob A) (i : hz) :
    ∏ i0 : hz, A ⟦AcyclicComplexFromObject_obs a i i0, AcyclicComplexFromObject_obs a i (i0 + 1)⟧.
  Proof.
    intros i0. unfold AcyclicComplexFromObject_obs. cbn. unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    + induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      * exact (fromempty (hzeqeisi e e')).
      * induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e'' | n''].
        -- exact (identity a).
        -- exact (fromempty (hzeqnmplusr e n'')).
    + induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      * induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        -- exact (fromempty (hzeqsnmnsm e' e'')).
        -- induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e''' | n'''].
           ++ exact (fromempty (hzeqeisi e' e''')).
           ++ exact (ZeroArrow (Additive.to_Zero A) a (Additive.to_Zero A)).
      * induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        -- exact (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) a).
        -- induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e''' | n'''].
           ++ exact (fromempty (hzeqnmplusr' n e''')).
           ++ exact (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (Additive.to_Zero A)).
  Defined.

  Local Lemma AcyclicComplexFromObject_diff (a : ob A) (i : hz) :
    ∏ i0 : hz, (AcyclicComplexFromObject_mors a i i0)
                 · (AcyclicComplexFromObject_mors a i (i0 + 1)) =
               ZeroArrow (Additive.to_Zero A) _ _.
  Proof.
    intros i0. unfold AcyclicComplexFromObject_obs. unfold AcyclicComplexFromObject_mors.
    unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    - induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      + exact (fromempty (hzeqeisi e e')).
      + induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e'' | n''].
        * induction (isdecrelhzeq i (i0 + 1 + 1)) as [e''' | n'''].
          -- exact (fromempty (hzeqsnmnsm e'' e''')).
          -- induction (isdecrelhzeq (i + 1) (i0 + 1 + 1)) as [e'''' | n''''].
             ++ exact (fromempty (hzeqeisi e'' e'''')).
             ++ exact (ZeroArrow_comp_right _ _ _ _ _ _).
        * exact (fromempty (hzeqnmplusr e n'')).
    - induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      + induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        * exact (fromempty (hzeqsnmnsm e' e'')).
        * induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e''' | n'''].
          -- exact (fromempty (hzeqeisi e' e''')).
          -- induction (isdecrelhzeq i (i0 + 1 + 1)) as [e'''' | n''''].
             ++ exact (ZeroArrow_comp_left _ _ _ _ _ _).
             ++ induction (isdecrelhzeq (i + 1) (i0 + 1 + 1)) as [e5 | n5].
                ** exact (fromempty (hzeqnmplusr' n'' e5)).
                ** exact (ZeroArrow_comp_left _ _ _ _ _ _).
      + induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        * induction (isdecrelhzeq i (i0 + 1 + 1)) as [e3 | n3].
          -- exact (fromempty (hzeqeisi e'' e3)).
          -- induction (isdecrelhzeq (i + 1) (i0 + 1 + 1)) as [e4 | n4].
             ++ exact (ZeroArrow_comp_left _ _ _ _ _ _).
             ++ exact (fromempty (hzeqnmplusr e'' n4)).
        * induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e3 | n3].
          -- exact (fromempty (hzeqnmplusr' n e3)).
          -- induction (isdecrelhzeq i (i0 + 1 + 1)) as [e4 | n4].
             ++ exact (ZeroArrow_comp_left _ _ _ _ _ _).
             ++ induction (isdecrelhzeq (i + 1) (i0 + 1 + 1)) as [e5 | n5].
                ** exact (fromempty (hzeqnmplusr' n'' e5)).
                ** exact (ZeroArrow_comp_left _ _ _ _ _ _).
  Qed.

  Definition AcyclicComplexFromObject (a : ob A) (i : hz) : Complex A.
  Proof.
    use mk_Complex.
    - exact (AcyclicComplexFromObject_obs a i).
    - exact (AcyclicComplexFromObject_mors a i).
    - exact (AcyclicComplexFromObject_diff a i).
  Defined.

  (** *** Morphism from [AcyclicComplexFromObject] to a complex
                           ... -->   0   -->  X^i  -->  X^i   -->   0    -->   ...
                                     |         |         |          |
                           .. --> X^{i-1} --> X^i --> X^{i+1} --> X^{i+2} -->  ...
   *)

  Definition FromAcyclicComplexFromObject_mors {a : ob A} {C : Complex A} {i : hz}
             (f : a --> (C i)) : ∏ i0 : hz, A ⟦(AcyclicComplexFromObject a i) i0, C i0⟧.
  Proof.
    intros i0.
    unfold AcyclicComplexFromObject. unfold AcyclicComplexFromObject_obs.
    unfold AcyclicComplexFromObject_mors. cbn.
    unfold coprod_rect.
    induction (isdecrelhzeq i i0) as [e | n].
    + exact (transportf (precategory_morphisms a) (maponpaths C e) f).
    + induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      * exact (transportf (precategory_morphisms a) (maponpaths C e') (f · Diff C i)).
      * exact (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (C i0)).
  Defined.

  Local Lemma FromAcyclicComplexFromObject_comm_eq1 {a : ob A} {C : Complex A} {i : hz}
        (f : a --> (C i)) (i0 : hz) (e : i = i0) (e'' : (i + 1) = (i0 + 1)) :
    transportf (precategory_morphisms a) (maponpaths C e) f · Diff C i0 =
    identity a · transportf (precategory_morphisms a) (maponpaths C e'') (f · Diff C i).
  Proof.
    rewrite id_left. rewrite transport_target_postcompose.
    rewrite transport_compose. apply cancel_precomposition.
    rewrite <- maponpathsinv0.
    use (pathscomp0 (! (transport_hz_section A C 1 (Diff C) _ _ e))).
    use transportf_paths. apply maponpaths. apply isasethz.
  Qed.

  Local Lemma FromAcyclicComplexFromObject_comm_eq2 {a : ob A} {C : Complex A} {i : hz}
        (f : a --> (C i)) (i0 : hz) (e' : i + 1 = i0) :
    transportf (precategory_morphisms a) (maponpaths C e') (f · Diff C i) · Diff C i0 =
    (ZeroArrow (Additive.to_Zero A) a (Additive.to_Zero A))
      · (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) (C (i0 + 1))).
  Proof.
    rewrite ZeroArrow_comp_left.
    rewrite (transport_hz_source_target A C 1 (Diff C) _ _ (e')).
    rewrite transport_compose'. rewrite <- transport_target_postcompose.
    rewrite <- assoc. rewrite DSq. rewrite ZeroArrow_comp_right.
    rewrite transport_target_ZeroArrow. apply idpath.
  Qed.

  Local Lemma FromAcyclicComplexFromObject_comm {a : ob A} {C : Complex A} {i : hz}
        (f : a --> (C i)) :
    ∏ i0 : hz, (FromAcyclicComplexFromObject_mors f i0) · (Diff C i0) =
               (Diff (AcyclicComplexFromObject a i) i0)
                 · (FromAcyclicComplexFromObject_mors f (i0 + 1)).
  Proof.
    intros i0.
    unfold AcyclicComplexFromObject. unfold AcyclicComplexFromObject_obs.
    unfold AcyclicComplexFromObject_mors. unfold FromAcyclicComplexFromObject_mors.
    unfold coprod_rect. cbn.
    induction (isdecrelhzeq i i0) as [e | n].
    + induction (isdecrelhzeq i (i0 + 1)) as [e' | n'].
      * exact (fromempty (hzeqeisi e e')).
      * induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e'' | n''].
        -- exact (FromAcyclicComplexFromObject_comm_eq1 f i0 e e'').
        -- exact (fromempty (n'' (maponpaths (λ i' : hz, i' + 1) e))).
    + induction (isdecrelhzeq (i + 1) i0) as [e' | n'].
      * induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        -- exact (fromempty (hzeqsnmnsm e' e'')).
        -- induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e''' | n'''].
           ++ exact (fromempty (hzeqeisi e' e''')).
           ++ exact (FromAcyclicComplexFromObject_comm_eq2 f i0 e').
      * induction (isdecrelhzeq i (i0 + 1)) as [e'' | n''].
        -- rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. apply idpath.
        -- induction (isdecrelhzeq (i + 1) (i0 + 1)) as [e''' | n'''].
           ++ exact (fromempty (n (hzplusrcan i i0 1 e'''))).
           ++ rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. apply idpath.
  Qed.

  Definition FromAcyclicComplexFromObject {a : ob A} {C : Complex A} {i : hz} (f : a --> (C i)) :
    Morphism (AcyclicComplexFromObject a i) C.
  Proof.
    use mk_Morphism.
    - exact (FromAcyclicComplexFromObject_mors f).
    - exact (FromAcyclicComplexFromObject_comm f).
  Defined.

  (** *** Morphism from [AcyclicComplexFromObject] to a complex
                           .. --> X^{i-1} --> X^i --> X^{i+1} --> X^{i+2} -->  ...
                                     |         |         |          |
                           ... -->   0   -->  X^i  -->  X^i   -->   0    -->   ...
   *)

  Definition ToAcyclicComplexFromObject_mors {a : ob A} {C : Complex A} {i : hz}
             (f : (C i) --> a) : ∏ i0 : hz, A ⟦C i0, (AcyclicComplexFromObject a (i - 1)) i0⟧.
  Proof.
    intros i0.
    unfold AcyclicComplexFromObject. unfold AcyclicComplexFromObject_obs.
    unfold AcyclicComplexFromObject_mors. cbn.
    unfold coprod_rect.
    induction (isdecrelhzeq (i - 1) i0) as [e | n].
    - use compose.
      + exact (C i).
      + exact (transportf (λ x' : ob A, A⟦x', C i⟧) (maponpaths C e)
                          (transportf (precategory_morphisms (C (i - 1)))
                                      (maponpaths C (hzrminusplus i 1))
                                      (Diff C (i - 1)))).
      + exact f.
    - induction (isdecrelhzeq (i - 1 + 1) i0) as [e' | n'].
      + exact (transportf (λ x' : ob A, A⟦x', a⟧) (maponpaths C (! (hzrminusplus i 1) @ e')) f).
      + exact (ZeroArrow (Additive.to_Zero A) (C i0) (Additive.to_Zero A)).
  Defined.

  Local Lemma ToAcyclicComplexFromObject_mors_comm_eq1 {a : ob A} {C : Complex A} {i : hz}
        (f : C i --> a) (i0 : hz) (e : i - 1 = i0) (e'' : i - 1 + 1 = i0 + 1) :
    (transportf (λ x' : A, A ⟦ x', C i ⟧) (maponpaths C e)
                (transportf (precategory_morphisms (C (i - 1)))
                            (maponpaths C (hzrminusplus i 1)) (Diff C (i - 1))))
      · f · identity a =
    Diff C i0 · transportf (λ x' : A, A ⟦ x', a ⟧) (maponpaths C (! hzrminusplus i 1 @ e'')) f.
  Proof.
    rewrite id_right. rewrite <- (pathsinv0inv0 (! hzrminusplus i 1 @ e'')).
    rewrite maponpathsinv0. rewrite <- transport_compose.
    apply cancel_postcomposition. rewrite transport_source_target_comm.
    induction e. use transportf_paths. apply maponpaths. apply isasethz.
  Qed.

  Local Lemma ToAcyclicComplexFromObject_mors_comm_eq2 {a : ob A} {C : Complex A} {i : hz}
        (f : (C i) --> a) (i0 : hz) (e' : i - 1 = i0 + 1) :
    (ZeroArrow (Additive.to_Zero A) (C i0) (Additive.to_Zero A))
      · (ZeroArrow (Additive.to_Zero A) (Additive.to_Zero A) a) =
    Diff C i0 · (transportf (λ x' : A, A ⟦ x', C i ⟧) (maponpaths C e')
                             (transportf (precategory_morphisms (C (i - 1)))
                                         (maponpaths C (hzrminusplus i 1))
                                         (Diff C (i - 1))) · f).
  Proof.
    rewrite ZeroArrow_comp_left. rewrite assoc.
    rewrite <- (pathsinv0inv0 e'). rewrite maponpathsinv0.
    rewrite <- transport_compose.
    rewrite <- (ZeroArrow_comp_left _ _ _ _ _ f). apply cancel_postcomposition.
    use (transport_target_path _ _ (! maponpaths C (hzrminusplus i 1))).
    rewrite <- transport_target_postcompose. rewrite transport_f_f.
    rewrite pathsinv0r. rewrite transport_target_ZeroArrow.
    use (transport_target_path _ _ (maponpaths C (hzplusradd _ _ 1 e'))).
    rewrite transport_target_ZeroArrow. rewrite transport_f_f. cbn.
    rewrite <- (DSq A C i0). rewrite transport_compose.
    rewrite transport_target_postcompose. apply cancel_precomposition.
    use (pathscomp0 (transport_hz_source_target A _ 1 (Diff C) _ _ e')).
    rewrite transport_source_target_comm.
    rewrite maponpathsinv0. rewrite pathsinv0inv0.
    apply idpath.
  Qed.

  Local Lemma ToAcyclicComplexFromObject_mors_comm {a : ob A} {C : Complex A} {i : hz}
        (f : (C i) --> a) :
    ∏ i0 : hz, (ToAcyclicComplexFromObject_mors f i0)
                 · (Diff (AcyclicComplexFromObject a (i - 1)) i0) =
               (Diff C i0) · (ToAcyclicComplexFromObject_mors f (i0 + 1)).
  Proof.
    intros i0.
    unfold AcyclicComplexFromObject. unfold AcyclicComplexFromObject_obs.
    unfold AcyclicComplexFromObject_mors. cbn.
    unfold ToAcyclicComplexFromObject_mors. unfold coprod_rect. cbn.
    induction (isdecrelhzeq (i - 1) i0) as [e | n].
    - induction (isdecrelhzeq (i - 1) (i0 + 1)) as [e' | n'].
      + exact (fromempty (hzeqeisi e e')).
      + induction (isdecrelhzeq (i - 1 + 1) (i0 + 1)) as [e'' | n''].
        * exact (ToAcyclicComplexFromObject_mors_comm_eq1 f i0 e e'').
        * exact (fromempty (hzeqnmplusr e n'')).
    - induction (isdecrelhzeq (i - 1) (i0 + 1)) as [e' | n'].
      + induction (isdecrelhzeq (i - 1 + 1) (i0 + 1)) as [e'' | n''].
        * induction (isdecrelhzeq (i - 1 + 1) i0) as [e''' | n'''].
          -- exact (fromempty (hzeqsnmnsm e''' e')).
          -- exact (ToAcyclicComplexFromObject_mors_comm_eq2 f i0 e').
        * induction (isdecrelhzeq (i - 1 + 1) i0) as [e''' | n'''].
          -- exact (fromempty (hzeqsnmnsm e''' e')).
          -- exact (ToAcyclicComplexFromObject_mors_comm_eq2 f i0 e').
      + induction (isdecrelhzeq (i - 1 + 1) i0) as [e''' | n'''].
        * induction (isdecrelhzeq (i - 1 + 1) (i0 + 1)) as [e'''' | n''''].
          -- exact (fromempty (hzeqeisi e''' e'''')).
          -- rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. apply idpath.
        * induction (isdecrelhzeq (i - 1 + 1) (i0 + 1)) as [e'''' | n''''].
          -- exact (fromempty (hzeqnmplusr' n e'''')).
          -- rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Definition ToAcyclicComplexFromObject {a : ob A} {C : Complex A} {i : hz} (f : (C i) --> a) :
    Morphism C (AcyclicComplexFromObject a (i - 1)).
  Proof.
    use mk_Morphism.
    - exact (ToAcyclicComplexFromObject_mors f).
    - exact (ToAcyclicComplexFromObject_mors_comm f).
  Defined.


  (** Some equalities *)
  Lemma FromAcyclicComplexFromObject_Eq {a : ob A} {C : Complex A} (i0 : hz) {i : hz}
        (f : a --> (C i)) :
    FromAcyclicComplexFromObject f i0 = FromAcyclicComplexFromObject_mors f i0.
  Proof.
    apply idpath.
  Qed.

  Lemma ToAcyclicComplexFromObject_Eq {a : ob A} {C : Complex A} (i0 : hz) {i : hz}
        (f : (C i) --> a) :
    ToAcyclicComplexFromObject f i0 = ToAcyclicComplexFromObject_mors f i0.
  Proof.
    apply idpath.
  Qed.

End acyclic_complexes.



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
    tpair (λ ob : UU, ob -> ob -> UU) (Complex A) (λ C1 C2 : Complex A, Morphism C1 C2).

  Definition ComplexPreCat_data : precategory_data :=
    precategory_data_pair
      ComplexPreCat_ob_mor (λ (C : Complex A), IdMor C)
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
        (H : g · (MMor (MonicArrow _ M) i) = h · (MMor (MonicArrow _ M) i)) :
    FromAcyclicComplexFromObject_mors A g i = FromAcyclicComplexFromObject_mors A h i.
  Proof.
    use (pathscomp0 (! (FromAcyclicComplexFromObject_Eq A i g))).
    use (pathscomp0 _ (FromAcyclicComplexFromObject_Eq A i h)).
    use MorphismEq'.
    use (MonicisMonic ComplexPreCat M). cbn.
    use MorphismEq.
    intros i0. cbn.
    unfold FromAcyclicComplexFromObject_mors. unfold coprod_rect.
    unfold AcyclicComplexFromObject_obs. cbn.
    induction (isdecrelhzeq i i0) as [T | F].
    - induction T. exact H.
    - induction (isdecrelhzeq (i + 1) i0) as [T' | F'].
      + induction T'. cbn. unfold idfun. rewrite <- assoc. rewrite <- assoc. rewrite <- MComm.
        rewrite assoc. rewrite assoc. apply cancel_postcomposition.
        exact H.
      + apply idpath.
  Qed.

  Lemma ComplexMonicIndexMonic {C1 C2 : Complex A} (M : Monic ComplexPreCat C1 C2) :
    ∏ i : hz, isMonic (@MMor A C1 C2 (MonicArrow _ M) i).
  Proof.
    intros i a g h H.
    set (tmp := ComplexMonicIndexMonic_eq M i g h H).
    unfold FromAcyclicComplexFromObject_mors in tmp. cbn in tmp.
    unfold coprod_rect in tmp. unfold AcyclicComplexFromObject_obs in tmp.
    unfold paths_rect in tmp. cbn in tmp.
    rewrite (isdecrelhzeqi i) in tmp.
    exact tmp.
  Qed.

  Lemma ComplexMonicIndexMonic' {C1 C2 : Complex A} (f : Morphism C1 C2)
        (H : ∏ i : hz, isMonic (f i)) : isMonic (f : ComplexPreCat⟦_, _⟧).
  Proof.
    use mk_isMonic.
    intros x g h X.
    use MorphismEq. intros i.
    set (tmp := MorphismEq' A _ _ X i). cbn in tmp. apply (H i) in tmp.
    exact tmp.
  Qed.

  (** ** Epi of complexes is indexwise epi *)

  Local Lemma ComplexEpiIndexEpi_eq {C1 C2 : Complex A} (E : Epi ComplexPreCat C1 C2) (i : hz)
        {a : A} (g h : A ⟦C2 i, a⟧)
        (H : (MMor (EpiArrow _ E) i) · g = (MMor (EpiArrow _ E) i) · h) :
    ToAcyclicComplexFromObject_mors A g i = ToAcyclicComplexFromObject_mors A h i.
  Proof.
    use (pathscomp0 (! (ToAcyclicComplexFromObject_Eq A i g))).
    use (pathscomp0 _ (ToAcyclicComplexFromObject_Eq A i h)).
    use MorphismEq'.
    use (EpiisEpi ComplexPreCat E). cbn.
    use MorphismEq.
    intros i0. cbn.
    unfold ToAcyclicComplexFromObject_mors. unfold coprod_rect.
    unfold AcyclicComplexFromObject_obs. cbn.
    induction (isdecrelhzeq (i - 1) i0) as [T | F].
    - rewrite <- transport_source_precompose. rewrite <- transport_source_precompose.
      rewrite <- (pathsinv0inv0 T). rewrite maponpathsinv0.
      rewrite <- transport_compose. rewrite <- transport_compose.
      rewrite assoc. rewrite assoc.
      rewrite <- transport_target_postcompose.
      assert (e : (transportf (precategory_morphisms (C1 i0)) (maponpaths C2 (! T))
                              (MMor (EpiArrow _ E) i0)) · Diff C2 (i - 1) =
                  (Diff C1 i0) · (transportf (precategory_morphisms (C1 (i0 + 1)))
                                              (maponpaths C2 (hzplusradd i0 (i - 1) 1 (! T)))
                                              (MMor (EpiArrow _ E) (i0 + 1)))).
      {
        rewrite <- transport_target_postcompose. rewrite <- MComm.
        rewrite transport_target_postcompose. induction T. apply idpath.
      }
      cbn in e. cbn. rewrite e. clear e.
      rewrite transport_target_postcompose.
      rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
      rewrite transport_f_f. rewrite <- maponpathscomp0.
      use (@transport_source_path
             A (C1 i) (C1 (i0 + 1)) a _ _
             (maponpaths C1 (hzplusradd i0 (i - 1) 1 (! T) @ hzrminusplus i 1))).
      rewrite transport_source_precompose. rewrite transport_source_precompose.
      rewrite transport_source_target_comm.
      set (tmp''' := transport_hz_double_section_source_target
                       A _ _ (MMor (EpiArrow _ E)) _ _
                       (hzplusradd i0 (i - 1) 1 (! T) @ hzrminusplus i 1)).
      cbn in tmp'''. cbn. rewrite <- tmp'''. clear tmp'''.
      exact H.
    - induction (isdecrelhzeq (i - 1 + 1) i0) as [e' | n'].
      + rewrite <- (pathsinv0inv0 e'). rewrite <- pathscomp_inv. rewrite maponpathsinv0.
        rewrite <- transport_compose. rewrite <- transport_compose.
        use (@transport_source_path
               A (C1 i) (C1 i0) a _ _ (maponpaths C1 (! e' @ hzrminusplus i 1))).
        rewrite transport_source_precompose. rewrite transport_source_precompose.
        rewrite transport_source_target_comm.
        set (tmp''' := transport_hz_double_section_source_target
                         A _ _ (MMor (EpiArrow _ E)) _ _
                         (! e' @ hzrminusplus i 1)).
        cbn in tmp'''. cbn. rewrite <- tmp'''. clear tmp'''.
        exact H.
      + apply idpath.
  Qed.

  Lemma ComplexEpiIndexEpi {C1 C2 : Complex A} (E : Epi ComplexPreCat C1 C2) :
    ∏ i : hz, isEpi (@MMor A C1 C2 (EpiArrow _ E) i).
  Proof.
    intros i a g h H.
    set (tmp := ComplexEpiIndexEpi_eq E i g h H).
    unfold ToAcyclicComplexFromObject_mors in tmp. cbn in tmp.
    unfold coprod_rect in tmp. unfold AcyclicComplexFromObject_obs in tmp. cbn in tmp.
    rewrite (isdecrelhzeqpii i) in tmp.
    rewrite (isdecrelhzeqminusplus' i) in tmp.
    rewrite pathsinv0l in tmp.
    exact tmp.
  Qed.

  Lemma ComplexEpiIndexEpi' {C1 C2 : Complex A} (f : Morphism C1 C2)
        (H : ∏ i : hz, isEpi (f i)) : isEpi (f : ComplexPreCat⟦_, _⟧).
  Proof.
    use mk_isEpi.
    intros z g h X.
    use MorphismEq. intros i.
    set (tmp := MorphismEq' A _ _ X i). cbn in tmp. apply (H i) in tmp.
    exact tmp.
  Qed.

  (** ** An morphism in complexes is an isomorphism if it is so indexwise *)

  Lemma ComplexIsoIndexIso {C1 C2 : Complex A} (f : ComplexPreCat⟦C1, C2⟧)
        (H : ∏ (i : hz), is_iso (MMor f i)) : is_iso f.
  Proof.
    use is_iso_qinv.
    - use mk_Morphism.
      + intros i. exact (iso_inv_from_is_iso _ (H i)).
      + intros i. cbn.
        use (post_comp_with_iso_is_inj _ _ _ _ (H (i + 1))).
        use (pre_comp_with_iso_is_inj _ _ _ _ _ (H i)).
        assert (e0 : MMor f i · inv_from_iso (MMor f i,, H i) = identity _).
        {
          apply (iso_inv_after_iso (isopair _ (H i))).
        }
        rewrite assoc. rewrite assoc. rewrite e0. rewrite id_left.
        rewrite <- (MComm f i). apply cancel_precomposition.
        assert (e1 : inv_from_iso (MMor f (i + 1),, H (i + 1)) · MMor f (i + 1) = identity _).
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
   We give the category of complexes over an additive category a natural structure as an additive
   category. Addition of morphisms is given by indexwise addition, [MorphismOp], [ZeroComplex] is a
   zero object, which is shown to be zero in [ComplexPreCat_isZero], and binary direct sums are
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

  Definition ComplexPreCat_categoryWithAbgrops : categoryWithAbgrops.
  Proof.
    use mk_categoryWithAbgrops.
    - exact ComplexPreCat_precategoryWithBinOps.
    - exact (has_homsets_ComplexPreCat A).
    - intros x y. exact (MorphismOp_isabgrop A x y).
  Defined.

  Lemma ComplexPreCat_isPreAdditive : isPreAdditive ComplexPreCat_categoryWithAbgrops.
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
    - exact ComplexPreCat_categoryWithAbgrops.
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

  Lemma ComplexPreCat_isBinCoproduct (C1 C2 : Complex A) :
    isBinCoproduct ComplexPreCat_PreAdditive C1 C2 (DirectSumComplex A C1 C2)
                         (DirectSumComplexIn1 A C1 C2) (DirectSumComplexIn2 A C1 C2).
  Proof.
    use mk_isBinCoproduct.
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

  Lemma ComplexPreCat_isBinProduct (C1 C2 : Complex A) :
    isBinProduct ComplexPreCat_PreAdditive C1 C2 (DirectSumComplex A C1 C2)
                     (DirectSumComplexPr1 A C1 C2) (DirectSumComplexPr2 A C1 C2).
  Proof.
    use mk_isBinProduct.
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

  Lemma ComplexPreCat_isBinDirectSum (C1 C2 : Complex A) :
    isBinDirectSum
      ComplexPreCat_PreAdditive C1 C2 (DirectSumComplex A C1 C2) (DirectSumComplexIn1 A C1 C2)
      (DirectSumComplexIn2 A C1 C2) (DirectSumComplexPr1 A C1 C2) (DirectSumComplexPr2 A C1 C2).
  Proof.
    use mk_isBinDirectSum.
    - exact (ComplexPreCat_isBinCoproduct C1 C2).
    - exact (ComplexPreCat_isBinProduct C1 C2).
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
        use (mk_BinDirectSum ComplexPreCat_PreAdditive).
        * exact (DirectSumComplex A C1 C2).
        * exact (DirectSumComplexIn1 A C1 C2).
        * exact (DirectSumComplexIn2 A C1 C2).
        * exact (DirectSumComplexPr1 A C1 C2).
        * exact (DirectSumComplexPr2 A C1 C2).
        * exact (ComplexPreCat_isBinDirectSum C1 C2).
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
        (i : hz) : (KernelArrow (Kernel (g i))) · (Diff Y i) · (g (i + 1)) =
                   ZeroArrow (to_Zero A) (Kernel (g i)) (Z (i + 1)).
  Proof.
    rewrite <- assoc. cbn. set (tmp := MComm g i). cbn in tmp. rewrite <- tmp. clear tmp.
    rewrite assoc. rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Local Lemma ComplexPreCat_Kernel_comp {Y Z : Complex (AbelianToAdditive A hs)} (g : Morphism Y Z)
        (i : hz) :
    (KernelIn (to_Zero A) (Kernel (g (i + 1))) (Kernel (g i))
              ((KernelArrow (Kernel (g i))) · (Diff Y i))
              (ComplexPreCat_Kernel_moreq g i))
      · (KernelIn (to_Zero A) (Kernel (g (i + 1 + 1))) (Kernel (g (i + 1)))
                   ((KernelArrow (Kernel (g (i + 1)))) · (Diff Y (i + 1)))
                   (ComplexPreCat_Kernel_moreq g (i + 1))) =
    ZeroArrow (to_Zero A) (Kernel (g i)) (Kernel (g (i + 1 + 1))).
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
      + exact (KernelArrow (Kernel (g i)) · Diff Y i).
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

  Local Lemma ComplexPreCat_KernelIn_comp {X Y w : Complex (AbelianToAdditive A hs)}
        (g : Morphism X Y) (h : Morphism w X) (i : hz) :
    let Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)) in
    MorphismComp h g = ZeroArrow Z w Y ->
    (h i) · (g i) = ZeroArrow (to_Zero A) (w i) (Y i).
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
    (* Composition KernelArrow · g = ZeroArrow *)
    - exact (ComplexPreCat_Kernels_comp f).
    (* isEqualizer property *)
    - exact (ComplexPreCat_Kernels_isKernel f).
  Defined.


  (** ** Cokernels in Complexes over Abelian *)

  (** *** Cokernel complex *)
  Local Lemma ComplexPreCat_Cokernel_comm {Y Z : Complex (AbelianToAdditive A hs)}
        (g : Morphism Y Z) (i : hz) :
    (g i) · ((Diff Z i) · (CokernelArrow (Cokernel (g (i + 1))))) =
    ZeroArrow (to_Zero A) (Y i) (Cokernel (g (i + 1))).
  Proof.
    rewrite assoc. cbn. set (tmp := MComm g i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite <- assoc. rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Local Lemma ComplexPreCat_Cokernel_comp {Y Z : Complex (AbelianToAdditive A hs)}
        (g : Morphism Y Z) (i : hz) :
    (CokernelOut (to_Zero A) (Cokernel (g i)) (Cokernel (g (i + 1)))
                 ((Diff Z i) · (CokernelArrow (Cokernel (g (i + 1)))))
                 (ComplexPreCat_Cokernel_comm g i))
      · (CokernelOut (to_Zero A) (Cokernel (g (i + 1))) (Cokernel (g (i + 1 + 1)))
                      ((Diff Z (i + 1)) · (CokernelArrow (Cokernel (g (i + 1 + 1)))))
                      (ComplexPreCat_Cokernel_comm g (i + 1))) =
    ZeroArrow (to_Zero A) (Cokernel (g i)) (Cokernel (g (i + 1 + 1))).
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
      + exact ((Diff Z i) · (CokernelArrow (Cokernel (g (i + 1))))).
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
    g · h = ZeroArrow Z0 Y w -> (MMor g i) · (MMor h i) = ZeroArrow (to_Zero A) (Y i) (w i).
  Proof.
    intros Z0. cbn. intros H. set (tmp := MorphismEq' _ (g · h) _ H i). cbn in tmp.
    rewrite tmp. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexPreCat_Cokernels_Eq {Y Z w : Complex (AbelianToAdditive A hs)}
        (g : (ComplexPreCat (AbelianToAdditive A hs))⟦Y, Z⟧)
        (h : (ComplexPreCat (AbelianToAdditive A hs))⟦Z, w⟧)
        (H : g · h =
             ZeroArrow (Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))) Y w)
        (i : hz) :
    (CokernelOut (to_Zero A) (Cokernel (MMor g i)) (w i) (MMor h i)
                 (ComplexPreCat_CokernelCompZero g h i H)) · (Diff w i) =
    (CokernelOut (to_Zero A) (Cokernel (MMor g i)) (Cokernel (MMor g (i + 1)))
                 ((Diff Z i) · (CokernelArrow (Cokernel (MMor g (i + 1)))))
                 (ComplexPreCat_Cokernel_comm g i))
      · (CokernelOut (to_Zero A) (Cokernel (MMor g (i + 1)))
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
    - exact (ComplexPreCat_CokernelArrow g).
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
      · ((Diff y i) · (CokernelArrow (Cokernel (MMor (MonicArrow _ M) (i + 1))))) =
    ZeroArrow (to_Zero A) _ (Cokernel (MMor (MonicArrow _ M) (i + 1))).
  Proof.
    rewrite assoc. rewrite (MComm (MonicArrow _ M)). rewrite <- assoc.
    rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Local Lemma ComplexPreCat_Monic_Kernel_Complex_comp
    {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (M : Monic (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) (i : hz) :
    (CokernelOut (to_Zero A) (Cokernel (MMor (MonicArrow _ M) i))
                 (Cokernel (MMor (MonicArrow _ M) (i + 1)))
                 ((Diff y i) · (CokernelArrow (Cokernel (MMor (MonicArrow _ M) (i + 1)))))
                 (ComplexPreCat_Monic_Kernel_Complex_comm M i))
      · (CokernelOut (to_Zero A) (Cokernel (MMor (MonicArrow _ M) (i + 1)))
                      (Cokernel (MMor (MonicArrow _ M) (i + 1 + 1)))
                      ((Diff y (i + 1))
                         · (CokernelArrow (Cokernel (MMor (MonicArrow _ M) (i + 1 + 1)))))
                      (ComplexPreCat_Monic_Kernel_Complex_comm M (i + 1))) =
    ZeroArrow (to_Zero A) (Cokernel (MMor (MonicArrow _ M) i))
              (Cokernel (MMor (MonicArrow _ M) (i + 1 + 1))).
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
      + exact ((Diff y i) · (CokernelArrow (Cokernel (@MMor _ x y (MonicArrow _ M) (i + 1))))).
      + use ComplexPreCat_Monic_Kernel_Complex_comm.
    - intros i. cbn. exact (ComplexPreCat_Monic_Kernel_Complex_comp M i).
  Defined.

  Local Lemma KernelMorphism_eq {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y)
        (Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))) :
    MorphismComp
      (MonicArrow _ M) (ComplexPreCat_CokernelArrow ((MonicArrow _ M) : Morphism _ _)) =
    ZeroMorphism _ _ _.
  Proof.
    use MorphismEq. intros i. use CokernelCompZero.
  Qed.

  Local Lemma ComplexMonicKernelInComm {x y : Complex (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
        {w : ComplexPreCat (AbelianToAdditive A hs)}
        (h : (ComplexPreCat (AbelianToAdditive A hs))⟦w, y⟧) (i : hz)
        (Z := @Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)))
        (H : h · (ComplexPreCat_CokernelArrow (MonicArrow _ M)) = ZeroArrow Z _ _) :
    (MMor h i) · (CokernelArrow (Cokernel (MMor (MonicArrow _ M) i))) =
    ZeroArrow (to_Zero A) _ (Cokernel (MMor (MonicArrow _ M) i)).
  Proof.
    set (H' := MorphismEq' _ _ _ H i). cbn in H'. cbn. rewrite H'. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexMonicKernelIn_Complex_Comm {x y w : Complex (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
        (h : (ComplexPreCat (AbelianToAdditive A hs))⟦w, y⟧) (i : hz)
        (Z := @Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)))
        (H : h · (ComplexPreCat_CokernelArrow (MonicArrow _ M)) = ZeroArrow Z _ _) :
    (KernelIn
       (to_Zero A)
       (MonicToKernel (mk_Monic A (MMor (MonicArrow _ M) i) ((ComplexMonicIndexMonic _ M) i)))
       (w i) (MMor h i) (ComplexMonicKernelInComm M h i H)) · (Diff x i) =
    (Diff w i)
      · (KernelIn
            (to_Zero A)
            (MonicToKernel (mk_Monic A (MMor (MonicArrow _ M) (i + 1))
                                     ((ComplexMonicIndexMonic _ M) (i + 1))))
            (w (i + 1)) (MMor h (i + 1)) (ComplexMonicKernelInComm M h (i + 1) H)).
  Proof.
    set (isM := ComplexMonicIndexMonic _ M).
    set (ker := MonicToKernel (mk_Monic _ _ (isM (i + 1)))).
    cbn in *. apply (KernelArrowisMonic _ ker).
    rewrite <- assoc. rewrite <- assoc. fold ker.
    rewrite (KernelCommutes _ ker). cbn. use (pathscomp0 _ (MComm h i)).
    set (tmp := MComm (MonicArrow _ M) i). cbn in tmp. rewrite <- tmp. clear tmp.
    rewrite assoc. apply cancel_postcomposition.
    apply (KernelCommutes _ (MonicToKernel (mk_Monic A _ (isM i))) (w i) (MMor h i)).
  Qed.

  Definition ComplexMonicKernelIn {x y : Complex (AbelianToAdditive A hs)}
             (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
             {w : ComplexPreCat (AbelianToAdditive A hs)}
             (h : (ComplexPreCat (AbelianToAdditive A hs))⟦w, y⟧)
             (Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))) :
    h · (ComplexPreCat_CokernelArrow (MonicArrow _ M)) = ZeroArrow Z _ _  ->
    (ComplexPreCat (AbelianToAdditive A hs))⟦w, x⟧.
  Proof.
    intros H'.
    set (isM := ComplexMonicIndexMonic _ M).
    use mk_Morphism.
    - intros i.
      exact (KernelIn (to_Zero A) (MonicToKernel (mk_Monic _ _ (isM i))) _ (MMor h i)
                      (ComplexMonicKernelInComm M h i H')).
    - intros i. exact (ComplexMonicKernelIn_Complex_Comm M h i H').
  Defined.

  Local Lemma KernelMorphism_eq' {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
        (Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))):
    M ·  (CokernelArrow (ComplexPreCat_Cokernels x y M)) =
    ZeroArrow Z x (ComplexPreCat_Cokernels x y M).
  Proof.
    cbn. rewrite KernelMorphism_eq. apply ComplexPreCat_ZeroArrow_ZeroMorphism.
  Qed.

  Definition ComplexPreCatAbelianMonicKernelsData_isKernel
             {x y : Complex (AbelianToAdditive A hs)}
             (M : Monic (ComplexPreCat (AbelianToAdditive A hs)) x y)
             (Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))) :
    @isKernel (ComplexPreCat (AbelianToAdditive A hs)) _ _ _ _ M
              (ComplexPreCat_CokernelArrow (MonicArrow _ M))
              (CokernelCompZero Z (ComplexPreCat_Cokernels _ _ (MonicArrow _ M))).
  Proof.
    set (isM := ComplexMonicIndexMonic _ M).
    use (mk_isKernel (has_homsets_ComplexPreCat (AbelianToAdditive A hs))).
    intros w h H'.
    use unique_exists.
    - apply (ComplexMonicKernelIn M h H').
    - cbn. use MorphismEq.
      intros i. cbn.
      apply (KernelCommutes _ (MonicToKernel (mk_Monic A _ (isM i))) _ (MMor h i)).
    - intros y0. apply has_homsets_ComplexPreCat.
    - intros y0 T. cbn in T.
      use MorphismEq.
      intros i. apply (isM i).
      set (tmp :=  MorphismEq' _ _ _ T i). cbn in tmp. cbn. rewrite tmp.
      apply pathsinv0. clear tmp.
      apply (KernelCommutes _ (MonicToKernel (mk_Monic A _ (isM i))) _ (MMor h i)).
  Qed.

  (** ** Epis are Cokernels of kernels *)

  Local Lemma ComplexPreCat_Epi_Cokernel_Complex_comm
        {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) (i : hz) :
    (KernelArrow (Kernel (MMor (EpiArrow _ E) i))) · (Diff x i) · (MMor (EpiArrow _ E) (i + 1)) =
    ZeroArrow (to_Zero A) (Kernel (MMor (EpiArrow _ E) i)) _.
  Proof.
    rewrite <- assoc. rewrite <- (MComm (EpiArrow _ E)). rewrite assoc.
    rewrite KernelCompZero. apply ZeroArrow_comp_left.
  Qed.

  Local Lemma ComplexPreCat_Epi_Cokernel_Complex_comp
        {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y) (i : hz) :
    (KernelIn (to_Zero A) (Kernel (MMor (EpiArrow _ E) (i + 1))) (Kernel (MMor (EpiArrow _ E) i))
              ((KernelArrow (Kernel (MMor (EpiArrow _ E) i))) · (Diff x i))
              (ComplexPreCat_Epi_Cokernel_Complex_comm E i))
      · (KernelIn (to_Zero A) (Kernel (MMor (EpiArrow _ E) (i + 1 + 1)))
                   (Kernel (MMor (EpiArrow _ E) (i + 1)))
                   ((KernelArrow (Kernel (MMor (EpiArrow _ E) (i + 1)))) · (Diff x (i + 1)))
                   (ComplexPreCat_Epi_Cokernel_Complex_comm E (i + 1))) =
    ZeroArrow (to_Zero A) (Kernel (MMor (EpiArrow _ E) i))
              (Kernel (MMor (EpiArrow _ E) (i + 1 + 1))).
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
      + exact ((KernelArrow (Kernel (@MMor _ x y (EpiArrow _ E) i))) · (Diff x i)).
      + apply ComplexPreCat_Epi_Cokernel_Complex_comm.
    - intros i. exact (ComplexPreCat_Epi_Cokernel_Complex_comp E i).
  Defined.

  Definition CokernelMorphism_eq {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
             (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y)
             (Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))) :
    MorphismComp (ComplexPreCat_KernelArrow ((EpiArrow _ E) : Morphism _ _)) (EpiArrow _ E) =
    ZeroMorphism _ _ _.
  Proof.
    use MorphismEq. intros i. use KernelCompZero.
  Qed.

  Local Lemma ComplexPreCatCokernelOut_comp
    {x y w0 : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y)
    (h : (ComplexPreCat (AbelianToAdditive A hs))⟦x, w0⟧) (i : hz)
    (Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)))
    (H : MorphismComp (ComplexPreCat_KernelArrow ((EpiArrow _ E) : Morphism _ _)) h =
         ZeroArrow Z _ _) :
    KernelArrow (Kernel (MMor (EpiArrow _ E) i)) · MMor h i =
    ZeroArrow (to_Zero A) (Kernel (MMor (EpiArrow _ E) i)) _.
  Proof.
    set (H' := MorphismEq' _ _ _ H i). cbn in H'. cbn. rewrite H'. apply ZeroArrowEq.
  Qed.

  Local Lemma ComplexPreCatCokernelOut_comm
    {x y w0 : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y) (i : hz)
    (h : (ComplexPreCat (AbelianToAdditive A hs))⟦x, w0⟧)
    (Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)))
    (H : MorphismComp (ComplexPreCat_KernelArrow ((EpiArrow _ E) : Morphism _ _)) h =
         ZeroArrow Z _ _)
    (isE := ComplexEpiIndexEpi _ E) :
    (CokernelOut (to_Zero A)
                 (EpiToCokernel (mk_Epi A (MMor (EpiArrow _ E) i) (isE i))) _ (MMor h i)
                 (ComplexPreCatCokernelOut_comp E h i H)) · (Diff w0 i) =
    (Diff y i)
      · (CokernelOut (to_Zero A)
                      (EpiToCokernel (mk_Epi A (MMor (EpiArrow _ E) (i + 1)) (isE (i + 1))))
                      _ (MMor h (i + 1)) (ComplexPreCatCokernelOut_comp E h (i + 1) H)).
  Proof.
    apply pathsinv0.
    set (coker := EpiToCokernel (mk_Epi _ _ (isE i))).
    apply (CokernelArrowisEpi _ coker). rewrite assoc. rewrite assoc. rewrite CokernelCommutes.
    use (pathscomp0 _ (! (MComm h i))). cbn.
    set (tmp := MComm (EpiArrow _ E) i). cbn in tmp. rewrite tmp. clear tmp.
    rewrite <- assoc. apply cancel_precomposition.
    apply (CokernelCommutes _ (EpiToCokernel (mk_Epi A _ (isE (i + 1))))).
  Qed.

  Definition ComplexPreCatCokernelOut
    {x y z : ComplexPreCat_Additive (AbelianToAdditive A hs)}
    (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y)
    (h : (ComplexPreCat (AbelianToAdditive A hs))⟦x, z⟧)
    (Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs)))
    (H : MorphismComp (ComplexPreCat_KernelArrow ((EpiArrow _ E) : Morphism _ _)) h =
         ZeroArrow Z _ _) :
    (ComplexPreCat (AbelianToAdditive A hs))⟦y, z⟧.
  Proof.
    set (isE := ComplexEpiIndexEpi _ E).
    use mk_Morphism.
    - intros i. exact (CokernelOut
                         (to_Zero A) (EpiToCokernel (mk_Epi _ _ (isE i))) _ (MMor h i)
                         (ComplexPreCatCokernelOut_comp E h i H)).
    - intros i. exact (ComplexPreCatCokernelOut_comm E i h H).
  Defined.

  (** *** EpisCokernelsData *)

  Local Lemma CokernelMorphism_eq' {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (E : Epi (ComplexPreCat (AbelianToAdditive A hs)) x y)
        (Z := Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))) :
    KernelArrow (ComplexPreCat_Kernels x y E) · E =
    ZeroArrow Z (ComplexPreCat_Kernels x y E) y.
  Proof.
    cbn. rewrite CokernelMorphism_eq. apply ComplexPreCat_ZeroArrow_ZeroMorphism.
  Qed.

  Local Lemma ComplexPreCatAbelianEpiCokernelsData_isCokernel
        {x y : ComplexPreCat_Additive (AbelianToAdditive A hs)}
        (E : Epi (ComplexPreCat_Additive (AbelianToAdditive A hs)) x y)
        (Add := ComplexPreCat_Additive (AbelianToAdditive A hs)) :
    @isCokernel Add _ _ _ _ (KernelArrow (ComplexPreCat_Kernels _ _ E)) E (CokernelMorphism_eq' E).
  Proof.
    set (isE := ComplexEpiIndexEpi (AbelianToAdditive A hs) E).
    use (mk_isCokernel (has_homsets_ComplexPreCat (AbelianToAdditive A hs))).
    intros w0 h H'.
    use unique_exists.
    - apply (ComplexPreCatCokernelOut E h H').
    - cbn. use MorphismEq.
      intros i. cbn.
      apply (CokernelCommutes _ (EpiToCokernel (mk_Epi A _ (isE i))) _ (MMor h i)).
    - intros y0. apply has_homsets_ComplexPreCat.
    - intros y0 T. cbn in T.
      use MorphismEq.
      intros i. apply (isE i).
      set (tmp :=  MorphismEq' _ _ _ T i). cbn in tmp. cbn. rewrite tmp.
      apply pathsinv0. clear tmp.
      apply (CokernelCommutes _ (EpiToCokernel (mk_Epi A _ (isE i))) _ (MMor h i)).
  Qed.

  (** ** Complexes over Abelian is Abelian *)

  Definition ComplexPreCat_AbelianPreCat : AbelianPreCat.
  Proof.
    use mk_Abelian.
    - exact (ComplexPreCat_Additive (AbelianToAdditive A hs)).
    - use mk_Data1.
      + exact (Additive.to_Zero (ComplexPreCat_Additive (AbelianToAdditive A hs))).
      + exact (Additive.to_BinProducts (ComplexPreCat_Additive (AbelianToAdditive A hs))).
      + exact (Additive.to_BinCoproducts (ComplexPreCat_Additive (AbelianToAdditive A hs))).
    - use mk_AbelianData.
      + use mk_Data2.
        * exact ComplexPreCat_Kernels.
        * exact ComplexPreCat_Cokernels.
      + use mk_MonicsAreKernels.
        intros x y M. cbn.
        exact (ComplexPreCatAbelianMonicKernelsData_isKernel M).
      + use mk_EpisAreCokernels.
        intros x y E. cbn.
        exact (ComplexPreCatAbelianEpiCokernelsData_isCokernel E).
  Defined.

  Lemma has_homsets_ComplexPreCat_AbelianPreCat : has_homsets ComplexPreCat_AbelianPreCat.
  Proof.
    apply has_homsets_ComplexPreCat.
  Qed.

End complexes_abelian.



(** * Transport binary direct sums *)
Section transport_hz_toBinDirectSums.

  Context {A : Additive}.

  Lemma transport_to_BinDirectSums (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    @maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i0)) _ _ e =
    (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i')) _ _ e)
      @ (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i) (f' i0)) _ _ e).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_to_BinDirectSums_comm (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i')) _ _ e)
      @ (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i) (f' i0)) _ _ e) =
    (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i') (f' i0)) _ _ e)
      @ (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i)) _ _ e).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_In1 (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    to_In1 A (to_BinDirectSums A (f i) (f' i)) =
    transportf (precategory_morphisms (f i))
               (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i0)) _ _ e)
               (transportf (λ (x : ob A), A⟦x, to_BinDirectSums A (f i') (f' i')⟧)
                           (maponpaths f e) (to_In1 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_In1' (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    transportf (precategory_morphisms (f i))
               (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i0)) _ _ (! e))
               (to_In1 A (to_BinDirectSums A (f i) (f' i))) =
    transportf (λ (x : ob A), A⟦x, to_BinDirectSums A (f i') (f' i')⟧) (maponpaths f e)
               (to_In1 A (to_BinDirectSums A (f i') (f' i'))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_In2 (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    to_In2 A (to_BinDirectSums A (f i) (f' i)) =
    transportf (precategory_morphisms (f' i))
               (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i0)) _ _ e)
               (transportf (λ (x : ob A), A⟦x, to_BinDirectSums A (f i') (f' i')⟧)
                           (maponpaths f' e) (to_In2 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_In2' (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    transportf (precategory_morphisms (f' i))
               (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i0)) _ _ (! e))
               (to_In2 A (to_BinDirectSums A (f i) (f' i))) =
    transportf (λ (x : ob A), A⟦x, to_BinDirectSums A (f i') (f' i')⟧) (maponpaths f' e)
               (to_In2 A (to_BinDirectSums A (f i') (f' i'))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_Pr1 (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    to_Pr1 A (to_BinDirectSums A (f i) (f' i)) =
    transportf (precategory_morphisms (to_BinDirectSums A (f i) (f' i)))
               (maponpaths f e)
               (transportf (λ (x : ob A), A⟦x, (f i')⟧)
                           (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i0)) _ _ e)
                           (to_Pr1 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_Pr1' (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    transportf (precategory_morphisms (to_BinDirectSums A (f i) (f' i)))
               (maponpaths f (! e)) (to_Pr1 A (to_BinDirectSums A (f i) (f' i))) =
               (transportf (λ (x : ob A), A⟦x, (f i')⟧)
                           (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i0)) _ _ e)
                           (to_Pr1 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_Pr2 (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    to_Pr2 A (to_BinDirectSums A (f i) (f' i)) =
    transportf (precategory_morphisms (to_BinDirectSums A (f i) (f' i)))
               (maponpaths f' e)
               (transportf (λ (x : ob A), A⟦x, (f' i')⟧)
                           (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i0)) _ _ e)
                           (to_Pr2 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_Pr2' (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    transportf (precategory_morphisms (to_BinDirectSums A (f i) (f' i)))
               (maponpaths f' (! e)) (to_Pr2 A (to_BinDirectSums A (f i) (f' i))) =
               (transportf (λ (x : ob A), A⟦x, (f' i')⟧)
                           (@maponpaths hz A (λ i0 : hz, to_BinDirectSums A (f i0) (f' i0)) _ _ e)
                           (to_Pr2 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

End transport_hz_toBinDirectSums.
