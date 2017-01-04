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

Require Import UniMath.CategoryTheory.precategoriesWithBinOps.
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

  Lemma ComplexEq' (C1 C2 : Complex) (H : Π (i : hz), C1 i = C2 i)
        (H1 : Π (i : hz),
              transportf (λ x : A, C2 i --> x) (H (i + 1))
                         (transportf (λ x : A, x --> C1 (i + 1)) (H i) (Diff C1 i)) =
              Diff C2 i) :
    transportf (λ x : hz → A, Π i : hz, A ⟦ x i, x (i + 1) ⟧)
               (funextfun (pr1 (pr1 C1)) (pr1 (pr1 C2)) (λ i : hz, H i)) (pr2 (pr1 C1)) =
    pr2 (pr1 C2).
  Proof.
    use funextsec. intros i.
    assert (e : transportf (λ x : hz → A, Π i0 : hz, A ⟦ x i0, x (i0 + 1) ⟧)
                           (funextfun (pr1 (pr1 C1)) (pr1 (pr1 C2)) (λ i0 : hz, H i0))
                           (pr2 (pr1 C1)) i =
                transportf (λ x : hz → A, A ⟦ x i, x (i + 1) ⟧)
                           (funextfun (pr1 (pr1 C1)) (pr1 (pr1 C2)) (λ i0 : hz, H i0))
                           (pr2 (pr1 C1) i)).
    {
      induction (funextfun (pr1 (pr1 C1)) (pr1 (pr1 C2)) (λ i0 : hz, H i0)).
      apply idpath.
    }
    rewrite e. clear e.
    rewrite transport_mor_funextfun.
    rewrite transport_source_funextfun. rewrite transport_target_funextfun.
    exact (H1 i).
  Qed.

  Lemma ComplexEq'' (C1 C2 : Complex) (H : Π (i : hz), C1 i = C2 i)
        (H1 : Π (i : hz),
              transportf (λ x : A, C2 i --> x) (H (i + 1))
                         (transportf (λ x : A, x --> C1 (i + 1)) (H i) (Diff C1 i)) =
              Diff C2 i) :
    transportf
      (λ x : Σ D : hz → A, Π i : hz, A ⟦ D i, D (i + 1) ⟧,
                                 Π i : hz, pr2 x i ;; pr2 x (i + 1) =
                                           ZeroArrow (Additive.to_Zero A) _ _)
      (total2_paths (funextfun (pr1 (pr1 C1)) (pr1 (pr1 C2)) (λ i : hz, H i))
                    (ComplexEq' C1 C2 H H1)) (pr2 C1) = pr2 C2.
  Proof.
    apply proofirrelevance. apply impred_isaprop. intros t. apply to_has_homsets.
  Qed.

  Lemma ComplexEq (C1 C2 : Complex) (H : Π (i : hz), C1 i = C2 i)
        (H1 : Π (i : hz),
              transportf (λ x : A, C2 i --> x) (H (i + 1))
                         (transportf (λ x : A, x --> C1 (i + 1)) (H i) (Diff C1 i)) =
              Diff C2 i) : C1 = C2.
  Proof.
    use total2_paths.
    - use total2_paths.
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
  Lemma MorphismEq {C1 C2 : Complex} (M1 M2 : Morphism C1 C2) (H : Π i : hz, M1 i = M2 i) :
    M1 = M2.
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

  Local Lemma ComplexPreCat_KernelIn_comp {X Y w : Complex (AbelianToAdditive A hs)}
        (g : Morphism X Y) (h : Morphism w X) (i : hz) :
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


(** * Transport of morphisms indexed by integers *)
Section transport_section'.

  Variable C : precategory.

  Lemma transport_hz_source_target (f : hz -> ob C) (n : hz) (H : Π (i : hz), C⟦f i, f (i + n)⟧)
        (i i' : hz) (e1 : i = i') :
    H i' = transportf (fun (x : ob C) => C⟦x, f (i' + n)⟧) (maponpaths f e1)
                      (transportf (precategory_morphisms (f i))
                                  (maponpaths f (hzplusradd i i' n e1)) (H i)).
  Proof.
    induction e1. apply idpath.
  Qed.

  Lemma transport_hz_target_source (f : hz -> ob C) (n : hz) (H : Π (i : hz), C⟦f i, f (i + n)⟧)
        (i i' : hz) (e1 : i = i') :
    H i' = transportf (precategory_morphisms (f i'))
                      (maponpaths f (hzplusradd i i' n e1))
                      (transportf (fun (x : ob C) => C⟦x, f (i + n)⟧) (maponpaths f e1) (H i)).
  Proof.
    induction e1. apply idpath.
  Qed.

  Lemma transport_hz_section (f : hz -> ob C) (n : hz) (H : Π (i : hz), C⟦f i, f (i + n)⟧)
        (i i' : hz) (e1 : i = i') :
    transportf (precategory_morphisms (f i)) (maponpaths f (hzplusradd i i' n e1)) (H i) =
    transportf (fun (x : ob C) => C⟦x, f (i' + n)⟧) (maponpaths f (! e1)) (H i').
  Proof.
    induction e1. apply idpath.
  Qed.

  Lemma transport_hz_section' (f : hz -> ob C) (n : hz) (H : Π (i : hz), C⟦f (i + n), f i⟧)
        (i i' : hz) (e1 : i + n = i' + n) (e2 : i = i') :
    transportf (precategory_morphisms (f (i + n))) (maponpaths f e2) (H i) =
    transportf (fun (x : ob C) => C⟦x, f i'⟧) (maponpaths f (! e1)) (H i').
  Proof.
    induction e2. assert (e : e1 = idpath _) by apply isasethz. rewrite e. clear e. apply idpath.
  Qed.

  Lemma transport_hz_double_section (f f' : hz -> ob C) (H : Π (i : hz), C⟦f i, f' i⟧)
        (i i' : hz) (e : i = i') :
    transportf (precategory_morphisms (f i)) (maponpaths f' e) (H i) =
    transportf (fun (x : ob C) => C⟦x, f' i'⟧) (maponpaths f (! e)) (H i').
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_double_section_source_target (f f' : hz -> ob C) (H : Π (i : hz), C⟦f i, f' i⟧)
        (i i' : hz) (e : i = i') :
    H i' = transportf (precategory_morphisms (f i')) (maponpaths f' e)
                      (transportf (fun (x : ob C) => C⟦x, f' i⟧) (maponpaths f e) (H i)).
  Proof.
    induction e. apply idpath.
  Qed.

End transport_section'.


(** * Transport binary direct sums *)
Section transport_hz_toBinDirectSums.

  Context {A : Additive}.

  Lemma transport_to_BinDirectSums (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    @maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i0)) _ _ e =
    (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i')) _ _ e)
      @ (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i) (f' i0)) _ _ e).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_to_BinDirectSums_comm (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i')) _ _ e)
      @ (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i) (f' i0)) _ _ e) =
    (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i') (f' i0)) _ _ e)
      @ (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i)) _ _ e).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_In1 (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    to_In1 A (to_BinDirectSums A (f i) (f' i)) =
    transportf (precategory_morphisms (f i))
               (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i0)) _ _ e)
               (transportf (fun (x : ob A) => A⟦x, to_BinDirectSums A (f i') (f' i')⟧)
                           (maponpaths f e) (to_In1 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_In1' (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    transportf (precategory_morphisms (f i))
               (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i0)) _ _ (! e))
               (to_In1 A (to_BinDirectSums A (f i) (f' i))) =
    transportf (fun (x : ob A) => A⟦x, to_BinDirectSums A (f i') (f' i')⟧) (maponpaths f e)
               (to_In1 A (to_BinDirectSums A (f i') (f' i'))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_In2 (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    to_In2 A (to_BinDirectSums A (f i) (f' i)) =
    transportf (precategory_morphisms (f' i))
               (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i0)) _ _ e)
               (transportf (fun (x : ob A) => A⟦x, to_BinDirectSums A (f i') (f' i')⟧)
                           (maponpaths f' e) (to_In2 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_In2' (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    transportf (precategory_morphisms (f' i))
               (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i0)) _ _ (! e))
               (to_In2 A (to_BinDirectSums A (f i) (f' i))) =
    transportf (fun (x : ob A) => A⟦x, to_BinDirectSums A (f i') (f' i')⟧) (maponpaths f' e)
               (to_In2 A (to_BinDirectSums A (f i') (f' i'))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_Pr1 (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    to_Pr1 A (to_BinDirectSums A (f i) (f' i)) =
    transportf (precategory_morphisms (to_BinDirectSums A (f i) (f' i)))
               (maponpaths f e)
               (transportf (fun (x : ob A) => A⟦x, (f i')⟧)
                           (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i0)) _ _ e)
                           (to_Pr1 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_Pr1' (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    transportf (precategory_morphisms (to_BinDirectSums A (f i) (f' i)))
               (maponpaths f (! e)) (to_Pr1 A (to_BinDirectSums A (f i) (f' i))) =
               (transportf (fun (x : ob A) => A⟦x, (f i')⟧)
                           (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i0)) _ _ e)
                           (to_Pr1 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_Pr2 (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    to_Pr2 A (to_BinDirectSums A (f i) (f' i)) =
    transportf (precategory_morphisms (to_BinDirectSums A (f i) (f' i)))
               (maponpaths f' e)
               (transportf (fun (x : ob A) => A⟦x, (f' i')⟧)
                           (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i0)) _ _ e)
                           (to_Pr2 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

  Lemma transport_hz_to_Pr2' (f f' : hz -> ob A) {i i' : hz} (e : i' = i) :
    transportf (precategory_morphisms (to_BinDirectSums A (f i) (f' i)))
               (maponpaths f' (! e)) (to_Pr2 A (to_BinDirectSums A (f i) (f' i))) =
               (transportf (fun (x : ob A) => A⟦x, (f' i')⟧)
                           (@maponpaths hz A (fun i0 : hz => to_BinDirectSums A (f i0) (f' i0)) _ _ e)
                           (to_Pr2 A (to_BinDirectSums A (f i') (f' i')))).
  Proof.
    induction e. apply idpath.
  Qed.

End transport_hz_toBinDirectSums.
