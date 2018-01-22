(** * AbelianPreCat is Additive *)
(** ** Contents
- AbelianPreCat is Additive
 - Preliminaries
 - AbelianPreCat is Additive
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

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

Local Open Scope cat.

(** * AbelianPreCat is Additive. *)
Section abelian_is_additive.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  (** ** Preliminaries *)

  (** Some maps we are going to use. *)
  Definition DiagonalMap {X : A} (BinProd : BinProduct A X X) :
    A⟦X, (BinProductObject A BinProd)⟧ := BinProductArrow A BinProd (identity X) (identity X).

  Definition IdZeroMap {X : A} (BinProd : BinProduct A X X) :
    A⟦X, (BinProductObject A BinProd)⟧ := BinProductArrow A BinProd (identity X)
                                                          (ZeroArrow (to_Zero A) X X).

  Definition ZeroIdMap {X : A} (BinProd : BinProduct A X X) :
    A⟦X, (BinProductObject A BinProd)⟧ := BinProductArrow A BinProd (ZeroArrow (to_Zero A) X X)
                                                          (identity X).

  (** Proofs that these maps are monics. *)
  Lemma DiagonalMap_isMonic {X : A} (BinProd : BinProduct A X X) :
    isMonic (DiagonalMap BinProd).
  Proof.
    intros x u v H.
    apply (maponpaths (λ f : _, f · (BinProductPr1 A BinProd))) in H.
    repeat rewrite <- assoc in H. unfold DiagonalMap in H.
    repeat rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) _) in H.
    repeat rewrite id_right in H.
    exact H.
  Qed.

  Lemma IdZeroMap_isMonic {X : A} (BinProd : BinProduct A X X) :
    isMonic (IdZeroMap BinProd).
  Proof.
    intros x u v H.
    apply (maponpaths (λ f : _, f · (BinProductPr1 A BinProd))) in H.
    repeat rewrite <- assoc in H. unfold IdZeroMap in H.
    repeat rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) _) in H.
    repeat rewrite id_right in H.
    exact H.
  Qed.

  Lemma ZeroIdMap_isMonic {X : A} (BinProd : BinProduct A X X) :
    isMonic (ZeroIdMap BinProd).
  Proof.
    intros x u v H.
    apply (maponpaths (λ f : _, f · (BinProductPr2 A BinProd))) in H.
    repeat rewrite <- assoc in H. unfold ZeroIdMap in H.
    repeat rewrite (BinProductPr2Commutes A _ _ BinProd _ _ (identity X)) in H.
    repeat rewrite id_right in H.
    exact H.
  Qed.

  (** We show that Pr1 and Pr2 of BinProduct are epimorphisms. *)
  Lemma BinProductPr1_isEpi {X : A} (BinProd : BinProduct A X X) :
    isEpi (BinProductPr1 A BinProd).
  Proof.
    use isEpi_precomp.
    - exact X.
    - exact (IdZeroMap BinProd).
    - unfold IdZeroMap. rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) _).
      apply identity_isEpi.
  Qed.

  Lemma BinProductPr2_isEpi {X : A} (BinProd : BinProduct A X X) :
    isEpi (BinProductPr2 A BinProd).
  Proof.
    use isEpi_precomp.
    - exact X.
    - exact (ZeroIdMap BinProd).
    - unfold ZeroIdMap. rewrite (BinProductPr2Commutes A _ _ BinProd _ _ (identity X)).
      apply identity_isEpi.
  Qed.

  (** We construct kernels of BinProduct Pr1 and Pr2. *)
  Lemma KernelOfPr1_Eq {X : A} (BinProd : BinProduct A X X) :
    ZeroIdMap BinProd · BinProductPr1 A BinProd = ZeroArrow (to_Zero A) X X.
  Proof.
    unfold ZeroIdMap.
    exact (BinProductPr1Commutes A _ _ BinProd _ _ (identity X)).
  Qed.

  Local Lemma KernelOfPr1_isKernel_comm (X : A) (BinProd : BinProduct A X X) (w : A)
        (h : A ⟦ w, BinProductObject A BinProd ⟧)
        (H' : h · BinProductPr1 A BinProd = ZeroArrow (to_Zero A) _ _) :
    h · (BinProductPr2 A BinProd)
      · BinProductArrow A BinProd (ZeroArrow (to_Zero A) X X) (identity X) = h.
  Proof.
    apply BinProductArrowsEq.
    - rewrite <- assoc. rewrite (BinProductPr1Commutes A _ _ BinProd _ _ (identity X)).
      rewrite H'. rewrite ZeroArrow_comp_right. apply idpath.
    - rewrite <- assoc. rewrite (BinProductPr2Commutes A _ _ BinProd _ _ (identity X)).
      apply id_right.
  Qed.

  Local Lemma KernelOfPr1_isKernel_unique (X : A) (BinProd : BinProduct A X X) (w : A)
        (h : A ⟦ w, BinProductObject A BinProd ⟧)
        (H' : h · BinProductPr1 A BinProd = ZeroArrow (to_Zero A) _ _)
        (y : A ⟦ w, X ⟧)
        (H : y · BinProductArrow A BinProd (ZeroArrow (to_Zero A) X X) (identity X) = h) :
    y = h · BinProductPr2 A BinProd.
  Proof.
    rewrite <- H. rewrite <- assoc.
    rewrite (BinProductPr2Commutes A _ _ BinProd _ _ (identity X)).
    rewrite id_right. apply idpath.
  Qed.

  Lemma KernelOfPr1_isKernel {X : A} (BinProd : BinProduct A X X) :
    isKernel (to_Zero A) (ZeroIdMap BinProd) (BinProductPr1 A BinProd) (KernelOfPr1_Eq BinProd).
  Proof.
    use (mk_isKernel hs).
    intros w h H'.
    unfold ZeroIdMap.
    use unique_exists.
    (* The arrow *)
    - exact (h · (BinProductPr2 A BinProd)).
    (* commutativity *)
    - exact (KernelOfPr1_isKernel_comm X BinProd w h H').
    (* equality of equalities of morphisms *)
    - intros y. apply hs.
    (* uniqueness *)
    - exact (KernelOfPr1_isKernel_unique X BinProd w h H').
  Qed.

  Definition KernelOfPr1 {X : A} (BinProd : BinProduct A X X) :
    kernels.Kernel (to_Zero A) (BinProductPr1 A BinProd).
  Proof.
    exact (mk_Kernel (to_Zero A) (ZeroIdMap BinProd) _ (KernelOfPr1_Eq BinProd)
                     (KernelOfPr1_isKernel BinProd)).
  Defined.

  Lemma KernelOfPr2_Eq {X : A} (BinProd : BinProduct A X X) :
    IdZeroMap BinProd · BinProductPr2 A BinProd = ZeroArrow (to_Zero A) X X.
  Proof.
    unfold IdZeroMap. rewrite (BinProductPr2Commutes A _ _ BinProd _ (identity X) _).
    apply idpath.
  Qed.

  Local Lemma KernelOfPr2_isKernel_comm (X : A) (BinProd : BinProduct A X X) (w : A)
        (h : A ⟦w, BinProductObject A BinProd⟧)
        (H' : h · BinProductPr2 A BinProd = ZeroArrow (to_Zero A) _ _) :
    h · (BinProductPr1 A BinProd)
      · BinProductArrow A BinProd (identity X) (ZeroArrow (to_Zero A) X X) = h.
  Proof.
    apply BinProductArrowsEq.
    - rewrite <- assoc. rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) _).
      apply id_right.
    - rewrite <- assoc. rewrite (BinProductPr2Commutes A _ _ BinProd _ (identity X) _).
      rewrite H'. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Local Lemma KernelOfPr2_isKernel_unique (X : A) (BinProd : BinProduct A X X) (w : A)
        (h : A ⟦ w, BinProductObject A BinProd ⟧)
        (H' : h · BinProductPr2 A BinProd = ZeroArrow (to_Zero A) _ _)
        (y : A ⟦ w, X ⟧)
        (H : y · BinProductArrow A BinProd (identity X) (ZeroArrow (to_Zero A) X X) = h) :
    y = h · BinProductPr1 A BinProd.
  Proof.
    rewrite <- H. rewrite <- assoc.
    rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) _).
    rewrite id_right. apply idpath.
  Qed.

  Definition KernelOfPr2_isKernel {X : A} (BinProd : BinProduct A X X) :
    isKernel (to_Zero A) (IdZeroMap BinProd) (BinProductPr2 A BinProd) (KernelOfPr2_Eq BinProd).
  Proof.
    use (mk_isKernel hs).
    intros w h H'.
    unfold IdZeroMap.
    use unique_exists.
    (* The arrow *)
    - exact (h · (BinProductPr1 A BinProd)).
    (* Commutativity *)
    - exact (KernelOfPr2_isKernel_comm X BinProd w h H').
    (* Equality of equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y H. exact (KernelOfPr2_isKernel_unique X BinProd w h H' y H).
  Qed.

  Definition KernelOfPr2 {X : A} (BinProd : BinProduct A X X) :
    kernels.Kernel (to_Zero A) (BinProductPr2 A BinProd).
  Proof.
    exact (mk_Kernel (to_Zero A) (IdZeroMap BinProd) _ (KernelOfPr2_Eq BinProd)
                     (KernelOfPr2_isKernel BinProd)).
  Defined.

  (** From properties of abelian categories, it follows that Pr1 and Pr2 are
      cokernels of the above kernels since they are epimorphisms. *)
  Definition CokernelOfKernelOfPr1 {X : A} (BinProd : BinProduct A X X) :
    cokernels.Cokernel (to_Zero A) (KernelArrow (KernelOfPr1 BinProd)).
  Proof.
    exact (EpiToCokernel' A hs (mk_Epi A _ (BinProductPr1_isEpi BinProd))
                          (KernelOfPr1 BinProd)).
  Defined.

  Definition CokernelOfKernelOfPr2 {X : A} (BinProd : BinProduct A X X) :
    cokernels.Cokernel (to_Zero A) (KernelArrow (KernelOfPr2 BinProd)).
  Proof.
    exact (EpiToCokernel' A hs (mk_Epi A _ (BinProductPr2_isEpi BinProd))
                          (KernelOfPr2 BinProd)).
  Defined.

  (** We construct a cokernel of the DiagonalMap. The CokernelOb is the
      object X.*)
  Lemma CokernelOfDiagonal_is_iso {X : A} (BinProd : BinProduct A X X) :
    is_z_isomorphism ((BinProductArrow A BinProd (identity X) (ZeroArrow (to_Zero A) X X))
                        · (CokernelArrow (Cokernel (DiagonalMap BinProd)))).
  Proof.
    set (coker := Cokernel (DiagonalMap BinProd)).
    set (r := (BinProductArrow A BinProd (identity X) (ZeroArrow (to_Zero A) X X))
                · (CokernelArrow coker)).
    set (M := mk_Monic A _ (DiagonalMap_isMonic BinProd)).
    set (ker := MonicToKernel M).
    use monic_epi_is_iso.
    (* isMonic *)
    - use (@KernelZeroisMonic A hs (to_Zero A) _ _ _ (ZeroArrow_comp_left _ _ _ _ _ _)).
      use (mk_isKernel hs).
      intros w h H'.
      use unique_exists.
      (* The arrow *)
      + exact (ZeroArrow (to_Zero A) w (to_Zero A)).
      (* Commutativity *)
      + unfold r in H'. rewrite assoc in H'.
        set (y := KernelIn _ ker _ _ H'). cbn in y.
        set (com1 := KernelCommutes _ ker _ _ H'). cbn in com1. fold y in com1.
        unfold DiagonalMap in com1.
        assert (H : y = ZeroArrow (to_Zero A) w ker).
        {
          rewrite <- (id_right y).
          set (tmp := BinProductPr2Commutes A _ _ BinProd _ (identity X) (identity X)).
          rewrite <- tmp. rewrite assoc. rewrite com1. rewrite <- assoc.
          rewrite (BinProductPr2Commutes A _ _ BinProd _ (identity X) _).
          apply ZeroArrow_comp_right.
        }
        cbn. rewrite ZeroArrow_comp_left. cbn in H. apply pathsinv0 in H.
        use (pathscomp0 H). rewrite <- id_right.
        rewrite <- (BinProductPr1Commutes A _ _ BinProd _ (identity X) (ZeroArrow (to_Zero A) _ _)).
        rewrite assoc. rewrite <- com1. rewrite <- assoc.
        rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) (identity X)).
        rewrite id_right. apply idpath.
      (* Equality on equalities of morphisms *)
      + intros y. apply hs.
      (* Uniqueness *)
      + intros y H. apply ArrowsToZero.
    (* isEpi *)
    - use (@CokernelZeroisEpi A hs _ _ (to_Zero A) _ (ZeroArrow_comp_right _ _ _ _ _ _)).
      use (mk_isCokernel hs).
      intros w h H'.
      use unique_exists.
      (* The arrow *)
      + exact (ZeroArrow (to_Zero A) (to_Zero A) w).
      (* Commutativity *)
      + set(coker2 := CokernelOfKernelOfPr2 BinProd).
        set(coker2ar := CokernelArrow coker2). cbn in coker2ar.
        unfold r in H'. rewrite <- assoc in H'.
        set (y := CokernelOut _ coker2 _ _ H'). cbn in y.
        set (com1 := CokernelCommutes _ coker2 _ _ H'). cbn in com1. fold y in com1.
        assert (H : y = ZeroArrow (to_Zero A) X w).
        {
          rewrite <- (id_left y).
          set (tmp := BinProductPr2Commutes A _ _ BinProd _ (identity X) (identity X)).
          rewrite <- tmp. rewrite <- assoc. rewrite com1. rewrite assoc.
          rewrite CokernelCompZero.
          apply ZeroArrow_comp_left.
        }
        rewrite H in com1. rewrite ZeroArrow_comp_right in com1.
        rewrite <- (ZeroArrow_comp_right A (to_Zero A) _ _ _ (CokernelArrow coker)) in com1.
        apply CokernelArrowisEpi in com1. rewrite <- com1.
        apply ZeroArrow_comp_left.
      (* Equality on equalities of morphisms. *)
      + intros y. apply hs.
      (* Uniqueness *)
      + intros y H. apply ArrowsFromZero.
  Qed.

  Definition CokernelOfDiagonal {X : A} (BinProd : BinProduct A X X) :
    cokernels.Cokernel (to_Zero A) (DiagonalMap BinProd).
  Proof.
    set (X0 := z_iso_inv (mk_z_iso _ _ (CokernelOfDiagonal_is_iso BinProd))).
    exact (Cokernel_up_to_iso A hs (to_Zero A) _
                              (CokernelArrow (Cokernel (DiagonalMap BinProd)) · X0)
                              (Cokernel (DiagonalMap BinProd)) X0 (idpath _)).
  Defined.

  (** We define the op which makes the homsets of an abelian category to abelian
    groups. *)
  Definition Abelian_minus_op {X Y : A} (f g : X --> Y) : A⟦X, Y⟧ :=
    (BinProductArrow A (to_BinProducts A Y Y) f g)
      · CokernelArrow (CokernelOfDiagonal (to_BinProducts A Y Y)).

  Definition Abelian_op (X Y : A) : binop (A⟦X, Y⟧) :=
    (λ f : _, λ g : _, Abelian_minus_op f (Abelian_minus_op (ZeroArrow (to_Zero A) _ _) g)).

  (** Construction of a precategory with binops from Abelian category. *)
  Definition AbelianToprecategoryWithBinops : precategoryWithBinOps.
  Proof.
    use (mk_precategoryWithBinOps A).
    unfold precategoryWithBinOpsData.
    intros x y. exact (Abelian_op x y).
  Defined.

  (** We need the following lemmas to prove that the homsets of an abelian
      precategory are abelian groups. *)
  Lemma Abelian_DiagonalMap_eq {X Y : A} (f : X --> Y) :
    f · (DiagonalMap (to_BinProducts A Y Y)) =
    (DiagonalMap (to_BinProducts A X X))
      · (BinProductArrow A (to_BinProducts A Y Y)
                          (BinProductPr1 _ (to_BinProducts A X X) · f)
                          (BinProductPr2 _ (to_BinProducts A X X) · f)).
  Proof.
    unfold DiagonalMap.
    use BinProductArrowsEq.
    - repeat rewrite <- assoc.
      rewrite BinProductPr1Commutes.
      rewrite BinProductPr1Commutes.
      rewrite assoc. rewrite BinProductPr1Commutes.
      rewrite id_left. apply id_right.
    - repeat rewrite <- assoc.
      rewrite BinProductPr2Commutes.
      rewrite BinProductPr2Commutes.
      rewrite assoc. rewrite BinProductPr2Commutes.
      rewrite id_left. apply id_right.
  Qed.

  Lemma Abelian_op_eq_IdZero (X : A) :
    IdZeroMap (to_BinProducts A X X) · CokernelArrow (CokernelOfDiagonal (to_BinProducts A X X)) =
    identity _.
  Proof.
    set (ar := (BinProductArrow A (to_BinProducts A X X) (identity X) (ZeroArrow (to_Zero A) X X))
                 · (CokernelArrow (Cokernel (DiagonalMap (to_BinProducts A X X))))).
    set (r := mk_z_iso ar _ (CokernelOfDiagonal_is_iso (to_BinProducts A X X))).
    cbn. fold ar. fold r. rewrite assoc. exact (is_inverse_in_precat1 r).
  Qed.

  Lemma Abelian_op_eq {X Y : A} (f : X --> Y) :
    let bp1 := to_BinProducts A X X in
    let bp2 := to_BinProducts A Y Y in
    CokernelArrow (CokernelOfDiagonal bp1) · f =
    (BinProductArrow A bp2 (BinProductPr1 _ bp1 · f) (BinProductPr2 _ bp1 · f))
      · (CokernelArrow (CokernelOfDiagonal bp2)).
  Proof.
    set (bpX := to_BinProducts A X X).
    set (bpY := to_BinProducts A Y Y).
    cbn beta. cbn zeta.
    (* Cancel precomposition *)
    set (ar := (BinProductArrow A bpY (BinProductPr1 _ bpX · f) (BinProductPr2 _ bpX · f))
                 · (CokernelArrow (CokernelOfDiagonal bpY))).
    assert (H: DiagonalMap bpX · ar = ZeroArrow (to_Zero A) _ _).
    {
      unfold ar. rewrite assoc.
      unfold bpX, bpY. rewrite <- (Abelian_DiagonalMap_eq f). fold bpY.
      rewrite <- assoc. rewrite CokernelCompZero.
      apply ZeroArrow_comp_right.
    }
    set (g := CokernelOut (to_Zero A) (CokernelOfDiagonal bpX) (CokernelOfDiagonal bpY) ar H).
    set (com := CokernelCommutes
                  (to_Zero A) (CokernelOfDiagonal bpX) (CokernelOfDiagonal bpY) ar H).
    rewrite <- com. apply cancel_precomposition.
    (* rewrite and use com *)
    set (e1 := Abelian_op_eq_IdZero X).
    set (e2 := Abelian_op_eq_IdZero Y).
    set (ar' := BinProductArrow A bpY (BinProductPr1 A bpX · f) (BinProductPr2 A bpX · f)).
    assert (e3 : IdZeroMap (to_BinProducts A X X) · ar' = f · IdZeroMap (to_BinProducts A Y Y)).
    {
      unfold ar', IdZeroMap.
      apply BinProductArrowsEq.
      - rewrite <- assoc.
        rewrite BinProductPr1Commutes. rewrite assoc.
        rewrite BinProductPr1Commutes. rewrite id_left.
        rewrite <- assoc. rewrite BinProductPr1Commutes.
        rewrite id_right. apply idpath.
      - rewrite <- assoc.
        rewrite BinProductPr2Commutes. rewrite assoc.
        rewrite BinProductPr2Commutes.
        rewrite <- assoc. rewrite BinProductPr2Commutes.
        rewrite ZeroArrow_comp_right.
        apply ZeroArrow_comp_left.
    }
    rewrite <- (id_right f). rewrite <- e2. rewrite assoc.
    rewrite <- e3. unfold ar'. rewrite <- assoc. fold ar.
    rewrite <- id_left. cbn. rewrite <- e1. rewrite <- assoc.
    apply cancel_precomposition. apply pathsinv0.
    apply com.
  Qed.

  (** Construction of morphisms to BinProducts. *)
  Definition Abelian_mor_to_BinProd {X Y : A} (f g : X --> Y) :
    A⟦X, (BinProductObject A (to_BinProducts A Y Y))⟧ :=
    BinProductArrow _ (to_BinProducts A Y Y) f g.

  Definition Abelian_mor_from_to_BinProd {X Y : A} (f g : X --> Y) :
    A⟦BinProductObject A (to_BinProducts A X X), BinProductObject A (to_BinProducts A Y Y)⟧ :=
    BinProductArrow _ (to_BinProducts A Y Y)
                    (BinProductPr1 _ (to_BinProducts A X X) · f)
                    (BinProductPr2 _ (to_BinProducts A X X) · g).

  (** A few equations Abelian_minus_op and Abelian_op. *)
  Lemma AbelianPreCat_op_eq1 {X Y : A} (a b c d : X --> Y) :
    Abelian_minus_op (Abelian_mor_to_BinProd a b) (Abelian_mor_to_BinProd c d) =
    Abelian_mor_to_BinProd (Abelian_minus_op a c) (Abelian_minus_op b d).
  Proof.
    set (com1 := Abelian_op_eq (BinProductPr1 A (to_BinProducts A Y Y))).
    set (com2 := Abelian_op_eq (BinProductPr2 A (to_BinProducts A Y Y))).
    unfold Abelian_minus_op. unfold Abelian_mor_to_BinProd.
    use BinProductArrowsEq.
    - rewrite <- assoc. rewrite com1.
      rewrite BinProductPr1Commutes. rewrite assoc.
      apply cancel_postcomposition.
      use BinProductArrowsEq.
      + rewrite BinProductPr1Commutes. rewrite <- assoc.
        rewrite BinProductPr1Commutes. rewrite assoc.
        rewrite BinProductPr1Commutes.
        rewrite BinProductPr1Commutes.
        apply idpath.
      + rewrite BinProductPr2Commutes. rewrite <- assoc.
        rewrite BinProductPr2Commutes. rewrite assoc.
        rewrite BinProductPr2Commutes.
        rewrite BinProductPr1Commutes.
        apply idpath.
    - rewrite <- assoc. rewrite com2.
      rewrite BinProductPr2Commutes. rewrite assoc.
      apply cancel_postcomposition.
      use BinProductArrowsEq.
      + rewrite BinProductPr1Commutes. rewrite <- assoc.
        rewrite BinProductPr1Commutes. rewrite assoc.
        rewrite BinProductPr1Commutes.
        rewrite BinProductPr2Commutes.
        apply idpath.
      + rewrite BinProductPr2Commutes. rewrite <- assoc.
        rewrite BinProductPr2Commutes. rewrite assoc.
        rewrite BinProductPr2Commutes.
        rewrite BinProductPr2Commutes.
        apply idpath.
  Qed.

  Lemma AbelianPreCat_op_eq2 {X Y : A} (a b c d : X --> Y) :
    (Abelian_mor_to_BinProd (Abelian_mor_to_BinProd a b) (Abelian_mor_to_BinProd c d))
      · (Abelian_mor_from_to_BinProd
            (CokernelArrow (CokernelOfDiagonal (to_BinProducts A Y Y)))
            (CokernelArrow (CokernelOfDiagonal (to_BinProducts A Y Y)))) =
    Abelian_mor_to_BinProd
      ((Abelian_mor_to_BinProd a b) · CokernelArrow (CokernelOfDiagonal (to_BinProducts A Y Y)))
      ((Abelian_mor_to_BinProd c d) · CokernelArrow (CokernelOfDiagonal (to_BinProducts A Y Y))).
  Proof.
    unfold Abelian_mor_to_BinProd.
    unfold Abelian_mor_from_to_BinProd.
    use BinProductArrowsEq.
    - rewrite BinProductPr1Commutes. rewrite <- assoc.
      rewrite BinProductPr1Commutes. rewrite assoc.
      rewrite BinProductPr1Commutes. apply idpath.
    - rewrite BinProductPr2Commutes. rewrite <- assoc.
      rewrite BinProductPr2Commutes. rewrite assoc.
      rewrite BinProductPr2Commutes. apply idpath.
  Qed.

  Lemma AbelianPreCat_op_eq3 {X Y : A} (a b c d : X --> Y) :
    Abelian_minus_op (Abelian_minus_op a b) (Abelian_minus_op c d) =
    Abelian_minus_op (Abelian_minus_op a c) (Abelian_minus_op b d).
  Proof.
    (* Rewrite Abelian_minus_op_eq1 *)
    unfold Abelian_minus_op at 1.
    set (tmp := AbelianPreCat_op_eq1 a c b d).
    unfold Abelian_mor_to_BinProd in tmp.
    rewrite <- tmp.
    (* Rewrite com *)
    set (com := Abelian_op_eq (CokernelArrow (CokernelOfDiagonal (to_BinProducts A Y Y)))).
    unfold Abelian_minus_op at 1. rewrite <- assoc. rewrite com.
    (* Cancel postcompostion *)
    rewrite assoc.
    set (tmp1 := AbelianPreCat_op_eq2 a c b d).
    unfold Abelian_mor_to_BinProd, Abelian_mor_from_to_BinProd in tmp1.
    rewrite tmp1. apply cancel_postcomposition.
    (* Use idpath *)
    unfold Abelian_minus_op. apply idpath.
  Qed.


  (** ** AbelianPreCat is Additive *)

  (** The zero element in a homset of A is given by the ZeroArrow. *)
  Definition AbelianPreCat_homset_zero (X Y : A) : A⟦X, Y⟧ := ZeroArrow (to_Zero A) X Y.

  (** Some equations involving Abelian_minus_op and Abelian_op. *)
  Lemma AbelianPreCat_homset_zero_right' {X Y : A} (f : X --> Y) :
    Abelian_minus_op f (AbelianPreCat_homset_zero X Y) = f.
  Proof.
    unfold AbelianPreCat_homset_zero. unfold Abelian_minus_op.
    set (tmp := Abelian_op_eq_IdZero Y). unfold IdZeroMap in tmp.
    assert (e : BinProductArrow A (to_BinProducts A Y Y) f (ZeroArrow (to_Zero A) X Y) =
                f · BinProductArrow A (to_BinProducts A Y Y) (identity _)
                  (ZeroArrow (to_Zero A) Y Y)).
    {
      apply BinProductArrowsEq.
      - rewrite BinProductPr1Commutes. rewrite <- assoc.
        rewrite BinProductPr1Commutes.
        rewrite id_right. apply idpath.
      - rewrite BinProductPr2Commutes. rewrite <- assoc.
        rewrite BinProductPr2Commutes.
        rewrite ZeroArrow_comp_right. apply idpath.
    }
    rewrite e. clear e. rewrite <- assoc. rewrite tmp. apply id_right.
  Qed.

  Lemma AbelianPreCat_homset_zero_right {X Y : A} (f : X --> Y) :
    Abelian_op _ _ f (AbelianPreCat_homset_zero X Y) = f.
  Proof.
    unfold AbelianPreCat_homset_zero.
    unfold Abelian_op. unfold Abelian_minus_op at 2.
    use (pathscomp0 _ (AbelianPreCat_homset_zero_right' f)).
    set (bpY := to_BinProducts A Y Y).
    assert (e : (BinProductArrow A bpY (ZeroArrow (to_Zero A) X Y) (ZeroArrow (to_Zero A) X Y))
                  · CokernelArrow (CokernelOfDiagonal bpY) = ZeroArrow (to_Zero A) _ _ ).
    {
      use (pathscomp0 _ (ZeroArrow_comp_left A (to_Zero A) _ _ _
                                             (CokernelArrow (CokernelOfDiagonal bpY)))).
      apply cancel_postcomposition.
      use BinProductArrowsEq.
      - rewrite BinProductPr1Commutes.
        rewrite ZeroArrow_comp_left. apply idpath.
      - rewrite BinProductPr2Commutes.
        rewrite ZeroArrow_comp_left. apply idpath.
    }
    rewrite e. apply idpath.
  Qed.

  Definition AbelianPreCat_homset_inv {X Y : A} (f : X --> Y) :
    A⟦X, Y⟧ := Abelian_minus_op (ZeroArrow (to_Zero A) _ _) f.

  Lemma AbelianPreCat_homset_inv_left' {X Y : A} (f : X --> Y) :
    Abelian_minus_op f f = (AbelianPreCat_homset_zero X Y).
  Proof.
    unfold AbelianPreCat_homset_zero. unfold Abelian_minus_op.
    set (bpY := to_BinProducts A Y Y).
    assert (e : BinProductArrow A bpY f f =
                f · BinProductArrow A bpY (identity _ ) (identity _ )).
    {
      use BinProductArrowsEq.
      - rewrite BinProductPr1Commutes. rewrite <- assoc.
        rewrite BinProductPr1Commutes. rewrite id_right.
        apply idpath.
      - rewrite BinProductPr2Commutes. rewrite <- assoc.
        rewrite BinProductPr2Commutes. rewrite id_right.
        apply idpath.
    }
    rewrite e. rewrite <- assoc. rewrite CokernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Lemma AbelianPreCat_homset_inv_left {X Y : A} (f : X --> Y) :
    Abelian_op _ _ (AbelianPreCat_homset_inv f) f = (AbelianPreCat_homset_zero X Y).
  Proof.
    unfold AbelianPreCat_homset_inv.
    unfold AbelianPreCat_homset_zero.
    unfold Abelian_op.
    rewrite AbelianPreCat_op_eq3.
    rewrite AbelianPreCat_homset_inv_left'.
    rewrite AbelianPreCat_homset_inv_left'.
    apply AbelianPreCat_homset_zero_right'.
  Qed.

  Lemma AbelianPreCat_homset_zero_left {X Y : A} (f : X --> Y) :
    Abelian_op _ _ (AbelianPreCat_homset_zero X Y) f = f.
  Proof.
    rewrite <- (AbelianPreCat_homset_inv_left' f).
    set (tmp := AbelianPreCat_homset_zero_right' f).
    apply (maponpaths (λ g : _, Abelian_op X Y (Abelian_minus_op f f) g)) in tmp.
    apply pathsinv0 in tmp.
    use (pathscomp0 tmp).
    unfold Abelian_op.
    rewrite AbelianPreCat_op_eq3.
    rewrite AbelianPreCat_homset_zero_right'.
    rewrite AbelianPreCat_homset_zero_right'.
    rewrite AbelianPreCat_homset_inv_left'.
    rewrite AbelianPreCat_homset_zero_right'.
    apply idpath.
  Qed.

  Lemma Abeliain_precategory_homset_comm' {X Y : A} (f g : X --> Y) :
    Abelian_minus_op (Abelian_minus_op (AbelianPreCat_homset_zero X Y) f) g =
    Abelian_minus_op (Abelian_minus_op (AbelianPreCat_homset_zero X Y) g) f.
  Proof.
    rewrite <- (AbelianPreCat_homset_zero_right' g).
    rewrite AbelianPreCat_op_eq3.
    rewrite (AbelianPreCat_homset_zero_right' f).
    rewrite (AbelianPreCat_homset_zero_right' g).
    apply idpath.
  Qed.

  Lemma AbelianPreCat_homset_comm {X Y : A} (f g : X --> Y) :
    Abelian_op _ _ f g = Abelian_op _ _ g f.
  Proof.
    (* Use zero left for f *)
    set (tmp1 := AbelianPreCat_homset_zero_left f).
    apply (maponpaths (λ h : _, Abelian_op X Y h g)) in tmp1.
    apply pathsinv0 in tmp1. use (pathscomp0 tmp1). clear tmp1.
    (* Use zero left for g *)
    set (tmp2 := AbelianPreCat_homset_zero_left g).
    apply (maponpaths (λ h : _, Abelian_op X Y h f)) in tmp2.
    use (pathscomp0 _ tmp2). clear tmp2.
    (* The goal follows from eq3 and comm' *)
    unfold Abelian_op.
    rewrite (AbelianPreCat_op_eq3 _ _ _ g).
    rewrite (AbelianPreCat_op_eq3 _ _ _ f).
    rewrite (Abeliain_precategory_homset_comm' _ g).
    apply idpath.
  Qed.

  Lemma AbelianPreCat_homset_inv_minus {X Y : A} (f g : X --> Y) :
    Abelian_op _ _ f (AbelianPreCat_homset_inv g) = Abelian_minus_op f g.
  Proof.
    unfold Abelian_op.
    unfold AbelianPreCat_homset_inv.
    set (tmp := AbelianPreCat_homset_zero_left g).
    unfold Abelian_op in tmp.
    unfold AbelianPreCat_homset_zero in tmp.
    rewrite tmp. apply idpath.
  Qed.

  Lemma AbelianPreCat_homset_inv_right {X Y : A} (f : X --> Y) :
    Abelian_op _ _ f (AbelianPreCat_homset_inv f) = AbelianPreCat_homset_zero X Y.
  Proof.
    rewrite AbelianPreCat_homset_inv_minus.
    apply AbelianPreCat_homset_inv_left'.
  Qed.

  Lemma AbelianPreCat_homset_assoc_eq1 {X Y : A} (f g : X --> Y) :
    Abelian_minus_op (AbelianPreCat_homset_zero X Y) (Abelian_minus_op f g) =
    Abelian_op _ _ (Abelian_minus_op (AbelianPreCat_homset_zero X Y) f) g.
  Proof.
    rewrite <- (AbelianPreCat_homset_inv_left' (AbelianPreCat_homset_zero X Y)).
    unfold Abelian_op.
    rewrite AbelianPreCat_op_eq3.
    rewrite (AbelianPreCat_homset_inv_left' (AbelianPreCat_homset_zero X Y)).
    apply idpath.
  Qed.

  Lemma AbelianPreCat_homset_assoc_eq2 {X Y : A} (f g : X --> Y) :
    Abelian_minus_op (AbelianPreCat_homset_zero X Y) (Abelian_op _ _ f g) =
    Abelian_minus_op (Abelian_minus_op (AbelianPreCat_homset_zero X Y) f) g.
  Proof.
    set (tmp := AbelianPreCat_homset_inv_left' (AbelianPreCat_homset_zero X Y)).
    apply (maponpaths (λ h : _, Abelian_minus_op h (Abelian_op X Y f g))) in tmp.
    apply pathsinv0 in tmp. use (pathscomp0 tmp).
    unfold Abelian_op.
    rewrite AbelianPreCat_op_eq3.
    set (tmp2 := AbelianPreCat_homset_zero_left g).
    unfold Abelian_op in tmp2. rewrite tmp2.
    apply idpath.
  Qed.

  Lemma AbelianPreCat_homset_assoc_eq3 {X Y : A} (f g h : X --> Y) :
     Abelian_op _ _ (Abelian_minus_op f g) h = Abelian_minus_op f (Abelian_minus_op g h).
  Proof.
    unfold Abelian_op.
    rewrite AbelianPreCat_op_eq3.
    rewrite AbelianPreCat_homset_zero_right'.
    apply idpath.
  Qed.

  Lemma AbelianPreCat_homset_assoc {X Y : A} (f g h : X --> Y) :
     Abelian_op _ _ (Abelian_op _ _ f g) h = Abelian_op _ _ f (Abelian_op _ _ g h).
  Proof.
    set (tmp := AbelianPreCat_homset_zero_left h).
    apply (maponpaths (λ k : _, Abelian_op X Y (Abelian_op X Y f g) k)) in tmp.
    apply pathsinv0 in tmp. use (pathscomp0 tmp).
    unfold Abelian_op.
    rewrite AbelianPreCat_op_eq3.
    rewrite AbelianPreCat_homset_zero_right'.
    rewrite AbelianPreCat_op_eq3.
    rewrite AbelianPreCat_homset_zero_right'.
    apply idpath.
  Qed.

  Definition AbelianTocategoryWithAbgropsData :
    categoryWithAbgropsData AbelianToprecategoryWithBinops hs.
  Proof.
    unfold categoryWithAbgropsData.
    intros x y.
    split.
    - use isgroppair.
      + split.
        * intros f g h. apply AbelianPreCat_homset_assoc.
        * use isunitalpair.
          -- apply AbelianPreCat_homset_zero.
          -- split.
             ++ intros f. apply AbelianPreCat_homset_zero_left.
             ++ intros f. apply AbelianPreCat_homset_zero_right.
      + use tpair.
        * intros f. apply (AbelianPreCat_homset_inv f).
        * split.
          -- intros f. apply AbelianPreCat_homset_inv_left.
          -- intros f. apply AbelianPreCat_homset_inv_right.
    - intros f g. apply AbelianPreCat_homset_comm.
  Defined.

  (** We prove that Abelian_precategories are PrecategoriesWithAbgrops. *)
  Definition AbelianTocategoryWithAbgrops :
    categoryWithAbgrops := mk_categoryWithAbgrops
                                AbelianToprecategoryWithBinops  hs
                                AbelianTocategoryWithAbgropsData.

  (** Hide isPreAdditive behind Qed. *)
  Lemma AbelianToisPreAdditive :
    isPreAdditive AbelianTocategoryWithAbgrops.
  Proof.
    use mk_isPreAdditive.
    (* precomposition ismonoidfun *)
    - intros x y z f.
      split.
      + intros x' x'0. unfold to_premor.
        cbn. unfold Abelian_op. unfold Abelian_minus_op.
        cbn in x', x'0. rewrite assoc. apply cancel_postcomposition.
        set (bpz := to_BinProducts A z z).
        assert (e : BinProductArrow
                      A bpz (f · x')
                      ((BinProductArrow A bpz (ZeroArrow (to_Zero A) x z) (f · x'0))
                         · CokernelArrow (CokernelOfDiagonal bpz)) =
                    BinProductArrow
                      A bpz (f · x')
                      ((BinProductArrow A bpz (f · ZeroArrow (to_Zero A) y z) (f · x'0))
                         · CokernelArrow (CokernelOfDiagonal bpz))).
        {
          set (tmp := ZeroArrow_comp_right A (to_Zero A) x y z f).
          apply (maponpaths
                   (λ h : _, BinProductArrow A bpz (f · x')
                                              ((BinProductArrow A bpz h (f · x'0))
                                                 · CokernelArrow (CokernelOfDiagonal bpz))))
            in tmp.
          apply pathsinv0 in tmp. apply tmp.
        }
        use (pathscomp0 _ (!e)). clear e.
        rewrite <- precompWithBinProductArrow. rewrite <- assoc.
        rewrite <- precompWithBinProductArrow. apply idpath.
      + unfold to_premor. cbn.
        unfold AbelianPreCat_homset_zero.
        apply ZeroArrow_comp_right.
    (* postcomposition is monoidfun *)
    - intros x y z f.
      split.
      + intros x' x'0. unfold to_postmor.
        cbn. unfold Abelian_op. unfold Abelian_minus_op.
        cbn in x', x'0.
        set (bpz := to_BinProducts A z z).
        assert (e : BinProductArrow A bpz (ZeroArrow (to_Zero A) x z) (x'0 · f) =
                    (BinProductArrow A (to_BinProducts A y y) (ZeroArrow (to_Zero A) x y) x'0)
                      · Abelian_mor_from_to_BinProd f f).
        {
          use BinProductArrowsEq.
          - unfold Abelian_mor_from_to_BinProd.
            rewrite <- assoc.
            rewrite BinProductPr1Commutes.
            rewrite BinProductPr1Commutes.
            rewrite assoc.
            rewrite BinProductPr1Commutes.
            rewrite ZeroArrow_comp_left.
            apply idpath.
          - unfold Abelian_mor_from_to_BinProd.
            rewrite <- assoc.
            rewrite BinProductPr2Commutes.
            rewrite BinProductPr2Commutes.
            rewrite assoc.
            rewrite BinProductPr2Commutes.
            apply idpath.
        }
        rewrite e. clear e.  unfold Abelian_mor_from_to_BinProd. repeat rewrite <- assoc.
        set (tmp := Abelian_op_eq f). cbn zeta in tmp. unfold bpz. rewrite <- tmp.
        repeat rewrite assoc.
        rewrite <- (postcompWithBinProductArrow A _ (to_BinProducts A y y)).
        repeat rewrite <- assoc.
        apply cancel_precomposition.
        unfold BinProductOfArrows.
        apply tmp.
      + unfold to_postmor. cbn.
        unfold AbelianPreCat_homset_zero.
        apply ZeroArrow_comp_left.
  Qed.

  (** We prove that Abelian_precategories are PreAddtitive. *)
  Definition AbelianToPreAdditive :
    PreAdditive := mk_PreAdditive AbelianTocategoryWithAbgrops AbelianToisPreAdditive.

  (** Finally, we show that Abelian_precategories are Additive. *)
  Definition AbelianToAdditive : Additive.
  Proof.
    use mk_Additive.
    - exact AbelianToPreAdditive.
    - use mk_isAdditive.
      + exact (to_Zero A).
      + exact (BinDirectSums_from_BinProducts
                 AbelianToPreAdditive hs (to_Zero A) (to_BinProducts A)).
  Defined.

End abelian_is_additive.
