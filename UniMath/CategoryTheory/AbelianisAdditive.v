(** We prove that Abelian_precategory is additive. *)
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
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.

Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.PrecategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.

Section abelian_is_additive.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  (** Some maps we are going to use. *)
  Definition DiagonalMap {X : A} (BinProd : BinProductCone A X X) :
    A⟦X, (BinProductObject A BinProd)⟧
    := BinProductArrow A BinProd (identity X) (identity X).

  Definition IdZeroMap {X : A} (BinProd : BinProductCone A X X) :
    A⟦X, (BinProductObject A BinProd)⟧
    := BinProductArrow A BinProd (identity X)
                       (ZeroArrow A (Abelian_Zero A) X X).
  Definition ZeroIdMap {X : A} (BinProd : BinProductCone A X X) :
    A⟦X, (BinProductObject A BinProd)⟧
    := BinProductArrow A BinProd (ZeroArrow A (Abelian_Zero A) X X)
                       (identity X).

  (** Proofs that these maps are monics. *)
  Definition DiagonalMap_isMonic {X : A} (BinProd : BinProductCone A X X) :
    isMonic A (DiagonalMap BinProd).
  Proof.
    intros x u v H.
    apply (maponpaths (fun f : _ => f ;; (BinProductPr1 A BinProd))) in H.
    repeat rewrite <- assoc in H. unfold DiagonalMap in H.
    repeat rewrite (BinProductPr1Commutes A _ _ BinProd _
                                          (identity X) (identity X)) in H.
    repeat rewrite id_right in H.
    exact H.
  Qed.

  Definition IdZeroMap_isMonic {X : A} (BinProd : BinProductCone A X X) :
    isMonic A (IdZeroMap BinProd).
  Proof.
    intros x u v H.
    apply (maponpaths (fun f : _ => f ;; (BinProductPr1 A BinProd))) in H.
    repeat rewrite <- assoc in H. unfold IdZeroMap in H.
    repeat rewrite (BinProductPr1Commutes A _ _ BinProd _
                                          (identity X) _) in H.
    repeat rewrite id_right in H.
    exact H.
  Qed.

  Definition ZeroIdMap_isMonic {X : A} (BinProd : BinProductCone A X X) :
    isMonic A (ZeroIdMap BinProd).
  Proof.
    intros x u v H.
    apply (maponpaths (fun f : _ => f ;; (BinProductPr2 A BinProd))) in H.
    repeat rewrite <- assoc in H. unfold ZeroIdMap in H.
    repeat rewrite (BinProductPr2Commutes A _ _ BinProd _
                                          _ (identity X)) in H.
    repeat rewrite id_right in H.
    exact H.
  Qed.

  (** We show that Pr1 and Pr2 of BinProduct are epimorphisms. *)
  Definition BinProductPr1_isEpi {X : A} (BinProd : BinProductCone A X X) :
    isEpi A (BinProductPr1 A BinProd).
  Proof.
    use isEpi_precomp.
    exact X.
    exact (IdZeroMap BinProd).
    unfold IdZeroMap.
    rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) _).
    apply identity_isEpi.
  Qed.

  Definition BinProductPr2_isEpi {X : A} (BinProd : BinProductCone A X X) :
    isEpi A (BinProductPr2 A BinProd).
  Proof.
    use isEpi_precomp.
    exact X.
    exact (ZeroIdMap BinProd).
    unfold ZeroIdMap.
    rewrite (BinProductPr2Commutes A _ _ BinProd _ _ (identity X)).
    apply identity_isEpi.
  Qed.

  (** We construct kernels of BinProduct Pr1 and Pr2. *)
  Definition KernelOfPr1_Eq {X : A} (BinProd : BinProductCone A X X) :
    ZeroIdMap BinProd ;; BinProductPr1 A BinProd
    = ZeroArrow A (Abelian_Zero A) X X.
  Proof.
    unfold ZeroIdMap.
    rewrite (BinProductPr1Commutes A _ _ BinProd _ _ (identity X)).
    apply idpath.
  Qed.

  Definition KernelOfPr1_isEqualizer {X : A} (BinProd : BinProductCone A X X) :
    isEqualizer (BinProductPr1 A BinProd)
                (ZeroArrow A (Abelian_Zero A) (BinProductObject A BinProd) X)
                (ZeroIdMap BinProd)
                (KernelEqRw (Abelian_Zero A) (KernelOfPr1_Eq BinProd)).
  Proof.
    use mk_isEqualizer.
    intros w h H'.
    unfold ZeroIdMap.
    apply (unique_exists (h ;; (BinProductPr2 A BinProd))).
    apply BinProductArrowsEq. rewrite <- assoc.
    rewrite (BinProductPr1Commutes A _ _ BinProd _ _ (identity X)).
    rewrite H'. repeat rewrite ZeroArrow_comp_right. apply idpath.
    rewrite <- assoc.
    rewrite (BinProductPr2Commutes A _ _ BinProd _ _ (identity X)).
    apply id_right.

    intros y. apply hs.

    intros y H. rewrite <- H. rewrite <- assoc.
    rewrite (BinProductPr2Commutes A _ _ BinProd _ _ (identity X)).
    rewrite id_right. apply idpath.
  Qed.

  Definition KernelOfPr1 {X : A} (BinProd : BinProductCone A X X) :
    Kernel (Abelian_Zero A) (BinProductPr1 A BinProd).
  Proof.
    exact (mk_Kernel (Abelian_Zero A) (ZeroIdMap BinProd) _
                     (KernelOfPr1_Eq BinProd)
                     (KernelOfPr1_isEqualizer BinProd)).
  Defined.

  Definition KernelOfPr2_Eq {X : A} (BinProd : BinProductCone A X X) :
    IdZeroMap BinProd ;; BinProductPr2 A BinProd
    = ZeroArrow A (Abelian_Zero A) X X.
  Proof.
    unfold IdZeroMap.
    rewrite (BinProductPr2Commutes A _ _ BinProd _ (identity X) _).
    apply idpath.
  Qed.

  Definition KernelOfPr2_isEqualizer {X : A} (BinProd : BinProductCone A X X) :
    isEqualizer (BinProductPr2 A BinProd)
                (ZeroArrow A (Abelian_Zero A) (BinProductObject A BinProd) X)
                (IdZeroMap BinProd)
                (KernelEqRw (Abelian_Zero A) (KernelOfPr2_Eq BinProd)).
  Proof.
    use mk_isEqualizer.
    intros w h H'.
    unfold IdZeroMap.
    apply (unique_exists (h ;; (BinProductPr1 A BinProd))).
    apply BinProductArrowsEq. rewrite <- assoc.
    rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) _).
    apply id_right. rewrite <- assoc.
    rewrite (BinProductPr2Commutes A _ _ BinProd _ (identity X) _).
    rewrite H'. repeat rewrite ZeroArrow_comp_right. apply idpath.

    intros y. apply hs.

    intros y H. rewrite <- H. rewrite <- assoc.
    rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) _).
    rewrite id_right. apply idpath.
  Qed.

  Definition KernelOfPr2 {X : A} (BinProd : BinProductCone A X X) :
    Kernel (Abelian_Zero A) (BinProductPr2 A BinProd).
  Proof.
    exact (mk_Kernel (Abelian_Zero A) (IdZeroMap BinProd) _
                     (KernelOfPr2_Eq BinProd)
                     (KernelOfPr2_isEqualizer BinProd)).
  Defined.

  (** From properties of abelian categories, it follows that Pr1 and Pr2 are
    cokernels of the above kernels since they are epimorphisms. *)
  Definition CokernelOfKernelOfPr1 {X : A} (BinProd : BinProductCone A X X) :
    Cokernel (Abelian_Zero A) (KernelArrow (Abelian_Zero A)
                                           (KernelOfPr1 BinProd)).
  Proof.
    exact (Abelian_EpiToCokernel' A hs
                                  (mk_Epi A _ (BinProductPr1_isEpi BinProd))
                                  (KernelOfPr1 BinProd)).
  Defined.

  Definition CokernelOfKernelOfPr2 {X : A} (BinProd : BinProductCone A X X) :
    Cokernel (Abelian_Zero A) (KernelArrow (Abelian_Zero A)
                                           (KernelOfPr2 BinProd)).
  Proof.
    exact (Abelian_EpiToCokernel' A hs
                                  (mk_Epi A _ (BinProductPr2_isEpi BinProd))
                                  (KernelOfPr2 BinProd)).
  Defined.

  (** We construct a cokernel of the DiagonalMap. The CokernelOb is the
   object X.*)
  Lemma CokernelOfDiagonal_is_iso {X : A} (BinProd : BinProductCone A X X) :
    is_iso ((BinProductArrow A BinProd (identity X)
                             (ZeroArrow A (Abelian_Zero A) X X))
              ;; (CokernelArrow (Abelian_Zero A)
                                (Abelian_Cokernel A (DiagonalMap BinProd)))).
  Proof.
    set (coker := Abelian_Cokernel A (DiagonalMap BinProd)).
    set (r := (BinProductArrow A BinProd (identity X)
                               (ZeroArrow A (Abelian_Zero A) X X))
                ;; (CokernelArrow (Abelian_Zero A) coker)).
    set (M := mk_Monic A _ (DiagonalMap_isMonic BinProd)).
    set (ker := Abelian_MonicToKernel A hs M).

    apply Abelian_monic_epi_is_iso.

    (* isMonic *)
    use (@Abelian_KernelZeroisMonic A hs (Abelian_Zero A)).
    apply ZeroArrow_comp_left.

    apply mk_isEqualizer.
    intros w h H'.
    apply (unique_exists (ZeroArrow A (Abelian_Zero A) w (Abelian_Zero A))).

    (* Commutativity *)
    rewrite ZeroArrow_comp_right in H'. unfold r in H'. rewrite assoc in H'.
    set (y := KernelIn _ ker _ _ H'). cbn in y.
    set (com1 := KernelCommutes _ ker _ _ H'). cbn in com1. fold y in com1.
    unfold DiagonalMap in com1.

    assert (H : y = ZeroArrow _ (Abelian_Zero A) w ker).
    {
      rewrite <- (id_right A _ _ y).
      set (tmp := BinProductPr2Commutes A _ _ BinProd _ (identity X)
                                        (identity X)).
      rewrite <- tmp. rewrite assoc. rewrite com1. rewrite <- assoc.
      rewrite (BinProductPr2Commutes A _ _ BinProd _ (identity X) _).
      apply ZeroArrow_comp_right.
    }

    rewrite ZeroArrow_comp_left. cbn in H. apply pathsinv0 in H.
    use (pathscomp0 H). rewrite <- id_right.
    rewrite <- (BinProductPr1Commutes A _ _ BinProd _ (identity X)
                                     (ZeroArrow _ (Abelian_Zero A) _ _)).
    rewrite assoc. rewrite <- com1. rewrite <- assoc.
    rewrite (BinProductPr1Commutes A _ _ BinProd _ (identity X) (identity X)).
    rewrite id_right. apply idpath.

    (* Equality on equalities of morphisms *)
    intros y. apply hs.

    (* Uniqueness *)
    intros y H. apply ArrowsToZero.

    (* isEpi *)
    use (@Abelian_CokernelZeroisEpi A hs).
    exact (Abelian_Zero A).
    apply ZeroArrow_comp_right.

    apply mk_isCoequalizer.
    intros w h H'.
    apply (unique_exists (ZeroArrow A (Abelian_Zero A) (Abelian_Zero A) w)).


    (* Commutativity *)
    set(coker2 := CokernelOfKernelOfPr2 BinProd).
    set(coker2ar := CokernelArrow _ coker2). cbn in coker2ar.
    rewrite ZeroArrow_comp_left in H'. unfold r in H'. rewrite <- assoc in H'.
    set (y := CokernelOut _ coker2 _ _ H'). cbn in y.
    set (com1 := CokernelCommutes _ coker2 _ _ H'). cbn in com1. fold y in com1.

    assert (H : y = ZeroArrow _ (Abelian_Zero A) X w).
    {
      rewrite <- (id_left A _ _ y).
      set (tmp := BinProductPr2Commutes A _ _ BinProd _ (identity X)
                                        (identity X)).
      rewrite <- tmp. rewrite <- assoc. rewrite com1. rewrite assoc.
      rewrite CokernelCompZero.
      apply ZeroArrow_comp_left.
    }

    rewrite H in com1. rewrite ZeroArrow_comp_right in com1.
    rewrite <- (ZeroArrow_comp_right A (Abelian_Zero A) _ _ _
                                    (CokernelArrow (Abelian_Zero A) coker))
      in com1.
    apply CokernelArrowisEpi in com1. rewrite <- com1.
    apply ZeroArrow_comp_left.

    (* Equality on equalities of morphisms. *)
    intros y. apply hs.

    (* Uniqueness *)
    intros y H. apply ArrowsFromZero.
  Qed.

  Definition CokernelOfDiagonal {X : A} (BinProd : BinProductCone A X X) :
    Cokernel (Abelian_Zero A) (DiagonalMap BinProd).
  Proof.
    set (X0 := CokernelOfDiagonal_is_iso BinProd).
    exact (Cokernel_up_to_iso A hs (Abelian_Zero A) _
                              (CokernelArrow (Abelian_Zero A)
                                             (Abelian_Cokernel A (DiagonalMap
                                                                    BinProd))
                                             ;; iso_inv_from_iso (isopair _ X0))
                              (Abelian_Cokernel A (DiagonalMap BinProd))
                              (iso_inv_from_iso (isopair _ X0)) (idpath _)).
  Defined.

  (** Verification that the CokernelArrow of the above is what we wanted. *)
  Lemma CokernelOfDiagonal_CokernelArrowEq {X : A}
        (BinProd : BinProductCone A X X) :
    CokernelArrow _ (CokernelOfDiagonal BinProd)
    = (CokernelArrow (Abelian_Zero A)
                     (Abelian_Cokernel A (DiagonalMap BinProd))
                     ;; iso_inv_from_iso (isopair _
                                                  (CokernelOfDiagonal_is_iso
                                                     BinProd))).
  Proof.
    apply idpath.
  Qed.

  (** We define the op which makes the homsets of an abelian category to abelian
    groups. *)
  Definition Abelian_minus_op {X Y : A} (f g : X --> Y) :
    A⟦X, Y⟧ :=
    (BinProductArrow A (Abelian_BinProducts A Y Y) f g)
      ;; CokernelArrow _ (CokernelOfDiagonal (Abelian_BinProducts A Y Y)).

  Definition Abelian_op (X Y : A) : binop (A⟦X, Y⟧) :=
    (fun f : _ => fun g : _ =>
                 Abelian_minus_op f (Abelian_minus_op
                                       (ZeroArrow A (Abelian_Zero A) _ _) g)).

  (** Construction of a precategory with binops from Abelian category. *)
  Definition Abelian_precategory_PrecategoryWithBinops :
    PrecategoryWithBinOps.
  Proof.
    use (mk_PrecategoryWithBinOps A).
    unfold PrecategoryWithBinOpsData.
    intros x y. exact (Abelian_op x y).
  Defined.

  (** We need the following lemmas to prove that the homsets of an abelian
     precategory are abelian groups. *)
  Lemma Abelian_DiagonalMap_eq {X Y : A} (f : X --> Y) :
    f ;; (DiagonalMap (Abelian_BinProducts A Y Y))
    = (DiagonalMap (Abelian_BinProducts A X X))
        ;; (BinProductArrow A (Abelian_BinProducts A Y Y)
                       (BinProductPr1 _ (Abelian_BinProducts A X X) ;; f)
                       (BinProductPr2 _ (Abelian_BinProducts A X X) ;; f)).
  Proof.
    unfold DiagonalMap.
    apply BinProductArrowsEq.
    repeat rewrite <- assoc.
    rewrite BinProductPr1Commutes.
    rewrite BinProductPr1Commutes.
    rewrite assoc. rewrite BinProductPr1Commutes.
    rewrite id_left. apply id_right.

    repeat rewrite <- assoc.
    rewrite BinProductPr2Commutes.
    rewrite BinProductPr2Commutes.
    rewrite assoc. rewrite BinProductPr2Commutes.
    rewrite id_left. apply id_right.
  Qed.

  Definition Abelian_op_eq_IdZero (X : A) :
    IdZeroMap (Abelian_BinProducts A X X)
              ;; CokernelArrow (Abelian_Zero A)
              (CokernelOfDiagonal (Abelian_BinProducts A X X))
    = identity _ .
  Proof.
    set (r := (isopair
                 (BinProductArrow A (Abelian_BinProducts A X X) (identity X)
                                  (ZeroArrow A (Abelian_Zero A) X X)
                                  ;; CokernelArrow (Abelian_Zero A)
                                  (Abelian_Cokernel A (DiagonalMap
                                                         (Abelian_BinProducts
                                                            A X X))))
                 (CokernelOfDiagonal_is_iso (Abelian_BinProducts A X X)))).
    cbn. fold r. rewrite assoc. unfold IdZeroMap.
    assert (e2 : BinProductArrow A (Abelian_BinProducts A X X) (identity X)
                                 (ZeroArrow A (Abelian_Zero A) X X) ;;
                                 CokernelArrow (Abelian_Zero A)
                                 (Abelian_Cokernel A (DiagonalMap
                                                        (Abelian_BinProducts
                                                           A X X)))
                 = r).
    {
      apply idpath.
    }
    rewrite e2. apply iso_inv_after_iso.
  Qed.

  Lemma Abelian_op_eq {X Y : A} (f : X --> Y) :
    CokernelArrow _ (CokernelOfDiagonal (Abelian_BinProducts A X X)) ;; f
    = (BinProductArrow A (Abelian_BinProducts A Y Y)
                       (BinProductPr1 _ (Abelian_BinProducts A X X) ;; f)
                       (BinProductPr2 _ (Abelian_BinProducts A X X) ;; f))
        ;; (CokernelArrow _ (CokernelOfDiagonal (Abelian_BinProducts A Y Y))).
  Proof.
    set (ar := (BinProductArrow A (Abelian_BinProducts A Y Y)
                       (BinProductPr1 _ (Abelian_BinProducts A X X) ;; f)
                       (BinProductPr2 _ (Abelian_BinProducts A X X) ;; f))
                  ;; CokernelArrow _
                  (CokernelOfDiagonal (Abelian_BinProducts A Y Y))).
    assert (H: DiagonalMap (Abelian_BinProducts A X X) ;; ar =
               ZeroArrow A (Abelian_Zero A) _ _).
    {
      unfold ar. rewrite assoc.
      rewrite <- (Abelian_DiagonalMap_eq f).
      rewrite <- assoc. rewrite CokernelCompZero.
      apply ZeroArrow_comp_right.
    }
    set (g := CokernelOut (Abelian_Zero A)
                           (CokernelOfDiagonal (Abelian_BinProducts A X X))
                           (CokernelOfDiagonal (Abelian_BinProducts A Y Y))
                           ar H).
    set (com := CokernelCommutes (Abelian_Zero A)
                           (CokernelOfDiagonal (Abelian_BinProducts A X X))
                           (CokernelOfDiagonal (Abelian_BinProducts A Y Y))
                           ar H).
    rewrite <- com.
    apply cancel_precomposition.

    set (e1 := Abelian_op_eq_IdZero X).
    set (e2 := Abelian_op_eq_IdZero Y).
    set (ar' := BinProductArrow A (Abelian_BinProducts A Y Y)
                                (BinProductPr1 A (Abelian_BinProducts A X X)
                                               ;; f)
                                (BinProductPr2 A (Abelian_BinProducts A X X)
                                               ;; f)).

    assert (e3 : IdZeroMap (Abelian_BinProducts A X X) ;; ar'
                 = f ;; IdZeroMap (Abelian_BinProducts A Y Y)).
    {
      unfold ar', IdZeroMap.
      apply BinProductArrowsEq. rewrite <- assoc.
      rewrite BinProductPr1Commutes. rewrite assoc.
      rewrite BinProductPr1Commutes. rewrite id_left.
      rewrite <- assoc. rewrite BinProductPr1Commutes.
      rewrite id_right. apply idpath.

      rewrite <- assoc.
      rewrite BinProductPr2Commutes. rewrite assoc.
      rewrite BinProductPr2Commutes.
      rewrite <- assoc. rewrite BinProductPr2Commutes.
      rewrite ZeroArrow_comp_right.
      apply ZeroArrow_comp_left.
    }

    rewrite <- (id_right A _ _ f). rewrite <- e2. rewrite assoc.
    rewrite <- e3. unfold ar'. rewrite <- assoc. fold ar.
    rewrite <- id_left. cbn. rewrite <- e1. rewrite <- assoc.
    apply cancel_precomposition. apply pathsinv0.
    apply com.
  Qed.


  (** Construction of morphisms to BinProducts. *)
  Definition Abelian_mor_to_BinProd {X Y : A} (f g : X --> Y) :
    A⟦X, (BinProductObject A (Abelian_BinProducts A Y Y))⟧
    :=  BinProductArrow _ (Abelian_BinProducts A Y Y) f g.

  Definition Abelian_mor_from_to_BinProd {X Y : A} (f g : X --> Y) :
    A⟦BinProductObject A (Abelian_BinProducts A X X),
      BinProductObject A (Abelian_BinProducts A Y Y)⟧
    :=  BinProductArrow _ (Abelian_BinProducts A Y Y)
                        (BinProductPr1 _ (Abelian_BinProducts A X X) ;; f)
                        (BinProductPr2 _ (Abelian_BinProducts A X X) ;; g).


  (** A few equations about the op. *)
  Definition Abelian_precategory_op_eq1 {X Y : A} (a b c d : X --> Y) :
    Abelian_minus_op (Abelian_mor_to_BinProd a b)
                     (Abelian_mor_to_BinProd c d)
    = Abelian_mor_to_BinProd (Abelian_minus_op a c)
                             (Abelian_minus_op b d).
  Proof.
    set (com1 := Abelian_op_eq (BinProductPr1 A (Abelian_BinProducts A Y Y))).
    set (com2 := Abelian_op_eq (BinProductPr2 A (Abelian_BinProducts A Y Y))).
    unfold Abelian_minus_op. unfold Abelian_mor_to_BinProd.
    apply BinProductArrowsEq.

    (* First *)
    rewrite <- assoc. rewrite com1.
    rewrite BinProductPr1Commutes. rewrite assoc.
    apply cancel_postcomposition.

    (* Another BinProductArrowsEq *)
    apply BinProductArrowsEq.
    rewrite BinProductPr1Commutes. rewrite <- assoc.
    rewrite BinProductPr1Commutes. rewrite assoc.
    rewrite BinProductPr1Commutes.
    rewrite BinProductPr1Commutes.
    apply idpath.

    rewrite BinProductPr2Commutes. rewrite <- assoc.
    rewrite BinProductPr2Commutes. rewrite assoc.
    rewrite BinProductPr2Commutes.
    rewrite BinProductPr1Commutes.
    apply idpath.

    (* Second *)
    rewrite <- assoc. rewrite com2.
    rewrite BinProductPr2Commutes. rewrite assoc.
    apply cancel_postcomposition.

    (* Another BinProductArrowsEq *)
    apply BinProductArrowsEq.
    rewrite BinProductPr1Commutes. rewrite <- assoc.
    rewrite BinProductPr1Commutes. rewrite assoc.
    rewrite BinProductPr1Commutes.
    rewrite BinProductPr2Commutes.
    apply idpath.

    rewrite BinProductPr2Commutes. rewrite <- assoc.
    rewrite BinProductPr2Commutes. rewrite assoc.
    rewrite BinProductPr2Commutes.
    rewrite BinProductPr2Commutes.
    apply idpath.
  Qed.

  Definition Abelian_precategory_op_eq2 {X Y : A} (a b c d : X --> Y) :
    Abelian_mor_to_BinProd
      (Abelian_mor_to_BinProd a b) (Abelian_mor_to_BinProd c d)
      ;; Abelian_mor_from_to_BinProd
      (CokernelArrow _ (CokernelOfDiagonal (Abelian_BinProducts A Y Y)))
      (CokernelArrow _ (CokernelOfDiagonal (Abelian_BinProducts A Y Y)))
    = Abelian_mor_to_BinProd
        ((Abelian_mor_to_BinProd a b)
           ;; (CokernelArrow _ (CokernelOfDiagonal
                                  (Abelian_BinProducts A Y Y))))
        ((Abelian_mor_to_BinProd c d)
            ;; (CokernelArrow _ (CokernelOfDiagonal
                                   (Abelian_BinProducts A Y Y)))).
  Proof.
    unfold Abelian_mor_to_BinProd.
    unfold Abelian_mor_from_to_BinProd.
    apply BinProductArrowsEq.

    (* Pr1 *)
    rewrite BinProductPr1Commutes. rewrite <- assoc.
    rewrite BinProductPr1Commutes. rewrite assoc.
    rewrite BinProductPr1Commutes. apply idpath.

    (* Pr2 *)
    rewrite BinProductPr2Commutes. rewrite <- assoc.
    rewrite BinProductPr2Commutes. rewrite assoc.
    rewrite BinProductPr2Commutes. apply idpath.
  Qed.

  Definition Abelian_precategory_op_eq3 {X Y : A} (a b c d : X --> Y) :
    Abelian_minus_op (Abelian_minus_op a b)
                     (Abelian_minus_op c d)
    = Abelian_minus_op (Abelian_minus_op a c)
                       (Abelian_minus_op b d).
  Proof.
    set (com := Abelian_op_eq
                  (CokernelArrow (Abelian_Zero A)
                                 (CokernelOfDiagonal
                                    (Abelian_BinProducts A Y Y)))).
    unfold Abelian_minus_op at 1.
    set (tmp := Abelian_precategory_op_eq1 a c b d).
    unfold Abelian_mor_to_BinProd in tmp.
    rewrite <- tmp.

    unfold Abelian_minus_op at 1. rewrite <- assoc. rewrite com.

    rewrite assoc.
    set (tmp1 := Abelian_precategory_op_eq2 a c b d).
    unfold Abelian_mor_to_BinProd, Abelian_mor_from_to_BinProd in tmp1.
    rewrite tmp1. apply cancel_postcomposition.

    unfold Abelian_minus_op. apply idpath.
  Qed.

  (** The zero element in a homset of A is given by the ZeroArrow. *)
  Definition Abelian_precategory_homset_zero (X Y : A) :
    A⟦X, Y⟧ := ZeroArrow A (Abelian_Zero A) X Y.

  (** Some equations involving Abelian_minus_op and Abelian_op. *)
  Definition Abelian_precategory_homset_zero_right' {X Y : A} (f : X --> Y) :
    Abelian_minus_op f (Abelian_precategory_homset_zero X Y) = f.
  Proof.
    unfold Abelian_precategory_homset_zero.
    unfold Abelian_minus_op.
    set (tmp := Abelian_op_eq_IdZero Y). unfold IdZeroMap in tmp.

    assert (e1 : BinProductArrow A (Abelian_BinProducts A Y Y) f
                                 (ZeroArrow A (Abelian_Zero A) X Y)
                 = f ;; BinProductArrow
                     A (Abelian_BinProducts A Y Y) (identity _)
                     (ZeroArrow A (Abelian_Zero A) Y Y)).
    {
      apply BinProductArrowsEq.
      rewrite BinProductPr1Commutes. rewrite <- assoc.
      rewrite BinProductPr1Commutes.
      rewrite id_right. apply idpath.

      rewrite BinProductPr2Commutes. rewrite <- assoc.
      rewrite BinProductPr2Commutes.
      rewrite ZeroArrow_comp_right. apply idpath.
    }

    rewrite e1. rewrite <- assoc. rewrite tmp.
    apply id_right.
  Qed.

  Definition Abelian_precategory_homset_zero_right {X Y : A} (f : X --> Y) :
    Abelian_op _ _ f (Abelian_precategory_homset_zero X Y) = f.
  Proof.
    unfold Abelian_precategory_homset_zero.
    unfold Abelian_op. unfold Abelian_minus_op at 2.
    use (pathscomp0 _ (Abelian_precategory_homset_zero_right' f)).

    assert (e1 :  (BinProductArrow A (Abelian_BinProducts A Y Y)
                                   (ZeroArrow A (Abelian_Zero A) X Y)
                                   (ZeroArrow A (Abelian_Zero A) X Y)
                                   ;; CokernelArrow (Abelian_Zero A)
                                   (CokernelOfDiagonal
                                      (Abelian_BinProducts A Y Y)))
                  = ZeroArrow A (Abelian_Zero A) _ _ ).
    {
      use (pathscomp0
             _ (ZeroArrow_comp_left A (Abelian_Zero A) _ _ _
                                    (CokernelArrow
                                       (Abelian_Zero A)
                                       (CokernelOfDiagonal
                                          (Abelian_BinProducts A Y Y))))).
      apply cancel_postcomposition.
      apply BinProductArrowsEq.
      rewrite BinProductPr1Commutes.
      rewrite ZeroArrow_comp_left. apply idpath.

      rewrite BinProductPr2Commutes.
      rewrite ZeroArrow_comp_left. apply idpath.
    }

    rewrite e1. apply idpath.
  Qed.

  Definition Abelian_precategory_homset_inv {X Y : A} (f : X --> Y) :
    A⟦X, Y⟧ := Abelian_minus_op (ZeroArrow _ (Abelian_Zero A) _ _) f.

  Definition Abelian_precategory_homset_inv_left' {X Y : A} (f : X --> Y) :
    Abelian_minus_op f f
    = (Abelian_precategory_homset_zero X Y).
  Proof.
    unfold Abelian_precategory_homset_zero. unfold Abelian_minus_op.

    assert (e1 : BinProductArrow A (Abelian_BinProducts A Y Y) f f
                 = f ;; BinProductArrow A (Abelian_BinProducts A Y Y)
                     (identity _ ) (identity _ )).
    {
      apply BinProductArrowsEq.
      rewrite BinProductPr1Commutes. rewrite <- assoc.
      rewrite BinProductPr1Commutes. rewrite id_right.
      apply idpath.

      rewrite BinProductPr2Commutes. rewrite <- assoc.
      rewrite BinProductPr2Commutes. rewrite id_right.
      apply idpath.
    }

    rewrite e1. rewrite <- assoc.
    rewrite CokernelCompZero.
    apply ZeroArrow_comp_right.
  Qed.

  Definition Abelian_precategory_homset_inv_left {X Y : A} (f : X --> Y) :
    Abelian_op _ _ (Abelian_precategory_homset_inv f) f
    = (Abelian_precategory_homset_zero X Y).
  Proof.
    unfold Abelian_precategory_homset_inv.
    unfold Abelian_precategory_homset_zero.
    unfold Abelian_op.
    rewrite Abelian_precategory_op_eq3.
    rewrite Abelian_precategory_homset_inv_left'.
    rewrite Abelian_precategory_homset_inv_left'.
    apply Abelian_precategory_homset_zero_right'.
  Qed.

  Definition Abelian_precategory_homset_zero_left {X Y : A} (f : X --> Y) :
    Abelian_op _ _ (Abelian_precategory_homset_zero X Y) f = f.
  Proof.
    rewrite <- (Abelian_precategory_homset_inv_left' f).
    set (tmp := Abelian_precategory_homset_zero_right' f).
    apply (maponpaths (fun g : _ => Abelian_op X Y (Abelian_minus_op f f) g))
      in tmp.
    apply pathsinv0 in tmp.
    use (pathscomp0 tmp).
    unfold Abelian_op.
    rewrite Abelian_precategory_op_eq3.
    rewrite Abelian_precategory_homset_zero_right'.
    rewrite Abelian_precategory_homset_zero_right'.
    rewrite Abelian_precategory_homset_inv_left'.
    rewrite Abelian_precategory_homset_zero_right'.
    apply idpath.
  Qed.

  Definition Abeliain_precategory_homset_comm' {X Y : A} (f g : X --> Y) :
    Abelian_minus_op
      (Abelian_minus_op (Abelian_precategory_homset_zero X Y) f) g
    = Abelian_minus_op
        (Abelian_minus_op (Abelian_precategory_homset_zero X Y) g) f.
  Proof.
    rewrite <- (Abelian_precategory_homset_zero_right' g).
    rewrite Abelian_precategory_op_eq3.
    rewrite (Abelian_precategory_homset_zero_right' f).
    rewrite (Abelian_precategory_homset_zero_right' g).
    apply idpath.
  Qed.

  Definition Abelian_precategory_homset_comm {X Y : A} (f g : X --> Y) :
    Abelian_op _ _ f g = Abelian_op _ _ g f.
  Proof.
    set (tmp1 := Abelian_precategory_homset_zero_left f).
    apply (maponpaths (fun h : _ => Abelian_op X Y h g)) in tmp1.
    apply pathsinv0 in tmp1. use (pathscomp0 tmp1).

    set (tmp2 := Abelian_precategory_homset_zero_left g).
    apply (maponpaths (fun h : _ => Abelian_op X Y h f)) in tmp2.
    use (pathscomp0 _ tmp2).
    unfold Abelian_op.
    rewrite (Abelian_precategory_op_eq3 _ _ _ g).
    rewrite (Abelian_precategory_op_eq3 _ _ _ f).
    rewrite (Abeliain_precategory_homset_comm' _ g).
    apply idpath.
  Qed.

  Definition Abelian_precategory_homset_assoc_eq1 {X Y : A} (f g : X --> Y) :
    Abelian_op _ _ f (Abelian_precategory_homset_inv g) =
    Abelian_minus_op f g.
  Proof.
    unfold Abelian_op.
    unfold Abelian_precategory_homset_inv.
    set (tmp := Abelian_precategory_homset_zero_left g).
    unfold Abelian_op in tmp.
    unfold Abelian_precategory_homset_zero in tmp.
    rewrite tmp. apply idpath.
  Qed.

  Definition Abelian_precategory_homset_inv_right {X Y : A} (f : X --> Y) :
    Abelian_op _ _ f (Abelian_precategory_homset_inv f) =
    Abelian_precategory_homset_zero X Y.
  Proof.
    rewrite Abelian_precategory_homset_assoc_eq1.
    apply Abelian_precategory_homset_inv_left'.
  Qed.

  Definition Abelian_precategory_homset_assoc_eq3 {X Y : A} (f g : X --> Y) :
    Abelian_minus_op (Abelian_precategory_homset_zero X Y)
                     (Abelian_minus_op f g)
    = Abelian_op _ _
                 (Abelian_minus_op (Abelian_precategory_homset_zero X Y) f) g.
  Proof.
    rewrite <- (Abelian_precategory_homset_inv_left'
                 (Abelian_precategory_homset_zero X Y)).
    unfold Abelian_op.
    rewrite Abelian_precategory_op_eq3.
    rewrite (Abelian_precategory_homset_inv_left'
               (Abelian_precategory_homset_zero X Y)).
    apply idpath.
  Qed.

  Definition Abelian_precategory_homset_assoc_eq4 {X Y : A} (f g : X --> Y) :
    Abelian_minus_op (Abelian_precategory_homset_zero X Y)
                     (Abelian_op _ _ f g)
    = Abelian_minus_op
        (Abelian_minus_op (Abelian_precategory_homset_zero X Y) f) g.
  Proof.
    set (tmp := Abelian_precategory_homset_inv_left'
                  (Abelian_precategory_homset_zero X Y)).
    apply (maponpaths (fun h : _ => Abelian_minus_op h (Abelian_op X Y f g)))
      in tmp.
    apply pathsinv0 in tmp. use (pathscomp0 tmp).
    unfold Abelian_op.
    rewrite Abelian_precategory_op_eq3.
    set (tmp2 := Abelian_precategory_homset_zero_left g).
    unfold Abelian_op in tmp2. rewrite tmp2.
    apply idpath.
  Qed.

  Definition Abelian_precategory_homset_assoc_eq5 {X Y : A} (f g h : X --> Y) :
     Abelian_op _ _ (Abelian_minus_op f g) h
     = Abelian_minus_op f (Abelian_minus_op g h).
  Proof.
    unfold Abelian_op.
    rewrite Abelian_precategory_op_eq3.
    rewrite Abelian_precategory_homset_zero_right'.
    apply idpath.
  Qed.

  Definition Abelian_precategory_homset_assoc {X Y : A} (f g h : X --> Y) :
     Abelian_op _ _ (Abelian_op _ _ f g) h
     = Abelian_op _ _ f (Abelian_op _ _ g h).
  Proof.
    set (tmp := Abelian_precategory_homset_zero_left h).
    apply (maponpaths (fun k : _ => Abelian_op X Y (Abelian_op X Y f g) k))
      in tmp.
    apply pathsinv0 in tmp. use (pathscomp0 tmp).
    unfold Abelian_op.
    rewrite Abelian_precategory_op_eq3.
    rewrite Abelian_precategory_homset_zero_right'.
    rewrite Abelian_precategory_op_eq3.
    rewrite Abelian_precategory_homset_zero_right'.
    apply idpath.
  Qed.

  (* TODO: change isPrecategorywithabgrops to PrecategoryWithAbgropsData *)
  Definition Abelian_precategory_isPrecategoryWithAbgrops :
    isPrecategoryWithAbgrops Abelian_precategory_PrecategoryWithBinops hs.
  Proof.
    unfold isPrecategoryWithAbgrops.
    intros x y.

    (* isabgrop *)
    split.
    use isgroppair.
    split.
    intros f g h. cbn.
    apply Abelian_precategory_homset_assoc.
    use isunitalpair. cbn.
    apply Abelian_precategory_homset_zero.
    split.
    intros f.
    apply Abelian_precategory_homset_zero_left.
    intros f.
    apply Abelian_precategory_homset_zero_right.

    cbn. use tpair. cbn. intros f.
    apply (Abelian_precategory_homset_inv f).
    cbn. split.

    intros f. apply Abelian_precategory_homset_inv_left.
    intros f. apply Abelian_precategory_homset_inv_right.

    intros f g.
    apply Abelian_precategory_homset_comm.
  Defined.

  (** We prove that Abelian_precategories are PrecategoriesWithAbgrops. *)
  Definition Abelian_precategory_PrecategoryWithAbgrops :
    PrecategoryWithAbgrops
    := mk_PrecategoryWithAbgrops
         Abelian_precategory_PrecategoryWithBinops
         hs
         Abelian_precategory_isPrecategoryWithAbgrops.

  (** We prove that Abelian_precategories are PreAddtitive. *)
  Definition Abelian_precategory_PreAdditive :
    PreAdditive.
  Proof.
    use (mk_PreAdditive Abelian_precategory_PrecategoryWithAbgrops).

    use mk_isPreAdditive.

    (* precomposition ismonoidfun *)
    intros x y z f.
    split.

    intros x' x'0. unfold PrecategoryWithAbgrops_premor.
    cbn. unfold Abelian_op. unfold Abelian_minus_op.
    cbn in x', x'0. rewrite assoc. apply cancel_postcomposition.

    assert (e2 : BinProductArrow
                   A (Abelian_BinProducts A z z) (f ;; x')
                   (BinProductArrow
                      A (Abelian_BinProducts A z z)
                      (ZeroArrow A (Abelian_Zero A) x z)
                      (f ;; x'0)
                      ;; CokernelArrow (Abelian_Zero A)
                      (CokernelOfDiagonal (Abelian_BinProducts A z z)))
                 = BinProductArrow
                   A (Abelian_BinProducts A z z) (f ;; x')
                   (BinProductArrow
                      A (Abelian_BinProducts A z z)
                      (f ;; ZeroArrow A (Abelian_Zero A) y z)
                      (f ;; x'0)
                      ;; CokernelArrow (Abelian_Zero A)
                      (CokernelOfDiagonal (Abelian_BinProducts A z z)))).
    {
      set (tmp := ZeroArrow_comp_right A (Abelian_Zero A) x y z f).
      apply (maponpaths
               (fun h : _ =>
                  BinProductArrow
                   A (Abelian_BinProducts A z z) (f ;; x')
                   (BinProductArrow
                      A (Abelian_BinProducts A z z)
                      h
                      (f ;; x'0)
                      ;; CokernelArrow (Abelian_Zero A)
                      (CokernelOfDiagonal (Abelian_BinProducts A z z)))))
        in tmp.
      apply pathsinv0 in tmp. apply tmp.
    }
    apply pathsinv0 in e2.
    use (pathscomp0 _ e2).
    rewrite <- precompWithBinProductArrow. rewrite <- assoc.
    rewrite <- precompWithBinProductArrow. apply idpath.

    unfold PrecategoryWithAbgrops_premor. cbn.
    unfold Abelian_precategory_homset_zero.
    apply ZeroArrow_comp_right.

    (* postcomposition is monoidfun *)
    intros x y z f.
    split.

    intros x' x'0. unfold PrecategoryWithAbgrops_postmor.
    cbn. unfold Abelian_op. unfold Abelian_minus_op.
    cbn in x', x'0.

    assert (e0 : BinProductArrow
                   A (Abelian_BinProducts A z z)
                   (ZeroArrow A (Abelian_Zero A) x z) (x'0 ;; f)
                 = BinProductArrow
                   A (Abelian_BinProducts A y y)
                   (ZeroArrow A (Abelian_Zero A) x y) x'0
                   ;; Abelian_mor_from_to_BinProd f f).
    {
      apply BinProductArrowsEq.
      unfold Abelian_mor_from_to_BinProd.
      rewrite <- assoc.
      rewrite BinProductPr1Commutes.
      rewrite BinProductPr1Commutes.
      rewrite assoc.
      rewrite BinProductPr1Commutes.
      rewrite ZeroArrow_comp_left.
      apply idpath.

      unfold Abelian_mor_from_to_BinProd.
      rewrite <- assoc.
      rewrite BinProductPr2Commutes.
      rewrite BinProductPr2Commutes.
      rewrite assoc.
      rewrite BinProductPr2Commutes.
      apply idpath.
    }

    rewrite e0.
    set (tmp := Abelian_op_eq f).
    unfold Abelian_mor_from_to_BinProd. rewrite <- assoc. rewrite <- assoc.
    rewrite <- tmp. rewrite assoc. rewrite assoc.

    rewrite <- (postcompWithBinProductArrow
                 A _ (Abelian_BinProducts A y y)).
    unfold BinProductOfArrows. rewrite <- assoc. rewrite <- assoc.
    rewrite <- tmp.
    apply idpath.

    unfold PrecategoryWithAbgrops_postmor. cbn.
    unfold Abelian_precategory_homset_zero.
    apply ZeroArrow_comp_left.
  Defined.

  (** Finally, we show that Abelian_precategories are Additive. *)
  Definition Abelian_precategory_Additive :
    Additive.
  Proof.
    use (mk_Additive Abelian_precategory_PreAdditive).
    use mk_isAdditive.
    exact (Abelian_Zero A).
    exact (BinDirectSums_from_BinProducts Abelian_precategory_PreAdditive
                                          hs (Abelian_Zero A)
                                          (Abelian_BinProducts A)).
  Defined.
End abelian_is_additive.
