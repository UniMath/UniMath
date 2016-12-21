(** * Additive functors *)
(** ** Contents
- Definition of additive functors
- Additive functor preserves BinDirectSums
 - Definition of PreservesBinDirectSums
   - Additive funtor preserves zero.
 - Preserves IdIn1, IdIn2, Unit1, Unit2, and Id of BinDirectSum
 - Preserves BinDirectCoproducts
 - Preserves BinDirectProducts
 - Preserves BinDirectSums
- If a functor preserves BinDirectSums, then it is additive
 - Preserves unel
 - Commutes with BinOp
 - isAdditiveFunctor
- The natural additive functor to quotient
 *)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.Foundations.Algebra.BinaryOperations.
Require Import UniMath.Foundations.Algebra.Monoids_and_Groups.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.precategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.


(** * Definition of additive functor
   Functor is additive if for any two objects a1 a2 of an additive category A, the map on morphisms
   A⟦a1, a2⟧ -> B⟦F a1, F a2⟧ is a morphism of abelian groups. *)
Section def_additivefunctor.

  (** ** isAdditiveFunctor *)

  Definition isAdditiveFunctor {A B : Additive} (F : functor A B) : UU :=
    Π (a1 a2 : A), @ismonoidfun (to_abgrop a1 a2) (to_abgrop (F a1) (F a2)) (# F).

  Definition mk_isAdditiveFunctor {A B : Additive} (F : functor A B)
             (H : Π (a1 a2 : A),
                  @ismonoidfun (to_abgrop a1 a2) (to_abgrop (F a1) (F a2)) (# F)) :
    isAdditiveFunctor F.
  Proof.
    intros a1 a2.
    exact (H a1 a2).
  Qed.

  Definition mk_isAdditiveFunctor' {A B : Additive} (F : functor A B)
             (H1 : Π (a1 a2 : A), (# F (ZeroArrow (to_Zero A) a1 a2)) =
                                  ZeroArrow (to_Zero B) (F a1) (F a2))
             (H2 : Π (a1 a2 : A) (f g : A⟦a1, a2⟧), # F (to_binop _ _ f g) =
                                                    to_binop _ _ (# F f) (# F g)) :
    isAdditiveFunctor F.
  Proof.
    use mk_isAdditiveFunctor.
    intros a1 a2.
    split.
    - intros f g. apply (H2 a1 a2 f g).
    - set (tmp := PreAdditive_unel_zero A (to_Zero A) a1 a2).
      unfold to_unel in tmp. rewrite tmp. clear tmp.
      set (tmp := PreAdditive_unel_zero B (to_Zero B) (F a1) (F a2)).
      unfold to_unel in tmp. rewrite tmp. clear tmp.
      apply (H1 a1 a2).
  Qed.

  Lemma isaprop_isAdditiveFunctor {A B : Additive} (F : functor A B) :
    isaprop (isAdditiveFunctor F).
  Proof.
    apply impred_isaprop. intros t.
    apply impred_isaprop. intros t0.
    apply isapropismonoidfun.
  Qed.

  (** ** Additive functor *)

  Definition AdditiveFunctor (A B : Additive) : UU := Σ F : (functor A B), isAdditiveFunctor F.

  Definition mk_AdditiveFunctor {A B : Additive} (F : functor A B) (H : isAdditiveFunctor F) :
    AdditiveFunctor A B := tpair _ F H.

  (** Accessor functions *)
  Definition AdditiveFunctor_Functor {A B : Additive} (F : AdditiveFunctor A B) :
    functor A B := pr1 F.
  Coercion AdditiveFunctor_Functor : AdditiveFunctor >-> functor.

  Definition AdditiveFunctor_isAdditiveFunctor {A B : Additive} (F : AdditiveFunctor A B) :
    isAdditiveFunctor (AdditiveFunctor_Functor F) := pr2 F.

End def_additivefunctor.


(** * Additive functor preserves BinDirectSums
   We say that a functor F between additive categories A and B preserves BinDirectSums if for any
   BinDirectSum (a1 ⊕ a2, in1, in2, pr1, pr2) in A, the data (F(a1 ⊕ a2), F(in1), F(in2), F(pr1),
   F(pr2)) is a BinDirectSum in B. *)
Section additivefunctor_preserves_bindirectsums.

  Definition PreservesBinDirectSums {A B : Additive} (F : functor A B) : UU :=
    Π (a1 a2 : A) (DS : BinDirectSumCone A a1 a2),
    isBinDirectSumCone B (F a1) (F a2) (F DS)
                       (# F (to_In1 A DS)) (# F (to_In2 A DS))
                       (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS)).

  Lemma isaprop_PreservesBinDirectSums {A B : Additive} (hs : has_homsets B) (F : functor A B) :
    isaprop (PreservesBinDirectSums F).
  Proof.
    apply impred_isaprop. intros t.
    apply impred_isaprop. intros t0.
    apply impred_isaprop. intros DS.
    apply isaprop_isBinDirectSumCone.
    apply hs.
  Qed.

  Lemma AdditiveFunctorUnel {A B : Additive} (F : AdditiveFunctor A B)
        (a1 a2 : A) : # F (to_unel a1 a2) = to_unel (F a1) (F a2).
  Proof.
    unfold to_unel.
    apply (pr2 (pr2 F a1 a2)).
  Qed.

  Lemma AdditiveFunctorZeroArrow {A B : Additive} (F : AdditiveFunctor A B)
        (a1 a2 : A) : # F (ZeroArrow (to_Zero A) a1 a2) = ZeroArrow (to_Zero B) (F a1) (F a2).
  Proof.
    rewrite <- PreAdditive_unel_zero. rewrite <- PreAdditive_unel_zero.
    apply AdditiveFunctorUnel.
  Qed.

  Lemma AdditiveFunctorLinear {A B : Additive} (F : AdditiveFunctor A B) {a1 a2 : A}
        (f g : a1 --> a2) : # F (to_binop _ _ f g) = to_binop _ _ (# F f) (# F g).
  Proof.
    apply (pr1 (pr2 F a1 a2)).
  Qed.

  Lemma AdditiveFunctorInv {A B : Additive} (F : AdditiveFunctor A B) {a1 a2 : A} (f : a1 --> a2) :
    # F (to_inv f) = to_inv (# F f).
  Proof.
    apply (to_lcan _ (# F f)). rewrite <- AdditiveFunctorLinear.
    rewrite rinvax. rewrite AdditiveFunctorUnel. rewrite rinvax.
    apply idpath.
  Qed.

  (** Additive functor preserves zeros. *)
  Lemma AdditiveFunctorPreservesBinDirectSums_zero {A B : Additive} (F : AdditiveFunctor A B) :
    isZero B (F (to_Zero A)).
  Proof.
    set (isadd0 := AdditiveFunctor_isAdditiveFunctor F (to_Zero A) (to_Zero A)).
    set (unel := to_unel (to_Zero A) (to_Zero A)).
    set (tmp := (pr2 isadd0)). cbn in tmp.
    set (tmp1 := PreAdditive_unel_zero A (to_Zero A) (to_Zero A) (to_Zero A)).
    unfold to_unel in tmp1. rewrite tmp1 in tmp. clear tmp1.
    assert (tmp2 : identity (to_Zero A) = ZeroArrow (to_Zero A) _ _) by apply ArrowsToZero.
    rewrite <- tmp2 in tmp. clear tmp2.
    assert (X : # F (identity (to_Zero A)) = identity (F (to_Zero A))) by apply functor_id.
    set (tmp2 := PreAdditive_unel_zero B (to_Zero B) (F (to_Zero A)) (F (to_Zero A))).
    unfold to_unel in tmp2. rewrite tmp2 in tmp. clear tmp2.
    assert (X0 : iso (F (to_Zero A)) (to_Zero B)).
    {
      use isopair.
      - apply (ZeroArrowTo (F (to_Zero A))).
      - use is_iso_qinv.
        apply (ZeroArrowFrom (F (to_Zero A))).
        split.
        + rewrite <- X. rewrite tmp. apply ZeroArrowEq.
        + apply ArrowsToZero.
    }
    apply (IsoToisZero B (to_Zero B) X0).
  Qed.


  (** ** F preserves IdIn1, IdIn2, IdUnit1, IdUnit2, and Id of BinDirectSum *)

  Local Lemma AdditiveFunctorPreservesBinDirectSums_idin1 {A B : Additive} (F : AdditiveFunctor A B)
        {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    (# F (to_In1 A DS)) ;; (# F (to_Pr1 A DS)) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite (to_IdIn1 A DS). apply functor_id.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_idin2 {A B : Additive} (F : AdditiveFunctor A B)
        {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    (# F (to_In2 A DS)) ;; (# F (to_Pr2 A DS)) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite (to_IdIn2 A DS). apply functor_id.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_unit1 {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    (# F (to_In1 A DS)) ;; (# F (to_Pr2 A DS)) = to_unel (F a1) (F a2).
  Proof.
    rewrite <- functor_comp. rewrite (to_Unel1 A DS). apply AdditiveFunctorUnel.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_unit2 {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    (# F (to_In2 A DS)) ;; (# F (to_Pr1 A DS)) = to_unel (F a2) (F a1).
  Proof.
    rewrite <- functor_comp. rewrite (to_Unel2 A DS). apply AdditiveFunctorUnel.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_id {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    to_binop _ _
             ((# F (to_Pr1 A DS)) ;; (# F (to_In1 A DS)))
             ((# F (to_Pr2 A DS)) ;; (# F (to_In2 A DS))) = identity _.
  Proof.
    rewrite <- functor_comp. rewrite <- functor_comp.
    rewrite <- AdditiveFunctorLinear. rewrite (to_BinOpId A DS). apply functor_id.
  Qed.


  (** ** Preserves BinCoproducts *)

  Local Lemma AdditiveFunctorPreservesBinDirectSums_isBinCoproductCocone_id1 {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    let BDS := to_BinDirectSums B (F a1) (F a2) in
    ToBinDirectSum B BDS (# F (to_Pr1 A DS))
                   (# F (to_Pr2 A DS)) ;; to_binop (to_BinDirectSums B (F a1) (F a2)) (F DS)
                   ((to_Pr1 B (to_BinDirectSums B (F a1) (F a2))) ;; # F (to_In1 A DS))
                   (to_Pr2 B (to_BinDirectSums B (F a1) (F a2)) ;; # F (to_In2 A DS)) =
    identity (F DS).
  Proof.
    cbn zeta.
    set (BDS := to_BinDirectSums B (F a1) (F a2)).
    set (mor := ToBinDirectSum B BDS (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS))).
    set (invmor := to_binop _ _ ((to_Pr1 B BDS) ;; (# F (to_In1 A DS)))
                            ((to_Pr2 B BDS) ;; (# F (to_In2 A DS)))).
    rewrite <- functor_id. rewrite <- (to_BinOpId A DS).
    set (isadd := AdditiveFunctor_isAdditiveFunctor F DS DS).
    set (tmp := pr1 isadd ((to_Pr1 A DS) ;; (to_In1 A DS)) ((to_Pr2 A DS) ;; (to_In2 A DS))).
    cbn in *. rewrite tmp. clear tmp. clear isadd.
    rewrite (functor_comp F). rewrite (functor_comp F).
    rewrite <- (BinDirectSumPr1Commutes B BDS _ (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS))). fold mor.
    rewrite <- (BinDirectSumPr2Commutes B BDS _ (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS))). fold mor.
    rewrite <- assoc. rewrite <- assoc. rewrite <- (@to_premor_linear' B). apply idpath.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_isBinCoproductCocone_id2' {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    let BDS := to_BinDirectSums B (F a1) (F a2) in
    let mor := ToBinDirectSum B BDS (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS)) in
    to_binop BDS BDS
             ((to_Pr1 B BDS) ;; (# F (to_In1 A DS)) ;; mor ;; (to_Pr1 B BDS) ;; (to_In1 B BDS))
             ((to_Pr2 B BDS) ;; (# F (to_In2 A DS)) ;; mor ;; (to_Pr2 B BDS) ;; (to_In2 B BDS)) =
    to_binop BDS BDS
             ((to_Pr1 B BDS) ;; (# F (to_In1 A DS)) ;; mor)
             ((to_Pr2 B BDS) ;; (# F (to_In2 A DS)) ;; mor)
             ;; identity _.
  Proof.
    cbn zeta.
    set (BDS := (to_BinDirectSums B (F a1) (F a2))).
    set (mor := (ToBinDirectSum B BDS (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS)))).
    set (invmor := (to_binop _ _
                             ((to_Pr1 B BDS) ;; (# F (to_In1 A DS)))
                             ((to_Pr2 B BDS) ;; (# F (to_In2 A DS))))).
    rewrite <- to_postmor_linear'. rewrite <- (to_BinOpId B BDS).
    rewrite to_premor_linear'.
    rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ (to_Pr1 B BDS)).
    rewrite <- (assoc _ _ (to_Pr1 B BDS)).
    rewrite <- (assoc _ _ (to_Pr2 B BDS)).
    rewrite <- (assoc _ _ (to_Pr2 B BDS)).
    unfold mor.
    rewrite (BinDirectSumPr1Commutes B BDS).
    rewrite (BinDirectSumPr2Commutes B BDS).
    rewrite to_postmor_linear'.
    rewrite <- (assoc _ (# F (to_In1 A DS))). rewrite <- functor_comp. rewrite (to_IdIn1 A DS).
    rewrite <- (assoc _ (# F (to_In2 A DS))). rewrite <- functor_comp. rewrite (to_IdIn2 A DS).
    rewrite <- (assoc _ (# F (to_In2 A DS))). rewrite <- functor_comp. rewrite (to_Unel2 A DS).
    rewrite to_postmor_linear'.
    rewrite functor_id. rewrite functor_id. rewrite id_right. rewrite id_right.
    rewrite AdditiveFunctorUnel.
    rewrite to_premor_unel'. rewrite to_postmor_unel'. rewrite to_runax'.
    rewrite to_postmor_linear'.
    rewrite <- (assoc _ (# F (to_In1 A DS))). rewrite <- functor_comp. rewrite (to_Unel1 A DS).
    rewrite <- (assoc _ (# F (to_In2 A DS))). rewrite <- functor_comp. rewrite (to_IdIn2 A DS).
    rewrite functor_id. rewrite AdditiveFunctorUnel. rewrite id_right.
    rewrite to_premor_unel'. rewrite to_lunax'. apply idpath.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_isBinCoproductCocone_id2 {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    to_binop (to_BinDirectSums B (F a1) (F a2)) (F DS)
             ((to_Pr1 B (to_BinDirectSums B (F a1) (F a2))) ;; # F (to_In1 A DS))
             ((to_Pr2 B (to_BinDirectSums B (F a1) (F a2))) ;; # F (to_In2 A DS)) ;;
             ToBinDirectSum B (to_BinDirectSums B (F a1) (F a2))
             (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS)) =
    identity (to_BinDirectSums B (F a1) (F a2)).
  Proof.
    set (BDS := to_BinDirectSums B (F a1) (F a2)).
    set (mor := ToBinDirectSum B BDS (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS))).
    set (invmor := (to_binop _ _
                             ((to_Pr1 B BDS) ;; (# F (to_In1 A DS)))
                             ((to_Pr2 B BDS) ;; (# F (to_In2 A DS))))).
    rewrite <- (to_BinOpId B BDS).
    rewrite <- (id_right (to_Pr1 B BDS)).
    rewrite <- (id_right (to_Pr2 B BDS)).
    rewrite <- functor_id. rewrite <- functor_id.
    rewrite <- (to_IdIn1 A DS). rewrite <- (to_IdIn2 A DS).
    rewrite functor_comp. rewrite functor_comp.
    rewrite <- (BinDirectSumPr1Commutes B BDS _ (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS))). fold mor.
    rewrite <- (BinDirectSumPr2Commutes B BDS _ (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS))). fold mor.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    unfold mor at 2 3.
    unfold BDS. rewrite AdditiveFunctorPreservesBinDirectSums_isBinCoproductCocone_id2'. fold BDS.
    fold mor. rewrite id_right.
    rewrite <- to_postmor_linear'. apply idpath.
  Qed.

  (** Additive functor preserves BinCoproductCocones *)
  Local Lemma AdditiveFunctorPreservesBinDirectSums_isBinCoproductCocone {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    isBinCoproductCocone B (F a1) (F a2) (F DS) (# F (to_In1 A DS)) (# F (to_In2 A DS)).
  Proof.
    set (BDS := (to_BinDirectSums B (F a1) (F a2))).
    set (mor := (ToBinDirectSum B BDS (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS)))).
    set (invmor := to_binop _ _
                      ((to_Pr1 B BDS) ;; (# F (to_In1 A DS)))
                      ((to_Pr2 B BDS) ;; (# F (to_In2 A DS)))).
    assert (i' : is_iso mor).
    {
      use is_iso_qinv.
      - exact invmor.
      - split.
        + exact (AdditiveFunctorPreservesBinDirectSums_isBinCoproductCocone_id1 F DS).
        + exact (AdditiveFunctorPreservesBinDirectSums_isBinCoproductCocone_id2 F DS).
    }
    set (i := isopair mor i').
    assert (e : inv_from_iso i = invmor).
    {
      apply pathsinv0.
      use inv_iso_unique'.
      unfold precomp_with.
      exact (AdditiveFunctorPreservesBinDirectSums_isBinCoproductCocone_id1 F DS).
    }
    set (BC := BinDirectSum_BinCoproduct B BDS).
    set (isBC := iso_to_isBinCoproductCocone B (@to_has_homsets B) BC i).
    cbn in isBC. rewrite e in isBC. unfold invmor in isBC. cbn in isBC.
    (* Rewrite isBC to get the goal *)
    rewrite to_premor_linear' in isBC.
    rewrite assoc in isBC. rewrite assoc in isBC.
    rewrite (to_IdIn1 B BDS) in isBC.
    rewrite (to_Unel1 B BDS) in isBC.
    rewrite to_postmor_unel' in isBC.
    rewrite id_left in isBC.
    rewrite to_premor_linear' in isBC.
    rewrite assoc in isBC. rewrite assoc in isBC.
    rewrite (to_IdIn2 B BDS) in isBC.
    rewrite (to_Unel2 B BDS) in isBC.
    rewrite to_postmor_unel' in isBC.
    rewrite id_left in isBC.
    rewrite to_runax' in isBC.
    rewrite to_lunax' in isBC.
    exact isBC.
  Qed.


  (** ** Preserves BinProducts *)

  Local Lemma AdditiveFunctorPreservesBinDirectSums_isBinProductCone_id1 {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    let BDS := to_BinDirectSums B (F a1) (F a2) in
    let mor := FromBinDirectSum B BDS (# F (to_In1 A DS)) (# F (to_In2 A DS)) in
    to_binop (F DS) (to_BinDirectSums B (F a1) (F a2))
             ((# F (to_Pr1 A DS)) ;; (to_In1 B BDS))
             ((# F (to_Pr2 A DS)) ;; (to_In2 B BDS)) ;; mor =
    identity (F DS).
  Proof.
    cbn zeta.
    set (BDS := to_BinDirectSums B (F a1) (F a2)).
    set (mor := FromBinDirectSum B BDS (# F (to_In1 A DS)) (# F (to_In2 A DS))).
    set (invmor := to_binop _ _
                            ((# F (to_Pr1 A DS)) ;; (to_In1 B BDS))
                            ((# F (to_Pr2 A DS)) ;; (to_In2 B BDS))).
    rewrite <- functor_id. rewrite <- (to_BinOpId A DS).
    rewrite AdditiveFunctorLinear.
    rewrite functor_comp. rewrite functor_comp.
    rewrite <- (BinDirectSumIn1Commutes B BDS _ (# F (to_In1 A DS)) (# F (to_In2 A DS))). fold mor.
    rewrite <- (BinDirectSumIn2Commutes B BDS _ (# F (to_In1 A DS)) (# F (to_In2 A DS))). fold mor.
    rewrite assoc. rewrite assoc.
    rewrite <- to_postmor_linear'.
    apply idpath.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_isBinProductCone_id2' {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    let BDS := to_BinDirectSums B (F a1) (F a2) in
    let mor := FromBinDirectSum B BDS (# F (to_In1 A DS)) (# F (to_In2 A DS)) in
    to_binop BDS BDS
      (to_Pr1 B BDS ;; to_In1 B BDS ;; mor ;; # F (to_Pr1 A DS) ;; to_In1 B BDS)
      (to_Pr2 B BDS ;; to_In2 B BDS ;; mor ;; # F (to_Pr2 A DS) ;; to_In2 B BDS) =
    (identity _)
      ;; (to_binop BDS BDS
                   (mor ;; (# F (to_Pr1 A DS)) ;; (to_In1 B BDS))
                   (mor ;; (# F (to_Pr2 A DS)) ;; (to_In2 B BDS))).
  Proof.
    cbn zeta.
    set (BDS := to_BinDirectSums B (F a1) (F a2)).
    set (mor := FromBinDirectSum B BDS (# F (to_In1 A DS)) (# F (to_In2 A DS))).
    set (invmor := to_binop _ _
                            ((# F (to_Pr1 A DS)) ;; (to_In1 B BDS))
                            ((# F (to_Pr2 A DS)) ;; (to_In2 B BDS))).
    rewrite to_premor_linear'. rewrite <- (to_BinOpId B BDS).
    rewrite to_postmor_linear'. rewrite to_postmor_linear'.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc.
    rewrite assoc. rewrite assoc.
    rewrite <- (assoc _ _ mor). rewrite <- (assoc _ _ mor).
    unfold mor.
    rewrite (BinDirectSumIn1Commutes B BDS). rewrite (BinDirectSumIn2Commutes B BDS).
    rewrite <- (assoc _ _ (# F (to_Pr1 A DS))). rewrite <- (assoc _ _ (# F (to_Pr1 A DS))).
    rewrite <- (assoc _ _ (# F (to_Pr2 A DS))). rewrite <- (assoc _ _ (# F (to_Pr2 A DS))).
    rewrite <- functor_comp. rewrite <- functor_comp.
    rewrite <- functor_comp. rewrite <- functor_comp.
    rewrite (to_IdIn1 A DS). rewrite (to_IdIn2 A DS).
    rewrite (to_Unel1 A DS). rewrite (to_Unel2 A DS).
    rewrite functor_id. rewrite functor_id.
    rewrite AdditiveFunctorUnel. rewrite AdditiveFunctorUnel.
    rewrite id_right. rewrite id_right.
    rewrite to_premor_unel'. rewrite to_premor_unel'.
    rewrite to_postmor_unel'. rewrite to_postmor_unel'.
    rewrite to_lunax'. rewrite to_runax'.
    apply idpath.
  Qed.

  Local Lemma AdditiveFunctorPreservesBinDirectSums_isBinProductCone_id2 {A B : Additive}
        (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    let BDS := to_BinDirectSums B (F a1) (F a2) in
    let mor := FromBinDirectSum B BDS (# F (to_In1 A DS)) (# F (to_In2 A DS)) in
    mor ;; (to_binop (F DS) BDS (# F (to_Pr1 A DS) ;; to_In1 B BDS)
                     (# F (to_Pr2 A DS) ;; to_In2 B BDS)) =
    identity _.
  Proof.
    cbn zeta.
    set (BDS := to_BinDirectSums B (F a1) (F a2)).
    set (mor := FromBinDirectSum B BDS (# F (to_In1 A DS)) (# F (to_In2 A DS))).
    set (invmor := to_binop _ _
                            ((# F (to_Pr1 A DS)) ;; (to_In1 B BDS))
                            ((# F (to_Pr2 A DS)) ;; (to_In2 B BDS))).
    rewrite <- (to_BinOpId B BDS).
    rewrite <- (id_right (to_Pr1 B BDS)). rewrite <- (id_right (to_Pr2 B BDS)).
    rewrite <- functor_id. rewrite <- functor_id.
    rewrite <- (to_IdIn1 A DS). rewrite <- (to_IdIn2 A DS).
    rewrite functor_comp. rewrite functor_comp.
    rewrite <- (BinDirectSumIn1Commutes B BDS _ (# F (to_In1 A DS)) (# F (to_In2 A DS))). fold mor.
    rewrite <- (BinDirectSumIn2Commutes B BDS _ (# F (to_In1 A DS)) (# F (to_In2 A DS))). fold mor.
    rewrite assoc. rewrite assoc. rewrite assoc. rewrite assoc. unfold mor, BDS.
    rewrite (AdditiveFunctorPreservesBinDirectSums_isBinProductCone_id2' F DS).
    fold BDS. fold mor. rewrite id_left.
    rewrite <- assoc. rewrite <- assoc.
    rewrite <- to_premor_linear'.
    apply idpath.
  Qed.

  (** Additive functor preserves BinProductCones *)
  Local Lemma AdditiveFunctorPreservesBinDirectSums_isBinProductCone
        {A B : Additive} (F : AdditiveFunctor A B) {a1 a2 : A} (DS : BinDirectSumCone A a1 a2) :
    isBinProductCone B (F a1) (F a2) (F DS) (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS)).
  Proof.
    set (BDS := to_BinDirectSums B (F a1) (F a2)).
    set (mor := FromBinDirectSum B BDS (# F (to_In1 A DS)) (# F (to_In2 A DS))).
    set (invmor := to_binop _ _
                      ((# F (to_Pr1 A DS)) ;; (to_In1 B BDS))
                      ((# F (to_Pr2 A DS)) ;; (to_In2 B BDS))).
    assert (i' : is_iso invmor).
    {
      use is_iso_qinv.
      - exact mor.
      - split.
        + exact (AdditiveFunctorPreservesBinDirectSums_isBinProductCone_id1 F DS).
        + exact (AdditiveFunctorPreservesBinDirectSums_isBinProductCone_id2 F DS).
    }
    set (i := isopair invmor i').
    set (BC := BinDirectSum_BinProduct B BDS).
    set (isBC := iso_to_isBinProductCone B (@to_has_homsets B) BC i).
    cbn in isBC.
    rewrite (to_postmor_linear' (# F (to_Pr1 A DS) ;; to_In1 B BDS)
                                (# F (to_Pr2 A DS) ;; to_In2 B BDS)) in isBC.
    rewrite <- assoc in isBC. rewrite <- assoc in isBC.
    rewrite (to_IdIn1 B BDS) in isBC. rewrite (to_Unel2 B BDS) in isBC.
    rewrite id_right in isBC. rewrite to_premor_unel' in isBC. rewrite to_runax' in isBC.
    unfold invmor in isBC. rewrite to_postmor_linear' in isBC.
    rewrite <- assoc in isBC. rewrite <- assoc in isBC.
    rewrite (to_IdIn2 B BDS) in isBC. rewrite (to_Unel1 B BDS) in isBC.
    rewrite id_right in isBC. rewrite to_premor_unel' in isBC. rewrite to_lunax' in isBC.
    exact isBC.
  Qed.


  (** ** Preserves BinDirectSums *)

  (** An additive functor preserves BinDirectSums *)
  Lemma AdditiveFunctorPreservesBinDirectSums {A B : Additive} (F : AdditiveFunctor A B) :
    PreservesBinDirectSums F.
  Proof.
    intros a1 a2 DS.
    use mk_isBinDirectSumCone.
    - use (AdditiveFunctorPreservesBinDirectSums_isBinCoproductCocone F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_isBinProductCone F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_idin1 F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_idin2 F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_unit1 F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_unit2 F DS).
    - use (AdditiveFunctorPreservesBinDirectSums_id F DS).
  Qed.

End additivefunctor_preserves_bindirectsums.


(** * Additive criteria
   In this section we show that a functor between additive categories which preserves BinDirectSums
   is additive. *)
Section additivefunctor_criteria.


  (** ** Preserves unel *)

  (** A functor which preserves binary direct sums preserves zero objects. *)
  Lemma isAdditiveCriteria_isZero {A B : Additive} (F : functor A B)
        (H : PreservesBinDirectSums F) : isZero B (F (to_Zero A)).
  Proof.
    set (DS := to_BinDirectSums A (to_Zero A) (to_Zero A)).
    set (isBDS := H (to_Zero A) (to_Zero A) DS).
    assert (e1 : (# F (to_In1 A DS)) = (# F (to_In2 A DS))).
    {
      apply maponpaths.
      apply ArrowsFromZero.
    }
    assert (e2 : (# F (to_Pr1 A DS)) = (# F (to_Pr2 A DS))).
    {
      apply maponpaths.
      apply ArrowsToZero.
    }
    rewrite e1 in isBDS. rewrite e2 in isBDS. clear e1 e2.
    set (BDS := mk_BinDirectSumCone _ _ _ _ _ _ _ _ isBDS).
    use mk_isZero.
    - intros b.
      use tpair.
      + apply (ZeroArrow (to_Zero B) _ _).
      + cbn. intros t.
        use (pathscomp0 (!(BinDirectSumIn1Commutes B BDS _ t (ZeroArrow (to_Zero B) _ _)))).
        use (pathscomp0 _ (BinDirectSumIn2Commutes B BDS _ t (ZeroArrow (to_Zero B) _ _))).
        cbn. apply cancel_precomposition. apply idpath.
    - intros a.
      use tpair.
      + apply (ZeroArrow (to_Zero B) _ _).
      + cbn. intros t.
        use (pathscomp0 (!(BinDirectSumPr1Commutes B BDS _ t (ZeroArrow (to_Zero B) _ _)))).
        use (pathscomp0 _ (BinDirectSumPr2Commutes B BDS _ t (ZeroArrow (to_Zero B) _ _))).
        cbn. apply cancel_postcomposition. apply idpath.
  Qed.

  (** F preserves unel *)
  Local Corollary isAdditiveCriteria_preservesUnel {A B : Additive} (F : functor A B)
        (H : PreservesBinDirectSums F) (a1 a2 : A) :
    (# F (to_unel a1 a2)) = (to_unel (F a1) (F a2)).
  Proof.
    set (Z := mk_Zero (F (to_Zero A)) (isAdditiveCriteria_isZero F H)).
    rewrite (PreAdditive_unel_zero A (to_Zero A) a1 a2).
    rewrite (PreAdditive_unel_zero B Z (F a1) (F a2)).
    unfold ZeroArrow. rewrite functor_comp. cbn.
    assert (e1 : # F (ZeroArrowTo a1) = @ZeroArrowTo B Z (F a1)).
    {
      apply (ArrowsToZero B Z).
    }
    assert (e2 : # F (ZeroArrowFrom a2) = @ZeroArrowFrom B Z (F a2)).
    {
      apply (ArrowsFromZero B Z).
    }
    rewrite e1. rewrite e2. apply idpath.
  Qed.


  (** ** Commutes with binop *)

  (** F commutes with addition of projections from a1 ⊕ a1 *)
  Local Lemma isAdditiveCriteria_isBinopFun_Pr {A B : Additive} (F : functor A B)
        (H : PreservesBinDirectSums F) {a1 a2 : A} (DS : BinDirectSumCone A a1 a1):
    # F (to_binop DS a1 (to_Pr1 A DS) (to_Pr2 A DS)) =
    to_binop (F DS) (F a1) (# F (to_Pr1 A DS)) (# F (to_Pr2 A DS)).
  Proof.
    set (isBDS := H a1 a1 DS).
    set (BDS := mk_BinDirectSumCone _ _ _ _ _ _ _ _ isBDS).
    use (FromBinDirectSumsEq B BDS); cbn.
    - rewrite <- functor_comp.
      rewrite to_premor_linear'.
      rewrite (to_IdIn1 A DS). rewrite (to_Unel1 A DS).
      rewrite to_runax'. rewrite functor_id.
      rewrite to_premor_linear'.
      rewrite <- functor_comp. rewrite <- functor_comp.
      rewrite (to_IdIn1 A DS). rewrite (to_Unel1 A DS).
      rewrite functor_id. rewrite (isAdditiveCriteria_preservesUnel _ H).
      rewrite to_runax'. apply idpath.
    - rewrite <- functor_comp.
      rewrite to_premor_linear'.
      rewrite (to_Unel2 A DS). rewrite (to_IdIn2 A DS). rewrite to_lunax'. rewrite functor_id.
      rewrite to_premor_linear'.
      rewrite <- functor_comp. rewrite <- functor_comp.
      rewrite (to_Unel2 A DS). rewrite (to_IdIn2 A DS).
      rewrite (isAdditiveCriteria_preservesUnel _ H). rewrite functor_id. rewrite to_lunax'.
      apply idpath.
  Qed.

  Local Lemma isAdditiveCriteria_BinOp_eq {A B : Additive} (F : functor A B)
        (H : PreservesBinDirectSums F) {a1 a2 : A} (f g : A⟦a1, a2⟧) :
    let DS := to_BinDirectSums A a2 a2 in
    to_binop a1 a2 f g = (to_binop a1 DS (f ;; (to_In1 A DS)) (g ;; (to_In2 A DS)))
                           ;; (to_binop DS a2 (to_Pr1 A DS) (to_Pr2 A DS)).
  Proof.
    cbn zeta.
    set (DS := to_BinDirectSums A a2 a2).
    set (isBDS := H a2 a2 DS).
    set (BDS := mk_BinDirectSumCone _ _ _ _ _ _ _ _ isBDS).
    (* First term of to_binop *)
    rewrite to_premor_linear'. rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn1 A DS). rewrite (to_Unel2 A DS).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_runax'.
    (* Second term of to_binop *)
    rewrite to_postmor_linear'. rewrite <- assoc. rewrite <- assoc.
    rewrite (to_Unel1 A DS). rewrite (to_IdIn2 A DS).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_lunax'.
    apply idpath.
  Qed.

  (** F commutes with addition of morphisms *)
  Local Lemma isAdditiveCriteria_BinOp {A B : Additive} (F : functor A B)
        (H : PreservesBinDirectSums F) {a1 a2 : A} (f g : A⟦a1, a2⟧) :
    # F (to_binop a1 a2 f g) = to_binop (F a1) (F a2) (# F f) (# F g).
  Proof.
    set (DS := to_BinDirectSums A a2 a2).
    set (isBDS := H a2 a2 DS).
    set (BDS := mk_BinDirectSumCone _ _ _ _ _ _ _ _ isBDS).
    rewrite (isAdditiveCriteria_BinOp_eq F H f g). rewrite functor_comp.
    rewrite (@isAdditiveCriteria_isBinopFun_Pr A B F H a2 DS).
    rewrite to_premor_linear'.
    (* First term of the first to_binop *)
    rewrite <- functor_comp. rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc.
    fold DS. rewrite (to_IdIn1 A DS). rewrite (to_Unel2 A DS).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_runax'.
    (* Second term of the first to_binop *)
    rewrite <- functor_comp. rewrite to_postmor_linear'.
    rewrite <- assoc. rewrite <- assoc.
    rewrite (to_IdIn2 A DS). rewrite (to_Unel1 A DS).
    rewrite id_right. rewrite to_premor_unel'. rewrite to_lunax'.
    apply idpath.
  Qed.

  Lemma isAdditiveCriteria {A B : Additive} (F : functor A B) (H : PreservesBinDirectSums F) :
    isAdditiveFunctor F.
  Proof.
    use mk_isAdditiveFunctor.
    intros a1 a2.
    split.
    - intros f g. cbn.
      apply (isAdditiveCriteria_BinOp F H f g).
    - set (tmp := isAdditiveCriteria_preservesUnel F H a1 a2). unfold to_unel in tmp.
      apply tmp.
  Qed.

  Definition AdditiveFunctorCriteria {A B : Additive} (F : functor A B)
             (H : PreservesBinDirectSums F) : AdditiveFunctor A B.
  Proof.
    use mk_AdditiveFunctor.
    - exact F.
    - exact (isAdditiveCriteria F H).
  Defined.

End additivefunctor_criteria.


(** * The functor [QuotPrecategoryFunctor] is additive *)
Section def_additive_quot_functor.

  Variable A : Additive.
  Variable PAS : PreAdditiveSubabgrs A.
  Variable PAC : PreAdditiveComps A PAS.

  Local Lemma QuotPrecategoryAdditiveFunctor_isAdditiveFunctor :
    @isAdditiveFunctor A (QuotPrecategory_Additive A PAS PAC)
                       (QuotPrecategoryFunctor (Additive_PreAdditive A) PAS PAC).
  Proof.
    use mk_isAdditiveFunctor.
    intros X Y.
    split.
    - intros f g. apply idpath.
    - apply idpath.
  Qed.

  Set Printing All.
  Definition QuotPrecategoryAdditiveFunctor :
    AdditiveFunctor A (QuotPrecategory_Additive A PAS PAC).
  Proof.
    use mk_AdditiveFunctor.
    - exact (QuotPrecategoryFunctor A PAS PAC).
    - exact QuotPrecategoryAdditiveFunctor_isAdditiveFunctor.
  Defined.

End def_additive_quot_functor.
