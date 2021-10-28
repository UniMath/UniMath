(** * Pushout of a Monic is Monic, Pullback of an Epi is Epi *)
(** Contents
- Pushout of a Monic is Monic
- Pushout of a Monic is Pullback
- Pullback of an Epi is Epi
- Pullback of an Epi is Pushout
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.Opp.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.Morphisms.
Require Import UniMath.CategoryTheory.CategoriesWithBinOps.
Require Import UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Import UniMath.CategoryTheory.PreAdditive.
Require Import UniMath.CategoryTheory.Additive.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.AbelianToAdditive.

Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.BinDirectSums.


(** ** Introduction
We show that in abelian categories pushout of a Monic is a Monic and pullback of an Epi is an Epi.
Also, in this case the pushout diagram (resp. pullback diagram) is a pullback diagram (resp. pushout
diagram).

More precisely, let f : x --> y and g : x --> z be morphisms in an abelian category. Consider the
following pushout diagram
                            x ----g----> z
                          f |        in2 |
                            y ---in1---> w
If f is a Monic, then in2 is a Monic, [AbelianPushoutMonic2]. If g is a Monic, then in1 is a Monic,
[AbelianPushoutMonic1]. In both of the cases the above diagram is a pullback diagram,
[AbelianPushoutMonicisPullback1], [AbelianPushoutMonicisPullback2].

Let f : x --> z and g : y --> z be morphisms in an abelian category. Consider the following pullback
diagram
                            w ---pr1---> x
                       pr2  |          f |
                            y ----g----> z
If f is an Epi, then pr2 is an Epi, [AbelianPushoutEpi2], and if g is an Epi, then pr1 is an Epi,
[AbelianPushoutEpi1]. In both of the cases the above diagram is a pushout diagram,
[AbelianPullbackEpiisPushout1], [AbelianPullbackEpiisPushout2].

 *)
Section pushout_monic_pullback_epi.

  Context {A : AbelianPreCat}.
  Let hs : has_homsets A := homset_property A.

  Local Opaque Abelian.Equalizer.
  Local Opaque Abelian.Coequalizer.
  Local Opaque to_BinDirectSums.
  Local Opaque to_binop to_inv.


  (** ** Pushout of a Monic is Monic *)

  Lemma AbelianPushoutMonic2 {x y z : A} (f : Monic A x y) (g : x --> z) (Po : Pushout f g) :
    Monics.isMonic (PushoutIn2 Po).
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A) y z).
    set (Po' := Pushout_from_Coequalizer_BinCoproduct
                  A hs _ _ _ f g (BinDirectSum_BinCoproduct _ DS)
                  (Abelian.Coequalizer
                     A
                     (f · (to_In1 DS))
                     (g · (to_In2 DS)))).
    (* Transform the statement to a statement about other pushout *)
    set (iso := iso_from_Pushout_to_Pushout Po Po').
    apply (isMonic_postcomp
             A _ (PushoutArrow Po Po' (PushoutIn1 Po') (PushoutIn2 Po')
                               (PushoutSqrCommutes Po'))).
    rewrite (PushoutArrow_PushoutIn2
               Po _ (PushoutIn1 Po') (PushoutIn2 Po')
               (PushoutSqrCommutes Po')).
    (* Prove that the arrow isMonic *)
    set (CE := Coequalizer A (f · to_In1 (A:=AbelianToPreAdditive A) DS)
                           (g · to_In2 (A:=AbelianToPreAdditive A) DS)).
    set (CK := AdditiveCoequalizerToCokernel (AbelianToAdditive A) _ _ CE).
    set (M1 := @isMonic_to_binop_BinDirectSum1' (AbelianToAdditive A) x y z f g DS).
    set (K := MonicToKernel' A (make_Monic _ _ M1) CK).
    use (@to_isMonic (AbelianToAdditive A)).
    intros z0 g0 H. cbn in H. rewrite assoc in H.
    set (φ := KernelIn _ K z0 (g0 · to_In2 (A:=AbelianToPreAdditive A) DS) H).
    set (KComm := KernelCommutes (to_Zero A) K z0 (g0 · to_In2 (A:=AbelianToPreAdditive A) DS) H).
    fold φ in KComm.
    (* The result follows from KComm and the fact that φ = ZeroArrow *)
    assert (e1 : φ = ZeroArrow (to_Zero A) _ _).
    {
      use (MonicisMonic _ f).
      rewrite ZeroArrow_comp_left. cbn in KComm.
      assert (e2 : (MonicArrow _ f) =
                   (@to_binop (AbelianToAdditive A) _ _
                              (f · to_In1 (A:=AbelianToPreAdditive A) DS)
                              (@to_inv (AbelianToAdditive A) _ _
                                       (g · to_In2 (A:=AbelianToPreAdditive A) DS)))
                     · to_Pr1 DS).
      {
        rewrite to_postmor_linear'. rewrite <- assoc.
        rewrite PreAdditive_invlcomp. rewrite <- assoc.
        set (tmp := to_IdIn1 DS). cbn in tmp. cbn. rewrite tmp. clear tmp.
        set (tmp := to_Unel2' DS). cbn in tmp. rewrite tmp. clear tmp.
        rewrite ZeroArrow_comp_right. rewrite id_right. apply pathsinv0.
        set (tmp := @to_runax'' (AbelianToAdditive A) (to_Zero A) _ _ f). exact tmp.
      }
      rewrite e2. clear e2. rewrite assoc. cbn in KComm. cbn. rewrite KComm.
      rewrite <- assoc. set (tmp := to_Unel2' DS). cbn in tmp. rewrite tmp. clear tmp.
      apply ZeroArrow_comp_right.
    }
    use (to_In2_isMonic _ DS). cbn in KComm. use (pathscomp0 (! KComm)).
    rewrite e1. rewrite ZeroArrow_comp_left. rewrite ZeroArrow_comp_left. apply idpath.
  Qed.

  Lemma AbelianPushoutMonic1 {x y z : A} (f : x --> y) (g : Monic A x z) (Po : Pushout f g) :
    Monics.isMonic (PushoutIn1 Po).
  Proof.
    set (Po' := make_Pushout _ _ _ _ _ _ (is_symmetric_isPushout hs _ (isPushout_Pushout Po))).
    use (AbelianPushoutMonic2 g f Po').
  Qed.

  (** ** Pushout of Monic is Pullback *)

  Local Lemma AbelianPushoutMonicisPullback_eq {x y z : A} (f : Monic A x y) (g : x --> z)
        {e : A} {h : A ⟦ e, y ⟧} {k : A ⟦ e, z ⟧}
        (Hk : let DS := to_BinDirectSums (AbelianToAdditive A) y z in
              let Po' := Pushout_from_Coequalizer_BinCoproduct
                           A hs _ _ _ f g (BinDirectSum_BinCoproduct _ DS)
                           (Abelian.Coequalizer A (f · (to_In1 DS)) (g · (to_In2 DS))) in
              h · PushoutIn1 Po' = k · PushoutIn2 Po') :
    let DS := to_BinDirectSums (AbelianToAdditive A) y z in
    let Po' := Pushout_from_Coequalizer_BinCoproduct
                 A hs _ _ _ f g (BinDirectSum_BinCoproduct _ DS)
                 (Abelian.Coequalizer A (f · (to_In1 DS)) (g · (to_In2 DS))) in
    h · CokernelArrow (Abelian.Cokernel f) = ZeroArrow (to_Zero A) e (Abelian.Cokernel f).
  Proof.
    intros DS Po'. cbn zeta in Hk. fold DS in Hk. fold Po' in Hk.
    set (CK := Abelian.Cokernel f).
    assert (e1 : f · CokernelArrow CK = g · ZeroArrow (to_Zero A) z CK).
    {
      rewrite CokernelCompZero. rewrite ZeroArrow_comp_right. apply idpath.
    }
    rewrite <- (PushoutArrow_PushoutIn1 Po' CK (CokernelArrow CK) (ZeroArrow (to_Zero A) _ _) e1).
    rewrite assoc. rewrite Hk. clear Hk. rewrite <- assoc.
    rewrite (PushoutArrow_PushoutIn2 Po' CK (CokernelArrow CK) (ZeroArrow (to_Zero A) _ _) e1).
    apply ZeroArrow_comp_right.
  Qed.

  Lemma AbelianPushoutMonicisPullback1 {x y z : A} (f : Monic A x y) (g : x --> z)
        (Po : Pushout f g) : isPullback (*(PushoutIn1 Po) (PushoutIn2 Po) f g*) (PushoutSqrCommutes Po).
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A) y z).
    set (Po' := Pushout_from_Coequalizer_BinCoproduct
                  A hs _ _ _ f g (BinDirectSum_BinCoproduct _ DS)
                  (Abelian.Coequalizer
                     A
                     (f · (to_In1 DS))
                     (g · (to_In2 DS)))).
    set (i := iso_from_Pushout_to_Pushout Po Po').
    use isPullback_up_to_iso.
    - exact hs.
    - exact Po'.
    - exact i.
    - use isPullback_mor_paths.
      + exact hs.
      + exact (PushoutIn1 Po').
      + exact (PushoutIn2 Po').
      + exact f.
      + exact g.
      + apply pathsinv0.
        exact (PushoutArrow_PushoutIn1
                 Po Po' (PushoutIn1 Po') (PushoutIn2 Po') (PushoutSqrCommutes Po')).
      + apply pathsinv0.
        exact (PushoutArrow_PushoutIn2
                 Po Po' (PushoutIn1 Po') (PushoutIn2 Po') (PushoutSqrCommutes Po')).
      + apply idpath.
      + apply idpath.
      + exact (PushoutSqrCommutes _ ).
      + set (K := MonicToKernel f).
        set (CK := Abelian.Cokernel f). fold CK in K.
        use make_isPullback.
        intros e h k Hk.
        use unique_exists.
        * use (KernelIn (to_Zero A) K).
          -- exact h.
          -- exact (AbelianPushoutMonicisPullback_eq f g Hk).
        * cbn. split.
          -- use (KernelCommutes (to_Zero A) K).
          -- assert (Hk' : h · PushoutIn1 Po' = k · PushoutIn2 Po') by apply Hk.
             set (comm := KernelCommutes
                            (to_Zero A) K _ h (AbelianPushoutMonicisPullback_eq f g Hk)).
             cbn in comm. rewrite <- comm in Hk'. clear comm.
             apply (AbelianPushoutMonic2 f g Po'). rewrite <- Hk'.
             cbn. rewrite <- assoc. rewrite <- assoc. apply cancel_precomposition.
             rewrite assoc. rewrite assoc. apply pathsinv0.
             use CoequalizerEqAr.
        * intros y0. apply isapropdirprod.
          -- apply hs.
          -- apply hs.
        * intros y0 X. cbn in X.
          use (KernelArrowisMonic (to_Zero A) K). rewrite KernelCommutes. exact (dirprod_pr1 X).
  Qed.

  Lemma AbelianPushoutMonicisPullback2 {x y z : A} (f : x --> y) (g : Monic A x z)
        (Po : Pushout f g) : isPullback (*(PushoutIn1 Po) (PushoutIn2 Po) f g*) (PushoutSqrCommutes Po).
  Proof.
    set (Po' := make_Pushout _ _ _ _ _ _ (is_symmetric_isPushout hs _ (isPushout_Pushout Po))).
    use is_symmetric_isPullback.
    - exact hs.
    - exact (! (PushoutSqrCommutes _ )).
    - exact (AbelianPushoutMonicisPullback1 g f Po').
  Qed.

  (** ** Pullback of an Epi is Epi *)

  Lemma AbelianPullbackEpi2 {x y z : A} (f : Epi A x z) (g : y --> z) (Pb : Pullback f g) :
    Epis.isEpi (PullbackPr2 Pb).
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A) x y).
    set (Pb' := Pullback_from_Equalizer_BinProduct
                  A  _ _ _ f g (BinDirectSum_BinProduct _ DS)
                  (Abelian.Equalizer
                     A
                     ((to_Pr1 DS) · f)
                     ((to_Pr2 DS) · g))).
    (* Transform the statement to a statement about other pullback *)
    set (iso := iso_from_Pullback_to_Pullback Pb Pb').
    apply (isEpi_precomp
             A (PullbackArrow Pb Pb' (PullbackPr1 Pb') (PullbackPr2 Pb')
                              (PullbackSqrCommutes Pb'))).
    rewrite (PullbackArrow_PullbackPr2
               Pb _ (PullbackPr1 Pb') (PullbackPr2 Pb')
               (PullbackSqrCommutes Pb')).
    (* Prove that the arrow isEpi *)
    set (E := Equalizer A ((to_Pr1 DS) · f) ((to_Pr2 DS) · g)).
    set (K := AdditiveEqualizerToKernel (AbelianToAdditive A) _ _ E).
    set (E1 := @isEpi_to_binop_BinDirectSum1' (AbelianToAdditive A) x y z f g DS).
    set (CK := EpiToCokernel' A hs (make_Epi _ _ E1) K).
    use (@to_isEpi (AbelianToAdditive A)).
    intros z0 g0 H. cbn in H. cbn. rewrite <- assoc in H.
    set (φ := CokernelOut _ CK z0 (to_Pr2 DS · g0) H).
    set (CKComm := CokernelCommutes (to_Zero A) CK z0 (to_Pr2 DS · g0) H).
    fold φ in CKComm.
    (* The result follows from CKComm and the fact that φ = ZeroArrow *)
    assert (e1 : φ = ZeroArrow (to_Zero A) _ _).
    {
      use (EpiisEpi _ f).
      rewrite ZeroArrow_comp_right. cbn in CKComm.
      assert (e2 : (EpiArrow _ f) =
                   (to_In1 DS)
                     · (@to_binop (AbelianToAdditive A) _ _
                                   (to_Pr1 DS · f)
                                   (@to_inv (AbelianToAdditive A) _ _ (to_Pr2 DS · g)))).
      {
        rewrite to_premor_linear'. rewrite assoc.
        rewrite PreAdditive_invrcomp. rewrite assoc.
        set (tmp := to_IdIn1 DS). cbn in tmp. cbn. rewrite tmp. clear tmp.
        set (tmp := to_Unel1' DS). cbn in tmp. rewrite tmp. clear tmp.
        rewrite ZeroArrow_comp_left. rewrite id_left. apply pathsinv0.
        set (tmp := @to_runax'' (AbelianToAdditive A) (to_Zero A) _ _ f). exact tmp.
      }
      rewrite e2. clear e2. rewrite <- assoc. cbn in CKComm. cbn. rewrite CKComm.
      rewrite assoc. set (tmp := to_Unel1' DS). cbn in tmp. rewrite tmp. clear tmp.
      apply ZeroArrow_comp_left.
    }
    use (to_Pr2_isEpi _ DS). cbn in CKComm. use (pathscomp0 (! CKComm)).
    rewrite e1. rewrite ZeroArrow_comp_right. rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Lemma AbelianPullbackEpi1 {x y z : A} (f : x --> z) (g : Epi A y z) (Pb : Pullback f g) :
    Epis.isEpi (PullbackPr1 Pb).
  Proof.
    set (Pb' := make_Pullback _ (is_symmetric_isPullback hs _ (isPullback_Pullback Pb))).
    use (AbelianPullbackEpi2 g f Pb').
  Qed.


  (** ** Pullback of Epi is Pushout *)

  Local Lemma AbelianPullbackEpiisPushout1_eq {x y z : A} (f : Epi A x z) (g : y --> z)
        {e : A} {h : A ⟦ x, e ⟧} {k : A ⟦ y, e ⟧}
        (Hk : let DS := to_BinDirectSums (AbelianToAdditive A) x y in
              let Pb' := Pullback_from_Equalizer_BinProduct
                           A _ _ _ f g (BinDirectSum_BinProduct _ DS)
                           (Abelian.Equalizer A ((to_Pr1 DS) · f) ((to_Pr2 DS) · g)) in
              PullbackPr1 Pb' · h = PullbackPr2 Pb' · k) :
    let DS := to_BinDirectSums (AbelianToAdditive A) x y in
    let Pb' := Pullback_from_Equalizer_BinProduct
                           A _ _ _ f g (BinDirectSum_BinProduct _ DS)
                           (Abelian.Equalizer A ((to_Pr1 DS) · f) ((to_Pr2 DS) · g)) in
    let K := Abelian.Kernel f in
    KernelArrow K · h = ZeroArrow (to_Zero A) K e.
  Proof.
    intros DS Pb' K. cbn zeta in Hk. fold DS in Hk. fold Pb' in Hk.
    assert (e1 : KernelArrow K · f = ZeroArrow (to_Zero A) _ _ · g).
    {
      rewrite KernelCompZero. rewrite ZeroArrow_comp_left. apply idpath.
    }
    rewrite <- (PullbackArrow_PullbackPr1 Pb' K (KernelArrow K) (ZeroArrow (to_Zero A) _ _) e1).
    rewrite <- assoc. rewrite Hk. clear Hk. rewrite assoc.
    rewrite (PullbackArrow_PullbackPr2 Pb' K (KernelArrow K) (ZeroArrow (to_Zero A) _ _) e1).
    apply ZeroArrow_comp_left.
  Qed.

  Lemma AbelianPullbackEpiisPushout1 {x y z : A} (f : Epi A x z) (g : y --> z) (Pb : Pullback f g) :
    isPushout (PullbackPr1 Pb) (PullbackPr2 Pb) f g (PullbackSqrCommutes Pb).
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A) x y).
    set (Pb' := Pullback_from_Equalizer_BinProduct
                  A _ _ _ f g (BinDirectSum_BinProduct _ DS)
                  (Abelian.Equalizer A ((to_Pr1 DS) · f) ((to_Pr2 DS) · g))).
    set (i := iso_from_Pullback_to_Pullback Pb' Pb).
    use isPushout_up_to_iso.
    - exact hs.
    - exact Pb'.
    - exact i.
    - use isPushout_mor_paths.
      + exact hs.
      + exact (PullbackPr1 Pb').
      + exact (PullbackPr2 Pb').
      + exact f.
      + exact g.
      + apply pathsinv0.
        exact (PullbackArrow_PullbackPr1
                 Pb Pb' (PullbackPr1 Pb') (PullbackPr2 Pb') (PullbackSqrCommutes Pb')).
      + apply pathsinv0.
        exact (PullbackArrow_PullbackPr2
                 Pb Pb' (PullbackPr1 Pb') (PullbackPr2 Pb') (PullbackSqrCommutes Pb')).
      + apply idpath.
      + apply idpath.
      + exact (PullbackSqrCommutes _ ).
      + set (CK := EpiToCokernel f).
        set (K := Abelian.Kernel f). fold K in CK.
        use make_isPushout.
        intros e h k Hk.
        use unique_exists.
        * use (CokernelOut (to_Zero A) CK).
          -- exact h.
          -- exact (AbelianPullbackEpiisPushout1_eq f g Hk).
        * cbn. split.
          -- use (CokernelCommutes (to_Zero A) CK).
          -- assert (Hk' : PullbackPr1 Pb' · h = PullbackPr2 Pb' · k) by apply Hk.
             set (comm := CokernelCommutes
                            (to_Zero A) CK _ h (AbelianPullbackEpiisPushout1_eq f g Hk)).
             cbn in comm. rewrite <- comm in Hk'. clear comm.
             apply (AbelianPullbackEpi2 f g Pb'). rewrite <- Hk'.
             cbn. rewrite assoc. rewrite assoc. apply cancel_postcomposition.
             rewrite <- assoc. rewrite <- assoc. apply pathsinv0.
             use EqualizerEqAr.
        * intros y0. apply isapropdirprod.
          -- apply hs.
          -- apply hs.
        * intros y0 X. cbn in X.
          use (CokernelArrowisEpi (to_Zero A) CK). rewrite CokernelCommutes. exact (dirprod_pr1 X).
  Qed.

  Lemma AbelianPullbackEpiisPushout2 {x y z : A} (f : x --> z) (g : Epi A y z) (Pb : Pullback f g) :
    isPushout (PullbackPr1 Pb) (PullbackPr2 Pb) f g (PullbackSqrCommutes Pb).
  Proof.
    set (Pb' := make_Pullback  _ (is_symmetric_isPullback hs _ (isPullback_Pullback Pb))).
    use is_symmetric_isPushout.
    - exact hs.
    - exact (! (PullbackSqrCommutes _ )).
    - exact (AbelianPullbackEpiisPushout1 g f Pb').
  Qed.

End pushout_monic_pullback_epi.
