(** * Short exact sequences *)
(** ** Contents
- ShortShortExact sequences
- Remark on monics, epis, kernels, and cokernels
- LeftShortExact sequences
- RightShortExact sequences
- ShortExact sequences
- A criteria for ShortShortExact
 - Cokernel from ShortShortExact
 - isCoequalizer to ShortShortExact
- Correspondence between ShortExact and ShortShortExact
 - ShortExact from ShortShortExact
 - ShortShortExact criteria
*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.Abelian.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.Morphisms.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.


(** * Introduction
  Short exact sequences consist of three objects and two morphisms such that the first morphism is a
  monic, the second morphism is an epi, and an image of the first morphism gives a kernel of the
  second morphism. These sequences are classically denoted by a diagram
                           0 -> A -> B -> C -> 0
  We call such diagrams [ShortExact].

  To define short exact sequences we first define short short exact sequences, [ShortShortExact],
  left short exact sequences, [LeftShortExact], and right short exact sequences, [RightShortExact].
  These correspond to the diagrams
          A -> B -> C,  0 -> A -> B -> C,  and,  A -> B -> C -> 0,
  respectively.

  The definition of [ShortShortExact] says that the image of A -> B is the kernel of B -> C. This is
  equivalent to saying that the coimage of B -> C is the cokernel of A -> B. We prove this
  correspondence in the Section [shortshortexact_coequalizer].

    Next, in the section [shortexact_correspondence] we prove a correspondence between
  [ShortShortExact] and [ShortExact] by using the factorization formula for morphisms in abelian
  precategories. We construct [ShortExact] from [ShortShortExact] and we give a criteria to
  construct [ShortShortExact] from properties similar to [ShortExact]. *)

(** * Definition of short exact sequences *)
Section def_shortexactseqs.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.

  (** Image of the first morphism and equality of morphisms associated to it. *)
  Definition Image (SSED : ShortShortExactData A Abelian.Zero) :
    Kernel Abelian.Zero (CokernelArrow (Abelian.Cokernel (Mor1 SSED))) := Image (Mor1 SSED).

  Lemma Image_Eq (SSED : ShortShortExactData A Abelian.Zero) :
    (KernelArrow (Image SSED)) ;; (Mor2 SSED) = ZeroArrow Abelian.Zero _ _.
  Proof.
    unfold Image.
    set (fact := factorization1 hs (Mor1 SSED)).
    unfold factorization1_monic in fact. cbn in fact.
    apply (factorization1_is_epi hs (Mor1 SSED)).
    rewrite ZeroArrow_comp_right.
    rewrite assoc. rewrite <- fact.
    apply (ShortShortExactData_Eq Abelian.Zero SSED).
  Qed.

  (** Coimage of the second morphism and equality of morphisms associated to it. *)
  Definition CoImage (SSED : ShortShortExactData A Abelian.Zero) :
    Cokernel Abelian.Zero (KernelArrow (Abelian.Kernel (Mor2 SSED))) := CoImage (Mor2 SSED).

  Lemma CoImage_Eq (SSED : ShortShortExactData A Abelian.Zero) :
    (Mor1 SSED) ;; (CokernelArrow (CoImage SSED)) = ZeroArrow Abelian.Zero _ _.
  Proof.
    unfold CoImage.
    set (fact := factorization2 hs (Mor2 SSED)).
    unfold factorization2_epi in fact. cbn in fact.
    apply (factorization2_is_monic hs (Mor2 SSED)).
    rewrite ZeroArrow_comp_left.
    rewrite <- assoc. rewrite <- fact.
    apply (ShortShortExactData_Eq Abelian.Zero SSED).
  Qed.


  (** ** [Short Short Exact]
    [ShortShortData] such that the image of the first morphism is the kernel of the second morphism.
    Informally, an exact sequence
                               A -> B -> C
  *)

  Definition ShortShortExact : UU :=
    Σ SSED : ShortShortExactData A Abelian.Zero,
             isEqualizer (Mor2 SSED) (ZeroArrow Abelian.Zero _ _)
                         (KernelArrow (Image SSED)) (KernelEqRw Abelian.Zero (Image_Eq SSED)).

  Definition mk_ShortShortExact (SSED : ShortShortExactData A Abelian.Zero)
             (H : isEqualizer (Mor2 SSED) (ZeroArrow Abelian.Zero _ _)
                              (KernelArrow (Image SSED))
                              (KernelEqRw Abelian.Zero (Image_Eq SSED))) :
    ShortShortExact.
  Proof.
    use tpair.
    - exact SSED.
    - exact H.
  Defined.

  (** Accessor functions *)
  Definition ShortShortExact_ShortShortExactData (SSE : ShortShortExact) :
    ShortShortExactData A Abelian.Zero := pr1 SSE.
  Coercion ShortShortExact_ShortShortExactData : ShortShortExact >-> ShortShortExactData.

  Definition ShortShortExact_isEqualizer (SSE : ShortShortExact) :
    isEqualizer (Mor2 SSE) (ZeroArrow Abelian.Zero _ _) (KernelArrow (Image SSE))
                (KernelEqRw Abelian.Zero (Image_Eq SSE)) := pr2 SSE.

  Definition ShortShortExact_Kernel (SSE : ShortShortExact) : Kernel Abelian.Zero (Mor2 SSE) :=
    mk_Kernel Abelian.Zero (KernelArrow (Image SSE)) (Mor2 SSE) (Image_Eq SSE)
              (ShortShortExact_isEqualizer SSE).


  (** ** Remark
    In Abelian.v we have already shown that a morphism is a monic if and only if its kernel is
    zero, and dually is an epi if and only if its cokernel is zero. See the results
    - Abelian_MonicKernelZero_isEqualizer, Abelian_MonicKernelZero
    - Abelian_EpiCokernelZero_isCoequalizer, Abelian_EpiCokernelZero
    - Abelian_KernelZeroisMonic, Abelian_KernelZeroMonic
    - Abelian_CokernelZeroisEpi, Abelian_CokernelZeroEpi
   in CategoryTheory/Abelian.v. Thus, to define short exact sequeces, it suffices to assume that
   the first morphism is a monic and the second morphism is an epi. Similarly for left short exact
   and right short exact.
   *)


  (** ** [LeftShortExact]
    [ShortShortExact] such that the first morphism is a monic. Informally, an exact sequence
                            0 -> A -> B -> C
  *)

  Definition LeftShortExact : UU := Σ SSE : ShortShortExact, isMonic (Mor1 SSE).

  Definition mk_LeftShortExact (SSE : ShortShortExact) (isM : isMonic (Mor1 SSE)) :
    LeftShortExact.
  Proof.
    use tpair.
    - exact SSE.
    - exact isM.
  Defined.

  (** Accessor functions *)
  Definition LeftShortExact_ShortShortExact (LSE : LeftShortExact) : ShortShortExact := pr1 LSE.
  Coercion LeftShortExact_ShortShortExact : LeftShortExact >-> ShortShortExact.

  Definition isMonic (LSE : LeftShortExact) : isMonic (Mor1 LSE) := pr2 LSE.


  (** ** [RightShortExact]
    [ShortShortExact] such that the second morphism is an epi. Informally, an exact sequece
                               A -> B -> C -> 0
   *)

  Definition RightShortExact : UU := Σ SSE : ShortShortExact, isEpi (Mor2 SSE).

  Definition mk_RightShortExact (SSE : ShortShortExact) (isE : isEpi (Mor2 SSE)) :
    RightShortExact.
  Proof.
    use tpair.
    - exact SSE.
    - exact isE.
  Defined.

  (** Accessor functions *)
  Definition RightShortExact_ShortShortExact (RSE : RightShortExact) : ShortShortExact := pr1 RSE.
  Coercion RightShortExact_ShortShortExact : RightShortExact >-> ShortShortExact.

  Definition isEpi (RSE : RightShortExact) : isEpi (Mor2 RSE) := pr2 RSE.


  (** ** [ShortExact]
    [ShortShortExact] such that the first morphism is monic and the second morphism is an epi.
    Informally, an exact sequece
                            0 -> A -> B -> C -> 0
  *)

  Definition ShortExact : UU :=
    Σ SSE : ShortShortExact, Monics.isMonic (Mor1 SSE) × Epis.isEpi (Mor2 SSE).

  Definition mk_ShortExact (SSE : ShortShortExact) (isM : Monics.isMonic (Mor1 SSE))
             (isE : Epis.isEpi (Mor2 SSE)) : ShortExact.
  Proof.
    use tpair.
    - exact SSE.
    - use dirprodpair.
      + exact isM.
      + exact isE.
  Defined.

  (** [LeftShortExact] and [RightShortExact] from [ShortExact] *)
  Definition ShortExact_LeftShortExact (SE : ShortExact) : LeftShortExact.
  Proof.
    use mk_LeftShortExact.
    - exact (pr1 SE).
    - exact (dirprod_pr1 (pr2 SE)).
  Defined.
  Coercion ShortExact_LeftShortExact : ShortExact >-> LeftShortExact.

  Definition ShortExact_RightShortExact (SE : ShortExact) : RightShortExact.
  Proof.
    use mk_RightShortExact.
    - exact (pr1 SE).
    - exact (dirprod_pr2 (pr2 SE)).
  Defined.
  Coercion ShortExact_RightShortExact : ShortExact >-> RightShortExact.

End def_shortexactseqs.
Arguments Image [A] _.
Arguments Image_Eq [A] _ _.
Arguments CoImage [A] _.
Arguments CoImage_Eq [A] _ _.
Arguments mk_ShortShortExact [A] _ _ _.
Arguments ShortShortExact_isEqualizer [A] _ _ _ _ _.
Arguments ShortShortExact_Kernel [A] _ _.
Arguments LeftShortExact [A] _.
Arguments mk_LeftShortExact [A] _ _ _.
Arguments isMonic [A] _ _ _ _ _ _.
Arguments RightShortExact [A] _.
Arguments mk_RightShortExact [A] _ _ _.
Arguments isEpi [A] _ _ _ _ _ _.
Arguments ShortShortExact [A] _.
Arguments mk_ShortShortExact [A] _ _ _.


(** * [ShortShortExact] criteria
  In this section we show that for [ShortShortExact] a coimage of the second morphism is a cokernel
  of the first morphism and give a way to construct [ShortShortExact] from certain isCoequalizer. *)
Section shortshortexact_coequalizer.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.


  (** ** [ShortShortExact] implies isCoequalizer.
    Note that in the definition of [ShortShortExact] we use isEqualizer to say that an image of the
    first morphism is a kernel of the second morphism. We show that also the coimage of the second
    morphism is a cokernel of the first morphism. Informally, this follows directly from the fact
    that the opposite category of an abelian category is an abelian category and that taking the
    opposite category twice, we get the same category. *)

  Local Lemma ShortShortExact_isCoequalizer_eq1 (SSE : ShortShortExact hs) (w0 : A)
        (h : A ⟦Ob2 SSE, w0⟧) (H : Mor1 SSE ;; h = (ZeroArrow Abelian.Zero _ _) ;; h) :
    (KernelArrow (ShortShortExact_Kernel hs SSE)) ;; h = ZeroArrow Abelian.Zero _ _.
  Proof.
    apply (factorization1_is_epi hs (Mor1 SSE)).
    set (tmp := factorization1 hs (Mor1 SSE)).
    unfold factorization1_epi in tmp.
    unfold factorization1_monic in tmp.
    cbn in tmp. rewrite assoc. unfold ShortShortExact_Kernel.
    cbn. unfold Image. rewrite <- tmp. clear tmp.
    rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left in H.
    exact H.
  Qed.

  Local Lemma ShortShortExact_isCoequalizer_eq2 (SSE : ShortShortExact hs) (w0 : A)
        (h : A ⟦Ob2 SSE, w0⟧) (H : Mor1 SSE ;; h = (ZeroArrow Abelian.Zero _ _) ;; h) :
    KernelArrow (Abelian.Kernel (Mor2 SSE)) ;; h = ZeroArrow Abelian.Zero _ _.
  Proof.
    set (i := iso_from_Kernel_to_Kernel Abelian.Zero (ShortShortExact_Kernel hs SSE)
                                        (Abelian.Kernel (Mor2 SSE))).
    set (epi := iso_Epi A i (pr2 i)).
    apply (pr2 epi). cbn. rewrite ZeroArrow_comp_right.
    rewrite assoc. unfold from_Kernel_to_Kernel.
    rewrite KernelCommutes.
    apply (ShortShortExact_isCoequalizer_eq1 SSE w0 h H).
  Qed.

  Local Lemma  ShortShortExact_isCoequalizer (SSE : ShortShortExact hs) :
    isCoequalizer (Mor1 SSE) (ZeroArrow Abelian.Zero _ _) (CokernelArrow (CoImage SSE))
                  (CokernelEqRw Abelian.Zero (CoImage_Eq hs SSE)).
  Proof.
    use mk_isCoequalizer.
    intros w0 h H'.
    use unique_exists.

    (* Construction of the morphism *)
    - apply (CokernelOut Abelian.Zero (CoImage SSE) w0 h
                         (ShortShortExact_isCoequalizer_eq2 SSE w0 h H')).

    (* Commutativity *)
    - apply CokernelCommutes.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. cbn in T.
      apply CokernelOutsEq.
      rewrite T. apply pathsinv0.
      apply CokernelCommutes.
  Qed.

  Definition ShortShortExact_Coequalizer (SSE : ShortShortExact hs) :
    Cokernel Abelian.Zero (Mor1 SSE) := mk_Cokernel Abelian.Zero (CokernelArrow (CoImage SSE))
                                                    (Mor1 SSE) (CoImage_Eq hs SSE)
                                                    (ShortShortExact_isCoequalizer SSE).


  (** ** From isCoequalizer to [ShortShortExact]
    We show that we can construct [ShortShortExact] from the isCoequalizer property proved above. *)

  Local Lemma ShortShortExact_from_isCoequalizer_eq1 (SSED : ShortShortExactData A Abelian.Zero)
        (w : A) (h : A ⟦w, Ob2 SSED⟧)
        (H : (h ;; (CokernelArrow (Abelian.CoImage (Mor2 SSED)))) = ZeroArrow Abelian.Zero _ _)
        (H' : isCoequalizer (Mor1 SSED) (ZeroArrow Abelian.Zero _ _) (CokernelArrow (CoImage SSED))
                            (CokernelEqRw Abelian.Zero (CoImage_Eq hs SSED))):
    h ;; CokernelArrow (Abelian.Cokernel (Mor1 SSED)) = ZeroArrow Abelian.Zero _ _.
  Proof.
    set (coker := mk_Cokernel Abelian.Zero (CokernelArrow (CoImage SSED)) (Mor1 SSED)
                              (CoImage_Eq hs SSED) H').
    set (i := iso_from_Cokernel_to_Cokernel Abelian.Zero (Abelian.Cokernel (Mor1 SSED)) coker).
    set (isM := iso_Monic A i (pr2 i)). apply (pr2 isM). cbn.
    rewrite ZeroArrow_comp_left. rewrite <- assoc.
    unfold from_Cokernel_to_Cokernel.
    rewrite CokernelCommutes.
    unfold coker. cbn. unfold CoImage.
    exact H.
  Qed.

  Local Lemma ShortShortExact_from_isCoequalizer_eq2 (SSED : ShortShortExactData A Abelian.Zero)
        (w : A) (h : A ⟦w, Ob2 SSED⟧)
        (H : h ;; Mor2 SSED = h ;; (ZeroArrow Abelian.Zero _ _))
        (H' : isCoequalizer (Mor1 SSED) (ZeroArrow Abelian.Zero _ _) (CokernelArrow (CoImage SSED))
                            (CokernelEqRw Abelian.Zero (CoImage_Eq hs SSED))) :
    h ;; CokernelArrow (Abelian.CoImage (Mor2 SSED)) = ZeroArrow Abelian.Zero _ _.
  Proof.
    apply (factorization2_is_monic hs (Mor2 SSED)).
    set (tmp := factorization2 hs (Mor2 SSED)).
    unfold factorization2_epi in tmp.
    unfold factorization2_monic in tmp.
    cbn in tmp. rewrite <- assoc. rewrite <- tmp.
    clear tmp.
    rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_right in H.
    exact H.
  Qed.

  Local Lemma ShortShortExact_from_isCoequalizer_isEqualizer
        (SSED : ShortShortExactData A Abelian.Zero)
        (H : isCoequalizer (Mor1 SSED) (ZeroArrow Abelian.Zero _ _) (CokernelArrow (CoImage SSED))
                           (CokernelEqRw Abelian.Zero (CoImage_Eq hs SSED))) :
    isEqualizer (Mor2 SSED) (ZeroArrow Abelian.Zero _ _) (KernelArrow (Image SSED))
                (KernelEqRw Abelian.Zero (Image_Eq hs SSED)).
  Proof.
    use mk_isEqualizer.
    intros w h H'.
    use unique_exists.

    (* Construction of the morphism *)
    - apply (KernelIn Abelian.Zero (Image SSED) w h
                      (ShortShortExact_from_isCoequalizer_eq1
                         SSED w h (ShortShortExact_from_isCoequalizer_eq2 SSED w h H' H) H)).

    (* Commutativity *)
    - apply KernelCommutes.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. cbn in T.
      apply KernelInsEq.
      rewrite T. apply pathsinv0.
      apply KernelCommutes.
  Qed.

  Definition ShortShortExact_from_isCoequalizer (SSED : ShortShortExactData A Abelian.Zero)
             (H : isCoequalizer (Mor1 SSED) (ZeroArrow Abelian.Zero _ _)
                                (CokernelArrow (CoImage SSED))
                                (CokernelEqRw Abelian.Zero (CoImage_Eq hs SSED))) :
    ShortShortExact hs := mk_ShortShortExact
                            hs SSED (ShortShortExact_from_isCoequalizer_isEqualizer SSED H).

End shortshortexact_coequalizer.
Arguments ShortShortExact_Coequalizer [A] _ _.
Arguments ShortShortExact_from_isCoequalizer [A] _ _ _.


(** * Correspondence between [ShortShortExact] and [ShortExact]
  In this section we prove correspondence between [ShortShortExact] and
  [ShortExact]. *)
Section shortexact_correspondence.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.


  (** ** Construction of [ShortExact] from [ShortShortExact]
    By using the factorization property of morphisms in abelian categories, we show that we can
    construct a [ShortExact] from [ShortShortExact] in a canonical way. More precisely, such
    [ShortExact] is given by taking the first morphism to be the image of the first morphism of the
    [ShortShortExact] and the second morphism to be the coimage of the second morphism of the
    [ShortShortExact]. *)

  Local Lemma ShortExact_from_ShortShortExact_eq (SSE : ShortShortExact hs) :
    (KernelArrow (Abelian.Image (Mor1 SSE))) ;; (CokernelArrow (Abelian.CoImage (Mor2 SSE))) =
    ZeroArrow Abelian.Zero _ _.
  Proof.
    (* Work on mor1 using factorization *)
    apply (factorization1_is_epi hs (Mor1 SSE)).
    rewrite assoc.
    set (fact := factorization1 hs (Mor1 SSE)).
    rewrite ZeroArrow_comp_right.
    unfold factorization1_monic in fact. cbn in fact. rewrite <- fact. clear fact.

    (* Work on mor2 using factorization *)
    apply (factorization2_is_monic hs (Mor2 SSE)).
    rewrite <- assoc.
    set (fact := factorization2 hs (Mor2 SSE)).
    unfold factorization2_epi in fact. cbn in fact. rewrite <- fact. clear fact.
    rewrite ZeroArrow_comp_left.

    apply (ShortShortExactData_Eq Abelian.Zero SSE).
  Qed.

  Local Lemma ShortExact_ShortShortExact_isEqualizer_Eq (SSE : ShortShortExact hs) (w : A)
             (h : A ⟦w, Ob2 SSE⟧)
             (H' : h ;; CokernelArrow (Abelian.CoImage (Mor2 SSE)) = ZeroArrow Abelian.Zero _ _) :
    let Im := Abelian.Image (Mor1 SSE) in
    h ;; (CokernelArrow (Abelian.Cokernel (KernelArrow Im))) = ZeroArrow Abelian.Zero _ _.
  Proof.
    cbn zeta.

    assert (X : h ;; Mor2 SSE = ZeroArrow Abelian.Zero _ _).
    {
      rewrite (factorization2 hs (Mor2 SSE)).
      unfold factorization2_epi. cbn.
      set (tmp := factorization2_monic A hs (Mor2 SSE)).
      apply (maponpaths (fun h' : _ => h' ;; tmp)) in H'. unfold tmp in H'.
      clear tmp. rewrite ZeroArrow_comp_left in H'. rewrite <- assoc in H'.
      unfold factorization2_monic in H'. cbn in H'.
      exact H'.
    }

    set (comm1 := KernelCommutes Abelian.Zero (Abelian.Kernel (Mor2 SSE)) w h X).
    set (ker := ShortShortExact_Kernel hs SSE).
    set (tmp := Abelian.Kernel (Mor2 SSE)).
    set (tmp_eq := (KernelEqAr Abelian.Zero tmp)).
    rewrite ZeroArrow_comp_right in tmp_eq.
    set (comm2 := KernelCommutes Abelian.Zero ker tmp (KernelArrow tmp) tmp_eq).
    unfold tmp in comm2. rewrite <- comm2 in comm1. clear comm2.
    rewrite <- comm1. rewrite <- assoc. rewrite <- assoc.
    rewrite CokernelCompZero. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Local Lemma ShortExact_ShortShortExact_isEqualizer (SSE : ShortShortExact hs) :
    let Im := Abelian.Image (Mor1 SSE) in
    let CoIm := Abelian.CoImage (Mor2 SSE) in
    let MP := mk_MorphismPair (KernelArrow Im) (CokernelArrow CoIm) in
    let SSED := mk_ShortShortExactData Abelian.Zero MP (ShortExact_from_ShortShortExact_eq SSE) in
    isEqualizer (CokernelArrow CoIm) (ZeroArrow Abelian.Zero _ _)
                (KernelArrow (Image SSED)) (KernelEqRw Abelian.Zero (Image_Eq hs SSED)).
  Proof.
    cbn zeta.
    use mk_isEqualizer.
    intros w h H'.
    use unique_exists.

    (* Construction of the morphism *)
    - use KernelIn.
      + exact h.
      + rewrite ZeroArrow_comp_right in H'.
        apply (ShortExact_ShortShortExact_isEqualizer_Eq SSE w h H').

    (* Commutativity *)
    - apply KernelCommutes.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. cbn in T. apply KernelInsEq.
      use (pathscomp0 T). apply pathsinv0.
      apply KernelCommutes.
  Qed.

  Definition ShortExact_from_ShortShortExact (SSE : ShortShortExact hs) : ShortExact A hs.
  Proof.
    use mk_ShortExact.
    - use mk_ShortShortExact.
      + use mk_ShortShortExactData.
        * use mk_MorphismPair.
          -- exact (Abelian.Image (Mor1 SSE)).
          -- exact (Ob2 SSE).
          -- exact (Abelian.CoImage (Mor2 SSE)).
          -- exact (KernelArrow (Abelian.Image (Mor1 SSE))).
          -- exact (CokernelArrow (Abelian.CoImage (Mor2 SSE))).
        * exact (ShortExact_from_ShortShortExact_eq SSE).
      + exact (ShortExact_ShortShortExact_isEqualizer SSE).
    - exact (KernelArrowisMonic Abelian.Zero _).
    - exact (CokernelArrowisEpi Abelian.Zero _).
  Defined.


  (** ** [ShortShortExact] from data of [ShortExact]
    We construct a [ShortShortExact] from data corresponding to [ShortExact]. For a more precise
    statement, see the comment above [ShortShortExact_from_isShortExact]. *)

  Local Lemma ShortShortExact_from_isSortExact_eq {a b c : A} (f : a --> b) (g : b --> c)
             (H : (KernelArrow (Abelian.Image f)) ;; (CokernelArrow (Abelian.CoImage g))
                  = ZeroArrow Abelian.Zero _ _)
             (isEq : isEqualizer (CokernelArrow (Abelian.CoImage g)) (ZeroArrow Abelian.Zero _ _)
                                 (KernelArrow (Abelian.Image f)) (KernelEqRw Abelian.Zero H)) :
    f ;; g = ZeroArrow Abelian.Zero _ _.
  Proof.
    set (tmp := maponpaths (fun h : _ => CokernelArrow (Abelian.CoImage f) ;; (CoIm_to_Im f) ;; h) H).
    cbn in tmp. rewrite ZeroArrow_comp_right in tmp.
    apply (maponpaths (fun h : _ => h ;; (CoIm_to_Im g) ;; ((KernelArrow (Abelian.Image g))))) in tmp.
    rewrite ZeroArrow_comp_left in tmp.
    repeat rewrite assoc in tmp.

    (* Work on f in tmp *)
    set (fact := factorization2 hs f).
    unfold factorization2_epi in fact. cbn in fact.
    rewrite assoc in fact. rewrite <- fact in tmp. clear fact.

    (* Work of g in tmp *)
    set (fact := factorization1 hs g).
    unfold factorization2_monic in fact. cbn in fact.
    repeat rewrite <- assoc in tmp. repeat rewrite <- assoc in fact.
    rewrite <- fact in tmp. clear fact.

    rewrite ZeroArrow_comp_left in tmp. exact tmp.
  Qed.

  Local Lemma ShortShortExact_from_isShortExact_isEqualizer_eq {a b c : A} (f : a --> b) (g : b --> c)
        (H : (KernelArrow (Abelian.Image f)) ;; (CokernelArrow (Abelian.CoImage g)) =
             ZeroArrow Abelian.Zero _ _)
        (isEq : isEqualizer (CokernelArrow (Abelian.CoImage g)) (ZeroArrow Abelian.Zero _ _)
                            (KernelArrow (Abelian.Image f)) (KernelEqRw Abelian.Zero H))
        (w : A) (h : A ⟦w, b⟧) (H' : h ;; g = h ;; ZeroArrow Abelian.Zero b c) :
    h ;; CokernelArrow (Abelian.Cokernel f) = ZeroArrow Abelian.Zero w (Abelian.Cokernel f).
  Proof.
    set (ker := mk_Kernel Abelian.Zero (KernelArrow (Abelian.Image f))
                          (CokernelArrow (Abelian.CoImage g)) H isEq).
    rewrite ZeroArrow_comp_right in H'.

    (* Rewrite g in H' *)
    set (fact := factorization2 hs g).
    unfold factorization2_epi in fact. cbn in fact.
    rewrite fact in H'. clear fact.

    (* Use commutativity of ker *)
    rewrite assoc in H'.
    assert (X : h ;; CokernelArrow (Abelian.CoImage g) = ZeroArrow Abelian.Zero _ _).
    {
      apply (factorization2_is_monic hs g).
      rewrite ZeroArrow_comp_left.
      apply H'.
    }
    set (comm1 := KernelCommutes Abelian.Zero ker w h X).
    unfold ker in comm1. cbn in comm1.

    rewrite <- comm1. unfold Image. rewrite <- assoc.
    rewrite KernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Local Lemma ShortShortExact_from_isShortExact_isEqualizer {a b c : A} (f : a --> b) (g : b --> c)
        (H : (KernelArrow (Abelian.Image f)) ;; (CokernelArrow (Abelian.CoImage g)) =
             ZeroArrow Abelian.Zero _ _)
        (isEq : isEqualizer (CokernelArrow (Abelian.CoImage g)) (ZeroArrow Abelian.Zero _ _)
                            (KernelArrow (Abelian.Image f)) (KernelEqRw Abelian.Zero H)) :
    let SSED := mk_ShortShortExactData Abelian.Zero (mk_MorphismPair f g)
                                       (ShortShortExact_from_isSortExact_eq f g H isEq) in
    isEqualizer g (ZeroArrow Abelian.Zero b c) (KernelArrow (Image SSED))
                (KernelEqRw Abelian.Zero (Image_Eq hs SSED)).
  Proof.
    cbn zeta.
    use mk_isEqualizer.
    intros w h H'.
    use unique_exists; cbn in *.

    (* Construction of the arrow *)
    - unfold Image; cbn.
      use KernelIn.
      + exact h.
      + exact (ShortShortExact_from_isShortExact_isEqualizer_eq f g H isEq w h H').

    (* Comutativity *)
    - apply KernelCommutes.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. apply KernelInsEq.
      rewrite T. apply pathsinv0.
      apply KernelCommutes.
  Qed.

  (** To see how the assumptions correspond to [ShortExact] note that every kernel is a monic and
     every cokernel is an epi. Also, the assumption H says that an image of f is the kernel of a
     coimage of g. In abelian categories every monic is the kernel of its cokernel, and thus one
     can show that in isE the kernelarrow can be "replaced" by the kernelarrow of the image of the
     kernelarrow. Thus the assumptions are similar to assumptions of [ShortExact]. *)
  Definition ShortShortExact_from_isShortExact {a b c : A} (f : a --> b) (g : b --> c)
             (H : (KernelArrow (Abelian.Image f)) ;; (CokernelArrow (Abelian.CoImage g)) =
                  ZeroArrow Abelian.Zero _ _)
             (isEq : isEqualizer (CokernelArrow (Abelian.CoImage g)) (ZeroArrow Abelian.Zero _ _)
                                 (KernelArrow (Abelian.Image f)) (KernelEqRw Abelian.Zero H)) :
    ShortShortExact hs.
  Proof.
    use mk_ShortShortExact.
    - use mk_ShortShortExactData.
      + use mk_MorphismPair.
        * exact a.
        * exact b.
        * exact c.
        * exact f.
        * exact g.
      + exact (ShortShortExact_from_isSortExact_eq f g H isEq).
    - exact (ShortShortExact_from_isShortExact_isEqualizer f g H isEq).
  Defined.

End shortexact_correspondence.
Arguments ShortExact_from_ShortShortExact [A] _ _.
Arguments ShortShortExact_from_isShortExact [A] _ _ _ _ _ _ _ _.
