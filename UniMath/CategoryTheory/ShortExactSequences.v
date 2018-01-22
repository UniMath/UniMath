(** * Short exact sequences *)
(** ** Contents
- Definitions
 - ShortShortExact sequences
 - Remark on monics, epis, kernels, and cokernels
 - LeftShortExact sequences
 - RightShortExact sequences
 - ShortExact sequences
- Opposite category and (short/left/right)exacts
- A criteria for ShortShortExact
 - Cokernel from ShortShortExact
 - isCoequalizer to ShortShortExact
- Correspondence between ShortExact and ShortShortExact
 - ShortExact from ShortShortExact
 - ShortShortExact criteria
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.Opp.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.opp_precat.
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

Local Open Scope cat.


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
  Definition Image (SSED : ShortShortExactData A (to_Zero A)) :
    Kernel (to_Zero A) (CokernelArrow (Abelian.Cokernel (Mor1 SSED))) := Image (Mor1 SSED).

  Lemma isExact_Eq {x y z : ob A} (f : x --> y) (g : y --> z)
        (H : f · g = ZeroArrow (to_Zero A) _ _) :
    KernelArrow (Abelian.Image f) · g = ZeroArrow (to_Zero A) _ _.
  Proof.
    unfold Abelian.Image.
    set (fact := factorization1 hs f).
    unfold factorization1_monic in fact. cbn in fact.
    apply (factorization1_is_epi hs f).
    rewrite ZeroArrow_comp_right.
    rewrite assoc. rewrite fact in H. clear fact.
    exact H.
  Qed.

  Definition isExact {x y z : ob A} (f : x --> y) (g : y --> z)
             (H : f · g = ZeroArrow (to_Zero A) _ _) : UU :=
    isKernel (to_Zero A) (KernelArrow (Abelian.Image f)) g (isExact_Eq f g H).

  Lemma Image_Eq (SSED : ShortShortExactData A (to_Zero A)) :
    (KernelArrow (Image SSED)) · (Mor2 SSED) = ZeroArrow (to_Zero A) _ _.
  Proof.
    exact (isExact_Eq (Mor1 SSED) (Mor2 SSED) (ShortShortExactData_Eq (to_Zero A) SSED)).
  Defined.

  (** Coimage of the second morphism and equality of morphisms associated to it. *)
  Definition CoImage (SSED : ShortShortExactData A (to_Zero A)) :
    Cokernel (to_Zero A) (KernelArrow (Abelian.Kernel (Mor2 SSED))) := CoImage (Mor2 SSED).

  Lemma isExact'_Eq {x y z : ob A} (f : x --> y) (g : y --> z)
        (H : f · g = ZeroArrow (to_Zero A) _ _) :
    f · CokernelArrow (Abelian.CoImage g) = ZeroArrow (to_Zero A) _ _.
  Proof.
    unfold Abelian.CoImage.
    set (fact := factorization2 hs g).
    unfold factorization2_epi in fact. cbn in fact. unfold Abelian.CoImage in fact.
    apply (factorization2_is_monic hs g).
    rewrite ZeroArrow_comp_left.
    rewrite <- assoc. apply (maponpaths (λ gg : _, f · gg)) in fact.
    use (pathscomp0 (! fact)). exact H.
  Qed.

  Definition isExact' {x y z : ob A} (f : x --> y) (g : y --> z)
             (H : f · g = ZeroArrow (to_Zero A) _ _) : UU :=
    isCokernel (to_Zero A) f (CokernelArrow (Abelian.CoImage g)) (isExact'_Eq f g H).

  Lemma CoImage_Eq (SSED : ShortShortExactData A (to_Zero A)) :
    (Mor1 SSED) · (CokernelArrow (CoImage SSED)) = ZeroArrow (to_Zero A) _ _.
  Proof.
    exact (isExact'_Eq (Mor1 SSED) (Mor2 SSED) (ShortShortExactData_Eq (to_Zero A) SSED)).
  Defined.


  (** ** Transform isExact to isExact' and isExact' to isExact *)

  Local Lemma isExact_to_isExact'_Eq {x y z : ob A} {f : x --> y} {g : y --> z}
        {H' : f · g = ZeroArrow (to_Zero A) _ _} (iE : isExact f g H') (w0 : A)
        (h : A ⟦y, w0⟧) (H : f · h = ZeroArrow (to_Zero A) _ _) :
    KernelArrow (Abelian.Kernel g) · h = ZeroArrow (to_Zero A) (Abelian.Kernel g) w0.
  Proof.
    unfold isExact in iE.
    set (K := mk_Kernel _ _ _ _ iE).
    set (i := iso_from_Kernel_to_Kernel (to_Zero A) K (Abelian.Kernel g)).
    use (is_iso_isEpi A i (pr2 i)). rewrite ZeroArrow_comp_right. rewrite assoc.
    cbn. unfold from_Kernel_to_Kernel. rewrite KernelCommutes.
    use (factorization1_is_epi hs f). cbn.
    set (tmp := factorization1 hs f).
    unfold factorization1_epi in tmp.
    unfold factorization1_monic in tmp.
    cbn in tmp. rewrite assoc. rewrite <- tmp. clear tmp.
    rewrite ZeroArrow_comp_right.
    exact H.
  Qed.

  Lemma isExact_to_isExact' {x y z : ob A} {f : x --> y} {g : y --> z}
        {H : f · g = ZeroArrow (to_Zero A) _ _} (iE : isExact f g H) : isExact' f g H.
  Proof.
    unfold isExact in iE. unfold isExact'.
    use (mk_isCokernel hs).
    intros w0 h H'.
    use unique_exists.
    (* Construction of the morphism *)
    - use CokernelOut.
      + exact h.
      + cbn. exact (isExact_to_isExact'_Eq iE w0 h H').
    (* Commutativity *)
    - apply CokernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y'. apply hs.
    (* Uniqueness *)
    - intros y' T. cbn in T.
      apply CokernelOutsEq.
      rewrite T. apply pathsinv0.
      apply CokernelCommutes.
  Qed.

  Local Lemma isExact'_to_isExact_Eq {x y z : ob A} {f : x --> y} {g : y --> z}
        {H : f · g = ZeroArrow (to_Zero A) _ _} (iE : isExact' f g H) {w0 : ob A}
        (h : A⟦ w0, y ⟧)  (H' : h · g = ZeroArrow (to_Zero A) w0 z) :
    h · CokernelArrow (Abelian.Cokernel f) = ZeroArrow (to_Zero A) w0 (Abelian.Cokernel f).
  Proof.
    unfold isExact' in iE.
    set (CK := mk_Cokernel _ _ _ _ iE).
    set (i := iso_from_Cokernel_to_Cokernel (to_Zero A) (Abelian.Cokernel f) CK).
    use (is_iso_isMonic A i (pr2 i)). rewrite ZeroArrow_comp_left. rewrite <- assoc.
    cbn. unfold from_Cokernel_to_Cokernel. rewrite CokernelCommutes.
    use (factorization2_is_monic hs g). cbn.
    set (tmp := factorization2 hs g).
    unfold factorization2_monic in tmp.
    unfold factorization2_epi in tmp.
    cbn in tmp. rewrite <- assoc. rewrite <- tmp. clear tmp.
    rewrite ZeroArrow_comp_left.
    exact H'.
  Qed.

  Lemma isExact'_to_isExact {x y z : ob A} {f : x --> y} {g : y --> z}
        {H : f · g = ZeroArrow (to_Zero A) _ _} (iE : isExact' f g H) : isExact f g H.
  Proof.
    unfold isExact' in iE. unfold isExact.
    use (mk_isKernel hs).
    intros w0 h H'.
    use unique_exists.
    (* Construction of the morphism *)
    - use KernelIn.
      + exact h.
      + cbn. exact (isExact'_to_isExact_Eq iE h H').
    (* Commutativity *)
    - apply KernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y'. apply hs.
    (* Uniqueness *)
    - intros y' T. cbn in T.
      apply KernelInsEq.
      rewrite T. apply pathsinv0.
      apply KernelCommutes.
  Qed.

  Lemma isExactisMonic {x y : ob A} {f : x --> y} (isM : isMonic f)
        (H : ZeroArrow (to_Zero A) (to_Zero A) x · f = ZeroArrow (to_Zero A) (to_Zero A) y) :
    isExact (ZeroArrow (to_Zero A) (to_Zero A) x) f H.
  Proof.
    unfold isExact.
    use mk_isKernel.
    - exact hs.
    - intros w h H'.
      use unique_exists.
      + use KernelIn.
        * exact h.
        * rewrite <- (ZeroArrow_comp_left _ _ _ _ _ f) in H'. apply isM in H'.
          rewrite H'. apply ZeroArrow_comp_left.
      + cbn. use KernelCommutes.
      + intros y'. apply hs.
      + intros y' X. cbn in X. cbn.
        use (KernelArrowisMonic (to_Zero A) (Abelian.Image (ZeroArrow (to_Zero A) (to_Zero A) x))).
        rewrite X. apply pathsinv0. use KernelCommutes.
  Qed.

  Lemma isExactisEpi {x y : ob A} {f : x --> y} (isE : isEpi f)
        (H : f · ZeroArrow (to_Zero A) y (to_Zero A) = ZeroArrow (to_Zero A) x (to_Zero A)) :
    isExact f (ZeroArrow (to_Zero A) y (to_Zero A)) H.
  Proof.
    unfold isExact.
    use mk_isKernel.
    - exact hs.
    - intros w h H'.
      use unique_exists.
      + use KernelIn.
        * exact h.
        * rewrite <- (ZeroArrow_comp_right _ _ _ _ _ h). apply cancel_precomposition.
          apply isE. rewrite CokernelCompZero. rewrite ZeroArrow_comp_right.
          apply idpath.
      + cbn. use KernelCommutes.
      + intros y'. apply hs.
      + intros y' X. cbn. cbn in X.
        use (KernelArrowisMonic (to_Zero A) (Abelian.Image f)).
        rewrite X. apply pathsinv0. use KernelCommutes.
  Qed.

  (** ** [Short Short Exact]
    [ShortShortData] such that the image of the first morphism is the kernel of the second morphism.
    Informally, an exact sequence
                               A -> B -> C
   *)

  Definition ShortShortExact : UU :=
    ∑ SSED : ShortShortExactData A (to_Zero A),
             isKernel (to_Zero A) (KernelArrow (Image SSED)) (Mor2 SSED) (Image_Eq SSED).

  Definition mk_ShortShortExact (SSED : ShortShortExactData A (to_Zero A))
             (H : isKernel (to_Zero A) (KernelArrow (Image SSED)) (Mor2 SSED) (Image_Eq SSED)) :
    ShortShortExact := tpair _ SSED H.

  (** Accessor functions *)
  Definition ShortShortExact_ShortShortExactData (SSE : ShortShortExact) :
    ShortShortExactData A (to_Zero A) := pr1 SSE.
  Coercion ShortShortExact_ShortShortExactData : ShortShortExact >-> ShortShortExactData.

  Definition ShortShortExact_isKernel (SSE : ShortShortExact) :
    isKernel (to_Zero A) (KernelArrow (Image SSE)) (Mor2 SSE) (Image_Eq SSE) := pr2 SSE.

  Definition ShortShortExact_Kernel (SSE : ShortShortExact) : Kernel (to_Zero A) (Mor2 SSE) :=
    mk_Kernel (to_Zero A) (KernelArrow (Image SSE)) (Mor2 SSE) (Image_Eq SSE)
               (ShortShortExact_isKernel SSE).


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

  Definition LeftShortExact : UU := ∑ SSE : ShortShortExact, isMonic (Mor1 SSE).

  Definition mk_LeftShortExact (SSE : ShortShortExact) (isM : isMonic (Mor1 SSE)) :
    LeftShortExact := tpair _ SSE isM.

  (** Accessor functions *)
  Definition LeftShortExact_ShortShortExact (LSE : LeftShortExact) : ShortShortExact := pr1 LSE.
  Coercion LeftShortExact_ShortShortExact : LeftShortExact >-> ShortShortExact.

  Definition isMonic (LSE : LeftShortExact) : isMonic (Mor1 LSE) := pr2 LSE.


  (** ** [RightShortExact]
    [ShortShortExact] such that the second morphism is an epi. Informally, an exact sequece
                               A -> B -> C -> 0
   *)

  Definition RightShortExact : UU := ∑ SSE : ShortShortExact, isEpi (Mor2 SSE).

  Definition mk_RightShortExact (SSE : ShortShortExact) (isE : isEpi (Mor2 SSE)) :
    RightShortExact := tpair _ SSE isE.

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
    ∑ SSE : ShortShortExact, Monics.isMonic (Mor1 SSE) × Epis.isEpi (Mor2 SSE).

  Definition mk_ShortExact (SSE : ShortShortExact) (isM : Monics.isMonic (Mor1 SSE))
             (isE : Epis.isEpi (Mor2 SSE)) : ShortExact := (SSE,,(isM,,isE)).

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
Arguments ShortShortExact_isKernel [A] _ _ _ _ _.
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
  of the first morphism and give a way to construct [ShortShortExact] from certain isCokernel. *)
Section shortshortexact_cokernel.

  Variable A : AbelianPreCat.
  Hypothesis hs : has_homsets A.


  (** ** [ShortShortExact] implies isCoequalizer.
    Note that in the definition of [ShortShortExact] we use isEqualizer to say that an image of the
    first morphism is a kernel of the second morphism. We show that also the coimage of the second
    morphism is a cokernel of the first morphism. Informally, this follows directly from the fact
    that the opposite category of an abelian category is an abelian category and that taking the
    opposite category twice, we get the same category. *)

  Local Lemma ShortShortExact_isCokernel_eq1 (SSE : ShortShortExact hs) (w0 : A)
        (h : A ⟦Ob2 SSE, w0⟧) (H : Mor1 SSE · h = ZeroArrow (to_Zero A) _ _) :
    (KernelArrow (ShortShortExact_Kernel hs SSE)) · h = ZeroArrow (to_Zero A) _ _.
  Proof.
    apply (factorization1_is_epi hs (Mor1 SSE)).
    set (tmp := factorization1 hs (Mor1 SSE)).
    unfold factorization1_epi in tmp.
    unfold factorization1_monic in tmp.
    cbn in tmp. rewrite assoc. unfold ShortShortExact_Kernel.
    cbn. unfold Image. rewrite <- tmp. clear tmp.
    rewrite ZeroArrow_comp_right.
    exact H.
  Qed.

  Local Lemma ShortShortExact_isCokernel_eq2 (SSE : ShortShortExact hs) (w0 : A)
        (h : A ⟦Ob2 SSE, w0⟧) (H : Mor1 SSE · h = ZeroArrow (to_Zero A) _ _) :
    KernelArrow (Abelian.Kernel (Mor2 SSE)) · h = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (i := iso_from_Kernel_to_Kernel (to_Zero A) (ShortShortExact_Kernel hs SSE)
                                        (Abelian.Kernel (Mor2 SSE))).
    set (epi := is_iso_Epi A i (pr2 i)).
    apply (pr2 epi). cbn. rewrite ZeroArrow_comp_right.
    rewrite assoc. unfold from_Kernel_to_Kernel.
    rewrite KernelCommutes.
    apply (ShortShortExact_isCokernel_eq1 SSE w0 h H).
  Qed.

  Local Lemma ShortShortExact_isCokernel (SSE : ShortShortExact hs) :
    isCokernel (to_Zero A) (Mor1 SSE) (CokernelArrow (CoImage SSE)) (CoImage_Eq hs SSE).
  Proof.
    use (mk_isCokernel hs).
    intros w0 h H'.
    use unique_exists.
    (* Construction of the morphism *)
    - exact (CokernelOut
               (to_Zero A) (CoImage SSE) w0 h (ShortShortExact_isCokernel_eq2 SSE w0 h H')).
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

  Definition ShortShortExact_Cokernel (SSE : ShortShortExact hs) :
    Cokernel (to_Zero A) (Mor1 SSE) := mk_Cokernel (to_Zero A) (Mor1 SSE) (CokernelArrow (CoImage SSE))
                                               (CoImage_Eq hs SSE)
                                               (ShortShortExact_isCokernel SSE).


  (** ** From isCokernel to [ShortShortExact]
    We show that we can construct [ShortShortExact] from the isCokernel property proved above. *)

  Local Lemma ShortShortExact_from_isCokernel_eq1 (SSED : ShortShortExactData A (to_Zero A))
        (w : A) (h : A ⟦w, Ob2 SSED⟧)
        (H : (h · (CokernelArrow (Abelian.CoImage (Mor2 SSED)))) = ZeroArrow (to_Zero A) _ _)
        (H' : isCokernel (to_Zero A) (Mor1 SSED) (CokernelArrow (CoImage SSED)) (CoImage_Eq hs SSED)) :
    h · CokernelArrow (Abelian.Cokernel (Mor1 SSED)) = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (coker := mk_Cokernel (to_Zero A) (Mor1 SSED) (CokernelArrow (CoImage SSED))
                              (CoImage_Eq hs SSED) H').
    set (i := iso_from_Cokernel_to_Cokernel (to_Zero A) (Abelian.Cokernel (Mor1 SSED)) coker).
    set (isM := is_iso_Monic A i (pr2 i)). apply (pr2 isM). cbn.
    rewrite ZeroArrow_comp_left. rewrite <- assoc.
    unfold from_Cokernel_to_Cokernel.
    rewrite CokernelCommutes.
    unfold coker. cbn. unfold CoImage.
    exact H.
  Qed.

  Local Lemma ShortShortExact_from_isCokernel_eq2 (SSED : ShortShortExactData A (to_Zero A))
        (w : A) (h : A ⟦w, Ob2 SSED⟧) (H : h · Mor2 SSED = ZeroArrow (to_Zero A) _ _)
        (H' : isCokernel
                (to_Zero A) (Mor1 SSED) (CokernelArrow (CoImage SSED)) (CoImage_Eq hs SSED)) :
    h · CokernelArrow (Abelian.CoImage (Mor2 SSED)) = ZeroArrow (to_Zero A) _ _.
  Proof.
    apply (factorization2_is_monic hs (Mor2 SSED)).
    set (tmp := factorization2 hs (Mor2 SSED)).
    unfold factorization2_epi in tmp.
    unfold factorization2_monic in tmp.
    cbn in tmp. rewrite <- assoc. rewrite <- tmp.
    clear tmp.
    rewrite ZeroArrow_comp_left.
    exact H.
  Qed.

  Lemma ShortShortExact_from_isCokernel_isKernel
        (SSED : ShortShortExactData A (to_Zero A))
        (H : isCokernel
               (to_Zero A) (Mor1 SSED) (CokernelArrow (CoImage SSED)) (CoImage_Eq hs SSED)) :
    isKernel (to_Zero A) (KernelArrow (Image SSED)) (Mor2 SSED) (Image_Eq hs SSED).
  Proof.
    use (mk_isKernel hs).
    intros w h H'.
    use unique_exists.
    (* Construction of the morphism *)
    - apply (KernelIn (to_Zero A) (Image SSED) w h
                      (ShortShortExact_from_isCokernel_eq1
                         SSED w h (ShortShortExact_from_isCokernel_eq2 SSED w h H' H) H)).
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

  Definition ShortShortExact_from_isCokernel (SSED : ShortShortExactData A (to_Zero A))
             (H : isCokernel (to_Zero A) (Mor1 SSED) (CokernelArrow (CoImage SSED))
                             (CoImage_Eq hs SSED)) : ShortShortExact hs :=
    mk_ShortShortExact hs SSED (ShortShortExact_from_isCokernel_isKernel SSED H).

End shortshortexact_cokernel.
Arguments ShortShortExact_Cokernel [A] _ _.
Arguments ShortShortExact_from_isCokernel [A] _ _ _.


(** * Correspondence of shortexact in A an A^op *)
Section shortexact_opp.

  Local Opaque ZeroArrow isKernel isCokernel.

  Lemma isExact_opp_Eq {A : AbelianPreCat} {hs : has_homsets A} {x y z : ob A} {f : x --> y}
        {g : y --> z} (H : f · g = ZeroArrow (to_Zero A) _ _) :
    (g : (Abelian_opp A hs)⟦_, _⟧) · (f : (Abelian_opp A hs)⟦_, _⟧) =
    @ZeroArrow (Abelian_opp A hs) (Zero_opp A (to_Zero A)) _ _.
  Proof.
    cbn. use (pathscomp0 H). use ZeroArrow_opp.
  Qed.

  Unset Kernel Term Sharing.
  Lemma isExact_opp {A : AbelianPreCat} {hs : has_homsets A} {x y z : ob A} {f : x --> y}
             {g : y --> z} {H : f · g = ZeroArrow (to_Zero A) _ _} (iE : isExact A hs f g H) :
    isExact (Abelian_opp A hs) (has_homsets_opp hs) g f (isExact_opp_Eq H).
  Proof.
    unfold isExact.
    use isKernel_opp.
    - exact hs.
    - exact (to_Zero A).
    - exact (isExact'_Eq A hs f g H).
    - exact (isExact_to_isExact' A hs iE).
  Qed.
  Set Kernel Term Sharing.

  Definition ShortShortExact_opp {A : AbelianPreCat} {hs : has_homsets A}
             (SSE : ShortShortExact hs) : ShortShortExact (has_homsets_Abelian_opp hs).
  Proof.
    use mk_ShortShortExact.
    - exact (ShortShortExactData_opp SSE).
    - cbn. use isKernel_opp.
      + exact hs.
      + exact (to_Zero A).
      + exact (CoImage_Eq hs SSE).
      + exact (CokernelisCokernel (to_Zero A) (ShortShortExact_Cokernel hs SSE)).
  Defined.

  Unset Kernel Term Sharing.
  Local Lemma opp_ShortShortExact_isKernel {A : AbelianPreCat} {hs : has_homsets A}
        (SSE : ShortShortExact (has_homsets_Abelian_opp hs)) :
    isKernel (to_Zero A) (KernelArrow (Image (opp_ShortShortExactData SSE)))
             (Mor2 (opp_ShortShortExactData SSE))
             (Image_Eq hs (opp_ShortShortExactData SSE)).
  Proof.
    cbn. use opp_isKernel.
    - exact hs.
    - exact (Zero_opp A (to_Zero A)).
    - exact (CoImage_Eq (has_homsets_Abelian_opp hs) SSE).
    - exact (@CokernelisCokernel
               (Abelian_opp A hs) (Zero_opp A (to_Zero A)) _ _ _
               (ShortShortExact_Cokernel (has_homsets_Abelian_opp hs) SSE)).
  Qed.
  Set Kernel Term Sharing.

  Definition opp_ShortShortExact {A : AbelianPreCat} {hs : has_homsets A}
             (SSE : ShortShortExact (has_homsets_Abelian_opp hs)) : ShortShortExact hs.
  Proof.
    use mk_ShortShortExact.
    - exact (opp_ShortShortExactData SSE).
    - exact (opp_ShortShortExact_isKernel SSE).
  Defined.

  Definition LeftShortExact_opp {A : AbelianPreCat} {hs : has_homsets A} (LSE : LeftShortExact hs) :
    RightShortExact (has_homsets_Abelian_opp hs).
  Proof.
    use mk_RightShortExact.
    - exact (ShortShortExact_opp LSE).
    - use isMonic_opp. exact (isMonic hs LSE).
  Defined.

  Definition opp_LeftShortExact {A : AbelianPreCat} {hs : has_homsets A}
             (LSE : LeftShortExact (has_homsets_Abelian_opp hs)) : RightShortExact hs.
  Proof.
    use mk_RightShortExact.
    - exact (opp_ShortShortExact LSE).
    - use opp_isMonic. exact (isMonic (has_homsets_Abelian_opp hs) LSE).
  Defined.

  Definition RightShortExact_opp {A : AbelianPreCat} {hs : has_homsets A}
             (RSE : RightShortExact hs) : LeftShortExact (has_homsets_Abelian_opp hs).
  Proof.
    use mk_LeftShortExact.
    - exact (ShortShortExact_opp RSE).
    - use isEpi_opp. exact (isEpi hs RSE).
  Defined.

  Definition opp_RightShortExact {A : AbelianPreCat} {hs : has_homsets A}
             (RSE : RightShortExact (has_homsets_Abelian_opp hs)) : LeftShortExact hs.
  Proof.
    use mk_LeftShortExact.
    - exact (opp_ShortShortExact RSE).
    - use opp_isEpi. exact (isEpi (has_homsets_Abelian_opp hs) RSE).
  Defined.

  Definition ShortExact_opp {A : AbelianPreCat} {hs : has_homsets A} (SE : ShortExact _ hs) :
    ShortExact _ (has_homsets_Abelian_opp hs).
  Proof.
    use mk_ShortExact.
    - exact (ShortShortExact_opp SE).
    - use isEpi_opp. exact (isEpi hs SE).
    - use isMonic_opp. exact (isMonic hs SE).
  Defined.

  Definition opp_ShortExact {A : AbelianPreCat} {hs : has_homsets A}
             (SE : ShortExact _ (has_homsets_Abelian_opp hs)) : ShortExact _ hs.
  Proof.
    use mk_ShortExact.
    - exact (opp_ShortShortExact SE).
    - use opp_isEpi. exact (isEpi (has_homsets_Abelian_opp hs) SE).
    - use opp_isMonic. exact (isMonic (has_homsets_Abelian_opp hs) SE).
  Defined.

End shortexact_opp.


(** * [LeftShortExact] and [RightShortExact] from a [ShortShortExact] with extra properties *)
Section shortshortexact_to_leftshortexact.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.

  Definition LeftShortExact_from_ShortShortExact (SSE : ShortShortExact hs)
             (isK : isKernel
                      (to_Zero A) (Mor1 SSE) (Mor2 SSE) (ShortShortExactData_Eq (to_Zero A) SSE)) :
    LeftShortExact hs.
  Proof.
    use mk_LeftShortExact.
    - exact SSE.
    - exact (KernelArrowisMonic _ (mk_Kernel _ _ _ _ isK)).
  Defined.

  Definition RightShortExact_from_ShortShortExact (SSE : ShortShortExact hs)
             (isCK : isCokernel
                       (to_Zero A) (Mor1 SSE) (Mor2 SSE) (ShortShortExactData_Eq (to_Zero A) SSE)) :
    RightShortExact hs.
  Proof.
    use mk_RightShortExact.
    - exact SSE.
    - exact (CokernelArrowisEpi _ (mk_Cokernel _ _ _ _ isCK)).
  Defined.

End shortshortexact_to_leftshortexact.


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
    (KernelArrow (Abelian.Image (Mor1 SSE))) · (CokernelArrow (Abelian.CoImage (Mor2 SSE))) =
    ZeroArrow (to_Zero A) _ _.
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
    (* Follows now from the Eq *)
    apply (ShortShortExactData_Eq (to_Zero A) SSE).
  Qed.

  Local Lemma ShortExact_ShortShortExact_isKernel_Eq (SSE : ShortShortExact hs) (w : A)
             (h : A ⟦w, Ob2 SSE⟧)
             (H' : h · CokernelArrow (Abelian.CoImage (Mor2 SSE)) = ZeroArrow (to_Zero A) _ _) :
    let Im := Abelian.Image (Mor1 SSE) in
    h · (CokernelArrow (Abelian.Cokernel (KernelArrow Im))) = ZeroArrow (to_Zero A) _ _.
  Proof.
    cbn zeta.
    assert (X : h · Mor2 SSE = ZeroArrow (to_Zero A) _ _).
    {
      rewrite (factorization2 hs (Mor2 SSE)).
      unfold factorization2_epi. cbn.
      set (tmp := factorization2_monic A hs (Mor2 SSE)).
      apply (maponpaths (λ h' : _, h' · tmp)) in H'. unfold tmp in H'.
      clear tmp. rewrite ZeroArrow_comp_left in H'. rewrite <- assoc in H'.
      unfold factorization2_monic in H'. cbn in H'.
      exact H'.
    }
    set (comm1 := KernelCommutes (to_Zero A) (Abelian.Kernel (Mor2 SSE)) w h X).
    set (ker := ShortShortExact_Kernel hs SSE).
    set (tmp := Abelian.Kernel (Mor2 SSE)).
    set (tmp_eq := (KernelCompZero (to_Zero A) tmp)).
    set (comm2 := KernelCommutes (to_Zero A) ker tmp (KernelArrow tmp) tmp_eq).
    unfold tmp in comm2. rewrite <- comm2 in comm1. clear comm2.
    rewrite <- comm1. rewrite <- assoc. rewrite <- assoc.
    rewrite CokernelCompZero. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Local Lemma ShortExact_ShortShortExact_isKernel (SSE : ShortShortExact hs) :
    let Im := Abelian.Image (Mor1 SSE) in
    let CoIm := Abelian.CoImage (Mor2 SSE) in
    let MP := mk_MorphismPair (KernelArrow Im) (CokernelArrow CoIm) in
    let SSED := mk_ShortShortExactData (to_Zero A) MP (ShortExact_from_ShortShortExact_eq SSE) in
    isKernel (to_Zero A) (KernelArrow (Image SSED)) (CokernelArrow CoIm) (Image_Eq hs SSED).
  Proof.
    intros Im CoIm MP SSED.
    use (mk_isKernel hs).
    intros w h H'.
    use unique_exists.
    (* Construction of the morphism *)
    - use KernelIn.
      + exact h.
      + apply (ShortExact_ShortShortExact_isKernel_Eq SSE w h H').
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
      + exact (ShortExact_ShortShortExact_isKernel SSE).
    - exact (KernelArrowisMonic (to_Zero A) _).
    - exact (CokernelArrowisEpi (to_Zero A) _).
  Defined.


  (** ** [ShortShortExact] from data of [ShortExact]
    We construct a [ShortShortExact] from data corresponding to [ShortExact]. For a more precise
    statement, see the comment above [ShortShortExact_from_isShortExact]. *)

  Local Lemma ShortShortExact_from_isSortExact_eq {a b c : A} (f : a --> b) (g : b --> c)
             (H : (KernelArrow (Abelian.Image f)) · (CokernelArrow (Abelian.CoImage g))
                  = ZeroArrow (to_Zero A) _ _)
             (isEq : isKernel (to_Zero A) (KernelArrow (Abelian.Image f))
                              (CokernelArrow (Abelian.CoImage g)) H) :
    f · g = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (tmp := maponpaths (λ h : _, CokernelArrow (Abelian.CoImage f) · (CoIm_to_Im f) · h) H).
    cbn in tmp. rewrite ZeroArrow_comp_right in tmp.
    apply (maponpaths (λ h : _, h · (CoIm_to_Im g) · ((KernelArrow (Abelian.Image g))))) in tmp.
    rewrite ZeroArrow_comp_left in tmp.
    rewrite assoc in tmp.
    (* Work on f in tmp *)
    set (fact := factorization2 hs f).
    unfold factorization2_epi in fact. cbn in fact.
    rewrite assoc in fact. rewrite <- fact in tmp. clear fact.
    (* Work of g in tmp *)
    set (fact := factorization1 hs g).
    unfold factorization2_monic in fact. cbn in fact.
    rewrite <- assoc in tmp. rewrite <- assoc in tmp. rewrite <- assoc in fact.
    rewrite <- fact in tmp. clear fact.
    (* Follows from tmp *)
    rewrite ZeroArrow_comp_left in tmp. exact tmp.
  Qed.

  Local Lemma ShortShortExact_from_isShortExact_isKernel_eq {a b c : A} (f : a --> b) (g : b --> c)
        (H : (KernelArrow (Abelian.Image f)) · (CokernelArrow (Abelian.CoImage g)) =
             ZeroArrow (to_Zero A) _ _)
        (isEq : isKernel (to_Zero A) (KernelArrow (Abelian.Image f))
                         (CokernelArrow (Abelian.CoImage g)) H)
        (w : A) (h : A ⟦w, b⟧) (H' : h · g = ZeroArrow (to_Zero A) w c) :
    h · CokernelArrow (Abelian.Cokernel f) = ZeroArrow (to_Zero A) w (Abelian.Cokernel f).
  Proof.
    set (ker := mk_Kernel (to_Zero A) (KernelArrow (Abelian.Image f))
                          (CokernelArrow (Abelian.CoImage g)) H isEq).
    (* Rewrite g in H' *)
    set (fact := factorization2 hs g).
    unfold factorization2_epi in fact. cbn in fact.
    rewrite fact in H'. clear fact.
    (* Use commutativity of ker *)
    rewrite assoc in H'.
    assert (X : h · CokernelArrow (Abelian.CoImage g) = ZeroArrow (to_Zero A) _ _).
    {
      apply (factorization2_is_monic hs g).
      rewrite ZeroArrow_comp_left.
      apply H'.
    }
    set (comm1 := KernelCommutes (to_Zero A) ker w h X).
    unfold ker in comm1. cbn in comm1. rewrite <- comm1. clear comm1.
    (* Follows from KernelCompZero *)
    unfold Image. rewrite <- assoc.
    rewrite KernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Local Lemma ShortShortExact_from_isShortExact_isKernel {a b c : A} (f : a --> b) (g : b --> c)
        (H : (KernelArrow (Abelian.Image f)) · (CokernelArrow (Abelian.CoImage g)) =
             ZeroArrow (to_Zero A) _ _)
        (isK : isKernel (to_Zero A) (KernelArrow (Abelian.Image f))
                        (CokernelArrow (Abelian.CoImage g)) H) :
    let SSED := mk_ShortShortExactData (to_Zero A) (mk_MorphismPair f g)
                                       (ShortShortExact_from_isSortExact_eq f g H isK) in
    isKernel (to_Zero A) (KernelArrow (Image SSED)) g (Image_Eq hs SSED).
  Proof.
    intros SSED.
    use (mk_isKernel hs).
    intros w h H'.
    use unique_exists.
    (* Construction of the arrow *)
    - use KernelIn.
      + exact h.
      + exact (ShortShortExact_from_isShortExact_isKernel_eq f g H isK w h H').
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
             (H : (KernelArrow (Abelian.Image f)) · (CokernelArrow (Abelian.CoImage g)) =
                  ZeroArrow (to_Zero A) _ _)
             (isEq : isKernel (to_Zero A) (KernelArrow (Abelian.Image f))
                              (CokernelArrow (Abelian.CoImage g)) H) :
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
    - exact (ShortShortExact_from_isShortExact_isKernel f g H isEq).
  Defined.

End shortexact_correspondence.
Arguments ShortExact_from_ShortShortExact [A] _ _.
Arguments ShortShortExact_from_isShortExact [A] _ _ _ _ _ _ _ _.


(** * [ShortShortExact] from isKernel and isCokernel *)
(** ** Introduction
In this section we construct [ShortShortExact] from a pair of morphisms where the first morphism is
the kernel of the second morphisms and where the second morphism is the cokernel of the first
morphism.
 *)
Section shortshortexact_iskernel_iscokernel.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.

  Lemma mk_ShortShortExact_isKernel_isKernel (SSED : ShortShortExactData A (to_Zero A))
        (H : isKernel
               (to_Zero A) (Mor1 SSED) (Mor2 SSED) (ShortShortExactData_Eq (to_Zero A) SSED)) :
    isKernel (to_Zero A) (KernelArrow (Image SSED)) (Mor2 SSED) (Image_Eq hs SSED).
  Proof.
    set (K := mk_Kernel _ _ _ _ H).
    set (e1 := factorization1 hs (Mor1 SSED)). cbn in e1. unfold Image.
    assert (e : is_z_isomorphism (CokernelArrow (Abelian.CoImage (Mor1 SSED))
                                                · CoIm_to_Im (Mor1 SSED))).
    {
      use monic_epi_is_iso.
      - use isMonic_postcomp.
        + exact (Ob2 SSED).
        + exact (KernelArrow (Abelian.Image (Mor1 SSED))).
        + rewrite <- e1. use (KernelArrowisMonic (to_Zero A) K).
      - exact (factorization1_is_epi hs (Mor1 SSED)).
    }
    use Kernel_up_to_iso_isKernel.
    + exact hs.
    + exact K.
    + exact (z_iso_inv (mk_z_iso _ _ e)).
    + apply (maponpaths (λ g : _, (z_iso_inv_mor (mk_z_iso _ _ e)) · g)) in e1.
      use (pathscomp0 _ (! e1)). clear e1. rewrite assoc.
      cbn. rewrite (is_inverse_in_precat2 e). rewrite id_left. apply idpath.
  Qed.

  Definition mk_ShortShortExact_isKernel (SSED : ShortShortExactData A (to_Zero A))
             (H : isKernel (to_Zero A) (Mor1 SSED) (Mor2 SSED)
                           (ShortShortExactData_Eq (to_Zero A) SSED)) :
    ShortShortExact hs.
  Proof.
    use mk_ShortShortExact.
    - exact SSED.
    - exact (mk_ShortShortExact_isKernel_isKernel SSED H).
  Defined.

  Lemma mk_ShortShortExact_isCokernel_isKernel (SSED : ShortShortExactData A (to_Zero A))
        (H : isCokernel
               (to_Zero A) (Mor1 SSED) (Mor2 SSED) (ShortShortExactData_Eq (to_Zero A) SSED)) :
    isKernel (to_Zero A) (KernelArrow (Image SSED)) (Mor2 SSED) (Image_Eq hs SSED).
  Proof.
    use ShortShortExact_from_isCokernel_isKernel.
    set (CK := mk_Cokernel _ _ _ _ H).
    set (e1 := factorization2 hs (Mor2 SSED)). cbn in e1. unfold CoImage.
    assert (e : is_z_isomorphism (CoIm_to_Im (Mor2 SSED)
                                             · KernelArrow (Abelian.Image (Mor2 SSED)))).
    {
      use monic_epi_is_iso.
      - exact (factorization2_is_monic hs (Mor2 SSED)).
      - use isEpi_precomp.
        + exact (Ob2 SSED).
        + exact (CokernelArrow (Abelian.CoImage (Mor2 SSED))).
        + rewrite <- e1. use (CokernelArrowisEpi (to_Zero A) CK).
    }
    use Cokernel_up_to_iso_isCokernel.
    + exact hs.
    + exact CK.
    + exact (z_iso_inv (mk_z_iso _ _ e)).
    + apply (maponpaths (λ g : _, g · (z_iso_inv_mor (mk_z_iso _ _ e)))) in e1.
      use (pathscomp0 _ (! e1)). clear e1. rewrite <- assoc. cbn.
      rewrite (is_inverse_in_precat1 e). rewrite id_right. apply idpath.
  Qed.

  Definition mk_ShortShortExact_isCokernel (SSED : ShortShortExactData A (to_Zero A))
             (H : isCokernel (to_Zero A) (Mor1 SSED) (Mor2 SSED)
                             (ShortShortExactData_Eq (to_Zero A) SSED)) :
    ShortShortExact hs.
  Proof.
    use mk_ShortShortExact.
    - exact SSED.
    - exact (mk_ShortShortExact_isCokernel_isKernel SSED H).
  Defined.

End shortshortexact_iskernel_iscokernel.


(** * [LeftShortExact] (resp. [RightShortExact]) construction for derived functors *)
(** ** Introduction
Let f : A --> B and g : A --> C be morphisms. In this section we construct a right short exact
sequence of the form
                     A --(f · i_1 - g · i_2)--> B ⊕ C --> W --> 0
where B ⊕ C --> W is the coequalizer of f · i_1 and g · i_2. Similarly for left short exact
sequences and equalizers.
 *)
Section left_right_shortexact_and_pullbacks_pushouts.

  Variable A : AbelianPreCat.
  Variable hs : has_homsets A.

  Local Opaque Abelian.Equalizer.
  Local Opaque Abelian.Coequalizer.
  Local Opaque to_BinDirectSums.
  Local Opaque to_binop to_inv.

  (** ** [LeftShortExact] containing an equalizer *)

  Definition LeftShortExact_Equalizer_ShortShortExactData {x1 x2 y : ob A} (f : x1 --> y)
             (g : x2 --> y) : ShortShortExactData A (to_Zero A).
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A hs) x1 x2).
    set (E := Abelian.Equalizer A hs (to_Pr1 _ DS · f) (to_Pr2 _ DS · g)).
    set (PA := (AbelianToAdditive A hs) : PreAdditive).
    use mk_ShortShortExactData.
    - use mk_MorphismPair.
      + exact E.
      + exact DS.
      + exact y.
      + exact (EqualizerArrow E).
      + use (@to_binop PA).
        * exact (to_Pr1 _ DS · f).
        * exact (@to_inv PA _ _ (to_Pr2 _ DS · g)).
    - cbn. exact (AdditiveEqualizerToKernel_eq1 (AbelianToAdditive A hs) _ _ E).
  Defined.

  Definition LeftShortExact_Equalizer_ShortShortExact {x1 x2 y : ob A} (f : x1 --> y)
             (g : x2 --> y) : ShortShortExact hs.
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A hs) x1 x2).
    set (E := Abelian.Equalizer A hs (to_Pr1 _ DS · f) (to_Pr2 _ DS · g)).
    use mk_ShortShortExact.
    - exact (LeftShortExact_Equalizer_ShortShortExactData f g).
    - cbn. cbn in E. fold DS. fold E.
      use mk_ShortShortExact_isKernel_isKernel.
      exact (AdditiveEqualizerToKernel_isKernel (AbelianToAdditive A hs) _ _ E).
  Defined.

  Definition LeftShortExact_Equalizer {x1 x2 y : ob A} (f : x1 --> y) (g : x2 --> y) :
    LeftShortExact hs.
  Proof.
    use mk_LeftShortExact.
    - exact (LeftShortExact_Equalizer_ShortShortExact f g).
    - use EqualizerArrowisMonic.
  Defined.


  (** ** [RightShortExact] containing a coequalizer *)

  Definition RightShortExact_Coequalizer_ShortShortExactData {x y1 y2 : ob A} (f : x --> y1)
             (g : x --> y2) : ShortShortExactData A (to_Zero A).
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A hs) y1 y2).
    set (CE := Abelian.Coequalizer A hs (f · to_In1 _ DS) (g · to_In2 _ DS)).
    set (PA := (AbelianToAdditive A hs) : PreAdditive).
    use mk_ShortShortExactData.
    - use mk_MorphismPair.
      + exact x.
      + exact DS.
      + exact CE.
      + use (@to_binop PA).
        * exact (f · to_In1 _ DS).
        * exact (@to_inv PA _ _ (g · to_In2 _ DS)).
      + exact (CoequalizerArrow CE).
    - cbn. exact (AdditiveCoequalizerToCokernel_eq1 (AbelianToAdditive A hs) _ _ CE).
  Defined.

  Definition RightShortExact_Coequalizer_ShortShortExact {x y1 y2 : ob A} (f : x --> y1)
             (g : x --> y2) : ShortShortExact hs.
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A hs) y1 y2).
    set (CE := Abelian.Coequalizer A hs (f · to_In1 _ DS) (g · to_In2 _ DS)).
    use mk_ShortShortExact.
    - exact (RightShortExact_Coequalizer_ShortShortExactData f g).
    - cbn. cbn in CE. fold DS. fold CE.
      use mk_ShortShortExact_isCokernel_isKernel.
      exact (AdditiveCoequalizerToCokernel_isCokernel (AbelianToAdditive A hs) _ _ CE).
  Defined.

  Definition RightShortExact_Coequalizer {x y1 y2 : ob A} (f : x --> y1) (g : x --> y2) :
    RightShortExact hs.
  Proof.
    use mk_RightShortExact.
    - exact (RightShortExact_Coequalizer_ShortShortExact f g).
    - use CoequalizerArrowisEpi.
  Defined.

End left_right_shortexact_and_pullbacks_pushouts.
