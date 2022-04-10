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

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
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
  Let hs : has_homsets A := homset_property A.

  (** Image of the first morphism and equality of morphisms associated to it. *)
  Definition Image (SSED : ShortShortExactData A (to_Zero A)) :
    Kernel (to_Zero A) (CokernelArrow (Abelian.Cokernel (Mor1 SSED))) := Image (Mor1 SSED).

  Lemma isExact_Eq {x y z : ob A} (f : x --> y) (g : y --> z)
        (H : f · g = ZeroArrow (to_Zero A) _ _) :
    KernelArrow (Abelian.Image f) · g = ZeroArrow (to_Zero A) _ _.
  Proof.
    unfold Abelian.Image.
    set (fact := factorization1 f).
    unfold factorization1_monic in fact. cbn in fact.
    apply (factorization1_is_epi f).
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
    set (fact := factorization2 g).
    unfold factorization2_epi in fact. cbn in fact. unfold Abelian.CoImage in fact.
    apply (factorization2_is_monic g).
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
    set (K := make_Kernel _ _ _ _ iE).
    set (i := iso_from_Kernel_to_Kernel (to_Zero A) K (Abelian.Kernel g)).
    use (is_iso_isEpi A i (pr2 i)). rewrite ZeroArrow_comp_right. rewrite assoc.
    cbn. unfold from_Kernel_to_Kernel. rewrite KernelCommutes.
    use (factorization1_is_epi f). cbn.
    set (tmp := factorization1 f).
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
    use make_isCokernel.
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
    set (CK := make_Cokernel _ _ _ _ iE).
    set (i := iso_from_Cokernel_to_Cokernel (to_Zero A) (Abelian.Cokernel f) CK).
    use (is_iso_isMonic A i (pr2 i)). rewrite ZeroArrow_comp_left. rewrite <- assoc.
    cbn. unfold from_Cokernel_to_Cokernel. rewrite CokernelCommutes.
    use (factorization2_is_monic g). cbn.
    set (tmp := factorization2 g).
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
    use make_isKernel.
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
    use make_isKernel.
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
    use make_isKernel.
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

  Definition make_ShortShortExact (SSED : ShortShortExactData A (to_Zero A))
             (H : isKernel (to_Zero A) (KernelArrow (Image SSED)) (Mor2 SSED) (Image_Eq SSED)) :
    ShortShortExact := tpair _ SSED H.

  (** Accessor functions *)
  Definition ShortShortExact_ShortShortExactData (SSE : ShortShortExact) :
    ShortShortExactData A (to_Zero A) := pr1 SSE.
  Coercion ShortShortExact_ShortShortExactData : ShortShortExact >-> ShortShortExactData.

  Definition ShortShortExact_isKernel (SSE : ShortShortExact) :
    isKernel (to_Zero A) (KernelArrow (Image SSE)) (Mor2 SSE) (Image_Eq SSE) := pr2 SSE.

  Definition ShortShortExact_Kernel (SSE : ShortShortExact) : Kernel (to_Zero A) (Mor2 SSE) :=
    make_Kernel (to_Zero A) (KernelArrow (Image SSE)) (Mor2 SSE) (Image_Eq SSE)
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

  Definition make_LeftShortExact (SSE : ShortShortExact) (isM : isMonic (Mor1 SSE)) :
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

  Definition make_RightShortExact (SSE : ShortShortExact) (isE : isEpi (Mor2 SSE)) :
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

  Definition make_ShortExact (SSE : ShortShortExact) (isM : Monics.isMonic (Mor1 SSE))
             (isE : Epis.isEpi (Mor2 SSE)) : ShortExact := (SSE,,(isM,,isE)).

  (** [LeftShortExact] and [RightShortExact] from [ShortExact] *)
  Definition ShortExact_LeftShortExact (SE : ShortExact) : LeftShortExact.
  Proof.
    use make_LeftShortExact.
    - exact (pr1 SE).
    - exact (dirprod_pr1 (pr2 SE)).
  Defined.
  Coercion ShortExact_LeftShortExact : ShortExact >-> LeftShortExact.

  Definition ShortExact_RightShortExact (SE : ShortExact) : RightShortExact.
  Proof.
    use make_RightShortExact.
    - exact (pr1 SE).
    - exact (dirprod_pr2 (pr2 SE)).
  Defined.
  Coercion ShortExact_RightShortExact : ShortExact >-> RightShortExact.

End def_shortexactseqs.
Arguments Image [A] _.
Arguments Image_Eq [A] _.
Arguments CoImage [A] _.
Arguments CoImage_Eq [A] _.
Arguments make_ShortShortExact [A] _ _.
Arguments ShortShortExact_isKernel [A] _ _ _ _.
Arguments ShortShortExact_Kernel [A] _.
Arguments LeftShortExact _.
Arguments make_LeftShortExact [A] _ _.
Arguments isMonic [A] _ _ _ _ _.
Arguments RightShortExact _.
Arguments make_RightShortExact [A] _ _ .
Arguments isEpi [A] _ _ _ _ _ .
Arguments ShortShortExact _.
Arguments make_ShortShortExact [A] _ _.


(** * [ShortShortExact] criteria
  In this section we show that for [ShortShortExact] a coimage of the second morphism is a cokernel
  of the first morphism and give a way to construct [ShortShortExact] from certain isCokernel. *)
Section shortshortexact_cokernel.

  Variable A : AbelianPreCat.
  Let hs : has_homsets A := homset_property A.


  (** ** [ShortShortExact] implies isCoequalizer.
    Note that in the definition of [ShortShortExact] we use isEqualizer to say that an image of the
    first morphism is a kernel of the second morphism. We show that also the coimage of the second
    morphism is a cokernel of the first morphism. Informally, this follows directly from the fact
    that the opposite category of an abelian category is an abelian category and that taking the
    opposite category twice, we get the same category. *)

  Local Lemma ShortShortExact_isCokernel_eq1 (SSE : ShortShortExact A) (w0 : A)
        (h : A ⟦Ob2 SSE, w0⟧) (H : Mor1 SSE · h = ZeroArrow (to_Zero A) _ _) :
    (KernelArrow (ShortShortExact_Kernel SSE)) · h = ZeroArrow (to_Zero A) _ _.
  Proof.
    apply (factorization1_is_epi (Mor1 SSE)).
    set (tmp := factorization1 (Mor1 SSE)).
    unfold factorization1_epi in tmp.
    unfold factorization1_monic in tmp.
    cbn in tmp. rewrite assoc. unfold ShortShortExact_Kernel.
    cbn. unfold Image. rewrite <- tmp. clear tmp.
    rewrite ZeroArrow_comp_right.
    exact H.
  Qed.

  Local Lemma ShortShortExact_isCokernel_eq2 (SSE : ShortShortExact A) (w0 : A)
        (h : A ⟦Ob2 SSE, w0⟧) (H : Mor1 SSE · h = ZeroArrow (to_Zero A) _ _) :
    KernelArrow (Abelian.Kernel (Mor2 SSE)) · h = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (i := iso_from_Kernel_to_Kernel (to_Zero A) (ShortShortExact_Kernel SSE)
                                        (Abelian.Kernel (Mor2 SSE))).
    set (epi := is_iso_Epi A i (pr2 i)).
    apply (pr2 epi). cbn. rewrite ZeroArrow_comp_right.
    rewrite assoc. unfold from_Kernel_to_Kernel.
    rewrite KernelCommutes.
    apply (ShortShortExact_isCokernel_eq1 SSE w0 h H).
  Qed.

  Local Lemma ShortShortExact_isCokernel (SSE : ShortShortExact A) :
    isCokernel (to_Zero A) (Mor1 SSE) (CokernelArrow (CoImage SSE)) (CoImage_Eq SSE).
  Proof.
    use make_isCokernel.
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

  Definition ShortShortExact_Cokernel (SSE : ShortShortExact A) :
    Cokernel (to_Zero A) (Mor1 SSE) := make_Cokernel (to_Zero A) (Mor1 SSE) (CokernelArrow (CoImage SSE))
                                               (CoImage_Eq SSE)
                                               (ShortShortExact_isCokernel SSE).


  (** ** From isCokernel to [ShortShortExact]
    We show that we can construct [ShortShortExact] from the isCokernel property proved above. *)

  Local Lemma ShortShortExact_from_isCokernel_eq1 (SSED : ShortShortExactData A (to_Zero A))
        (w : A) (h : A ⟦w, Ob2 SSED⟧)
        (H : (h · (CokernelArrow (Abelian.CoImage (Mor2 SSED)))) = ZeroArrow (to_Zero A) _ _)
        (H' : isCokernel (to_Zero A) (Mor1 SSED) (CokernelArrow (CoImage SSED)) (CoImage_Eq SSED)) :
    h · CokernelArrow (Abelian.Cokernel (Mor1 SSED)) = ZeroArrow (to_Zero A) _ _.
  Proof.
    set (coker := make_Cokernel (to_Zero A) (Mor1 SSED) (CokernelArrow (CoImage SSED))
                              (CoImage_Eq SSED) H').
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
                (to_Zero A) (Mor1 SSED) (CokernelArrow (CoImage SSED)) (CoImage_Eq SSED)) :
    h · CokernelArrow (Abelian.CoImage (Mor2 SSED)) = ZeroArrow (to_Zero A) _ _.
  Proof.
    apply (factorization2_is_monic (Mor2 SSED)).
    set (tmp := factorization2 (Mor2 SSED)).
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
               (to_Zero A) (Mor1 SSED) (CokernelArrow (CoImage SSED)) (CoImage_Eq SSED)) :
    isKernel (to_Zero A) (KernelArrow (Image SSED)) (Mor2 SSED) (Image_Eq SSED).
  Proof.
    use make_isKernel.
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
                             (CoImage_Eq SSED)) : ShortShortExact A :=
    make_ShortShortExact SSED (ShortShortExact_from_isCokernel_isKernel SSED H).

End shortshortexact_cokernel.
Arguments ShortShortExact_Cokernel [A] _ .
Arguments ShortShortExact_from_isCokernel [A] _ _.


(** * Correspondence of shortexact in A an A^op *)
Section shortexact_opp.

  Local Opaque ZeroArrow isKernel isCokernel.

  Lemma isExact_opp_Eq {A : AbelianPreCat} {x y z : ob A} {f : x --> y}
        {g : y --> z} (H : f · g = ZeroArrow (to_Zero A) _ _) :
    (g : (Abelian_opp A)⟦_, _⟧) · (f : (Abelian_opp A)⟦_, _⟧) =
    @ZeroArrow (Abelian_opp A) (Zero_opp A (to_Zero A)) _ _.
  Proof.
    cbn. use (pathscomp0 H). use ZeroArrow_opp.
  Qed.

  Unset Kernel Term Sharing.
  Lemma isExact_opp {A : AbelianPreCat} {x y z : ob A} {f : x --> y}
             {g : y --> z} {H : f · g = ZeroArrow (to_Zero A) _ _} (iE : isExact A f g H) :
    isExact (Abelian_opp A) g f (isExact_opp_Eq H).
  Proof.
    unfold isExact.
    use isKernel_opp.
    - exact (to_Zero A).
    - exact (isExact'_Eq A f g H).
    - exact (isExact_to_isExact' A iE).
  Qed.
  Set Kernel Term Sharing.

  Definition ShortShortExact_opp {A : AbelianPreCat}
             (SSE : ShortShortExact A) : ShortShortExact (Abelian_opp A).
  Proof.
    use make_ShortShortExact.
    - exact (ShortShortExactData_opp SSE).
    - cbn. use isKernel_opp.
      + exact (to_Zero A).
      + exact (CoImage_Eq SSE).
      + exact (CokernelisCokernel (to_Zero A) (ShortShortExact_Cokernel SSE)).
  Defined.

  Unset Kernel Term Sharing.
  Local Lemma opp_ShortShortExact_isKernel {A : AbelianPreCat}
        (SSE : ShortShortExact (Abelian_opp A)) :
    isKernel (to_Zero A) (KernelArrow (Image (opp_ShortShortExactData SSE)))
             (Mor2 (opp_ShortShortExactData SSE))
             (Image_Eq (opp_ShortShortExactData SSE)).
  Proof.
    cbn. use opp_isKernel.
    - exact (Zero_opp A (to_Zero A)).
    - exact (CoImage_Eq SSE).
    - exact (@CokernelisCokernel
               (Abelian_opp A) (Zero_opp A (to_Zero A)) _ _ _
               (ShortShortExact_Cokernel SSE)).
  Qed.
  Set Kernel Term Sharing.

  Definition opp_ShortShortExact {A : AbelianPreCat}
             (SSE : ShortShortExact (Abelian_opp A)) : ShortShortExact A.
  Proof.
    use make_ShortShortExact.
    - exact (opp_ShortShortExactData SSE).
    - exact (opp_ShortShortExact_isKernel SSE).
  Defined.

  Definition LeftShortExact_opp {A : AbelianPreCat} (LSE : LeftShortExact A) :
    RightShortExact (Abelian_opp A).
  Proof.
    use make_RightShortExact.
    - exact (ShortShortExact_opp LSE).
    - use isMonic_opp. exact (isMonic LSE).
  Defined.

  Definition opp_LeftShortExact {A : AbelianPreCat}
             (LSE : LeftShortExact (Abelian_opp A)) : RightShortExact A.
  Proof.
    use make_RightShortExact.
    - exact (opp_ShortShortExact LSE).
    - use opp_isMonic. exact (isMonic LSE).
  Defined.

  Definition RightShortExact_opp {A : AbelianPreCat}
             (RSE : RightShortExact A) : LeftShortExact (Abelian_opp A).
  Proof.
    use make_LeftShortExact.
    - exact (ShortShortExact_opp RSE).
    - use isEpi_opp. exact (isEpi RSE).
  Defined.

  Definition opp_RightShortExact {A : AbelianPreCat}
             (RSE : RightShortExact (Abelian_opp A)) : LeftShortExact A.
  Proof.
    use make_LeftShortExact.
    - exact (opp_ShortShortExact RSE).
    - use opp_isEpi. exact (isEpi RSE).
  Defined.

  Definition ShortExact_opp {A : AbelianPreCat} (SE : ShortExact A) :
    ShortExact (Abelian_opp A).
  Proof.
    use make_ShortExact.
    - exact (ShortShortExact_opp SE).
    - use isEpi_opp. exact (isEpi SE).
    - use isMonic_opp. exact (isMonic SE).
  Defined.

  Definition opp_ShortExact {A : AbelianPreCat}
             (SE : ShortExact (Abelian_opp A)) : ShortExact A.
  Proof.
    use make_ShortExact.
    - exact (opp_ShortShortExact SE).
    - use opp_isEpi. exact (isEpi SE).
    - use opp_isMonic. exact (isMonic SE).
  Defined.

End shortexact_opp.


(** * [LeftShortExact] and [RightShortExact] from a [ShortShortExact] with extra properties *)
Section shortshortexact_to_leftshortexact.

  Variable A : AbelianPreCat.

  Definition LeftShortExact_from_ShortShortExact (SSE : ShortShortExact A)
             (isK : isKernel
                      (to_Zero A) (Mor1 SSE) (Mor2 SSE) (ShortShortExactData_Eq (to_Zero A) SSE)) :
    LeftShortExact A.
  Proof.
    use make_LeftShortExact.
    - exact SSE.
    - exact (KernelArrowisMonic _ (make_Kernel _ _ _ _ isK)).
  Defined.

  Definition RightShortExact_from_ShortShortExact (SSE : ShortShortExact A)
             (isCK : isCokernel
                       (to_Zero A) (Mor1 SSE) (Mor2 SSE) (ShortShortExactData_Eq (to_Zero A) SSE)) :
    RightShortExact A.
  Proof.
    use make_RightShortExact.
    - exact SSE.
    - exact (CokernelArrowisEpi _ (make_Cokernel _ _ _ _ isCK)).
  Defined.

End shortshortexact_to_leftshortexact.


(** * Correspondence between [ShortShortExact] and [ShortExact]
  In this section we prove correspondence between [ShortShortExact] and
  [ShortExact]. *)
Section shortexact_correspondence.

  Variable A : AbelianPreCat.


  (** ** Construction of [ShortExact] from [ShortShortExact]
    By using the factorization property of morphisms in abelian categories, we show that we can
    construct a [ShortExact] from [ShortShortExact] in a canonical way. More precisely, such
    [ShortExact] is given by taking the first morphism to be the image of the first morphism of the
    [ShortShortExact] and the second morphism to be the coimage of the second morphism of the
    [ShortShortExact]. *)

  Local Lemma ShortExact_from_ShortShortExact_eq (SSE : ShortShortExact A) :
    (KernelArrow (Abelian.Image (Mor1 SSE))) · (CokernelArrow (Abelian.CoImage (Mor2 SSE))) =
    ZeroArrow (to_Zero A) _ _.
  Proof.
    (* Work on mor1 using factorization *)
    apply (factorization1_is_epi (Mor1 SSE)).
    rewrite assoc.
    set (fact := factorization1 (Mor1 SSE)).
    rewrite ZeroArrow_comp_right.
    unfold factorization1_monic in fact. cbn in fact. rewrite <- fact. clear fact.
    (* Work on mor2 using factorization *)
    apply (factorization2_is_monic (Mor2 SSE)).
    rewrite <- assoc.
    set (fact := factorization2 (Mor2 SSE)).
    unfold factorization2_epi in fact. cbn in fact. rewrite <- fact. clear fact.
    rewrite ZeroArrow_comp_left.
    (* Follows now from the Eq *)
    apply (ShortShortExactData_Eq (to_Zero A) SSE).
  Qed.

  Local Lemma ShortExact_ShortShortExact_isKernel_Eq (SSE : ShortShortExact A) (w : A)
             (h : A ⟦w, Ob2 SSE⟧)
             (H' : h · CokernelArrow (Abelian.CoImage (Mor2 SSE)) = ZeroArrow (to_Zero A) _ _) :
    let Im := Abelian.Image (Mor1 SSE) in
    h · (CokernelArrow (Abelian.Cokernel (KernelArrow Im))) = ZeroArrow (to_Zero A) _ _.
  Proof.
    cbn zeta.
    assert (X : h · Mor2 SSE = ZeroArrow (to_Zero A) _ _).
    {
      rewrite (factorization2 (Mor2 SSE)).
      unfold factorization2_epi. cbn.
      set (tmp := factorization2_monic A (Mor2 SSE)).
      apply (maponpaths (λ h' : _, h' · tmp)) in H'. unfold tmp in H'.
      clear tmp. rewrite ZeroArrow_comp_left in H'. rewrite <- assoc in H'.
      unfold factorization2_monic in H'. cbn in H'.
      exact H'.
    }
    set (comm1 := KernelCommutes (to_Zero A) (Abelian.Kernel (Mor2 SSE)) w h X).
    set (ker := ShortShortExact_Kernel SSE).
    set (tmp := Abelian.Kernel (Mor2 SSE)).
    set (tmp_eq := (KernelCompZero (to_Zero A) tmp)).
    set (comm2 := KernelCommutes (to_Zero A) ker tmp (KernelArrow tmp) tmp_eq).
    unfold tmp in comm2. rewrite <- comm2 in comm1. clear comm2.
    rewrite <- comm1. rewrite <- assoc. rewrite <- assoc.
    rewrite CokernelCompZero. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  Local Lemma ShortExact_ShortShortExact_isKernel (SSE : ShortShortExact A) :
    let Im := Abelian.Image (Mor1 SSE) in
    let CoIm := Abelian.CoImage (Mor2 SSE) in
    let MP := make_MorphismPair (KernelArrow Im) (CokernelArrow CoIm) in
    let SSED := make_ShortShortExactData (to_Zero A) MP (ShortExact_from_ShortShortExact_eq SSE) in
    isKernel (to_Zero A) (KernelArrow (Image SSED)) (CokernelArrow CoIm) (Image_Eq SSED).
  Proof.
    intros Im CoIm MP SSED.
    use make_isKernel.
    intros w h H'.
    use unique_exists.
    (* Construction of the morphism *)
    - use KernelIn.
      + exact h.
      + apply (ShortExact_ShortShortExact_isKernel_Eq SSE w h H').
    (* Commutativity *)
    - apply KernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y. apply homset_property.
    (* Uniqueness *)
    - intros y T. cbn in T. apply KernelInsEq.
      use (pathscomp0 T). apply pathsinv0.
      apply KernelCommutes.
  Qed.

  Definition ShortExact_from_ShortShortExact (SSE : ShortShortExact A) : ShortExact A.
  Proof.
    use make_ShortExact.
    - use make_ShortShortExact.
      + use make_ShortShortExactData.
        * use make_MorphismPair.
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
    set (fact := factorization2 f).
    unfold factorization2_epi in fact. cbn in fact.
    rewrite assoc in fact. rewrite <- fact in tmp. clear fact.
    (* Work of g in tmp *)
    set (fact := factorization1 g).
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
    set (ker := make_Kernel (to_Zero A) (KernelArrow (Abelian.Image f))
                          (CokernelArrow (Abelian.CoImage g)) H isEq).
    (* Rewrite g in H' *)
    set (fact := factorization2 g).
    unfold factorization2_epi in fact. cbn in fact.
    rewrite fact in H'. clear fact.
    (* Use commutativity of ker *)
    rewrite assoc in H'.
    assert (X : h · CokernelArrow (Abelian.CoImage g) = ZeroArrow (to_Zero A) _ _).
    {
      apply (factorization2_is_monic g).
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
    let SSED := make_ShortShortExactData (to_Zero A) (make_MorphismPair f g)
                                       (ShortShortExact_from_isSortExact_eq f g H isK) in
    isKernel (to_Zero A) (KernelArrow (Image SSED)) g (Image_Eq SSED).
  Proof.
    intros SSED.
    use make_isKernel.
    intros w h H'.
    use unique_exists.
    (* Construction of the arrow *)
    - use KernelIn.
      + exact h.
      + exact (ShortShortExact_from_isShortExact_isKernel_eq f g H isK w h H').
    (* Comutativity *)
    - apply KernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y. apply homset_property.
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
    ShortShortExact A.
  Proof.
    use make_ShortShortExact.
    - use make_ShortShortExactData.
      + use make_MorphismPair.
        * exact a.
        * exact b.
        * exact c.
        * exact f.
        * exact g.
      + exact (ShortShortExact_from_isSortExact_eq f g H isEq).
    - exact (ShortShortExact_from_isShortExact_isKernel f g H isEq).
  Defined.

End shortexact_correspondence.
Arguments ShortExact_from_ShortShortExact [A] _ .
Arguments ShortShortExact_from_isShortExact [A] _ _ _ _ _ _ _ .


(** * [ShortShortExact] from isKernel and isCokernel *)
(** ** Introduction
In this section we construct [ShortShortExact] from a pair of morphisms where the first morphism is
the kernel of the second morphisms and where the second morphism is the cokernel of the first
morphism.
 *)
Section shortshortexact_iskernel_iscokernel.

  Variable A : AbelianPreCat.

  Lemma make_ShortShortExact_isKernel_isKernel (SSED : ShortShortExactData A (to_Zero A))
        (H : isKernel
               (to_Zero A) (Mor1 SSED) (Mor2 SSED) (ShortShortExactData_Eq (to_Zero A) SSED)) :
    isKernel (to_Zero A) (KernelArrow (Image SSED)) (Mor2 SSED) (Image_Eq SSED).
  Proof.
    set (K := make_Kernel _ _ _ _ H).
    set (e1 := factorization1 (Mor1 SSED)). cbn in e1. unfold Image.
    assert (e : is_z_isomorphism (CokernelArrow (Abelian.CoImage (Mor1 SSED))
                                                · CoIm_to_Im (Mor1 SSED))).
    {
      use monic_epi_is_iso.
      - use isMonic_postcomp.
        + exact (Ob2 SSED).
        + exact (KernelArrow (Abelian.Image (Mor1 SSED))).
        + rewrite <- e1. use (KernelArrowisMonic (to_Zero A) K).
      - exact (factorization1_is_epi (Mor1 SSED)).
    }
    use Kernel_up_to_iso_isKernel.
    + exact K.
    + exact (z_iso_inv (make_z_iso _ _ e)).
    + apply (maponpaths (λ g : _, (inv_from_z_iso (make_z_iso _ _ e)) · g)) in e1.
      use (pathscomp0 _ (! e1)). clear e1. rewrite assoc.
      cbn. rewrite (is_inverse_in_precat2 e). rewrite id_left. apply idpath.
  Qed.

  Definition make_ShortShortExact_isKernel (SSED : ShortShortExactData A (to_Zero A))
             (H : isKernel (to_Zero A) (Mor1 SSED) (Mor2 SSED)
                           (ShortShortExactData_Eq (to_Zero A) SSED)) :
    ShortShortExact A.
  Proof.
    use make_ShortShortExact.
    - exact SSED.
    - exact (make_ShortShortExact_isKernel_isKernel SSED H).
  Defined.

  Lemma make_ShortShortExact_isCokernel_isKernel (SSED : ShortShortExactData A (to_Zero A))
        (H : isCokernel
               (to_Zero A) (Mor1 SSED) (Mor2 SSED) (ShortShortExactData_Eq (to_Zero A) SSED)) :
    isKernel (to_Zero A) (KernelArrow (Image SSED)) (Mor2 SSED) (Image_Eq SSED).
  Proof.
    use ShortShortExact_from_isCokernel_isKernel.
    set (CK := make_Cokernel _ _ _ _ H).
    set (e1 := factorization2 (Mor2 SSED)). cbn in e1. unfold CoImage.
    assert (e : is_z_isomorphism (CoIm_to_Im (Mor2 SSED)
                                             · KernelArrow (Abelian.Image (Mor2 SSED)))).
    {
      use monic_epi_is_iso.
      - exact (factorization2_is_monic (Mor2 SSED)).
      - use isEpi_precomp.
        + exact (Ob2 SSED).
        + exact (CokernelArrow (Abelian.CoImage (Mor2 SSED))).
        + rewrite <- e1. use (CokernelArrowisEpi (to_Zero A) CK).
    }
    use Cokernel_up_to_iso_isCokernel.
    + exact CK.
    + exact (z_iso_inv (make_z_iso _ _ e)).
    + apply (maponpaths (λ g : _, g · (inv_from_z_iso (make_z_iso _ _ e)))) in e1.
      use (pathscomp0 _ (! e1)). clear e1. rewrite <- assoc. cbn.
      rewrite (is_inverse_in_precat1 e). rewrite id_right. apply idpath.
  Qed.

  Definition make_ShortShortExact_isCokernel (SSED : ShortShortExactData A (to_Zero A))
             (H : isCokernel (to_Zero A) (Mor1 SSED) (Mor2 SSED)
                             (ShortShortExactData_Eq (to_Zero A) SSED)) :
    ShortShortExact A.
  Proof.
    use make_ShortShortExact.
    - exact SSED.
    - exact (make_ShortShortExact_isCokernel_isKernel SSED H).
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

  Local Opaque Abelian.Equalizer.
  Local Opaque Abelian.Coequalizer.
  Local Opaque to_BinDirectSums.
  Local Opaque to_binop to_inv.

  (** ** [LeftShortExact] containing an equalizer *)

  Definition LeftShortExact_Equalizer_ShortShortExactData {x1 x2 y : ob A} (f : x1 --> y)
             (g : x2 --> y) : ShortShortExactData A (to_Zero A).
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A) x1 x2).
    set (E := Abelian.Equalizer A (to_Pr1 DS · f) (to_Pr2 DS · g)).
    set (PA := (AbelianToAdditive A) : PreAdditive).
    use make_ShortShortExactData.
    - use make_MorphismPair.
      + exact E.
      + exact DS.
      + exact y.
      + exact (EqualizerArrow E).
      + use (@to_binop PA).
        * exact (to_Pr1 DS · f).
        * exact (@to_inv PA _ _ (to_Pr2 DS · g)).
    - cbn. exact (AdditiveEqualizerToKernel_eq1 (AbelianToAdditive A) _ _ E).
  Defined.

  Definition LeftShortExact_Equalizer_ShortShortExact {x1 x2 y : ob A} (f : x1 --> y)
             (g : x2 --> y) : ShortShortExact A.
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A) x1 x2).
    set (E := Abelian.Equalizer A (to_Pr1 DS · f) (to_Pr2 DS · g)).
    use make_ShortShortExact.
    - exact (LeftShortExact_Equalizer_ShortShortExactData f g).
    - cbn. cbn in E. fold DS. fold E.
      use make_ShortShortExact_isKernel_isKernel.
      exact (AdditiveEqualizerToKernel_isKernel (AbelianToAdditive A) _ _ E).
  Defined.

  Definition LeftShortExact_Equalizer {x1 x2 y : ob A} (f : x1 --> y) (g : x2 --> y) :
    LeftShortExact A.
  Proof.
    use make_LeftShortExact.
    - exact (LeftShortExact_Equalizer_ShortShortExact f g).
    - use EqualizerArrowisMonic.
  Defined.


  (** ** [RightShortExact] containing a coequalizer *)

  Definition RightShortExact_Coequalizer_ShortShortExactData {x y1 y2 : ob A} (f : x --> y1)
             (g : x --> y2) : ShortShortExactData A (to_Zero A).
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A) y1 y2).
    set (CE := Abelian.Coequalizer A (f · to_In1 DS) (g · to_In2 DS)).
    set (PA := (AbelianToAdditive A) : PreAdditive).
    use make_ShortShortExactData.
    - use make_MorphismPair.
      + exact x.
      + exact DS.
      + exact CE.
      + use (@to_binop PA).
        * exact (f · to_In1 DS).
        * exact (@to_inv PA _ _ (g · to_In2 DS)).
      + exact (CoequalizerArrow CE).
    - cbn. exact (AdditiveCoequalizerToCokernel_eq1 (AbelianToAdditive A) _ _ CE).
  Defined.

  Definition RightShortExact_Coequalizer_ShortShortExact {x y1 y2 : ob A} (f : x --> y1)
             (g : x --> y2) : ShortShortExact A.
  Proof.
    set (DS := to_BinDirectSums (AbelianToAdditive A) y1 y2).
    set (CE := Abelian.Coequalizer A (f · to_In1 DS) (g · to_In2 DS)).
    use make_ShortShortExact.
    - exact (RightShortExact_Coequalizer_ShortShortExactData f g).
    - cbn. cbn in CE. fold DS. fold CE.
      use make_ShortShortExact_isCokernel_isKernel.
      exact (AdditiveCoequalizerToCokernel_isCokernel (AbelianToAdditive A) _ _ CE).
  Defined.

  Definition RightShortExact_Coequalizer {x y1 y2 : ob A} (f : x --> y1) (g : x --> y2) :
    RightShortExact A.
  Proof.
    use make_RightShortExact.
    - exact (RightShortExact_Coequalizer_ShortShortExact f g).
    - use CoequalizerArrowisEpi.
  Defined.

End left_right_shortexact_and_pullbacks_pushouts.
