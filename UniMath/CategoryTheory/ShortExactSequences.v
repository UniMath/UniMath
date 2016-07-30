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
  Short exact sequences consist of three objects and two morphisms such that the
  first morphism is a monic, the second morphism is an epi, and an image of
  the first morphism gives a kernel of the second morphism. These sequences are
  classically denoted by a diagram
                           0 -> A -> B -> C -> 0
  We call such diagrams [ShortExact].

  To define short exact sequences we first define short short exact sequences,
  [ShortShortExact], left short exact sequences, [LeftShortExact], and
  right short exact sequences, [RightShortExact]. These correspond
  to the diagrams
          A -> B -> C,  0 -> A -> B -> C,  and,  A -> B -> C -> 0,
  respectively.

  The definition of [ShortShortExact] says that the image of A -> B is the
  kernel of B -> C. This is equivalent to saying that the coimage of B -> C is
  the cokernel of A -> B. We prove this correspondence in the Section
  [shortshortexact_coequalizer].

    Next, in the section [shortexact_correspondence] we prove a correspondence
  between [ShortShortExact] and [ShortExact] by using the factorization
  formula for morphisms in abelian precategories. We construct [ShortExact]
  from [ShortShortExact] and we give a criteria to construct
  [ShortShortExact] from properties similar to [ShortExact]. *)

(** * Definition of short exact sequences *)
Section def_shortexactseqs.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.

  (** Image of the first morphism and equality of morphisms associated to it. *)
  Definition ShortShortExactData_Im
             (SSED : ShortShortExactData A (Abelian_Zero A)) :
    Kernel (Abelian_Zero A)
           (CokernelArrow
              (Abelian_Zero A)
              (Abelian_Cokernel
                 A (MorphismPairMor1
                      A (ShortShortExactData_MorphismPair
                           A (Abelian_Zero A) SSED))))
    :=  Abelian_Im
          A (MorphismPairMor1 A (ShortShortExactData_MorphismPair
                                   A (Abelian_Zero A) SSED)).

  Lemma ShortShortExactData_Im_Eq
        (SSED : ShortShortExactData A (Abelian_Zero A)) :
    (KernelArrow (Abelian_Zero A) (ShortShortExactData_Im SSED))
      ;; (MorphismPairMor2
            A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))
    = ZeroArrow A (Abelian_Zero A) _ _.
  Proof.
    unfold ShortShortExactData_Im.
    set (fact := Abelian_factorization1
                   A hs
                   (MorphismPairMor1
                      A (ShortShortExactData_MorphismPair
                           A (Abelian_Zero A) SSED))).
    unfold Abelian_factorization1_monic in fact. cbn in fact.
    apply (Abelian_factorization1_is_epi
             A hs
             (MorphismPairMor1
                A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))).
    rewrite ZeroArrow_comp_right.
    rewrite assoc. rewrite <- fact.
    apply (ShortShortExactData_Eq A (Abelian_Zero A) SSED).
  Qed.

  (** Coimage of the second morphism and equality of morphisms associated
    to it. *)
  Definition ShortShortExactData_CoIm
             (SSED : ShortShortExactData A (Abelian_Zero A)) :
    Cokernel (Abelian_Zero A)
             (KernelArrow
                (Abelian_Zero A)
                (Abelian_Kernel
                   A (MorphismPairMor2
                        A (ShortShortExactData_MorphismPair
                             A (Abelian_Zero A) SSED))))
    :=  Abelian_CoIm
          A (MorphismPairMor2 A (ShortShortExactData_MorphismPair
                                   A (Abelian_Zero A) SSED)).

  Lemma ShortShortExactData_CoIm_Eq
        (SSED : ShortShortExactData A (Abelian_Zero A)) :
    (MorphismPairMor1
       A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))
      ;; (CokernelArrow (Abelian_Zero A) (ShortShortExactData_CoIm SSED))
    = ZeroArrow A (Abelian_Zero A) _ _.
  Proof.
    unfold ShortShortExactData_CoIm.
    set (fact := Abelian_factorization2
                   A hs
                   (MorphismPairMor2
                      A (ShortShortExactData_MorphismPair
                           A (Abelian_Zero A) SSED))).
    unfold Abelian_factorization2_epi in fact. cbn in fact.
    apply (Abelian_factorization2_is_monic
             A hs
             (MorphismPairMor2
                A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))).
    rewrite ZeroArrow_comp_left.
    rewrite <- assoc. rewrite <- fact.
    apply (ShortShortExactData_Eq A (Abelian_Zero A) SSED).
  Qed.


  (** ** [Short Short Exact]
    [ShortShortData] such that the image of the first morphism is the kernel
    of the second morphism. Informally, an exact sequence
                               A -> B -> C
  *)

  Definition ShortShortExact : UU
    := Σ SSED : ShortShortExactData A (Abelian_Zero A),
                isEqualizer (MorphismPairMor2
                               A (ShortShortExactData_MorphismPair
                                    A (Abelian_Zero A) SSED))
                            (ZeroArrow A (Abelian_Zero A) _ _)
                            (KernelArrow (Abelian_Zero A)
                                         (ShortShortExactData_Im SSED))
                            (KernelEqRw
                               (Abelian_Zero A)
                               (ShortShortExactData_Im_Eq SSED)).
  Definition mk_ShortShortExact (SSED : ShortShortExactData A (Abelian_Zero A))
             (H : isEqualizer (MorphismPairMor2
                                 A (ShortShortExactData_MorphismPair
                                      A (Abelian_Zero A) SSED))
                              (ZeroArrow A (Abelian_Zero A) _ _)
                              (KernelArrow (Abelian_Zero A)
                                           (ShortShortExactData_Im SSED))
                              (KernelEqRw
                                (Abelian_Zero A)
                                (ShortShortExactData_Im_Eq SSED)))  :
    ShortShortExact.
  Proof.
    use tpair.
    - exact SSED.
    - exact H.
  Defined.

  (* Accessor functions *)
  Definition ShortShortExact_ShortShortExactData (SSE : ShortShortExact) :
    ShortShortExactData A (Abelian_Zero A) := pr1 SSE.
  Definition ShortShortExact_isEqualizer (SSE : ShortShortExact) :
    isEqualizer (MorphismPairMor2
                   A (ShortShortExactData_MorphismPair
                        A (Abelian_Zero A)
                        (ShortShortExact_ShortShortExactData SSE)))
                (ZeroArrow A (Abelian_Zero A) _ _)
                (KernelArrow (Abelian_Zero A)
                             (ShortShortExactData_Im
                                (ShortShortExact_ShortShortExactData SSE)))
                (KernelEqRw
                   (Abelian_Zero A)
                   (ShortShortExactData_Im_Eq
                      (ShortShortExact_ShortShortExactData SSE)))
    := pr2 SSE.
  Definition ShortShortExact_Kernel (SSE : ShortShortExact) :
    Kernel (Abelian_Zero A)
         (MorphismPairMor2
            A (ShortShortExactData_MorphismPair
                 A (Abelian_Zero A)
                 (ShortShortExact_ShortShortExactData SSE)))
    := mk_Kernel
         (Abelian_Zero A)
         (KernelArrow (Abelian_Zero A)
                      (ShortShortExactData_Im
                         (ShortShortExact_ShortShortExactData SSE)))
         (MorphismPairMor2
            A (ShortShortExactData_MorphismPair
                 A (Abelian_Zero A)
                 (ShortShortExact_ShortShortExactData SSE)))
         (ShortShortExactData_Im_Eq
            (ShortShortExact_ShortShortExactData SSE))
         (ShortShortExact_isEqualizer SSE).

  (** ** Remark
    In Abelian.v we have already shown that a morphism is a monic if and only if
    its kernel is zero, and dually is an epi if and only if its cokernel is
    zero. See the results
    - Abelian_MonicKernelZero_isEqualizer, Abelian_MonicKernelZero
    - Abelian_EpiCokernelZero_isCoequalizer, Abelian_EpiCokernelZero
    - Abelian_KernelZeroisMonic, Abelian_KernelZeroMonic
    - Abelian_CokernelZeroisEpi, Abelian_CokernelZeroEpi
   in CategoryTheory/Abelian.v. Thus, to define short exact sequeces, it
   suffices to assume that the first morphism is a monic and the second
   morphism is an epi. Similarly for left short exact and right short exact.
   *)

  (** ** [LeftShortExact]
    [ShortShortExact] such that the first morphism is a monic. Informally,
    an exact sequence
                            0 -> A -> B -> C
  *)

  Definition LeftShortExact : UU
    := Σ SSE : ShortShortExact,
               isMonic A (MorphismPairMor1
                            A (ShortShortExactData_MorphismPair
                                 A (Abelian_Zero A)
                                 (ShortShortExact_ShortShortExactData SSE))).
  Definition mk_LeftShortExact (SSE : ShortShortExact)
             (isM : isMonic
                      A (MorphismPairMor1
                           A (ShortShortExactData_MorphismPair
                                A (Abelian_Zero A)
                                (ShortShortExact_ShortShortExactData SSE)))) :
    LeftShortExact.
  Proof.
    use tpair.
    - exact SSE.
    - exact isM.
  Defined.

  (** Accessor functions *)
  Definition LeftShortExact_ShortShortExact (LSE : LeftShortExact) :
    ShortShortExact := pr1 LSE.
  Definition LeftShortExact_isMonic (LSE : LeftShortExact) :
    isMonic A (MorphismPairMor1
                 A (ShortShortExactData_MorphismPair
                      A (Abelian_Zero A)
                      (ShortShortExact_ShortShortExactData
                         (LeftShortExact_ShortShortExact LSE))))
    := pr2 LSE.

  (** ** [RightShortExact]
    [ShortShortExact] such that the second morphism is an epi. Informally, an
    exact sequece
                               A -> B -> C -> 0
   *)

  Definition RightShortExact : UU
    := Σ SSE : ShortShortExact,
               isEpi A (MorphismPairMor2
                          A (ShortShortExactData_MorphismPair
                               A (Abelian_Zero A)
                               (ShortShortExact_ShortShortExactData SSE))).
  Definition mk_RightShortExact (SSE : ShortShortExact)
             (isE : isEpi
                      A (MorphismPairMor2
                           A (ShortShortExactData_MorphismPair
                                A (Abelian_Zero A)
                                (ShortShortExact_ShortShortExactData SSE)))) :
    RightShortExact.
  Proof.
    use tpair.
    - exact SSE.
    - exact isE.
  Defined.

  (** Accessor functions *)
  Definition RightShortExact_ShortShortExact (RSE : RightShortExact) :
    ShortShortExact := pr1 RSE.
  Definition RightShortExact_isEpi (RSE : RightShortExact) :
    isEpi A (MorphismPairMor2
               A (ShortShortExactData_MorphismPair
                    A (Abelian_Zero A)
                    (ShortShortExact_ShortShortExactData
                       (RightShortExact_ShortShortExact RSE))))
    := pr2 RSE.

  (** ** [ShortExact]
    [ShortShortExact] such that the first morphism is monic and the second
    morphism is an epi. Informally, an exact sequece
                            0 -> A -> B -> C -> 0
  *)

  Definition ShortExact : UU
    := Σ SSE : ShortShortExact,
               isMonic
                 A (MorphismPairMor1
                      A (ShortShortExactData_MorphismPair
                           A (Abelian_Zero A)
                           (ShortShortExact_ShortShortExactData SSE)))
                 × isEpi A (MorphismPairMor2
                              A (ShortShortExactData_MorphismPair
                                   A (Abelian_Zero A)
                                   (ShortShortExact_ShortShortExactData SSE))).
  Definition mk_ShortExact (SSE : ShortShortExact)
             (isM : isMonic
                      A (MorphismPairMor1
                           A (ShortShortExactData_MorphismPair
                                A (Abelian_Zero A)
                                (ShortShortExact_ShortShortExactData SSE))))
             (isE : isEpi
                      A (MorphismPairMor2
                           A (ShortShortExactData_MorphismPair
                                A (Abelian_Zero A)
                                (ShortShortExact_ShortShortExactData SSE)))) :
    ShortExact.
  Proof.
    use tpair.
    - exact SSE.
    - use tpair.
      + exact isM.
      + exact isE.
  Defined.

  (** Accessor functions *)
  Definition ShortExact_ShortShortExact (SE : ShortExact) : ShortShortExact
    := pr1 SE.
  Definition ShortExact_isMonic (SE : ShortExact) :
    isMonic A (MorphismPairMor1
                 A (ShortShortExactData_MorphismPair
                      A (Abelian_Zero A)
                      (ShortShortExact_ShortShortExactData
                         (ShortExact_ShortShortExact SE))))
    := pr1 (pr2 SE).
  Definition ShortExact_isEpi (SE : ShortExact) :
    isEpi A (MorphismPairMor2
               A (ShortShortExactData_MorphismPair
                    A (Abelian_Zero A)
                    (ShortShortExact_ShortShortExactData
                       (ShortExact_ShortShortExact SE))))
    := pr2 (pr2 SE).

  (** [LeftShortExact] and [RightShortExact] from [ShortExact] *)
  Definition ShortExact_LeftShortExact (SE : ShortExact) : LeftShortExact.
  Proof.
    use mk_LeftShortExact.
    - exact (ShortExact_ShortShortExact SE).
    - exact (ShortExact_isMonic SE).
  Defined.

  Definition ShortExact_RightShortExact (SE : ShortExact) : RightShortExact.
  Proof.
    use mk_RightShortExact.
    - exact (ShortExact_ShortShortExact SE).
    - exact (ShortExact_isEpi SE).
  Defined.

End def_shortexactseqs.


(** * [ShortShortExact] criteria
  In this section we show that for [ShortShortExact] a coimage of the second
  morphism is a cokernel of the first morphism and give a way to construct
  [ShortShortExact] from certain isCoequalizer. *)
Section shortshortexact_coequalizer.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.


  (** ** [ShortShortExact] implies isCoequalizer.
    Note that in the definition of [ShortShortExact] we use isEqualizer to say
    that an image of the first morphism is a kernel of the second morphism.
    We show that also the coimage of the second morphism is a cokernel of the
    first morphism. Informally, this follows directly from the fact that
    the opposite category of an abelian category is an abelian category and that
    taking the opposite category twice, we get the same category. *)

  Lemma ShortShortExact_isCoequalizer_eq1 (SSE : ShortShortExact A hs)
        (w0 : A)
        (h : A ⟦MorphismPairOb2
                  A (ShortShortExactData_MorphismPair
                       A (Abelian_Zero A)
                       (ShortShortExact_ShortShortExactData A hs SSE)), w0⟧)
        (H : MorphismPairMor1
               A (ShortShortExactData_MorphismPair
                    A (Abelian_Zero A)
                    (ShortShortExact_ShortShortExactData A hs SSE)) ;; h
             = (ZeroArrow A (Abelian_Zero A) _ _) ;; h) :
    (KernelArrow
       (Abelian_Zero A)
       (ShortShortExact_Kernel A hs SSE))
      ;; h
    = ZeroArrow A (Abelian_Zero A) _ _.
  Proof.
    apply (Abelian_factorization1_is_epi
             A hs
             (MorphismPairMor1
                A (ShortShortExactData_MorphismPair
                     A (Abelian_Zero A)
                     (ShortShortExact_ShortShortExactData A hs SSE)))).
    set (tmp := Abelian_factorization1
                  A hs
                  (MorphismPairMor1
                     A (ShortShortExactData_MorphismPair
                          A (Abelian_Zero A)
                          (ShortShortExact_ShortShortExactData A hs SSE)))).
    unfold Abelian_factorization1_epi in tmp.
    unfold Abelian_factorization1_monic in tmp.
    cbn in tmp. rewrite assoc. unfold ShortShortExact_Kernel.
    cbn. unfold ShortShortExactData_Im. rewrite <- tmp. clear tmp.
    rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_left in H.
    exact H.
  Qed.

  Lemma ShortShortExact_isCoequalizer_eq2 (SSE : ShortShortExact A hs)
        (w0 : A)
        (h : A ⟦MorphismPairOb2
                  A (ShortShortExactData_MorphismPair
                       A (Abelian_Zero A)
                       (ShortShortExact_ShortShortExactData A hs SSE)), w0⟧)
        (H : MorphismPairMor1
               A (ShortShortExactData_MorphismPair
                    A (Abelian_Zero A)
                    (ShortShortExact_ShortShortExactData A hs SSE)) ;; h =
             (ZeroArrow A (Abelian_Zero A) _ _) ;; h) :
    KernelArrow (Abelian_Zero A)
                (Abelian_Kernel
                   A (MorphismPairMor2
                        A (ShortShortExactData_MorphismPair
                             A (Abelian_Zero A)
                             (ShortShortExact_ShortShortExactData A hs SSE))))
                ;; h
    = ZeroArrow A (Abelian_Zero A) _ _.
  Proof.
    set (i := iso_from_Kernel_to_Kernel
                (Abelian_Zero A)
                (ShortShortExact_Kernel A hs SSE)
                (Abelian_Kernel
                   A (MorphismPairMor2
                        A (ShortShortExactData_MorphismPair
                             A (Abelian_Zero A)
                             (ShortShortExact_ShortShortExactData A hs SSE))))).
    set (epi := iso_Epi A i (pr2 i)).
    apply (pr2 epi). cbn. rewrite ZeroArrow_comp_right.
    rewrite assoc. unfold from_Kernel_to_Kernel.
    rewrite KernelCommutes.
    apply (ShortShortExact_isCoequalizer_eq1 SSE w0 h H).
  Qed.

  Definition ShortShortExact_isCoequalizer (SSE : ShortShortExact A hs) :
    isCoequalizer (MorphismPairMor1
                     A (ShortShortExactData_MorphismPair
                          A (Abelian_Zero A)
                          (ShortShortExact_ShortShortExactData A hs SSE)))
                  (ZeroArrow A (Abelian_Zero A) _ _)
                  (CokernelArrow
                     (Abelian_Zero A)
                     (ShortShortExactData_CoIm
                        A (ShortShortExact_ShortShortExactData A hs SSE)))
                  (CokernelEqRw
                     (Abelian_Zero A)
                     (ShortShortExactData_CoIm_Eq
                        A hs (ShortShortExact_ShortShortExactData A hs SSE))).
  Proof.
    use mk_isCoequalizer.
    intros w0 h H'.
    use unique_exists.

    (* Construction of the morphism *)
    - apply (CokernelOut
               (Abelian_Zero A)
               (ShortShortExactData_CoIm
                  A (ShortShortExact_ShortShortExactData A hs SSE))
               w0 h
               (ShortShortExact_isCoequalizer_eq2 SSE w0 h H')).

    (* Commutativity *)
    - cbn. apply CokernelCommutes.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. cbn in T.
      apply CokernelOutsEq.
      rewrite T. apply pathsinv0.
      apply CokernelCommutes.
  Qed.

  Definition ShortShortExact_Coequalizer (SSE : ShortShortExact A hs) :
    Cokernel (Abelian_Zero A)
             (MorphismPairMor1
                A (ShortShortExactData_MorphismPair
                     A (Abelian_Zero A)
                     (ShortShortExact_ShortShortExactData A hs SSE)))
    := mk_Cokernel
         (Abelian_Zero A)
         (CokernelArrow (Abelian_Zero A)
                        (ShortShortExactData_CoIm
                           A (ShortShortExact_ShortShortExactData A hs SSE)))
         (MorphismPairMor1
            A (ShortShortExactData_MorphismPair
                 A (Abelian_Zero A)
                 (ShortShortExact_ShortShortExactData A hs SSE)))
         (ShortShortExactData_CoIm_Eq
            A hs (ShortShortExact_ShortShortExactData A hs SSE))
         (ShortShortExact_isCoequalizer SSE).


  (** ** From isCoequalizer to [ShortShortExact]
    We show that we can construct [ShortShortExact] from the isCoequalizer
    property proved above. *)


  Lemma ShortShortExact_from_isCoequalizer_eq1
        (SSED : ShortShortExactData A (Abelian_Zero A))
        (w : A)
        (h : A ⟦w, MorphismPairOb2
                     A (ShortShortExactData_MorphismPair
                          A (Abelian_Zero A) SSED)⟧)
        (H : h ;; (CokernelArrow
                     (Abelian_Zero A)
                     (Abelian_CoIm A (MorphismPairMor2
                                        A (ShortShortExactData_MorphismPair
                                             A (Abelian_Zero A) SSED))))
             = ZeroArrow A (Abelian_Zero A) _ _)
        (H' : isCoequalizer
                (MorphismPairMor1
                   A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))
                (ZeroArrow A (Abelian_Zero A) _ _)
                (CokernelArrow
                   (Abelian_Zero A)
                   (ShortShortExactData_CoIm A SSED))
                (CokernelEqRw
                   (Abelian_Zero A)
                   (ShortShortExactData_CoIm_Eq A hs SSED))):
    h ;; CokernelArrow (Abelian_Zero A)
      (Abelian_Cokernel
         A (MorphismPairMor1 A (ShortShortExactData_MorphismPair
                                  A (Abelian_Zero A) SSED)))
    = ZeroArrow A (Abelian_Zero A) _ _.
  Proof.
    set (coker
         := mk_Cokernel
              (Abelian_Zero A)
              (CokernelArrow (Abelian_Zero A)
                             (ShortShortExactData_CoIm A SSED))
              (MorphismPairMor1
                 A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))
              (ShortShortExactData_CoIm_Eq A hs SSED)
              H').
    set (i := iso_from_Cokernel_to_Cokernel
                (Abelian_Zero A)
                (Abelian_Cokernel
                   A (MorphismPairMor1
                        A (ShortShortExactData_MorphismPair
                             A (Abelian_Zero A) SSED)))
                coker).
    set (isM := iso_Monic A i (pr2 i)). apply (pr2 isM). cbn.
    rewrite ZeroArrow_comp_left. rewrite <- assoc.
    unfold from_Cokernel_to_Cokernel.
    rewrite CokernelCommutes.
    unfold coker. cbn. unfold ShortShortExactData_CoIm.
    exact H.
  Qed.

  Lemma ShortShortExact_from_isCoequalizer_eq2
        (SSED : ShortShortExactData A (Abelian_Zero A))
        (w : A)
        (h : A ⟦w, MorphismPairOb2
                     A (ShortShortExactData_MorphismPair
                          A (Abelian_Zero A) SSED)⟧)
        (H : h ;; MorphismPairMor2 A (ShortShortExactData_MorphismPair
                                        A (Abelian_Zero A) SSED)
             = h ;; (ZeroArrow A (Abelian_Zero A) _ _))
        (H' : isCoequalizer
                (MorphismPairMor1
                   A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))
                (ZeroArrow A (Abelian_Zero A) _ _)
                (CokernelArrow
                   (Abelian_Zero A)
                   (ShortShortExactData_CoIm A SSED))
                (CokernelEqRw
                   (Abelian_Zero A)
                   (ShortShortExactData_CoIm_Eq A hs SSED))):
    h ;; CokernelArrow (Abelian_Zero A)
      (Abelian_CoIm A (MorphismPairMor2 A (ShortShortExactData_MorphismPair
                                             A (Abelian_Zero A) SSED)))
    = ZeroArrow A (Abelian_Zero A) _ _.
  Proof.
    apply (Abelian_factorization2_is_monic
             A hs
             (MorphismPairMor2
                A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))).
    set (tmp := Abelian_factorization2
                  A hs
                  (MorphismPairMor2
                     A (ShortShortExactData_MorphismPair
                          A (Abelian_Zero A) SSED))).
    unfold Abelian_factorization2_epi in tmp.
    unfold Abelian_factorization2_monic in tmp.
    cbn in tmp. rewrite <- assoc. rewrite <- tmp.
    clear tmp.
    rewrite ZeroArrow_comp_left.
    rewrite ZeroArrow_comp_right in H.
    exact H.
  Qed.

  Lemma ShortShortExact_from_isCoequalizer_isEqualizer
        (SSED : ShortShortExactData A (Abelian_Zero A))
        (H : isCoequalizer
                (MorphismPairMor1
                   A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))
                (ZeroArrow A (Abelian_Zero A) _ _)
                (CokernelArrow
                   (Abelian_Zero A)
                   (ShortShortExactData_CoIm A SSED))
                (CokernelEqRw
                   (Abelian_Zero A)
                   (ShortShortExactData_CoIm_Eq A hs SSED))) :
    isEqualizer (MorphismPairMor2
                   A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))
                (ZeroArrow A (Abelian_Zero A) _ _)
                (KernelArrow
                   (Abelian_Zero A)
                   (ShortShortExactData_Im A SSED))
                (KernelEqRw
                   (Abelian_Zero A)
                   (ShortShortExactData_Im_Eq A hs SSED)).
  Proof.
    set (coker
         := mk_Cokernel
              (Abelian_Zero A)
              (CokernelArrow (Abelian_Zero A)
                             (ShortShortExactData_CoIm A SSED))
              (MorphismPairMor1
                 A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))
              (ShortShortExactData_CoIm_Eq A hs SSED)
              H).

    use mk_isEqualizer.
    intros w h H'.
    use unique_exists.

    (* Construction of the morphism *)
    - apply (KernelIn
               (Abelian_Zero A)
               (ShortShortExactData_Im A SSED)
               w h
               (ShortShortExact_from_isCoequalizer_eq1
                  SSED w h
                  (ShortShortExact_from_isCoequalizer_eq2 SSED w h H' H)
                  H)).

    (* Commutativity *)
    - cbn. apply KernelCommutes.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. cbn in T.
      apply KernelInsEq.
      rewrite T. apply pathsinv0.
      apply KernelCommutes.
  Qed.

  Definition ShortShortExact_from_isCoequalizer
             (SSED : ShortShortExactData A (Abelian_Zero A))
    (H : isCoequalizer
           (MorphismPairMor1
              A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))
           (ZeroArrow A (Abelian_Zero A) _ _)
           (CokernelArrow
              (Abelian_Zero A)
              (ShortShortExactData_CoIm A SSED))
           (CokernelEqRw
              (Abelian_Zero A)
              (ShortShortExactData_CoIm_Eq A hs SSED))) :
    ShortShortExact A hs
    := mk_ShortShortExact
         A hs SSED (ShortShortExact_from_isCoequalizer_isEqualizer SSED H).

End shortshortexact_coequalizer.


(** * Correspondence between [ShortShortExact] and [ShortExact]
  In this section we prove correspondence between [ShortShortExact] and
  [ShortExact]. *)
Section shortexact_correspondence.

  Variable A : Abelian_precategory.
  Hypothesis hs : has_homsets A.


  (** ** Construction of [ShortExact] from [ShortShortExact]
    By using the factorization property of morphisms in abelian categories, we
    show that we can construct a [ShortExact] from [ShortShortExact] in a
    canonical way. More precisely, such [ShortExact] is given by taking the
    first morphism to be the image of the first morphism of the
    [ShortShortExact] and the second morphism to be the coimage of the second
    morphism of the [ShortShortExact]. *)

  Lemma ShortExact_from_ShortShortExact_eq (SSE : ShortShortExact A hs) :
    (KernelArrow
       (Abelian_Zero A)
       (Abelian_Im
          A (MorphismPairMor1
               A (ShortShortExactData_MorphismPair
                    A (Abelian_Zero A)
                    (ShortShortExact_ShortShortExactData A hs SSE)))))
      ;; (CokernelArrow
            (Abelian_Zero A)
            (Abelian_CoIm
               A (MorphismPairMor2
                    A (ShortShortExactData_MorphismPair
                         A (Abelian_Zero A)
                         (ShortShortExact_ShortShortExactData A hs SSE)))))
    = ZeroArrow A (Abelian_Zero A) _ _.
  Proof.
    set (SSED := ShortShortExact_ShortShortExactData A hs SSE).
    set (SSED_Eq := ShortShortExactData_Eq A (Abelian_Zero A) SSED).
    set (MP := ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED).
    set (mor1 := MorphismPairMor1 A MP).
    set (mor2 := MorphismPairMor2 A MP).

    (* Work on mor1 using factorization *)
    apply (Abelian_factorization1_is_epi
             A hs
             (MorphismPairMor1
                A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))).
    rewrite assoc.
    set (fact := Abelian_factorization1
                   A hs
                   (MorphismPairMor1
                      A (ShortShortExactData_MorphismPair
                           A (Abelian_Zero A) SSED))).
    rewrite ZeroArrow_comp_right.
    unfold Abelian_factorization1_monic in fact. cbn in fact.
    unfold mor1. unfold MP. rewrite <- fact. clear fact. fold MP. fold mor1.

    (* Work on mor2 using factorization *)
    apply (Abelian_factorization2_is_monic
             A hs
             (MorphismPairMor2
                A (ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED))).
    rewrite <- assoc.
    set (fact := Abelian_factorization2
                   A hs
                   (MorphismPairMor2
                      A (ShortShortExactData_MorphismPair
                           A (Abelian_Zero A) SSED))).
    unfold Abelian_factorization2_epi in fact. cbn in fact.
    unfold mor2. unfold MP. rewrite <- fact. clear fact. fold MP. fold mor2.
    rewrite ZeroArrow_comp_left.

    apply SSED_Eq.
  Qed.

  Definition SHortExact_ShortShortExact_isEqualizer_Eq
             (SSE : ShortShortExact A hs)
             (w : A)
             (h : A ⟦w,
                     MorphismPairOb2
                       A (ShortShortExactData_MorphismPair
                            A (Abelian_Zero A)
                            (ShortShortExact_ShortShortExactData
                               A hs SSE))⟧)
             (H' : h ;; CokernelArrow
                     (Abelian_Zero A)
                     (Abelian_CoIm
                        A (MorphismPairMor2
                             A (ShortShortExactData_MorphismPair
                                  A (Abelian_Zero A)
                                  (ShortShortExact_ShortShortExactData
                                     A hs SSE))))
                   = ZeroArrow A (Abelian_Zero A) _ _) :
    h ;; (CokernelArrow
            (Abelian_Zero A)
            (Abelian_Cokernel
               A (KernelArrow
                    (Abelian_Zero A)
                    (Abelian_Im
                       A (MorphismPairMor1
                            A (ShortShortExactData_MorphismPair
                                 A (Abelian_Zero A)
                                 (ShortShortExact_ShortShortExactData
                                    A hs SSE)))))))
    = ZeroArrow A (Abelian_Zero A) _ _.
  Proof.
    set (SSED := ShortShortExact_ShortShortExactData A hs SSE).
    set (SSED_Eq := ShortShortExactData_Eq A (Abelian_Zero A) SSED).
    set (MP := ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED).
    set (mor1 := MorphismPairMor1 A MP).
    set (mor2 := MorphismPairMor2 A MP).

    set (Im := Abelian_Im A mor1).
    set (CoIm := Abelian_CoIm A mor2).

    assert (X : h ;; (MorphismPairMor2 A MP)
                = ZeroArrow A (Abelian_Zero A) _ _).
    {
      unfold MP.
      rewrite (Abelian_factorization2
                 A hs
                 (MorphismPairMor2
                    A (ShortShortExactData_MorphismPair
                         A (Abelian_Zero A) SSED))).
      unfold Abelian_factorization2_epi. unfold SSED. cbn.

      set (tmp := Abelian_factorization2_monic
                    A hs (MorphismPairMor2
                            A (ShortShortExactData_MorphismPair
                                 A (Abelian_Zero A) SSED))).
      apply (maponpaths (fun h' : _ => h' ;; tmp)) in H'. unfold tmp in H'.
      clear tmp. rewrite ZeroArrow_comp_left in H'. rewrite <- assoc in H'.
      unfold Abelian_factorization2_monic, SSED in H'. cbn in H'.
      exact H'.
    }

    unfold MP in X. unfold SSED in X.
    set (comm1 := KernelCommutes
                    (Abelian_Zero A)
                    (Abelian_Kernel
                       A (MorphismPairMor2
                            A (ShortShortExactData_MorphismPair
                                 A (Abelian_Zero A)
                                 (ShortShortExact_ShortShortExactData
                                    A hs SSE))))
                    w h X).
    set (ker := ShortShortExact_Kernel A hs SSE).

    set (tmp := (Abelian_Kernel
                   A (MorphismPairMor2
                        A (ShortShortExactData_MorphismPair
                             A (Abelian_Zero A)
                             (ShortShortExact_ShortShortExactData A hs SSE))))).
    set (tmp_eq := (KernelEqAr (Abelian_Zero A) tmp)).
    rewrite ZeroArrow_comp_right in tmp_eq.
    set (comm2 := KernelCommutes
                    (Abelian_Zero A)
                    ker
                    tmp
                    (KernelArrow (Abelian_Zero A) tmp)
                    tmp_eq).
    unfold tmp in comm2.
    rewrite <- comm2 in comm1. clear comm2.
    rewrite <- comm1. rewrite <- assoc. rewrite <- assoc.
    rewrite CokernelCompZero. rewrite ZeroArrow_comp_right.
    rewrite ZeroArrow_comp_right. apply idpath.
  Qed.

  (* Is there a way to clean the type of the following definition ? *)
  Definition ShortExact_ShortShortExact_isEqualizer
             (SSE : ShortShortExact A hs) :
    isEqualizer
      (MorphismPairMor2
         A (ShortShortExactData_MorphismPair
              A (Abelian_Zero A)
              (mk_ShortShortExactData
                 A (Abelian_Zero A)
                 (mk_MorphismPair
                    A (KernelArrow
                         (Abelian_Zero A)
                         (Abelian_Im
                            A (MorphismPairMor1
                                 A (ShortShortExactData_MorphismPair
                                      A (Abelian_Zero A)
                                      (ShortShortExact_ShortShortExactData
                                         A hs SSE)))))
                    (CokernelArrow
                       (Abelian_Zero A)
                       (Abelian_CoIm
                          A (MorphismPairMor2
                               A (ShortShortExactData_MorphismPair
                                    A (Abelian_Zero A)
                                    (ShortShortExact_ShortShortExactData
                                       A hs SSE))))))
                 (ShortExact_from_ShortShortExact_eq SSE))))
      (ZeroArrow A (Abelian_Zero A) _ _)
      (KernelArrow
         (Abelian_Zero A)
         (ShortShortExactData_Im
            A (mk_ShortShortExactData
                 A (Abelian_Zero A)
                 (mk_MorphismPair
                    A (KernelArrow
                         (Abelian_Zero A)
                         (Abelian_Im
                            A (MorphismPairMor1
                                 A (ShortShortExactData_MorphismPair
                                      A (Abelian_Zero A)
                                      (ShortShortExact_ShortShortExactData
                                         A hs SSE)))))
                    (CokernelArrow
                       (Abelian_Zero A)
                       (Abelian_CoIm
                          A (MorphismPairMor2
                               A (ShortShortExactData_MorphismPair
                                    A (Abelian_Zero A)
                                    (ShortShortExact_ShortShortExactData
                                       A hs SSE))))))
                 (ShortExact_from_ShortShortExact_eq SSE))))
      (KernelEqRw
         (Abelian_Zero A)
         (ShortShortExactData_Im_Eq
            A hs
            (mk_ShortShortExactData
               A (Abelian_Zero A)
               (mk_MorphismPair
                  A (KernelArrow
                       (Abelian_Zero A)
                       (Abelian_Im
                          A (MorphismPairMor1
                               A (ShortShortExactData_MorphismPair
                                      A (Abelian_Zero A)
                                      (ShortShortExact_ShortShortExactData
                                         A hs SSE)))))
                  (CokernelArrow
                     (Abelian_Zero A)
                     (Abelian_CoIm
                        A (MorphismPairMor2
                             A (ShortShortExactData_MorphismPair
                                  A (Abelian_Zero A)
                                  (ShortShortExact_ShortShortExactData
                                     A hs SSE))))))
               (ShortExact_from_ShortShortExact_eq SSE)))).
  Proof.
    set (SSED := ShortShortExact_ShortShortExactData A hs SSE).
    set (SSED_Eq := ShortShortExactData_Eq A (Abelian_Zero A) SSED).
    set (MP := ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED).
    set (mor1 := MorphismPairMor1 A MP).
    set (mor2 := MorphismPairMor2 A MP).

    set (Im := Abelian_Im A mor1).
    set (CoIm := Abelian_CoIm A mor2).

    cbn in *.
    use mk_isEqualizer.
    intros w h H'.
    use unique_exists.

    (* Construction of the morphism *)
    - use KernelIn.
      + exact h.
      + rewrite ZeroArrow_comp_right in H'.
        apply (SHortExact_ShortShortExact_isEqualizer_Eq SSE w h H').

    (* Commutativity *)
    - apply KernelCommutes.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. apply KernelInsEq.
      rewrite T. apply pathsinv0.
      apply KernelCommutes.
  Qed.

  Definition ShortExact_from_ShortShortExact (SSE : ShortShortExact A hs) :
    ShortExact A hs.
  Proof.
    set (SSED := ShortShortExact_ShortShortExactData A hs SSE).
    set (SSED_Eq := ShortShortExactData_Eq A (Abelian_Zero A) SSED).
    set (MP := ShortShortExactData_MorphismPair A (Abelian_Zero A) SSED).
    set (mor1 := MorphismPairMor1 A MP).
    set (mor2 := MorphismPairMor2 A MP).

    set (Im := Abelian_Im A mor1).
    set (CoIm := Abelian_CoIm A mor2).

    use mk_ShortExact.
    - use mk_ShortShortExact.
      + use mk_ShortShortExactData.
        * use mk_MorphismPair.
          -- exact Im.
          -- exact (MorphismPairOb2 A MP).
          -- exact CoIm.
          -- exact (KernelArrow (Abelian_Zero A) Im).
          -- exact (CokernelArrow (Abelian_Zero A) CoIm).
        * exact (ShortExact_from_ShortShortExact_eq SSE).
      + exact (ShortExact_ShortShortExact_isEqualizer SSE).
    - exact (KernelArrowisMonic (Abelian_Zero A) _).
    - exact (CokernelArrowisEpi (Abelian_Zero A) _).
  Defined.


  (** ** [ShortShortExact] from data of [ShortExact]
    We construct a [ShortShortExact] from data corresponding to [ShortExact].
    For a more precise statement, see the comment above
    [ShortShortExact_from_isShortExact]. *)

  Lemma ShortShortExact_from_isSortExact_eq {a b c : A}
             (f : a --> b) (g : b --> c)
             (H : (KernelArrow
                    (Abelian_Zero A)
                    (Abelian_Im A f))
                    ;; (CokernelArrow
                          (Abelian_Zero A)
                          (Abelian_CoIm A g))
             = ZeroArrow A (Abelian_Zero A) _ _)
             (isEq : isEqualizer
                       (CokernelArrow
                          (Abelian_Zero A)
                          (Abelian_CoIm A g))
                       (ZeroArrow A (Abelian_Zero A) _ _)
                       (KernelArrow
                          (Abelian_Zero A)
                          (Abelian_Im A f))
                       (KernelEqRw (Abelian_Zero A) H)) :
    MorphismPairMor1 A (mk_MorphismPair A f g)
                     ;; MorphismPairMor2 A (mk_MorphismPair A f g)
    = ZeroArrow A (Abelian_Zero A) _ _.
  Proof.
    cbn.
    set (tmp :=  maponpaths
                   (fun h' : _ =>
                      CokernelArrow (Abelian_Zero A) (Abelian_CoIm A f)
                                    ;; (Abelian_CoIm_to_Im A f) ;; h') H).
    cbn in tmp. rewrite ZeroArrow_comp_right in tmp.
    apply (maponpaths
             (fun h' : _ =>
                h' ;; (Abelian_CoIm_to_Im A g)
                   ;; ((KernelArrow (Abelian_Zero A) (Abelian_Im A g)))))
                in tmp.
    rewrite ZeroArrow_comp_left in tmp.
    repeat rewrite assoc in tmp.

    (* Work on f in tmp *)
    set (fact := Abelian_factorization2 A hs f).
    unfold Abelian_factorization2_epi in fact. cbn in fact.
    rewrite assoc in fact. rewrite <- fact in tmp. clear fact.

    (* Work of g in tmp *)
    set (fact := Abelian_factorization1 A hs g).
    unfold Abelian_factorization2_monic in fact. cbn in fact.
    repeat rewrite <- assoc in tmp. repeat rewrite <- assoc in fact.
    rewrite <- fact in tmp. clear fact.

    rewrite ZeroArrow_comp_left in tmp.  apply tmp.
  Qed.

  Lemma ShortShortExact_from_isShortExact_isEqualizer_eq {a b c : A}
        (f : a --> b) (g : b --> c)
        (H : (KernelArrow
                (Abelian_Zero A)
                (Abelian_Im A f))
               ;; (CokernelArrow
                     (Abelian_Zero A)
                     (Abelian_CoIm A g))
             = ZeroArrow A (Abelian_Zero A) _ _)
        (isEq : isEqualizer
                  (CokernelArrow
                     (Abelian_Zero A)
                     (Abelian_CoIm A g))
                  (ZeroArrow A (Abelian_Zero A) _ _)
                  (KernelArrow
                     (Abelian_Zero A)
                     (Abelian_Im A f))
                  (KernelEqRw (Abelian_Zero A) H))
        (w : A)
        (h : A ⟦w, b⟧)
        (H' : h ;; g = h ;; ZeroArrow A (Abelian_Zero A) b c) :
    h ;; CokernelArrow (Abelian_Zero A) (Abelian_Cokernel A f) =
    ZeroArrow A (Abelian_Zero A) w (Abelian_Cokernel A f).
  Proof.
    set (ker
         := mk_Kernel
              (Abelian_Zero A)
              (KernelArrow (Abelian_Zero A) (Abelian_Im A f))
              (CokernelArrow (Abelian_Zero A) (Abelian_CoIm A g))
              H isEq).

    rewrite ZeroArrow_comp_right in H'.

    (* Rewrite g in H' *)
    set (fact := Abelian_factorization2 A hs g).
    unfold Abelian_factorization2_epi in fact. cbn in fact.
    rewrite fact in H'. clear fact.

    (* Use commutativity of ker *)
    rewrite assoc in H'.
    assert (X : h ;; CokernelArrow (Abelian_Zero A) (Abelian_CoIm A g)
                = ZeroArrow A (Abelian_Zero A) _ _).
    {
      apply (Abelian_factorization2_is_monic A hs g).
      rewrite ZeroArrow_comp_left.
      apply H'.
    }
    set (comm1 := KernelCommutes (Abelian_Zero A) ker w h X).
    unfold ker in comm1. cbn in comm1.

    rewrite <- comm1. unfold Abelian_Im. rewrite <- assoc.
    rewrite KernelCompZero. apply ZeroArrow_comp_right.
  Qed.

  Lemma ShortShortExact_from_isShortExact_isEqualizer {a b c : A}
        (f : a --> b) (g : b --> c)
        (H : (KernelArrow
                (Abelian_Zero A)
                (Abelian_Im A f))
               ;; (CokernelArrow
                     (Abelian_Zero A)
                     (Abelian_CoIm A g))
             = ZeroArrow A (Abelian_Zero A) _ _)
        (isEq : isEqualizer
                  (CokernelArrow
                     (Abelian_Zero A)
                     (Abelian_CoIm A g))
                  (ZeroArrow A (Abelian_Zero A) _ _)
                  (KernelArrow
                     (Abelian_Zero A)
                     (Abelian_Im A f))
                  (KernelEqRw (Abelian_Zero A) H)) :
    isEqualizer
      (MorphismPairMor2
         A (ShortShortExactData_MorphismPair
              A (Abelian_Zero A)
              (mk_ShortShortExactData
                 A (Abelian_Zero A) (mk_MorphismPair A f g)
                 (ShortShortExact_from_isSortExact_eq f g H isEq))))
      (ZeroArrow A (Abelian_Zero A) _ _)
      (KernelArrow
         (Abelian_Zero A)
         (ShortShortExactData_Im
            A (mk_ShortShortExactData
                 A (Abelian_Zero A) (mk_MorphismPair A f g)
                 (ShortShortExact_from_isSortExact_eq f g H isEq))))
      (KernelEqRw (Abelian_Zero A)
                  (ShortShortExactData_Im_Eq
                     A hs
                     (mk_ShortShortExactData
                        A (Abelian_Zero A) (mk_MorphismPair A f g)
                        (ShortShortExact_from_isSortExact_eq f g H isEq)))).
  Proof.
    cbn.
    use mk_isEqualizer.
    intros w h H'.
    use unique_exists; cbn in *.

    (* Construction of the arrow *)
    - unfold ShortShortExactData_Im; cbn.
      use KernelIn.
      + exact h.
      + exact (ShortShortExact_from_isShortExact_isEqualizer_eq
                 f g H isEq w h H').

    (* Comutativity *)
    - apply KernelCommutes.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. apply KernelInsEq.
      rewrite T. apply pathsinv0.
      apply KernelCommutes.
  Qed.

  (** To see how the assumptions correspond to [ShortExact] note that every
    kernel is a monic and every cokernel is an epi. Also, the assumption H
    says that an image of f is the kernel of a coimage of g. In abelian
    categories every monic is the kernel of its cokernel, and thus one can
    show that in isE the kernelarrow can be "replaced" by the kernelarrow of
    the image of the kernelarrow. Thus the assumptions are similar to
    assumptions of [ShortExact]. *)
  Definition ShortShortExact_from_isShortExact {a b c : A}
             (f : a --> b) (g : b --> c)
             (H : (KernelArrow
                    (Abelian_Zero A)
                    (Abelian_Im A f))
                    ;; (CokernelArrow
                          (Abelian_Zero A)
                          (Abelian_CoIm A g))
             = ZeroArrow A (Abelian_Zero A) _ _)
             (isEq : isEqualizer
                       (CokernelArrow
                          (Abelian_Zero A)
                          (Abelian_CoIm A g))
                       (ZeroArrow A (Abelian_Zero A) _ _)
                       (KernelArrow
                          (Abelian_Zero A)
                          (Abelian_Im A f))
                       (KernelEqRw (Abelian_Zero A) H)) :
    ShortShortExact A hs.
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
