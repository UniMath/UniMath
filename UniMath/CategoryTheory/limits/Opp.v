(** * Duality between C and C^op *)
(** ** Contents
- From C^op to C
 - Monics and Epis
 - Initial, Terminal, and Zero
 - Equalizers and Coequalizers
 - Kernels and Cokernels
 - Pullbacks and Pushouts
 - BinProducts and BinCoproducts
- From C to C^op
 - Monics and Epis
 - Initial, Terminal, and Zero
 - Equalizers and Coequalizers
 - Kernels and Cokernels
 - Pullbacks and Pushouts
 - BinProducts and BinCoproducts
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.cokernels.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Local Open Scope cat.

Local Notation "C '^op'" := (op_category C) (at level 3, format "C ^op") : cat.

(** * Translation of structures from C^op to C *)
Section def_opposites.

  Variable C : category.
  Let hs : has_homsets C := homset_property C.

  (** ** Monic and Epi *)

  Definition opp_isMonic {a b : C} (f : a --> b) (H : @isMonic (op_category C) _ _ f) : @isEpi C _ _ f := H.
  Opaque opp_isMonic.

  Definition opp_Monic {a b : C} (f : @Monic (op_category C) a b) : @Epi C b a :=
    @make_Epi C _ _ f (opp_isMonic f (pr2 f)).

  Definition opp_isEpi {a b : C} (f : a --> b) (H : @isEpi (C^op) _ _ f) : @isMonic C _ _ f := H.
  Opaque opp_isEpi.

  Definition opp_Epi {a b : C} (f : @Epi (C^op) a b) : @Monic C b a :=
    @make_Monic C _ _ f (opp_isEpi f (pr2 f)).


  (** ** Initial, Terminal, and Zero *)

  Definition opp_isInitial {x : C} (H : @isInitial (C^op) x) : @isTerminal C x := H.

  Definition opp_Initial (I : @Initial (C^op)) : @Terminal C :=
    @make_Terminal C _ (opp_isInitial (pr2 I)).

  Definition opp_isTerminal {x : C} (H : @isTerminal (C^op) x) : @isInitial C x := H.

  Definition opp_Terminal (T : @Terminal (C^op)) : @Initial C :=
    @make_Initial C _ (opp_isTerminal (pr2 T)).

  Lemma opp_isZero {x : C} (H : @isZero (C^op) x) : @isZero C x.
  Proof.
    use make_isZero.
    - intros a. exact (dirprod_pr2 H a).
    - intros a. exact (dirprod_pr1 H a).
  Qed.

  Definition opp_Zero (Z : @Zero (C^op)) : @Zero C := @make_Zero C _ (opp_isZero (pr2 Z)).


  (** ** Equality on ZeroArrows *)

  Lemma opp_ZeroArrowTo {x : C} (Z : @Zero (C^op)) :
    @ZeroArrowTo (C^op) Z x = @ZeroArrowFrom C (opp_Zero Z) x.
  Proof.
    apply ArrowsToZero.
  Qed.

  Lemma opp_ZeroArrowFrom {x : C} (Z : @Zero (C^op)) :
    @ZeroArrowFrom (C^op) Z x = @ZeroArrowTo C (opp_Zero Z) x.
  Proof.
    apply ArrowsFromZero.
  Qed.

  Lemma opp_ZeroArrow {x y : C} (Z : @Zero (C^op)) :
    @ZeroArrow (C^op) Z x y = @ZeroArrow C (opp_Zero Z) y x.
  Proof.
    unfold ZeroArrow.
    rewrite opp_ZeroArrowTo.
    rewrite opp_ZeroArrowFrom.
    apply idpath.
  Qed.

  Local Opaque ZeroArrow.


  (** ** Equalizers and Coequalizers *)

  Lemma opp_isEqualizer {x y z : C} (f g : (C^op)⟦y, z⟧) (e : (C^op)⟦x, y⟧) (H : e · f = e · g)
    (H' : @isEqualizer (op_category C) _ _ _ f g e H) : @isCoequalizer C _ _ _ f g e H.
  Proof.
    exact H'.
  Qed.

  Lemma opp_isCoequalizer {x y z : C} (f g : (C^op)⟦x, y⟧) (e : (C^op)⟦y, z⟧)
        (H : f · e = g · e) (H' : @isCoequalizer (C^op) _ _ _ f g e H) :
    @isEqualizer C _ _ _ f g e H.
  Proof.
    exact H'.
  Qed.

  Definition opp_Equalizer {y z : C} (f g : (C^op)⟦y, z⟧) (E : @Equalizer (op_category C) y z f g) :
    @Coequalizer C z y f g := @make_Coequalizer C _ _ _ f g (EqualizerArrow E) (EqualizerEqAr E)
                                              (opp_isEqualizer f g (EqualizerArrow E)
                                                               (EqualizerEqAr E)
                                                               (isEqualizer_Equalizer E)).

  Definition opp_Coequalizer {y z : C} (f g : (C^op)⟦y, z⟧) (E : @Coequalizer (C^op) y z f g) :
    @Equalizer C z y f g := @make_Equalizer C _ _ _ f g (CoequalizerArrow E) (CoequalizerEqAr E)
                                          (opp_isCoequalizer f g (CoequalizerArrow E)
                                                             (CoequalizerEqAr E)
                                                             (isCoequalizer_Coequalizer E)).

  Definition opp_Equalizers (E : @Equalizers (op_category C)) : @Coequalizers C.
  Proof.
    intros x y f g.
    use opp_Equalizer.
    exact (E y x f g).
  Defined.

  Definition opp_Coequalizers (E : @Coequalizers (C^op)) : @Equalizers C.
  Proof.
    intros x y f g.
    use opp_Coequalizer.
    exact (E y x f g).
  Defined.


  (** ** Kernels and Cokernels *)


  Local Lemma opp_isCokernel_eq {x y z : C^op} (f : (C^op)⟦x, y⟧) (g : C^op⟦y, z⟧) (Z : Zero (C^op))
        (H : f · g = ZeroArrow Z _ _) (Z' : Zero C) :
    (g : C⟦z, y⟧) · (f : C⟦y, x⟧) = ZeroArrow Z' _ _.
  Proof.
    cbn in *. rewrite H. rewrite opp_ZeroArrow.
    exact (ZerosArrowEq C (opp_Zero Z) Z' z x).
  Qed.

  Lemma opp_isCokernel {x y z : C^op} {f : (C^op)⟦x, y⟧} {g : C^op⟦y, z⟧} {Z : Zero (C^op)}
        {H : f · g = ZeroArrow Z _ _} (K' : isKernel (C:=op_category C) Z f g H) {Z' : Zero C} :
    isCokernel Z' (g : C⟦z, y⟧) (f : C⟦y, x⟧) (opp_isCokernel_eq f g Z H Z').
  Proof.
    set (K := make_Kernel _ _ _ _ K').
    use make_isCokernel.
    - exact hs.
    - intros w h H'.
      rewrite <- (ZerosArrowEq C (opp_Zero Z) Z' z w) in H'.
      rewrite <- opp_ZeroArrow in H'.
      use unique_exists.
      + exact (KernelIn (C:=op_category _ )Z K w h H').
      + use (KernelCommutes (C:=op_category _) Z K).
      + intros y0. apply hs.
      + cbn. intros y0 X. use (KernelInsEq (C:=op_category _) Z K). rewrite (KernelCommutes (C:=op_category _) Z K). cbn. rewrite X.
        apply idpath.
  Qed.

  Local Lemma opp_Kernel_eq {y z : C} (f : (C^op)⟦y, z⟧) (Z : Zero (C^op))
             (K : @Kernel (op_category C) Z y z f) :
    @compose C^op _ _ _ (KernelArrow K) f = ZeroArrow (opp_Zero Z) z K.
  Proof.
    cbn. rewrite <- opp_ZeroArrow. apply (KernelCompZero (C:= op_category _) Z K).
  Qed.

  Lemma opp_Kernel_isCokernel {y z : C} (f : (C^op)⟦y, z⟧) (Z : Zero (C^op))
             (K : @Kernel (C^op) Z y z f) :
    isCokernel (opp_Zero Z) f (KernelArrow K) (opp_Kernel_eq f Z K).
  Proof.
    use make_isCokernel.
    - exact hs.
    - intros w h H'. rewrite <- opp_ZeroArrow in H'.
      use unique_exists.
      + exact (KernelIn Z K w h H').
      + use (KernelCommutes Z K).
      + intros y0. apply hs.
      + cbn. intros y0 X. use (@KernelInsEq C^op). rewrite (KernelCommutes Z K). cbn. rewrite X.
        apply idpath.
  Qed.

  Definition opp_Kernel {y z : C} (f : (C^op)⟦y, z⟧) (Z : Zero (C^op))
             (K : @Kernel (C^op) Z y z f) : @Cokernel C (opp_Zero Z) z y f.
  Proof.
    use make_Cokernel.
    - exact K.
    - exact (KernelArrow K).
    - exact (opp_Kernel_eq f Z K).
    - exact (opp_Kernel_isCokernel f Z K).
  Defined.

  Lemma opp_isKernel {x y z : C^op} {f : (C^op)⟦x, y⟧} {g : C^op⟦y, z⟧} {Z : Zero (C^op)}
        {H : f · g = ZeroArrow Z _ _} (CK' : isCokernel Z f g H) {Z' : Zero C} :
    isKernel Z' (g : C⟦z, y⟧) (f : C⟦y, x⟧) (opp_isCokernel_eq f g Z H Z').
  Proof.
    set (CK := make_Cokernel _ _ _ _ CK').
    use make_isKernel.
    intros w h H'.
    rewrite <- (ZerosArrowEq C (opp_Zero Z) Z' w x) in H'.
    rewrite <- opp_ZeroArrow in H'.
    use unique_exists.
    + exact (CokernelOut Z CK w h H').
    + use (CokernelCommutes Z CK).
    + intros y0. apply hs.
    + cbn. intros y0 X. use (CokernelOutsEq _ CK). rewrite (CokernelCommutes Z CK). cbn. rewrite X.
      apply idpath.
  Qed.

  Local Lemma opp_Cokernel_eq {y z : C} (f : (C^op)⟦y, z⟧) (Z : Zero (C^op))
             (CK : @Cokernel (C^op) Z y z f) :
    @compose (C^op) _ _ _ f (CokernelArrow CK) = ZeroArrow (opp_Zero Z) CK y.
  Proof.
    cbn. rewrite <- opp_ZeroArrow. apply (CokernelCompZero Z CK).
  Qed.

  Lemma opp_Cokernel_isKernel {y z : C} (f : (C^op)⟦y, z⟧) (Z : Zero (C^op))
             (CK : @Cokernel (C^op) Z y z f) :
    isKernel (opp_Zero Z) (CokernelArrow CK) f (opp_Cokernel_eq f Z CK).
  Proof.
    use make_isKernel.
    intros w h H'. rewrite <- opp_ZeroArrow in H'.
    use unique_exists.
    + exact (CokernelOut Z CK w h H').
    + use (CokernelCommutes Z CK).
    + intros y0. apply hs.
    + cbn. intros y0 X. use (@CokernelOutsEq C^op). rewrite (CokernelCommutes Z CK). cbn. rewrite X.
      apply idpath.
  Qed.

  Definition opp_Cokernel {y z : C} (f : (C^op)⟦y, z⟧) (Z : Zero (C^op))
             (CK : @Cokernel (C^op) Z y z f) : @Kernel C (opp_Zero Z) z y f.
  Proof.
    use make_Kernel.
    - exact CK.
    - exact (CokernelArrow CK).
    - exact (opp_Cokernel_eq f Z CK).
    - exact (opp_Cokernel_isKernel f Z CK).
  Defined.

  Definition opp_Kernels (Z : Zero (C^op)) (K : @Kernels (C^op) Z) : @Cokernels C (opp_Zero Z).
  Proof.
    intros x y f.
    use opp_Kernel.
    apply (K y x f).
  Defined.

  Definition opp_Cokernels (Z : Zero (C^op)) (CK : @Cokernels (C^op) Z) : @Kernels C (opp_Zero Z).
  Proof.
    intros x y f.
    use opp_Cokernel.
    apply (CK y x f).
  Defined.


  (** ** Pushouts and pullbacks *)

  Lemma opp_isPushout {a b c d : C} (f : (C^op)⟦a, b⟧) (g : (C^op)⟦a, c⟧)
        (in1 : (C^op)⟦b, d⟧) (in2 : (C^op)⟦c, d⟧) (H : f · in1 = g · in2)
        (iPo : @isPushout (C^op) a b c d f g in1 in2 H) : @isPullback C a b c d f g in1 in2 H.
  Proof.
    exact iPo.
  Qed.

  Lemma opp_isPullback {a b c d : C} (f : (C^op)⟦b, a⟧) (g : (C^op)⟦c, a⟧)
        (p1 : (C^op)⟦d, b⟧) (p2 : (C^op)⟦d, c⟧) (H : p1 · f = p2 · g)
        (iPb : @isPullback (C^op) a b c d f g p1 p2 H) : @isPushout C a b c d f g p1 p2 H.
  Proof.
    exact iPb.
  Qed.

  Definition opp_Pushout {a b c : C} (f : (C^op)⟦a, b⟧) (g : (C^op)⟦a, c⟧)
             (Po : @Pushout (C^op) a b c f g) : @Pullback C a b c f g.
  Proof.
    exact Po.
  Defined.

  Definition opp_Pullback {a b c : C} (f : (C^op)⟦b, a⟧) (g : (C^op)⟦c, a⟧)
             (Pb : @Pullback (C^op) a b c f g) : @Pushout C a b c f g.
  Proof.
    exact Pb.
  Defined.

  Definition opp_Pushouts (Pos : @Pushouts (C^op)) : @Pullbacks C.
  Proof.
    exact Pos.
  Defined.

  Definition opp_Pullbacks (Pbs : @Pushouts (C^op)) : @Pullbacks C.
  Proof.
    exact Pbs.
  Defined.


  (** ** BinProducts and BinCoproducts *)

  Definition opp_isBinProduct (c d p : C) (p1 : (C^op)⟦p, c⟧) (p2 : (C^op)⟦p, d⟧)
             (iBPC : @isBinProduct (C^op) c d p p1 p2) : @isBinCoproduct C c d p p1 p2 :=
    iBPC.

  Definition opp_isBinCoproduct (a b co : C) (ia : (C^op)⟦a, co⟧) (ib : (C^op)⟦b, co⟧)
             (iBCC : @isBinCoproduct (C^op) a b co ia ib) :
    @isBinProduct C a b co ia ib := iBCC.

  Definition opp_BinProduct (c d : C) (BPC : @BinProduct (C^op) c d) :
    @BinCoproduct C c d := BPC.

  Definition opp_BinCoproduct (c d : C) (BCC : @BinCoproduct (C^op) c d) :
    @BinProduct C c d := BCC.

  Definition opp_BinProducts (BP : @BinProducts (C^op)) : @BinCoproducts C := BP.

  Definition opp_BinCoproducts (BC : @BinCoproducts (C^op)) : @BinProducts C := BC.

End def_opposites.


(** * Translation of structures from C to C^op *)
Section def_opposites'.

  Variable C : category.
  Let hs : has_homsets C := homset_property C.

  (** ** Monic and Epi *)

  Definition isMonic_opp {a b : C} {f : C⟦a, b⟧} (H : @isMonic C a b f) : @isEpi (C^op) b a f := H.
  Opaque isMonic_opp.

  Definition Monic_opp {a b : C} (f : @Monic C a b) : @Epi (C^op) b a :=
    @make_Epi (C^op) b a f (isMonic_opp (pr2 f)).

  Definition isEpi_opp {a b : C} {f : C⟦a, b⟧} (H : @isEpi C a b f) : @isMonic (C^op) b a f := H.
  Opaque isEpi_opp.

  Definition Epi_opp {a b : C} (f : @Epi C a b) : @Monic (C^op) b a :=
    @make_Monic (C^op) b a f (isEpi_opp (pr2 f)).


  (** ** Initial, Terminal, and Zero *)

  Definition isInitial_opp {x : C} (H : @isInitial C x) : @isTerminal (C^op) x := H.

  Definition Initial_opp (I : @Initial C) : @Terminal (C^op) :=
    @make_Terminal (C^op) _ (isInitial_opp (pr2 I)).

  Definition isTerminal_opp {x : C} (H : @isTerminal C x) : @isInitial (C^op) x := H.

  Definition Terminal_opp (T : @Terminal C) : @Initial (C^op) :=
    @make_Initial (C^op) _ (isTerminal_opp (pr2 T)).

  Lemma isZero_opp {x : C} (H : @isZero C x) : @isZero (C^op) x.
  Proof.
    use make_isZero.
    - intros a. apply (pr2 H a).
    - intros a. apply (pr1 H a).
  Defined.

  Definition Zero_opp (T : @Zero C) : @Zero (C^op) := @make_Zero (C^op) _ (isZero_opp (pr2 T)).

  (** ** Equality on ZeroArrows *)

  Lemma ZeroArrowTo_opp {x : C} (Z : @Zero C) :
    @ZeroArrowTo C Z x = @ZeroArrowFrom (C^op) (Zero_opp Z) x.
  Proof.
    apply ArrowsToZero.
  Qed.

  Lemma ZeroArrowFrom_opp {x : C} (Z : @Zero C) :
    @ZeroArrowFrom C Z x = @ZeroArrowTo (C^op) (Zero_opp Z) x.
  Proof.
    apply ArrowsFromZero.
  Qed.

  Lemma ZeroArrow_opp {x y : C} (Z : @Zero C) :
    @ZeroArrow C Z x y = @ZeroArrow (C^op) (Zero_opp Z) y x.
  Proof.
    unfold ZeroArrow.
    rewrite ZeroArrowTo_opp.
    rewrite ZeroArrowFrom_opp.
    apply idpath.
  Qed.

  Local Opaque ZeroArrow.


  (** ** Equalizers and Coequalizers *)

  Definition isEqualizer_opp {x y z : C} (f g : C⟦y, z⟧) (e : C⟦x, y⟧) (H : e · f = e · g)
             (isE : @isEqualizer C _ _ _ f g e H) : @isCoequalizer (C^op) _ _ _ f g e H := isE.

  Definition isCoequalizer_opp {x y z : C} (f g : C⟦x, y⟧) (e : C⟦y, z⟧) (H : f · e = g · e)
             (isC : @isCoequalizer C _ _ _ f g e H) : @isEqualizer (C^op) _ _ _ f g e H := isC.

  Definition Equalizer_opp {y z : C} (f g : C⟦y, z⟧) (E : @Equalizer C y z f g) :
    @Coequalizer (C^op) z y f g := @make_Coequalizer (C^op) _ _ _ f g (EqualizerArrow E)
                                                   (EqualizerEqAr E)
                                                   (isEqualizer_opp f g (EqualizerArrow E)
                                                                    (EqualizerEqAr E)
                                                                    (isEqualizer_Equalizer E)).

  Definition Coequalizer_opp {y z : C} (f g : C⟦y, z⟧) (CE : @Coequalizer C y z f g) :
    @Equalizer (C^op) z y f g := @make_Equalizer (C^op) _ _ _ f g (CoequalizerArrow CE)
                                               (CoequalizerEqAr CE)
                                               (isCoequalizer_opp f g (CoequalizerArrow CE)
                                                                  (CoequalizerEqAr CE)
                                                                  (isCoequalizer_Coequalizer CE)).

  Definition Equalizers_opp (E : @Equalizers C) : @Coequalizers (C^op).
  Proof.
    intros x y f g.
    use Equalizer_opp.
    exact (E y x f g).
  Defined.

  Definition Coequalizers_opp (CE : @Coequalizers C) : @Equalizers (C^op).
  Proof.
    intros x y f g.
    use Coequalizer_opp.
    exact (CE y x f g).
  Defined.


  (** ** Kernels and Cokernels *)

  Local Lemma isCokernel_opp_eq {x y z : C} (f : C⟦x, y⟧) (g : C⟦y, z⟧) (Z : Zero C)
        (H : f · g = ZeroArrow Z _ _) (Z' : Zero C^op) :
    (g : C^op⟦z, y⟧) · (f : C^op⟦y, x⟧) = ZeroArrow Z' _ _.
  Proof.
    cbn in *. rewrite H. rewrite ZeroArrow_opp.
    exact (ZerosArrowEq C^op (Zero_opp Z) Z' z x).
  Qed.



  Lemma isCokernel_opp {x y z : C} {f : C⟦x, y⟧} {g : C⟦y, z⟧} {Z : Zero C}
        {H : f · g = ZeroArrow Z _ _} (K' : isKernel Z f g H) {Z' : Zero C^op} :
    isCokernel Z' (g : C^op⟦z, y⟧) (f : C^op⟦y, x⟧) (isCokernel_opp_eq f g Z H Z').
  Proof.
    set (K := make_Kernel _ _ _ _ K').
    use make_isCokernel.
    - exact (has_homsets_opp hs).
    - intros w h H'. cbn in H'.
      set (XXX := (ZerosArrowEq C^op (Zero_opp Z) Z' z w)).
      use unique_exists.
      + use (KernelIn Z K w h _).
        rewrite ZeroArrow_opp.
        rewrite XXX.
        apply H'.
      + cbn. use (KernelCommutes Z K).
      + intros y0. apply (has_homsets_opp hs).
      + cbn. intros y0 X. use (KernelInsEq Z K). rewrite KernelCommutes. exact X.
  Qed.



  Local Lemma Kernel_opp_eq {y z : C} (f : C⟦y, z⟧) (Z : Zero C) (K : @Kernel C Z y z f) :
    @compose C^op _ _ _ f (KernelArrow K) = ZeroArrow (Zero_opp Z) z K.
  Proof.
    cbn. rewrite (KernelCompZero Z K). apply ZeroArrow_opp.
  Qed.

  Lemma Kernel_opp_isCokernel {y z : C} (f : C⟦y, z⟧) (Z : Zero C) (K : @Kernel C Z y z f) :
    isCokernel (Zero_opp Z) f (KernelArrow K) (Kernel_opp_eq f Z K).
  Proof.
    use make_isCokernel.
    - exact (has_homsets_opp hs).
    - intros w h H'. cbn in H'.
      use unique_exists.
      + rewrite <- ZeroArrow_opp in H'. exact (KernelIn Z K w h H').
      + cbn. use KernelCommutes.
      + intros y0. apply (has_homsets_opp hs).
      + cbn. intros y0 X. use KernelInsEq. rewrite KernelCommutes. exact X.
  Qed.

  Definition Kernel_opp {y z : C} (f : C⟦y, z⟧) (Z : Zero C) (K : @Kernel C Z y z f) :
    @Cokernel (C^op) (Zero_opp Z) z y f.
  Proof.
    use make_Cokernel.
    - exact K.
    - exact (KernelArrow K).
    - exact (Kernel_opp_eq f Z K).
    - exact (Kernel_opp_isCokernel f Z K).
  Defined.

  Lemma isKernel_opp {x y z : C^op} {f : C⟦x, y⟧} {g : C⟦y, z⟧} {Z : Zero C}
        {H : f · g = ZeroArrow Z _ _} (CK' : isCokernel Z f g H) {Z' : Zero C^op} :
    isKernel Z' (g : C^op⟦z, y⟧) (f : C^op⟦y, x⟧) (isCokernel_opp_eq f g Z H Z').
  Proof.
    set (CK := make_Cokernel _ _ _ _ CK').
    use make_isKernel.
    - intros w h H'.
      rewrite <- (ZerosArrowEq C^op (Zero_opp Z) Z' w x) in H'.
      rewrite <- ZeroArrow_opp in H'.
      use unique_exists.
      + exact (CokernelOut Z CK w h H').
      + use (CokernelCommutes Z CK).
      + intros y0. apply hs.
      + cbn. intros y0 X. use (CokernelOutsEq _ CK). rewrite (CokernelCommutes Z CK). cbn. rewrite X.
        apply idpath.
  Qed.

  Local Lemma Cokernel_opp_eq {y z : C} (f : C⟦y, z⟧) (Z : Zero C) (CK : @Cokernel C Z y z f) :
    @compose C^op _ _ _ (CokernelArrow CK) f = ZeroArrow (Zero_opp Z) CK y.
  Proof.
    cbn. rewrite (CokernelCompZero Z CK). apply ZeroArrow_opp.
  Qed.

  Lemma Cokernel_opp_isKernel {y z : C} (f : C⟦y, z⟧) (Z : Zero C)
        (CK : @Cokernel C Z y z f) :
    isKernel (Zero_opp Z) (CokernelArrow CK) f (Cokernel_opp_eq f Z CK).
  Proof.
    use make_isKernel.

    - intros w h H'. cbn in H'.
      use unique_exists.
      + rewrite <- ZeroArrow_opp in H'. exact (CokernelOut Z CK w h H').
      + cbn. use CokernelCommutes.
      + intros y0. apply (has_homsets_opp hs).
      + cbn. intros y0 X. use CokernelOutsEq. rewrite CokernelCommutes. exact X.
  Qed.

  Definition Cokernel_opp {y z : C} (f : C⟦y, z⟧) (Z : Zero C) (CK : @Cokernel C Z y z f) :
    @Kernel (C^op) (Zero_opp Z) z y f.
  Proof.
    use make_Kernel.
    - exact CK.
    - exact (CokernelArrow CK).
    - exact (Cokernel_opp_eq f Z CK).
    - exact (Cokernel_opp_isKernel f Z CK).
  Defined.

  Definition Kernels_opp (Z : Zero C) (K : @Kernels C Z) : @Cokernels (C^op) (Zero_opp Z).
  Proof.
    intros x y f.
    use Kernel_opp.
    apply (K y x f).
  Defined.

  Definition Cokernels_opp (Z : Zero C) (CK : @Cokernels C Z) : @Kernels (C^op) (Zero_opp Z).
  Proof.
    intros x y f.
    use Cokernel_opp.
    apply (CK y x f).
  Defined.


  (** ** Pushouts and pullbacks *)

  Definition isPushout_opp {a b c d : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧) (in1 : C⟦b, d⟧) (in2 : C⟦c, d⟧)
             (H : f · in1 = g · in2) (iPo : @isPushout C a b c d f g in1 in2 H) :
    @isPullback (C^op) a b c d f g in1 in2 H := iPo.

  Definition isPullback_opp {a b c d : C} (f : C⟦b, a⟧) (g : C⟦c, a⟧) (p1 : C⟦d, b⟧) (p2 : C⟦d, c⟧)
        (H : p1 · f = p2 · g) (iPb : @isPullback C a b c d f g p1 p2 H) :
    @isPushout (C^op) a b c d f g p1 p2 H := iPb.

  Definition Pushout_opp {a b c : C} (f : C⟦a, b⟧) (g : C⟦a, c⟧) (Po : @Pushout C a b c f g) :
    @Pullback (C^op) a b c f g := Po.

  Definition Pullback_opp {a b c : C} (f : C⟦b, a⟧) (g : C⟦c, a⟧) (Pb : @Pullback C a b c f g) :
    @Pushout (C^op) a b c f g := Pb.

  Definition Pushouts_opp (Pos : @Pushouts C) : @Pullbacks (C^op) := Pos.

  Definition Pullbacks_opp (Pbs : @Pushouts C) : @Pullbacks (C^op) := Pbs.


  (** ** BinProducts and BinCoproducts *)

  Definition isBinProduct_opp (c d p : C) (p1 : C⟦p, c⟧) (p2 : C⟦p, d⟧)
             (iBPC : @isBinProduct C c d p p1 p2) :
    @isBinCoproduct (C^op) c d p p1 p2 := iBPC.

  Definition isBinCoproduct_opp (a b co : C) (ia : C⟦a, co⟧) (ib : C⟦b, co⟧)
             (iBCC : @isBinCoproduct C a b co ia ib) :
    @isBinProduct (C^op) a b co ia ib := iBCC.

  Definition BinProduct_opp (c d : C) (iBPC : @BinProduct C c d) :
    @BinCoproduct (C^op) c d := iBPC.

  Definition BinCoproduct_opp (c d : C) (iBCC : @BinCoproduct C c d) :
    @BinProduct (C^op) c d := iBCC.

  Definition BinProducts_opp (BP : @BinProducts C) : @BinCoproducts (C^op) := BP.

  Definition BinCoproducts_opp (BC : @BinCoproducts C) : @BinProducts (C^op) := BC.

End def_opposites'.

Definition opp_zero_lifts {C:category} {X:Type} (j : X -> ob C) :
  zero_lifts C j -> zero_lifts (opp_precat C) j.
Proof.
  apply hinhfun; intros [z iz]. exists z. exact (isZero_opp C iz).
Defined.
