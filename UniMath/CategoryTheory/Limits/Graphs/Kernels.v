(** * Kernels defined in terms of limits *)
(** ** Contents
- Definition coincides with the direct definition
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.

Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Limits.Graphs.Zero.
Require Import UniMath.CategoryTheory.Limits.Graphs.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Kernels.


(** * Definition of kernels in terms of limits *)
Section def_Kernels.

  Variable C : precategory.
  Variable hs: has_homsets C.
  Variable Z : Zero C.

  Definition Kernel {a b : C} (f : C⟦a, b⟧) := Equalizer C f (ZeroArrow Z a b).

  (** ** Maps between Kernels as limits and direct definition. *)
  Lemma equiv_Kernel1_eq {a b : C} (f : C⟦a, b⟧) (K : Limits.Kernels.Kernel (equiv_Zero2 Z) f) :
    KernelArrow K · f = KernelArrow K · ZeroArrow Z a b.
  Proof.
    rewrite precomp_with_ZeroArrow. rewrite <- equiv_ZeroArrow. apply KernelCompZero.
  Qed.

  Lemma equiv_Kernel1_isEqualizer {a b : C} (f : C⟦a, b⟧)
        (K : Limits.Kernels.Kernel (equiv_Zero2 Z) f) :
    isEqualizer C f (ZeroArrow Z a b) K (KernelArrow K) (equiv_Kernel1_eq f K).
  Proof.
    use (mk_isEqualizer _ hs).
    intros e h' H'.
    use unique_exists.
    (* Construction of the morphism *)
    - use KernelIn.
      + exact h'.
      + rewrite precomp_with_ZeroArrow in H'.
        use (pathscomp0 _ (!(equiv_ZeroArrow e b Z))).
        exact H'.
    (* Commutativity *)
    - cbn. use KernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y X. cbn in X.
      use Limits.Kernels.KernelInsEq. unfold KernelArrow.
      use (pathscomp0 X). apply pathsinv0.
      use Limits.Kernels.KernelCommutes.
  Qed.

  Definition equiv_Kernel1 {a b : C} (f : C⟦a, b⟧) (K : Limits.Kernels.Kernel (equiv_Zero2 Z) f) :
    Kernel f.
  Proof.
    use mk_Equalizer.
    - exact K.
    - exact (KernelArrow K).
    - exact (equiv_Kernel1_eq f K).
    - exact (equiv_Kernel1_isEqualizer f K).
  Defined.

  (* Other direction *)

  Lemma equiv_Kernel2_eq {a b : C} (f : C⟦a, b⟧) (K : Kernel f) :
    EqualizerArrow C K · f = Limits.Zero.ZeroArrow (equiv_Zero2 Z) (EqualizerObject C K) b.
  Proof.
    rewrite (EqualizerArrowEq C K). rewrite equiv_ZeroArrow.
    rewrite precomp_with_ZeroArrow. apply idpath.
  Qed.


  Lemma equiv_Kernel2_isEqualizer {a b : C} (f : C⟦a, b⟧) (K : Kernel f) :
    isKernel (equiv_Zero2 Z) (EqualizerArrow C K) f (equiv_Kernel2_eq f K).
  Proof.
    use (mk_isKernel hs).
    intros w h H.
    use unique_exists.
    (* Construction of the morphism *)
    - use EqualizerIn.
      + exact h.
      + rewrite H.
        rewrite precomp_with_ZeroArrow.
        apply equiv_ZeroArrow.
    (* Commutativity *)
    - use EqualizerArrowComm.
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y T. cbn in T.
      use EqualizerInUnique. exact T.
  Qed.

  Definition equiv_Kernel2 {a b : C} (f : C⟦a, b⟧) (K : Kernel f) :
    Limits.Kernels.Kernel (equiv_Zero2 Z) f.
  Proof.
    use mk_Kernel.
    - exact (EqualizerObject C K).
    - exact (EqualizerArrow C K).
    - exact (equiv_Kernel2_eq f K).
    - exact (equiv_Kernel2_isEqualizer f K).
  Defined.

End def_Kernels.
