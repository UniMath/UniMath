(** * Kernels defined in terms of limits *)
(** ** Contents
- Definition coincides with the direct definition
*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.zero.
Require Import UniMath.CategoryTheory.limits.graphs.equalizers.
Require Import UniMath.CategoryTheory.limits.kernels.


(** * Definition of kernels in terms of limits *)
Section def_kernels.

  Variable C : precategory.
  Variable hs: has_homsets C.
  Variable Z : Zero C.

  Definition Kernel {a b : C} (f : C⟦a, b⟧)
    := Equalizer C f (ZeroArrow Z a b).

  (** ** Maps between Kernels as limits and direct definition. *)
  Lemma equiv_Kernel1_eq {a b : C} (f : C⟦a, b⟧) (K : limits.kernels.Kernel (equiv_Zero2 Z) f) :
    limits.equalizers.EqualizerArrow K ;; f = limits.equalizers.EqualizerArrow K ;; ZeroArrow Z a b.
  Proof.
    set (tmp := limits.equalizers.EqualizerEqAr K).
    set (tmp1 := equiv_ZeroArrow a b Z).
    apply (maponpaths (fun h : _ => limits.equalizers.EqualizerArrow K ;; h)) in tmp1.
    set (tmp2 := pathscomp0 tmp tmp1).
    apply tmp2.
  Qed.

  Lemma equiv_Kernel1_isEqualizer {a b : C} (f : C⟦a, b⟧)
        (K : limits.kernels.Kernel (equiv_Zero2 Z) f) :
    limits.equalizers.isEqualizer
      f (ZeroArrow Z a b) (limits.equalizers.EqualizerArrow K) (equiv_Kernel1_eq f K).
  Proof.
    use limits.equalizers.mk_isEqualizer.
    intros w h H.
    use unique_exists.
    (* Construction of the morphism *)
    - use limits.kernels.KernelIn.
      + exact h.
      + rewrite precomp_with_ZeroArrow in H.
        use (pathscomp0 _ (!(equiv_ZeroArrow w b Z))).
        exact H.
    (* Commutativity *)
    - use limits.kernels.KernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y T. cbn in T.
      use limits.kernels.KernelInsEq. unfold KernelArrow.
      use (pathscomp0 T). apply pathsinv0.
      use limits.kernels.KernelCommutes.
  Qed.

  Definition equiv_Kernel1 {a b : C} (f : C⟦a, b⟧) :
    limits.kernels.Kernel (equiv_Zero2 Z) f -> Kernel f.
  Proof.
    intros K.
    exact (equiv_Equalizer1
           C hs f _
           (@limits.equalizers.mk_Equalizer
              C K a b f _
              (limits.equalizers.EqualizerArrow K)
              (equiv_Kernel1_eq f K)
              (equiv_Kernel1_isEqualizer f K))).
  Defined.

  (* Other direction *)

  Lemma equiv_Kernel2_eq {a b : C} (f : C⟦a, b⟧) (K : Kernel f) :
    EqualizerArrow C K ;; f = EqualizerArrow C K ;; limits.zero.ZeroArrow (equiv_Zero2 Z) a b.
  Proof.
    set (tmp := EqualizerArrowEq C K).
    set (tmp1 := equiv_ZeroArrow a b Z).
    apply pathsinv0 in tmp1.
    apply (maponpaths (fun h : _ => EqualizerArrow C K ;; h)) in tmp1.
    set (tmp2 := pathscomp0 tmp tmp1).
    apply tmp2.
  Qed.

  Lemma equiv_Kernel2_isEqualizer {a b : C} (f : C⟦a, b⟧) (K : Kernel f) :
    isEqualizer C f (limits.zero.ZeroArrow (equiv_Zero2 Z) a b)
                (EqualizerObject C K) (EqualizerArrow C K) (equiv_Kernel2_eq f K).
  Proof.
    use mk_isEqualizer. apply hs.
    intros w h H.
    use unique_exists.
    (* Construction of the morphism *)
    - use EqualizerIn.
      + exact h.
      + rewrite precomp_with_ZeroArrow.
        rewrite limits.zero.ZeroArrow_comp_right in H.
        use (pathscomp0 H).
        apply (equiv_ZeroArrow w b Z).
    (* Commutativity *)
    - use EqualizerArrowComm.
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y T. cbn in T.
      use EqualizerInUnique. exact T.
  Qed.

  Definition equiv_Kernel2 {a b : C} (f : C⟦a, b⟧) :
    limits.kernels.Kernel (equiv_Zero2 Z) f <- Kernel f.
  Proof.
    intros K.
    exact (equiv_Equalizer2
           C hs f _
           (@mk_Equalizer
              C a b f _ (EqualizerObject C K)
              (EqualizerArrow C K)
              (equiv_Kernel2_eq f K)
              (equiv_Kernel2_isEqualizer f K))).
  Defined.

End def_kernels.
