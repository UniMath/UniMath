(** * Cokernels defined in terms of colimits. *)
(** ** Contents
- Definition coincides with direct definition
*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.zero.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.cokernels.


(** * Definition of cokernels in terms of colimits *)
Section def_cokernels.

  Variable C : precategory.
  Variable hs: has_homsets C.
  Variable Z : Zero C.

  Definition Cokernel {a b : C} (f : C⟦a, b⟧)
    := Coequalizer C f (ZeroArrow Z a b).

  (** ** Coincides with the direct definiton *)
  Lemma equiv_Cokernel1_eq {a b : C} (f : C⟦a, b⟧)
        (K : limits.cokernels.Cokernel (equiv_Zero2 Z) f) :
    f ;; limits.coequalizers.CoequalizerArrow K
    = ZeroArrow Z a b ;; limits.coequalizers.CoequalizerArrow K.
  Proof.
    set (tmp := limits.coequalizers.CoequalizerEqAr K).
    set (tmp1 := equiv_ZeroArrow a b Z).
    apply (maponpaths (fun h : _ => h ;; limits.coequalizers.CoequalizerArrow K))
      in tmp1.
    set (tmp2 := pathscomp0 tmp tmp1).
    apply tmp2.
  Qed.

  Lemma equiv_Cokernel1_isCoequalizer {a b : C} (f : C⟦a, b⟧)
        (K : limits.cokernels.Cokernel (equiv_Zero2 Z) f) :
    limits.coequalizers.isCoequalizer
      f (ZeroArrow Z a b) (limits.coequalizers.CoequalizerArrow K)
      (equiv_Cokernel1_eq f K).
  Proof.
    use limits.coequalizers.mk_isCoequalizer.
    intros w h H.
    use unique_exists.

    (* Construction of the morphism *)
    - use limits.cokernels.CokernelOut.
      + exact h.
      + rewrite postcomp_with_ZeroArrow in H.
        use (pathscomp0 _ (!(equiv_ZeroArrow a w Z))).
        exact H.

    (* Commutativity *)
    - use limits.cokernels.CokernelCommutes.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. cbn in T.
      use limits.cokernels.CokernelOutsEq. unfold CokernelArrow.
      use (pathscomp0 T). apply pathsinv0.
      use limits.cokernels.CokernelCommutes.
  Qed.

  Definition equiv_Cokernel1 {a b : C} (f : C⟦a, b⟧) :
    limits.cokernels.Cokernel (equiv_Zero2 Z) f -> Cokernel f.
  Proof.
    intros K.
    exact (equiv_Coequalizer1
           C hs f _
           (@limits.coequalizers.mk_Coequalizer
              C a b K f _
              (limits.coequalizers.CoequalizerArrow K)
              (equiv_Cokernel1_eq f K)
              (equiv_Cokernel1_isCoequalizer f K))).
  Defined.

  (* Other direction *)

  Lemma equiv_Cokernel2_eq {a b : C} (f : C⟦a, b⟧) (K : Cokernel f ) :
    f ;; CoequalizerArrow C K
    = limits.zero.ZeroArrow C (equiv_Zero2 Z) a b ;; CoequalizerArrow C K.
  Proof.
    set (tmp := CoequalizerArrowEq C K).
    set (tmp1 := equiv_ZeroArrow a b Z).
    apply pathsinv0 in tmp1.
    apply (maponpaths (fun h : _ => h ;; CoequalizerArrow C K)) in tmp1.
    set (tmp2 := pathscomp0 tmp tmp1).
    apply tmp2.
  Qed.

  Lemma equiv_Cokernel2_isCoequalizer {a b : C} (f : C⟦a, b⟧)
        (K : Cokernel f ) :
    isCoequalizer C f (limits.zero.ZeroArrow C (equiv_Zero2 Z) a b)
                  (CoequalizerObject C K)
                  (CoequalizerArrow C K) (equiv_Cokernel2_eq f K).
  Proof.
    use mk_isCoequalizer. apply hs.
    intros w h H.
    use unique_exists.

    (* Construction of the morphism *)
    - use CoequalizerOut.
      + exact h.
      + rewrite postcomp_with_ZeroArrow.
        rewrite limits.zero.ZeroArrow_comp_left in H.
        use (pathscomp0 H).
        apply (equiv_ZeroArrow a w Z).

    (* Commutativity *)
    - use CoequalizerArrowComm.

    (* Equality on equalities of morphisms *)
    - intros y. apply hs.

    (* Uniqueness *)
    - intros y T. cbn in T.
      use CoequalizerOutUnique. exact T.
  Qed.

  Definition equiv_Cokernel2 {a b : C} (f : C⟦a, b⟧) :
    limits.cokernels.Cokernel (equiv_Zero2 Z) f <- Cokernel f.
  Proof.
    intros K.
    exact (equiv_Coequalizer2
           C hs f _
           (@mk_Coequalizer
              C a b f _ (CoequalizerObject C K)
              (CoequalizerArrow C K)
              (equiv_Cokernel2_eq f K)
              (equiv_Cokernel2_isCoequalizer f K))).
  Defined.

End def_cokernels.
