(** * Cokernels defined in terms of colimits. *)
(** ** Contents
- Definition coincides with direct definition
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.limits.graphs.zero.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.cokernels.


(** * Definition of cokernels in terms of colimits *)
Section def_cokernels.

  Variable C : precategory.
  Variable hs: has_homsets C.
  Variable Z : Zero C.

  Definition Cokernel {a b : C} (f : C⟦a, b⟧) := Coequalizer C f (ZeroArrow Z a b).

  (** ** Coincides with the direct definiton *)
  Lemma equiv_Cokernel1_eq {a b : C} (f : C⟦a, b⟧)
        (CK : limits.cokernels.Cokernel (equiv_Zero2 Z) f) :
    f · (CokernelArrow CK) = ZeroArrow Z a b · (CokernelArrow CK).
  Proof.
    rewrite CokernelCompZero. rewrite postcomp_with_ZeroArrow. apply equiv_ZeroArrow.
  Qed.

  Lemma equiv_Cokernel1_isCoequalizer {a b : C} (f : C⟦a, b⟧)
        (CK : limits.cokernels.Cokernel (equiv_Zero2 Z) f) :
    isCoequalizer C f (ZeroArrow Z a b) CK (CokernelArrow CK) (equiv_Cokernel1_eq f CK).
  Proof.
    use (make_isCoequalizer _ hs).
    intros w h H.
    use unique_exists.
    (* Construction of the morphism *)
    - use CokernelOut.
      + exact h.
      + rewrite postcomp_with_ZeroArrow in H.
        use (pathscomp0 _ (!(equiv_ZeroArrow a w Z))).
        exact H.
    (* Commutativity *)
    - use CokernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y T. cbn in T.
      use CokernelOutsEq. unfold CokernelArrow.
      use (pathscomp0 T). apply pathsinv0.
      use CokernelCommutes.
  Qed.

  Definition equiv_Cokernel1 {a b : C} (f : C⟦a, b⟧)
             (CK : limits.cokernels.Cokernel (equiv_Zero2 Z) f) : Cokernel f.
  Proof.
    use make_Coequalizer.
    - exact CK.
    - exact (CokernelArrow CK).
    - exact (equiv_Cokernel1_eq f CK).
    - exact (equiv_Cokernel1_isCoequalizer f CK).
  Defined.

  (* Other direction *)


  Lemma equiv_Cokernel2_eq {a b : C} (f : C⟦a, b⟧) (CK : cokernels.Cokernel (equiv_Zero2 Z) f) :
    f · CokernelArrow CK = ZeroArrow Z a b · CokernelArrow CK.
  Proof.
    rewrite CokernelCompZero. rewrite postcomp_with_ZeroArrow. apply equiv_ZeroArrow.
  Qed.

  Lemma equiv_Cokernel2_isCoequalizer {a b : C} (f : C⟦a, b⟧)
        (CK : cokernels.Cokernel (equiv_Zero2 Z) f) :
    isCoequalizer C f (ZeroArrow Z a b) CK (CokernelArrow CK) (equiv_Cokernel2_eq f CK).
  Proof.
    use (make_isCoequalizer _ hs).
    intros w h H.
    use unique_exists.
    (* Construction of the morphism *)
    - use CokernelOut.
      + exact h.
      + use (pathscomp0 H). apply pathsinv0. rewrite postcomp_with_ZeroArrow. apply equiv_ZeroArrow.
    (* Commutativity *)
    - use CokernelCommutes.
    (* Equality on equalities of morphisms *)
    - intros y. apply hs.
    (* Uniqueness *)
    - intros y T. cbn in T. use CokernelOutsEq. rewrite T. rewrite CokernelCommutes.
      apply idpath.
  Qed.

  Definition equiv_Cokernel2 {a b : C} (f : C⟦a, b⟧)
             (CK : limits.cokernels.Cokernel (equiv_Zero2 Z) f) : Cokernel f.
  Proof.
    use make_Coequalizer.
    - exact CK.
    - exact (CokernelArrow CK).
    - exact (equiv_Cokernel2_eq f CK).
    - exact (equiv_Cokernel2_isCoequalizer f CK).
  Defined.

End def_cokernels.
