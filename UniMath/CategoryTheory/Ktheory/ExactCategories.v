(** Exact categories *)

Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.limits.zero.
Require Export UniMath.CategoryTheory.limits.kernels.
Require Export UniMath.CategoryTheory.limits.cokernels.
Require Export UniMath.CategoryTheory.limits.pullbacks.
Require Export UniMath.CategoryTheory.limits.pushouts.
Require Export UniMath.CategoryTheory.limits.BinDirectSums.
Require Export UniMath.CategoryTheory.Categories.
Require Export UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Export UniMath.CategoryTheory.PreAdditive.
Require Export UniMath.CategoryTheory.Additive.
Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.Propositions.
Require Export UniMath.Algebra.Monoids_and_Groups.

Local Open Scope logic.

Delimit Scope addcat with addcat.

Notation "a --> b" := (to_abgrop a b) : addcat.

Notation "C ⟦ a , b ⟧" := (to_abgrop (PA:=C) a b) : addcat.

Notation "f · g" := (compose f g : to_abgrop _ _) : addcat.

Notation "f = g" := (eqset f g) : addcat.

Section MoveUpstream.

  Local Open Scope cat.

  Context {C : precategory} {hs : has_homsets C} {Z : Zero C}.

  Definition isKernel' {x y z : C} (f : x --> y) (g : y --> z) (H : f · g = ZeroArrow Z x z) : hProp :=
    ∀ (w : C) (h : w --> y) (H : h · g = ZeroArrow Z w z), ∃! φ : w --> x, φ · f = h.

  Definition isCokernel' {x y z : C} (f : x --> y) (g : y --> z) (H : f · g = (ZeroArrow Z x z)) : hProp :=
    ∀ (w : C) (h : y --> w) (H : f · h = ZeroArrow Z x w), ∃! φ : z --> w, g · φ = h.

End MoveUpstream.

Section theDefinition.

  Context (M:Additive).

  Local Open Scope addcat.

  Goal ∏ (a b:M), hSet.
    intros. exact (a --> b).
  Defined.

  Goal ∏ (a b:M) (f g : a --> b), hProp.
    intros. exact (f = g).
  Defined.

  Context (Z := to_Zero M).

  Context (dirsum : BinDirectSums M := to_BinDirectSums M).

  Local Notation zero := (ZeroArrow Z _ _ : _ --> _).

  Goal ∏ (a b:M) (f : a --> b), hProp.
    intros. exact (f = zero).
  Defined.

  Goal ∏ (a b:M) (f : a --> b), hProp.
    intros. exact (zero = f).
  Defined.

  Definition ShortSequence := ∑ (A B C:M), A --> B × B --> C.

  Definition left (P : ShortSequence) : M := pr1 P.
  Definition middle (P : ShortSequence) : M := pr12 P.
  Definition right (P : ShortSequence) : M := pr122 P.
  Definition leftmap (P : ShortSequence) : left P --> middle P := pr1 (pr222 P).
  Definition rightmap (P : ShortSequence) : middle P --> right P := pr2 (pr222 P).

  Context (E : ShortSequence -> hProp).

  Definition isAdmissibleMonomorphism {A B:M} (i : A --> B) : hProp :=
    ∃ C (p : B --> C), E (A,,B,,C,,i,,p).

  Definition isAdmissibleEpimorphism {B C:M} (p : B --> C) : hProp :=
    ∃ A (i : A --> B), E (A,,B,,C,,i,,p).

  Definition ShortSequenceIsomorphism (P Q : ShortSequence) :=
    ∑ (f : iso (left P) (left Q))
      (g : iso (middle P) (middle Q))
      (h : iso (right P) (right Q)),
    f · leftmap Q = leftmap P · g  ×  g · rightmap Q = rightmap P · h.

  Definition isKernelCokernelPair {A B C:M} (i : A --> B) (p: B --> C) : hProp.
  Proof.
    exists (∑ (ip : i · p = zero), isKernel' i p ip ∧ isCokernel' i p ip).
    apply (isofhleveltotal2 1).
    - Set Printing All.
      apply setproperty.
    - intros e. apply propproperty.
  Defined.

  (** This is definition 2.1 from the paper of Bühler. *)
  Local Definition isExactFamily : hProp :=
      (∀ P Q, ShortSequenceIsomorphism P Q ⇒ E P ⇒ E Q)
      ∧
      (∀ A, isAdmissibleMonomorphism (identity A))
      ∧
      (∀ A, isAdmissibleEpimorphism (identity A))
      ∧
      (∀ P, E P ⇒ isKernelCokernelPair (leftmap P) (rightmap P))
      ∧
      (∀ A B C (f : A --> B) (g : B --> C),
       isAdmissibleMonomorphism f ⇒ isAdmissibleMonomorphism g ⇒ isAdmissibleMonomorphism (f · g))
      ∧
      (∀ A B C (f : A --> B) (g : B --> C),
       isAdmissibleEpimorphism f ⇒ isAdmissibleEpimorphism g ⇒ isAdmissibleEpimorphism (f · g))
      ∧
      (∀ A B C (f : A --> B) (g : C --> B),
       isAdmissibleEpimorphism f ⇒ ∃ (pb : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 pb))
      ∧
      (∀ A B C (f : B --> A) (g : B --> C),
       isAdmissibleMonomorphism f ⇒ ∃ (po : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 po)).

  Context (ie : isExactFamily).

  Definition standardSplitShortSequence (A B:M) : ShortSequence.
  Proof.
    set (SUM := dirsum A B).
    set (C := BinDirectSumOb _ SUM).
    set (in1 := to_In1 _ SUM).
    set (pr2 := to_Pr2 _ SUM).
    exact (A,,C,,B,,in1,,pr2).
  Defined.

  (** Now prove one of the properties in Quillen's definition.  *)

  Lemma splitIsExact (A B:M) : E (standardSplitShortSequence A B).
  Proof.
  Abort.

End theDefinition.

Definition ExactCategory := ∑ (M:Additive) (E : ShortSequence M -> hProp), isExactFamily M E.
