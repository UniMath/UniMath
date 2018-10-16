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

Delimit Scope excat with excat.

Notation "a --> b" := (to_abgrop a b) : addcat.

Notation "C ⟦ a , b ⟧" := (to_abgrop (PA:=C) a b) : addcat.

Notation "f · g" := (compose f g : to_abgrop _ _) : addcat.

Notation "0" := (AdditiveZeroArrow _ _ : to_abgrop _ _) : addcat.

Notation "1" := (identity _ : to_abgrop _ _) : addcat.

Notation "f = g" := (eqset f g) : addcat.

Notation "f - g" := (@op _ f (grinv _ g) : to_abgrop _ _) : addcat.

Notation "A ++ B" := (BinDirectSumOb _ (to_BinDirectSums _ A B)) : addcat.

Reserved Notation "A ↣ B" (at level 50). (* move upstream to Init.v *)
(* to input: type "\r->" or "\rightarrowtail" or "\r" with Agda input method *)

Reserved Notation "B ↠ C" (at level 50). (* move upstream to Init.v *)
(* to input: type "\rr-" or "\r" or "\twoheadrightarrow" with Agda input method *)

Section MoveUpstream.

  Local Open Scope cat.

  Context {C : precategory} {hs : has_homsets C} {Z : Zero C}.

  Definition isKernel' {x y z : C} (f : x --> y) (g : y --> z) (H : f · g = ZeroArrow Z x z) : hProp :=
    ∀ (w : C) (h : w --> y) (H : h · g = ZeroArrow Z w z), ∃! φ : w --> x, φ · f = h.

  Definition isCokernel' {x y z : C} (f : x --> y) (g : y --> z) (H : f · g = (ZeroArrow Z x z)) : hProp :=
    ∀ (w : C) (h : y --> w) (H : f · h = ZeroArrow Z x w), ∃! φ : z --> w, g · φ = h.

End MoveUpstream.

Local Open Scope addmonoid_scope.
Local Open Scope addcat.

Section AdditiveCategories'.     (* maybe move upstream *)

  Context (M : Additive).

  Definition ShortSequence := ∑ (A B C:M), A --> B × B --> C.

End AdditiveCategories'.

Section AdditiveCategories.     (* maybe move upstream *)

  Context {M : Additive}.

  Definition toShortSequence {A B C:M} (f : A --> B) (g : B --> C) : ShortSequence M
    := A,,B,,C,,f,,g.

  Definition standardSplitShortSequence (A B:M) : ShortSequence M
    := toShortSequence (to_In1 _ _ : A --> (A ++ B)) (to_Pr2 _ _ : (A ++ B) --> B).

  Context (Zero := to_Zero M).

  (* some sanity checks for our notations *)

  Goal ∏ (a b:M), hSet.
    intros. exact (a --> b).
  Defined.

  Goal ∏ (a b:M) (f g : a --> b), hProp.
    intros. exact (f = g).
  Defined.

  Goal ∏ (a b:M) (f : a --> b), hProp.
    intros. exact (f = 0).
  Defined.

  Goal ∏ (a b:M) (f : a --> b), hProp.
    intros. exact (0 = f).
  Defined.

  Goal ∏ (a b:M) (f g : a --> b), a --> b.
    intros. exact (f + g).
  Defined.

  Goal ∏ (a b:M) (f g : a --> b), a --> b.
    intros. exact (f - g).
  Defined.

  Definition isKernelCokernelPair {A B C:M} (i : A --> B) (p: B --> C) : hProp.
  Proof.
    exists (∑ (ip : i · p = 0), isKernel' i p ip ∧ isCokernel' i p ip).
    apply (isofhleveltotal2 1).
    - apply setproperty.
    - intro ip. apply propproperty.
  Defined.

  Lemma kerCoker10 (A:M) : isKernelCokernelPair (1 : A --> A) (0 : A --> Zero).
  Proof.
  Abort.

  Lemma kerCoker01 (A:M) : isKernelCokernelPair (0 : Zero --> A) (1 : A --> A).
  Proof.
  Abort.

  Lemma kerCokerSum (A B:M) : isKernelCokernelPair (to_In1 _ _ : A --> (A ++ B)) (to_Pr2 _ _ : (A ++ B) --> B).
  Proof.
  Abort.

  (* Lemma kerCokerDirsum *)
  (*       {A B C:M} (i : A --> B) (p : B --> C) *)
  (*       {A' B' C':M} (i' : A' --> B') (p' : B' --> C') : *)
  (*   isKernelCokernelPair (i ++ i') (p ++ p'). *)
  (* Proof. *)
  (* Abort. *)

  Definition left (P : ShortSequence M) : M := pr1 P.
  Definition middle (P : ShortSequence M) : M := pr12 P.
  Definition right (P : ShortSequence M) : M := pr122 P.
  Definition leftmap (P : ShortSequence M) : left P --> middle P := pr1 (pr222 P).
  Definition rightmap (P : ShortSequence M) : middle P --> right P := pr2 (pr222 P).

End AdditiveCategories.

Local Open Scope excat.

Section theDefinition.

  Context (M:Additive).

  Context (Zero := to_Zero M).

  Context (E : ShortSequence M -> hProp).

  Definition isAdmissibleMonomorphism {A B:M} (i : A --> B) : hProp :=
    ∃ C (p : B --> C), E (A,,B,,C,,i,,p).

  Definition AdmissibleMonomorphism (A B:M) : hSet :=
    (∑ (i : A --> B), isAdmissibleMonomorphism i) % set.

  Definition AdmMonoToMap {A B:M} : AdmissibleMonomorphism A B -> A --> B := pr1.

  Notation "A ↣ B" := (AdmissibleMonomorphism A B) : excat.
  (* to input: type "\r->" or "\rightarrowtail" or "\r" with Agda input method *)

  Definition isAdmissibleEpimorphism {B C:M} (p : B --> C) : hProp :=
    ∃ A (i : A --> B), E (A,,B,,C,,i,,p).

  Definition AdmissibleEpimorphism (B C:M) : hSet :=
    (∑ (p : B --> C), isAdmissibleMonomorphism p) % set.

  Definition AdmEpiToMap {B C:M} : AdmissibleEpimorphism B C -> B --> C := pr1.

  Notation "B ↠ C" := (AdmissibleEpimorphism B C) : excat.
  (* to input: type "\rr-" or "\r" or "\twoheadrightarrow" with Agda input method *)

  Definition ShortSequenceIsomorphism (P Q : ShortSequence M) :=
    ∑ (f : iso (left P) (left Q))
      (g : iso (middle P) (middle Q))
      (h : iso (right P) (right Q)),
    f · leftmap Q = leftmap P · g  ×  g · rightmap Q = rightmap P · h.

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
      (∀ A B C (f : A ↣ B) (g : B ↣ C), isAdmissibleMonomorphism (AdmMonoToMap f · AdmMonoToMap g))
      ∧
      (∀ A B C (f : A ↠ B) (g : B ↠ C), isAdmissibleEpimorphism (AdmEpiToMap f · AdmEpiToMap g))
      ∧
      (∀ A B C (f : A ↠ B) (g : C --> B),
          ∃ (pb : Pullback (AdmEpiToMap f) g), isAdmissibleEpimorphism (PullbackPr2 pb))
      ∧
      (∀ A B C (f : B ↣ A) (g : B --> C),
          ∃ (po : Pushout (AdmMonoToMap f) g), isAdmissibleMonomorphism (PushoutIn2 po)).

End theDefinition.

Definition ExactCategory := ∑ (M:Additive) (E : @ShortSequence M -> hProp), @isExactFamily M E.

Definition ExCatToAddCat : ExactCategory -> Additive := pr1.

Coercion ExCatToAddCat : ExactCategory >-> Additive.

Definition isExact {M : ExactCategory} : ShortSequence M -> hProp := pr12 M.

Notation "A ↣ B" := (AdmissibleMonomorphism _ isExact A B) : excat.
(* to input: type "\r->" or "\rightarrowtail" or "\r" with Agda input method *)

Notation "B ↠ C" := (AdmissibleEpimorphism _ isExact B C) : excat.
(* to input: type "\rr-" or "\r" or "\twoheadrightarrow" with Agda input method *)

Section ExactCategoryProperties.

  Context {M : ExactCategory}.

  Goal ∏ (a b:M), hSet.
    intros. exact (a ↣ b).
  Defined.

  Goal ∏ (a b:M), hSet.
    intros. exact (a ↠ b).
  Defined.

  (** Now prove one of the properties in Quillen's definition.  *)

  Lemma splitIsExact (A B:M) : isExact (standardSplitShortSequence A B).
  Proof.

  Abort.

End ExactCategoryProperties.
