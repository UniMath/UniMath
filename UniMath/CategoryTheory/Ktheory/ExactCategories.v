(** Exact categories *)

Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.limits.zero.
Require Export UniMath.CategoryTheory.limits.kernels.
Require Export UniMath.CategoryTheory.limits.cokernels.
Require Export UniMath.CategoryTheory.limits.pullbacks.
Require Export UniMath.CategoryTheory.limits.pushouts.
Require Export UniMath.CategoryTheory.limits.BinDirectSums.
Require Export UniMath.CategoryTheory.CategoriesWithBinOps.
Require Export UniMath.CategoryTheory.Categories.
Require Export UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Export UniMath.CategoryTheory.PreAdditive.
Require Export UniMath.CategoryTheory.Additive.
Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.Propositions.
Require Export UniMath.Algebra.Monoids_and_Groups.

Local Arguments to_Pr1 {_ _ _} _.
Local Arguments to_Pr2 {_ _ _} _.
Local Arguments to_In1 {_ _ _} _.
Local Arguments to_In2 {_ _ _} _.

Local Open Scope logic.

Delimit Scope addcat with addcat. (* move upstream *)

Notation "a --> b" := (to_abgr a b) : addcat.
Notation "C ⟦ a , b ⟧" := (@to_abgr C a b) : addcat.
Notation "f · g" := (compose f g : to_abgr _ _) : addcat.
Notation "0" := (ZeroArrow (to_Zero _) _ _) : cat.
Notation "0" := (unel _ : to_abgr _ _) : addcat.
Notation "1" := (identity _ : to_abgr _ _) : addcat.
Notation "f = g" := (eqset f g) : addcat.
Notation "f - g" := (@op _ f (grinv _ g) : to_abgr _ _) : addcat.
Notation "A ⊕ B" := (to_BinDirectSums _ A B) : addcat.

Local Open Scope cat.
Local Open Scope Cat.

Definition ShortSequence (M : Additive) := ∑ (A B C:M), A --> B × B --> C.
Section ShortSequenceAccessorFunctions.
  Context {M : Additive}.
  Definition SS_left (P : ShortSequence M) : M := pr1 P.
  Definition SS_middle (P : ShortSequence M) : M := pr12 P.
  Definition SS_right (P : ShortSequence M) : M := pr122 P.
  Definition SS_leftmap (P : ShortSequence M) : SS_left P --> SS_middle P := pr1 (pr222 P).
  Definition SS_rightmap (P : ShortSequence M) : SS_middle P --> SS_right P := pr2 (pr222 P).
End ShortSequenceAccessorFunctions.

Local Open Scope addmonoid.
Local Open Scope addcat.
Import AddNotation.

Section AdditiveCategories.     (* maybe move upstream *)
  Context {M : Additive}.
  (** Reprove some standard facts with the 0 map (the zero element of the group)
      replacing the zero map (defined by composing maps to and from the zero object). *)
  Lemma ZeroArrow_comp_left' (a b c : M) (f : b --> c) : (0 : a --> b) · f = 0.
  Proof.
    refine (_ @ ZeroArrow_comp_left M (to_Zero M) a b c f @ _).
    - apply (maponpaths (λ g, g · f)). apply PreAdditive_unel_zero.
    - apply pathsinv0, PreAdditive_unel_zero.
  Defined.
  Lemma ZeroArrow_comp_right' (a b c : M) (f : a --> b) : f · (0 : b --> c) = 0.
  Proof.
    refine (_ @ ZeroArrow_comp_right M (to_Zero M) a b c f @ _).
    - apply maponpaths, PreAdditive_unel_zero.
    - apply pathsinv0, PreAdditive_unel_zero.
  Defined.
  Definition leftComp (a b c : M) (f : a --> b) : (b --> c) -> (a --> c)
    := λ g, f · g.
  Definition rightComp (a b c : M) (f : b --> c) : (a --> b) -> (a --> c)
    := λ g, g · f.
  Lemma leftCompHomo (a b c : M) (f : a --> b) : ismonoidfun (leftComp a b c f).
  Proof.
    split.
    - intros g h. apply to_premor_linear'.
    - apply ZeroArrow_comp_right'.
  Defined.
  Lemma rightCompHomo (a b c : M) (f : b --> c) : ismonoidfun (rightComp a b c f).
  Proof.
    split.
    - intros g h. apply to_postmor_linear'.
    - apply ZeroArrow_comp_left'.
  Defined.
  Definition isKernel' {x y z : M} (f : x --> y) (g : y --> z) (H : f · g = 0) : hProp :=
    ∀ (w : M) (h : w --> y) (H : h · g = 0), ∃! φ : w --> x, φ · f = h.
  Definition isCokernel' {x y z : M} (f : x --> y) (g : y --> z) (H : f · g = 0) : hProp :=
    ∀ (w : M) (h : y --> w) (H : f · h = 0), ∃! φ : z --> w, g · φ = h.

  (** Now for something new.  *)

  Definition toShortSequence {A B C:M} (f : A --> B) (g : B --> C) : ShortSequence M
    := A,,B,,C,,f,,g.
  Definition standardSplitShortSequence (A B:M) : ShortSequence M
    := toShortSequence (to_In1 _ : A --> (A ⊕ B)) (to_Pr2 _ : (A ⊕ B) --> B).
  Definition isKernelCokernelPair {A B C:M} (i : A --> B) (p: B --> C) : hProp.
  Proof.
    exists (∑ (ip : i · p = 0), isKernel' i p ip ∧ isCokernel' i p ip).
    apply (isofhleveltotal2 1).
    - apply setproperty.
    - intro ip. apply propproperty.
  Defined.
  Lemma kerCokerDirectSum {A B:M} (S:BinDirectSum M A B) : isKernelCokernelPair (to_In1 S) (to_Pr2 S).
  Proof.
    assert (E := BinDirectSum_isBinDirectSum M S).
    use tpair.
    - exact (to_Unel1 M S).
    - cbn beta. split.
      * intros T h H. use unique_exists; cbn beta.
        + exact (h · to_Pr1 _).
        + rewrite <- assoc. refine (_ @ id_right h). rewrite <- (to_BinOpId _ S).
          rewrite to_premor_linear'. rewrite (assoc h (to_Pr2 S) (to_In2 S)).
          rewrite H; clear H.
          rewrite ZeroArrow_comp_left'.
          exact (! runax _ (h · (to_Pr1 S · to_In1 S))).
        + intros k. apply to_has_homsets.
        + clear H. intros k e. induction e. rewrite <- assoc.
          rewrite (to_IdIn1 M S). apply pathsinv0, id_right.
      * intros T h H. use unique_exists; cbn beta.
        + exact (to_In2 _ · h).
        + rewrite assoc. refine (_ @ id_left h). rewrite <- (to_BinOpId _ S).
          rewrite to_postmor_linear'.
          rewrite <- (assoc (to_Pr1 S) (to_In1 S) h). rewrite H; clear H.
          rewrite ZeroArrow_comp_right'.
          exact (! lunax _ (to_Pr2 S · to_In2 S · h)).
        + intros k. apply to_has_homsets.
        + clear H. intros k e. induction e. rewrite assoc. rewrite (to_IdIn2 M S).
          apply pathsinv0, id_left.
  Defined.
  Definition TrivialDirectSum (Z:Zero M) (A:M) : BinDirectSum M A Z.
  Proof.
    exists (A,,1,,0,,1,,0).
    repeat split; cbn.
    - apply id_right.
    - apply ArrowsToZero.
    - apply ArrowsToZero.
    - apply ArrowsFromZero.
    - rewrite id_right. rewrite ZeroArrow_comp_right'. rewrite rewrite_op.
      rewrite runax. reflexivity.
  Defined.
  Definition TrivialDirectSum' (Z:Zero M) (A:M) : BinDirectSum M Z A.
  Proof.
    exists (A,,0,,1,,0,,1).
    repeat split; cbn.
    - apply ArrowsToZero.
    - apply id_right.
    - apply ArrowsFromZero.
    - apply ArrowsToZero.
    - rewrite id_right. rewrite ZeroArrow_comp_right'. rewrite rewrite_op.
      rewrite lunax. reflexivity.
  Defined.
  Lemma kerCoker10 (Z:Zero M) (A:M) : isKernelCokernelPair (1 : A --> A) (0 : A --> Z).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum Z A)).
  Defined.
  Lemma kerCoker01 (Z:Zero M) (A:M) : isKernelCokernelPair (0 : Z --> A) (1 : A --> A).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum' Z A)).
  Defined.

End AdditiveCategories.

Delimit Scope excat with excat.
Local Open Scope excat.

Section theDefinition.
  Context (M:Additive) (E : ShortSequence M -> hProp).
  Definition isAdmissibleMonomorphism {A B:M} (i : A --> B) : hProp :=
    ∃ C (p : B --> C), E (A,,B,,C,,i,,p).
  Definition AdmissibleMonomorphism (A B:M) : Type :=
    ∑ (i : A --> B), isAdmissibleMonomorphism i.
  Coercion AdmMonoToMap {A B:M} : AdmissibleMonomorphism A B -> A --> B := pr1.
  Coercion AdmMonoToMap' {A B:M} : AdmissibleMonomorphism A B -> (A --> B)%cat := pr1.
  Notation "A ↣ B" := (AdmissibleMonomorphism A B) : excat.
  (* to input: type "\r->" or "\rightarrowtail" or "\r" with Agda input method *)
  Definition isAdmissibleEpimorphism {B C:M} (p : B --> C) : hProp :=
    ∃ A (i : A --> B), E (A,,B,,C,,i,,p).
  Definition AdmissibleEpimorphism (B C:M) : Type :=
    ∑ (p : B --> C), isAdmissibleMonomorphism p.
  Coercion AdmEpiToMap {B C:M} : AdmissibleEpimorphism B C -> B --> C := pr1.
  Coercion AdmEpiToMap' {B C:M} : AdmissibleEpimorphism B C -> (B --> C)%cat := pr1.
  Notation "B ↠ C" := (AdmissibleEpimorphism B C) : excat.
  (* to input: type "\rr-" or "\r" or "\twoheadrightarrow" with Agda input method *)
  Definition ShortSequenceIsomorphism (P Q : ShortSequence M) :=
    ∑ (f : iso (SS_left P) (SS_left Q))
      (g : iso (SS_middle P) (SS_middle Q))
      (h : iso (SS_right P) (SS_right Q)),
    f · SS_leftmap Q = SS_leftmap P · g  ×  g · SS_rightmap Q = SS_rightmap P · h.
  (** This is definition 2.1 from the paper of Bühler. *)
  Local Definition isExactFamily : hProp :=
      (∀ P Q, ShortSequenceIsomorphism P Q ⇒ E P ⇒ E Q) ∧
      (∀ A, isAdmissibleMonomorphism (identity A)) ∧
      (∀ A, isAdmissibleEpimorphism (identity A)) ∧
      (∀ P, E P ⇒ isKernelCokernelPair (SS_leftmap P) (SS_rightmap P)) ∧
      (∀ A B C (f : A ↣ B) (g : B ↣ C), isAdmissibleMonomorphism (f · g)) ∧
      (∀ A B C (f : A ↠ B) (g : B ↠ C), isAdmissibleEpimorphism (f · g)) ∧
      (∀ A B C (f : A ↠ B) (g : C --> B), ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)) ∧
      (∀ A B C (f : B ↣ A) (g : B --> C), ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO)).
End theDefinition.

Definition ExactCategory := ∑ (M:Additive) (E : @ShortSequence M -> hProp), @isExactFamily M E.
Coercion ExCatToAddCat (E:ExactCategory) : Additive := pr1 E.

Definition isExact {E : ExactCategory} : ShortSequence E -> hProp := pr12 E.

Notation "A ↣ B" := (AdmissibleMonomorphism _ isExact A B) : excat.
Notation "B ↠ C" := (AdmissibleEpimorphism _ isExact B C) : excat.

Arguments ShortSequenceIsomorphism {_}.
Arguments isAdmissibleMonomorphism {_ _ _ _}.
Arguments isAdmissibleEpimorphism {_ _ _ _}.

Section ExactCategoryAccessFunctions.
  Context {M:ExactCategory}.
  Definition EC_IsomorphicToExact
    : ∀ (P Q:ShortSequence M), ShortSequenceIsomorphism P Q ⇒ isExact P ⇒ isExact Q
    := pr122 M.
  Definition EC_IdentityIsMono
    : ∀ (A:M), isAdmissibleMonomorphism (identity A)
    := pr122 (pr2 M).
  Definition EC_IdentityIsEpi
    : ∀ (A:M), isAdmissibleEpimorphism (identity A)
    := pr122 (pr22 M).
  Definition EC_ExactToKernelCokernel
    : ∀ (P : ShortSequence M), isExact P ⇒ isKernelCokernelPair (SS_leftmap P) (SS_rightmap P)
    := pr122 (pr222 M).
  Definition EC_ComposeMono
    : ∀ (A B C:M) (f : A ↣ B) (g : B ↣ C), isAdmissibleMonomorphism (f · g)
    := pr122 (pr222 (pr2 M)).
  Definition EC_ComposeEpi
    : ∀ (A B C:M) (f : A ↠ B) (g : B ↠ C), isAdmissibleEpimorphism (f · g)
    := pr122 (pr222 (pr22 M)).
  Definition EC_PullbackEpi
    : ∀ (A B C:M) (f : A ↠ B) (g : C --> B), ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)
    := pr122 (pr222 (pr222 M)).
  Definition EC_PushoutMono
    : ∀ (A B C:M) (f : B ↣ A) (g : B --> C), ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO)
    := pr222 (pr222 (pr222 M)).
End ExactCategoryAccessFunctions.

Section ShortExactSequences.
  Context (M:ExactCategory).
  Definition ShortExactSequence := ∑ (P : ShortSequence M), isExact P.
  Coercion ShortExactSequenceToShortSequence (P : ShortExactSequence) : ShortSequence M := pr1 P.
End ShortExactSequences.

Section ShortExactSequencesAccessorFunctions.
  Context {M:ExactCategory} (P : ShortExactSequence M).
  Definition ES_ExactToKernelCokernel
    : isKernelCokernelPair (SS_leftmap P) (SS_rightmap P)
    := EC_ExactToKernelCokernel P (pr2 P).
End ShortExactSequencesAccessorFunctions.

Section ExactCategoryProperties.
  Context {M : ExactCategory}.
  (** Now prove one of the properties in Quillen's definition.  *)
  Lemma splitIsExact (A B:M) : isExact (standardSplitShortSequence A B).
  Proof.
  Abort.
End ExactCategoryProperties.
