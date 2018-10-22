(** Exact categories *)

Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.Monics.
Require Export UniMath.CategoryTheory.Epis.
Require Export UniMath.CategoryTheory.limits.zero.
Require Export UniMath.CategoryTheory.limits.kernels.
Require Export UniMath.CategoryTheory.limits.cokernels.
Require Export UniMath.CategoryTheory.limits.binproducts.
Require Export UniMath.CategoryTheory.limits.pullbacks.
Require Export UniMath.CategoryTheory.limits.pushouts.
Require Export UniMath.CategoryTheory.limits.BinDirectSums.
Require Export UniMath.CategoryTheory.CategoriesWithBinOps.
Require Export UniMath.CategoryTheory.Categories.
Require Export UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Export UniMath.CategoryTheory.PreAdditive.
Require Export UniMath.CategoryTheory.Morphisms.
Require Export UniMath.CategoryTheory.Additive.
Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.Propositions.
Require Export UniMath.Algebra.Monoids_and_Groups.

Local Arguments BinDirectSum {_}.
Local Arguments to_Pr1 {_ _ _} _.
Local Arguments to_Pr2 {_ _ _} _.
Local Arguments to_In1 {_ _ _} _.
Local Arguments to_In2 {_ _ _} _.
Local Arguments MorphismPair : clear implicits.

Local Open Scope logic.

Delimit Scope addcat with addcat. (* move upstream *)

Notation "C ⟦ a , b ⟧" := (@to_abgr C a b) : addcat.
Notation "a --> b" := (to_abgr a b) : addcat.
Notation "f · g" := (compose f g : to_abgr _ _) : addcat.
Notation "0" := (ZeroArrow (to_Zero _) _ _) : cat.
Notation "0" := (unel _ : to_abgr _ _) : addcat.
Notation "1" := (identity _ : to_abgr _ _) : addcat.
Notation "f = g" := (eqset f g) : addcat.
Notation "f - g" := (@op _ f (grinv _ g) : to_abgr _ _) : addcat.
Notation "A ⊕ B" := (to_BinDirectSums _ A B) : addcat.

Local Open Scope cat.
Local Open Scope addmonoid.
Local Open Scope addcat.
Import AddNotation.

Section AdditiveCategories.     (* maybe move upstream *)
  Context {M : Additive}.
  (** Reprove some standard facts in additive categories with the 0 map (the zero element of the
      group) replacing the zero map (defined by composing maps to and from the zero object). *)
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
    := precomp_with f.
  Definition rightComp (a b c : M) (f : b --> c) : (a --> b) -> (a --> c)
    := postcomp_with f.
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
  Definition isKernel' {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : w --> y), h · g = 0 ⇒ ∃! φ : w --> x, φ · f = h.
  Definition isCokernel' {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : y --> w), f · h = 0 ⇒ ∃! φ : z --> w, g · φ = h.
  Lemma KernelIsMonic {x y z:M} (f : x --> y) (g : y --> z) : isKernel' f g -> isMonic f.
  Proof.
    intros [t i] w p q e.
    set (T := ∑ r : w --> x, r · f = q · f). assert (ic : isProofIrrelevant T).
    { apply proofirrelevance, isapropifcontr.
      use i. rewrite <- assoc. rewrite t. apply ZeroArrow_comp_right'. }
    set (t1 := (p,,e) : T). set (t2 := (q,,idpath _) : T).
    assert (Q := ic t1 t2). exact (maponpaths pr1 Q).
  Defined.
  Lemma CokernelIsEpi {x y z:M} (f : x --> y) (g : y --> z) : isCokernel' f g -> isEpi g.
  Proof.
    intros [t i] w p q e.
    set (T := ∑ r : z --> w, g · r = g · q). assert (ic : isProofIrrelevant T).
    { apply proofirrelevance, isapropifcontr.
      use i. rewrite assoc. rewrite t. apply ZeroArrow_comp_left'. }
    set (t1 := (p,,e) : T). set (t2 := (q,,idpath _) : T).
    assert (Q := ic t1 t2). exact (maponpaths pr1 Q).
  Defined.
  Definition IsoArrowTo   {A A' B:M} (g : A --> B) (g' : A' --> B) := ∑ i : iso A A', i · g' = g .
  Definition IsoArrowFrom {A B B':M} (g : A --> B) (g' : A --> B') := ∑ i : iso B B', g · i  = g'.
  Lemma IsoArrowTo_isaprop {A A' B:M} (g : A --> B) (g' : A' --> B) :
    isMonic g' -> isaprop (IsoArrowTo g g').
  Proof.
    intros i. apply invproofirrelevance; intros k k'. apply subtypeEquality'.
    - induction k as [[k K] e], k' as [[k' K'] e']; cbn; cbn in e, e'.
      induction (i A k k' (e @ !e')). apply maponpaths. apply isaprop_is_iso.
    - apply propproperty.
  Defined.
  Lemma IsoArrowFrom_isaprop {A B B':M} (g : A --> B) (g' : A --> B') :
     isEpi g -> isaprop (IsoArrowFrom g g').
  Proof.
    intros i. apply invproofirrelevance; intros k k'. apply subtypeEquality'.
    - induction k as [[k K] e], k' as [[k' K'] e']; cbn; cbn in e, e'.
      unfold isEpi in i.
      induction (i B' k k' (e @ !e')). apply maponpaths. apply isaprop_is_iso.
    - apply propproperty.
  Defined.
  Lemma KernelUniqueness {x x' y z : M} {f : x --> y} {f' : x' --> y} {g : y --> z} :
    isKernel' f g -> isKernel' f' g -> iscontr (IsoArrowTo f f').
  Proof.
    intros i j. apply iscontraprop1.
    - apply IsoArrowTo_isaprop. exact (KernelIsMonic f' g j).
    - induction (iscontrpr1 (pr2 j _ f (pr1 i))) as [p P].
      induction (iscontrpr1 (pr2 i _ f' (pr1 j))) as [q Q].
      assert (d : is_iso p).
      { apply is_iso_from_is_z_iso. exists q. split.
        - apply (KernelIsMonic _ _ i). rewrite <- assoc. rewrite Q. rewrite P. rewrite id_left. reflexivity.
        - apply (KernelIsMonic _ _ j). rewrite <- assoc. rewrite P. rewrite Q. rewrite id_left. reflexivity. }
      set (θ := isopair p d). exists θ. exact P.
  Defined.
  Lemma CokernelUniqueness {x y z z' : M} {f : x --> y} {g : y --> z} {g' : y --> z'} :
    isCokernel' f g -> isCokernel' f g' -> iscontr (IsoArrowFrom g g').
  Proof.
    intros i j. apply iscontraprop1.
    - apply IsoArrowFrom_isaprop. exact (CokernelIsEpi f g i).
    - induction (iscontrpr1 (pr2 j _ g (pr1 i))) as [p P].
      induction (iscontrpr1 (pr2 i _ g' (pr1 j))) as [q Q].
      assert (d : is_iso q).
      { apply is_iso_from_is_z_iso. exists p. split.
        - apply (CokernelIsEpi _ _ i). rewrite assoc. rewrite Q. rewrite P. rewrite id_right. reflexivity.
        - apply (CokernelIsEpi _ _ j). rewrite assoc. rewrite P. rewrite Q. rewrite id_right. reflexivity. }
      set (θ := isopair q d). exists θ. exact Q.
  Defined.
  Lemma DirectSumToPullback {A B:M} (S : BinDirectSum A B) (Z : Zero M) :
    Pullback (0 : A --> Z) (0 : B --> Z).
  Proof.
    use tpair.
    - exists S. exact (to_Pr1 S,, to_Pr2 S).
    - cbn. use tpair.
      + apply ArrowsToZero.
      + cbn. intros T f g e. exact (to_isBinProduct M S T f g).
  Defined.
  Lemma DirectSumToPushout {A B:M} (S : BinDirectSum A B) (Z : Zero M) :
    Pushout (0 : Z --> A) (0 : Z --> B).
  Proof.
    use tpair.
    - exists S. exact (to_In1 S,, to_In2 S).
    - cbn. use tpair.
      + apply ArrowsFromZero.
      + cbn. intros T f g e. exact (to_isBinCoproduct M S T f g).
  Defined.
End AdditiveCategories.

Section KernelCokernelPairs.
  Context {M : Additive}.
  Definition isKernelCokernelPair {A B C:M} (i : A --> B) (p: B --> C) : hProp
    := isKernel' i p ∧ isCokernel' i p.
  Lemma PairUniqueness1 {A A' B C:M} (i : A --> B) (i' : A' --> B) (p: B --> C) :
    isKernelCokernelPair i p -> isKernelCokernelPair i' p -> iscontr (IsoArrowTo i i').
  Proof.
    intros [k _] [k' _]. exact (KernelUniqueness k k').
  Defined.
  Lemma PairUniqueness2 {A B C C':M} (i : A --> B) (p: B --> C) (p': B --> C') :
    isKernelCokernelPair i p -> isKernelCokernelPair i p' -> iscontr (IsoArrowFrom p p').
  Proof.
    intros [_ c] [_ c']. exact (CokernelUniqueness c c').
  Defined.
  Lemma kerCokerDirectSum {A B:M} (S:BinDirectSum A B) : isKernelCokernelPair (to_In1 S) (to_Pr2 S).
  Proof.
    assert (E := BinDirectSum_isBinDirectSum M S).
    split.
    - exists (to_Unel1 M S). intros T h H. use unique_exists; cbn beta.
      + exact (h · to_Pr1 _).
      + rewrite <- assoc. refine (_ @ id_right h). rewrite <- (to_BinOpId _ S).
        rewrite to_premor_linear'. rewrite (assoc h (to_Pr2 S) (to_In2 S)).
        rewrite H; clear H.
        rewrite ZeroArrow_comp_left'.
        exact (! runax _ (h · (to_Pr1 S · to_In1 S))).
      + intros k. apply to_has_homsets.
      + clear H. intros k e. induction e. rewrite <- assoc.
        rewrite (to_IdIn1 M S). apply pathsinv0, id_right.
    - exists (to_Unel1 M S). intros T h H. use unique_exists; cbn beta.
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
  Definition TrivialDirectSum (Z:Zero M) (A:M) : BinDirectSum A Z.
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
  Definition TrivialDirectSum' (Z:Zero M) (A:M) : BinDirectSum Z A.
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
  Lemma kerCoker10 (Z:Zero M) (A:M) : isKernelCokernelPair (identity A) (0 : A --> Z).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum Z A)).
  Defined.
  Lemma kerCoker01 (Z:Zero M) (A:M) : isKernelCokernelPair (0 : Z --> A) (identity A).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum' Z A)).
  Defined.
End KernelCokernelPairs.

Delimit Scope preexcat with preexcat.
Local Open Scope preexcat.

Delimit Scope excat with excat.
Local Open Scope excat.

Section theDefinition.
  Definition AddCatWithExactness := ∑ M:Additive, MorphismPair M -> hProp. (* properties added below *)
  Coercion AE_to_AC (ME : AddCatWithExactness) : Additive := pr1 ME.
  Context (M : AddCatWithExactness).
  Definition isExact (E : MorphismPair M) : hProp := pr2 M E.
  Definition isAdmissibleMonomorphism {A B:M} (i : A --> B) : hProp :=
    ∃ C (p : B --> C), isExact (mk_MorphismPair i p).
  Definition AdmissibleMonomorphism (A B:M) : Type :=
    ∑ (i : A --> B), isAdmissibleMonomorphism i.
  Coercion AdmMonoToMap {A B:M} : AdmissibleMonomorphism A B -> A --> B := pr1.
  Coercion AdmMonoToMap' {A B:M} : AdmissibleMonomorphism A B -> (A --> B)%cat := pr1.
  Notation "A ↣ B" := (AdmissibleMonomorphism A B) : excat.
  Definition isAdmissibleEpimorphism {B C:M} (p : B --> C) : hProp :=
    ∃ A (i : A --> B), isExact (mk_MorphismPair i p).
  Definition AdmissibleEpimorphism (B C:M) : Type :=
    ∑ (p : B --> C), isAdmissibleEpimorphism p.
  Coercion AdmEpiToMap {B C:M} : AdmissibleEpimorphism B C -> B --> C := pr1.
  Coercion AdmEpiToMap' {B C:M} : AdmissibleEpimorphism B C -> (B --> C)%cat := pr1.
  Notation "B ↠ C" := (AdmissibleEpimorphism B C) : excat.
  Definition MorphismPairIsomorphism (P Q : MorphismPair M) :=
    ∑ (f : iso (Ob1 P) (Ob1 Q))
      (g : iso (Ob2 P) (Ob2 Q))
      (h : iso (Ob3 P) (Ob3 Q)),
    f · Mor1 Q = Mor1 P · g  ×  g · Mor2 Q = Mor2 P · h.
  (** This is definition 2.1 from the paper of Bühler. *)
  Local Definition ExactCategoryProperties : hProp :=
      (∀ P Q, MorphismPairIsomorphism P Q ⇒ isExact P ⇒ isExact Q) ∧
      (∀ A, isAdmissibleMonomorphism (identity A)) ∧
      (∀ A, isAdmissibleEpimorphism (identity A)) ∧
      (∀ P, isExact P ⇒ isKernelCokernelPair (Mor1 P) (Mor2 P)) ∧
      (∀ A B C (f : A ↣ B) (g : B ↣ C), isAdmissibleMonomorphism (f · g)) ∧
      (∀ A B C (f : A ↠ B) (g : B ↠ C), isAdmissibleEpimorphism (f · g)) ∧
      (∀ A B C (f : A ↠ B) (g : C --> B), ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)) ∧
      (∀ A B C (f : B ↣ A) (g : B --> C), ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO)).
End theDefinition.

Arguments isExact {_}.

Definition ExactCategory := ∑ (ME:AddCatWithExactness), ExactCategoryProperties ME.
Coercion ExCatToAddCatWithExactness (E:ExactCategory) : AddCatWithExactness := pr1 E.

Notation "A ↣ B" := (AdmissibleMonomorphism _ A B) : excat.
Notation "B ↠ C" := (AdmissibleEpimorphism _ B C) : excat.

Arguments MorphismPairIsomorphism {_}.
Arguments isAdmissibleMonomorphism {_ _ _}.
Arguments isAdmissibleEpimorphism {_ _ _}.

Section ExactCategoryAccessFunctions.
  Context {M:ExactCategory}.
  Definition EC_IsomorphicToExact
    : ∀ (P Q:MorphismPair M), MorphismPairIsomorphism P Q ⇒ isExact P ⇒ isExact Q
    := pr12 M.
  Definition EC_IdentityIsMono (A:M)
    : isAdmissibleMonomorphism (identity A)
    := pr122 M A.
  Definition EC_IdentityIsEpi (A:M)
    : isAdmissibleEpimorphism (identity A)
    := pr122 (pr2 M) A.
  Definition EC_ExactToKernelCokernel
    : ∀ (P : MorphismPair M), isExact P ⇒ isKernelCokernelPair (Mor1 P) (Mor2 P)
    := pr122 (pr22 M).
  Definition EC_ComposeMono
    : ∀ (A B C:M) (f : A ↣ B) (g : B ↣ C), isAdmissibleMonomorphism (f · g)
    := pr122 (pr222 M).
  Definition EC_ComposeEpi
    : ∀ (A B C:M) (f : A ↠ B) (g : B ↠ C), isAdmissibleEpimorphism (f · g)
    := pr122 (pr222 (pr2 M)).
  Definition EC_PullbackEpi {A B C:M} (f : A ↠ B) (g : C --> B) :
    ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)
    := pr122 (pr222 (pr22 M)) A B C f g.
  Definition EC_PushoutMono
    : ∀ (A B C:M) (f : B ↣ A) (g : B --> C), ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO)
    := pr222 (pr222 (pr22 M)).
End ExactCategoryAccessFunctions.

Section ShortExactSequences.
  Context (M:ExactCategory).
  Definition ShortExactSequence := ∑ (P : MorphismPair M), isExact P.
  Coercion ShortExactSequenceToMorphismPair (P : ShortExactSequence) : MorphismPair M := pr1 P.
End ShortExactSequences.

Section ShortExactSequencesAccessorFunctions.
  Context {M:ExactCategory} (P : ShortExactSequence M).
  Definition ES_ExactToKernelCokernel
    : isKernelCokernelPair (Mor1 P) (Mor2 P)
    := EC_ExactToKernelCokernel P (pr2 P).
End ShortExactSequencesAccessorFunctions.

Section ExactCategoryFacts.
  Context {M : ExactCategory}.
  Lemma ExactSequenceFromMono {A B C:M} (i : A --> B) (p : B --> C) :
    isCokernel' i p -> isAdmissibleMonomorphism i -> isExact (mk_MorphismPair i p).
  Proof.
    intros co mo.
    unfold isAdmissibleMonomorphism in mo.
    apply (squash_to_hProp mo); clear mo; intros [C' [p' e]].
    assert (co' := pr2 (EC_ExactToKernelCokernel _ e) : isCokernel' i p').
    assert (R := iscontrpr1 (CokernelUniqueness co' co)). induction R as [R r].
    use (EC_IsomorphicToExact _ _ _ e).
    exists (identity_iso _). exists (identity_iso _).
    use tpair; cbn.
    - exact R.
    - split.
      + exact (id_left _ @ ! id_right _).
      + exact (id_left _ @ ! r).
  Defined.
  Lemma ExactSequenceFromEpi {A B C:M} (i : A --> B) (p : B --> C) :
    isKernel' i p -> isAdmissibleEpimorphism p -> isExact (mk_MorphismPair i p).
  Proof.
    intros co mo.
    unfold isAdmissibleMonomorphism in mo.
    apply (squash_to_hProp mo); clear mo; intros [A' [i' e]].
    assert (co' := pr1 (EC_ExactToKernelCokernel _ e) : isKernel' i' p).
    assert (R := iscontrpr1 (KernelUniqueness co' co)). induction R as [R r].
    use (EC_IsomorphicToExact _ _ _ e).
    use tpair; cbn.
    - exact R.
    - exists (identity_iso _). exists (identity_iso _).
      split.
      + exact (r @ ! id_right _).
      + exact (id_left _ @ ! id_right _).
  Defined.
  Lemma ExactSequence10 (A:M) (Z:Zero M) : isExact (mk_MorphismPair (identity A) (0 : A --> Z)).
  Proof.
    exact (ExactSequenceFromMono _ _ (pr2 (kerCoker10 Z A)) (EC_IdentityIsMono A)).
  Defined.
  Lemma ExactSequence01 (A:M) (Z:Zero M) : isExact (mk_MorphismPair (0 : Z --> A) (identity A)).
  Proof.
    exact (ExactSequenceFromEpi _ _ (pr1 (kerCoker01 Z A)) (EC_IdentityIsEpi A)).
  Defined.
  Lemma MonoToZero (Z:Zero M) (A:M) : Z ↣ A.
  Proof.
    exists (0 : Z --> A). apply hinhpr. exists A. exists (identity A). use ExactSequence01.
  Defined.
  Lemma EpiToZero (A:M) (Z:Zero M) : A ↠ Z.
  Proof.
    exists (0 : A --> Z). apply hinhpr. exists A. exists (identity A). use ExactSequence10.
  Defined.
  Lemma DirectSumToExact {A B:M} (S:BinDirectSum A B) :
    isExact (mk_MorphismPair (to_In1 S) (to_Pr2 S)).
  Proof.
    set (Z := to_Zero M).
    set (p := EpiToZero A Z).
    assert (pb := DirectSumToPullback S Z).
    assert (Q := @EC_PullbackEpi M A Z B p 0).
    apply (squash_to_hProp Q); clear Q; intros [pb' R].
    assert (T := iso_from_Pullback_to_Pullback pb pb').
    set (t := morphism_from_iso _ _ _ T).

  Abort.
End ExactCategoryFacts.
