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
Local Arguments to_BinOpId {_ _ _ _ _ _ _ _}.
Local Arguments to_IdIn1 {_ _ _ _ _ _ _ _}.
Local Arguments to_IdIn2 {_ _ _ _ _ _ _ _}.
Local Arguments to_Unel1 {_ _ _ _ _ _ _ _}.
Local Arguments to_Unel2 {_ _ _ _ _ _ _ _}.
Local Arguments MorphismPair : clear implicits.
Local Arguments morphism_from_iso {_ _ _}.

Local Open Scope logic.

Delimit Scope addcat with addcat. (* move upstream *)

Local Definition hom (C:precategory_data) : ob C -> ob C -> UU := λ c c', precategory_morphisms c c'.
Local Definition Hom (C : category) : ob C -> ob C -> hSet := λ c c', hSetpair _ (homset_property C c c').
Local Definition Hom_add (C : PreAdditive) : ob C -> ob C -> abgr := λ c c', (@to_abgr C c c').

Section Sanity.
  Context (M : category) (x y:M) (f : hom M x y) (g : Hom M x y).
  Goal Hom M x y. exact f. Defined.
  Goal hom M x y. exact g. Defined.
End Sanity.

Section Sanity2.
  Context (M : PreAdditive) (x y:M) (f : hom M x y) (g : Hom M x y) (h : Hom_add M x y).
  Goal Hom_add M x y. exact f. Defined.
  Goal Hom_add M x y. exact g. Defined.
  Goal Hom M x y. exact f. Defined.
  Goal Hom M x y. exact h. Defined.
  Goal hom M x y. exact g. Defined.
  Goal hom M x y. exact h. Defined.
End Sanity2.

Local Notation "a --> b" := (precategory_morphisms a b) : cat.
Local Notation "a --> b" := (hSetpair (precategory_morphisms a b) (homset_property _ a b)) : Cat.
Local Notation "a --> b" := (to_abgr a b) : addcat.
Local Notation "b <-- a" := (precategory_morphisms a b) (only parsing) : cat.
Local Notation "b <-- a" := (hSetpair (precategory_morphisms a b) (homset_property _ a b)) (only parsing) : Cat.
Local Notation "b <-- a" := (to_abgr a b) (only parsing) : addcat.
Local Notation "f · g" := (compose f g : to_abgr _ _) : Cat.
Local Notation "f · g" := (compose f g : to_abgr _ _) : addcat.
Local Notation "g ∘ f" := (compose f g : to_abgr _ _) : Cat.
Local Notation "g ∘ f" := (compose f g : to_abgr _ _) : addcat.
Local Notation "0" := (ZeroArrow (to_Zero _) _ _) : cat.
Local Notation "0" := (unel _ : to_abgr _ _) : addcat.
Local Notation "1" := (identity _ : to_abgr _ _) : addcat.
Local Notation "f = g" := (eqset f g) : Cat.
Local Notation "f - g" := (@op _ f (grinv _ g) : to_abgr _ _) : addcat.
Local Notation "A ⊕ B" := (to_BinDirectSums _ A B) : addcat.

Local Open Scope cat.

Section Categories.
  Definition is_iso' {C : precategory} {b c : C} (f : b --> c) :=
    ∏ a, isweq (postcomp_with f (a:=a)).
  Lemma is_iso'_to_is_iso {C : precategory} {b c : C} (f : b --> c) :
    is_iso' f -> is_iso f.
  Proof.
    intros i. use is_iso_from_is_z_iso.
    assert (Q := i c (identity c)). induction Q as [[g E] _]. unfold postcomp_with in E.
    exists g.
    split.
    2 : { exact E. }
    assert (X := id_left _ : postcomp_with f (identity _) = f).
    assert (Y := ! assoc _ _ _ @ maponpaths (precomp_with f) E @ id_right _
                 : postcomp_with f (f · g) = f).
    clear E.
    set (x := (_,,X) : hfiber (postcomp_with f) f).
    set (y := (_,,Y) : hfiber (postcomp_with f) f).
    exact (maponpaths pr1 ((proofirrelevance _ (isapropifcontr (i b f))) y x)).
  Defined.
End Categories.

Import AddNotation.

Section MorphismPairs.          (* move upstream *)
  Context {M : precategory}.
  Definition MorphismPairMap (P Q : MorphismPair M) :=
    ∑ (f : Ob1 P --> Ob1 Q)
      (g : Ob2 P --> Ob2 Q)
      (h : Ob3 P --> Ob3 Q),
    f · Mor1 Q = Mor1 P · g  ×  g · Mor2 Q = Mor2 P · h.
  Definition Map1 {P Q : MorphismPair M} (f : MorphismPairMap P Q) : Ob1 P --> Ob1 Q := pr1 f.
  Definition Map2 {P Q : MorphismPair M} (f : MorphismPairMap P Q) : Ob2 P --> Ob2 Q := pr12 f.
  Definition Map3 {P Q : MorphismPair M} (f : MorphismPairMap P Q) : Ob3 P --> Ob3 Q := pr122 f.
  Definition MorphismPairIsomorphism (P Q : MorphismPair M) :=
    ∑ (f : iso (Ob1 P) (Ob1 Q))
      (g : iso (Ob2 P) (Ob2 Q))
      (h : iso (Ob3 P) (Ob3 Q)),
    f · Mor1 Q = Mor1 P · g  ×  g · Mor2 Q = Mor2 P · h.
End MorphismPairs.

Section Pullbacks.              (* move upstream *)
  Context {M : precategory}.
  Lemma pullbackiso {A B C:M} {f : A --> C} {g : B --> C}
        (pb : Pullback f g) (pb' : Pullback f g)
    : ∑ (t : iso (PullbackObject pb) (PullbackObject pb')),
      t · PullbackPr1 pb' = PullbackPr1 pb ×
      t · PullbackPr2 pb' = PullbackPr2 pb.
  Proof.
    use tpair.
    - use iso_from_Pullback_to_Pullback.
    - cbn beta. split.
      + use PullbackArrow_PullbackPr1.
      + use PullbackArrow_PullbackPr2.
  Defined.
  Definition IsoArrowTo     {A A' B:M} (g : A --> B) (g' : A' --> B) := ∑ i : iso A A', i · g' = g .
  Coercion IsoArrowTo_pr1   {A A' B:M} (g : A --> B) (g' : A' --> B) : IsoArrowTo g g' -> iso A A' := pr1.
  Definition IsoArrowFrom   {A B B':M} (g : A --> B) (g' : A --> B') := ∑ i : iso B B', g · i  = g'.
  Coercion IsoArrowFrom_pr1 {A B B':M} (g : A --> B) (g' : A --> B') : IsoArrowFrom g g' -> iso B B' := pr1.
  Lemma pullbackiso1 {A B C:M} {f : A --> C} {g : B --> C}
        (pb : Pullback f g) (pb' : Pullback f g)
    : IsoArrowTo (PullbackPr1 pb) (PullbackPr1 pb').
  Proof.
    exact (pr1 (pullbackiso pb pb'),, pr12 (pullbackiso pb pb')).
  Defined.
  Lemma pullbackiso2 {A B C:M} {f : A --> C} {g : B --> C}
        (pb : Pullback f g) (pb' : Pullback f g)
    : IsoArrowTo (PullbackPr2 pb) (PullbackPr2 pb').
  Proof.
    exact (pr1 (pullbackiso pb pb'),, pr22 (pullbackiso pb pb')).
  Defined.
End Pullbacks.

Local Open Scope Cat.

Section Pullbacks2.              (* move upstream *)
  Context (M : category).        (* giving this argument makes it work better (?) *)
  Lemma IsoArrowTo_isaprop {A A' B:M} (g : A --> B) (g' : A' --> B) :
    isMonic g' -> isaprop (IsoArrowTo g g').
  Proof.
    intros i. apply invproofirrelevance; intros k k'. apply subtypeEquality'.
    - induction k as [[k K] e], k' as [[k' K'] e']; cbn; cbn in e, e'.
      induction (i A k k' (e @ !e')). apply maponpaths. apply isaprop_is_iso.
    - apply homset_property.
  Qed.
  Lemma IsoArrowFrom_isaprop {A B B':M} (g : A --> B) (g' : A --> B') :
     isEpi g -> isaprop (IsoArrowFrom g g').
  Proof.
    intros i. apply invproofirrelevance; intros k k'. apply subtypeEquality.
    { intros j. apply homset_property. }
    induction k as [[k K] e], k' as [[k' K'] e']; cbn; cbn in e, e'.
    apply subtypeEquality; cbn.
    { intros f. apply isaprop_is_iso. }
    use i. exact (e @ !e').
  Qed.
End Pullbacks2.

Local Open Scope addmonoid.
Local Open Scope addcat.

Section AdditiveCategories.     (* move upstream *)
  Context {M : Additive}.
  (** Reprove some standard facts in additive categories with the 0 map (the zero element of the
      group) replacing the zero map (defined by composing maps to and from the zero object). *)
  Lemma zeroLeft {a b c : M} (f : b --> c) : (0 : a --> b) · f = 0.
  (* compare with ZeroArrow_comp_left *)
  Proof.
    refine (_ @ ZeroArrow_comp_left M (to_Zero M) a b c f @ _).
    - apply (maponpaths (λ g, g · f)). apply PreAdditive_unel_zero.
    - apply pathsinv0, PreAdditive_unel_zero.
  Qed.
  Lemma zeroRight {a b c : M} (f : a --> b) : f · (0 : b --> c) = 0.
  (* compare with ZeroArrow_comp_right *)
  Proof.
    refine (_ @ ZeroArrow_comp_right M (to_Zero M) a b c f @ _).
    - apply maponpaths, PreAdditive_unel_zero.
    - apply pathsinv0, PreAdditive_unel_zero.
  Qed.
  Definition leftComp (a b c : M) (f : a --> b) : (b --> c) -> (a --> c)
    := precomp_with f.          (* replace with to_premor *)
  Definition rightComp (a b c : M) (f : b --> c) : (a --> b) -> (a --> c)
    := postcomp_with f.         (* replace with to_postmor *)
  Lemma leftCompHomo (a b c : M) (f : a --> b) : ismonoidfun (leftComp a b c f).
  Proof.
    split.
    - intros g h. apply to_premor_linear'.
    - apply zeroRight.
  Defined.
  Lemma rightCompHomo (a b c : M) (f : b --> c) : ismonoidfun (rightComp a b c f).
  Proof.
    split.
    - intros g h. apply to_postmor_linear'.
    - apply zeroLeft.
  Qed.
  Definition isKernel' {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : w --> y), h · g = 0 ⇒ ∃! φ : w --> x, φ · f = h.
  Definition isCokernel' {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : y --> w), f · h = 0 ⇒ ∃! φ : z --> w, g · φ = h.
  Lemma KernelIsMonic {x y z:M} (f : x --> y) (g : y --> z) : isKernel' f g -> isMonic f.
  Proof.
    intros [t i] w p q e.
    set (T := ∑ r : w --> x, r · f = q · f). assert (ic : isProofIrrelevant T).
    { apply proofirrelevance, isapropifcontr.
      use i. rewrite <- assoc. rewrite t. apply zeroRight. }
    set (t1 := (p,,e) : T). set (t2 := (q,,idpath _) : T).
    assert (Q := ic t1 t2). exact (maponpaths pr1 Q).
  Qed.
  Lemma CokernelIsEpi {x y z:M} (f : x --> y) (g : y --> z) : isCokernel' f g -> isEpi g.
  Proof.
    intros [t i] w p q e.
    set (T := ∑ r : z --> w, g · r = g · q). assert (ic : isProofIrrelevant T).
    { apply proofirrelevance, isapropifcontr.
      use i. rewrite assoc. rewrite t. apply zeroLeft. }
    set (t1 := (p,,e) : T). set (t2 := (q,,idpath _) : T).
    assert (Q := ic t1 t2). exact (maponpaths pr1 Q).
  Qed.
  Lemma KernelOfZeroMapIsIso {x y z:M} (g : x --> y) : isKernel' g (0 : y --> z) -> is_iso g.
  (* compare with KernelofZeroArrow_is_iso *)
  Proof.
    intros [_ ke]. apply is_iso'_to_is_iso. intros T h. use ke. apply zeroRight.
  Defined.
  Lemma CokernelOfZeroMapIsIso {x y z:M} (g : y --> z) : isCokernel' (0 : x --> y) g -> is_iso g.
  (* compare with CokernelofZeroArrow_is_iso *)
  Proof.
    (* this proof makes efficient use of the definition of is_iso *)
    intros [_ co] T h. use co. apply zeroLeft.
  Defined.
  Lemma KernelUniqueness {x x' y z : M} {f : x --> y} {f' : x' --> y} {g : y --> z} :
    isKernel' f g -> isKernel' f' g -> iscontr (IsoArrowTo f f').
  Proof.
    intros i j. apply iscontraprop1.
    - exact (IsoArrowTo_isaprop M f f' (KernelIsMonic f' g j)).
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
    - exact (IsoArrowFrom_isaprop M g g' (CokernelIsEpi f g i)).
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
  Definition reverseBinDirectSum {A B:M} : BinDirectSum A B -> BinDirectSum B A.
  Proof.
    intros S.
    use tpair.
    - exact (BinDirectSumOb M S ,, to_In2 S ,, to_In1 S ,, to_Pr2 S ,, to_Pr1 S).
    - cbn. repeat split.
      + exact (to_IdIn2 (pr2 S)).
      + exact (to_IdIn1 (pr2 S)).
      + exact (to_Unel2 (pr2 S)).
      + exact (to_Unel1 (pr2 S)).
      + refine (_ @ to_BinOpId (pr2 S)). use (commax (to_abgr _ _)).
  Defined.
End AdditiveCategories.

Section KernelCokernelPairs.
  Context {M : Additive}.
  Definition isKernelCokernelPair {A B C:M} (i : A --> B) (p: B --> C) : hProp
    := isKernel' i p ∧ isCokernel' i p.
  Definition PairToKernel {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair i p -> isKernel' i p := pr1.
  Definition PairToCokernel {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair i p -> isCokernel' i p := pr2.
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
    - exists (to_Unel1 S). intros T h H. use unique_exists; cbn beta.
      + exact (h · to_Pr1 S).
      + refine (! assoc _ _ _ @ _ @ id_right _). rewrite <- (to_BinOpId S).
        rewrite to_premor_linear'. rewrite (assoc h (to_Pr2 S) (to_In2 S)).
        rewrite H; clear H. rewrite zeroLeft. exact (! runax _ (h · _)).
      + intros k. apply to_has_homsets.
      + clear H. intros k e. induction e. rewrite <- assoc.
        rewrite (to_IdIn1 S). apply pathsinv0, id_right.
    - exists (to_Unel1 S). intros T h H. use unique_exists; cbn beta.
      + exact (to_In2 _ · h).
      + refine (assoc _ _ _ @ _ @ id_left h). rewrite <- (to_BinOpId S).
        rewrite to_postmor_linear'.
        rewrite <- (assoc (to_Pr1 S) (to_In1 S) h). rewrite H; clear H.
        rewrite zeroRight. exact (! lunax _ (to_Pr2 S · to_In2 S · h)).
      + intros k. apply to_has_homsets.
      + clear H. intros k e. induction e. rewrite assoc. rewrite (to_IdIn2 S).
        exact (! id_left _).
  Qed.
  Definition TrivialDirectSum (Z:Zero M) (A:M) : BinDirectSum A Z.
  Proof.
    exists (A,,1,,0,,1,,0).
    repeat split; cbn.
    - apply id_right.
    - apply ArrowsToZero.
    - apply ArrowsToZero.
    - apply ArrowsFromZero.
    - rewrite id_right. rewrite zeroRight. rewrite rewrite_op.
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
    - rewrite id_right. rewrite zeroRight. rewrite rewrite_op.
      rewrite lunax. reflexivity.
  Defined.
  Lemma kerCoker10 (Z:Zero M) (A:M) : isKernelCokernelPair (identity A) (0 : A --> Z).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum Z A)).
  Qed.
  Lemma kerCoker01 (Z:Zero M) (A:M) : isKernelCokernelPair (0 : Z --> A) (identity A).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum' Z A)).
  Qed.
  Lemma PairPushoutMap {A B C A':M} (i : A --> B) (p : B --> C)
        (pr : isKernelCokernelPair i p)
        (r : A --> A') (po : Pushout i r) :
    ∑ (q : po --> C), PushoutIn1 po · q = p × PushoutIn2 po · q = 0.
  Proof.
    refine (iscontrpr1 (isPushout_Pushout po C p 0 _)).
    refine (pr1 (PairToCokernel pr) @ ! _). apply zeroRight.
  Defined.
  Lemma PairPullbackMap {A B C A':M} (i : A <-- B) (p : B <-- C)
        (pr : isKernelCokernelPair p i)
        (r : A <-- A') (pb : Pullback i r) :
    ∑ (q : pb <-- C), PullbackPr1 pb ∘ q = p × PullbackPr2 pb ∘ q = 0.
  Proof.
    refine (iscontrpr1 (isPullback_Pullback pb C p 0 _)).
    refine (pr1 (PairToCokernel pr) @ ! _). apply zeroLeft.
  Defined.
  Lemma PairPushoutCokernel {A B C A':M} (i : A --> B) (p : B --> C)
        (pr : isKernelCokernelPair i p)
        (r : A --> A') (po : Pushout i r)
        (j := PushoutIn2 po)
        (pp := PairPushoutMap i p pr r po) :
    isCokernel' j (pr1 pp).
  Proof.
    set (s := PushoutIn1 po).
    induction pp as [q [e1 e2]]; change (isCokernel' j q);
      change (hProptoType (s · q = p)) in e1;
      change (hProptoType (j · q = 0)) in e2.
    exists e2.
    intros T h e.
    assert (L : i · (s · h) = 0).
    { refine (assoc _ _ _ @ _).
      intermediate_path (r · j · h).
      { apply (maponpaths (λ s, s · h)). exact (PushoutSqrCommutes po). }
      refine (! assoc _ _ _ @ _).
      induction (!e).
      apply zeroRight. }
    assert (V := iscontrpr1 ((pr22 pr) T (s · h) L)); clear L.
    induction V as [k e3].
    use iscontraprop1.
    { apply invproofirrelevance; intros φ φ'.
      apply subtypeEquality_prop.
      induction φ as [φ e4]; induction φ' as [φ' e5]; cbn.
      use (_ : isEpi q).
      { apply (isEpi_precomp M s q). rewrite e1. apply (CokernelIsEpi i p). apply pr. }
      exact (e4 @ ! e5). }
    exists  k.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout po)); fold s j.
    { refine (assoc _ _ _ @ _ @ e3). apply (maponpaths (λ s, s · k)). exact e1. }
    { refine (assoc _ _ _ @ _ @ ! e). rewrite e2. apply zeroLeft. }
  Qed.
  Lemma PairPullbackKernel {A B C A':M} (i : A <-- B) (p : B <-- C)
        (pr : isKernelCokernelPair p i)
        (r : A <-- A') (pb : Pullback i r)
        (j := PullbackPr2 pb)
        (pp := PairPullbackMap i p pr r pb) :
    isKernel' (pr1 pp) j.
  Proof.
    set (s := PullbackPr1 pb).
    induction pp as [q [e1 e2]]; change (isKernel' q j);
      change (hProptoType (s ∘ q = p)) in e1;
      change (hProptoType (j ∘ q = 0)) in e2.
    exists e2.
    intros T h e.
    assert (L : i ∘ (s ∘ h) = 0).
    { refine (! assoc _ _ _ @ _).
      intermediate_path (r ∘ j ∘ h).
      { apply (maponpaths (λ s, s ∘ h)). exact (PullbackSqrCommutes pb). }
      refine (assoc _ _ _ @ _).
      induction (!e).
      apply zeroLeft. }
    assert (V := iscontrpr1 ((pr21 pr) T (s ∘ h) L)); clear L.
    induction V as [k e3].
    use iscontraprop1.
    { apply invproofirrelevance; intros φ φ'.
      apply subtypeEquality_prop.
      induction φ as [φ e4]; induction φ' as [φ' e5]; cbn.
      use (_ : isMonic q).
      { apply (isMonic_postcomp M q s). rewrite e1. apply (KernelIsMonic p i). apply pr. }
      exact (e4 @ ! e5). }
    exists  k.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback pb)); fold s j.
    { refine (! assoc _ _ _ @ _ @ e3). apply (maponpaths (λ s, s ∘ k)). exact e1. }
    { refine (! assoc _ _ _ @ _ @ ! e). rewrite e2. apply zeroRight. }
  Qed.
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
  (** The following definition is definition 2.1 from the paper of Bühler. *)
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
  Definition EC_IsomorphicToExact {P Q:MorphismPair M}
    : MorphismPairIsomorphism P Q ⇒ isExact P ⇒ isExact Q
    := pr12 M P Q.
  Definition EC_IdentityIsMono (A:M) : isAdmissibleMonomorphism (identity A)
    := pr122 M A.
  Definition EC_IdentityIsEpi (A:M) : isAdmissibleEpimorphism (identity A)
    := pr122 (pr2 M) A.
  Definition EC_ExactToKernelCokernel {P : MorphismPair M} :
    isExact P ⇒ isKernelCokernelPair (Mor1 P) (Mor2 P)
    := pr122 (pr22 M) P.
  Definition EC_ComposeMono {A B C:M} (f : A ↣ B) (g : B ↣ C) :
    isAdmissibleMonomorphism (f · g)
    := pr122 (pr222 M) A B C f g.
  Definition EC_ComposeEpi {A B C:M} (f : A ↠ B) (g : B ↠ C) :
    isAdmissibleEpimorphism (f · g)
    := pr122 (pr222 (pr2 M)) A B C f g.
  Definition EC_PullbackEpi {A B C:M} (f : A ↠ B) (g : C --> B) :
    ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)
    := pr122 (pr222 (pr22 M)) A B C f g.
  Definition EC_PushoutMono {A B C:M} (f : B ↣ A) (g : B --> C) :
    ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO)
    := pr222 (pr222 (pr22 M)) A B C f g.
End ExactCategoryAccessFunctions.

Section ExactCategoryFacts.
  Context {M : ExactCategory}.
  Lemma ExactSequenceFromMono {A B C:M} (i : A --> B) (p : B --> C) :
    isCokernel' i p -> isAdmissibleMonomorphism i -> isExact (mk_MorphismPair i p).
  Proof.
    intros co mo. apply (squash_to_hProp mo); clear mo; intros [C' [p' e]].
    assert (co' := pr2 (EC_ExactToKernelCokernel e) : isCokernel' i p').
    assert (R := iscontrpr1 (CokernelUniqueness co' co)). induction R as [R r].
    use (EC_IsomorphicToExact _ e).
    exists (identity_iso _). exists (identity_iso _).
    exact (R ,, (id_left _ @ ! id_right _) ,, id_left _ @ ! r).
  Qed.
  Lemma ExactSequenceFromEpi {A B C:M} (i : A --> B) (p : B --> C) :
    isKernel' i p -> isAdmissibleEpimorphism p -> isExact (mk_MorphismPair i p).
  Proof.
    intros co mo. apply (squash_to_hProp mo); clear mo; intros [A' [i' e]].
    assert (co' := pr1 (EC_ExactToKernelCokernel e) : isKernel' i' p).
    assert (R := iscontrpr1 (KernelUniqueness co' co)). induction R as [R r].
    use (EC_IsomorphicToExact _ e).
    exact (R ,, (identity_iso _) ,, (identity_iso _) ,, (r @ ! id_right _) ,, (id_left _ @ ! id_right _)).
  Qed.
  Lemma ExactSequence10 (A:M) (Z:Zero M) : isExact (mk_MorphismPair (identity A) (0 : A --> Z)).
  Proof.
    exact (ExactSequenceFromMono _ _ (pr2 (kerCoker10 Z A)) (EC_IdentityIsMono A)).
  Qed.
  Lemma ExactSequence01 (A:M) (Z:Zero M) : isExact (mk_MorphismPair (0 : Z --> A) (identity A)).
  Proof.
    exact (ExactSequenceFromEpi _ _ (pr1 (kerCoker01 Z A)) (EC_IdentityIsEpi A)).
  Qed.
  Lemma MonoToZero (Z:Zero M) (A:M) : Z ↣ A.
  Proof.
    exists (0 : Z --> A). apply hinhpr. exists A. exists (identity A). use ExactSequence01.
  Defined.
  Lemma EpiToZero (A:M) (Z:Zero M) : A ↠ Z.
  Proof.
    exists (0 : A --> Z). apply hinhpr. exists A. exists (identity A). use ExactSequence10.
  Defined.
  Lemma IsomMono {A B B':M} (f : A --> B) (f' : A --> B') :
    IsoArrowFrom f f' -> isAdmissibleMonomorphism f -> isAdmissibleMonomorphism f'.
  Proof.
    intros [i I] E. apply (squash_to_hProp E); clear E; intros [C [p E]].
    apply hinhpr. exists C. exists (iso_inv_from_iso i · p). use (EC_IsomorphicToExact _ E).
    exists (identity_iso A). exists i. exists (identity_iso C). split; cbn.
    - exact (id_left _ @ ! I).
    - refine (assoc _ _ _ @ _ @ id_left _ @ ! id_right _).
      apply (maponpaths (λ k, k · p)). apply iso_inv_after_iso.
  Qed.
  Lemma IsomEpi {A A' B:M} (f : A --> B) (f' : A' --> B) :
    IsoArrowTo f f' -> isAdmissibleEpimorphism f -> isAdmissibleEpimorphism f'.
  Proof.
    intros [i I] E. apply (squash_to_hProp E); clear E; intros [K [j E]].
    apply hinhpr. exists K. exists (j · i). use (EC_IsomorphicToExact _ E).
    exists (identity_iso K). exists i. exists (identity_iso B). cbn.
    exists (id_left _). exact (I @ ! id_right f).
  Qed.
  Lemma DirectSumToExact {A B:M} (S:BinDirectSum A B) :
    isExact (mk_MorphismPair (to_In1 S) (to_Pr2 S)).
  Proof.
    use ExactSequenceFromEpi.
    { exact (PairToKernel (kerCokerDirectSum S)). }
    set (Z := to_Zero M).
    set (pb := DirectSumToPullback S Z).
    change (isAdmissibleEpimorphism (PullbackPr2 pb)).
    assert (Q := EC_PullbackEpi (EpiToZero A Z) (0 : B --> Z)).
    apply (squash_to_hProp Q); clear Q; intros [pb' R'].
    exact (IsomEpi (PullbackPr2 pb') (PullbackPr2 pb) (pullbackiso2 pb' pb) R').
  Qed.
  Lemma DirectSumToExact' {A B:M} (S:BinDirectSum A B) :
    isExact (mk_MorphismPair (to_In2 S) (to_Pr1 S)).
  Proof.
    exact (DirectSumToExact (reverseBinDirectSum S)).
  Qed.
  Lemma ExactPushout {A B C A':M} (i : A --> B) (p : B --> C)
        (pr : isExact (mk_MorphismPair i p))
        (r : A --> A') :
    ∃ (po : Pushout i r),
      isExact (mk_MorphismPair (PushoutIn2 po) (pr1 (PairPushoutMap i p (EC_ExactToKernelCokernel pr) r po))).
  Proof.
    assert (I := hinhpr (C ,, p ,, pr) : isAdmissibleMonomorphism i).
    assert (R := EC_PushoutMono (i,,I) r).
    apply (squash_to_hProp R); clear R; intros [po J]; apply hinhpr.
    exists po. use ExactSequenceFromMono.
    { exact (PairPushoutCokernel i p (EC_ExactToKernelCokernel pr) r po). }
    exact J.
  Qed.
  Lemma ExactPullback {A B C A':M} (i : A <-- B) (p : B <-- C)
        (pr : isExact (mk_MorphismPair p i))
        (r : A <-- A') :
    ∃ (pb : Pullback i r),
      isExact (mk_MorphismPair (pr1 (PairPullbackMap i p (EC_ExactToKernelCokernel pr) r pb)) (PullbackPr2 pb)).
  Proof.
    assert (I := hinhpr (C ,, p ,, pr) : isAdmissibleEpimorphism i).
    assert (R := EC_PullbackEpi (i,,I) r).
    apply (squash_to_hProp R); clear R; intros [pb J]; apply hinhpr.
    exists pb. use ExactSequenceFromEpi.
    { exact (PairPullbackKernel i p (EC_ExactToKernelCokernel pr) r pb). }
    exact J.
  Qed.
  Lemma MonicAdmEpiIsIso {A B:M} (p : A ↠ B) : isMonic p -> is_iso p.
  Proof.
    induction p as [p E]. cbn. intros I. apply (squash_to_prop E).
    { apply isaprop_is_iso. }
    clear E; intros [K [i E]].
    assert (Q := EC_ExactToKernelCokernel E); clear E.
    induction Q as [ke co];
      change (hProptoType (isKernel' i p)) in ke;
      change (hProptoType (isCokernel' i p)) in co.
    assert (Q : i = 0).
    { use (I K i 0). exact (pr1 ke @ ! zeroLeft _). }
    clear I ke. induction (!Q); clear Q. exact (CokernelOfZeroMapIsIso p co).
  Defined.
  Lemma EpiAdmMonoIsIso {A B:M} (i : A ↣ B) : isEpi i -> is_iso i.
  Proof.
    induction i as [i E]. cbn. intros I. apply (squash_to_prop E).
    { apply isaprop_is_iso. }
    clear E; intros [K [p E]].
    assert (Q := EC_ExactToKernelCokernel E); clear E.
    induction Q as [ke co];
      change (hProptoType (isKernel' i p)) in ke;
      change (hProptoType (isCokernel' i p)) in co.
    assert (Q : p = 0).
    { use (I K p 0). exact (pr1 co @ ! zeroRight _). }
    clear I co. induction (!Q); clear Q. exact (KernelOfZeroMapIsIso i ke).
  Defined.
End ExactCategoryFacts.

Section ShortExactSequences.
  (* I'm not sure this type will be useful. *)
  Definition ShortExactSequence (M:ExactCategory) := ∑ (P : MorphismPair M), isExact P.
  Coercion ShortExactSequenceToMorphismPair {M:ExactCategory} (P : ShortExactSequence M) : MorphismPair M := pr1 P.
  Definition ES_ExactToKernelCokernel {M:ExactCategory} (P : ShortExactSequence M)
    : isKernelCokernelPair (Mor1 P) (Mor2 P)
    := EC_ExactToKernelCokernel (pr2 P).
  Context {M:ExactCategory}.
  Definition ShortExactSequenceMap (P Q:ShortExactSequence M) := MorphismPairMap P Q.
End ShortExactSequences.
