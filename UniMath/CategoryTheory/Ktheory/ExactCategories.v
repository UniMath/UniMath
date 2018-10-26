(** Exact categories *)

Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.Monics.
Require Export UniMath.CategoryTheory.Epis.
Require Export UniMath.CategoryTheory.limits.zero.
Require Export UniMath.CategoryTheory.limits.kernels.
Require Export UniMath.CategoryTheory.limits.cokernels.
Require Export UniMath.CategoryTheory.limits.binproducts.
Require Export UniMath.CategoryTheory.limits.bincoproducts.
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
Local Notation "'π₁'" := (to_Pr1 _).
Local Notation "'π₂'" := (to_Pr2 _).
Local Notation "'ι₁'" := (to_In1 _).
Local Notation "'ι₂'" := (to_In2 _).
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

Section Precategories.             (* move upstream *)
  Definition iso_to_z_iso {C : precategory} {b c : C} (f : iso b c) : z_iso b c
    := pr1 f ,, is_z_iso_from_is_iso (pr1 f) (pr2 f).
  Definition z_iso_to_iso {C : precategory} {b c : C} (f : z_iso b c) : iso b c
    := pr1 f ,, is_iso_from_is_z_iso (pr1 f) (pr2 f).
  Definition is_iso' {C : precategory} {b c : C} (f : b --> c) :=
    ∏ a, isweq (postcomp_with f (a:=a)).
  Lemma is_iso'_to_is_z_iso (C : precategory) {b c : C} (f : b --> c) :
    is_iso' f -> is_z_isomorphism f.
  Proof.
    intros i.
    assert (Q := i c (identity c)). induction Q as [[g E] _]. unfold postcomp_with in E.
    exists g. split.
    2 : { exact E. }
    assert (X := id_left _ : postcomp_with f (identity _) = f).
    assert (Y := ! assoc _ _ _ @ maponpaths (precomp_with f) E @ id_right _
                 : postcomp_with f (f · g) = f).
    clear E.
    set (x := (_,,X) : hfiber (postcomp_with f) f).
    set (y := (_,,Y) : hfiber (postcomp_with f) f).
    exact (maponpaths pr1 ((proofirrelevance _ (isapropifcontr (i b f))) y x)).
  Defined.
End Precategories.

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
    ∑ (f : z_iso (Ob1 P) (Ob1 Q))
      (g : z_iso (Ob2 P) (Ob2 Q))
      (h : z_iso (Ob3 P) (Ob3 Q)),
    f · Mor1 Q = Mor1 P · g  ×  g · Mor2 Q = Mor2 P · h.
End MorphismPairs.

Section Pullbacks.              (* move upstream *)
  Context {M : precategory}.
  Lemma pullbackiso {A B C:M} {f : A --> C} {g : B --> C}
        (pb : Pullback f g) (pb' : Pullback f g)
    : ∑ (t : z_iso (PullbackObject pb) (PullbackObject pb')),
      t · PullbackPr1 pb' = PullbackPr1 pb ×
      t · PullbackPr2 pb' = PullbackPr2 pb.
  Proof.
    use tpair.
    - apply iso_to_z_iso. use iso_from_Pullback_to_Pullback.
    - cbn beta. split.
      + use PullbackArrow_PullbackPr1.
      + use PullbackArrow_PullbackPr2.
  Defined.
  Definition IsoArrowTo     {A A' B:M} (g : A --> B) (g' : A' --> B) := ∑ i : z_iso A A', i · g' = g .
  Coercion IsoArrowTo_pr1   {A A' B:M} (g : A --> B) (g' : A' --> B) : IsoArrowTo g g' -> z_iso A A' := pr1.
  Definition IsoArrowFrom   {A B B':M} (g : A --> B) (g' : A --> B') := ∑ i : z_iso B B', g · i  = g'.
  Coercion IsoArrowFrom_pr1 {A B B':M} (g : A --> B) (g' : A --> B') : IsoArrowFrom g g' -> z_iso B B' := pr1.
  Definition IsoArrow       {A A' B B':M} (g : A --> B) (g' : A' --> B') := ∑ (i : z_iso A A') (j : z_iso B B'), i · g' = g · j.
  Definition pullbackiso1 {A B C:M} {f : A --> C} {g : B --> C}
        (pb : Pullback f g) (pb' : Pullback f g)
    : IsoArrowTo (PullbackPr1 pb) (PullbackPr1 pb')
    := pr1 (pullbackiso pb pb'),,pr12 (pullbackiso pb pb').
  Definition pullbackiso2 {A B C:M} {f : A --> C} {g : B --> C}
        (pb : Pullback f g) (pb' : Pullback f g)
    : IsoArrowTo (PullbackPr2 pb) (PullbackPr2 pb')
    := pr1 (pullbackiso pb pb'),,pr22 (pullbackiso pb pb').
End Pullbacks.

Local Open Scope Cat.

Section Pullbacks2.              (* move upstream *)
  Context (M : category).        (* giving this argument makes it work better (?) *)
  Lemma IsoArrowTo_isaprop {A A' B:M} (g : A --> B) (g' : A' --> B) :
    isMonic g' -> isaprop (IsoArrowTo g g').
  Proof.
    intros i. apply invproofirrelevance; intros k k'. apply subtypeEquality'.
    - induction k as [[k K] e], k' as [[k' K'] e']; cbn; cbn in e, e'.
      induction (i A k k' (e @ !e')). apply maponpaths. apply isaprop_is_z_isomorphism.
      apply homset_property.
    - apply homset_property.
  Qed.
  Lemma IsoArrowFrom_isaprop {A B B':M} (g : A --> B) (g' : A --> B') :
     isEpi g -> isaprop (IsoArrowFrom g g').
  Proof.
    intros i. apply invproofirrelevance; intros k k'. apply subtypeEquality.
    { intros j. apply homset_property. }
    induction k as [[k K] e], k' as [[k' K'] e']; cbn; cbn in e, e'.
    apply subtypeEquality; cbn.
    { intros f. apply isaprop_is_z_isomorphism. apply homset_property. }
    use i. exact (e @ !e').
  Qed.
End Pullbacks2.

Local Open Scope addmonoid.
Local Open Scope addcat.

Section AdditiveCategories.     (* move upstream *)
  (** Reprove some standard facts in additive categories with the 0 map (the zero element of the
      group) replacing the zero map (defined by composing maps to and from the zero object). *)
  Context {M : Additive}.
  Lemma DirectSumIn1Pr2 {a b:M} (S:BinDirectSum a b) : to_In1 S · to_Pr2 S = 0.
  Proof.
    exact (to_Unel1 S).
  Defined.
  Lemma DirectSumIn2Pr1 {a b:M} (S:BinDirectSum a b) : to_In2 S · to_Pr1 S = 0.
  Proof.
    exact (to_Unel2 S).
  Defined.
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
  Lemma leftCompHomo (a b c : M) (f : a --> b) : ismonoidfun (to_premor c f).
  Proof.
    split.
    - intros g h. apply to_premor_linear'.
    - apply zeroRight.
  Defined.
  Lemma rightCompHomo (a b c : M) (f : b --> c) : ismonoidfun (to_postmor a f).
  Proof.
    split.
    - intros g h. apply to_postmor_linear'.
    - apply zeroLeft.
  Qed.
  Lemma rightDistribute {a b c : M} (f : a --> b) (g h : b --> c) : f · (g + h) = f · g + f · h.
  Proof.
    apply leftCompHomo.
  Qed.
  Lemma leftDistribute {a b c : M} (f g : a --> b) (h : b --> c) : (f + g) · h = f · h + g · h.
  Proof.
    apply rightCompHomo.
  Qed.
  Lemma ThroughZeroIsZero (a b:M) (Z : Zero M) (f : a --> Z) (g : Z --> b) : f · g = 0.
  Proof.
    intermediate_path ((0:a-->Z) · g).
    - apply (maponpaths (postcomp_with g)). apply ArrowsToZero.
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
  Lemma IsoWithKernel {x y z z':M} (f : x --> y) (g : y --> z) (h : z --> z') :
    isKernel' f g -> is_z_isomorphism h -> isKernel' f (g·h).
  Proof.
    intros i j.
    exists (assoc _ _ _ @ maponpaths (postcomp_with _) (pr1 i) @ zeroLeft h).
    intros w q e.
    apply iscontraprop1.
    { apply invproofirrelevance. intros [r R] [s S]. apply subtypeEquality_prop; cbn.
      apply (KernelIsMonic _ _ i). exact (R @ !S). }
    apply (pr2 i).
    refine (post_comp_with_iso_is_inj _ _ _ h (is_iso_from_is_z_iso h j) _ _ _ _).
    refine (! assoc _ _ _ @ e @ ! zeroLeft _).
  Qed.
  Lemma KernelOfZeroMapIsIso {x y z:M} (g : x --> y) : isKernel' g (0 : y --> z) -> is_iso g.
  (* compare with KernelofZeroArrow_is_iso *)
  Proof.
    intros [_ ke]. use is_iso_from_is_z_iso. use (is_iso'_to_is_z_iso M).
    intros T h. exact (ke _ _ (zeroRight _)).
  Defined.
  Lemma CokernelOfZeroMapIsIso {x y z:M} (g : y --> z) : isCokernel' (0 : x --> y) g -> is_iso g.
  (* compare with CokernelofZeroArrow_is_iso *)
  Proof.
    (* this proof makes efficient use of the definition of is_iso *)
    intros [_ co] T h. exact (co _ _ (zeroLeft _)).
  Defined.
  Lemma KernelUniqueness {x x' y z : M} {f : x --> y} {f' : x' --> y} {g : y --> z} :
    isKernel' f g -> isKernel' f' g -> iscontr (IsoArrowTo (M:=M) f f').
  Proof.
    intros i j. apply iscontraprop1.
    - exact (IsoArrowTo_isaprop M f f' (KernelIsMonic f' g j)).
    - induction (iscontrpr1 (pr2 j _ f (pr1 i))) as [p P].
      induction (iscontrpr1 (pr2 i _ f' (pr1 j))) as [q Q].
      use tpair.
      + exists p. exists q. split.
        * apply (KernelIsMonic _ _ i). rewrite <- assoc. rewrite Q. rewrite P. rewrite id_left. reflexivity.
        * apply (KernelIsMonic _ _ j). rewrite <- assoc. rewrite P. rewrite Q. rewrite id_left. reflexivity.
      + cbn. exact P.
  Defined.
  Lemma CokernelUniqueness {x y z z' : M} {f : x --> y} {g : y --> z} {g' : y --> z'} :
    isCokernel' f g -> isCokernel' f g' -> iscontr (IsoArrowFrom (M:=M) g g').
  Proof.
    intros i j. apply iscontraprop1.
    - exact (IsoArrowFrom_isaprop M g g' (CokernelIsEpi f g i)).
    - induction (iscontrpr1 (pr2 j _ g (pr1 i))) as [p P].
      induction (iscontrpr1 (pr2 i _ g' (pr1 j))) as [q Q].
      use tpair.
      + exists q. exists p. split.
        * apply (CokernelIsEpi _ _ i). rewrite assoc. rewrite Q. rewrite P. rewrite id_right. reflexivity.
        * apply (CokernelIsEpi _ _ j). rewrite assoc. rewrite P. rewrite Q. rewrite id_right. reflexivity.
      + cbn. exact Q.
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
  Definition directSumMap {a b c d:M} (f : a --> b) (g : c --> d) : (a ⊕ c) --> (b ⊕ d)
    := BinDirectSumIndAr M f g _ _.
  Lemma directSumMapEqPr1 {a b c d:M} (f : a --> b) (g : c --> d) :
    directSumMap f g · to_Pr1 _ = to_Pr1 _ · f.
  Proof.
    apply BinDirectSumPr1Commutes.
  Qed.
  Lemma directSumMapEqPr2 {a b c d:M} (f : a --> b) (g : c --> d) :
    directSumMap f g · to_Pr2 _ = to_Pr2 _ · g.
  Proof.
    apply BinDirectSumPr2Commutes.
  Qed.
  Lemma directSumMapEqIn1 {a b c d:M} (f : a --> b) (g : c --> d) :
    to_In1 _ · directSumMap f g = f · to_In1 _.
  Proof.
    unfold directSumMap. rewrite BinDirectSumIndArEq. apply BinDirectSumIn1Commutes.
  Qed.
  Lemma directSumMapEqIn2 {a b c d:M} (f : a --> b) (g : c --> d) :
    to_In2 _ · directSumMap f g = g · to_In2 _.
  Proof.
    unfold directSumMap. rewrite BinDirectSumIndArEq. apply BinDirectSumIn2Commutes.
  Qed.
  Definition SwitchMap (a b:M) : a ⊕ b --> b ⊕ a := to_Pr1 _ · to_In2 _ + to_Pr2 _ · to_In1 _.
  Lemma SwitchMapEqn {a b:M} : SwitchMap a b · SwitchMap b a = 1.
  Proof.
    unfold SwitchMap.
    rewrite leftDistribute, 2 rightDistribute.
    rewrite <- assoc. rewrite (assoc (to_In2 (b ⊕ a))). rewrite DirectSumIn2Pr1.
    rewrite zeroLeft. rewrite zeroRight. rewrite lunax.
    rewrite <- assoc. rewrite (assoc (to_In2 (b ⊕ a))). rewrite (to_IdIn2 (b ⊕ a)). rewrite id_left.
    rewrite <- assoc. rewrite (assoc (to_In1 (b ⊕ a))). rewrite (to_IdIn1 (b ⊕ a)). rewrite id_left.
    rewrite <- assoc. rewrite (assoc (to_In1 (b ⊕ a))). rewrite DirectSumIn1Pr2. rewrite zeroLeft. rewrite zeroRight. rewrite runax.
    apply (to_BinOpId (a⊕b)).
  Defined.
  Definition SwitchIso (a b:M) : z_iso (a⊕b) (b⊕a).
  Proof.
    exists (SwitchMap _ _). exists (SwitchMap _ _). split; apply SwitchMapEqn.
  Defined.
  Definition change_binop (a b:M) (f g:a --> b) : to_binop _ _ f g = f+g := idpath _.
  Definition SwitchMapMapEqn {a b c d:M} (f : a --> b) (g : c --> d) :
    SwitchMap _ _ · directSumMap f g = directSumMap g f · SwitchMap _ _.
  Proof.
    unfold SwitchMap.
    rewrite leftDistribute, rightDistribute.
    rewrite assoc. rewrite directSumMapEqPr1.
    rewrite <- assoc. rewrite directSumMapEqIn2. rewrite assoc.
    apply maponpaths.
    rewrite <- assoc. rewrite directSumMapEqIn1.
    rewrite 2 assoc. rewrite directSumMapEqPr2.
    reflexivity.
  Qed.
  Definition directSumMapSwitch {a b c d:M} (f : a --> b) (g : c --> d) :
    IsoArrow (directSumMap f g) (directSumMap g f).
  Proof.
    exists (SwitchIso _ _). exists (SwitchIso _ _).
    apply SwitchMapMapEqn.
  Defined.
  Lemma SumOfKernels {x y z x' y' z' : M}
        (f : x --> y) (g : y --> z) (f' : x' --> y') (g' : y' --> z') :
    isKernel' f g -> isKernel' f' g' -> isKernel' (directSumMap f f') (directSumMap g g').
  Proof.
    intros i i'. split.
    { refine (BinDirectSumIndArComp _ _ _ _ _ _ _ _ @ ! _).
      apply ToBinDirectSumUnique.
      - exact (zeroLeft _ @ ! zeroRight _ @ maponpaths _ (! pr1 i)).
      - exact (zeroLeft _ @ ! zeroRight _ @ maponpaths _ (! pr1 i')). }
    intros w h e. apply iscontraprop1.
    2:{
      assert (e1 := ! assoc _ _ _
                      @ ! maponpaths (precomp_with _) (directSumMapEqPr1 _ _)
                      @ assoc _ _ _
                      @ maponpaths (postcomp_with _) e
                      @ zeroLeft _).
      assert (e2 := ! assoc _ _ _
                      @ ! maponpaths (precomp_with _) (directSumMapEqPr2 _ _)
                      @ assoc _ _ _
                      @ maponpaths (postcomp_with _) e
                      @ zeroLeft _).
      induction (iscontrpr1 (pr2 i  w (h · to_Pr1 _) e1)) as [h1 H1].
      induction (iscontrpr1 (pr2 i' w (h · to_Pr2 _) e2)) as [h2 H2].
      exists (ToBinDirectSum _ _ h1 h2).
      apply ToBinDirectSumsEq.
      + refine (! assoc _ _ _ @ _ @ H1).
        refine (maponpaths (precomp_with _) (directSumMapEqPr1 _ _) @ _).
        unfold precomp_with.
        refine (assoc _ _ _ @ _).
        apply (maponpaths (postcomp_with _)).
        apply BinDirectSumPr1Commutes.
      + refine (! assoc _ _ _ @ _ @ H2).
        refine (maponpaths (precomp_with _) (directSumMapEqPr2 _ _) @ _).
        unfold precomp_with.
        refine (assoc _ _ _ @ _).
        apply (maponpaths (postcomp_with _)).
        apply BinDirectSumPr2Commutes. }
    apply invproofirrelevance.
    intros [k K] [k' K'].
    apply subtypeEquality_prop; cbn.
    apply ToBinDirectSumsEq.
    - refine (KernelIsMonic _ _ i _ _ _ _).
      exact (! assoc _ _ _
               @ ! maponpaths (precomp_with k) (directSumMapEqPr1 f f')
               @ assoc _ _ _
               @ maponpaths (postcomp_with _) (K @ !K')
               @ ! assoc _ _ _
               @ maponpaths (precomp_with k') (directSumMapEqPr1 f f')
               @ assoc _ _ _).
    - refine (KernelIsMonic _ _ i' _ _ _ _).
      exact (! assoc _ _ _
               @ ! maponpaths (precomp_with k) (directSumMapEqPr2 f f')
               @ assoc _ _ _
               @ maponpaths (postcomp_with _) (K @ !K')
               @ ! assoc _ _ _
               @ maponpaths (precomp_with k') (directSumMapEqPr2 f f')
               @ assoc _ _ _).
  Qed.
  Lemma SumOfCokernels {x y z x' y' z' : M}
        (f : x --> y) (g : y --> z) (f' : x' --> y') (g' : y' --> z') :
    isCokernel' f g -> isCokernel' f' g' -> isCokernel' (directSumMap f f') (directSumMap g g').
  Proof.
    intros i i'. split.
    { refine (BinDirectSumIndArComp _ _ _ _ _ _ _ _ @ ! _).
      apply ToBinDirectSumUnique.
      - exact (zeroLeft _ @ ! zeroRight _ @ maponpaths _ (! pr1 i)).
      - exact (zeroLeft _ @ ! zeroRight _ @ maponpaths _ (! pr1 i')). }
    intros w h e. apply iscontraprop1.
    2:{
      assert (e1 := assoc _ _ _
                      @ ! maponpaths (postcomp_with _) (directSumMapEqIn1 _ _)
                      @ ! assoc _ _ _
                      @ maponpaths (precomp_with _) e
                      @ zeroRight _).
      assert (e2 := assoc _ _ _
                      @ ! maponpaths (postcomp_with _) (directSumMapEqIn2 _ _)
                      @ ! assoc _ _ _
                      @ maponpaths (precomp_with _) e
                      @ zeroRight _).
      induction (iscontrpr1 (pr2 i  w (to_In1 _ · h) e1)) as [h1 H1].
      induction (iscontrpr1 (pr2 i' w (to_In2 _ · h) e2)) as [h2 H2].
      exists (FromBinDirectSum _ _ h1 h2).
      apply FromBinDirectSumsEq.
      + refine (assoc _ _ _ @ _ @ H1).
        refine (maponpaths (postcomp_with _) (directSumMapEqIn1 _ _) @ _).
        unfold postcomp_with.
        refine (! assoc _ _ _ @ _).
        apply (maponpaths (precomp_with _)).
        apply BinDirectSumIn1Commutes.
      + refine (assoc _ _ _ @ _ @ H2).
        refine (maponpaths (postcomp_with _) (directSumMapEqIn2 _ _) @ _).
        unfold postcomp_with.
        refine (! assoc _ _ _ @ _).
        apply (maponpaths (precomp_with _)).
        apply BinDirectSumIn2Commutes. }
    apply invproofirrelevance.
    intros [k K] [k' K'].
    apply subtypeEquality_prop; cbn.
    apply FromBinDirectSumsEq.
    - refine (CokernelIsEpi _ _ i _ _ _ _).
      exact (assoc _ _ _
               @ ! maponpaths (postcomp_with k) (directSumMapEqIn1 g g')
               @ ! assoc _ _ _
               @ maponpaths (precomp_with _) (K @ !K')
               @ assoc _ _ _
               @ maponpaths (postcomp_with k') (directSumMapEqIn1 g g')
               @ ! assoc _ _ _).
    - refine (CokernelIsEpi _ _ i' _ _ _ _).
      exact (assoc _ _ _
               @ ! maponpaths (postcomp_with k) (directSumMapEqIn2 g g')
               @ ! assoc _ _ _
               @ maponpaths (precomp_with _) (K @ !K')
               @ assoc _ _ _
               @ maponpaths (postcomp_with k') (directSumMapEqIn2 g g')
               @ ! assoc _ _ _).
  Qed.
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
    isKernelCokernelPair i p -> isKernelCokernelPair i' p -> iscontr (IsoArrowTo (M:=M) i i').
  Proof.
    intros [k _] [k' _]. exact (KernelUniqueness k k').
  Defined.
  Lemma PairUniqueness2 {A B C C':M} (i : A --> B) (p: B --> C) (p': B --> C') :
    isKernelCokernelPair i p -> isKernelCokernelPair i p' -> iscontr (IsoArrowFrom (M:=M) p p').
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
  Lemma SumOfKernelCokernelPairs {x y z x' y' z' : M}
        {f : x --> y} {g : y --> z} {f' : x' --> y'} {g' : y' --> z'}
    : isKernelCokernelPair f g -> isKernelCokernelPair f' g' -> isKernelCokernelPair (directSumMap f f') (directSumMap g g').
  Proof.
    intros i i'.
    exists (SumOfKernels   f g f' g' (pr1 i) (pr1 i')).
    exact  (SumOfCokernels f g f' g' (pr2 i) (pr2 i')).
  Qed.
End KernelCokernelPairs.
Delimit Scope excat with excat.
Local Open Scope excat.
Section theDefinition.
  Definition AddCatWithExactness := ∑ M:Additive, MorphismPair M -> hProp. (* properties added below *)
  Coercion AE_to_AC (ME : AddCatWithExactness) : Additive := pr1 ME.
  Context (M : AddCatWithExactness).
  Definition isExact (E : MorphismPair M) : hProp := pr2 M E.
  Definition isExact2 {A B C:M} (f:A-->B) (g:B-->C) := isExact (mk_MorphismPair f g).
  Definition isAdmissibleMonomorphism {A B:M} (i : A --> B) : hProp :=
    ∃ C (p : B --> C), isExact2 i p.
  Definition AdmissibleMonomorphism (A B:M) : Type :=
    ∑ (i : A --> B), isAdmissibleMonomorphism i.
  Coercion AdmMonoToMap {A B:M} : AdmissibleMonomorphism A B -> A --> B := pr1.
  Coercion AdmMonoToMap' {A B:M} : AdmissibleMonomorphism A B -> (A --> B)%cat := pr1.
  Notation "A ↣ B" := (AdmissibleMonomorphism A B) : excat.
  Definition isAdmissibleEpimorphism {B C:M} (p : B --> C) : hProp :=
    ∃ A (i : A --> B), isExact2 i p.
  Definition AdmissibleEpimorphism (B C:M) : Type :=
    ∑ (p : B --> C), isAdmissibleEpimorphism p.
  Coercion AdmEpiToMap {B C:M} : AdmissibleEpimorphism B C -> B --> C := pr1.
  Coercion AdmEpiToMap' {B C:M} : AdmissibleEpimorphism B C -> (B --> C)%cat := pr1.
  Notation "B ↠ C" := (AdmissibleEpimorphism B C) : excat.
  (** The following definition is definition 2.1 from the paper of Bühler. *)
  Local Definition ExactCategoryProperties : hProp :=
      (∀ P Q, MorphismPairIsomorphism (M:=M) P Q ⇒ isExact P ⇒ isExact Q) ∧
      (∀ A, isAdmissibleMonomorphism (identity A)) ∧
      (∀ A, isAdmissibleEpimorphism (identity A)) ∧
      (∀ P, isExact P ⇒ isKernelCokernelPair (Mor1 P) (Mor2 P)) ∧
      (∀ A B C (f : A --> B) (g : B --> C),
          isAdmissibleMonomorphism f ⇒ isAdmissibleMonomorphism g ⇒
          isAdmissibleMonomorphism (f · g)) ∧
      (∀ A B C (f : A --> B) (g : B --> C),
          isAdmissibleEpimorphism f ⇒ isAdmissibleEpimorphism g ⇒
          isAdmissibleEpimorphism (f · g)) ∧
      (∀ A B C (f : A --> B) (g : C --> B),
          isAdmissibleEpimorphism f ⇒
          ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)) ∧
      (∀ A B C (f : B --> A) (g : B --> C),
          isAdmissibleMonomorphism f ⇒
          ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO)).
End theDefinition.

Arguments isExact {_}.
Arguments isExact2 {_ _ _ _}.

Definition ExactCategory := ∑ (ME:AddCatWithExactness), ExactCategoryProperties ME.
Coercion ExCatToAddCatWithExactness (E:ExactCategory) : AddCatWithExactness := pr1 E.

Notation "A ↣ B" := (AdmissibleMonomorphism _ A B) : excat.
Notation "B ↠ C" := (AdmissibleEpimorphism _ B C) : excat.

Arguments isAdmissibleMonomorphism {_ _ _}.
Arguments isAdmissibleEpimorphism {_ _ _}.

Section ExactCategoryAccessFunctions.
  Context {M:ExactCategory}.
  Definition EC_IsomorphicToExact {P Q:MorphismPair M}
    : MorphismPairIsomorphism (M:=M) P Q ⇒ isExact P ⇒ isExact Q
    := pr12 M P Q.
  Definition EC_IdentityIsMono (A:M) : isAdmissibleMonomorphism (identity A)
    := pr122 M A.
  Definition EC_IdentityIsEpi (A:M) : isAdmissibleEpimorphism (identity A)
    := pr122 (pr2 M) A.
  Definition EC_ExactToKernelCokernel {P : MorphismPair M} :
    isExact P ⇒ isKernelCokernelPair (Mor1 P) (Mor2 P)
    := pr122 (pr22 M) P.
  Definition EC_ExactToKernel {P : MorphismPair M} :
    isExact P ⇒ isKernel' (Mor1 P) (Mor2 P)
    := λ i, (pr1 (pr122 (pr22 M) P i)).
  Definition EC_ExactToCokernel {P : MorphismPair M} :
    isExact P ⇒ isCokernel' (Mor1 P) (Mor2 P)
    := λ i, (pr2 (pr122 (pr22 M) P i)).
  Definition EC_ComposeMono {A B C:M} (f : A --> B) (g : B --> C) :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism g ->
    isAdmissibleMonomorphism (f · g)
    := pr122 (pr222 M) A B C f g.
  Definition EC_ComposeEpi {A B C:M} (f : A --> B) (g : B --> C) :
    isAdmissibleEpimorphism f ⇒ isAdmissibleEpimorphism g ⇒
    isAdmissibleEpimorphism (f · g)
    := pr122 (pr222 (pr2 M)) A B C f g.
  Definition EC_PullbackEpi {A B C:M} (f : A --> B) (g : C --> B) :
    isAdmissibleEpimorphism f ⇒
    ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)
    := pr122 (pr222 (pr22 M)) A B C f g.
  Definition EC_PushoutMono {A B C:M} (f : B --> A) (g : B --> C) :
    isAdmissibleMonomorphism f ⇒
    ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO)
    := pr222 (pr222 (pr22 M)) A B C f g.
End ExactCategoryAccessFunctions.

Section ExactCategoryFacts.
  Context {M : ExactCategory}.
  Lemma ExactToAdmMono {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isAdmissibleMonomorphism i.
  Proof.
    intros e. exact (hinhpr(C,,p,,e)).
  Qed.
  Lemma ExactToAdmEpi {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isAdmissibleEpimorphism p.
  Proof.
    intros e. exact (hinhpr(A,,i,,e)).
  Qed.
  Lemma ExactToMono {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isMonic i.
  Proof.
    intros e. exact (KernelIsMonic i p (EC_ExactToKernel e)).
  Qed.
  Lemma ExactToEpi {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isEpi p.
  Proof.
    intros e. refine (CokernelIsEpi i p (EC_ExactToCokernel e)).
  Qed.
  Lemma ExactSequenceFromMono {A B C:M} (i : A --> B) (p : B --> C) :
    isCokernel' i p -> isAdmissibleMonomorphism i -> isExact2 i p.
  Proof.
    intros co mo. apply (squash_to_hProp mo); clear mo; intros [C' [p' e]].
    assert (co' := pr2 (EC_ExactToKernelCokernel e) : isCokernel' i p').
    assert (R := iscontrpr1 (CokernelUniqueness co' co)). induction R as [R r].
    use (EC_IsomorphicToExact _ e).
    exists (identity_z_iso _). exists (identity_z_iso _).
    exact (R ,, (id_left _ @ ! id_right _) ,, id_left _ @ ! r).
  Qed.
  Lemma ExactSequenceFromEpi {A B C:M} (i : A --> B) (p : B --> C) :
    isKernel' i p -> isAdmissibleEpimorphism p -> isExact2 i p.
  Proof.
    intros co mo. apply (squash_to_hProp mo); clear mo; intros [A' [i' e]].
    assert (co' := pr1 (EC_ExactToKernelCokernel e) : isKernel' i' p).
    assert (R := iscontrpr1 (KernelUniqueness co' co)). induction R as [R r].
    use (EC_IsomorphicToExact _ e).
    exact (R ,, (identity_z_iso _) ,, (identity_z_iso _) ,, (r @ ! id_right _) ,, (id_left _ @ ! id_right _)).
  Qed.
  Lemma ExactSequence10 (A:M) (Z:Zero M) : isExact2 (identity A) (0 : A --> Z).
  Proof.
    exact (ExactSequenceFromMono _ _ (pr2 (kerCoker10 Z A)) (EC_IdentityIsMono A)).
  Qed.
  Lemma ExactSequence01 (A:M) (Z:Zero M) : isExact2 (0 : Z --> A) (identity A).
  Proof.
    exact (ExactSequenceFromEpi _ _ (pr1 (kerCoker01 Z A)) (EC_IdentityIsEpi A)).
  Qed.
  Lemma MonoFromZero (Z:Zero M) (A:M) : Z ↣ A.
  Proof.
    exists (0 : Z --> A). apply hinhpr. exists A. exists (identity A). use ExactSequence01.
  Defined.
  Lemma EpiToZero (A:M) (Z:Zero M) : A ↠ Z.
  Proof.
    exists (0 : A --> Z). apply hinhpr. exists A. exists (identity A). use ExactSequence10.
  Defined.
  Lemma FromZeroIsMono (Z:Zero M) (A:M) : isAdmissibleMonomorphism (0 : Z --> A).
  Proof.
    apply MonoFromZero.
  Defined.
  Lemma ToZeroIsEpi (A:M) (Z:Zero M) : isAdmissibleEpimorphism (0 : A --> Z).
  Proof.
    apply EpiToZero.
  Defined.
  Lemma IsomMono1 {A B B':M} (f : A --> B) (f' : A --> B') :
    IsoArrowFrom f f' -> isAdmissibleMonomorphism f -> isAdmissibleMonomorphism f'.
  Proof.
    intros [i I] E. apply (squash_to_hProp E); clear E; intros [C [p E]].
    apply hinhpr. exists C. exists (z_iso_inv i · p). use (EC_IsomorphicToExact _ E).
    exists (identity_z_iso A). exists i. exists (identity_z_iso C). split; cbn.
    - exact (id_left _ @ ! I).
    - refine (assoc _ _ _ @ _ @ id_left _ @ ! id_right _).
      apply (maponpaths (λ k, k · p)). apply z_iso_inv_after_z_iso.
  Qed.
  Lemma IsomEpi1 {A A' B:M} (f : A --> B) (f' : A' --> B) :
    IsoArrowTo f f' -> isAdmissibleEpimorphism f -> isAdmissibleEpimorphism f'.
  Proof.
    intros [i I] E. apply (squash_to_hProp E); clear E; intros [C [p E]].
    apply hinhpr. exists C. exists (p · i). use (EC_IsomorphicToExact _ E).
    exists (identity_z_iso _). exists i. exists (identity_z_iso _). split; cbn.
    - exact (id_left _).
    - exact (I @ ! id_right _).
  Qed.
  Lemma IsomMono {A A' B B':M} (f : A --> B) (f' : A' --> B') :
    IsoArrow f f' -> isAdmissibleMonomorphism f -> isAdmissibleMonomorphism f'.
  Proof.
    intros [g [h e]] i. apply (squash_to_hProp i); clear i; intros [C [p E]].
    apply hinhpr. exists C. exists (z_iso_inv h · p). use (EC_IsomorphicToExact _ E).
    exists g; exists h; exists (identity_z_iso C); cbn. exists e.
    refine (assoc _ _ _ @ maponpaths (postcomp_with p) _ @ id_left p @ ! id_right p).
    apply z_iso_inv_after_z_iso.
  Qed.
  Lemma IsoIsMono {A B:M} (f:z_iso A B) : isAdmissibleMonomorphism (z_iso_mor f).
  Proof.
    use (IsomMono1 (identity A) (z_iso_mor f)).
    - exists f. apply id_left.
    - apply EC_IdentityIsMono.
  Qed.
  Lemma IsoIsEpi {A B:M} (f:z_iso A B) : isAdmissibleEpimorphism (z_iso_mor f).
  Proof.
    use (IsomEpi1 (identity B) (z_iso_mor f)).
    - exists (z_iso_inv f). apply z_iso_after_z_iso_inv.
    - apply EC_IdentityIsEpi.
  Qed.
  Lemma DirectSumToExact {A B:M} (S:BinDirectSum A B) : isExact2 (to_In1 S) (to_Pr2 S).
  Proof.
    use ExactSequenceFromEpi.
    { exact (PairToKernel (kerCokerDirectSum S)). }
    set (Z := to_Zero M).
    set (pb := DirectSumToPullback S Z).
    change (isAdmissibleEpimorphism (PullbackPr2 pb)).
    assert (Q := EC_PullbackEpi (0 : A --> Z) (0 : B --> Z) (ToZeroIsEpi A Z)).
    apply (squash_to_hProp Q); clear Q; intros [pb' R'].
    exact (IsomEpi1 (PullbackPr2 pb') (PullbackPr2 pb) (pullbackiso2 pb' pb) R').
  Qed.
  Lemma DirectSumToExact' {A B:M} (S:BinDirectSum A B) : isExact2 (to_In2 S) (to_Pr1 S).
  Proof.
    exact (DirectSumToExact (reverseBinDirectSum S)).
  Qed.
  Lemma DirectSumIn1Mono {A B:M} (S:BinDirectSum A B) : isAdmissibleMonomorphism (to_In1 S : A --> S).
  Proof.
    exact (hinhpr (B,,to_Pr2 S,,DirectSumToExact S)).
  Qed.
  Lemma DirectSumIn2Mono {A B:M} (S:BinDirectSum A B) : isAdmissibleMonomorphism (to_In2 S : B --> S).
  Proof.
    exact (hinhpr (A,,to_Pr1 S,,DirectSumToExact' S)).
  Qed.
  Lemma DirectSumPr1Epi {A B:M} (S:BinDirectSum A B) : isAdmissibleEpimorphism (to_Pr1 S : S --> A).
  Proof.
    exact (hinhpr (B,,to_In2 S,,DirectSumToExact' S)).
  Qed.
  Lemma DirectSumPr2Epi {A B:M} (S:BinDirectSum A B) : isAdmissibleEpimorphism (to_Pr2 S : S --> B).
  Proof.
    exact (hinhpr (A,,to_In1 S,,DirectSumToExact S)).
  Qed.
  Lemma ExactPushout {A B C A':M} (i : A --> B) (p : B --> C)
        (pr : isExact2 i p) (r : A --> A') :
    ∃ (po : Pushout i r),
      isExact2 (PushoutIn2 po) (pr1 (PairPushoutMap i p (EC_ExactToKernelCokernel pr) r po)).
  Proof.
    assert (I := hinhpr (C ,, p ,, pr) : isAdmissibleMonomorphism i).
    assert (R := EC_PushoutMono i r I).
    apply (squash_to_hProp R); clear R; intros [po J]; apply hinhpr.
    exists po. use ExactSequenceFromMono.
    { exact (PairPushoutCokernel i p (EC_ExactToKernelCokernel pr) r po). }
    exact J.
  Qed.
  Lemma ExactPullback {A B C A':M} (i : A <-- B) (p : B <-- C)
        (pr : isExact2 p i)
        (r : A <-- A') :
    ∃ (pb : Pullback i r),
      isExact2 (pr1 (PairPullbackMap i p (EC_ExactToKernelCokernel pr) r pb)) (PullbackPr2 pb).
  Proof.
    assert (I := hinhpr (C ,, p ,, pr) : isAdmissibleEpimorphism i).
    assert (R := EC_PullbackEpi i r I).
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
  Lemma MonoPlusIdentity {A B:M} (f:A-->B) (C:M) :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism (directSumMap f (identity C)).
  Proof.
    (* see Bühler's 2.9 *)
    intro i. apply (squash_to_hProp i). intros [D [p j]].
    apply hinhpr. exists D. exists (to_Pr1 _ · p). apply ExactSequenceFromEpi.
    2:{ apply EC_ComposeEpi.
        - apply DirectSumPr1Epi.
        - exact (hinhpr(A,,f,,j)). }
    assert (Z := to_Zero M).
    assert (m := pr1 (SumOfKernelCokernelPairs
                   (EC_ExactToKernelCokernel j : isKernelCokernelPair f p)
                   (kerCoker10 Z C : isKernelCokernelPair (identity C) 0))).
    assert (R : directSumMap p 0 · to_Pr1 (D⊕Z) = to_Pr1 (B⊕C) · p).
    { apply directSumMapEqPr1. }
    induction R. apply IsoWithKernel.
    { exact m. }
    exists (to_In1 _). split.
    { refine (! runax _ (to_Pr1 (D ⊕ Z) · to_In1 (D ⊕ Z)) @ ! _ @ to_BinOpId (D⊕Z)).
      apply maponpaths. apply ThroughZeroIsZero. }
    { refine (to_IdIn1 (D⊕Z)). }
  Qed.
  Lemma IdentityPlusMono {B C:M} (A:M) (f:B-->C) :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism (directSumMap (identity A) f).
  Proof.
    intros i.
    use IsomMono.
    - exact (B ⊕ A).
    - exact (C ⊕ A).
    - exact (directSumMap f (identity A)).
    - exists (SwitchIso _ _). exists (SwitchIso _ _). apply SwitchMapMapEqn.
    - apply MonoPlusIdentity. exact i.
  Defined.
  Lemma SumOfExactSequences {A B C A' B' C':M}
        (f : A --> B) (g : B --> C) (f' : A' --> B') (g' : B' --> C') :
    isExact2 f g -> isExact2 f' g' -> isExact2 (directSumMap f f') (directSumMap g g').
  Proof.
    (* see Bühler's 2.9 *)
    intros i i'. apply ExactSequenceFromMono.
    { use SumOfCokernels.
      - exact (EC_ExactToCokernel i).
      - exact (EC_ExactToCokernel i'). }
    set (j := directSumMap f (identity B')).
    set (k := directSumMap (identity A) f').
    assert (kj : k · j = directSumMap f f').
    { apply ToBinDirectSumUnique.
      - refine (! assoc _ _ _ @ _). intermediate_path (k · (to_Pr1 _ · f)).
        + apply maponpaths. apply directSumMapEqPr1.
        + refine (assoc _ _ _ @ _). apply (maponpaths (postcomp_with _)).
          exact (directSumMapEqPr1 _ _ @ id_right _).
      - refine (! assoc _ _ _ @ _). intermediate_path (k · (to_Pr2 _ · (identity B'))).
        + apply maponpaths. apply directSumMapEqPr2.
        + refine (assoc _ _ _ @ id_right _ @ _). apply directSumMapEqPr2. }
    induction kj. use (EC_ComposeMono k j).
    2:{ apply MonoPlusIdentity. exact (ExactToAdmMono i). }
    apply IdentityPlusMono. exact (ExactToAdmMono i').
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
