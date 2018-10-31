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
Require Export UniMath.CategoryTheory.limits.Opp.
Require Export UniMath.CategoryTheory.CategoriesWithBinOps.
Require Export UniMath.CategoryTheory.Categories.
Require Export UniMath.CategoryTheory.opp_precat.
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
(* Local Notation "a --> b" := (hSetpair (precategory_morphisms a b) (homset_property _ a b)) : Cat. *)
Local Notation "a --> b" := (to_abgr a b) : addcat.
Local Notation "b <-- a" := (precategory_morphisms a b) (only parsing) : cat.
(* Local Notation "b <-- a" := (hSetpair (precategory_morphisms a b) (homset_property _ a b)) (only parsing) : Cat. *)
Local Notation "b <-- a" := (to_abgr a b) (only parsing) : addcat.
(* Local Notation "f · g" := (compose f g : to_abgr _ _) : Cat. *)
Local Notation "f · g" := (compose f g : to_abgr _ _) : addcat.
(* Local Notation "g ∘ f" := (compose f g : to_abgr _ _) : Cat. *)
Local Notation "g ∘ f" := (compose f g : to_abgr _ _) : addcat.
Local Notation "0" := (ZeroArrow (to_Zero _) _ _) : cat.
Local Notation "0" := (unel _ : to_abgr _ _) : addcat.
Local Notation "1" := (identity _ : to_abgr _ _) : addcat.
(* Local Notation "f = g" := (eqset f g) : Cat. *)
Local Notation "f = g" := (eqset f g) : addcat.
Local Notation "f - g" := (@op _ f (grinv _ g) : to_abgr _ _) : addcat.
Local Notation "A ⊕ B" := (to_BinDirectSums _ A B) : addcat.
Local Notation "'π₁'" := (to_Pr1 _) : addcat.
Local Notation "'π₂'" := (to_Pr2 _) : addcat.
Local Notation "'ι₁'" := (to_In1 _) : addcat.
Local Notation "'ι₂'" := (to_In2 _) : addcat.

Local Open Scope cat.

Section Precategories.             (* move upstream *)
  Definition iso_to_z_iso {C : precategory} {b c : C} (f : iso b c) : z_iso b c
    := pr1 f ,, is_z_iso_from_is_iso (pr1 f) (pr2 f).
  Definition z_iso_to_iso {C : precategory} {b c : C} (f : z_iso b c) : iso b c
    := pr1 f ,, is_iso_from_is_z_iso (pr1 f) (pr2 f).
  Definition is_iso' {C : precategory} {b c : C} (f : b --> c) :=
    ∏ a, isweq (postcomp_with f (a:=a)).
  Lemma is_z_iso_from_is_iso' (C : precategory) {b c : C} (f : b --> c) :
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
  Goal ∏ (C : precategory) (a b : C), @iso C^op b a -> @iso C a b.
  Proof.
    intros C a b f.
    exact (opp_iso f).
  Defined.
  Goal ∏ (C : precategory) (a b : C), @z_iso C^op b a -> @z_iso C a b.
  Proof.
    intros C a b f.
    exact (opp_z_iso f).
  Defined.
  Goal ∏ (C:precategory) (a b:C) (f: a --> b), isMonic (C:=C) f = isEpi (C:=C^op) f.
    reflexivity.
  Defined.
  Goal ∏ (C:precategory) (a b:C) (f: a --> b), isEpi (C:=C) f = isMonic (C:=C^op) f.
    reflexivity.
  Defined.
  (** Here's why we prefer to use z_iso instead of iso : *)
  Goal ∏ (C:precategory) (a b:C) (f:z_iso a b), z_iso_inv (z_iso_inv f) = f.
    reflexivity.
  Defined.
  Goal ∏ (C:precategory) (a b:C) (f:z_iso (C:=C) a b), opp_z_iso (opp_z_iso f) = f.
    reflexivity.
  Defined.
  Goal ∏ (C:precategory) (a b:C) (f:z_iso (C:=C^op) b a), opp_z_iso (opp_z_iso f) = f.
    reflexivity.
  Defined.
  Goal ∏ (C:precategory) (a b:C) (f:iso a b), iso_inv_from_iso (iso_inv_from_iso f) = f.
    Fail reflexivity.
  Abort.
  Goal ∏ (C:precategory) (a b:C) (f:iso a b), opp_iso (opp_iso f) = f.
    Fail reflexivity.
  Abort.
End Precategories.

Import AddNotation.

Section MorphismPairs.          (* move upstream *)
  Context {M : precategory}.
  Lemma reverseCommIsoSquare {P Q P' Q':M} (f:P'-->P) (g:Q'-->Q) (i:z_iso P' Q') (j:z_iso P Q) :
    i · g = f · j -> z_iso_inv i · f = g · z_iso_inv j.
  Proof.
    intros l.
    refine (! id_right _ @ _).
    refine (maponpaths _ (! is_inverse_in_precat1 (z_iso_is_inverse_in_precat j)) @ _).
    refine (! assoc (z_iso_inv i) _ _ @ _).
    refine (maponpaths _ (assoc f _ _) @ _).
    refine (maponpaths (precomp_with (z_iso_inv i)) (maponpaths (postcomp_with (z_iso_inv_mor j)) (!l)) @ _);
      unfold precomp_with, postcomp_with.
    refine (maponpaths _ (! assoc _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (maponpaths (postcomp_with (g · z_iso_inv_mor j)) (is_inverse_in_precat2 (z_iso_is_inverse_in_precat i)) @ _);
      unfold postcomp_with.
    exact (id_left _).
  Qed.
  Lemma reverseCommIsoSquare' {P Q P' Q':M} (f:P'-->P) (g:Q'-->Q) (i:z_iso P' Q') (j:z_iso P Q) :
    f · j = i · g -> g · z_iso_inv j = z_iso_inv i · f.
  Proof.
    intros l. refine (! _). apply reverseCommIsoSquare. refine (! _). exact l.
  Qed.
  Definition MorphismPairMap (P Q : MorphismPair M) :=
    ∑ (f : Ob1 P --> Ob1 Q) (g : Ob2 P --> Ob2 Q) (h : Ob3 P --> Ob3 Q),
    f · Mor1 Q = Mor1 P · g  ×  g · Mor2 Q = Mor2 P · h.
  Definition Map1 {P Q : MorphismPair M} (f : MorphismPairMap P Q) : Ob1 P --> Ob1 Q := pr1 f.
  Definition Map2 {P Q : MorphismPair M} (f : MorphismPairMap P Q) : Ob2 P --> Ob2 Q := pr12 f.
  Definition Map3 {P Q : MorphismPair M} (f : MorphismPairMap P Q) : Ob3 P --> Ob3 Q := pr122 f.
  Definition MorphismPairIsomorphism (P Q : MorphismPair M) :=
    ∑ (f : z_iso (Ob1 P) (Ob1 Q)) (g : z_iso (Ob2 P) (Ob2 Q)) (h : z_iso (Ob3 P) (Ob3 Q)),
    ( f · Mor1 Q = Mor1 P · g
      ×
      Mor1 P · g = f · Mor1 Q )
    ×
    ( g · Mor2 Q = Mor2 P · h
      ×
      Mor2 P · h = g · Mor2 Q ).
  Definition InverseMorphismPairIsomorphism {P Q : MorphismPair M} :
    MorphismPairIsomorphism P Q -> MorphismPairIsomorphism Q P.
  Proof.
    intros f.
    exists (z_iso_inv (pr1 f)). exists (z_iso_inv (pr12 f)). exists (z_iso_inv (pr122 f)).
    split.
    - split.
      + apply reverseCommIsoSquare. exact (pr11 (pr222 f)).
      + apply reverseCommIsoSquare'. exact (pr21 (pr222 f)).
    - split.
      + apply reverseCommIsoSquare. exact (pr12 (pr222 f)).
      + apply reverseCommIsoSquare'. exact (pr22 (pr222 f)).
  Defined.
  Definition mk_MorphismPairIsomorphism
             (P Q : MorphismPair M)
             (f : z_iso (Ob1 P) (Ob1 Q))
             (g : z_iso (Ob2 P) (Ob2 Q))
             (h : z_iso (Ob3 P) (Ob3 Q)) :
    f · Mor1 Q = Mor1 P · g ->
    g · Mor2 Q = Mor2 P · h -> MorphismPairIsomorphism P Q
    := λ r s, (f,,g,,h,,(r,,!r),,(s,,!s)).
  Goal ∏ (P Q : MorphismPair M) (f:MorphismPairIsomorphism P Q),
       InverseMorphismPairIsomorphism (InverseMorphismPairIsomorphism f) = f.
  Proof.
    (* Because this fails, we will have two (dual) properties in the definition
       of exact category, so we can get duality to work better. *)
    Fail reflexivity.
  Abort.
End MorphismPairs.

Section OppositeMorphismPairs.
  Definition oppositeMorphismPair {M:precategory} (p:MorphismPair M) : MorphismPair (M^op)
    := pr122 p,,pr12 p,,pr1 p,,pr2 (pr222 p),,pr1 (pr222 p).
  Goal ∏ (M:precategory) (P:MorphismPair M), oppositeMorphismPair (oppositeMorphismPair P) = P.
  Proof.
    reflexivity.
  Qed.
  Goal ∏ (M:precategory) (p:MorphismPair (M^op)), MorphismPair M.
    intros. exact (oppositeMorphismPair p).
  Qed.
  Definition oppositeMorphismPairIsomorphism {M:precategory} {P Q: MorphismPair M} :
    MorphismPairIsomorphism P Q -> MorphismPairIsomorphism (oppositeMorphismPair Q) (oppositeMorphismPair P)
    := λ f, opp_z_iso (pr122 f),,
            opp_z_iso (pr12 f),,
            opp_z_iso (pr1 f),,
            (pr22 (pr222 f),,pr12 (pr222 f)),,
            (pr21 (pr222 f),,pr11 (pr222 f)).
  Goal ∏ (M:precategory) (P Q : MorphismPair M^op) (f:MorphismPairIsomorphism P Q),
    oppositeMorphismPairIsomorphism (oppositeMorphismPairIsomorphism f) = f.
  Proof.
    reflexivity.
  Qed.
  Goal ∏ (M:precategory) (P Q : MorphismPair M^op),
   MorphismPairIsomorphism (M:=M^op) P Q ->
   MorphismPairIsomorphism (M:=M) (oppositeMorphismPair Q) (oppositeMorphismPair P).
  Proof.
    intros M P Q. exact (oppositeMorphismPairIsomorphism (M:=M^op)).
  Qed.
End OppositeMorphismPairs.

Section Pullbacks.              (* move upstream *)
  Context {M : precategory}.
  Goal ∏ (A B C:M) (f : A --> C) (g : B --> C), Pullback f g = Pushout (C:=M^op) f g.
    reflexivity.
  Defined.
  Goal ∏ (A B C:M) (f : A --> C) (g : A --> C), Pushout f g = Pullback (C:=M^op) f g.
    reflexivity.
  Defined.
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
  (* this definition of IsoArrow is asymmetric *)
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
Section OppositeIsoArrows.
  Definition opposite_IsoArrowTo {M:precategory} {A A' B:M} {g : A --> B} {g' : A' --> B} :
    IsoArrowTo g g' -> IsoArrowFrom (M:=M^op) g' g.
  Proof.
    intros i. use tpair.
    - exact (opp_z_iso (pr1 i)).
    - cbn. exact (pr2 i).
  Defined.
  Definition opposite_IsoArrowFrom {M:precategory} {A B B':M} {g : A --> B} {g' : A --> B'} :
    IsoArrowFrom g g' -> IsoArrowTo (M:=M^op) g' g.
  Proof.
    intros i. use tpair.
    - exact (opp_z_iso (pr1 i)).
    - cbn. exact (pr2 i).
  Defined.
  Goal ∏ (M:precategory) (A A' B:M) (g : A --> B) (g' : A' --> B) (i:IsoArrowTo g g'),
    opposite_IsoArrowFrom (opposite_IsoArrowTo i) = i.
  Proof.
    reflexivity.
  Defined.
  Goal ∏ (M:precategory) (A B B':M) (g : A --> B) (g' : A --> B') (i:IsoArrowFrom g g'),
    opposite_IsoArrowTo (opposite_IsoArrowFrom i) = i.
  Proof.
    reflexivity.
  Defined.
  Definition opposite_IsoArrow {M:precategory} {A A' B B':M} (g : A --> B) (g' : A' --> B') :
    IsoArrow g g' -> IsoArrow (M:=M^op) (opp_mor g') (opp_mor g).
  Proof.
    intros i.
    exists (opp_z_iso (pr12 i)).
    exists (opp_z_iso (pr1 i)).
    exact (! pr22 i).
  Defined.
End OppositeIsoArrows.

(* Local Open Scope Cat. *)
Local Open Scope cat.

Section Pullbacks2.              (* move upstream *)
  Context (M : category).        (* giving this argument explicitly makes it work better (?) *)
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

Section AdditiveBasics.         (* move upstream *)
  Context {M : Additive}.
  Lemma zeroLeft {a b c : M} (f : b --> c) : (0 : a --> b) · f = 0.
  (* compare with ZeroArrow_comp_left *)
  Proof.
    refine (_ @ ZeroArrow_comp_left M (to_Zero M) a b c f @ _).
    - apply (maponpaths (λ g, g · f)). apply PreAdditive_unel_zero.
    - apply pathsinv0, PreAdditive_unel_zero.
  Defined.
  Lemma zeroRight {a b c : M} (f : a --> b) : f · (0 : b --> c) = 0.
  (* compare with ZeroArrow_comp_right *)
  Proof.
    refine (_ @ ZeroArrow_comp_right M (to_Zero M) a b c f @ _).
    - apply maponpaths, PreAdditive_unel_zero.
    - apply pathsinv0, PreAdditive_unel_zero.
  Defined.
  Definition leftCompHomo  (a b c : M) (f : a --> b) : ismonoidfun (to_premor c f)
    := @to_premor_monoid _ M _ _ _ _.
  Definition rightCompHomo (a b c : M) (f : b --> c) : ismonoidfun (to_postmor a f)
    := @to_postmor_monoid _ M _ _ _ _.
End AdditiveBasics.

Section OppositeAdditiveCategory.     (* move upstream *)
  Definition oppositePrecategoryWithBinOps (M : precategoryWithBinOps) : precategoryWithBinOps
    := mk_precategoryWithBinOps
         (opp_precat M)
         (λ A B f g, to_binop B A f g).
  Goal ∏ (M : precategoryWithBinOps), oppositePrecategoryWithBinOps (oppositePrecategoryWithBinOps M) = M.
  Proof.
    reflexivity.
  Defined.
  Definition oppositeCategoryWithAbgrops (M : categoryWithAbgrops) : categoryWithAbgrops
    := mk_categoryWithAbgrops
         (oppositePrecategoryWithBinOps M)
         (λ A B, to_has_homsets B A)
         (λ A B, to_isabgrop B A).
  Goal ∏ (M : categoryWithAbgrops), oppositeCategoryWithAbgrops (oppositeCategoryWithAbgrops M) = M.
  Proof.
    reflexivity.
  Defined.
  Definition oppositePreAdditive (M : PreAdditive) : PreAdditive
    := mk_PreAdditive
             (oppositeCategoryWithAbgrops M)
             (mk_isPreAdditive (oppositeCategoryWithAbgrops M)
                               (λ x y z f, @to_postmor_monoid M M z y x f)
                               (λ x y z f, @to_premor_monoid M M z y x f)).
  Goal ∏ (M : PreAdditive), oppositePreAdditive (oppositePreAdditive M) = M.
  Proof.
    reflexivity.
  Defined.
  Definition oppositeAdditiveCategory (M:Additive) : Additive.
  Proof.
    use (mk_Additive (oppositePreAdditive M)).
    use mk_isAdditive.
    - use mk_Zero; cbn.
      + exact (to_Zero M).
      + use mk_isZero;cbn.
        * exact (pr22 (to_Zero M)).
        * exact (pr12 (to_Zero M)).
    - intros A B.
      assert (Q := to_BinDirectSums M A B).
      use mk_BinDirectSum.
      + exact (BinDirectSumOb M Q).
      + exact (to_Pr1 Q).
      + exact (to_Pr2 Q).
      + exact (to_In1 Q).
      + exact (to_In2 Q).
      + exact (mk_isBinDirectSum (oppositePreAdditive M) _ _ _ _ _ _ _
           (to_IdIn1 Q) (to_IdIn2 Q) (to_Unel2 Q) (to_Unel1 Q)
           (to_BinOpId Q)).
  Defined.
End OppositeAdditiveCategory.

Local Notation "C '^op'" := (oppositeAdditiveCategory C) (at level 3, format "C ^op") : addcat.
Local Open Scope addcat.
Goal ∏ (M : Additive), M^op^op = M.
Proof.
  reflexivity.
Defined.

Section AdditiveCategories.     (* move upstream *)
  (** Reprove some standard facts in additive categories with the 0 map (the zero element of the
      group) replacing the zero map (defined by composing maps to and from the zero object). *)
  Lemma DirectSumIn1Pr2 {M:Additive} {a b:M} (S:BinDirectSum a b) : to_In1 S · to_Pr2 S = 0.
  Proof.
    exact (to_Unel1 S).
  Defined.
  Lemma DirectSumIn2Pr1 {M:Additive} {a b:M} (S:BinDirectSum a b) : to_In2 S · to_Pr1 S = 0.
  Proof.
    exact (to_Unel2 S).
  Defined.
  Lemma rightDistribute {M:Additive} {a b c : M} (f : a --> b) (g h : b --> c) : f · (g + h) = f · g + f · h.
  Proof.
    apply leftCompHomo.
  Qed.
  Lemma leftDistribute {M:Additive} {a b c : M} (f g : a --> b) (h : b --> c) : (f + g) · h = f · h + g · h.
  Proof.
    apply rightCompHomo.
  Qed.
  Lemma ThroughZeroIsZero {M:Additive} (a b:M) (Z : Zero M) (f : a --> Z) (g : Z --> b) : f · g = 0.
  Proof.
    intermediate_path ((0:a-->Z) · g).
    - apply (maponpaths (postcomp_with g)). apply ArrowsToZero.
    - apply zeroLeft.
  Qed.
  Definition isKernel' {M:Additive} {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : w --> y), h · g = 0 ⇒ ∃! φ : w --> x, φ · f = h.
  Definition isCokernel' {M:Additive} {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : y --> w), f · h = 0 ⇒ ∃! φ : z --> w, g · φ = h.
  Lemma KernelIsMonic {M:Additive} {x y z:M} (f : x --> y) (g : y --> z) : isKernel' f g -> isMonic f.
  Proof.
    intros [t i] w p q e.
    set (T := ∑ r : w --> x, r · f = q · f). assert (ic : isProofIrrelevant T).
    { apply proofirrelevance, isapropifcontr.
      use i. rewrite <- assoc. rewrite t. apply zeroRight. }
    set (t1 := (p,,e) : T). set (t2 := (q,,idpath _) : T).
    assert (Q := ic t1 t2). exact (maponpaths pr1 Q).
  Qed.
  Lemma CokernelIsEpi {M:Additive} {x y z:M} (f : x --> y) (g : y --> z) : isCokernel' f g -> isEpi g.
  Proof.
    exact (KernelIsMonic (M:=M^op) _ _).
  Qed.
  Lemma IsoWithKernel {M:Additive} {x y z z':M} (f : x --> y) (g : y --> z) (h : z --> z') :
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
  Lemma IsoWithCokernel {M:Additive} {x x' y z:M} (f : x --> y) (g : y --> z) (h : x' --> x) :
    isCokernel' f g -> is_z_isomorphism h -> isCokernel' (h·f) g.
  Proof.
    exact (λ c i, IsoWithKernel (M:=M^op) g f h c (opp_is_z_isomorphism h i)).
  Qed.
  Lemma KernelOfZeroMapIsIso {M:Additive} {x y z:M} (g : x --> y) : isKernel' g (0 : y --> z) -> is_z_isomorphism g.
  (* compare with KernelofZeroArrow_is_iso *)
  Proof.
    intros [_ ke]. use (is_z_iso_from_is_iso' M). intros T h. exact (ke _ _ (zeroRight _)).
  Defined.
  Lemma CokernelOfZeroMapIsIso {M:Additive} {x y z:M} (g : y --> z) : isCokernel' (0 : x --> y) g -> is_z_isomorphism g.
  (* compare with CokernelofZeroArrow_is_iso *)
  Proof.
    intros [_ co]. use is_z_iso_from_is_iso. intros T h. exact (co _ _ (zeroLeft _)).
  Defined.
  Lemma KernelUniqueness {M:Additive} {x x' y z : M} {f : x --> y} {f' : x' --> y} {g : y --> z} :
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
  Lemma CokernelUniqueness {M:Additive} {x y z z' : M} {f : x --> y} {g : y --> z} {g' : y --> z'} :
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
  Lemma DirectSumToPullback {M:Additive} {A B:M} (S : BinDirectSum A B) (Z : Zero M) :
    Pullback (0 : A --> Z) (0 : B --> Z).
  Proof.
    use tpair.
    - exists S. exact (to_Pr1 S,, to_Pr2 S).
    - cbn. use tpair.
      + apply ArrowsToZero.
      + cbn. intros T f g e. exact (to_isBinProduct M S T f g).
  Defined.
  Lemma DirectSumToPushout {M:Additive} {A B:M} (S : BinDirectSum A B) (Z : Zero M) :
    Pushout (0 : Z --> A) (0 : Z --> B).
  Proof.
    use tpair.
    - exists S. exact (to_In1 S,, to_In2 S).
    - cbn. use tpair.
      + apply ArrowsFromZero.
      + cbn. intros T f g e. exact (to_isBinCoproduct M S T f g).
  Defined.
  Definition reverseBinDirectSum {M:Additive} {A B:M} : BinDirectSum A B -> BinDirectSum B A.
  Proof.
    intros S.
    use tpair.
    - exact (BinDirectSumOb M S ,, ι₂ ,, ι₁ ,, π₂ ,, π₁).
    - cbn. repeat split.
      + exact (to_IdIn2 (pr2 S)).
      + exact (to_IdIn1 (pr2 S)).
      + exact (to_Unel2 (pr2 S)).
      + exact (to_Unel1 (pr2 S)).
      + refine (_ @ to_BinOpId (pr2 S)). use (commax (to_abgr _ _)).
  Defined.
  Definition directSumMap {M:Additive} {a b c d:M} (f : a --> b) (g : c --> d) : (a ⊕ c) --> (b ⊕ d)
    := BinDirectSumIndAr M f g _ _.
  Lemma directSumMapEqPr1 {M:Additive} {a b c d:M} (f : a --> b) (g : c --> d) :
    directSumMap f g · π₁ = π₁ · f.
  Proof.
    apply BinDirectSumPr1Commutes.
  Qed.
  Lemma directSumMapEqPr2 {M:Additive} {a b c d:M} (f : a --> b) (g : c --> d) :
    directSumMap f g · π₂ = π₂ · g.
  Proof.
    apply BinDirectSumPr2Commutes.
  Qed.
  Lemma directSumMapEqIn1 {M:Additive} {a b c d:M} (f : a --> b) (g : c --> d) :
    ι₁ · directSumMap f g = f · ι₁.
  Proof.
    unfold directSumMap. rewrite BinDirectSumIndArEq. apply BinDirectSumIn1Commutes.
  Qed.
  Lemma directSumMapEqIn2 {M:Additive} {a b c d:M} (f : a --> b) (g : c --> d) :
    ι₂ · directSumMap f g = g · ι₂.
  Proof.
    unfold directSumMap. rewrite BinDirectSumIndArEq. apply BinDirectSumIn2Commutes.
  Qed.
  Definition change_binop {M:Additive} (a b:M) (f g:a --> b) : to_binop _ _ f g = f+g := idpath _.
  Definition SwitchMap {M:Additive} (a b:M) : a ⊕ b --> b ⊕ a := π₁ · ι₂ + π₂ · ι₁.
  Lemma SwitchMapEqn {M:Additive} {a b:M} : SwitchMap a b · SwitchMap b a = 1.
  Proof.
    Local Open Scope cat.           (* ? *)
    unfold SwitchMap.
    rewrite <- (to_BinOpId (a⊕b)), change_binop.
    rewrite leftDistribute, 2 rightDistribute.
    rewrite <- assoc, (assoc ι₂). rewrite DirectSumIn2Pr1.
    rewrite zeroLeft, zeroRight, lunax.
    rewrite <- assoc, (assoc ι₂). rewrite (to_IdIn2 (b ⊕ a)), id_left.
    apply maponpaths.
    rewrite <- assoc, (assoc ι₁). rewrite (to_IdIn1 (b ⊕ a)), id_left.
    rewrite <- assoc, (assoc ι₁). rewrite DirectSumIn1Pr2.
    rewrite zeroLeft, zeroRight, runax.
    reflexivity.
  Defined.
  Definition SwitchIso {M:Additive} (a b:M) : z_iso (a⊕b) (b⊕a).
  Proof.
    exists (SwitchMap _ _). exists (SwitchMap _ _). split; apply SwitchMapEqn.
  Defined.
  Definition SwitchMapMapEqn {M:Additive} {a b c d:M} (f : a --> b) (g : c --> d) :
    SwitchMap _ _ · directSumMap f g = directSumMap g f · SwitchMap _ _.
  Proof.
    unfold SwitchMap.
    rewrite leftDistribute.
    rewrite <- assoc. rewrite directSumMapEqIn2. rewrite assoc.
    rewrite rightDistribute. rewrite assoc. rewrite directSumMapEqPr1.
    apply maponpaths.
    rewrite <- assoc. rewrite directSumMapEqIn1. rewrite assoc.
    rewrite assoc. rewrite directSumMapEqPr2.
    reflexivity.
  Qed.
  Definition directSumMapSwitch {M:Additive} {a b c d:M} (f : a --> b) (g : c --> d) :
    IsoArrow (directSumMap f g) (directSumMap g f).
  Proof.
    exists (SwitchIso _ _). exists (SwitchIso _ _).
    apply SwitchMapMapEqn.
  Defined.
  Local Open Scope addcat.      (* ? *)
  Lemma opposite_directSumMap {M:Additive} {a b c d:M} (f : a --> b) (g : c --> d) :
    directSumMap (M:=M^op) (opp_mor f) (opp_mor g)
    =
    opp_mor (directSumMap (M:=M) f g).
  Proof.
    apply BinDirectSumIndArEq.
  Qed.
  Lemma opposite_directSumMap' {M:Additive} {a b c d:M} (f : a --> b) (g : c --> d) :
    opp_mor (directSumMap (M:=M^op) (opp_mor f) (opp_mor g))
    =
    directSumMap (M:=M) f g.
  Proof.
    apply (maponpaths opp_mor). apply BinDirectSumIndArEq.
  Qed.
  Lemma SumOfKernels {M:Additive} {x y z x' y' z' : M}
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
      induction (iscontrpr1 (pr2 i  w (h · π₁) e1)) as [h1 H1].
      induction (iscontrpr1 (pr2 i' w (h · π₂) e2)) as [h2 H2].
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
  Lemma SumOfCokernels {M:Additive} {x y z x' y' z' : M}
        (f : x --> y) (g : y --> z) (f' : x' --> y') (g' : y' --> z') :
    isCokernel' f g -> isCokernel' f' g' -> isCokernel' (directSumMap f f') (directSumMap g g').
  Proof.
    intros i i'.
    rewrite <- (opposite_directSumMap' f f').
    rewrite <- (opposite_directSumMap' g g').
    apply (SumOfKernels (M:=M^op) g f g' f' i i').
  Qed.
End AdditiveCategories.
Goal ∏ (M:Additive) (x y z : M) (f : x --> y) (g : y --> z), isKernel' (M:=M) f g = isCokernel' (M:=M^op) g f.
  reflexivity.
Defined.
Goal ∏ (M:Additive) (x y z : M) (f : x --> y) (g : y --> z), isCokernel' (M:=M) f g = isKernel' (M:=M^op) g f.
  reflexivity.
Defined.
Section KernelCokernelPairs.
  Definition isKernelCokernelPair {M : Additive} {A B C:M} (i : A --> B) (p: B --> C) : hProp
    := isKernel' i p ∧ isCokernel' i p.
  Definition PairToKernel {M : Additive} {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair i p -> isKernel' i p := pr1.
  Definition PairToCokernel {M : Additive} {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair i p -> isCokernel' i p := pr2.
  Definition opposite_isKernelCokernelPair {M:Additive} {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair (M:=M) i p -> isKernelCokernelPair (M:=M^op) p i.
  Proof.
    intros s.
    split.
    - exact (PairToCokernel s).
    - exact (PairToKernel s).
  Defined.
  Lemma PairUniqueness1 {M : Additive} {A A' B C:M} (i : A --> B) (i' : A' --> B) (p: B --> C) :
    isKernelCokernelPair i p -> isKernelCokernelPair i' p -> iscontr (IsoArrowTo (M:=M) i i').
  Proof.
    intros [k _] [k' _]. exact (KernelUniqueness k k').
  Defined.
  Lemma PairUniqueness2 {M : Additive} {A B C C':M} (i : A --> B) (p: B --> C) (p': B --> C') :
    isKernelCokernelPair i p -> isKernelCokernelPair i p' -> iscontr (IsoArrowFrom (M:=M) p p').
  Proof.
    intros [_ c] [_ c']. exact (CokernelUniqueness c c').
  Defined.
  Lemma kerCokerDirectSum {M : Additive} {A B:M} (S:BinDirectSum A B) : isKernelCokernelPair (to_In1 S) (to_Pr2 S).
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
      + exact (ι₂ · h).
      + refine (assoc _ _ _ @ _ @ id_left h). rewrite <- (to_BinOpId S).
        rewrite to_postmor_linear'.
        rewrite <- (assoc (to_Pr1 S) (to_In1 S) h). rewrite H; clear H.
        rewrite zeroRight. exact (! lunax _ (to_Pr2 S · to_In2 S · h)).
      + intros k. apply to_has_homsets.
      + clear H. intros k e. induction e. rewrite assoc. rewrite (to_IdIn2 S).
        exact (! id_left _).
  Qed.
  Definition TrivialDirectSum {M : Additive} (Z:Zero M) (A:M) : BinDirectSum A Z.
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
  Definition TrivialDirectSum' {M : Additive} (Z:Zero M) (A:M) : BinDirectSum Z A.
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
  Lemma kerCoker10 {M : Additive} (Z:Zero M) (A:M) : isKernelCokernelPair (identity A) (0 : A --> Z).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum Z A)).
  Qed.
  Lemma kerCoker01 {M : Additive} (Z:Zero M) (A:M) : isKernelCokernelPair (0 : Z --> A) (identity A).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum' Z A)).
  Qed.
  Lemma PairPushoutMap {M : Additive} {A B C A':M} {i : A --> B} {p : B --> C}
        (pr : isKernelCokernelPair i p)
        (r : A --> A') (po : Pushout i r) :
    ∑ (q : po --> C), PushoutIn1 po · q = p × PushoutIn2 po · q = 0.
  Proof.
    refine (iscontrpr1 (isPushout_Pushout po C p 0 _)).
    refine (pr1 (PairToCokernel pr) @ ! _). apply zeroRight.
  Qed.
  Lemma PairPullbackMap {M : Additive} {A B C A':M} {i : A <-- B} {p : B <-- C}
        (pr : isKernelCokernelPair p i)
        (r : A <-- A') (pb : Pullback i r) :
    ∑ (q : pb <-- C), PullbackPr1 pb ∘ q = p × PullbackPr2 pb ∘ q = 0.
  Proof.
    (* giving the dual proof here helps later! *)
    exact (PairPushoutMap (M:=M^op) (opposite_isKernelCokernelPair pr) r pb).
  Defined.
  Goal ∏ (M : Additive) (A B C A':M) (i : A <-- B) (p : B <-- C)
        (pr : isKernelCokernelPair p i)
        (r : A <-- A') (pb : Pullback i r),
    PairPullbackMap pr r pb
    =
    PairPushoutMap (M:=M^op) (opposite_isKernelCokernelPair pr) r pb.
  Proof.
    reflexivity.
  Defined.
  Goal ∏ (M : Additive) (A B C A':M) (i : A --> B) (p : B --> C)
        (pr : isKernelCokernelPair i p)
        (r : A --> A') (po : Pushout i r),
    PairPushoutMap pr r po
    =
    PairPullbackMap (M:=M^op) (opposite_isKernelCokernelPair pr) r po.
  Proof.
    reflexivity.
  Defined.
  Lemma PairPushoutCokernel {M : Additive} {A B C A':M} (i : A --> B) (p : B --> C)
        (pr : isKernelCokernelPair i p)
        (r : A --> A') (po : Pushout i r)
        (j := PushoutIn2 po)
        (pp := PairPushoutMap pr r po) :
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
  Lemma PairPullbackKernel {M : Additive} {A B C A':M} (i : A <-- B) (p : B <-- C)
        (pr : isKernelCokernelPair p i)
        (r : A <-- A') (pb : Pullback i r)
        (j := PullbackPr2 pb)
        (pp := PairPullbackMap pr r pb) :
    isKernel' (pr1 pp) j.
  Proof.
    (* Here's where giving the right proof of PairPullbackMap above helped us give this dual proof here. *)
    exact (PairPushoutCokernel (M:=M^op) i p (opposite_isKernelCokernelPair pr) r pb).
  Defined.
  Lemma SumOfKernelCokernelPairs {M : Additive} {x y z x' y' z' : M}
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
      ((∀ P Q, MorphismPairIsomorphism (M:=M) P Q ⇒ isExact P ⇒ isExact Q) ∧
       (∀ P Q, MorphismPairIsomorphism (M:=M) Q P ⇒ isExact P ⇒ isExact Q)) ∧
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
Definition mk_ExactCategory (ME:AddCatWithExactness) (p : ExactCategoryProperties ME) : ExactCategory := ME,,p.

Notation "A ↣ B" := (AdmissibleMonomorphism _ A B) : excat.
Notation "B ↠ C" := (AdmissibleEpimorphism _ B C) : excat.

Arguments isAdmissibleMonomorphism {_ _ _}.
Arguments isAdmissibleEpimorphism {_ _ _}.
Arguments AdmissibleMonomorphism {_}.
Arguments AdmissibleEpimorphism {_}.

Section ExactCategoryAccessFunctions.
  Context {M:ExactCategory}.
  Definition EC_IsomorphicToExact {P Q:MorphismPair M}
    : MorphismPairIsomorphism (M:=M) P Q ⇒ isExact P ⇒ isExact Q
    := pr112 M P Q.
  Definition EC_IsomorphicToExact' {P Q:MorphismPair M}
    : MorphismPairIsomorphism (M:=M) Q P ⇒ isExact P ⇒ isExact Q
    := pr212 M P Q.
  Definition EC_IdentityIsMono (A:M) : isAdmissibleMonomorphism (identity A)
    := pr122 M A.
  Definition IdentityMono (A:M) : AdmissibleMonomorphism A A
    := identity A,, EC_IdentityIsMono A.
  Definition EC_IdentityIsEpi (A:M) : isAdmissibleEpimorphism (identity A)
    := pr122 (pr2 M) A.
  Definition IdentityEpi (A:M) : AdmissibleEpimorphism A A
    := identity A,, EC_IdentityIsEpi A.
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

Section OppositeExactCategory.
  Definition oppositeExactCategory (M:ExactCategory) : ExactCategory.
  Proof.
    set (M' := M^op).
    set (E' := λ p, @isExact M (oppositeMorphismPair (M:=M^op) p)).
    set (ME := (M',,E') : AddCatWithExactness).
    use (mk_ExactCategory ME).
    split.
    { split.
      * intros P Q f. exact (EC_IsomorphicToExact' (oppositeMorphismPairIsomorphism f)).
      * intros P Q f. exact (EC_IsomorphicToExact (oppositeMorphismPairIsomorphism f)). }
    exists EC_IdentityIsEpi.
    exists EC_IdentityIsMono.
    split.
    { intros P i. exact (opposite_isKernelCokernelPair (EC_ExactToKernelCokernel i)). }
    split.
    { intros A B C f g i j. exact (@EC_ComposeEpi M C B A g f j i). }
    split.
    { intros A B C f g i j. exact (@EC_ComposeMono M C B A g f j i). }
    split.
    { exact (@EC_PushoutMono M). }
    { exact (@EC_PullbackEpi M). }
  Defined.
  Goal ∏ (M:ExactCategory), oppositeExactCategory (oppositeExactCategory M) = M.
  Proof.
    reflexivity.
  Defined.
  Goal ∏ (M:ExactCategory) (A B:M) (f : A --> B),
    isAdmissibleMonomorphism f = isAdmissibleEpimorphism (M:=oppositeExactCategory M) (opp_mor f).
  Proof.
    reflexivity.
  Defined.
  Goal ∏ (M:ExactCategory) (A B:M) (f : A --> B), isAdmissibleEpimorphism f = isAdmissibleMonomorphism (M:=oppositeExactCategory M) (opp_mor f).
  Proof.
    reflexivity.
  Defined.
  Goal ∏ (M:ExactCategory) (A B:M),
    AdmissibleMonomorphism A B = @AdmissibleEpimorphism (oppositeExactCategory M) B A.
  Proof.
    reflexivity.
  Defined.
  Goal ∏ (M:ExactCategory) (A B:M),
    AdmissibleEpimorphism A B = @AdmissibleMonomorphism (oppositeExactCategory M) B A.
  Proof.
    reflexivity.
  Defined.
End OppositeExactCategory.

Local Notation "C '^op'" := (oppositeExactCategory C) (at level 3, format "C ^op") : excat.

Section ExactCategoryFacts.
  Lemma ExactToAdmMono {M : ExactCategory} {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isAdmissibleMonomorphism i.
  Proof.
    intros e. exact (hinhpr(C,,p,,e)).
  Qed.
  Lemma ExactToAdmEpi {M : ExactCategory} {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isAdmissibleEpimorphism p.
  Proof.
    intros e. exact (hinhpr(A,,i,,e)).
  Qed.
  Lemma ExactToMono {M : ExactCategory} {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isMonic i.
  Proof.
    intros e. exact (KernelIsMonic i p (EC_ExactToKernel e)).
  Qed.
  Lemma ExactToEpi {M : ExactCategory} {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isEpi p.
  Proof.
    intros e. refine (CokernelIsEpi i p (EC_ExactToCokernel e)).
  Qed.
  Lemma ExactSequenceFromMono {M : ExactCategory} {A B C:M} (i : A --> B) (p : B --> C) :
    isCokernel' i p -> isAdmissibleMonomorphism i -> isExact2 i p.
  Proof.
    intros co mo. apply (squash_to_hProp mo); clear mo; intros [C' [p' e]].
    assert (co' := pr2 (EC_ExactToKernelCokernel e) : isCokernel' i p').
    assert (R := iscontrpr1 (CokernelUniqueness co' co)). induction R as [R r].
    use (EC_IsomorphicToExact _ e).
    exists (identity_z_iso _). exists (identity_z_iso _). exists R.
    split.
    - split.
      + exact (id_left _ @ ! id_right _).
      + exact (id_right _ @ ! id_left _).
    - split.
      + exact (id_left _ @ ! r).
      + exact (r @ !id_left _).
  Qed.
  Lemma ExactSequenceFromEpi {M : ExactCategory} {A B C:M} (i : A --> B) (p : B --> C) :
    isKernel' i p -> isAdmissibleEpimorphism p -> isExact2 i p.
  Proof.
    exact (ExactSequenceFromMono (M:=M^op) p i).
  Defined.
  Lemma ExactSequence10 {M : ExactCategory} (A:M) (Z:Zero M) : isExact2 (identity A) (0 : A --> Z).
  Proof.
    exact (ExactSequenceFromMono _ _ (pr2 (kerCoker10 Z A)) (EC_IdentityIsMono A)).
  Qed.
  Lemma ExactSequence01 {M : ExactCategory} (A:M) (Z:Zero M) : isExact2 (0 : Z --> A) (identity A).
  Proof.
    exact (ExactSequenceFromEpi _ _ (pr1 (kerCoker01 Z A)) (EC_IdentityIsEpi A)).
  Qed.
  Lemma FromZeroIsMono {M : ExactCategory} (Z:Zero M) (A:M) : isAdmissibleMonomorphism (0 : Z --> A).
  Proof.
    apply hinhpr. exists A. exists (identity A). use ExactSequence01.
  Defined.
  Definition MonoFromZero {M : ExactCategory} (Z:Zero M) (A:M) : Z ↣ A
    := (0 : Z --> A),,FromZeroIsMono Z A.
  Lemma ToZeroIsEpi {M : ExactCategory} (A:M) (Z:Zero M) : isAdmissibleEpimorphism (0 : A --> Z).
  Proof.
    apply hinhpr. exists A. exists (identity A). use ExactSequence10.
  Defined.
  Definition EpiToZero {M : ExactCategory} (A:M) (Z:Zero M) : A ↠ Z
    := (0 : A --> Z),,ToZeroIsEpi A Z.
  Local Open Scope excat.
  Goal ∏ (M:ExactCategory) (A:M) (Z:Zero M), EpiToZero A Z = MonoFromZero (M:=M^op) (Zero_opp M Z) A.
  Abort.
  Lemma IsomMono1 {M : ExactCategory} {A B B':M} (f : A --> B) (f' : A --> B') :
    IsoArrowFrom f f' -> isAdmissibleMonomorphism f -> isAdmissibleMonomorphism f'.
  Proof.
    intros [i I] E. apply (squash_to_hProp E); clear E; intros [C [p E]].
    apply hinhpr. exists C. exists (z_iso_inv i · p). use (EC_IsomorphicToExact _ E).
    exists (identity_z_iso A). exists i. exists (identity_z_iso C). split; cbn.
    - split.
      + exact (id_left _ @ ! I).
      + exact (I @ ! id_left _).
    - split.
      + refine (assoc _ _ _ @ _ @ id_left _ @ ! id_right _).
        apply (maponpaths (λ k, k · p)). apply z_iso_inv_after_z_iso.
      + apply pathsinv0.
        refine (assoc _ _ _ @ _ @ id_left _ @ ! id_right _).
        apply (maponpaths (λ k, k · p)). apply z_iso_inv_after_z_iso.
  Qed.
  Lemma IsomEpi1 {M : ExactCategory} {A A' B:M} (f : A --> B) (f' : A' --> B) :
    IsoArrowTo f' f -> isAdmissibleEpimorphism f -> isAdmissibleEpimorphism f'.
  Proof.
    intros i e.
    exact (IsomMono1 (M:=M^op) f f' (opposite_IsoArrowTo i) e).
  Defined.
  Lemma IsomMono {M : ExactCategory} {A A' B B':M} (f : A --> B) (f' : A' --> B') :
    IsoArrow f f' -> isAdmissibleMonomorphism f -> isAdmissibleMonomorphism f'.
  Proof.
    intros [g [h e]] i. apply (squash_to_hProp i); clear i; intros [C [p E]].
    apply hinhpr. exists C. exists (z_iso_inv h · p). use (EC_IsomorphicToExact _ E).
    simple refine (mk_MorphismPairIsomorphism
                     (mk_MorphismPair f p) (mk_MorphismPair f' (z_iso_inv h · p))
                     g h (identity_z_iso C) e _).
    refine (assoc _ _ _ @ maponpaths (postcomp_with p) _ @ id_left p @ ! id_right p).
    apply z_iso_inv_after_z_iso.
  Qed.
  Lemma IsomEpi {M : ExactCategory} {A A' B B':M} (f : A --> B) (f' : A' --> B') :
    IsoArrow f' f -> isAdmissibleEpimorphism f -> isAdmissibleEpimorphism f'.
  Proof.
    intros i.
    exact (IsomMono (M:=M^op) f f' (opposite_IsoArrow _ _ i)).
  Defined.
  Lemma IsoIsMono {M : ExactCategory} {A B:M} (f:z_iso A B) : isAdmissibleMonomorphism (z_iso_mor f).
  Proof.
    use (IsomMono1 (identity A) (z_iso_mor f)).
    - exists f. apply id_left.
    - apply EC_IdentityIsMono.
  Qed.
  Lemma IsoIsEpi {M : ExactCategory} {A B:M} (f:z_iso A B) : isAdmissibleEpimorphism (z_iso_mor f).
  Proof.
    exact (IsoIsMono (M:=M^op) (opp_z_iso f)).
  Defined.
  Lemma DirectSumToExact {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isExact2 (to_In1 S) (to_Pr2 S).
  Proof.
    use ExactSequenceFromEpi.
    { exact (PairToKernel (kerCokerDirectSum S)). }
    set (Z := to_Zero M).
    set (pb := DirectSumToPullback S Z).
    change (isAdmissibleEpimorphism (PullbackPr2 pb)).
    assert (Q := EC_PullbackEpi (0 : A --> Z) (0 : B --> Z) (ToZeroIsEpi A Z)).
    apply (squash_to_hProp Q); clear Q; intros [pb' R'].
    exact (IsomEpi1 (PullbackPr2 pb') (PullbackPr2 pb) (pullbackiso2 pb pb') R').
  Qed.
  Lemma DirectSumToExact' {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isExact2 (to_In2 S) (to_Pr1 S).
  Proof.
    exact (DirectSumToExact (reverseBinDirectSum S)).
  Qed.
  Lemma DirectSumIn1Mono {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isAdmissibleMonomorphism (to_In1 S : A --> S).
  Proof.
    exact (hinhpr (B,,to_Pr2 S,,DirectSumToExact S)).
  Qed.
  Lemma DirectSumIn2Mono {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isAdmissibleMonomorphism (to_In2 S : B --> S).
  Proof.
    exact (hinhpr (A,,to_Pr1 S,,DirectSumToExact' S)).
  Qed.
  Lemma DirectSumPr1Epi {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isAdmissibleEpimorphism (to_Pr1 S : S --> A).
  Proof.
    exact (hinhpr (B,,to_In2 S,,DirectSumToExact' S)).
  Qed.
  Lemma DirectSumPr2Epi {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isAdmissibleEpimorphism (to_Pr2 S : S --> B).
  Proof.
    exact (hinhpr (A,,to_In1 S,,DirectSumToExact S)).
  Qed.
  Lemma ExactPushout {M : ExactCategory} {A B C A':M} (i : A --> B) (p : B --> C)
        (pr : isExact2 i p) (r : A --> A') :
    ∃ (po : Pushout i r),
      isExact2 (PushoutIn2 po) (pr1 (PairPushoutMap (EC_ExactToKernelCokernel pr) r po)).
  Proof.
    assert (I := hinhpr (C ,, p ,, pr) : isAdmissibleMonomorphism i).
    assert (R := EC_PushoutMono i r I).
    apply (squash_to_hProp R); clear R; intros [po J]; apply hinhpr.
    exists po. use ExactSequenceFromMono.
    { exact (PairPushoutCokernel i p (EC_ExactToKernelCokernel pr) r po). }
    exact J.
  Qed.
  Lemma ExactPullback {M : ExactCategory} {A B C A':M} (i : A <-- B) (p : B <-- C)
        (pr : isExact2 p i)
        (r : A <-- A') :
    ∃ (pb : Pullback i r),
      isExact2 (pr1 (PairPullbackMap (EC_ExactToKernelCokernel pr) r pb)) (PullbackPr2 pb).
  Proof.
    assert (I := hinhpr (C ,, p ,, pr) : isAdmissibleEpimorphism i).
    assert (R := EC_PullbackEpi i r I).
    apply (squash_to_hProp R); clear R; intros [pb J]; apply hinhpr.
    exists pb. use ExactSequenceFromEpi.
    { exact (PairPullbackKernel i p (EC_ExactToKernelCokernel pr) r pb). }
    exact J.
  Qed.
  Lemma MonicAdmEpiIsIso {M : ExactCategory} {A B:M} (p : A ↠ B) : isMonic p -> is_z_isomorphism p.
  Proof.
    induction p as [p E]. cbn. intros I. apply (squash_to_prop E).
    { apply isaprop_is_z_isomorphism. apply to_has_homsets. }
    clear E; intros [K [i E]].
    assert (Q := EC_ExactToKernelCokernel E); clear E.
    induction Q as [ke co];
      change (hProptoType (isKernel' i p)) in ke;
      change (hProptoType (isCokernel' i p)) in co.
    assert (Q : i = 0).
    { use (I K i 0). exact (pr1 ke @ ! zeroLeft _). }
    clear I ke. induction (!Q); clear Q. exact (CokernelOfZeroMapIsIso p co).
  Qed.
  Lemma EpiAdmMonoIsIso {M : ExactCategory} {A B:M} (i : A ↣ B) : isEpi i -> is_z_isomorphism i.
  Proof.
    intros e.
    exact (opp_is_z_isomorphism _ (MonicAdmEpiIsIso (M:=M^op) i e)).
  Defined.
  Lemma MonoPlusIdentity {M : ExactCategory} {A B:M} (f:A-->B) (C:M) :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism (directSumMap f (identity C)).
  Proof.
    (* see Bühler's 2.9 *)
    intro i. apply (squash_to_hProp i). intros [D [p j]].
    apply hinhpr. exists D. exists (π₁ · p). apply ExactSequenceFromEpi.
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
    exists (ι₁). split.
    { refine (! runax _ (to_Pr1 (D ⊕ Z) · to_In1 (D ⊕ Z)) @ ! _ @ to_BinOpId (D⊕Z)).
      apply maponpaths. apply ThroughZeroIsZero. }
    { refine (to_IdIn1 (D⊕Z)). }
  Qed.
  Lemma EpiPlusIdentity {M : ExactCategory} {A B:M} (f:A-->B) (C:M) :
    isAdmissibleEpimorphism f -> isAdmissibleEpimorphism (directSumMap f (identity C)).
  Proof.
    intro i. rewrite <- opposite_directSumMap'. exact (MonoPlusIdentity (M:=M^op) f C i).
  Defined.
  Lemma IdentityPlusMono {M : ExactCategory} {B C:M} (A:M) (f:B-->C) :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism (directSumMap (identity A) f).
  Proof.
    intros i. use (IsomMono (directSumMap f (identity A)) (directSumMap (identity A) f)).
    - exists (SwitchIso _ _). exists (SwitchIso _ _). apply SwitchMapMapEqn.
    - apply MonoPlusIdentity. exact i.
  Defined.
  Lemma IdentityPlusEpi {M : ExactCategory} {B C:M} (A:M) (f:B-->C) :
    isAdmissibleEpimorphism f -> isAdmissibleEpimorphism (directSumMap (identity A) f).
  Proof.
    intros i. use (IsomEpi (directSumMap f (identity A)) (directSumMap (identity A) f)).
    - exists (SwitchIso _ _). exists (SwitchIso _ _). apply SwitchMapMapEqn.
    - apply EpiPlusIdentity. exact i.
  Defined.
  Lemma SumOfExactSequences {M:ExactCategory} {A B C A' B' C':M}
        {f : A --> B} {g : B --> C} {f' : A' --> B'} {g' : B' --> C'} :
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
      - refine (! assoc _ _ _ @ _). intermediate_path (k · (π₁ · f)).
        + apply maponpaths. apply directSumMapEqPr1.
        + refine (assoc _ _ _ @ _). apply (maponpaths (postcomp_with _)).
          exact (directSumMapEqPr1 _ _ @ id_right _).
      - refine (! assoc _ _ _ @ _). intermediate_path (k · (π₂ · (identity B'))).
        + apply maponpaths. apply directSumMapEqPr2.
        + refine (assoc _ _ _ @ id_right _ @ _). apply directSumMapEqPr2. }
    induction kj. use (EC_ComposeMono k j).
    2:{ apply MonoPlusIdentity. exact (ExactToAdmMono i). }
    apply IdentityPlusMono. exact (ExactToAdmMono i').
  Qed.
  Lemma SumOfAdmissibleEpis {M:ExactCategory} {A B A' B':M} (f : A --> B) (f' : A' --> B') :
    isAdmissibleEpimorphism f -> isAdmissibleEpimorphism f' -> isAdmissibleEpimorphism (directSumMap f f').
  Proof.
    intros e e'.
    apply (squash_to_hProp e); clear e; intros [C [g e]].
    apply (squash_to_hProp e'); clear e'; intros [C' [g' e']].
    exact (ExactToAdmEpi (SumOfExactSequences e e')).
  Qed.
  Lemma SumOfAdmissibleMonos {M:ExactCategory} {A B A' B':M} (f : A --> B) (f' : A' --> B') :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism f' -> isAdmissibleMonomorphism (directSumMap f f').
  Proof.
    intros e e'.
    apply (squash_to_hProp e); clear e; intros [C [g e]].
    apply (squash_to_hProp e'); clear e'; intros [C' [g' e']].
    exact (ExactToAdmMono (SumOfExactSequences e e')).
  Qed.
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
