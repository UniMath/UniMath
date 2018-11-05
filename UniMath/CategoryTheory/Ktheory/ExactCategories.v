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
Require Export UniMath.Algebra.BinaryOperations.
Require Export UniMath.Algebra.Monoids_and_Groups.
Import AddGroupNotation.

Local Arguments to_binop {_ _ _}.
Local Arguments grinv {_}.
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
Local Arguments ToBinDirectSum {_ _ _} _ {_}.

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

Local Open Scope cat.

Section Sanity2.
  Context (M : PreAdditive) (x y:M) (f : hom M x y) (g : Hom M x y) (h : Hom_add M x y).
  Goal Hom_add M x y. exact f. Defined.
  Goal Hom_add M x y. exact g. Defined.
  Goal Hom M x y. exact f. Defined.
  Goal Hom M x y. exact h. Defined.
  Goal hom M x y. exact g. Defined.
  Goal hom M x y. exact h. Defined.

  Local Open Scope addmonoid.
  Local Open Scope abgrcat.
  Definition A : (h + h) · 1 = h ∧ htrue.
    (* A slight problem with printing, due to notation capture; the goal
       appears here as "((h + h) · 1 = h)%set ∧ htrue" *)
  Abort.

End Sanity2.

Local Notation "b <-- a" := (to_abgr a b) (only parsing) : abgrcat.
Local Notation "b <-- a" := (precategory_morphisms a b) (only parsing) : cat.
Local Notation "'π₁'" := (to_Pr1 _) : abgrcat.
Local Notation "'π₂'" := (to_Pr2 _) : abgrcat.
Local Notation "'ι₁'" := (to_In1 _) : abgrcat.
Local Notation "'ι₂'" := (to_In2 _) : abgrcat.

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
  Lemma cancel_z_iso {M:precategory} {x y z : M} (f f' : x --> y) (g : z_iso y z) :
    f · g = f' · g -> f = f'.
  Proof.
    intros e.
    refine (_ @ maponpaths (λ k, k · z_iso_inv g) e @ _).
    - rewrite assoc'. rewrite z_iso_inv_after_z_iso. rewrite id_right. reflexivity.
    - rewrite assoc'. rewrite z_iso_inv_after_z_iso. rewrite id_right. reflexivity.
  Qed.
  Lemma cancel_z_iso' {M:precategory} {w x y : M} (g : z_iso w x) (f f' : x --> y) :
    g · f = g · f' -> f = f'.
  Proof.
    intros e.
    refine (_ @ maponpaths (λ k, z_iso_inv g · k) e @ _).
    - rewrite assoc. rewrite z_iso_inv_after_z_iso. rewrite id_left. reflexivity.
    - rewrite assoc. rewrite z_iso_inv_after_z_iso. rewrite id_left. reflexivity.
  Qed.
  Lemma wrap_inverse {M:precategory} {x y : M} (g : hom M x x) (f : z_iso x y) :
    g = identity x -> z_iso_inv f · g · f = identity y.
  Proof.
    intros e. rewrite e. rewrite id_right. apply z_iso_after_z_iso_inv.
  Defined.
  Lemma wrap_inverse' {M:precategory} {x y : M} (g : hom M x x) (f : z_iso y x) :
    g = identity x -> f · g · z_iso_inv f = identity y.
  Proof.
    intros e. rewrite e. rewrite id_right. apply z_iso_inv_after_z_iso.
  Defined.
End Precategories.

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

Section Pushouts.              (* move upstream *)
  Definition hasPushout {M : precategory} {A B C:M} (f:A-->B) (g:A-->C) := ∥ Pushout f g ∥.
End Pushouts.

Section Pullbacks.              (* move upstream *)
  Definition hasPullback {M : precategory} {A B C:M} (f:A-->C) (g:B-->C) := ∥ Pullback f g ∥.
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

Definition switchPullback {M:category} {A B C:M} {f : A --> C} {g : B --> C} (pb : Pullback f g) : Pullback g f.
Proof.
  induction pb as [[P [r s]] [e ip]]; simpl in e.
  use (mk_Pullback _ _ _ _ _ (!e) (is_symmetric_isPullback (homset_property M) _ ip)).
Defined.

Section OppositeIsoArrows.
  Definition opposite_IsoArrowTo {M:precategory} {A A' B:M} {g : A --> B} {g' : A' --> B} :
    IsoArrowTo g g' -> IsoArrowFrom (M:=M^op) g' g.
  Proof.
    intros i.
    Fail exact i.
    use tpair.
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

Local Open Scope abgrcat.

Section PreAdditive.
  Definition oppositePrecategoryWithBinOps (M : precategoryWithBinOps) : precategoryWithBinOps
    := mk_precategoryWithBinOps
         (opp_precat M)
         (λ A B f g, to_binop f g).
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
  Definition oppositeBinDirectSum {M:PreAdditive} {x y:M} :
    BinDirectSum (A:=M) x y -> BinDirectSum (A:=oppositePreAdditive M) x y.
  Proof.
    intros Q.
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
  Goal ∏ (M:PreAdditive) (x y:M) (xy : BinDirectSum x y),
    oppositeBinDirectSum (M:=oppositePreAdditive M) (oppositeBinDirectSum xy) = xy.
  Proof.
    reflexivity.
  Defined.
  Lemma zeroLeft {M:PreAdditive} {a b c : M} (f : b --> c) : ((0 : a --> b) · f = 0)%abgrcat.
  Proof.
    apply to_postmor_unel'.
  Defined.
  Lemma zeroRight {M:PreAdditive} {a b c : M} (f : a --> b) : f · (0 : b --> c) = 0.
  Proof.
    apply to_premor_unel'.
  Defined.
  Definition leftCompIsHomo {M:PreAdditive} {a b : M} (f : a --> b) (c:M) : ismonoidfun (to_premor c f)
    := @to_premor_monoid _ M _ _ _ _.
  Definition rightCompIsHomo {M:PreAdditive} {b c : M} (a:M) (f : b --> c) : ismonoidfun (to_postmor a f)
    := @to_postmor_monoid _ M _ _ _ _.
  Definition leftCompHomo {M:PreAdditive} {a b : M} (f : a --> b) (c:M) : monoidfun (b-->c) (a-->c)
    := to_premor c f,, to_premor_monoid M _ _ _ f.
  Definition rightCompHomo {M:PreAdditive} {b c : M} (a:M) (f : b --> c) : monoidfun (a-->b) (a-->c)
    := to_postmor a f,, to_postmor_monoid M _ _ _ f.
  Lemma DirectSumIn1Pr2 {M:PreAdditive} {a b:M} (S:BinDirectSum a b) : to_In1 S · to_Pr2 S = 0.
  Proof.
    exact (to_Unel1 S).
  Defined.
  Lemma DirectSumIn2Pr1 {M:PreAdditive} {a b:M} (S:BinDirectSum a b) : to_In2 S · to_Pr1 S = 0.
  Proof.
    exact (to_Unel2 S).
  Defined.
  Lemma rightDistribute {M:PreAdditive} {a b c : M} (f : a --> b) (g h : b --> c) : f · (g + h) = f · g + f · h.
  Proof.
    apply leftCompIsHomo.
  Qed.
  Lemma leftDistribute {M:PreAdditive} {a b c : M} (f g : a --> b) (h : b --> c) : (f + g) · h = f · h + g · h.
  Proof.
    apply rightCompIsHomo.
  Qed.
  Lemma rightMinus {M:PreAdditive} {a b c : M} (f : a --> b) (g : b --> c) : f · (- g) = - (f·g).
  Proof.
    exact (monoidfuninvtoinv (leftCompHomo f c) g).
  Qed.
  Lemma leftMinus {M:PreAdditive} {a b c : M} (f : a --> b) (g : b --> c) : (- f) · g = - (f·g).
  Proof.
    exact (monoidfuninvtoinv (rightCompHomo a g) f).
  Qed.
End PreAdditive.

Section DirectSums.
  Open Scope addmonoid.
  Definition reverseBinDirectSum {M:PreAdditive} {A B:M} : BinDirectSum A B -> BinDirectSum B A.
  Proof.
    intros AB.
    exists (BinDirectSumOb M AB ,, ι₂ ,, ι₁ ,, π₂ ,, π₁).
    exists (to_IdIn2 (pr2 AB)).
    exists (to_IdIn1 (pr2 AB)).
    exists (to_Unel2 (pr2 AB)).
    exists (to_Unel1 (pr2 AB)).
    cbn. rewrite rewrite_op.
    (* goal is now π₂ · ι₂ + π₁ · ι₁ = 1 *)
    exact (commax (to_abgr _ _) _ _ @ to_BinOpId (pr2 AB)).
  Defined.
  Goal ∏ (M:PreAdditive) (A B:M) (AB : BinDirectSum A B), reverseBinDirectSum (oppositeBinDirectSum AB) = oppositeBinDirectSum (reverseBinDirectSum AB).
    reflexivity.
  Defined.
  Goal ∏ (M:PreAdditive) (A B:M) (AB : BinDirectSum A B), reverseBinDirectSum (reverseBinDirectSum AB) = AB.
    Fail reflexivity.
  Abort.
  Definition isTrivialDirectSum {M : PreAdditive} (Z:Zero M) (A:M) :
    isBinDirectSum M A Z A 1 0 1 0.
  Proof.
    repeat split; cbn.
    - apply id_right.
    - apply ArrowsToZero.
    - apply ArrowsToZero.
    - apply ArrowsFromZero.
    - rewrite id_right. rewrite zeroRight. rewrite rewrite_op. rewrite runax. reflexivity.
  Qed.
  Definition TrivialDirectSum {M : PreAdditive} (Z:Zero M) (A:M) : BinDirectSum A Z.
  Proof.
    exact (mk_BinDirectSum _ _ _ _ _ _ _ _ (isTrivialDirectSum _ _)).
  Defined.
  Definition isTrivialDirectSum' {M : PreAdditive} (Z:Zero M) (A:M) :
    isBinDirectSum M Z A A 0 1 0 1.
  Proof.
    repeat split; cbn.
    - apply ArrowsToZero.
    - apply id_right.
    - apply ArrowsFromZero.
    - apply ArrowsToZero.
    - rewrite id_right. rewrite zeroRight. rewrite rewrite_op. rewrite lunax. reflexivity.
  Qed.
  Definition TrivialDirectSum' {M : PreAdditive} (Z:Zero M) (A:M) : BinDirectSum Z A.
  Proof.
    exact (mk_BinDirectSum _ _ _ _ _ _ _ _ (isTrivialDirectSum' _ _)).
  Defined.
End DirectSums.

Section AdditiveBasics.         (* move upstream *)
  (* first fix the definition of additive category to follow traditional mathematical practice *)
  Definition isAdditive' (PA : PreAdditive) : UU := hasZero PA × hasBinDirectSums PA.
  Definition mk_isAdditive' (PA : PreAdditive) (H1 : hasZero PA) (H2 : hasBinDirectSums PA) : isAdditive' PA := H1,,H2.
  Definition Additive' : UU := ∑ PA : PreAdditive, isAdditive' PA.
  Coercion Additive'_to_PreAdditive (A : Additive') : PreAdditive := pr1 A.
  Definition mk_Additive' (PA : PreAdditive) (H : isAdditive' PA) : Additive' := PA,,H.
  Definition to_Zero' (A : Additive') : hasZero A := pr12 A.
  Definition to_BinDirectSums' {A : Additive'} : hasBinDirectSums A := pr22 A.

  Context {M : Additive'}.
End AdditiveBasics.

Local Notation "A ⊕ B" := (to_BinDirectSums' A B) : addcat.

Section OppositeAdditiveCategory.     (* move upstream *)
  Open Scope addcat.
  Definition oppositeAdditiveCategory (M:Additive') : Additive'.
  Proof.
    exists (oppositePreAdditive M). split.
    - use (hinhfun _ (to_Zero' M)). exact (λ Z, pr1 Z,, pr22 Z,, pr12 Z).
    - intros A B. exact (hinhfun oppositeBinDirectSum (A ⊕ B)).
  Defined.
  Goal ∏ (M : Additive'), oppositeAdditiveCategory (oppositeAdditiveCategory M) = M.
  Proof.
    reflexivity.
  Defined.
End OppositeAdditiveCategory.

Local Notation "C '^op'" := (oppositeAdditiveCategory C) (at level 3, format "C ^op") : addcat.
Local Open Scope addcat.

Section AdditiveCategories.     (* move upstream *)
  (** Reprove some standard facts in additive categories with the 0 map (the zero element of the
      group) replacing the zero map (defined by composing maps to and from the zero object). *)
  Local Open Scope addmonoid.
  Local Open Scope abgr.
  Local Open Scope abgrcat.
  Lemma ThroughZeroIsZero {M:PreAdditive} (a b:M) (Z : Zero M) (f : a --> Z) (g : Z --> b) : f · g = 0.
  Proof.
    intermediate_path ((0:a-->Z) · g).
    - apply (maponpaths (postcomp_with g)). apply ArrowsToZero.
    - apply to_postmor_unel'.
  Qed.
  Definition elem21 {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) (f:A-->B) : AB-->AB := 1 + π₁·f·ι₂.
  Section Foo.
    Definition elem21_isiso {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) (f:A-->B) : is_z_isomorphism (elem21 AB f).
    Proof.
      exists (1 - π₁·f·ι₂).
      (* Why are these needed to make the goals look nice?  Compare to the dual proof below. *)
      Local Open Scope addmonoid.
      Local Open Scope abgr.
      unfold elem21. split.
      - rewrite leftDistribute, 2 rightDistribute. rewrite id_left. refine (_ @ runax (_-->_) _).
        rewrite assocax. apply maponpaths. rewrite id_right, id_left. rewrite rightMinus.
        rewrite <- assocax. rewrite grlinvax. rewrite lunax. rewrite assoc'. rewrite <- (assoc π₁ f ι₂).
        rewrite (assoc ι₂). rewrite DirectSumIn2Pr1. rewrite zeroLeft. rewrite zeroRight. use grinvunel.
      - rewrite leftDistribute, 2 rightDistribute. rewrite id_left. refine (_ @ runax (_-->_) _).
        rewrite assocax. apply maponpaths. rewrite id_right, id_left. rewrite leftMinus.
        rewrite <- assocax. rewrite grrinvax. rewrite lunax. rewrite assoc'. rewrite <- (assoc π₁ f ι₂).
        rewrite (assoc ι₂). rewrite DirectSumIn2Pr1. rewrite zeroLeft. rewrite zeroRight. use grinvunel.
    Defined.
  End Foo.
  Definition elem12 {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) (f:B-->A) : AB-->AB := 1 + π₂·f·ι₁.
  Definition elem12_isiso {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) (f:B-->A) : is_z_isomorphism (elem12 AB f).
  Proof.
    exists (1 - π₂·f·ι₁). unfold elem12. split.
    - rewrite leftDistribute, 2 rightDistribute. rewrite id_left. refine (_ @ runax (_-->_) _).
      rewrite assocax. apply maponpaths. rewrite id_right, id_left. rewrite rightMinus.
      rewrite <- assocax. rewrite grlinvax. rewrite lunax. rewrite assoc'. rewrite <- (assoc _ f _).
      rewrite 2 (assoc ι₁). rewrite DirectSumIn1Pr2. rewrite zeroLeft. rewrite zeroLeft.
      rewrite 2 zeroRight.
      use grinvunel.
    - rewrite leftDistribute, 2 rightDistribute. rewrite id_left. refine (_ @ runax (_-->_) _).
      rewrite assocax. apply maponpaths. rewrite id_right, id_left. rewrite leftMinus.
      rewrite <- assocax. rewrite grrinvax. rewrite lunax. rewrite assoc'. rewrite <- (assoc _ f _).
      rewrite (assoc ι₁). rewrite (assoc ι₁). rewrite DirectSumIn1Pr2. rewrite 2 zeroLeft.
      rewrite 2 zeroRight. use grinvunel.
  Defined.
  Definition isKernel' {M:PreAdditive} {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : w --> y), h · g = 0 ⇒ ∃! φ : w --> x, φ · f = h.
  Definition hasKernel {M:PreAdditive} {y z : M} (g : y --> z) : hProp :=
    ∃ x (f:x-->y), isKernel' f g.
  Definition isCokernel' {M:PreAdditive} {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : y --> w), f · h = 0 ⇒ ∃! φ : z --> w, g · φ = h.
  Definition hasCokernel {M:PreAdditive} {x y : M} (f : x --> y) : hProp :=
    ∃ z (g:y-->z), isCokernel' f g.
  Goal ∏ (M:PreAdditive) (x y z : M) (f : x --> y) (g : y --> z), isKernel' (M:=M) f g = isCokernel' (M:=oppositePreAdditive M) g f.
    reflexivity.
  Defined.
  Goal ∏ (M:PreAdditive) (x y z : M) (f : x --> y) (g : y --> z), isCokernel' (M:=M) f g = isKernel' (M:=oppositePreAdditive M) g f.
    reflexivity.
  Defined.
  Lemma KernelIsMonic {M:PreAdditive} {x y z:M} (f : x --> y) (g : y --> z) : isKernel' f g -> isMonic f.
  Proof.
    intros [t i] w p q e.
    set (T := ∑ r : w --> x, r · f = q · f). assert (ic : isProofIrrelevant T).
    { apply proofirrelevance, isapropifcontr.
      use i. rewrite assoc'. rewrite t. apply zeroRight. }
    set (t1 := (p,,e) : T). set (t2 := (q,,idpath _) : T).
    assert (Q := ic t1 t2). exact (maponpaths pr1 Q).
  Qed.
  Lemma CokernelIsEpi {M:PreAdditive} {x y z:M} (f : x --> y) (g : y --> z) : isCokernel' f g -> isEpi g.
  Proof.
    exact (KernelIsMonic (M:=oppositePreAdditive M) g f).
  Qed.
  Definition makeMonicKernel {M:PreAdditive} {x y z : M} (f : x --> y) (g : y --> z) :
    isMonic f -> f · g = 0 ->
    (∏ (w : M) (h : w --> y), h · g = 0 -> ∑ φ : w --> x, φ · f = h) ->
    isKernel' f g.
  Proof.
    intros im eq ex. exists eq. intros w h e.
    apply iscontraprop1.
    - apply invproofirrelevance; intros [r R] [s S].
      apply subtypeEquality_prop; simpl. apply im. exact (R@!S).
    - apply ex. exact e.
  Qed.
  Definition makeEpiCokernel {M:PreAdditive} {x y z : M} (f : x --> y) (g : y --> z) :
    isEpi g -> f · g = 0 ->
    (∏ (w : M) (h : y --> w), f · h = 0 -> ∑ φ : z --> w, g · φ = h) ->
    isCokernel' f g.
  Proof.
    exact (makeMonicKernel (M:=oppositePreAdditive M) g f).
  Qed.
  Lemma IsoWithKernel {M:PreAdditive} {x y z z':M} (f : x --> y) (g : y --> z) (h : z --> z') :
    isKernel' f g -> is_z_isomorphism h -> isKernel' f (g·h).
  Proof.
    intros i j.
    apply makeMonicKernel.
    - exact (KernelIsMonic _ _ i).
    - exact (assoc _ _ _ @ maponpaths (postcomp_with _) (pr1 i) @ zeroLeft h).
    - intros w k e. apply (pr2 i).
      refine (post_comp_with_iso_is_inj _ _ _ h (is_iso_from_is_z_iso h j) _ _ _ _).
      refine (! assoc _ _ _ @ e @ ! zeroLeft _).
  Qed.
  Lemma IsoWithCokernel {M:PreAdditive} {x x' y z:M} (f : x --> y) (g : y --> z) (h : x' --> x) :
    isCokernel' f g -> is_z_isomorphism h -> isCokernel' (h·f) g.
  Proof.
    exact (λ c i, IsoWithKernel (M:=oppositePreAdditive M) g f h c (opp_is_z_isomorphism h i)).
  Qed.
  Lemma KernelOfZeroMapIsIso {M:PreAdditive} {x y z:M} (g : x --> y) : isKernel' g (0 : y --> z) -> is_z_isomorphism g.
  (* compare with KernelofZeroArrow_is_iso *)
  Proof.
    intros [_ ke]. use (is_z_iso_from_is_iso' M). intros T h. exact (ke _ _ (zeroRight _)).
  Defined.
  Lemma CokernelOfZeroMapIsIso {M:PreAdditive} {x y z:M} (g : y --> z) : isCokernel' (0 : x --> y) g -> is_z_isomorphism g.
  (* compare with CokernelofZeroArrow_is_iso *)
  Proof.
    intros [_ co]. use is_z_iso_from_is_iso. intros T h. exact (co _ _ (zeroLeft _)).
  Defined.
  Lemma KernelUniqueness {M:PreAdditive} {x x' y z : M} {f : x --> y} {f' : x' --> y} {g : y --> z} :
    isKernel' f g -> isKernel' f' g -> iscontr (IsoArrowTo f f').
  Proof.
    intros i j. apply iscontraprop1.
    - exact (IsoArrowTo_isaprop M f f' (KernelIsMonic f' g j)).
    - induction (iscontrpr1 (pr2 j _ f (pr1 i))) as [p P].
      induction (iscontrpr1 (pr2 i _ f' (pr1 j))) as [q Q].
      use tpair.
      + exists p. exists q. split.
        * apply (KernelIsMonic _ _ i). rewrite assoc'. rewrite Q. rewrite P. rewrite id_left. reflexivity.
        * apply (KernelIsMonic _ _ j). rewrite assoc'. rewrite P. rewrite Q. rewrite id_left. reflexivity.
      + cbn. exact P.
  Defined.
  Lemma CokernelUniqueness {M:PreAdditive} {x y z z' : M} {f : x --> y} {g : y --> z} {g' : y --> z'} :
    isCokernel' f g -> isCokernel' f g' -> iscontr (IsoArrowFrom g g').
  Proof.
    intros i j.
    (*
      The dual proof would go like this:
      assert (Q := KernelUniqueness (M:=oppositePreAdditive M) i j).
      generalize Q.
      Now we would need this: weq (IsoArrowTo g g') (IsoArrowFrom g g')
     *)
    apply iscontraprop1.
    - exact (IsoArrowFrom_isaprop M g g' (CokernelIsEpi f g i)).
    - induction (iscontrpr1 (pr2 j _ g (pr1 i))) as [p P].
      induction (iscontrpr1 (pr2 i _ g' (pr1 j))) as [q Q].
      use tpair.
      + exists q. exists p. split.
        * apply (CokernelIsEpi _ _ i). rewrite assoc. rewrite Q. rewrite P. rewrite id_right. reflexivity.
        * apply (CokernelIsEpi _ _ j). rewrite assoc. rewrite P. rewrite Q. rewrite id_right. reflexivity.
      + cbn. exact Q.
  Defined.
  Lemma DirectSumToPullback {M:PreAdditive} {A B:M} (S : BinDirectSum A B) (Z : Zero M) :
    Pullback (0 : A --> Z) (0 : B --> Z).
  Proof.
    use tpair.
    - exists S. exact (to_Pr1 S,, to_Pr2 S).
    - cbn. use tpair.
      + apply ArrowsToZero.
      + cbn. intros T f g e. exact (to_isBinProduct M S T f g).
  Defined.
  Lemma DirectSumToPushout {M:PreAdditive} {A B:M} (S : BinDirectSum A B) (Z : Zero M) :
    Pushout (0 : Z --> A) (0 : Z --> B).
  Proof.
    use tpair.
    - exists S. exact (to_In1 S,, to_In2 S).
    - cbn. use tpair.
      + apply ArrowsFromZero.
      + cbn. intros T f g e. exact (to_isBinCoproduct M S T f g).
  Defined.
  Definition directSumMap {M:PreAdditive} {a b c d:M} (ac : BinDirectSum a c) (bd : BinDirectSum b d) (f : a --> b) (g : c --> d) : ac --> bd
    := BinDirectSumIndAr M f g _ _.
  Lemma directSumMapEqPr1 {M:PreAdditive} {a b c d:M} {ac : BinDirectSum a c} {bd : BinDirectSum b d} {f : a --> b} {g : c --> d} :
    directSumMap ac bd f g · π₁ = π₁ · f.
  Proof.
    apply BinDirectSumPr1Commutes.
  Qed.
  Lemma directSumMapEqPr2 {M:PreAdditive} {a b c d:M} {ac : BinDirectSum a c} {bd : BinDirectSum b d} {f : a --> b} {g : c --> d} :
    directSumMap ac bd f g · π₂ = π₂ · g.
  Proof.
    apply BinDirectSumPr2Commutes.
  Qed.
  Lemma directSumMapEqIn1 {M:PreAdditive} {a b c d:M} {ac : BinDirectSum a c} {bd : BinDirectSum b d} {f : a --> b} {g : c --> d} :
    ι₁ · directSumMap ac bd f g = f · ι₁.
  Proof.
    unfold directSumMap. rewrite BinDirectSumIndArEq. apply BinDirectSumIn1Commutes.
  Qed.
  Lemma directSumMapEqIn2 {M:PreAdditive} {a b c d:M} {ac : BinDirectSum a c} {bd : BinDirectSum b d} {f : a --> b} {g : c --> d} :
    ι₂ · directSumMap ac bd f g = g · ι₂.
  Proof.
    unfold directSumMap. rewrite BinDirectSumIndArEq. apply BinDirectSumIn2Commutes.
  Qed.
  (* One of these should replace to_BinOpId upstream.  Also fix ToBinDirectSumFormula and FromBinDirectSumFormula. *)
  Definition to_BinOpId' {M:PreAdditive} {a b co : M} {i1 : a --> co} {i2 : b --> co} {p1 : co --> a} {p2 : co --> b}
             (B : isBinDirectSum _ a b co i1 i2 p1 p2) :
    p1 · i1 + p2 · i2 = identity co := to_BinOpId B.
  Definition to_BinOpId'' {M:PreAdditive} {a b : M} (ab : BinDirectSum a b) := to_BinOpId ab.
  Definition SwitchMap {M:PreAdditive} (a b:M) (ab : BinDirectSum a b) (ba : BinDirectSum b a) : ab --> ba := π₁ · ι₂ + π₂ · ι₁.
  Lemma SwitchMapEqn {M:PreAdditive} {a b:M} (ab : BinDirectSum a b) (ba : BinDirectSum b a) : SwitchMap a b ab ba · SwitchMap b a ba ab = 1.
  Proof.
    unfold SwitchMap.
    rewrite <- to_BinOpId''.
    rewrite leftDistribute, 2 rightDistribute.
    rewrite assoc', (assoc ι₂). rewrite DirectSumIn2Pr1.
    rewrite zeroLeft, zeroRight, lunax.
    rewrite assoc', (assoc ι₂). rewrite (to_IdIn2 ba), id_left.
    apply maponpaths.
    rewrite assoc', (assoc ι₁). rewrite (to_IdIn1 ba), id_left.
    rewrite assoc', (assoc ι₁). rewrite DirectSumIn1Pr2.
    rewrite zeroLeft, zeroRight, runax.
    reflexivity.
  Defined.
  Definition SwitchIso {M:PreAdditive} (a b:M) (ab : BinDirectSum a b) (ba : BinDirectSum b a) : z_iso ab ba.
  Proof.
    exists (SwitchMap _ _ _ _). exists (SwitchMap _ _ _ _). split; apply SwitchMapEqn.
  Defined.
  Lemma SwitchMapEqnTo {M:PreAdditive} {a b c:M} (bc : BinDirectSum b c) (cb : BinDirectSum c b) (f:a-->b) (g:a-->c) :
    ToBinDirectSum bc f g · SwitchMap b c bc cb = ToBinDirectSum cb g f.
  Proof.
    unfold SwitchMap. apply ToBinDirectSumsEq.
    - rewrite rightDistribute. rewrite 2 assoc.
      rewrite 2 BinDirectSumPr1Commutes, BinDirectSumPr2Commutes.
      rewrite leftDistribute. rewrite 2 assoc'.
      rewrite (to_Unel2 cb).
      unfold to_unel.           (* fix to_Unel2! *)
      rewrite zeroRight. rewrite lunax.
      rewrite (to_IdIn1 cb). rewrite id_right. reflexivity.
    - rewrite assoc'. rewrite leftDistribute. rewrite (assoc' π₂ _ π₂).
      rewrite (to_Unel1 cb). unfold to_unel. rewrite zeroRight. rewrite runax.
      rewrite 2 assoc. rewrite BinDirectSumPr1Commutes, BinDirectSumPr2Commutes.
      rewrite assoc'. rewrite (to_IdIn2 cb). rewrite id_right. reflexivity.
  Qed.
  Lemma SwitchMapMapEqn {M:PreAdditive} {a b c d:M}
        (ac : BinDirectSum a c) (ca : BinDirectSum c a)
        (bd : BinDirectSum b d) (db : BinDirectSum d b)
        (f : a --> b) (g : c --> d) :
    SwitchMap c a ca ac · directSumMap ac bd f g = directSumMap ca db g f · SwitchMap d b db bd.
  Proof.
    unfold SwitchMap.
    rewrite leftDistribute.
    rewrite assoc'. rewrite directSumMapEqIn2. rewrite assoc.
    rewrite rightDistribute. rewrite assoc. rewrite directSumMapEqPr1.
    apply maponpaths.
    rewrite assoc'. rewrite directSumMapEqIn1. rewrite assoc.
    rewrite assoc. rewrite directSumMapEqPr2.
    reflexivity.
  Qed.
  Definition directSumMapSwitch {M:PreAdditive} {a b c d:M}
        (ac : BinDirectSum a c) (ca : BinDirectSum c a)
        (bd : BinDirectSum b d) (db : BinDirectSum d b)
        (f : a --> b) (g : c --> d) :
    IsoArrow (directSumMap ac bd f g) (directSumMap ca db g f).
  Proof.
    exists (SwitchIso _ _ _ _). exists (SwitchIso _ _ _ _). apply SwitchMapMapEqn.
  Defined.
  Lemma opposite_directSumMap {M:PreAdditive} {a b c d:M}
        (ac : BinDirectSum a c) (bd : BinDirectSum b d)
        (f : a --> b) (g : c --> d) :
    directSumMap (M:=oppositePreAdditive M) (oppositeBinDirectSum bd) (oppositeBinDirectSum ac) (opp_mor f) (opp_mor g)
    =
    opp_mor (directSumMap ac bd f g).
  Proof.
    apply BinDirectSumIndArEq.
  Qed.
  Lemma opposite_directSumMap' {M:PreAdditive} {a b c d:M}
        (ac : BinDirectSum a c) (bd : BinDirectSum b d)
        (f : a --> b) (g : c --> d) :
    opp_mor (directSumMap (M:=oppositePreAdditive M) (oppositeBinDirectSum bd) (oppositeBinDirectSum ac) (opp_mor f) (opp_mor g))
    =
    directSumMap ac bd f g.
  Proof.
    apply (maponpaths opp_mor). apply opposite_directSumMap.
  Qed.
  Lemma SumOfKernels {M:PreAdditive} {x y z X Y Z : M}
        (xX : BinDirectSum x X) (yY : BinDirectSum y Y) (zZ : BinDirectSum z Z)
        (f : x --> y) (g : y --> z) (f' : X --> Y) (g' : Y --> Z) :
    isKernel' f g -> isKernel' f' g' -> isKernel' (directSumMap xX yY f f') (directSumMap yY zZ g g').
  Proof.
    intros i i'. split.
    { refine (BinDirectSumIndArComp _ _ _ _ _ _ _ _ @ ! _).
      apply ToBinDirectSumUnique.
      - exact (zeroLeft _ @ ! zeroRight _ @ maponpaths _ (! pr1 i)).
      - exact (zeroLeft _ @ ! zeroRight _ @ maponpaths _ (! pr1 i')). }
    intros w h e. apply iscontraprop1.
    2:{
      assert (e1 := ! assoc _ _ _
                      @ ! maponpaths (precomp_with _) directSumMapEqPr1
                      @ assoc _ _ _
                      @ maponpaths (postcomp_with _) e
                      @ zeroLeft _).
      assert (e2 := ! assoc _ _ _
                      @ ! maponpaths (precomp_with _) directSumMapEqPr2
                      @ assoc _ _ _
                      @ maponpaths (postcomp_with _) e
                      @ zeroLeft _).
      induction (iscontrpr1 (pr2 i  w (h · π₁) e1)) as [h1 H1].
      induction (iscontrpr1 (pr2 i' w (h · π₂) e2)) as [h2 H2].
      exists (ToBinDirectSum _ h1 h2).
      apply ToBinDirectSumsEq.
      + refine (! assoc _ _ _ @ _ @ H1).
        refine (maponpaths (precomp_with _) directSumMapEqPr1 @ _).
        unfold precomp_with.
        refine (assoc _ _ _ @ _).
        apply (maponpaths (postcomp_with _)).
        apply BinDirectSumPr1Commutes.
      + refine (! assoc _ _ _ @ _ @ H2).
        refine (maponpaths (precomp_with _) directSumMapEqPr2 @ _).
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
               @ ! maponpaths (precomp_with k) directSumMapEqPr1
               @ assoc _ _ _
               @ maponpaths (postcomp_with _) (K @ !K')
               @ ! assoc _ _ _
               @ maponpaths (precomp_with k') directSumMapEqPr1
               @ assoc _ _ _).
    - refine (KernelIsMonic _ _ i' _ _ _ _).
      exact (! assoc _ _ _
               @ ! maponpaths (precomp_with k) directSumMapEqPr2
               @ assoc _ _ _
               @ maponpaths (postcomp_with _) (K @ !K')
               @ ! assoc _ _ _
               @ maponpaths (precomp_with k') directSumMapEqPr2
               @ assoc _ _ _).
  Qed.
  Lemma SumOfCokernels {M:PreAdditive} {x y z X Y Z : M}
        (xX : BinDirectSum x X) (yY : BinDirectSum y Y) (zZ : BinDirectSum z Z)
        (f : x --> y) (g : y --> z) (f' : X --> Y) (g' : Y --> Z) :
    isCokernel' f g -> isCokernel' f' g' -> isCokernel' (directSumMap xX yY f f') (directSumMap yY zZ g g').
  Proof.
    intros i i'.
    rewrite <- (opposite_directSumMap' xX yY f f').
    rewrite <- (opposite_directSumMap' yY zZ g g').
    exact (SumOfKernels (M:=oppositePreAdditive M) (oppositeBinDirectSum zZ) (oppositeBinDirectSum yY) (oppositeBinDirectSum xX) g f g' f' i i').
  Qed.
End AdditiveCategories.
Local Notation "f ++ g" := (directSumMap _ _ f g) : addcat.
Section KernelCokernelPairs.
  Definition isKernelCokernelPair {M :PreAdditive} {A B C:M} (i : A --> B) (p: B --> C) : hProp
    := isKernel' i p ∧ isCokernel' i p.
  Definition PairToKernel {M :PreAdditive} {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair i p -> isKernel' i p := pr1.
  Definition PairToCokernel {M :PreAdditive} {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair i p -> isCokernel' i p := pr2.
  Definition opposite_isKernelCokernelPair {M:PreAdditive} {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair i p -> isKernelCokernelPair (M:=oppositePreAdditive M) p i.
  Proof.
    intros s.
    split.
    - exact (PairToCokernel s).
    - exact (PairToKernel s).
  Defined.
  Lemma PairUniqueness1 {M :PreAdditive} {A A' B C:M} (i : A --> B) (i' : A' --> B) (p: B --> C) :
    isKernelCokernelPair i p -> isKernelCokernelPair i' p -> iscontr (IsoArrowTo i i').
  Proof.
    intros [k _] [k' _]. exact (KernelUniqueness k k').
  Defined.
  Lemma PairUniqueness2 {M :PreAdditive} {A B C C':M} (i : A --> B) (p: B --> C) (p': B --> C') :
    isKernelCokernelPair i p -> isKernelCokernelPair i p' -> iscontr (IsoArrowFrom p p').
  Proof.
    intros [_ c] [_ c']. exact (CokernelUniqueness c c').
  Defined.
  Lemma kerCokerDirectSum {M :PreAdditive} {A B:M} (S:BinDirectSum A B) : isKernelCokernelPair (to_In1 S) (to_Pr2 S).
  Proof.
    assert (E := BinDirectSum_isBinDirectSum M S).
    split.
    - exists (to_Unel1 S). intros T h H. use unique_exists; cbn beta.
      + exact (h · to_Pr1 S).
      + refine (! assoc _ _ _ @ _ @ id_right _). rewrite <- (to_BinOpId' S).
        rewrite rightDistribute. rewrite (assoc h (to_Pr2 S) (to_In2 S)).
        rewrite H; clear H. rewrite zeroLeft. apply pathsinv0. apply (runax (T-->S)).
      + intros k. apply to_has_homsets.
      + clear H. intros k e. induction e. rewrite assoc'.
        rewrite (to_IdIn1 S). apply pathsinv0, id_right.
    - exists (to_Unel1 S). intros T h H. use unique_exists; cbn beta.
      + exact (ι₂ · h).
      + refine (assoc _ _ _ @ _ @ id_left h). rewrite <- (to_BinOpId' S).
        rewrite leftDistribute.
        rewrite <- (assoc (to_Pr1 S) (to_In1 S) h). rewrite H; clear H.
        rewrite zeroRight. apply pathsinv0. apply (lunax (S-->T)).
      + intros k. apply to_has_homsets.
      + clear H. intros k e. induction e. rewrite assoc. rewrite (to_IdIn2 S).
        exact (! id_left _).
  Qed.
  Lemma kerCoker10 {M :PreAdditive} (Z:Zero M) (A:M) : isKernelCokernelPair (identity A) (0 : A --> Z).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum Z A)).
  Qed.
  Lemma kerCoker01 {M :PreAdditive} (Z:Zero M) (A:M) : isKernelCokernelPair (0 : Z --> A) (identity A).
  Proof.
    exact (kerCokerDirectSum (TrivialDirectSum' Z A)).
  Qed.
  Lemma PairPushoutMap {M :PreAdditive} {A B C A':M} {i : A --> B} {p : B --> C}
        (pr : isKernelCokernelPair i p)
        (r : A --> A') (po : Pushout i r) :
    ∑ (q : po --> C), PushoutIn1 po · q = p × PushoutIn2 po · q = 0.
  Proof.
    refine (iscontrpr1 (isPushout_Pushout po C p 0 _)).
    refine (pr1 (PairToCokernel pr) @ ! _). apply zeroRight.
  Qed.
  Lemma PairPullbackMap {M :PreAdditive} {A B C A':M} {i : A <-- B} {p : B <-- C}
        (pr : isKernelCokernelPair p i)
        (r : A <-- A') (pb : Pullback i r) :
    ∑ (q : pb <-- C), PullbackPr1 pb ∘ q = p × PullbackPr2 pb ∘ q = 0.
  Proof.
    (* giving the dual proof here helps later! *)
    exact (PairPushoutMap (M:=oppositePreAdditive M) (opposite_isKernelCokernelPair pr) r pb).
  Defined.
  Goal ∏ (M :PreAdditive) (A B C A':M) (i : A <-- B) (p : B <-- C)
        (pr : isKernelCokernelPair p i)
        (r : A <-- A') (pb : Pullback i r),
    PairPullbackMap pr r pb
    =
    PairPushoutMap (M:=oppositePreAdditive M) (opposite_isKernelCokernelPair pr) r pb.
  Proof.
    reflexivity.
  Defined.
  Goal ∏ (M :PreAdditive) (A B C A':M) (i : A --> B) (p : B --> C)
        (pr : isKernelCokernelPair i p)
        (r : A --> A') (po : Pushout i r),
    PairPushoutMap pr r po
    =
    PairPullbackMap (M:=oppositePreAdditive M) (opposite_isKernelCokernelPair pr) r po.
  Proof.
    reflexivity.
  Defined.
  Lemma PairPushoutCokernel {M :PreAdditive} {A B C A':M} (i : A --> B) (p : B --> C)
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
  Lemma PairPullbackKernel {M : Additive'} {A B C A':M} (i : A <-- B) (p : B <-- C)
        (pr : isKernelCokernelPair p i)
        (r : A <-- A') (pb : Pullback i r)
        (j := PullbackPr2 pb)
        (pp := PairPullbackMap pr r pb) :
    isKernel' (pr1 pp) j.
  Proof.
    (* Here's where giving the right proof of PairPullbackMap above helped us give this dual proof here. *)
    exact (PairPushoutCokernel (M:=M^op) i p (opposite_isKernelCokernelPair pr) r pb).
  Defined.
  Lemma SumOfKernelCokernelPairs {M : Additive'} {x y z X Y Z : M}
        (xX : BinDirectSum x X) (yY : BinDirectSum y Y) (zZ : BinDirectSum z Z)
        {f : x --> y} {g : y --> z} {f' : X --> Y} {g' : Y --> Z}
    : isKernelCokernelPair f g -> isKernelCokernelPair f' g' -> isKernelCokernelPair (directSumMap xX yY f f') (directSumMap yY zZ g g').
  Proof.
    intros i i'.
    exists (SumOfKernels   _ _ _ f g f' g' (pr1 i) (pr1 i')).
    exact  (SumOfCokernels _ _ _ f g f' g' (pr2 i) (pr2 i')).
  Qed.
End KernelCokernelPairs.

Section theDefinition.
  Definition ExactCategoryData := ∑ M:Additive', MorphismPair M -> hProp. (* properties added below *)
  Coercion ECD_to_AC (ME : ExactCategoryData) : Additive' := pr1 ME.
  Context (M : ExactCategoryData).
  Definition isExact (E : MorphismPair M) : hProp := pr2 M E.
  Definition isExact2 {A B C:M} (f:A-->B) (g:B-->C) := isExact (mk_MorphismPair f g).
  Definition isAdmissibleMonomorphism {A B:M} (i : A --> B) : hProp :=
    ∃ C (p : B --> C), isExact2 i p.
  Definition AdmissibleMonomorphism (A B:M) : Type :=
    ∑ (i : A --> B), isAdmissibleMonomorphism i.
  Coercion AdmMonoToMap {A B:M} : AdmissibleMonomorphism A B -> A --> B := pr1.
  Coercion AdmMonoToMap' {A B:M} : AdmissibleMonomorphism A B -> (A --> B)%cat := pr1.
  Definition isAdmissibleEpimorphism {B C:M} (p : B --> C) : hProp :=
    ∃ A (i : A --> B), isExact2 i p.
  Definition AdmissibleEpimorphism (B C:M) : Type :=
    ∑ (p : B --> C), isAdmissibleEpimorphism p.
  Coercion AdmEpiToMap {B C:M} : AdmissibleEpimorphism B C -> B --> C := pr1.
  Coercion AdmEpiToMap' {B C:M} : AdmissibleEpimorphism B C -> (B --> C)%cat := pr1.
  (** The following definition is definition 2.1 from the paper of Bühler. *)
  Local Definition ExactCategoryProperties : hProp :=
      ((∀ P Q, MorphismPairIsomorphism P Q ⇒ isExact P ⇒ isExact Q) ∧
       (∀ P Q, MorphismPairIsomorphism Q P ⇒ isExact P ⇒ isExact Q)) ∧
      ((∀ A, isAdmissibleMonomorphism (identity A)) ∧
       (∀ A, isAdmissibleEpimorphism (identity A))) ∧
      (∀ P, isExact P ⇒ isKernelCokernelPair (Mor1 P) (Mor2 P)) ∧
      ((∀ A B C (f : A --> B) (g : B --> C),
          isAdmissibleMonomorphism f ⇒ isAdmissibleMonomorphism g ⇒
          isAdmissibleMonomorphism (f · g)) ∧
       (∀ A B C (f : A --> B) (g : B --> C),
          isAdmissibleEpimorphism f ⇒ isAdmissibleEpimorphism g ⇒
          isAdmissibleEpimorphism (f · g))) ∧
      ((∀ A B C (f : A --> B) (g : C --> B),
          isAdmissibleEpimorphism f ⇒
          ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)) ∧
       (∀ A B C (f : B --> A) (g : B --> C),
          isAdmissibleMonomorphism f ⇒
          ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO))).
  (** The following definition is from Higher Algebraic K-theory I, by Quillen. *)
  Local Definition ExactCategoryProperties_Quillen : hProp :=
      (∀ P Q, MorphismPairIsomorphism P Q ⇒ isExact P ⇒ isExact Q) ∧
      (∀ A B (AB:BinDirectSum A B), isExact2 (to_In1 AB) (to_Pr2 AB)) ∧
      (∀ P, isExact P ⇒ isKernel' (Mor1 P) (Mor2 P) ∧ isCokernel' (Mor1 P) (Mor2 P)) ∧
      ((∀ A B C (f : A --> B) (g : B --> C),
          isAdmissibleMonomorphism f ⇒ isAdmissibleMonomorphism g ⇒
          isAdmissibleMonomorphism (f · g)) ∧
       (∀ A B C (f : A --> B) (g : B --> C),
          isAdmissibleEpimorphism f ⇒ isAdmissibleEpimorphism g ⇒
          isAdmissibleEpimorphism (f · g))) ∧
      ((∀ A B C (f : A --> B) (g : C --> B),
          isAdmissibleEpimorphism f ⇒
          ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)) ∧
       (∀ A B C (f : B --> A) (g : B --> C),
          isAdmissibleMonomorphism f ⇒
          ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO))) ∧
       ((∀ A B C (i:A-->B) (j:B-->C),
          hasCokernel i ⇒ isAdmissibleMonomorphism (i·j) ⇒ isAdmissibleMonomorphism i) ∧
        (∀ A B C (i:A-->B) (j:B-->C),
          hasKernel j ⇒ isAdmissibleEpimorphism (i·j) ⇒ isAdmissibleEpimorphism j)).
  (** We prove below that the two definitions are equivalent. *)
End theDefinition.

Arguments isExact {_}.
Arguments isExact2 {_ _ _ _}.

Definition ExactCategory := ∑ (ME:ExactCategoryData), ExactCategoryProperties ME.
Coercion ExCatToExactCategoryData (E:ExactCategory) : ExactCategoryData := pr1 E.
Definition mk_ExactCategory (ME:ExactCategoryData) (p : ExactCategoryProperties ME) : ExactCategory := ME,,p.

Delimit Scope excat with excat.
Local Open Scope excat.
Notation "A ↣ B" := (AdmissibleMonomorphism _ A B) : excat.
Notation "B ↠ C" := (AdmissibleEpimorphism _ B C) : excat.

Arguments isAdmissibleMonomorphism {_ _ _}.
Arguments isAdmissibleEpimorphism {_ _ _}.
Arguments AdmissibleMonomorphism {_}.
Arguments AdmissibleEpimorphism {_}.

Section ExactCategoryAccessFunctions.
  Context {M:ExactCategory}.
  Definition EC_IsomorphicToExact {P Q:MorphismPair M}
    : MorphismPairIsomorphism P Q ⇒ isExact P ⇒ isExact Q
    := pr112 M P Q.
  Definition EC_IsomorphicToExact' {P Q:MorphismPair M}
    : MorphismPairIsomorphism Q P ⇒ isExact P ⇒ isExact Q
    := pr212 M P Q.
  Definition EC_IdentityIsMono (A:M) : isAdmissibleMonomorphism (identity A)
    := pr1 (pr122 M) A.
  Definition IdentityMono (A:M) : AdmissibleMonomorphism A A
    := identity A,, EC_IdentityIsMono A.
  Definition EC_IdentityIsEpi (A:M) : isAdmissibleEpimorphism (identity A)
    := pr2 (pr122 M) A.
  Definition IdentityEpi (A:M) : AdmissibleEpimorphism A A
    := identity A,, EC_IdentityIsEpi A.
  Definition EC_ExactToKernelCokernel {P : MorphismPair M} :
    isExact P ⇒ isKernelCokernelPair (Mor1 P) (Mor2 P)
    := pr12 (pr22 M) P.
  Definition EC_ExactToKernel {P : MorphismPair M} :
    isExact P ⇒ isKernel' (Mor1 P) (Mor2 P)
    := λ i, (pr1 (EC_ExactToKernelCokernel i)).
  Definition EC_ExactToCokernel {P : MorphismPair M} :
    isExact P ⇒ isCokernel' (Mor1 P) (Mor2 P)
    := λ i, (pr2 (EC_ExactToKernelCokernel i)).
  Definition EC_ComposeMono {A B C:M} (f : A --> B) (g : B --> C) :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism g ->
    isAdmissibleMonomorphism (f · g)
    := pr112 (pr222 M) A B C f g.
  Definition EC_ComposeEpi {A B C:M} (f : A --> B) (g : B --> C) :
    isAdmissibleEpimorphism f ⇒ isAdmissibleEpimorphism g ⇒
    isAdmissibleEpimorphism (f · g)
    := pr212 (pr222 M) A B C f g.
  Definition EC_PullbackEpi {A B C:M} (f : A --> B) (g : C --> B) :
    isAdmissibleEpimorphism f ⇒
    ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)
    := pr122 (pr222 M) A B C f g.
  Definition EC_PushoutMono {A B C:M} (f : B --> A) (g : B --> C) :
    isAdmissibleMonomorphism f ⇒
    ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO)
    := pr222 (pr222 M) A B C f g.
End ExactCategoryAccessFunctions.

Section OppositeExactCategory.
  Definition oppositeExactCategoryData (M:ExactCategoryData) : ExactCategoryData.
  Proof.
    exists (M^op).
    exact (λ p, @isExact M (oppositeMorphismPair (M:=M^op) p)).
  Defined.
  Goal ∏ (M:ExactCategoryData), oppositeExactCategoryData (oppositeExactCategoryData M) = M.
    reflexivity.
  Qed.
  Definition oppositeExactCategory (M:ExactCategory) : ExactCategory.
  Proof.
    use (mk_ExactCategory (oppositeExactCategoryData M)).
    split.
    { split;intros P Q f.
      - exact (EC_IsomorphicToExact' (oppositeMorphismPairIsomorphism f)).
      - exact (EC_IsomorphicToExact (oppositeMorphismPairIsomorphism f)). }
    split.
    { split.
      - exact EC_IdentityIsEpi.
      - exact EC_IdentityIsMono. }
    split.
    { intros P i. exact (opposite_isKernelCokernelPair (EC_ExactToKernelCokernel i)). }
    split.
    { split.
      { intros A B C f g i j. exact (@EC_ComposeEpi M C B A g f j i). }
      { intros A B C f g i j. exact (@EC_ComposeMono M C B A g f j i). } }
    { split.
      { exact (@EC_PushoutMono M). }
      { exact (@EC_PullbackEpi M). } }
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

Notation "C '^op'" := (oppositeExactCategory C) (at level 3, format "C ^op") : excat.

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
  Lemma PullbackEpiIsEpi {M : ExactCategory} {A B C:M} (f : A --> B) (g : C --> B)
        (pb : Pullback f g) :
    isAdmissibleEpimorphism f -> isAdmissibleEpimorphism (PullbackPr2 pb).
  (* dual needed *)
  Proof.
    intros fepi.
    assert (qb := EC_PullbackEpi f g fepi).
    apply (squash_to_hProp qb); clear qb; intros [qb epi2].
    assert (I := pullbackiso2 pb qb).
    apply (IsomEpi1 _ _ I). exact epi2.
  Qed.
  Lemma IsPullbackEpiIsEpi {M : ExactCategory} {P A B C:M} {f : A --> B} {g : C --> B}
        {h : P --> A} {k : P --> C} {e : h·f=k·g} :
    isPullback f g h k e -> isAdmissibleEpimorphism f -> isAdmissibleEpimorphism k.
  (* dual needed *)
  Proof.
    intros pb. exact (PullbackEpiIsEpi f g (mk_Pullback _ _ _ _ _ _ pb)).
  Qed.
  Lemma IsIsoIsMono {M : ExactCategory} {A B:M} (f:A-->B) :
    is_z_isomorphism f -> isAdmissibleMonomorphism f.
  Proof.
    intros i.
    use (IsomMono1 (identity A)).
    - use tpair.
      + exact (f,,i).
      + cbn. apply id_left.
    - apply EC_IdentityIsMono.
  Qed.
  Lemma IsoIsMono {M : ExactCategory} {A B:M} (f:z_iso A B) : isAdmissibleMonomorphism (z_iso_mor f).
  Proof.
    use IsIsoIsMono. apply f.
  Qed.
  Definition IsoToAdmMono {M : ExactCategory} {A B:M} (f:z_iso A B) : AdmissibleMonomorphism A B
    := z_iso_mor f,,IsoIsMono f.
  Lemma IsoIsEpi {M : ExactCategory} {A B:M} (f:z_iso A B) : isAdmissibleEpimorphism (z_iso_mor f).
  Proof.
    exact (IsoIsMono (M:=M^op) (opp_z_iso f)).
  Defined.
  Definition IsoToAdmEpi {M : ExactCategory} {A B:M} (f:z_iso A B) : AdmissibleEpimorphism A B
    := z_iso_mor f,,IsoIsEpi f.
  Lemma DirectSumToExact {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isExact2 (to_In1 S) (to_Pr2 S).
  Proof.
    use ExactSequenceFromEpi.
    { exact (PairToKernel (kerCokerDirectSum S)). }
    apply (squash_to_hProp (to_Zero' M)); intros Z.
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
  Lemma In1IsAdmMono {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isAdmissibleMonomorphism (ι₁ : A --> S).
  Proof.
    exact (hinhpr (B,,to_Pr2 S,,DirectSumToExact S)).
  Qed.
  Lemma In2IsAdmMono {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isAdmissibleMonomorphism (ι₂ : B --> S).
  Proof.
    exact (hinhpr (A,,to_Pr1 S,,DirectSumToExact' S)).
  Qed.
  Lemma Pr1IsAdmEpi {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isAdmissibleEpimorphism (π₁ : S --> A).
  Proof.
    exact (hinhpr (B,,to_In2 S,,DirectSumToExact' S)).
  Qed.
  Lemma Pr2IsAdmEpi {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : isAdmissibleEpimorphism (π₂ : S --> B).
  Proof.
    exact (hinhpr (A,,to_In1 S,,DirectSumToExact S)).
  Qed.
  Definition In1AdmMono {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : AdmissibleMonomorphism A S := ι₁ ,, In1IsAdmMono S.
  Definition In2AdmMono {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : AdmissibleMonomorphism B S := ι₂ ,, In2IsAdmMono S.
  Definition Pr1AdmEpi {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : AdmissibleEpimorphism S A := π₁ ,, Pr1IsAdmEpi S.
  Definition Pr2AdmEpi {M : ExactCategory} {A B:M} (S:BinDirectSum A B) : AdmissibleEpimorphism S B := π₂ ,, Pr2IsAdmEpi S.
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
  Lemma MonoPlusIdentity {M : ExactCategory} {A B:M}
        (f:A-->B) (C:M) (AC : BinDirectSum A C) (BC : BinDirectSum B C) :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism (directSumMap AC BC f (identity C)).
  Proof.
    (* see Bühler's 2.9 *)
    intro i. apply (squash_to_hProp i). intros [D [p j]].
    apply hinhpr. exists D. exists (π₁ · p). apply ExactSequenceFromEpi.
    2:{ apply EC_ComposeEpi.
        - apply Pr1IsAdmEpi.
        - exact (hinhpr(A,,f,,j)). }
    apply (squash_to_hProp (to_Zero' M)); intros Z.
    apply (squash_to_hProp (D ⊕ Z)); intros DZ.
    assert (m := pr1 (SumOfKernelCokernelPairs AC BC DZ
                   (EC_ExactToKernelCokernel j : isKernelCokernelPair f p)
                   (kerCoker10 Z C : isKernelCokernelPair (identity C) 0))).
    assert (R : directSumMap BC DZ p 0 · to_Pr1 DZ = to_Pr1 BC · p).
    { apply directSumMapEqPr1. }
    induction R. apply IsoWithKernel.
    { exact m. }
    exists (ι₁). split.
    { refine (! runax (_ --> _) _ @ ! _ @ to_BinOpId'' _). apply maponpaths. apply ThroughZeroIsZero. }
    { refine (to_IdIn1 DZ). }
  Qed.
  Lemma EpiPlusIdentity {M : ExactCategory} {A B:M} (f:A-->B) (C:M) (AC : BinDirectSum A C) (BC : BinDirectSum B C) :
    isAdmissibleEpimorphism f -> isAdmissibleEpimorphism (directSumMap AC BC f (identity C)).
  Proof.
    intro i. rewrite <- opposite_directSumMap'.
    exact (MonoPlusIdentity (M:=M^op) f C (oppositeBinDirectSum BC) (oppositeBinDirectSum AC) i).
  Defined.
  Lemma IdentityPlusMono {M : ExactCategory} {B C:M} (A:M) (f:B-->C)
         (AB : BinDirectSum A B) (AC : BinDirectSum A C) :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism (directSumMap AB AC (identity A) f).
  Proof.
    intros i. use (IsomMono (directSumMap (reverseBinDirectSum AB) (reverseBinDirectSum AC) f (identity A)) (directSumMap AB AC (identity A) f)).
    - exists (SwitchIso _ _ _ _). exists (SwitchIso _ _ _ _). apply SwitchMapMapEqn.
    - apply MonoPlusIdentity. exact i.
  Defined.
  Lemma IdentityPlusEpi {M : ExactCategory} {B C:M} (A:M) (f:B-->C)
        (AB : BinDirectSum A B) (AC : BinDirectSum A C) :
    isAdmissibleEpimorphism f -> isAdmissibleEpimorphism (directSumMap AB AC (identity A) f).
  Proof.
    intros i. use (IsomEpi (directSumMap (reverseBinDirectSum AB) (reverseBinDirectSum AC) f (identity A)) (directSumMap AB AC (identity A) f)).
    - exists (SwitchIso _ _ _ _). exists (SwitchIso _ _ _ _). apply SwitchMapMapEqn.
    - apply EpiPlusIdentity. exact i.
  Defined.
  Lemma SumOfExactSequences {M:ExactCategory} {A B C A' B' C':M}
        (AA' : BinDirectSum A A') (BB' : BinDirectSum B B') (CC' : BinDirectSum C C')
        {f : A --> B} {g : B --> C} {f' : A' --> B'} {g' : B' --> C'} :
    isExact2 f g -> isExact2 f' g' -> isExact2 (directSumMap AA' BB' f f') (directSumMap BB' CC' g g').
  Proof.
    (* see Bühler's 2.9 *)
    intros i i'. apply ExactSequenceFromMono.
    { use SumOfCokernels.
      - exact (EC_ExactToCokernel i).
      - exact (EC_ExactToCokernel i'). }
    apply (squash_to_hProp (A ⊕ B')); intros AB'.
    set (j := directSumMap AB' BB' f (identity B')).
    set (k := directSumMap AA' AB' (identity A) f').
    assert (kj : k · j = directSumMap AA' BB' f f').
    { apply ToBinDirectSumUnique.
      - refine (! assoc _ _ _ @ _). intermediate_path (k · (π₁ · f)).
        + apply maponpaths. apply directSumMapEqPr1.
        + refine (assoc _ _ _ @ _). apply (maponpaths (postcomp_with _)).
          exact (directSumMapEqPr1 @ id_right _).
      - refine (! assoc _ _ _ @ _). intermediate_path (k · (π₂ · (identity B'))).
        + apply maponpaths. apply directSumMapEqPr2.
        + refine (assoc _ _ _ @ id_right _ @ _). apply directSumMapEqPr2. }
    induction kj. use (EC_ComposeMono k j).
    - apply IdentityPlusMono. exact (ExactToAdmMono i').
    - apply MonoPlusIdentity. exact (ExactToAdmMono i).
  Qed.
  Lemma AdmMonoEnlargement {M:ExactCategory} {A B C:M}
        (BC : BinDirectSum B C) (i:A-->B) (f:A-->C) :
    isAdmissibleMonomorphism i -> isAdmissibleMonomorphism (ToBinDirectSum BC i f).
  Proof.
    (* see Bühler's 2.12 *)
    intros I.
    (* write the map as a composite of three maps *)
    apply (squash_to_hProp (A ⊕ C)); intros AC.
    assert (e : ToBinDirectSum BC i f  = ι₁ · (1 + π₁·f·ι₂) · (directSumMap AC _ i 1)).
    { apply ToBinDirectSumsEq.
      - rewrite BinDirectSumPr1Commutes. rewrite assoc'. unfold directSumMap.
        unfold BinDirectSumIndAr. rewrite BinDirectSumPr1Commutes.
        rewrite assoc. rewrite rightDistribute. rewrite 2 leftDistribute.
        rewrite id_right. rewrite (to_IdIn1 AC). rewrite id_left.
        refine (! runax (A-->B) _ @ _). apply maponpaths. rewrite assoc.
        rewrite (assoc' _ _ π₁). rewrite (to_Unel2 AC). unfold to_unel.
        rewrite zeroRight, zeroLeft. reflexivity.
      - rewrite BinDirectSumPr2Commutes. rewrite assoc'. unfold directSumMap.
        unfold BinDirectSumIndAr. rewrite BinDirectSumPr2Commutes.
        rewrite assoc. rewrite rightDistribute. rewrite 2 leftDistribute.
        rewrite 2 id_right. rewrite (to_Unel1 AC). unfold to_unel.
        rewrite lunax. rewrite id_right. rewrite 2 assoc.
        rewrite (to_IdIn1 AC). rewrite id_left.
        rewrite assoc'. rewrite (to_IdIn2 AC). rewrite id_right. reflexivity. }
    induction (!e); clear e.
    apply EC_ComposeMono.
    - apply EC_ComposeMono.
      + apply In1IsAdmMono.
      + apply IsIsoIsMono. apply elem21_isiso.
    - now apply MonoPlusIdentity.
  Qed.
  Lemma SumOfAdmissibleEpis {M:ExactCategory} {A B A' B':M}
        (AA' : BinDirectSum A A') (BB' : BinDirectSum B B')
        (f : A --> B) (f' : A' --> B') :
    isAdmissibleEpimorphism f -> isAdmissibleEpimorphism f' -> isAdmissibleEpimorphism (directSumMap AA' BB' f f').
  Proof.
    intros e e'.
    apply (squash_to_hProp e); clear e; intros [C [g e]].
    apply (squash_to_hProp e'); clear e'; intros [C' [g' e']].
    apply (squash_to_hProp (C ⊕ C')); intros CC'.
    exact (ExactToAdmEpi (SumOfExactSequences CC' _ _ e e')).
  Qed.
  Lemma SumOfAdmissibleMonos {M:ExactCategory} {A B A' B':M}
        (AA' : BinDirectSum A A') (BB' : BinDirectSum B B')
        (f : A --> B) (f' : A' --> B') :
    isAdmissibleMonomorphism f -> isAdmissibleMonomorphism f' -> isAdmissibleMonomorphism (directSumMap AA' BB' f f').
  Proof.
    intros e e'.
    apply (squash_to_hProp e); clear e; intros [C [g e]].
    apply (squash_to_hProp e'); clear e'; intros [C' [g' e']].
    apply (squash_to_hProp (C ⊕ C')); intros CC'.
    exact (ExactToAdmMono (SumOfExactSequences _ _ CC' e e')).
  Qed.
  Lemma MapPlusIdentityToCommSq {M:ExactCategory} {A B:M}
        (f:A-->B) (C:M)
        (AC : BinDirectSum A C) (BC : BinDirectSum B C) :
    f · ι₁ = ι₁ · (directSumMap AC BC f (identity C)).
  Proof.
    apply ToBinDirectSumsEq.
    - rewrite assoc'. rewrite (to_IdIn1 BC). rewrite id_right. unfold directSumMap.
      unfold BinDirectSumIndAr. rewrite assoc'. rewrite BinDirectSumPr1Commutes.
      rewrite assoc. rewrite (to_IdIn1 AC). rewrite id_left. reflexivity.
    - rewrite assoc'. rewrite (to_Unel1 BC). unfold to_unel. rewrite zeroRight.
      unfold directSumMap, BinDirectSumIndAr. rewrite assoc'.
      rewrite BinDirectSumPr2Commutes. rewrite id_right. apply pathsinv0.
      use (to_Unel1 AC).
  Qed.
  Lemma KernelPlusIdentity {M:ExactCategory} {A B C:M}
        (f:A-->B) (g:B-->C) (D:M)
        (BD : BinDirectSum B D) (CD : BinDirectSum C D) :
    isKernel' (f · ι₁) (directSumMap BD CD g (identity D)) -> isKernel' f g.
  Proof.
    intros K. apply makeMonicKernel.
    - exact (isMonic_postcomp _ _ _ (KernelIsMonic _ _ K)).
    - use (to_In1_isMonic _ CD). rewrite zeroLeft. rewrite assoc'.
      assert (Q := pr1 K); simpl in Q. rewrite assoc' in Q.
      rewrite directSumMapEqIn1 in Q. exact Q.
    - intros T h eqn.
      assert (E : h · ι₁ · directSumMap BD CD g (identity D) = 0).
      { rewrite assoc'. rewrite directSumMapEqIn1. rewrite assoc.
        refine (maponpaths (λ r, r·ι₁) eqn @ _). apply zeroLeft. }
      assert (Q := iscontrpr1 (pr2 K T (h·ι₁) E)); simpl in Q.
      induction Q as [p e].
      exists p.
      rewrite assoc in e.
      apply (to_In1_isMonic _ _ _ _ _ e).
  Qed.
  Lemma CokernelPlusIdentity {M:ExactCategory} {A B C:M} (f:A-->B) (g:B-->C) (D:M)
        (BD : BinDirectSum B D) (CD : BinDirectSum C D):
    isCokernel' f g ->
    isCokernel' (f · ι₁) (directSumMap BD CD g (identity D)).
  Proof.
    intros ic.
    split.
    { rewrite assoc'. rewrite directSumMapEqIn1. rewrite assoc. rewrite (pr1 ic). apply zeroLeft. }
    intros T h u.
    apply iscontraprop1.
    { apply invproofirrelevance. intros [r r'] [s s']. apply subtypeEquality_prop; cbn.
      assert (Q := r' @ ! s'); clear r' s' u h. apply FromBinDirectSumsEq.
      - assert (L := maponpaths (λ w, ι₁ · w) Q); clear Q. simpl in L. rewrite 2 assoc in L.
        rewrite directSumMapEqIn1 in L.
        rewrite 2 assoc' in L. exact (CokernelIsEpi _ g ic _ _ _ L).
      - assert (L := maponpaths (λ w, ι₂ · w) Q); clear Q. simpl in L. rewrite 2 assoc in L.
        rewrite directSumMapEqIn2 in L.
        rewrite 2 assoc' in L. rewrite 2 id_left in L. exact L. }
    assert (Q := iscontrpr1 (pr2 ic _ _ (assoc _ _ _ @ u))).
    induction Q as [q Q].
    exists (π₁ · q + π₂ · ι₂ · h).
    rewrite rightDistribute.
    rewrite assoc. rewrite assoc. rewrite assoc.
    unfold directSumMap. unfold BinDirectSumIndAr. rewrite BinDirectSumPr1Commutes,BinDirectSumPr2Commutes.
    rewrite id_right.
    rewrite assoc'. rewrite Q. rewrite assoc.
    rewrite <- leftDistribute.
    refine (_ @ id_left _).
    apply (maponpaths (λ w, w·h)).
    use to_BinOpId''.
  Qed.
  Lemma MapPlusIdentityToPullback {M:ExactCategory} {A B:M} (f:A-->B) (C:M)
        (AC : BinDirectSum A C) (BC : BinDirectSum B C) :
    isPullback _ _ _ _ (MapPlusIdentityToCommSq f C AC BC).
  Proof.
    intros T g h e. apply iscontraprop1.
    - apply invproofirrelevance. intros [p [P P']] [q [Q Q']].
      apply subtypeEquality.
      { intros r. apply isapropdirprod; apply to_has_homsets. }
      cbn. clear P Q.
      refine (! id_right _ @ _ @ id_right _).
      rewrite <- (to_IdIn1 AC). rewrite 2 assoc. induction (!P'), (!Q'). reflexivity.
    - exists (h · π₁).
      split.
      + refine (_ @ id_right _). rewrite <- (to_IdIn1 BC).
        rewrite (assoc g). rewrite e. rewrite (assoc' h _ π₁).
        unfold directSumMap. unfold BinDirectSumIndAr. rewrite BinDirectSumPr1Commutes.
        rewrite assoc. reflexivity.
      + refine (_ @ id_right _). rewrite <- (to_BinOpId' AC).
        rewrite rightDistribute. rewrite assoc. refine (! runax (_-->_) _ @ _).
        apply maponpaths. rewrite assoc. apply pathsinv0.
        assert (K : h · π₂ = 0).
        { refine ( _ @ maponpaths (λ w, w · π₂) (!e) @ _ ).
          - rewrite assoc'.
            unfold directSumMap. unfold BinDirectSumIndAr. rewrite BinDirectSumPr2Commutes.
            rewrite id_right. reflexivity.
          - rewrite assoc'. rewrite (to_Unel1 BC). unfold to_unel.
            apply zeroRight. }
        rewrite K. apply zeroLeft.
  Qed.
  (** The "obscure" axiom c of Quillen. *)
  Lemma AdmMonoFromComposite {M:ExactCategory} {A B C:M} (i:A-->B) (j:B-->C) :
    hasCokernel i -> isAdmissibleMonomorphism (i·j) -> isAdmissibleMonomorphism i.
  Proof.
    (* see Bühler's 2.16 *)
    intros hc im.
    apply (squash_to_hProp (C ⊕ B)); intros CB.
    apply (squash_to_hProp (B ⊕ C)); intros BC.
    set (q := ToBinDirectSum CB (i · j) i).
    assert (s := AdmMonoEnlargement _ (i·j) i im : isAdmissibleMonomorphism q); clear im.
    assert (e : q · elem12 _ (grinv j) = ToBinDirectSum CB 0 i).
    { apply ToBinDirectSumsEq.
      - rewrite BinDirectSumPr1Commutes. unfold elem12. rewrite rightDistribute, leftDistribute.
        rewrite id_right. rewrite (assoc' π₂). rewrite (assoc q). rewrite (assoc (q · π₂)).
        rewrite (assoc' _ _ π₁). rewrite (to_IdIn1 CB). rewrite id_right.
        rewrite rightMinus. unfold q. rewrite BinDirectSumPr1Commutes, BinDirectSumPr2Commutes.
        apply (grrinvax (_-->_)).
      - rewrite BinDirectSumPr2Commutes. unfold elem12. rewrite rightDistribute, leftDistribute.
        rewrite id_right. rewrite assoc. rewrite (assoc' _ _ π₂).
        rewrite (to_Unel1 CB); unfold to_unel. rewrite zeroRight. rewrite runax.
        unfold q. rewrite BinDirectSumPr2Commutes. reflexivity. }
    assert (e' : q · elem12 _ (grinv j) · SwitchMap _ _ _ _ = ToBinDirectSum BC i 0).
    { rewrite e. apply SwitchMapEqnTo. }
    assert (l : isAdmissibleMonomorphism (ToBinDirectSum BC i 0)).
    { induction e'. apply EC_ComposeMono.
      - apply EC_ComposeMono.
        + exact s.
        + apply IsIsoIsMono. apply elem12_isiso.
      - apply IsIsoIsMono. apply (SwitchIso C B). }
    clear e' e s q.
    apply (squash_to_hProp hc); clear hc; intros [D [k ic]].
    apply (squash_to_hProp (D ⊕ C)); intros DC.
    assert (PB := is_symmetric_isPullback (homset_property M) _ (MapPlusIdentityToPullback k C BC DC)).
    assert (co := CokernelPlusIdentity i k C BC DC ic).
    assert (es := ExactSequenceFromMono _ _ co); clear co.
    assert (t : i · to_In1 BC = ToBinDirectSum BC i 0).
    { rewrite <- ToBinDirectSumFormulaUnique. unfold ToBinDirectSumFormula.
      rewrite rewrite_op. rewrite zeroLeft, runax. reflexivity. }
    assert (l' : isAdmissibleMonomorphism (i · to_In1 BC)).
    { induction (!t). exact l. }
    clear l t.
    assert (ee := es l'); clear es l'.
    use (ExactToAdmMono (p:=k)). use (ExactSequenceFromEpi i k).
    - use KernelPlusIdentity. 4: exact (EC_ExactToKernel ee).
    - use (IsPullbackEpiIsEpi PB). exact (ExactToAdmEpi ee).
  Qed.
  Lemma AdmEpiFromComposite {M:ExactCategory} {A B C:M} (i:A-->B) (j:B-->C) :
    hasKernel j -> isAdmissibleEpimorphism (i·j) -> isAdmissibleEpimorphism j.
  Proof.
    exact (AdmMonoFromComposite (M:=M^op) j i).
  Qed.
End ExactCategoryFacts.

Section EquivalenceOfTwoDefinitions.
  Theorem EquivalenceOfTwoDefinitions (D:ExactCategoryData) :
    ExactCategoryProperties D ⇔ ExactCategoryProperties_Quillen D.
  Proof.
    split.
    { intros prop.
      set (M := (D,,prop) : ExactCategory).
      split.
      { exact (@EC_IsomorphicToExact M). }
      split.
      { exact (@DirectSumToExact M). }
      split.
      { exact (@EC_ExactToKernelCokernel M). }
      split.
      { split.
        { exact (@EC_ComposeMono M). }
        { exact (@EC_ComposeEpi M). } }
      split.
      { split.
        { exact (@EC_PullbackEpi M). }
        { exact (@EC_PushoutMono M). } }
      { split.
        { exact (@AdmMonoFromComposite M). }
        { exact (@AdmEpiFromComposite M). } } }
    { intros [P1 [P2 [P3 [[P4 P4'] [[P5 P5'] [P6 P7]]]]]].
      split.
      { split.
        { exact P1. }
        { intros P Q i. exact (P1 P Q (InverseMorphismPairIsomorphism i)). } }
      { split.
        { split.
          { intros A. apply (squash_to_hProp (to_Zero' D)); intros Z. apply hinhpr.
            exists Z. set (Q := TrivialDirectSum Z A). exists (to_Pr2 Q).
            exact (P2 A Z Q). }
          { intros A. apply (squash_to_hProp (to_Zero' D)); intros Z. apply hinhpr.
            exists Z. set (Q := TrivialDirectSum' Z A). exists (to_In1 Q).
            exact (P2 Z A Q). } }
        split.
        { exact P3. }
        split.
        { split.
          { exact P4. }
          { exact P4'. } }
        split.
        { exact P5. }
        { exact P5'. } } }
  Defined.
End EquivalenceOfTwoDefinitions.

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

Section SplitSequences.
  Local Open Scope addmonoid.
  Local Open Scope abgr.
  Local Open Scope abgrcat.
  Definition isSplit2 {M:PreAdditive} {A B C:M} (i:A-->B) (p:B-->C) : hProp :=
    ∃ (q:A<--B) (j:B<--C), isBinDirectSum M A C B i j q p.
  Definition isSplit {M:PreAdditive} (P : MorphismPair M) : hProp := isSplit2 (Mor1 P) (Mor2 P).
  Lemma DirectSumToSplit {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isSplit2 (to_In1 AB) (to_Pr2 AB).
  Proof.
    exact (hinhpr (π₁,, ι₂,, BinDirectSum_isBinDirectSum M AB)).
  Qed.
  Lemma DirectSumToSplit' {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isSplit2 (to_In2 AB) (to_Pr1 AB).
  Proof.
    exact (hinhpr(π₂,,ι₁,,BinDirectSum_isBinDirectSum M (reverseBinDirectSum AB))).
  Qed.
  Lemma IsomorphicToSplit {M:PreAdditive} (P Q : MorphismPair M) :
    MorphismPairIsomorphism P Q ⇒ isSplit P ⇒ isSplit Q.
  Proof.
    intros [f' [f [f'' [[e _] [e' _]]]]] ex.
    apply (squash_to_hProp ex); clear ex; intros [q [j su]]; apply hinhpr.
    exists (z_iso_inv f · q · f').
    exists (z_iso_inv f'' · j · f).
    split.
    { intermediate_path (z_iso_inv f' · Mor1 P · q · f').
      { rewrite 2 assoc. apply (maponpaths (λ k, k·f')).
        apply (maponpaths (λ k, k·q)). apply pathsinv0.
        apply z_iso_inv_on_right. rewrite assoc. apply z_iso_inv_on_left. exact e. }
      { rewrite 2 assoc'. rewrite (assoc _ q _).
        intermediate_path (z_iso_inv f' · (identity _ · f')).
        { apply maponpaths. apply (maponpaths (λ k, k·f')). exact (to_IdIn1 su). }
        { rewrite id_left. apply z_iso_after_z_iso_inv. } } }
    split.
    { rewrite assoc'. rewrite e'.  rewrite assoc. rewrite (assoc' _ j _).
      apply wrap_inverse. apply (to_IdIn2 su). }
    split.
    { assert (r := to_Unel1 su); unfold to_unel in r.
      assert (r' := maponpaths (λ t, t · f'') r); cbn in r'; clear r.
      rewrite assoc' in r'. rewrite <- e' in r'. rewrite assoc in r'.
      rewrite <- e in r'. assert (r'' := maponpaths (λ t, z_iso_inv f' · t) r'); clear r'; cbn in r''.
      rewrite 2 assoc in r''. rewrite z_iso_after_z_iso_inv in r''.
      rewrite assoc' in r''. rewrite id_left in r''. rewrite zeroLeft,zeroRight in r''.
      exact r''. }
    split.
    { rewrite 2 assoc. rewrite (assoc' _ f _). rewrite z_iso_inv_after_z_iso.
      rewrite id_right. rewrite (assoc' _ j _). rewrite (to_Unel2 su).
      unfold to_unel. rewrite zeroRight, zeroLeft. reflexivity. }
    { apply (cancel_z_iso' f). rewrite id_right. rewrite rightDistribute.
      rewrite 3 (assoc f). rewrite z_iso_inv_after_z_iso, id_left.
      rewrite assoc'. rewrite e. rewrite assoc.
      rewrite (assoc f). rewrite e'. rewrite (assoc' _ f'').
      rewrite 2 (assoc f''). rewrite z_iso_inv_after_z_iso, id_left. rewrite assoc.
      rewrite <- leftDistribute. rewrite (to_BinOpId' su). rewrite id_left. reflexivity. }
  Qed.
  Local Open Scope addmonoid.
  Local Open Scope abgr.
  Lemma DirectSumToKernel {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isKernel' (to_In1 AB) (to_Pr2 AB).
  Proof.
    apply makeMonicKernel.
    - apply to_In1_isMonic.
    - exact (to_Unel1 AB).
    - intros T h e. exists (h · π₁). unfold eqset; cbn. refine (_ @ id_right _).
      rewrite <- (to_BinOpId AB). rewrite rewrite_op. rewrite rightDistribute.
      rewrite assoc'. rewrite (assoc _ π₂ _). rewrite e. rewrite zeroLeft. rewrite runax. reflexivity.
  Defined.
  Lemma DirectSumToCokernel {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isCokernel' (to_In1 AB) (to_Pr2 AB).
  Proof.
    apply makeEpiCokernel.
    - apply to_Pr2_isEpi.
    - exact (to_Unel1 AB).
    - intros T h e. exists (ι₂ · h). unfold eqset; cbn. refine (_ @ id_left _).
      rewrite <- (to_BinOpId AB). rewrite rewrite_op. rewrite leftDistribute.
      rewrite assoc. rewrite (assoc' _ ι₁ _). rewrite e. rewrite zeroRight. rewrite lunax. reflexivity.
  Defined.
  Lemma isSplitToKernelCokernelPair {M:PreAdditive} {A B C:M} (i:A-->B) (p:B-->C) :
    isSplit2 i p -> isKernelCokernelPair i p.
  Proof.
    intros sp.
    apply (squash_to_hProp sp); clear sp; intros [j [q issum]].
    set (S := mk_BinDirectSum _ _ _ _ _ _ _ _ issum).
    exact (DirectSumToKernel S,,DirectSumToCokernel S).
  Qed.
End SplitSequences.

Section AdditiveToExact.
  Context (M:Additive').
  Lemma AdditiveExactnessProperties : ExactCategoryProperties (M,,isSplit).
  Proof.
    split;unfold ECD_to_AC,pr1.
    - split.
      { intros P Q. apply IsomorphicToSplit. }
      { intros P Q i e. use IsomorphicToSplit.
        2 : { exact (InverseMorphismPairIsomorphism i). }
        exact e. }
    - split.
      { split.
        { intros A. apply (squash_to_hProp (to_Zero' M)); intros Z.
          apply hinhpr. exists Z. set (Q := TrivialDirectSum Z A).
          exact (to_Pr2 Q,, DirectSumToSplit Q). }
        { intros A. apply (squash_to_hProp (to_Zero' M)); intros Z.
          apply hinhpr. exists Z. set (Q := TrivialDirectSum' Z A).
          exact (to_In1 Q,, DirectSumToSplit Q). } }
      split.
      { intros P e. exact (isSplitToKernelCokernelPair _ _ e). }
      split.
      { split.
        {




  Abort.


End AdditiveToExact.
