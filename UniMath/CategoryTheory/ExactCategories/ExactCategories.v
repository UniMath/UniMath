(** * Exact categories *)

(** ** Contents

  - Preliminaries
    - Diagram chasing lemmas

  - The definition of exact category
    - Equivalence with Quillen's definition
    - The exact category structure induced on X by
      a function X -> ob M, where M is an exact category.

 *)

Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.Notations.
Require Export UniMath.MoreFoundations.PartA.

Require Export UniMath.Algebra.BinaryOperations.
Require Export UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.
Require Export UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Export UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.Core.NaturalTransformations.

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
Require Export UniMath.CategoryTheory.opp_precat.
Require Export UniMath.CategoryTheory.PrecategoriesWithAbgrops.
Require Export UniMath.CategoryTheory.PreAdditive.
Require Export UniMath.CategoryTheory.Morphisms.
Require Export UniMath.CategoryTheory.Additive.
Require Export UniMath.CategoryTheory.Subcategory.Full.

Require Export UniMath.MoreFoundations.Propositions.

Local Arguments grinv {_}.

Local Open Scope logic.
Local Open Scope cat.

Local Definition hom (C:precategory_data) : ob C -> ob C -> UU := λ c c', precategory_morphisms c c'.
Local Definition Hom (C : category) : ob C -> ob C -> hSet := λ c c', make_hSet _ (homset_property C c c').
Local Definition Hom_add (C : PreAdditive) : ob C -> ob C -> abgr := λ c c', (@to_abgr C c c').

(* move upstream, when ready *)

Section InvestigateNotations.
  Context (M : PreAdditive) (x y z:M) (f g : hom M x y) (h k : Hom_add M y z).
  Local Open Scope abgrcat.
  Goal empty.
    set (Q := h+k).
    set (r := -g).
    set (t := f-g).
    set (p := f·h + (h∘f) · 1).
    set (o := (h + h) · 1 = h).
    set (s := f+g).
    set (u := f·1).
    set (v := f·0·h).
    (* Set Printing All. *)
  Abort.
End InvestigateNotations.

Section Categories.
  Definition isPushout' {M:category} {a b c d : M} (f : a --> b) (g : a --> c)
             (in1 : b --> d) (in2 : c --> d) : hProp.
  Proof.
    exists (∑ (H : f · in1 = g · in2), isPushout f g in1 in2 H).
    abstract (                  (* this abstraction is important! *)
        apply isaproptotal2 ;
        [ intros H; apply isaprop_isPushout
        | intros H H' po po'; apply homset_property ]) using _P_.
  Defined.
  Definition isPullback' {M:category} {a b c d : M} (f : b --> a) (g : c --> a)
             (p1 : d --> b) (p2 : d --> c) : hProp.
  Proof.
    exists (∑ (H : p1 · f = p2· g), isPullback (*f g p1 p2*) H).
    exact (_P_ (oppositeCategory M) a b c d f g p1 p2).
  Defined.
  Lemma isPullback'_up_to_z_iso {M:category} {a b c d d' : M}
        (f : b --> a) (g : c --> a) (p1 : d --> b) (p2 : d --> c)
        (i : z_iso d' d) :
    isPullback' f g p1 p2 -> isPullback' f g (i·p1) (i·p2).
  Proof.
    intros [e pb]. use tpair.
    - abstract (rewrite 2 assoc'; apply maponpaths; exact e) using _P_.
    - cbn beta. intros T r s eq.
      assert (Q := pb T r s eq).
      use (iscontrweqf _ Q); clear Q.
      use weqtotal2.
      { apply z_iso_comp_left_weq. exact (z_iso_inv i). }
      { intros h. cbn beta. apply weqiff.
        { cbn.
          rewrite 2 (assoc' h). rewrite 2 (assoc _ i).
          rewrite z_iso_after_z_iso_inv. rewrite 2 id_left.
          apply isrefl_logeq. }
        { apply isapropdirprod; apply homset_property. }
        { apply isapropdirprod; apply homset_property. }
        }
  Defined.
  Lemma isPushout'_up_to_z_iso {M:category} {a b c d d' : M}
        (f : a --> b) (g : a --> c) (in1 : b --> d) (in2 : c --> d)
        (i : z_iso d d') :
    isPushout' f g in1 in2 -> isPushout' f g (i∘in1) (i∘in2).
  Proof.
    exact (isPullback'_up_to_z_iso (M:=oppositeCategory M) f g in1 in2 (opp_z_iso i)).
  Qed.
  (* Section bottleneck. *)
  (*   Context {M:category} {a b c d : M} (f : b --> a) (g : c --> a) *)
  (*            (p1 : d --> b) (p2 : d --> c) (pb : isPullback' f g p1 p2). *)
  (*   Time Check (pb : @isPushout' (oppositeCategory M) a b c d f g p1 p2). *)
  (*   (* without the abstraction above, this would be too slow, 13.5 seconds *) *)
  (* End bottleneck. *)
  Lemma Pushout_to_isPushout' {M:category} {a b c : M} (f : a --> b) (g : a --> c)
        (po : Pushout f g) :
    isPushout' f g (PushoutIn1 po) (PushoutIn2 po).
  Proof.
    use tpair.
    - apply PushoutSqrCommutes.
    - cbn beta. apply isPushout_Pushout.
  Qed.
  Lemma Pullback_to_isPullback' {M:category} {a b c : M} (f : b --> a) (g : c --> a)
        (pb : Pullback f g) :
    isPullback' f g (PullbackPr1 pb) (PullbackPr2 pb).
  Proof.
    use tpair.
    - apply PullbackSqrCommutes.
    - cbn beta. apply isPullback_Pullback.
  Qed.
End Categories.

Section MorphismPairs.
  Goal ∏ (M : precategory) (P Q : MorphismPair M) (f:MorphismPairIsomorphism P Q),
       InverseMorphismPairIsomorphism (InverseMorphismPairIsomorphism f) = f.
  Proof.
    (* Because this fails, we will have two (dual) properties in the definition
       of exact category, so we can get duality to work better. *)
    Fail reflexivity.
  Abort.
End MorphismPairs.

Section Pullbacks.              (* move upstream *)

  Local Open Scope type.

  Definition IsoArrowTo {M : category}     {A A' B:M} (g : A --> B) (g' : A' --> B) := ∑ i : z_iso A A', i · g' = g.
  Coercion IsoArrowTo_pr1 {M : category}   {A A' B:M} (g : A --> B) (g' : A' --> B) : IsoArrowTo g g' -> z_iso A A' := pr1.

  Definition IsoArrowFrom {M : category}   {A B B':M} (g : A --> B) (g' : A --> B') := ∑ i : z_iso B B', g · i  = g'.
  Coercion IsoArrowFrom_pr1 {M : category} {A B B':M} (g : A --> B) (g' : A --> B') : IsoArrowFrom g g' -> z_iso B B' := pr1.
  (* this definition of IsoArrow is asymmetric *)

  Definition IsoArrow {M : category}       {A A' B B':M} (g : A --> B) (g' : A' --> B') := ∑ (i : z_iso A A') (j : z_iso B B'), i · g' = g · j.

  Definition pullbackiso1 {M : category} {A B C:M} {f : A --> C} {g : B --> C}
        (pb : Pullback f g) (pb' : Pullback f g)
    : IsoArrowTo (PullbackPr1 pb) (PullbackPr1 pb')
    := pr1 (pullbackiso _ pb pb'),,pr12 (pullbackiso _ pb pb').

  Definition pullbackiso2 {M : category} {A B C:M} {f : A --> C} {g : B --> C}
        (pb : Pullback f g) (pb' : Pullback f g)
    : IsoArrowTo (PullbackPr2 pb) (PullbackPr2 pb')
    := pr1 (pullbackiso _ pb pb'),,pr22 (pullbackiso _ pb pb').

  Section OppositeIsoArrows.

    Definition opposite_IsoArrowTo {M:category} {A A' B:M} {g : A --> B} {g' : A' --> B} :
      IsoArrowTo g g' -> IsoArrowFrom (M:=M^op) g' g.
    Proof.
      intros i.
      Fail exact i.
      use tpair.
      - exact (opp_z_iso (pr1 i)).
      - cbn. exact (pr2 i).
    Defined.
    Definition opposite_IsoArrowFrom {M:category} {A B B':M} {g : A --> B} {g' : A --> B'} :
      IsoArrowFrom g g' -> IsoArrowTo (M:=M^op) g' g.
    Proof.
      intros i. use tpair.
      - exact (opp_z_iso (pr1 i)).
      - cbn. exact (pr2 i).
    Defined.
    Definition opposite_IsoArrow {M:category} {A A' B B':M} (g : A --> B) (g' : A' --> B') :
      IsoArrow g g' -> IsoArrow (M:=M^op) (opp_mor g') (opp_mor g).
    Proof.
      intros i.
      exists (opp_z_iso (pr12 i)).
      exists (opp_z_iso (pr1 i)).
      exact (! pr22 i).
    Defined.
  End OppositeIsoArrows.
  Lemma IsoArrowTo_isaprop (M : category) {A A' B:M} (g : A --> B) (g' : A' --> B) :
    isMonic g' -> isaprop (IsoArrowTo g g').
  Proof.
    intros i. apply invproofirrelevance; intros k k'. apply subtypePath.
    - intro. apply homset_property.
    - induction k as [[k K] e], k' as [[k' K'] e']; cbn; cbn in e, e'.
      induction (i A k k' (e @ !e')). apply maponpaths. apply isaprop_is_z_isomorphism.
  Qed.
  Lemma IsoArrowFrom_isaprop (M : category) {A B B':M} (g : A --> B) (g' : A --> B') :
     isEpi g -> isaprop (IsoArrowFrom g g').
  Proof.
    intros i. apply invproofirrelevance; intros k k'. apply subtypePath.
    { intros j. apply homset_property. }
    induction k as [[k K] e], k' as [[k' K'] e']; cbn; cbn in e, e'.
    apply subtypePath; cbn.
    { intros f. apply isaprop_is_z_isomorphism. }
    use i. exact (e @ !e').
  Qed.
End Pullbacks.

Local Open Scope abgrcat.

(* This exactly duplicates definitions upstream, but Import doesn't get the ones overridden,
   which are useful (mysteriously) for printing: *)
Local Notation "0"     := (unel (grtomonoid (abgrtogr _))) : abgrcat.
Local Notation "0"     := (unel (grtomonoid (abgrtogr (to_abgr _ _)))) : abgrcat.
Local Notation "f + g" := (@op (pr1monoid (grtomonoid (abgrtogr _))) f g) : abgrcat.
Local Notation "f + g" := (@op (pr1monoid (grtomonoid (abgrtogr (to_abgr _ _)))) f g) : abgrcat.
Local Notation "  - g" := (@grinv (abgrtogr _) g) : abgrcat.
Local Notation "  - g" := (@grinv (abgrtogr (to_abgr _ _)) g) : abgrcat.
Local Notation "f - g" := (@op (pr1monoid (grtomonoid (abgrtogr _))) f (@grinv (abgrtogr (to_abgr _ _)) g)) : abgrcat.
Local Notation "f - g" := (@op (pr1monoid (grtomonoid (abgrtogr (to_abgr _ _)))) f (@grinv (abgrtogr (to_abgr _ _)) g)) : abgrcat.

Section PreAdditive.
  (** Reprove some standard facts in additive categories with the 0 map (the zero element of the
      group) replacing the zero map (defined by composing maps to and from the zero object). *)
  Lemma ThroughZeroIsZero {M:PreAdditive} (a b:M) (Z : Zero M) (f : a --> Z) (g : Z --> b) : f · g = 0.
  Proof.
    intermediate_path ((0:a-->Z) · g).
    - apply (maponpaths (postcomp_with g)). apply ArrowsToZero.
    - apply to_postmor_unel'.
  Qed.
  Definition elem21 {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) (f:A-->B) : AB-->AB := 1 + π₁·f·ι₂.
  Section Foo.                  (* because we open scopes *)
    Definition elem21_isiso {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) (f:A-->B) : is_z_isomorphism (elem21 AB f).
    Proof.
      exists (1 - π₁·f·ι₂).
      unfold elem21. split.
      - rewrite leftDistribute, 2 rightDistribute. rewrite id_left. refine (_ @ runax (Hom_add _ _ _) _).
        rewrite assocax. apply maponpaths. rewrite id_right, id_left. rewrite rightMinus.
        rewrite <- assocax. rewrite grlinvax. rewrite lunax. rewrite assoc'. rewrite <- (assoc π₁ f ι₂).
        rewrite (assoc ι₂). rewrite DirectSumIn2Pr1. rewrite zeroLeft. rewrite zeroRight.
        rewrite grinvunel. reflexivity.
      - rewrite leftDistribute, 2 rightDistribute. rewrite id_left. refine (_ @ runax (Hom_add _ _ _) _).
        rewrite assocax. apply maponpaths. rewrite id_right, id_left. rewrite leftMinus.
        rewrite <- assocax. rewrite grrinvax. rewrite lunax. rewrite assoc'. rewrite <- (assoc π₁ f ι₂).
        rewrite (assoc ι₂). rewrite DirectSumIn2Pr1. rewrite zeroLeft. rewrite zeroRight.
        rewrite grinvunel. reflexivity.
    Defined.
  End Foo.
  Definition elem12 {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) (f:B-->A) : AB-->AB := 1 + π₂·f·ι₁.
  Definition elem12_isiso {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) (f:B-->A) : is_z_isomorphism (elem12 AB f).
  Proof.
    exists (1 - π₂·f·ι₁). unfold elem12. split.
    - rewrite leftDistribute, 2 rightDistribute. rewrite id_left. refine (_ @ runax (Hom_add _ _ _) _).
      rewrite assocax. apply maponpaths. rewrite id_right, id_left. rewrite rightMinus.
      rewrite <- assocax. rewrite grlinvax. rewrite lunax. rewrite assoc'. rewrite <- (assoc _ f _).
      rewrite 2 (assoc ι₁). rewrite DirectSumIn1Pr2. rewrite zeroLeft. rewrite zeroLeft.
      rewrite 2 zeroRight.
      use grinvunel.
    - rewrite leftDistribute, 2 rightDistribute. rewrite id_left. refine (_ @ runax (Hom_add _ _ _) _).
      rewrite assocax. apply maponpaths. rewrite id_right, id_left. rewrite leftMinus.
      rewrite <- assocax. rewrite grrinvax. rewrite lunax. rewrite assoc'. rewrite <- (assoc _ f _).
      rewrite (assoc ι₁). rewrite (assoc ι₁). rewrite DirectSumIn1Pr2. rewrite 2 zeroLeft.
      rewrite 2 zeroRight. use grinvunel.
  Defined.

  Definition isKernel' {M:PreAdditive} {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : w --> y), h · g = 0 ⇒ ∃! φ : w --> x, φ · f = h.
  Definition hasKernel {M:PreAdditive} {y z : M} (g : y --> z) : hProp :=
    ∃ x (f:x-->y), isKernel' f g.
  Lemma isKernel_iff {M:PreAdditive} {x y z : M} (Z:Zero M) (f : x --> y) (g : y --> z) :
    isKernel' f g <-> ∑ e : f · g = ZeroArrow Z x z, isKernel Z f g e.
  Proof.
    split.
    { intros [e' ik].
      use tpair.
      { refine (e' @ _). apply PreAdditive_unel_zero. }
      intros T h e.
      exact (ik T h (e @ ! PreAdditive_unel_zero _ _ _ _)). }
    { intros [e ik]. use tpair.
      { refine (e @ ! _). apply PreAdditive_unel_zero. }
      cbn beta. intros T h e'.
      exact (ik T h (e' @ PreAdditive_unel_zero _ _ _ _)). }
  Qed.
  Definition isKernel'_to_Kernel {M:PreAdditive} (Z:Zero M) {x y z : M} (f : x --> y) (g : y --> z) :
    isKernel' f g -> Kernel Z g.
  Proof.
    intros co. exists (x,,f). now apply isKernel_iff.
  Defined.
  Definition isCokernel' {M:PreAdditive} {x y z : M} (f : x --> y) (g : y --> z) : hProp :=
    f · g = 0 ∧ ∀ (w : M) (h : y --> w), f · h = 0 ⇒ ∃! φ : z --> w, g · φ = h.
  Definition hasCokernel {M:PreAdditive} {x y : M} (f : x --> y) : hProp :=
    ∃ z (g:y-->z), isCokernel' f g.
  Lemma isCokernel_iff {M:PreAdditive} {x y z : M} (Z:Zero M) (f : x <-- y) (g : y <-- z) :
    isCokernel' g f <-> ∑ e : f ∘ g = ZeroArrow Z z x, isCokernel Z g f e.
  Proof.
    split.
    { intros [e' ik].
      use tpair.
      { refine (e' @ _). apply PreAdditive_unel_zero. }
      intros T h e.
      exact (ik T h (e @ ! PreAdditive_unel_zero _ _ _ _)). }
    { intros [e ik]. use tpair.
      { refine (e @ ! _). apply PreAdditive_unel_zero. }
      cbn beta. intros T h e'.
      exact (ik T h (e' @ PreAdditive_unel_zero _ _ _ _)). }
  Qed.
  Definition isCokernel'_to_Cokernel {M:PreAdditive} (Z:Zero M) {x y z : M} (f : x --> y) (g : y --> z) :
    isCokernel' f g -> Cokernel Z f.
  Proof.
    intros co. exists (z,,g). now apply isCokernel_iff.
  Defined.
  Section Tmp.
    Lemma PushoutCokernel {M:PreAdditive} {A B C D E:M} (i:A-->B) (p:B-->C)
          (j:B-->D) (p':D-->E) (j':C-->E) :
      isCokernel' i p -> isPushout' (M:=M) j p p' j' -> isCokernel' (i·j) p'.
    Proof.
      intros [b co] [e po].
      (* We show the universal property of the cokernel by showing uniqueness
         and existence simultaneously, i.e., by working with equivalences to show
         a type is contractible. *)
      split.
      - rewrite assoc'.
        (* ambiguous coercions!
           (category_to_precategory (categoryWithAbgrops_category _))
           (precategoryWithBinOps_precategory (categoryWithAbgrops_precategoryWithBinOps _))
         *)
        rewrite e.
(*        unfold  category_to_precategory, pr1 in e.
        rewrite e.
*)
        rewrite assoc. rewrite b. apply zeroLeft.
      - intros T h v. rewrite assoc' in v.
        assert (Q := co T (j·h) v); cbn in Q. generalize Q; clear Q.
        apply iscontrweqb. use make_weq.
        + intros [k w]; exists (j'·k). rewrite assoc. rewrite <- e. rewrite assoc'.
          rewrite w. reflexivity.
        + cbn beta. intros [l w]; unfold hfiber. assert (PO := po T h l (!w)); clear po.
          generalize PO; clear PO. apply iscontrweqb.
          refine (weqcomp (weqtotal2asstor _ _) _). apply weqfibtototal; intros m. cbn.
          apply weqiff.
          { split.
            - intros [x y]. split.
              + exact x.
              + exact (maponpaths pr1 y).
            - intros [x y]. exists x. induction y. apply maponpaths, to_has_homsets.
            }
          { apply isofhleveltotal2.
              - apply to_has_homsets.
              - intros u. refine ((_:isofhlevel 2 _) _ _). apply isofhleveltotal2.
                + apply to_has_homsets.
                + intros n. apply hlevelntosn. apply to_has_homsets. }
          { apply isapropdirprod; apply to_has_homsets. }
    Qed.
  End Tmp.
  Lemma PullbackKernel {M:PreAdditive} {A B C D E:M} (i:A<--B) (p:B<--C)
        (j:B<--D) (p':D<--E) (j':C<--E) :
    isKernel' p i -> isPullback' (M:=M) j p p' j' -> isKernel' p' (i∘j).
  Proof.
    exact (@PushoutCokernel (oppositePreAdditive M) A B C D E i p j p' j').
  Defined.
  Lemma KernelIsMonic {M:PreAdditive} {x y z:M} (f : x --> y) (g : y --> z) : isKernel' f g -> isMonic f.
  Proof.
    intros [t i] w p q e.
    set (T := ∑ r : w --> x, r · f = q · f). assert (ic : ∏ t1 t2 : T, t1 = t2).
    { apply proofirrelevancecontr.
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
      Unset Printing Notations. Arguments paths _ _ _ : clear implicits.
      try assumption.
      refine (@subtypePath_prop _ _ (_,,_) (_,,_) _); simpl. apply im. exact (R@!S).
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
      refine (post_comp_with_iso_is_inj _ _ h (is_iso_from_is_z_iso h j) _ _ _ _).
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
    := BinDirectSumIndAr f g _ _.
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
             (B : isBinDirectSum i1 i2 p1 p2) :
    p1 · i1 + p2 · i2 = identity co := to_BinOpId B.
  Definition to_BinOpId'' {M:PreAdditive} {a b : M} (ab : BinDirectSum a b)
             : (to_Pr1 ab · to_In1 ab) + (to_Pr2 ab · to_In2 ab) = 1
    := to_BinOpId ab.
  Definition ismonoidfun_prop {G H:abgr} (f:G->H) : hProp := make_hProp (ismonoidfun f) (isapropismonoidfun f).
  Definition PreAdditive_functor (M N:PreAdditive) :=
    ∑ F : M ⟶ N, ∀ A B:M, ismonoidfun_prop (@functor_on_morphisms M N F A B : A --> B -> F A --> F B).
  Coercion PreAdditive_functor_to_functor {M N:PreAdditive} : PreAdditive_functor M N -> functor M N := pr1.
  Definition functor_on_morphisms_add {C C' : PreAdditive} (F : PreAdditive_functor C C') { a b : C}
    : monoidfun (a --> b) (F a --> F b)
    := monoidfunconstr (pr2 F a b).
  Local Notation "# F" := (functor_on_morphisms_add F) : abgrcat.
  Lemma add_functor_comp {M N:PreAdditive} (F : PreAdditive_functor M N) {A B C:M} (f:A --> B) (g:B --> C) :
    # F (f · g) = # F f · # F g.
  Proof.
    exact (functor_comp F f g).
  Qed.
  Lemma add_functor_add {M N:PreAdditive} (F : PreAdditive_functor M N) {A B:M} (f g:A --> B) :
    # F (f+g) = # F f + # F g.
  Proof.
    exact (ismonoidfunisbinopfun (pr2 F A B) f g).
  Qed.
  Lemma add_functor_zero {M N:PreAdditive} (F : PreAdditive_functor M N) (A B:M) :
    functor_on_morphisms_add (a:=A) (b:=B) F 0 = 0.
  Proof.
    exact (ismonoidfununel (pr2 F A B)).
  Qed.
  Lemma add_functor_sub {M N:PreAdditive} (F : PreAdditive_functor M N) {A B:M} (g:A --> B) :
    # F (-g) = - # F g.
  Proof.
    exact (grinvandmonoidfun _ _ (pr2 F A B) g).
  Qed.
  Lemma zeroCriterion {M:PreAdditive} {Z:M} : identity Z = 0 <-> isZero Z.
  Proof.
    split.
    { intros e. split.
      - intros T. exists 0. intros h. refine (! id_left h @ _). induction (!e); clear e. apply zeroLeft.
      - intros T. exists 0. intros h. refine (! id_right h @ _). induction (!e); clear e. apply zeroRight. }
    { intros i. apply (isapropifcontr (pr1 i Z)). }
  Qed.
  Lemma applyFunctorToIsZero {M N:PreAdditive} (F : PreAdditive_functor M N) (Z : M) :
    isZero Z -> isZero (F Z).
  Proof.
    exact (λ i, pr1 zeroCriterion (! functor_id F Z @ maponpaths (#F) (pr2 zeroCriterion i) @ add_functor_zero F Z Z)).
  Qed.
  Definition applyFunctorToZero {M N:PreAdditive} (F : PreAdditive_functor M N) : Zero M -> Zero N.
  Proof.
    intros Z. exact (F Z,, applyFunctorToIsZero F Z (pr2 Z)).
  Defined.
  Definition applyFunctorToIsBinDirectSum {M N:PreAdditive} (F : PreAdditive_functor M N)
             (A B S : M) (i1 : A --> S) (i2 : B --> S) (p1 : S --> A) (p2 : S --> B) :
    isBinDirectSum i1 i2 p1 p2 -> isBinDirectSum (# F i1) (# F i2) (# F p1) (# F p2).
  Proof.
    intros ds.
    repeat split.
    - rewrite <- add_functor_comp. rewrite (to_IdIn1 ds). apply functor_id.
    - rewrite <- add_functor_comp. rewrite (to_IdIn2 ds). apply functor_id.
    - rewrite <- add_functor_comp. rewrite (to_Unel1 ds); unfold to_unel. use ismonoidfununel. use (pr2 F).
    - rewrite <- add_functor_comp. rewrite (to_Unel2 ds); unfold to_unel. use ismonoidfununel. use (pr2 F).
    - rewrite <- 2 add_functor_comp. rewrite <- add_functor_add. rewrite (to_BinOpId' ds). apply functor_id.
  Qed.
  Definition applyFunctorToBinDirectSum {M N:PreAdditive} (F : PreAdditive_functor M N) {A B:M} :
    BinDirectSum A B -> BinDirectSum (F A) (F B)
    := λ S, make_BinDirectSum _ _ _ _ _ _ _ _ (applyFunctorToIsBinDirectSum F A B S ι₁ ι₂ π₁ π₂ (pr2 S)).
  Definition induced_PreAdditive_incl (M : PreAdditive) {X:Type} (j : X -> ob M) :
    PreAdditive_functor (induced_PreAdditive M j) M.
  Proof.
    exists (induced_precategory_incl j). intros A B. split.
    + intros f g. reflexivity.
    + reflexivity.
  Defined.
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
    apply subtypePath_prop; cbn.
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
  Lemma inducedMapReflectsKernels (M : PreAdditive) {X:Type} (j : X -> ob M)
        {A B C:induced_PreAdditive M j} (i:A-->B) (p:B-->C) :
    isKernel' (# (induced_PreAdditive_incl M j) i)
              (# (induced_PreAdditive_incl M j) p)
    ->
    isKernel' i p.
  Proof.
    exact (λ k, pr1 k,,λ T h e, pr2 k (j T) h e).
  Qed.
  Lemma inducedMapReflectsCokernels (M : PreAdditive) {X:Type} (j : X -> ob M)
        {A B C:induced_PreAdditive M j} (i:A-->B) (p:B-->C) :
    isCokernel' (# (induced_PreAdditive_incl M j) i)
              (# (induced_PreAdditive_incl M j) p)
    ->
    isCokernel' i p.
  Proof.
    exact (λ k, pr1 k,,λ T h e, pr2 k (j T) h e).
  Qed.
End PreAdditive.
Section KernelCokernelPairs.
  Definition isKernelCokernelPair {M :PreAdditive} {A B C:M} (i : A --> B) (p: B --> C) : hProp
    := isKernel' i p ∧ isCokernel' i p.
  Definition PairToKernel {M :PreAdditive} {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair i p -> isKernel' i p := pr1.
  Definition PairToCokernel {M :PreAdditive} {A B C:M} {i : A --> B} {p: B --> C} :
    isKernelCokernelPair i p -> isCokernel' i p := pr2.
  Lemma inducedMapReflectsKernelCokernelPairs (M : PreAdditive) {X:Type} (j : X -> ob M)
        {A B C:induced_PreAdditive M j} (i:A-->B) (p:B-->C) :
    isKernelCokernelPair
      (# (induced_PreAdditive_incl M j) i)
      (# (induced_PreAdditive_incl M j) p)
    ->
    isKernelCokernelPair i p.
  Proof.
    intros [k c]. split.
    - now apply inducedMapReflectsKernels.
    - now apply inducedMapReflectsCokernels.
  Qed.
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
      apply subtypePath_prop.
      induction φ as [φ e4]; induction φ' as [φ' e5]; cbn.
      use (_ : isEpi q).
      { apply (isEpi_precomp M s q). rewrite e1. apply (CokernelIsEpi i p). apply pr. }
      exact (e4 @ ! e5). }
    exists  k.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout po)); fold s j.
    { refine (assoc _ _ _ @ _ @ e3). apply (maponpaths (λ s, s · k)). exact e1. }
    { refine (assoc _ _ _ @ _ @ ! e). rewrite e2. apply zeroLeft. }
  Qed.
  Lemma PairPullbackKernel {M : PreAdditive} {A B C A':M} (i : A <-- B) (p : B <-- C)
        (pr : isKernelCokernelPair p i)
        (r : A <-- A') (pb : Pullback i r)
        (j := PullbackPr2 pb)
        (pp := PairPullbackMap pr r pb) :
    isKernel' (pr1 pp) j.
  Proof.
    (* Here's where giving the right proof of PairPullbackMap above helped us give this dual proof here. *)
    exact (PairPushoutCokernel (M:=oppositePreAdditive M) i p (opposite_isKernelCokernelPair pr) r pb).
  Defined.
  Lemma SumOfKernelCokernelPairs {M : PreAdditive} {x y z X Y Z : M}
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
  Definition ExactCategoryData := ∑ M:AdditiveCategory, MorphismPair M -> hProp. (* properties added below *)
  Coercion ExactCategoryDataToAdditiveCategory (ME : ExactCategoryData) : AdditiveCategory := pr1 ME.
  Definition isExact {M : ExactCategoryData} (E : MorphismPair M) : hProp := pr2 M E.
  Definition isExact2 {M : ExactCategoryData} {A B C:M} (f:A-->B) (g:B-->C) := isExact (make_MorphismPair f g).
  Definition isAdmissibleMonomorphism {M : ExactCategoryData} {A B:M} (i : A --> B) : hProp :=
    ∃ C (p : B --> C), isExact2 i p.
  Definition AdmissibleMonomorphism {M : ExactCategoryData} (A B:M) : Type :=
    ∑ (i : A --> B), isAdmissibleMonomorphism i.
  Coercion AdmMonoToMap  {M : ExactCategoryData} {A B:M} : AdmissibleMonomorphism A B ->  A --> B := pr1.
  Coercion AdmMonoToMap' {M : ExactCategoryData} {A B:M} : AdmissibleMonomorphism A B -> (A --> B)%cat := pr1.
  Definition isAdmissibleEpimorphism {M : ExactCategoryData} {B C:M} (p : B --> C) : hProp :=
    ∃ A (i : A --> B), isExact2 i p.
  Definition AdmissibleEpimorphism {M : ExactCategoryData} (B C:M) : Type :=
    ∑ (p : B --> C), isAdmissibleEpimorphism p.
  Coercion AdmEpiToMap  {M : ExactCategoryData} {B C:M} : AdmissibleEpimorphism B C ->  B --> C := pr1.
  Coercion AdmEpiToMap' {M : ExactCategoryData} {B C:M} : AdmissibleEpimorphism B C -> (B --> C)%cat := pr1.
  Lemma ExactToAdmMono {M : ExactCategoryData} {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isAdmissibleMonomorphism i.
  Proof.
    intros e. exact (hinhpr(C,,p,,e)).
  Qed.
  Lemma ExactToAdmEpi {M : ExactCategoryData} {A B C:M} {i : A --> B} {p : B --> C} : isExact2 i p -> isAdmissibleEpimorphism p.
  Proof.
    intros e. exact (hinhpr(A,,i,,e)).
  Qed.
  (** The following definition is definition 2.1 from the paper of Bühler. *)
  Local Definition ExactCategoryProperties (M : ExactCategoryData) : hProp :=
      ((∀ (P Q : MorphismPair M), MorphismPairIsomorphism P Q ⇒ isExact P ⇒ isExact Q) ∧
       (∀ (P Q : MorphismPair M), MorphismPairIsomorphism Q P ⇒ isExact P ⇒ isExact Q)) ∧
      ((∀ A:M, isAdmissibleMonomorphism (identity A)) ∧
       (∀ A:M, isAdmissibleEpimorphism (identity A))) ∧
      (∀ P : MorphismPair M, isExact P ⇒ isKernelCokernelPair (Mor1 P) (Mor2 P)) ∧
      ((∀ (A B C:M) (f : A --> B) (g : B --> C),
          isAdmissibleMonomorphism f ⇒ isAdmissibleMonomorphism g ⇒
          isAdmissibleMonomorphism (f · g)) ∧
       (∀ (A B C:M) (f : A --> B) (g : B --> C),
          isAdmissibleEpimorphism f ⇒ isAdmissibleEpimorphism g ⇒
          isAdmissibleEpimorphism (f · g))) ∧
      ((∀ (A B C:M) (f : A --> B) (g : C --> B),
          isAdmissibleEpimorphism f ⇒
          ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)) ∧
       (∀ (A B C:M) (f : B --> A) (g : B --> C),
          isAdmissibleMonomorphism f ⇒
          ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO))).
  (** The following definition is from Higher Algebraic K-theory I, by Quillen.
      We prove below that the two definitions are equivalent. *)
  Local Definition ExactCategoryProperties_Quillen (M : ExactCategoryData) : hProp :=
      (∀ (P Q:MorphismPair M), MorphismPairIsomorphism P Q ⇒ isExact P ⇒ isExact Q) ∧
      (∀ (A B:M) (AB:BinDirectSum A B), isExact2 (to_In1 AB) (to_Pr2 AB)) ∧
      (∀ P : MorphismPair M, isExact P ⇒ isKernel' (Mor1 P) (Mor2 P) ∧ isCokernel' (Mor1 P) (Mor2 P)) ∧
      ((∀ (A B C:M) (f : A --> B) (g : B --> C),
          isAdmissibleMonomorphism f ⇒ isAdmissibleMonomorphism g ⇒
          isAdmissibleMonomorphism (f · g)) ∧
       (∀ (A B C:M) (f : A --> B) (g : B --> C),
          isAdmissibleEpimorphism f ⇒ isAdmissibleEpimorphism g ⇒
          isAdmissibleEpimorphism (f · g))) ∧
      ((∀ (A B C:M) (f : A --> B) (g : C --> B),
          isAdmissibleEpimorphism f ⇒
          ∃ (PB : Pullback f g), isAdmissibleEpimorphism (PullbackPr2 PB)) ∧
       (∀ (A B C:M) (f : B --> A) (g : B --> C),
          isAdmissibleMonomorphism f ⇒
          ∃ (PO : Pushout f g), isAdmissibleMonomorphism (PushoutIn2 PO))) ∧
       ((∀ (A B C:M) (i:A-->B) (j:B-->C),
          hasCokernel i ⇒ isAdmissibleMonomorphism (i·j) ⇒ isAdmissibleMonomorphism i) ∧
        (∀ (A B C:M) (i:A-->B) (j:B-->C),
          hasKernel j ⇒ isAdmissibleEpimorphism (i·j) ⇒ isAdmissibleEpimorphism j)).
  Definition ExactCategory := ∑ (ME:ExactCategoryData), ExactCategoryProperties ME.
  Coercion ExactCategoryToData (M:ExactCategory) : ExactCategoryData := pr1 M.
  Definition make_ExactCategory (ME:ExactCategoryData) (p : ExactCategoryProperties ME) : ExactCategory := ME,,p.
  Definition isExactFunctor {M N:ExactCategory} (F : M ⟶ N) : hProp
    := ∀ (P : MorphismPair M), isExact P ⇒ isExact (applyFunctorToPair F P).
  Definition ExactFunctor (M N:ExactCategory)
    := ∑ F : M ⟶ N, isExactFunctor F.
  (* TO DO : show an exact functor is additive, or else include that as a condition.
     That includes showing it induces monoid functions on Hom groups.
     Start by defining preadditive functors and additive functors. *)
  Coercion ExactFunctorToFunctor {M N:ExactCategory}
    : ExactFunctor M N -> (M ⟶ N)
    := pr1.
  Definition ShortExactSequence (M:ExactCategory) := ∑ (P : MorphismPair M), isExact P.
  Coercion ShortExactSequenceToMorphismPair {M:ExactCategory} (P : ShortExactSequence M)
    : MorphismPair M
    := pr1 P.
  Definition ShortExactSequenceMap {M:ExactCategory} (P Q:ShortExactSequence M) := MorphismPairMap P Q.
  Definition applyFunctorToShortExactSequence {M N:ExactCategory} (F : ExactFunctor M N) :
    ShortExactSequence M -> ShortExactSequence N.
  Proof.
    intros E. exists (applyFunctorToPair F E).
    induction E as [E iE]. unfold ShortExactSequenceToMorphismPair,pr1.
    exact (pr2 F E iE).
  Defined.
  Definition composeExactFunctors {L M N:ExactCategory} : ExactFunctor L M -> ExactFunctor M N -> ExactFunctor L N.
  Proof.
    intros F G. exists (F ∙ G). exact (λ E e, pr2 G _ (pr2 F E e)).
  Defined.
End theDefinition.

Declare Scope excat.
Delimit Scope excat with excat.
Local Open Scope excat.
Notation "A ↣ B" := (AdmissibleMonomorphism A B) : excat.
Notation "B ↠ C" := (AdmissibleEpimorphism  B C) : excat.
Notation "F ∙ G" := (composeExactFunctors F G) : excat.
Notation "M ⟶ N" := (ExactFunctor M N) : excat.

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
    exists (oppositeAdditiveCategory M). exact (λ p, @isExact M (opp_MorphismPair p)).
  Defined.
  Definition oppositeExactCategory (M:ExactCategory) : ExactCategory.
  Proof.
    use (make_ExactCategory (oppositeExactCategoryData M)).
    split.
    { split;intros P Q f.
      - exact (EC_IsomorphicToExact' (opp_MorphismPairIsomorphism f)).
      - exact (EC_IsomorphicToExact (opp_MorphismPairIsomorphism f)). }
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
End OppositeExactCategory.

Notation "C '^op'" := (oppositeExactCategory C) (at level 3, format "C ^op") : excat.

Section ExactCategoryFacts.
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
    simple refine (make_MorphismPairIsomorphism
                     (make_MorphismPair f p) (make_MorphismPair f' (z_iso_inv h · p))
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
        {h : P --> A} {k : P --> C} :
    isPullback' (M:=M) f g h k -> isAdmissibleEpimorphism f -> isAdmissibleEpimorphism k.
  (* dual needed *)
  Proof.
    intros pb. exact (PullbackEpiIsEpi f g (make_Pullback _ (pr2 pb))).
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
    apply (squash_to_hProp (to_hasZero M)); intros Z.
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
  Definition TrivialExactSequence {M : ExactCategory} (A:M) (Z:Zero M) : ShortExactSequence M.
  Proof.
    assert (Q := DirectSumToExact (TrivialDirectSum Z A)).
    exact (make_MorphismPair ι₁ π₂,, Q).
  Defined.
  Definition TrivialExactSequence' {M : ExactCategory} (Z:Zero M) (A:M) : ShortExactSequence M.
  Proof.
    assert (Q := DirectSumToExact (TrivialDirectSum' Z A)).
    exact (make_MorphismPair ι₁ π₂,, Q).
  Defined.
  Lemma ExactPushout {M : ExactCategory} {A B C A':M} (i : A --> B) (p : B --> C)
        (pr : isExact2 i p) (r : A --> A') :
    ∃ (po : Pushout i r),
      isExact2 (PushoutIn2 po) (pr1 (PairPushoutMap (EC_ExactToKernelCokernel pr) r po)).
  Proof.
    assert (I := ExactToAdmMono pr).
    assert (R := EC_PushoutMono i r I).
    apply (squash_to_hProp R); clear R; intros [po J]; apply hinhpr.
    exists po. use ExactSequenceFromMono.
    { exact (PairPushoutCokernel i p (EC_ExactToKernelCokernel pr) r po). }
    exact J.
  Qed.
  Lemma ExactPushout' {M : ExactCategory} {A B C A':M} (i : A --> B) (p : B --> C)
        (pr : isExact2 i p) (r : A --> A') :
    ∃ (B':M) (i':A'-->B') (s:B-->B') (p':B'-->C),
       s·p' = p ∧ isPushout' (M:=M) i r s i' ∧ isExact2 i' p'.
  Proof.
    assert (I := ExactToAdmMono pr). assert (R := EC_PushoutMono i r I).
    use (hinhfun _ R); clear R; intros [po J].
    set (pomap := PairPushoutMap (EC_ExactToKernelCokernel pr) r po).
    set (p' := pr1 pomap).
    exists po. exists (PushoutIn2 po). exists (PushoutIn1 po). exists p'.
    split.
    { exact (pr12 pomap). }
    split.
    { apply Pushout_to_isPushout'. }
    { use ExactSequenceFromMono.
      { exact (PairPushoutCokernel i p (EC_ExactToKernelCokernel pr) r po). }
      exact J. }
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
  Lemma ExactPullback' {M : ExactCategory} {A B C A':M} (i : A <-- B) (p : B <-- C)
        (pr : isExact2 p i) (r : A <-- A') :
    ∃ (B':M) (i':A'<--B') (s:B<--B') (p':B'<--C),
      s∘p' = p ∧ isPullback' (M:=M) i r s i' ∧ isExact2 p' i'.
  Proof.
    assert (I := ExactToAdmEpi pr). assert (R := EC_PullbackEpi i r I).
    use (hinhfun _ R); clear R; intros [pb J].
    set (pbmap := PairPullbackMap (EC_ExactToKernelCokernel pr) r pb).
    set (p' := pr1 pbmap).
    exists pb. exists (PullbackPr2 pb). exists (PullbackPr1 pb). exists p'.
    split.
    { exact (pr12 pbmap). }
    split.
    { apply Pullback_to_isPullback'. }
    { use ExactSequenceFromEpi.
      { exact (PairPullbackKernel i p (EC_ExactToKernelCokernel pr) r pb). }
      exact J. }
  Qed.
  Lemma MonicAdmEpiIsIso {M : ExactCategory} {A B:M} (p : A ↠ B) : isMonic p -> is_z_isomorphism p.
  Proof.
    induction p as [p E]. cbn. intros I. apply (squash_to_prop E).
    { apply (isaprop_is_z_isomorphism (C:=M)). }
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
    apply (squash_to_hProp (to_hasZero M)); intros Z.
    apply (squash_to_hProp (to_hasBinDirectSums D Z)); intros DZ.
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
    apply (squash_to_hProp (to_hasBinDirectSums A B')); intros AB'.
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
    apply (squash_to_hProp (to_hasBinDirectSums A C)); intros AC.
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
    apply (squash_to_hProp (to_hasBinDirectSums C C')); intros CC'.
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
    apply (squash_to_hProp (to_hasBinDirectSums C C')); intros CC'.
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
    { apply invproofirrelevance. intros [r r'] [s s']. apply subtypePath_prop; cbn.
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
    isPullback (MapPlusIdentityToCommSq f C AC BC).
  Proof.
    intros T g h e. apply iscontraprop1.
    - apply invproofirrelevance. intros [p [P P']] [q [Q Q']].
      apply subtypePath.
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
        rewrite rightDistribute. rewrite assoc. refine (! runax (Hom_add _ _ _) _ @ _).
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
    apply (squash_to_hProp (to_hasBinDirectSums C B)); intros CB.
    apply (squash_to_hProp (to_hasBinDirectSums B C)); intros BC.
    set (q := ToBinDirectSum CB (i · j) i).
    assert (s := AdmMonoEnlargement _ (i·j) i im : isAdmissibleMonomorphism q); clear im.
    assert (e : q · elem12 _ (grinv j) = ToBinDirectSum CB 0 i).
    { apply ToBinDirectSumsEq.
      - rewrite BinDirectSumPr1Commutes. unfold elem12. rewrite rightDistribute, leftDistribute.
        rewrite id_right. rewrite (assoc' π₂). rewrite (assoc q). rewrite (assoc (q · π₂)).
        rewrite (assoc' _ _ π₁). rewrite (to_IdIn1 CB). rewrite id_right.
        rewrite rightMinus. unfold q. rewrite BinDirectSumPr1Commutes, BinDirectSumPr2Commutes.
        apply (grrinvax (Hom_add _ _ _)).
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
    apply (squash_to_hProp (to_hasBinDirectSums D C)); intros DC.
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
    - use (IsPullbackEpiIsEpi (_,,PB)). exact (ExactToAdmEpi ee).
  Qed.
  Lemma AdmEpiFromComposite {M:ExactCategory} {A B C:M} (i:A-->B) (j:B-->C) :
    hasKernel j -> isAdmissibleEpimorphism (i·j) -> isAdmissibleEpimorphism j.
  Proof.
    exact (AdmMonoFromComposite (M:=M^op) j i).
  Qed.
  Section Tmp.
    Lemma CokernelSequence {M:ExactCategory} {A B C P R:M}
          (i : A --> B) (j : B --> C) (p : B --> P) (q : C --> R) :
      isExact2 i p -> isExact2 j q ->
      ∃ Q (s : C --> Q) (k : P --> Q) (r : Q --> R),
        isExact2 (i·j) s ∧ isExact2 k r ∧ isPushout' (M:=M) j p s k ∧ s · r = q.
    Proof.
      intros ip jq.
      assert (co := EC_ExactToCokernel ip : isCokernel' i p).
      assert (b := EC_ExactToCokernel jq : isCokernel' j q).
      assert (I := ExactToAdmMono ip).
      assert (J := ExactToAdmMono jq).
      assert (IJ := EC_ComposeMono _ _ I J).
      induction b as [a co'].
      assert (ijq : i · (j · q) = 0).
      { rewrite a. apply zeroRight. }
      assert (po := EC_PushoutMono j p (ExactToAdmMono jq)).
      use (hinhfun _ po); clear po; intros [[[Q [s k]] [e1 po]] K].
      change (isPushout j p s k e1) in po;
        change (hProptoType (isAdmissibleMonomorphism k)) in K;
        change (hProptoType (j · s = p · k)) in e1.
      assert (L := PushoutCokernel _ _ _ _ _ co (_,,po)).
      exists Q. exists s. exists k.
      assert (e2 : j · q = p · 0).
      { rewrite a. now rewrite zeroRight. }
      assert (PO := iscontrpr1 (po R q 0 e2)).
      induction PO as [u [e3 e4]].
      exists u.
      assert (ijs := ExactSequenceFromMono (i·j) s L IJ).
      exists ijs.
      split.
      { use (ExactSequenceFromMono k u _ K). exists e4. intros T h e0.
        assert (e5 : j · (s · h) = 0).
        { rewrite assoc. rewrite e1. rewrite assoc'. rewrite e0. now rewrite zeroRight. }
        assert (W := co' T (s·h) e5); cbn in W.
        use (iscontrweqf _ W). apply weqfibtototal; intros l. apply weqiff.
        rewrite <- e3. rewrite assoc'.
        split.
        { intros e. now apply (CokernelIsEpi (i·j) s (EC_ExactToCokernel ijs)). }
        { intros e. now apply maponpaths. }
        + apply to_has_homsets.
        + apply to_has_homsets. }
      split.
      - exists e1. exact po.
      - exact e3.
    Defined.
  End Tmp.



  Lemma KernelSequence {M:ExactCategory} {A B C P R:M}
        (i : B --> A) (j : C --> B) (p : P --> B) (q : R --> C) :
    isExact2 p i -> isExact2 q j ->
    ∃ Q (s : Q --> C) (k : Q --> P) (r : R --> Q),
      isExact2 s (j·i) ∧ isExact2 r k ∧ isPullback' (M:=M) j p s k ∧ r · s = q.
  Proof.
    exact (CokernelSequence (M := oppositeExactCategory M) i j p q).
  Defined.


  Lemma ExactIso3 {M:ExactCategory} {A B C C':M} (i:A-->B) (p:B-->C) (t:z_iso C C') :
    isExact2 i p -> isExact2 i (p·t).
  Proof.
    intros ex. use (EC_IsomorphicToExact _ ex).
    exists (identity_z_iso A). exists (identity_z_iso B). exists t. repeat split;cbn.
    - now rewrite id_left, id_right.
    - now rewrite id_left, id_right.
    - apply id_left.
    - apply pathsinv0, id_left.
  Qed.
  Lemma ExactIso2 {M:ExactCategory} {A B C B':M} (i:A-->B) (p:B-->C) (t:z_iso B B') :
    isExact2 i p -> isExact2 (i · t) (z_iso_inv t · p).
  Proof.
    intros ex. use (EC_IsomorphicToExact _ ex).
    exists (identity_z_iso A). exists t. exists (identity_z_iso C). repeat split;cbn.
    - exact (id_left _).
    - exact (! id_left _).
    - rewrite assoc. rewrite z_iso_inv_after_z_iso. rewrite id_left, id_right. reflexivity.
    - rewrite assoc. rewrite z_iso_inv_after_z_iso. rewrite id_left, id_right. reflexivity.
  Qed.
  Lemma ExactIso1 {M:ExactCategory} {A' A B C:M} (t:z_iso A' A) (i:A-->B) (p:B-->C) :
    isExact2 i p -> isExact2 (t·i) p.
  Proof.
    exact (ExactIso3 (M:=oppositeExactCategory M) p i (opp_z_iso t)).
  Defined.
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
          { intros A. apply (squash_to_hProp (to_hasZero D)); intros Z. apply hinhpr.
            exists Z. set (Q := TrivialDirectSum Z A). exists (to_Pr2 Q).
            exact (P2 A Z Q). }
          { intros A. apply (squash_to_hProp (to_hasZero D)); intros Z. apply hinhpr.
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

Section SplitSequences.
  Definition isSplit2 {M:PreAdditive} {A B C:M} (i:A-->B) (q:B-->C) : hProp :=
    ∃ (p:A<--B) (j:B<--C), isBinDirectSum i j p q.
  Lemma commax_hom {M:PreAdditive} {A B:M} (f g:A-->B) : f+g = g+f.
  Proof.
    exact (commax (A-->B) f g).
  Qed.
  Section Foo.
    Goal ∏ {M:PreAdditive} {A B C:M} (i:A-->B) (p:B-->C),
      isSplit2 (M:=M) i p = isSplit2 (M := oppositePreAdditive M) p i.
    Proof.
      Fail reflexivity.
      intros M A B C k r.
      unfold isSplit2, isBinDirectSum; cbn; rewrite rewrite_op.
      (* do we need this? *)
    Abort.
  End Foo.
  Lemma opposite_isSplit2 {M:PreAdditive} {A B C:M} (i:A-->B) (p:B-->C) :
    isSplit2 i p -> isSplit2 (M := oppositePreAdditive M) p i.
  Proof.
    intros s.
    Fail exact s.               (* sigh *)
    use (hinhfun _ s); intros [q [j jq]]. exists j. exists q.
    exists (to_IdIn2 jq). exists (to_IdIn1 jq).
    exists (to_Unel1 jq). exists (to_Unel2 jq).
    rewrite commax_hom. exact (to_BinOpId' jq).
  Qed.
  Definition isSplit {M:PreAdditive} (P : MorphismPair M) : hProp := isSplit2 (Mor1 P) (Mor2 P).
  Lemma opposite_isSplit {M:PreAdditive} (P : MorphismPair M) :
    isSplit P -> isSplit (M:=oppositePreAdditive M) (MorphismPair_opp P).
  Proof.
    exact (opposite_isSplit2 _ _).
  Qed.
  Definition isSplitMonomorphism {M:PreAdditive} {A B:M} (i : A --> B) : hProp :=
    ∃ C (p : B --> C), isSplit2 i p.
  Definition isSplitEpimorphism {M:PreAdditive} {B C:M} (p : B --> C) : hProp :=
    ∃ A (i : A --> B), isSplit2 i p.
  Lemma opposite_isSplitMonomorphism {M:PreAdditive} {A B:M} (i : A --> B) :
    isSplitMonomorphism i -> isSplitEpimorphism (M:=oppositePreAdditive M) i.
  Proof.
    intros s. use (hinhfun _ s); clear s. intros [C [p s]].
    exists C. exists p. exact (opposite_isSplit2 _ _ s).
  Qed.
  Lemma opposite_isSplitEpimorphism {M:PreAdditive} {A B:M} (p : A --> B) :
    isSplitEpimorphism p -> isSplitMonomorphism (M:=oppositePreAdditive M) p.
  Proof.
    intros s. use (hinhfun _ s); clear s. intros [C [i s]].
    exists C. exists i. exact (opposite_isSplit2 _ _ s).
  Qed.
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
  Lemma DirectSumToKernel {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isKernel' (to_In1 AB) (to_Pr2 AB).
  Proof.
    apply makeMonicKernel.
    - apply to_In1_isMonic.
    - exact (to_Unel1 AB).
    - intros T h e. exists (h · π₁). refine (_ @ id_right _).
      rewrite <- (to_BinOpId AB). rewrite rewrite_op. rewrite rightDistribute.
      rewrite assoc'. rewrite (assoc _ π₂ _). rewrite e. rewrite zeroLeft. rewrite runax. reflexivity.
  Defined.
  Lemma DirectSumToCokernel {M:PreAdditive} {A B:M} (AB : BinDirectSum A B) : isCokernel' (to_In1 AB) (to_Pr2 AB).
  Proof.
    apply makeEpiCokernel.
    - apply to_Pr2_isEpi.
    - exact (to_Unel1 AB).
    - intros T h e. exists (ι₂ · h). refine (_ @ id_left _).
      rewrite <- (to_BinOpId AB). rewrite rewrite_op. rewrite leftDistribute.
      rewrite assoc. rewrite (assoc' _ ι₁ _). rewrite e. rewrite zeroRight. rewrite lunax. reflexivity.
  Defined.
  Lemma isSplitToKernelCokernelPair {M:PreAdditive} {A B C:M} (i:A-->B) (p:B-->C) :
    isSplit2 i p -> isKernelCokernelPair i p.
  Proof.
    intros sp.
    apply (squash_to_hProp sp); clear sp; intros [j [q issum]].
    set (S := make_BinDirectSum _ _ _ _ _ _ _ _ issum).
    exact (DirectSumToKernel S,,DirectSumToCokernel S).
  Qed.
  Lemma ComposeSplitMono {M:AdditiveCategory} {A B C : M} (i : A --> B) (j : B --> C) :
    isSplitMonomorphism i ⇒ isSplitMonomorphism j ⇒ isSplitMonomorphism (i · j).
  Proof.
    intros s t.
    apply (squash_to_hProp s); clear s; intros [P [p ip]];cbn in P.
    apply (squash_to_hProp ip); clear ip; intros [p' [i' ip]].
    change (hProptoType (isBinDirectSum i i' p' p)) in ip.
    apply (squash_to_hProp t); clear t; intros [Q [q jq]];cbn in Q.
    apply (squash_to_hProp jq); clear jq; intros [q' [j' jq]].
    change (hProptoType (isBinDirectSum j j' q' q)) in jq.
    apply (squash_to_hProp (to_hasBinDirectSums P Q)); intros PQ.
    apply hinhpr;unfold ExactCategoryDataToAdditiveCategory,pr1.
    exists PQ.
    exists (q' · p · ι₁ + q · ι₂).
    apply hinhpr.
    exists (q' · p').
    exists (π₁ · i' · j + π₂ · j').
    repeat split; rewrite ? rewrite_op.
    { rewrite assoc'. rewrite (assoc j). rewrite (to_IdIn1 jq). rewrite id_left.
      rewrite (to_IdIn1 ip). reflexivity. }
    { rewrite rightDistribute, 2 leftDistribute.
      rewrite (assoc' q'). rewrite (assoc' _ j).
      rewrite (assoc j). rewrite (to_IdIn1 jq). rewrite id_left.
      rewrite assoc'. rewrite (assoc i'). rewrite (to_IdIn2 ip). rewrite id_left.
      rewrite (assoc _ q'). rewrite (assoc' _ j'). rewrite (to_Unel2 jq); unfold to_unel.
      rewrite zeroRight, zeroLeft, runax.
      rewrite (assoc' _ j). rewrite (assoc j). rewrite (to_Unel1 jq). unfold to_unel.
      rewrite zeroLeft, zeroRight, lunax. rewrite assoc'.
      rewrite (assoc j'). rewrite (to_IdIn2 jq). rewrite id_left. apply (to_BinOpId PQ). }
    { rewrite rightDistribute. rewrite assoc'. rewrite (assoc' q').
      rewrite (assoc j). rewrite (to_IdIn1 jq). rewrite id_left.
      rewrite assoc. rewrite (to_Unel1 ip); unfold to_unel.
      rewrite zeroLeft. rewrite lunax. rewrite assoc'.
      rewrite (assoc j). rewrite (to_Unel1 jq); unfold to_unel.
      rewrite zeroLeft, zeroRight. reflexivity. }
    { rewrite leftDistribute. rewrite assoc'. rewrite (assoc j).
      rewrite (to_IdIn1 jq). rewrite id_left. rewrite (assoc' _ i').
      rewrite (to_Unel2 ip); unfold to_unel.
      rewrite zeroRight. rewrite lunax. rewrite assoc'.
      rewrite (assoc j'). rewrite (to_Unel2 jq);unfold to_unel.
      rewrite zeroLeft, zeroRight. reflexivity. }
    { rewrite rightDistribute, 2 leftDistribute. rewrite assoc.
      rewrite (assoc' _ i'). rewrite (assoc' _ ι₁). rewrite (assoc ι₁).
      rewrite (to_IdIn1 PQ). rewrite id_left. rewrite assoc.
      rewrite (assoc' q). rewrite (assoc _ _ (i' · j)).
      rewrite (to_Unel2 PQ); unfold to_unel. rewrite zeroLeft, zeroRight, runax.
      rewrite <- assocax. rewrite <- (leftDistribute _ _ j).
      rewrite 2 (assoc' q'). rewrite <- (rightDistribute q').
      rewrite (to_BinOpId' ip). rewrite id_right.
      rewrite (assoc' _ ι₁). rewrite (assoc ι₁). rewrite (to_Unel1 PQ); unfold to_unel.
      rewrite zeroLeft, zeroRight, lunax. rewrite (assoc' q).
      rewrite (assoc ι₂). rewrite (to_IdIn2 PQ).
      rewrite id_left. exact (to_BinOpId' jq). }
  Qed.
  Lemma ComposeSplitEpi {M:AdditiveCategory} {A B C : M} (p : A --> B) (q : B --> C) :
    isSplitEpimorphism p ⇒ isSplitEpimorphism q ⇒ isSplitEpimorphism (p · q).
  Proof.
    intros r s.
    exact (opposite_isSplitMonomorphism _
             (ComposeSplitMono (M:=oppositeAdditiveCategory M)
                               _ _ (opposite_isSplitEpimorphism _ s) (opposite_isSplitEpimorphism _ r))).
  Qed.
  Lemma PullbackSplitEpi {M:AdditiveCategory} {A A'' C : M} (q : A --> A'') (g : C --> A'') :
    isSplitEpimorphism q -> ∃ PB : Pullback q g, isSplitEpimorphism (PullbackPr2 PB).
  Proof.
    intros s.
    apply (squash_to_hProp s); clear s; intros [A' [i e]].
    apply (squash_to_hProp e); clear e; intros [p [j e]].
    apply (squash_to_hProp (to_hasBinDirectSums A' C)); intros A'C.
    apply hinhpr.
    use tpair.
    - use tpair.
      + exists A'C. exists (π₁ · i + π₂ · g · j). exact π₂.
      + simpl. rewrite rewrite_op.
        use tpair.
        * rewrite leftDistribute. rewrite (assoc' _ j q). rewrite (to_IdIn2 e).
          rewrite id_right. rewrite (assoc' _ i q). rewrite (to_Unel1 e); unfold to_unel.
          rewrite zeroRight, lunax. reflexivity.
        * intros T r s eqn. apply iscontraprop1.
          { apply invproofirrelevance. intros h k.
            apply subtypePath.
            { intros l. apply isapropdirprod;apply to_has_homsets. }
            induction h as [h [H H']], k as [k [K K']]. simpl.
            rewrite <- (id_right h), <- (id_right k). rewrite <- (to_BinOpId' A'C).
            rewrite 2 rightDistribute. rewrite 4 assoc. rewrite H', K'.
            apply (maponpaths (λ z, z + s · ι₂)). rewrite rightDistribute in H, K.
            rewrite 3 assoc in H, K. rewrite H' in H. rewrite K' in K.
            apply (maponpaths (λ z, z · ι₁)).
            apply (to_In1_isMonic _ (make_BinDirectSum _ _ _ _ _ _ _ _ e)).
            change (h · π₁ · i = k · π₁ · i). apply (grrcan (T-->A) (s · g · j)).
            exact (H @ !K). }
          exists (r · p · ι₁ + s · ι₂).
          split.
          { rewrite leftDistribute, 2 rightDistribute.
            rewrite assoc'. rewrite (assoc _ _ i). rewrite (to_IdIn1 A'C). rewrite id_left.
            rewrite (assoc' (r · p)). rewrite 2 (assoc ι₁).
            rewrite (to_Unel1 A'C); unfold to_unel. rewrite 2 zeroLeft, zeroRight, runax.
            rewrite (assoc' s). rewrite (assoc ι₂). rewrite (to_Unel2 A'C); unfold to_unel.
            rewrite zeroLeft, zeroRight, lunax. rewrite 2 assoc. rewrite (assoc' s).
            rewrite (to_IdIn2 A'C). rewrite id_right. rewrite (!eqn).
            rewrite 2 assoc'. rewrite <- (rightDistribute r). rewrite (to_BinOpId' e).
            apply id_right. }
          { rewrite leftDistribute. rewrite (assoc' (r · p)). rewrite (to_Unel1 A'C); unfold to_unel.
            rewrite zeroRight, lunax. rewrite assoc'. rewrite (to_IdIn2 A'C).
            apply id_right. }
    - cbn. exact (hinhpr(A',,ι₁,, hinhpr (π₁,,ι₂,,BinDirectSum_isBinDirectSum _ A'C))).
  Qed.
  Lemma PushoutSplitMono {M:AdditiveCategory} {A A' C : M} (i : A' --> A) (g : A' --> C) :
    isSplitMonomorphism i ⇒ ∃ PO : Pushout i g, isSplitMonomorphism (PushoutIn2 PO).
  Proof.
    intros s.
    assert (Q := @PullbackSplitEpi (oppositeAdditiveCategory M) _ _ _ i g (opposite_isSplitMonomorphism _ s)).
    use (hinhfun _ Q); clear Q; intros [A''C epi].
    exists (A''C).
    exact (opposite_isSplitEpimorphism _ epi).
  Qed.
End SplitSequences.

Section AdditiveToExact.
  Lemma AdditiveExactnessProperties (M:AdditiveCategory) : ExactCategoryProperties (M,,isSplit).
  Proof.
    split;unfold ExactCategoryDataToAdditiveCategory,pr1.
    - split.
      { intros P Q. apply IsomorphicToSplit. }
      { intros P Q i e. use IsomorphicToSplit.
        2 : { exact (InverseMorphismPairIsomorphism i). }
        exact e. }
    - split.
      { split.
        { intros A. apply (squash_to_hProp (to_hasZero M)); intros Z.
          apply hinhpr. exists Z. set (Q := TrivialDirectSum Z A).
          exact (to_Pr2 Q,, DirectSumToSplit Q). }
        { intros A. apply (squash_to_hProp (to_hasZero M)); intros Z.
          apply hinhpr. exists Z. set (Q := TrivialDirectSum' Z A).
          exact (to_In1 Q,, DirectSumToSplit Q). } }
      split.
      { intros P. exact (isSplitToKernelCokernelPair (Mor1 P) (Mor2 P)). }
      split.
      { split.
        { exact (@ComposeSplitMono M). }
        { exact (@ComposeSplitEpi M). } }
      { split.
        { exact (@PullbackSplitEpi M). }
        { exact (@PushoutSplitMono M). } }
  Defined.
  Definition AdditiveToExact : AdditiveCategory -> ExactCategory
    := λ M, make_ExactCategory (M,,isSplit) (AdditiveExactnessProperties M).
  Lemma additive_exact_opposite {M:AdditiveCategory} :
    AdditiveToExact (oppositeAdditiveCategory M) = oppositeExactCategory (AdditiveToExact M).
  Proof.
    intros. apply subtypePath_prop. apply pair_path_in2.
    apply funextsec; intros P. apply hPropUnivalence.
    * exact (opposite_isSplit P).
    * exact (opposite_isSplit (MorphismPair_opp P)).
  Qed.
End AdditiveToExact.

Section InducedExactCategory.
  Definition exts_lift (M:ExactCategory) {X:Type} (j : X -> ob M) :=
    zero_lifts M j ∧ ∀ a B c (i : j a --> B) (p : B --> j c), isExact2 i p ⇒ ∃ b, z_iso (j b) B.
  Definition exts_lift_sums (M:ExactCategory) {X:Type} (j : X -> ob M) :
    exts_lift M j -> sums_lift M j.
  Proof.
    intros el. exists (pr1 el). exact (λ a c S, pr2 el a S c ι₁ π₂ (DirectSumToExact S)).
  Defined.
  Definition induced_ExactCategoryData {M:ExactCategory} {X:Type}
             (j : X -> ob M) : exts_lift M j -> ExactCategoryData.
  Proof.
    intros el. exists (induced_Additive M j (exts_lift_sums M j el)).
    exact (λ P, isExact2 (Mor1 P) (Mor2 P)).
  Defined.
  Definition opp_exts_lift {M:ExactCategory} {X:Type} (j : X -> ob M) :
    exts_lift M j -> exts_lift (oppositeExactCategory M) j.
  Proof.
    intros [hz ce]. exists (opp_zero_lifts j hz).
    intros a B c i p ex. generalize (ce c B a p i ex). apply hinhfun.
    intros [b t]. exists b. exact (z_iso_inv (opp_z_iso t)).
  Defined.
  Lemma opp_sums_exts_lift (M:ExactCategory) {X:Type} (j : X -> ob M) (ce : exts_lift M j ):
    opp_sums_lift M j (exts_lift_sums M j ce) =
    exts_lift_sums M^op j (opp_exts_lift j ce).
  Proof.
    apply pair_path_in2.
    apply funextsec; intro a.
    apply funextsec; intro b.
    apply funextsec; intro S.
    apply isapropishinh.
  Qed.


  Goal ∏ {M:ExactCategory} {X:Type} (j : X -> ob M) (ce : exts_lift M j),
    oppositeExactCategoryData (induced_ExactCategoryData j ce) =
    induced_ExactCategoryData (M:=oppositeExactCategory M) j (opp_exts_lift j ce).
  Proof.
    intros.
    simple refine (total2_paths2_f _ _).
    - refine (induced_opposite_Additive j (exts_lift_sums M j ce) @ _).
      apply maponpaths. apply opp_sums_exts_lift.
    - apply funextsec; intros P. apply hPropUnivalence.
      (* Getting this to work would be good, because then some proofs below
         could be shortened by using duality. *)
      + intros ex. admit.
      + intros ex. admit.
  Abort.

  Definition induced_ExactCategoryProperties {M:ExactCategory} {X:Type}
             (j : X -> ob M) (ce : exts_lift M j) :
    ExactCategoryProperties (induced_ExactCategoryData j ce).
  Proof.
    set (N := induced_ExactCategoryData j ce).
    induction ce as [hz ce].
    transparent assert (J : (PreAdditive_functor N M)).
    { exact (induced_PreAdditive_incl M j). }
    split.
    + split;intros P Q t.
      * exact (EC_IsomorphicToExact  (applyFunctorToPairIsomorphism J _ _ t)).
      * exact (EC_IsomorphicToExact' (applyFunctorToPairIsomorphism J _ _ t)).
    + split.
      * apply (squash_to_hProp hz). intros [_Z iz]. set (zM := make_Zero (j _Z) iz).
        assert (izz : @isZero N _Z).
        { split; intros a; apply iz. }
        set (zN := @make_Zero N _Z izz). (* J zN = zM judgmentally *)
        split.
        { intros A. use ExactToAdmMono.
          3 : { exact (pr2 (TrivialExactSequence (J A) zM)). } }
        { intros A. use ExactToAdmEpi.
          3 : { exact (pr2 (TrivialExactSequence' zM (J A))). } }
      * split;unfold ExactCategoryDataToAdditiveCategory,pr1.
        { intros P iP. apply inducedMapReflectsKernelCokernelPairs.
          exact (EC_ExactToKernelCokernel iP). }
        split.
        { split.
          { intros A B C f g mf mg.
            apply (squash_to_hProp mf); clear mf; intros [P [p fp]].
            apply (squash_to_hProp mg); clear mg; intros [R [q gq]].
            assert (cs := CokernelSequence _ _ _ _ fp gq).
            apply (squash_to_hProp cs); clear cs; intros [T [s [k [r [fgs [kr _]]]]]].
            apply (squash_to_hProp (ce P T R k r kr)); intros [U α].
            apply hinhpr. exists U. exists (s · z_iso_inv α).
            exact (ExactIso3 (f·g) s (z_iso_inv α) fgs). }
          { intros A B C f g mf mg.
            apply (squash_to_hProp mf); clear mf; intros [P [p fp]].
            apply (squash_to_hProp mg); clear mg; intros [R [q gq]].
            assert (cs := KernelSequence _ _ _ _ gq fp).
            apply (squash_to_hProp cs); clear cs; intros [T [s [k [r [fgs [kr _]]]]]].
            apply (squash_to_hProp (ce P T R r k kr)); intros [U α].
            apply hinhpr. exists U. exists (α · s).
            exact (ExactIso1 α s (f·g) fgs). } }
        split.
        { intros A A'' B'' p f'' ep.
          apply (squash_to_hProp ep); clear ep; intros [A' [i ex]].
          assert (Q := ExactPullback' p i ex f'').
          use (squash_to_hProp Q); clear Q; intros [B [p' [f [i' [eq [pb ex']]]]]].
          assert (Q := ce A' B B'' i' p' ex').
          apply (squash_to_hProp Q); clear Q; intros [_B t].
          assert (t' := z_iso_inv t); clear t.
          set (i'' := i' · t'). set (p'' := z_iso_inv t' · p').
          assert (ex'' := ExactIso2 (M:=M) _ _ t' ex' : isExact2 i'' p'').
          assert (pb' : isPullback' (M:=M) p f'' (z_iso_inv t'·f) p'').
          { exact (isPullback'_up_to_z_iso (M:=M) _ _ _ _ (z_iso_inv t') pb). }
          induction pb' as [eq2 pb']. apply hinhpr. use tpair.
          - use tpair.
            + exists _B. exists (z_iso_inv t'·f). exact p''.
            + cbn. exists eq2. now apply induced_precategory_reflects_pullbacks.
          - cbn beta. exact (ExactToAdmEpi (M:=N) ex''). }
        { intros A A'' B'' p f'' ep.
          apply (squash_to_hProp ep); clear ep; intros [A' [i ex]].
          assert (Q := ExactPushout' p i ex f'').
          use (squash_to_hProp Q); clear Q; intros [B [p' [f [i' [eq [pb ex']]]]]].
          assert (Q := ce B'' B A' p' i' ex').
          apply (squash_to_hProp Q); clear Q; intros [_B t].
          set (i'' := i' ∘ t). set (p'' := z_iso_inv t ∘ p').
          assert (ex'' := ExactIso2 (M:=M) _ _ _ ex' : isExact2 p'' i'').
          assert (pb' : isPushout' (M:=M) p f'' (z_iso_inv t∘f) p'').
          { exact (isPushout'_up_to_z_iso (M:=M) _ _ _ _ _ pb). }
          induction pb' as [eq2 pb']. apply hinhpr. use tpair.
          - use tpair.
            + exists _B. exists (z_iso_inv t∘f). exact p''.
            + cbn. exists eq2. now apply induced_precategory_reflects_pushouts.
          - cbn beta. exact (ExactToAdmMono (M:=N) ex''). }
  Qed.
  Definition induced_ExactCategory {M:ExactCategory} {X:Type}
             (j : X -> ob M) (ce : exts_lift M j) : ExactCategory
    := make_ExactCategory (induced_ExactCategoryData j ce)
                        (induced_ExactCategoryProperties j ce).
End InducedExactCategory.
