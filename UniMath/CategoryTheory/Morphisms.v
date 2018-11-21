(** * Some general constructions *)
(** ** Contensts
- Pair of morphisms
- Short exact sequence data
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.functor_categories.

Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.Opp.

(** * Pair of morphisms *)
Section def_morphismpair.

  Context {C : precategory}.

  (** ** Morphism **)

  Definition Morphism : UU := ∑ (a b : C), a --> b.

  Definition mk_Morphism {a b : C} (f : a --> b) : Morphism := (a,,(b,,f)).

  Definition Source (M : Morphism) : ob C := pr1 M.

  Definition Target (M : Morphism) : ob C := pr1 (pr2 M).

  Definition MorphismMor (M : Morphism) : C⟦Source M, Target M⟧ := pr2 (pr2 M).
  Coercion MorphismMor : Morphism >-> precategory_morphisms.


  (** ** MorphismPair **)

  Definition MorphismPair : UU := ∑ (a b c : C), (a --> b × b --> c).

  Definition mk_MorphismPair {a b c : C} (f : a --> b) (g : b --> c) : MorphismPair.
  Proof.
    use tpair.
    - exact a.
    - use tpair.
      + exact b.
      + use tpair.
        * exact c.
        * use dirprodpair.
          -- exact f.
          -- exact g.
  Defined.

  (** Accessor function *)
  Definition Ob1 (MP : MorphismPair) : ob C := pr1 MP.

  Definition Ob2 (MP : MorphismPair) : ob C := pr1 (pr2 MP).

  Definition Ob3 (MP : MorphismPair) : ob C := pr1 (pr2 (pr2 MP)).

  Definition Mor1 (MP : MorphismPair) : C⟦Ob1 MP, Ob2 MP⟧ := dirprod_pr1 (pr2 (pr2 (pr2 MP))).

  Definition Mor2 (MP : MorphismPair) : C⟦Ob2 MP, Ob3 MP⟧ := dirprod_pr2 (pr2 (pr2 (pr2 MP))).

  (** Morphism of morphism pairs *)
  Definition MPMorMors (MP1 MP2 : MorphismPair) : UU :=
    (Ob1 MP1 --> Ob1 MP2) × (Ob2 MP1 --> Ob2 MP2) × (Ob3 MP1 --> Ob3 MP2).

  Definition mk_MPMorMors {MP1 MP2 : MorphismPair} (f1 : Ob1 MP1 --> Ob1 MP2)
             (f2 : Ob2 MP1 --> Ob2 MP2) (f3 : Ob3 MP1 --> Ob3 MP2) : MPMorMors MP1 MP2 :=
    (f1,,(f2,,f3)).

  Definition MPMor1 {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2) : Ob1 MP1 --> Ob1 MP2 :=
    dirprod_pr1 MPM.

  Definition MPMor2 {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2) : Ob2 MP1 --> Ob2 MP2 :=
    dirprod_pr1 (dirprod_pr2 MPM).

  Definition MPMor3 {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2) : Ob3 MP1 --> Ob3 MP2 :=
    dirprod_pr2 (dirprod_pr2 MPM).

  Definition MPMorComms {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2) : UU :=
    (MPMor1 MPM · Mor1 MP2 = Mor1 MP1 · MPMor2 MPM)
      × (MPMor2 MPM · Mor2 MP2 = Mor2 MP1 · MPMor3 MPM).

  Definition mk_MPMorComms {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2)
             (H1 : MPMor1 MPM · Mor1 MP2 = Mor1 MP1 · MPMor2 MPM)
             (H2 : MPMor2 MPM · Mor2 MP2 = Mor2 MP1 · MPMor3 MPM) : MPMorComms MPM := (H1,,H2).

  Definition MPComm1 {MP1 MP2 : MorphismPair} {MPM : MPMorMors MP1 MP2} (MPMC : MPMorComms MPM) :
    MPMor1 MPM · Mor1 MP2 = Mor1 MP1 · MPMor2 MPM := dirprod_pr1 MPMC.

  Definition MPComm2 {MP1 MP2 : MorphismPair} {MPM : MPMorMors MP1 MP2} (MPMC : MPMorComms MPM) :
    MPMor2 MPM · Mor2 MP2 = Mor2 MP1 · MPMor3 MPM := dirprod_pr2 MPMC.

  Definition MPMor (MP1 MP2 : MorphismPair) : UU := ∑ MPM : MPMorMors MP1 MP2, MPMorComms MPM.

  Definition mk_MPMor {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2) (MPMC : MPMorComms MPM) :
    MPMor MP1 MP2 := (MPM,,MPMC).

  Definition MPMor_MPMorMors {MP1 MP2 : MorphismPair} (MPM : MPMor MP1 MP2) :
    MPMorMors MP1 MP2 := pr1 MPM.
  Coercion MPMor_MPMorMors : MPMor >-> MPMorMors.

  Definition MPMor_MPMorComms {MP1 MP2 : MorphismPair} (MPM : MPMor MP1 MP2) :
    MPMorComms MPM := pr2 MPM.
  Coercion MPMor_MPMorComms : MPMor >-> MPMorComms.

  Lemma reverseCommIsoSquare {M : precategory} {P Q P' Q':M} (f:P'-->P) (g:Q'-->Q) (i:z_iso P' Q') (j:z_iso P Q) :
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
  Lemma reverseCommIsoSquare' {M : precategory} {P Q P' Q':M} (f:P'-->P) (g:Q'-->Q) (i:z_iso P' Q') (j:z_iso P Q) :
    f · j = i · g -> g · z_iso_inv j = z_iso_inv i · f.
  Proof.
    intros l. refine (! _). apply reverseCommIsoSquare. refine (! _). exact l.
  Qed.
  Definition MorphismPairMap (P Q : MorphismPair) :=
    ∑ (f : Ob1 P --> Ob1 Q) (g : Ob2 P --> Ob2 Q) (h : Ob3 P --> Ob3 Q),
    f · Mor1 Q = Mor1 P · g  ×  g · Mor2 Q = Mor2 P · h.
  Definition Map1 {P Q : MorphismPair} (f : MorphismPairMap P Q) : Ob1 P --> Ob1 Q := pr1 f.
  Definition Map2 {P Q : MorphismPair} (f : MorphismPairMap P Q) : Ob2 P --> Ob2 Q := pr1 (pr2 f).
  Definition Map3 {P Q : MorphismPair} (f : MorphismPairMap P Q) : Ob3 P --> Ob3 Q := pr1 (pr2 (pr2 f)).
  Definition MorphismPairIsomorphism (P Q : MorphismPair) :=
    ∑ (f : z_iso (Ob1 P) (Ob1 Q)) (g : z_iso (Ob2 P) (Ob2 Q)) (h : z_iso (Ob3 P) (Ob3 Q)),
    ( f · Mor1 Q = Mor1 P · g
      ×
      Mor1 P · g = f · Mor1 Q )
    ×
    ( g · Mor2 Q = Mor2 P · h
      ×
      Mor2 P · h = g · Mor2 Q ).
  Definition InverseMorphismPairIsomorphism {P Q : MorphismPair} :
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
             (P Q : MorphismPair)
             (f : z_iso (Ob1 P) (Ob1 Q))
             (g : z_iso (Ob2 P) (Ob2 Q))
             (h : z_iso (Ob3 P) (Ob3 Q)) :
    f · Mor1 Q = Mor1 P · g ->
    g · Mor2 Q = Mor2 P · h -> MorphismPairIsomorphism P Q
    := λ r s, (f,,g,,h,,(r,,!r),,(s,,!s)).
End def_morphismpair.

(** * MorphismPair and opposite categories *)
Section MorphismPair_opp.

  Definition MorphismPair_opp {C : precategory} (MP : @MorphismPair C) :
    @MorphismPair (opp_precat C).
  Proof.
    use mk_MorphismPair.
    - exact (Ob3 MP).
    - exact (Ob2 MP).
    - exact (Ob1 MP).
    - exact (Mor2 MP).
    - exact (Mor1 MP).
  Defined.

  Definition opp_MorphismPair {C : precategory} (MP : @MorphismPair (opp_precat C)) :
    @MorphismPair C.
  Proof.
    exact (MorphismPair_opp MP).
  Defined.

  Definition applyFunctorToPair {M N:precategory} :
    (M⟶N) -> @MorphismPair M -> @MorphismPair N
    := λ F P, mk_MorphismPair (# F (Mor1 P)) (# F (Mor2 P)).
  Definition applyFunctorToPairIsomorphism {M N:precategory}
             (F : M⟶N) (P Q : @MorphismPair M) :
    MorphismPairIsomorphism P Q ->
    MorphismPairIsomorphism (applyFunctorToPair F P) (applyFunctorToPair F Q).
  Proof.
    intros [i1 [i2 [i3 [[d d'][e e']]]]].
    exists (functor_on_z_iso F i1).
    exists (functor_on_z_iso F i2).
    exists (functor_on_z_iso F i3).
    repeat split.
    - refine (! _ @ (maponpaths (# F) d ) @ _);apply functor_comp.
    - refine (! _ @ (maponpaths (# F) d') @ _);apply functor_comp.
    - refine (! _ @ (maponpaths (# F) e ) @ _);apply functor_comp.
    - refine (! _ @ (maponpaths (# F) e') @ _);apply functor_comp.
  Defined.
  Definition opp_MorphismPairIsomorphism {M:precategory} {P Q: @MorphismPair M} :
    MorphismPairIsomorphism P Q -> MorphismPairIsomorphism (MorphismPair_opp Q) (MorphismPair_opp P)
    := λ f, opp_z_iso (pr122 f),,
            opp_z_iso (pr12 f),,
            opp_z_iso (pr1 f),,
            (pr22 (pr222 f),,pr12 (pr222 f)),,
            (pr21 (pr222 f),,pr11 (pr222 f)).

End MorphismPair_opp.


(** * ShortShortExactData *)
Section def_shortshortexactdata.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.
  Variable Z : Zero C.

  (** ** Data for [ShortShortExact]
    A pair of morphism such that composition of the morphisms is the zero
    morphism. *)

  Definition ShortShortExactData : UU :=
    ∑ MP : MorphismPair, Mor1 MP · Mor2 MP = ZeroArrow Z _ _.

  Definition mk_ShortShortExactData (MP : MorphismPair)
             (H : Mor1 MP · Mor2 MP = ZeroArrow Z _ _) : ShortShortExactData := tpair _ MP H.

  (** Accessor functions *)
  Definition ShortShortExactData_MorphismPair (SSED : ShortShortExactData) :
    MorphismPair := pr1 SSED.
  Coercion ShortShortExactData_MorphismPair : ShortShortExactData >-> MorphismPair.

  Definition ShortShortExactData_Eq (SSED : ShortShortExactData) :
    (Mor1 SSED) · (Mor2 SSED) = ZeroArrow Z _ _ := pr2 SSED.

End def_shortshortexactdata.
Arguments mk_ShortShortExactData [C] _ _ _.
Arguments ShortShortExactData_Eq [C] _ _.


(** * ShortShortExactData and opposite categories *)
Section shortshortexactdata_opp.

  Lemma opp_ShortShortExactData_Eq {C : precategory} {Z : Zero C}
             (SSED : ShortShortExactData (opp_precat C) (Zero_opp C Z)) :
    Mor1 (opp_MorphismPair SSED) · Mor2 (opp_MorphismPair SSED) =
    ZeroArrow Z (Ob1 (opp_MorphismPair SSED)) (Ob3 (opp_MorphismPair SSED)).
  Proof.
    use (pathscomp0 (@ShortShortExactData_Eq (opp_precat C) (Zero_opp C Z) SSED)).
    rewrite <- ZeroArrow_opp. apply idpath.
  Qed.

  Definition opp_ShortShortExactData {C : precategory} {Z : Zero C}
             (SSED : ShortShortExactData (opp_precat C) (Zero_opp C Z)) : ShortShortExactData C Z.
  Proof.
    use mk_ShortShortExactData.
    - exact (opp_MorphismPair SSED).
    - exact (opp_ShortShortExactData_Eq SSED).
  Defined.

  Lemma ShortShortExactData_opp_Eq {C : precategory} {Z : Zero C}
        (SSED : ShortShortExactData C Z) :
    Mor1 (MorphismPair_opp SSED) · Mor2 (MorphismPair_opp SSED) =
    ZeroArrow (Zero_opp C Z) (Ob1 (MorphismPair_opp SSED)) (Ob3 (MorphismPair_opp SSED)).
  Proof.
    use (pathscomp0 (@ShortShortExactData_Eq C Z SSED)).
    rewrite <- ZeroArrow_opp. apply idpath.
  Qed.

  Definition ShortShortExactData_opp {C : precategory} {Z : Zero C}
             (SSED : ShortShortExactData C Z) : ShortShortExactData (opp_precat C) (Zero_opp C Z).
  Proof.
    use mk_ShortShortExactData.
    - exact (MorphismPair_opp SSED).
    - exact (ShortShortExactData_opp_Eq SSED).
  Defined.

End shortshortexactdata_opp.
