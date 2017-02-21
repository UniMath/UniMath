(** * Some general constructions *)
(** ** Contensts
- Pair of morphisms
- Short exact sequence data
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.opp_precat.

Require Import UniMath.CategoryTheory.limits.zero.
Require Import UniMath.CategoryTheory.limits.Opp.

(** * Pair of morphisms *)
Section def_morphismpair.

  Variable C : precategory.

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

  Definition MPMors1 {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2) : Ob1 MP1 --> Ob1 MP2 :=
    dirprod_pr1 MPM.

  Definition MPMors2 {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2) : Ob2 MP1 --> Ob2 MP2 :=
    dirprod_pr1 (dirprod_pr2 MPM).

  Definition MPMors3 {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2) : Ob3 MP1 --> Ob3 MP2 :=
    dirprod_pr2 (dirprod_pr2 MPM).

  Definition MPMorComms {MP1 MP2 : MorphismPair} (MPM : MPMorMors MP1 MP2) : UU :=
    (MPMors1 MPM ;; Mor1 MP2 = Mor1 MP1 ;; MPMors2 MPM)
      × (MPMors2 MPM ;; Mor2 MP2 = Mor2 MP1 ;; MPMors3 MPM).

  Definition MPComm1 {MP1 MP2 : MorphismPair} {MPM : MPMorMors MP1 MP2} (MPMC : MPMorComms MPM) :
    MPMors1 MPM ;; Mor1 MP2 = Mor1 MP1 ;; MPMors2 MPM := dirprod_pr1 MPMC.

  Definition MPComm2 {MP1 MP2 : MorphismPair} {MPM : MPMorMors MP1 MP2} (MPMC : MPMorComms MPM) :
    MPMors2 MPM ;; Mor2 MP2 = Mor2 MP1 ;; MPMors3 MPM := dirprod_pr2 MPMC.

  Definition MPMorphism (MP1 MP2 : MorphismPair) : UU := ∑ MPM : MPMorMors MP1 MP2, MPMorComms MPM.

  Definition MPMorphism_MPMorMors {MP1 MP2 : MorphismPair} (MPM : MPMorphism MP1 MP2) :
    MPMorMors MP1 MP2 := pr1 MPM.
  Coercion MPMorphism_MPMorMors : MPMorphism >-> MPMorMors.

  Definition MPMorphism_MPMorComms {MP1 MP2 : MorphismPair} (MPM : MPMorphism MP1 MP2) :
    MPMorComms MPM := pr2 MPM.
  Coercion MPMorphism_MPMorComms : MPMorphism >-> MPMorComms.

End def_morphismpair.
Arguments mk_MorphismPair [C] [a] [b] [c] _ _.
Arguments Ob1 [C] _.
Arguments Ob2 [C] _.
Arguments Ob3 [C] _.
Arguments Mor1 [C] _.
Arguments Mor2 [C] _.


(** * MorphismPair and opposite categories *)
Section MorphismPair_opp.

  Definition MorphismPair_opp {C : precategory} (MP : MorphismPair C) : MorphismPair (opp_precat C).
  Proof.
    use mk_MorphismPair.
    - exact (Ob3 MP).
    - exact (Ob2 MP).
    - exact (Ob1 MP).
    - exact (Mor2 MP).
    - exact (Mor1 MP).
  Defined.

  Definition opp_MorphismPair {C : precategory} (MP : MorphismPair (opp_precat C)) : MorphismPair C.
  Proof.
    use mk_MorphismPair.
    - exact (Ob3 MP).
    - exact (Ob2 MP).
    - exact (Ob1 MP).
    - exact (Mor2 MP).
    - exact (Mor1 MP).
  Defined.

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
    ∑ MP : MorphismPair C, Mor1 MP ;; Mor2 MP = ZeroArrow Z _ _.

  Definition mk_ShortShortExactData (MP : MorphismPair C)
             (H : Mor1 MP ;; Mor2 MP = ZeroArrow Z _ _) : ShortShortExactData := tpair _ MP H.

  (** Accessor functions *)
  Definition ShortShortExactData_MorphismPair (SSED : ShortShortExactData) :
    MorphismPair C := pr1 SSED.
  Coercion ShortShortExactData_MorphismPair : ShortShortExactData >-> MorphismPair.

  Definition ShortShortExactData_Eq (SSED : ShortShortExactData) :
    (Mor1 SSED) ;; (Mor2 SSED) = ZeroArrow Z _ _ := pr2 SSED.

End def_shortshortexactdata.
Arguments mk_ShortShortExactData [C] _ _ _.
Arguments ShortShortExactData_Eq [C] _ _.


(** * ShortShortExactData and opposite categories *)
Section shortshortexactdata_opp.

  Lemma opp_ShortShortExactData_Eq {C : precategory} {Z : Zero C}
             (SSED : ShortShortExactData (opp_precat C) (Zero_opp C Z)) :
    Mor1 (opp_MorphismPair SSED) ;; Mor2 (opp_MorphismPair SSED) =
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
    Mor1 (MorphismPair_opp SSED) ;; Mor2 (MorphismPair_opp SSED) =
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
