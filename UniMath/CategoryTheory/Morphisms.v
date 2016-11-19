(** * Some general constructions *)
(** ** Contensts
- Pair of morphisms
- Short exact sequence data
*)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import UniMath.CategoryTheory.limits.zero.


(** * Pair of morphisms *)
Section def_morphismpair.

  Variable C : precategory.

  Definition MorphismPair : UU := Σ (a b c : C), (a --> b × b --> c).

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

End def_morphismpair.
Arguments mk_MorphismPair [C] [a] [b] [c] _ _.
Arguments Ob1 [C] _.
Arguments Ob2 [C] _.
Arguments Ob3 [C] _.
Arguments Mor1 [C] _.
Arguments Mor2 [C] _.

(** * ShortShortExactData *)
Section def_shortshortexactdata.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.
  Variable Z : Zero C.

  (** ** Data for [ShortShortExact]
    A pair of morphism such that composition of the morphisms is the zero
    morphism. *)

  Definition ShortShortExactData : UU :=
    Σ MP : MorphismPair C, Mor1 MP ;; Mor2 MP = ZeroArrow Z _ _.

  Definition mk_ShortShortExactData (MP : MorphismPair C)
             (H : Mor1 MP ;; Mor2 MP = ZeroArrow Z _ _) : ShortShortExactData.
  Proof.
    use tpair.
    - exact MP.
    - exact H.
  Defined.

  (** Accessor functions *)
  Definition ShortShortExactData_MorphismPair (SSED : ShortShortExactData) :
    MorphismPair C := pr1 SSED.
  Coercion ShortShortExactData_MorphismPair : ShortShortExactData >-> MorphismPair.

  Definition ShortShortExactData_Eq (SSED : ShortShortExactData) :
    (Mor1 SSED) ;; (Mor2 SSED) = ZeroArrow Z _ _ := pr2 SSED.

End def_shortshortexactdata.
Arguments mk_ShortShortExactData [C] _ _ _.
Arguments ShortShortExactData_Eq [C] _ _.
