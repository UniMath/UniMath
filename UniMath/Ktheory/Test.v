(** testing whether our way of doing coproducts fits with SubstitutionSystems  *)

(** ******************************************
Benedikt Ahrens, March 2015
*********************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.

Require Import UniMath.Ktheory.Representation.
Require UniMath.Ktheory.Precategories.


Section interface.

Variable C : category.

Definition isCoproductCocone (a b co : C) (ia : a --> co) (ib : b --> co) :=
  binarySumProperty ia ib.

Definition mk_isCoproductCocone (a b co : C) (ia : a --> co) (ib : b --> co) :
   (∏ (c : C) (f : a --> c) (g : b --> c),
    ∃! k : C ⟦co, c⟧,
      ia · k = f ×
      ib · k = g)
   ->
   isCoproductCocone a b co ia ib.
Proof.
  intros u c fg. refine (iscontrweqf _ (u c (pr1 fg) (pr2 fg))).
  apply weqfibtototal. intro d. apply weqiff.
  { split.
    { intros ee. apply dirprodeq.
      { simpl. exact (pr1 ee). }
      { simpl. exact (pr2 ee). } }
    { intros ee. split.
      { simpl. exact (maponpaths (HomPair_1 _ _ _) ee). }
      { simpl. exact (maponpaths (HomPair_2 _ _ _) ee). } } }
  { apply isapropdirprod; apply (homset_property C). }
  { apply setproperty. }
Defined.

Definition CoproductCocone (a b : C) := BinarySum a b.

Definition mk_CoproductCocone (a b : C) :
  ∏ (c : C) (f : a --> c) (g : b --> c),
    isCoproductCocone _ _ _ f g -> CoproductCocone a b
  := λ c f g i, c,,(f,,g),,i.

Definition Coproducts := BinarySums C.
Definition hasCoproducts (C:category) := ∏ (a b:C), ∥ BinarySum a b ∥.


Definition CoproductObject {a b : C} (CC : CoproductCocone a b) : C :=
  universalObject CC.

Definition CoproductIn1 {a b : C} (CC : CoproductCocone a b): a --> CoproductObject CC
  := in_1 CC.

Definition CoproductIn2 {a b : C} (CC : CoproductCocone a b) : b --> CoproductObject CC
  := in_2 CC.

Definition CoproductArrow {a b : C} (CC : CoproductCocone a b) {c : C} (f : a --> c) (g : b --> c) :
  CoproductObject CC --> c
  := binarySumMap CC f g.

Lemma CoproductIn1Commutes (a b : C) (CC : CoproductCocone a b):
     ∏ (c : C) (f : a --> c) g, CoproductIn1 CC · CoproductArrow CC f g  = f.
Proof.
  intros c f g.
  exact (binarySum_in_1_eqn CC f g).
Qed.

Lemma CoproductIn2Commutes (a b : C) (CC : CoproductCocone a b):
     ∏ (c : C) (f : a --> c) g, CoproductIn2 CC · CoproductArrow CC f g = g.
Proof.
  intros c f g.
  exact (binarySum_in_2_eqn CC f g).
Qed.

Lemma CoproductArrowUnique (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : a --> x) (g : b --> x) (k : CoproductObject CC --> x) :
    CoproductIn1 CC · k = f -> CoproductIn2 CC · k = g ->
      k = CoproductArrow CC f g.
Proof.
  intros u v.
  apply binarySumMapUniqueness.
  { refine (u @ _). apply pathsinv0, CoproductIn1Commutes. }
  { refine (v @ _). apply pathsinv0, CoproductIn2Commutes. }
Qed.

Lemma CoproductArrowEta (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : CoproductObject CC --> x) :
    f = CoproductArrow CC (CoproductIn1 CC · f) (CoproductIn2 CC · f).
Proof.
  apply CoproductArrowUnique;
  apply idpath.
Qed.

Definition CoproductOfArrows {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a --> c) (g : b --> d) :
          CoproductObject CCab --> CoproductObject CCcd :=
    CoproductArrow CCab (f · CoproductIn1 CCcd) (g · CoproductIn2 CCcd).

Lemma CoproductOfArrowsIn1 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a --> c) (g : b --> d) :
    CoproductIn1 CCab · CoproductOfArrows CCab CCcd f g = f · CoproductIn1 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn1Commutes.
Qed.

Lemma CoproductOfArrowsIn2 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a --> c) (g : b --> d) :
    CoproductIn2 CCab · CoproductOfArrows CCab CCcd f g = g · CoproductIn2 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn2Commutes.
Qed.


Lemma precompWithCoproductArrow {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a --> c) (g : b --> d)
    {x : C} (k : c --> x) (h : d --> x) :
        CoproductOfArrows CCab CCcd f g · CoproductArrow CCcd k h =
         CoproductArrow CCab (f · k) (g · h).
Proof.
  apply CoproductArrowUnique.
  - rewrite assoc. rewrite CoproductOfArrowsIn1.
    rewrite <- assoc, CoproductIn1Commutes.
    apply idpath.
  - rewrite assoc, CoproductOfArrowsIn2.
    rewrite <- assoc, CoproductIn2Commutes.
    apply idpath.
Qed.


Lemma postcompWithCoproductArrow {a b : C} (CCab : CoproductCocone a b) {c : C}
    (f : a --> c) (g : b --> c) {x : C} (k : c --> x)  :
       CoproductArrow CCab f g · k = CoproductArrow CCab (f · k) (g · k).
Proof.
  apply CoproductArrowUnique.
  -  rewrite assoc, CoproductIn1Commutes;
     apply idpath.
  -  rewrite assoc, CoproductIn2Commutes;
     apply idpath.
Qed.


Section coproduct_unique.

Hypothesis H : is_univalent C.

Variables a b : C.

Definition from_Coproduct_to_Coproduct (CC CC' : CoproductCocone a b)
  : CoproductObject CC --> CoproductObject CC'.
Proof.
  apply (CoproductArrow CC  (CoproductIn1 _ ) (CoproductIn2 _ )).
Defined.


Lemma Coproduct_endo_is_identity (CC : CoproductCocone a b)
  (k : CoproductObject CC --> CoproductObject CC)
  (H1 : CoproductIn1 CC · k = CoproductIn1 CC)
  (H2 : CoproductIn2 CC · k = CoproductIn2 CC)
  : identity _ = k.
Proof.
(*  apply pathsinv0. *)
(*   apply colim_endo_is_identity. *)
(*   intro u; induction u; simpl; assumption. *)
(* Defined. *)
Abort.

End coproduct_unique.


End interface.

Section def_functor_pointwise_coprod.

Variable C D : category.
Variable HD : Coproducts D.

Definition hsD := homset_property D.

Section coproduct_functor.

Variables F G : functor C D.

Definition Coproducts_functor_precat : Coproducts (functor_category C D).
Proof.
  apply functorBinarySum.
  exact HD.
Defined.

Definition coproduct_functor : functor C D := universalObject (functorBinarySum HD F G).

End coproduct_functor.
End def_functor_pointwise_coprod.
