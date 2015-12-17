
(** ******************************************
Benedikt Ahrens, March 2015
*********************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.

(** * Definition of binary coproduct of objects in a precategory *)

Definition two_graph : graph.
Proof.
  exists bool.
  exact (fun _ _ => empty).
Defined.

Definition coproduct_diagram {C : precategory} (a b : C) : diagram two_graph C.
Proof.
  exists (fun x : bool => if x then a else b).
  intros u v F.
  induction F.
Defined.

Definition CopCocone {C : precategory} {a b : C} {c : C} (ac : a ⇒ c) (bc : b ⇒ c) :
   cocone (coproduct_diagram a b) c.
unshelve refine (tpair _ _ _ ).
+ intro v.
  induction v; simpl.
  - exact ac.
  - exact bc.
+ intros u v e; induction e.
Defined.

Section coproduct_def.

Variable C : precategory.

Definition isCoproductCocone (a b co : C) (ia : a ⇒ co) (ib : b ⇒ co) :=
  isColimCocone (coproduct_diagram a b) co (CopCocone ia ib).

Definition mk_isCoproductCocone (hsC : has_homsets C)(a b co : C) (ia : a ⇒ co) (ib : b ⇒ co) :
   (∀ (c : C) (f : a ⇒ c) (g : b ⇒ c),
    ∃! k : C ⟦co, c⟧,
      ia ;; k = f ×
      ib ;; k = g)
   →
   isCoproductCocone a b co ia ib.
Proof.
  intros H c cc.
  set (H':= H c (coconeIn cc true) (coconeIn cc false)).
  unshelve refine (tpair _ _ _ ).
  - exists (pr1 (pr1 H')).
    set (T := pr2 (pr1 H')). simpl in T.
    abstract (intro u; induction u;
              [ apply (pr1 T) | apply (pr2 T)]).
  - intros. abstract (intros;
              apply subtypeEquality;
              [ intro; apply impred; intro; apply hsC
              | apply path_to_ctr; split; [ apply (pr2 t true) | apply (pr2 t false)] ]).
Defined.

Definition CoproductCocone (a b : C) :=
  ColimCocone (coproduct_diagram a b).

Definition mk_CoproductCocone (a b : C) :
  ∀ (c : C) (f : a ⇒ c) (g : b ⇒ c),
   isCoproductCocone _ _ _ f g →  CoproductCocone a b.
Proof.
  intros.
  unshelve refine (tpair _ _ _ ).
  - exists c.
    apply (CopCocone f g).
  - apply X.
Defined.

Definition Coproducts := ∀ (a b : C), CoproductCocone a b.
Definition hasCoproducts := ishinh Coproducts.

Definition CoproductObject {a b : C} (CC : CoproductCocone a b) : C := colim CC.
Definition CoproductIn1 {a b : C} (CC : CoproductCocone a b): a ⇒ CoproductObject CC
  := colimIn CC true.

Definition CoproductIn2 {a b : C} (CC : CoproductCocone a b) : b ⇒ CoproductObject CC
  := colimIn CC false.

Definition CoproductArrow {a b : C} (CC : CoproductCocone a b) {c : C} (f : a ⇒ c) (g : b ⇒ c) :
      CoproductObject CC ⇒ c.
Proof.
  apply (colimArrow CC).
  unshelve refine (mk_cocone _ _ ).
  + intro v. induction v.
    - apply f.
    - apply g.
  + simpl. intros ? ? e; induction e.
Defined.

Lemma CoproductIn1Commutes (a b : C) (CC : CoproductCocone a b):
     ∀ (c : C) (f : a ⇒ c) g, CoproductIn1 CC ;; CoproductArrow CC f g  = f.
Proof.
  intros c f g.
  unfold CoproductIn1.
  set (H:=colimArrowCommutes CC  _ (CopCocone f g) true).
  apply H.
Qed.

Lemma CoproductIn2Commutes (a b : C) (CC : CoproductCocone a b):
     ∀ (c : C) (f : a ⇒ c) g, CoproductIn2 CC ;; CoproductArrow CC f g = g.
Proof.
  intros c f g.
  unfold CoproductIn1.
  set (H:=colimArrowCommutes CC  _ (CopCocone f g) false).
  apply H.
Qed.

Lemma CoproductArrowUnique (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : a ⇒ x) (g : b ⇒ x) (k : CoproductObject CC ⇒ x) :
    CoproductIn1 CC ;; k = f → CoproductIn2 CC ;; k = g →
      k = CoproductArrow CC f g.
Proof.
  intros H1 H2.
  apply colimArrowUnique.
  simpl. intro u; induction u; simpl.
  - apply H1.
  - apply H2.
Qed.


Lemma CoproductArrowEta (a b : C) (CC : CoproductCocone a b) (x : C)
    (f : CoproductObject CC ⇒ x) :
    f = CoproductArrow CC (CoproductIn1 CC ;; f) (CoproductIn2 CC ;; f).
Proof.
  apply CoproductArrowUnique;
  apply idpath.
Qed.


Definition CoproductOfArrows {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) :
          CoproductObject CCab ⇒ CoproductObject CCcd :=
    CoproductArrow CCab (f ;; CoproductIn1 CCcd) (g ;; CoproductIn2 CCcd).

Lemma CoproductOfArrowsIn1 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) :
    CoproductIn1 CCab ;; CoproductOfArrows CCab CCcd f g = f ;; CoproductIn1 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn1Commutes.
Qed.

Lemma CoproductOfArrowsIn2 {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d) :
    CoproductIn2 CCab ;; CoproductOfArrows CCab CCcd f g = g ;; CoproductIn2 CCcd.
Proof.
  unfold CoproductOfArrows.
  apply CoproductIn2Commutes.
Qed.


Lemma precompWithCoproductArrow {a b : C} (CCab : CoproductCocone a b) {c d : C}
    (CCcd : CoproductCocone c d) (f : a ⇒ c) (g : b ⇒ d)
    {x : C} (k : c ⇒ x) (h : d ⇒ x) :
        CoproductOfArrows CCab CCcd f g ;; CoproductArrow CCcd k h =
         CoproductArrow CCab (f ;; k) (g ;; h).
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
    (f : a ⇒ c) (g : b ⇒ c) {x : C} (k : c ⇒ x)  :
       CoproductArrow CCab f g ;; k = CoproductArrow CCab (f ;; k) (g ;; k).
Proof.
  apply CoproductArrowUnique.
  -  rewrite assoc, CoproductIn1Commutes;
     apply idpath.
  -  rewrite assoc, CoproductIn2Commutes;
     apply idpath.
Qed.


(** * Proof that coproducts are unique when the precategory [C] is a category *)

Section coproduct_unique.

Hypothesis H : is_category C.

Variables a b : C.

Definition from_Coproduct_to_Coproduct (CC CC' : CoproductCocone a b)
  : CoproductObject CC ⇒ CoproductObject CC'.
Proof.
  apply (CoproductArrow CC  (CoproductIn1 _ ) (CoproductIn2 _ )).
Defined.


Lemma Coproduct_endo_is_identity (CC : CoproductCocone a b)
  (k : CoproductObject CC ⇒ CoproductObject CC)
  (H1 : CoproductIn1 CC ;; k = CoproductIn1 CC)
  (H2 : CoproductIn2 CC ;; k = CoproductIn2 CC)
  : identity _ = k.
Proof.
(*  apply pathsinv0. *)
  apply colim_endo_is_identity.
  intro u; induction u; simpl; assumption.
Defined.


Lemma is_iso_from_Coproduct_to_Coproduct (CC CC' : CoproductCocone a b)
  : is_iso (from_Coproduct_to_Coproduct CC CC').
Proof.
  apply is_iso_from_is_z_iso.
  exists (from_Coproduct_to_Coproduct CC' CC).
  split; simpl.
  - apply pathsinv0.
    apply Coproduct_endo_is_identity.
    + rewrite assoc. unfold from_Coproduct_to_Coproduct.
      rewrite CoproductIn1Commutes.
      rewrite CoproductIn1Commutes.
      apply idpath.
    + rewrite assoc. unfold from_Coproduct_to_Coproduct.
      rewrite CoproductIn2Commutes.
      rewrite CoproductIn2Commutes.
      apply idpath.
  - apply pathsinv0.
    apply Coproduct_endo_is_identity.
    + rewrite assoc; unfold from_Coproduct_to_Coproduct.
      repeat rewrite CoproductIn1Commutes; apply idpath.
    + rewrite assoc; unfold from_Coproduct_to_Coproduct.
      repeat rewrite CoproductIn2Commutes; apply idpath.
Defined.

Definition iso_from_Coproduct_to_Coproduct (CC CC' : CoproductCocone a b)
  : iso (CoproductObject CC) (CoproductObject CC')
  := isopair _ (is_iso_from_Coproduct_to_Coproduct CC CC').

Lemma transportf_isotoid' (c d d': C) (p : iso d d') (f : c ⇒ d) :
  transportf (λ a0 : C, c ⇒ a0) (isotoid C H p) f = f ;; p .
Proof.
  rewrite <- idtoiso_postcompose.
  rewrite idtoiso_isotoid.
  apply idpath.
Defined.


(* should be an instance of a lemma about colimits *)
(*
Lemma isaprop_CoproductCocone : isaprop (CoproductCocone a b).
Proof.
  apply invproofirrelevance.
  intros CC CC'.
  apply subtypeEquality.
  + intros.
    unfold isColimCocone.
    do 2 (apply impred; intro); apply isapropiscontr.
  + apply (total2_paths (isotoid _ H (iso_from_Coproduct_to_Coproduct CC CC'))).
    rewrite transportf_dirprod.
    rewrite transportf_isotoid'. simpl.
    rewrite transportf_isotoid'.
    destruct CC as [CC bla].
    destruct CC' as [CC' bla']; simpl in *.
    destruct CC as [CC [CC1 CC2]].
    destruct CC' as [CC' [CC1' CC2']]; simpl in *.
    unfold from_Coproduct_to_Coproduct.
    rewrite CoproductIn1Commutes.
    rewrite CoproductIn2Commutes.
    apply idpath.
Qed.
*)

End coproduct_unique.
End coproduct_def.

Lemma Coproducts_from_Colims (C : precategory) :
  Colims C -> Coproducts C.
Proof.
now intros H a b; apply H.
Defined.
