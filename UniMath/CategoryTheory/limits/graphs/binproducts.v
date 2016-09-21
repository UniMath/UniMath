(** Binary products via limits *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Section binproduct_def.

Variable (C : precategory).

Definition two_graph : graph.
Proof.
  exists bool.
  exact (fun _ _ => empty).
Defined.

Definition binproduct_diagram (a b : C) : diagram two_graph C.
Proof.
  exists (fun x : bool => if x then a else b).
  intros u v F.
  induction F.
Defined.

Definition ProdCone {a b c : C} (ca : C⟦c,a⟧) (cb : C⟦c,b⟧) :
  cone (binproduct_diagram a b) c.
Proof.
simple refine (tpair _ _ _); simpl.
- intro v; induction v.
  + exact ca.
  + exact cb.
- intros u v e; induction e.
Defined.

Definition isBinProductCone (c d p : C) (p1 : C⟦p,c⟧) (p2 : C⟦p,d⟧) :=
  isLimCone (binproduct_diagram c d) p (ProdCone p1 p2).

Definition mk_isBinProductCone (hsC : has_homsets C) (a b p : C)
  (pa : C⟦p,a⟧) (pb : C⟦p,b⟧) :
  (Π (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
    ∃! k : C⟦c,p⟧, k ;; pa = f × k ;; pb = g) ->
  isBinProductCone a b p pa pb.
Proof.
intros H c cc.
simpl in *.
set (H' := H c (coneOut cc true) (coneOut cc false)).
unshelve refine (tpair _ _ _).
- exists (pr1 (pr1 H')).
  set (T := pr2 (pr1 H')); simpl in T.
  abstract (intro u; induction u; simpl; [exact (pr1 T)|exact (pr2 T)]).
- abstract (intros; apply subtypeEquality;
              [intro; apply impred;intro; apply hsC|]; simpl;
            apply path_to_ctr; split; [ apply (pr2 t true) | apply (pr2 t false) ]).
Defined.

Definition BinProductCone (a b : C) := LimCone (binproduct_diagram a b).

Definition mk_BinProductCone (a b : C) :
  Π (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
   isBinProductCone _ _ _ f g -> BinProductCone a b.
Proof.
  intros.
  simple refine (tpair _ _ _ ).
  - exists c.
    apply (ProdCone f g).
  - apply X.
Defined.

Definition BinProducts := Π (a b : C), BinProductCone a b.

(* What is the best definition of this? *)
(* Definition hasBinProducts (C : precategory) := ishinh (BinProducts C). *)

Definition BinProductObject {c d : C} (P : BinProductCone c d) : C := lim P.
Definition BinProductPr1 {c d : C} (P : BinProductCone c d): C⟦BinProductObject P,c⟧ :=
  limOut P true.

Definition BinProductPr2 {c d : C} (P : BinProductCone c d) : C⟦BinProductObject P,d⟧ :=
   limOut P false.

(* Definition isBinProductCone_BinProductCone {c d : C} (P : BinProductCone c d) :  *)
(*    isBinProductCone c d (BinProductObject P) (BinProductPr1 P) (BinProductPr2 P). *)

Definition BinProductArrow {a b : C} (P : BinProductCone a b) {c : C}
  (f : C⟦c,a⟧) (g : C⟦c,b⟧) : C⟦c,BinProductObject P⟧.
Proof.
apply (limArrow P).
simple refine (mk_cone _ _).
- intro v; induction v; [ apply f | apply g ].
- intros ? ? e; induction e. (* <- should not be opaque! otherwise BinProductPr1Commutes doesn't work *)
Defined.

Lemma BinProductPr1Commutes (a b : C) (P : BinProductCone a b):
     Π (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧), BinProductArrow P f g ;; BinProductPr1 P = f.
Proof.
intros c f g.
apply (limArrowCommutes P c (ProdCone f g) true).
Qed.

Lemma BinProductPr2Commutes (a b : C) (P : BinProductCone a b):
     Π (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧), BinProductArrow P f g ;; BinProductPr2 P = g.
Proof.
intros c f g.
apply (limArrowCommutes P c (ProdCone f g) false).
Qed.

Lemma BinProductArrowUnique (a b : C) (P : BinProductCone a b) (c : C)
    (f : C⟦c,a⟧) (g : C⟦c,b⟧) (k : C⟦c,BinProductObject P⟧) :
    k ;; BinProductPr1 P = f -> k ;; BinProductPr2 P = g ->
      k = BinProductArrow P f g.
Proof.
intros H1 H2.
refine (limArrowUnique _ _ _ _ _); simpl.
now intro u; induction u; simpl; [ apply H1 | apply H2 ].
Qed.

Lemma BinProductArrowEta (a b : C) (P : BinProductCone a b) (c : C)
    (f : C⟦c,BinProductObject P⟧) :
    f = BinProductArrow P (f ;; BinProductPr1 P) (f ;; BinProductPr2 P).
Proof.
now apply BinProductArrowUnique.
Qed.

Definition BinProductOfArrows {c d : C} (Pcd : BinProductCone c d) {a b : C}
    (Pab : BinProductCone a b) (f : C⟦a,c⟧) (g : C⟦b,d⟧) :
          C⟦BinProductObject Pab,BinProductObject Pcd⟧ :=
    BinProductArrow Pcd (BinProductPr1 Pab ;; f) (BinProductPr2 Pab ;; g).

Lemma BinProductOfArrowsPr1 {c d : C} (Pcd : BinProductCone c d) {a b : C}
    (Pab : BinProductCone a b) (f : C⟦a,c⟧) (g : C⟦b,d⟧) :
    BinProductOfArrows Pcd Pab f g ;; BinProductPr1 Pcd = BinProductPr1 Pab ;; f.
Proof.
now apply BinProductPr1Commutes.
Qed.

Lemma BinProductOfArrowsPr2 {c d : C} (Pcd : BinProductCone c d) {a b : C}
    (Pab : BinProductCone a b) (f : C⟦a,c⟧) (g : C⟦b,d⟧) :
    BinProductOfArrows Pcd Pab f g ;; BinProductPr2 Pcd = BinProductPr2 Pab ;; g.
Proof.
now apply BinProductPr2Commutes.
Qed.

Lemma postcompWithBinProductArrow {c d : C} (Pcd : BinProductCone c d) {a b : C}
    (Pab : BinProductCone a b) (f : C⟦a,c⟧) (g : C⟦b,d⟧)
    {x : C} (k : C⟦x,a⟧) (h : C⟦x,b⟧) :
        BinProductArrow Pab k h ;; BinProductOfArrows Pcd Pab f g =
         BinProductArrow Pcd (k ;; f) (h ;; g).
Proof.
apply BinProductArrowUnique.
- now rewrite <- assoc, BinProductOfArrowsPr1, assoc, BinProductPr1Commutes.
- now rewrite <- assoc, BinProductOfArrowsPr2, assoc, BinProductPr2Commutes.
Qed.

Lemma precompWithBinProductArrow {c d : C} (Pcd : BinProductCone c d) {a : C}
    (f : C⟦a,c⟧) (g : C⟦a,d⟧) {x : C} (k : C⟦x,a⟧)  :
       k ;; BinProductArrow Pcd f g  = BinProductArrow Pcd (k ;; f) (k ;; g).
Proof.
apply BinProductArrowUnique.
- now rewrite <- assoc, BinProductPr1Commutes.
- now rewrite <- assoc, BinProductPr2Commutes.
Qed.

End binproduct_def.

Lemma BinProducts_from_Lims (C : precategory) :
  Lims C -> BinProducts C.
Proof.
now intros H a b; apply H.
Defined.
