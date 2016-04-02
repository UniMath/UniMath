Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").

Section product_def.

Variable (C : precategory).

Definition two_graph : graph.
Proof.
  exists bool.
  exact (fun _ _ => empty).
Defined.

Definition product_diagram (a b : C) : diagram two_graph C^op.
Proof.
  exists (fun x : bool => if x then a else b).
  intros u v F.
  induction F.
Defined.

Definition ProdCone {a b c : C} (ca : C⟦c,a⟧) (cb : C⟦c,b⟧) :
  cone (product_diagram a b) c.
Proof.
simple refine (tpair _ _ _); simpl.
- intro v; induction v.
  + exact ca.
  + exact cb.
- intros u v e; induction e.
Defined.

Definition isProductCone (c d p : C) (p1 : C⟦p,c⟧) (p2 : C⟦p,d⟧) :=
  isLimCone (product_diagram c d) p (ProdCone p1 p2).

Definition mk_isProductCone (hsC : has_homsets C) (a b p : C)
  (pa : C⟦p,a⟧) (pb : C⟦p,b⟧) :
  (∀ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
    ∃! k : C⟦c,p⟧, k ;; pa = f × k ;; pb = g) ->
  isProductCone a b p pa pb.
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

Definition ProductCone (a b : C) := LimCone (product_diagram a b).

Definition mk_ProductCone (a b : C) :
  ∀ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
   isProductCone _ _ _ f g -> ProductCone a b.
Proof.
  intros.
  simple refine (tpair _ _ _ ).
  - exists c.
    apply (ProdCone f g).
  - apply X.
Defined.

Definition Products := forall (a b : C), ProductCone a b.

(* What is the best definition of this? *)
(* Definition hasProducts (C : precategory) := ishinh (Products C). *)

Definition ProductObject {c d : C} (P : ProductCone c d) : C := lim P.
Definition ProductPr1 {c d : C} (P : ProductCone c d): C⟦ProductObject P,c⟧ :=
  limOut P true.

Definition ProductPr2 {c d : C} (P : ProductCone c d) : C⟦ProductObject P,d⟧ :=
   limOut P false.

(* Definition isProductCone_ProductCone {c d : C} (P : ProductCone c d) :  *)
(*    isProductCone c d (ProductObject P) (ProductPr1 P) (ProductPr2 P). *)

Definition ProductArrow {a b : C} (P : ProductCone a b) {c : C}
  (f : C⟦c,a⟧) (g : C⟦c,b⟧) : C⟦c,ProductObject P⟧.
Proof.
apply (limArrow P).
simple refine (mk_cone _ _).
- intro v; induction v; [ apply f | apply g ].
- intros ? ? e; induction e. (* <- should not be opaque! otherwise ProductPr1Commutes doesn't work *)
Defined.

Lemma ProductPr1Commutes (a b : C) (P : ProductCone a b):
     forall (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧), ProductArrow P f g ;; ProductPr1 P = f.
Proof.
intros c f g.
apply (limArrowCommutes P c (ProdCone f g) true).
Qed.

Lemma ProductPr2Commutes (a b : C) (P : ProductCone a b):
     forall (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧), ProductArrow P f g ;; ProductPr2 P = g.
Proof.
intros c f g.
apply (limArrowCommutes P c (ProdCone f g) false).
Qed.

Lemma ProductArrowUnique (a b : C) (P : ProductCone a b) (c : C)
    (f : C⟦c,a⟧) (g : C⟦c,b⟧) (k : C⟦c,ProductObject P⟧) :
    k ;; ProductPr1 P = f -> k ;; ProductPr2 P = g ->
      k = ProductArrow P f g.
Proof.
intros H1 H2.
refine (limArrowUnique _ _ _ _ _); simpl.
now intro u; induction u; simpl; [ apply H1 | apply H2 ].
Qed.

Lemma ProductArrowEta (a b : C) (P : ProductCone a b) (c : C)
    (f : C⟦c,ProductObject P⟧) :
    f = ProductArrow P (f ;; ProductPr1 P) (f ;; ProductPr2 P).
Proof.
now apply ProductArrowUnique.
Qed.

Definition ProductOfArrows {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : C⟦a,c⟧) (g : C⟦b,d⟧) :
          C⟦ProductObject Pab,ProductObject Pcd⟧ :=
    ProductArrow Pcd (ProductPr1 Pab ;; f) (ProductPr2 Pab ;; g).

Lemma ProductOfArrowsPr1 {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : C⟦a,c⟧) (g : C⟦b,d⟧) :
    ProductOfArrows Pcd Pab f g ;; ProductPr1 Pcd = ProductPr1 Pab ;; f.
Proof.
now apply ProductPr1Commutes.
Qed.

Lemma ProductOfArrowsPr2 {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : C⟦a,c⟧) (g : C⟦b,d⟧) :
    ProductOfArrows Pcd Pab f g ;; ProductPr2 Pcd = ProductPr2 Pab ;; g.
Proof.
now apply ProductPr2Commutes.
Qed.

Lemma postcompWithProductArrow {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : C⟦a,c⟧) (g : C⟦b,d⟧)
    {x : C} (k : C⟦x,a⟧) (h : C⟦x,b⟧) :
        ProductArrow Pab k h ;; ProductOfArrows Pcd Pab f g =
         ProductArrow Pcd (k ;; f) (h ;; g).
Proof.
apply ProductArrowUnique.
- now rewrite <- assoc, ProductOfArrowsPr1, assoc, ProductPr1Commutes.
- now rewrite <- assoc, ProductOfArrowsPr2, assoc, ProductPr2Commutes.
Qed.

Lemma precompWithProductArrow {c d : C} (Pcd : ProductCone c d) {a : C}
    (f : C⟦a,c⟧) (g : C⟦a,d⟧) {x : C} (k : C⟦x,a⟧)  :
       k ;; ProductArrow Pcd f g  = ProductArrow Pcd (k ;; f) (k ;; g).
Proof.
apply ProductArrowUnique.
- now rewrite <- assoc, ProductPr1Commutes.
- now rewrite <- assoc, ProductPr2Commutes.
Qed.

End product_def.

Lemma Products_from_Lims (C : precategory) :
  Lims C -> Products C.
Proof.
now intros H a b; apply H.
Defined.
