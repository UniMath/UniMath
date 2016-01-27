Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.colimits.colimits.
Require Import UniMath.CategoryTheory.limits.limits.
Require Import UniMath.CategoryTheory.opp_precat.

Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op").
Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).

Section product_def.

Variable C : precategory.

Definition isProductCone (c d p: C) (p1 : p --> c) (p2 : p --> d) :=
  forall (a : C) (f : a --> c) (g : a --> d),
    iscontr (total2 (fun fg : a --> p => dirprod (fg ;; p1 = f)
                                                 (fg ;; p2 = g))).

Definition ProductCone (c d : C) :=
   total2 (fun pp1p2 : total2 (fun p : C => dirprod (p --> c) (p --> d)) =>
             isProductCone c d (pr1 pp1p2) (pr1 (pr2 pp1p2)) (pr2 (pr2 pp1p2))).


Definition Products := forall (c d : C), ProductCone c d.
Definition hasProducts := ishinh Products.

Definition ProductObject {c d : C} (P : ProductCone c d) : C := pr1 (pr1 P).
Definition ProductPr1 {c d : C} (P : ProductCone c d): ProductObject P --> c :=
  pr1 (pr2 (pr1 P)).
Definition ProductPr2 {c d : C} (P : ProductCone c d) : ProductObject P --> d :=
   pr2 (pr2 (pr1 P)).

Definition isProductCone_ProductCone {c d : C} (P : ProductCone c d) :
   isProductCone c d (ProductObject P) (ProductPr1 P) (ProductPr2 P).
Proof.
  exact (pr2 P).
Defined.

Definition ProductArrow {c d : C} (P : ProductCone c d) {a : C} (f : a --> c) (g : a --> d) :
       a --> ProductObject P.
Proof.
  exact (pr1 (pr1 (isProductCone_ProductCone P _ f g))).
Defined.

Lemma ProductPr1Commutes (c d : C) (P : ProductCone c d):
     forall (a : C) (f : a --> c) g, ProductArrow P f g ;; ProductPr1 P = f.
Proof.
  intros a f g.
  exact (pr1 (pr2 (pr1 (isProductCone_ProductCone P _ f g)))).
Qed.

Lemma ProductPr2Commutes (c d : C) (P : ProductCone c d):
     forall (a : C) (f : a --> c) g, ProductArrow P f g ;; ProductPr2 P = g.
Proof.
  intros a f g.
  exact (pr2 (pr2 (pr1 (isProductCone_ProductCone P _ f g)))).
Qed.

Lemma ProductArrowUnique (c d : C) (P : ProductCone c d) (x : C)
    (f : x --> c) (g : x --> d) (k : x --> ProductObject P) :
    k ;; ProductPr1 P = f -> k ;; ProductPr2 P = g ->
      k = ProductArrow P f g.
Proof.
  intros H1 H2.
  set (H := tpair (fun h => dirprod _ _ ) k (dirprodpair H1 H2)).
  set (H' := (pr2 (isProductCone_ProductCone P _ f g)) H).
  apply (base_paths _ _ H').
Qed.


Definition mk_ProductCone (a b : C) :
  ∀ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
   isProductCone _ _ _ f g -> ProductCone a b.
Proof.
  intros.
  simple refine (tpair _ _ _ ).
  - exists c.
    exists f.
    exact g.
  - exact X.
Defined.

Definition mk_isProductCone (hsC : has_homsets C) (a b p : C)
  (pa : C⟦p,a⟧) (pb : C⟦p,b⟧) :
  (∀ (c : C) (f : C⟦c,a⟧) (g : C⟦c,b⟧),
    ∃! k : C⟦c,p⟧, k ;; pa = f × k ;; pb = g) ->
  isProductCone a b p pa pb.
Proof.
  intros H c cc g.
  apply H.
Defined.

Lemma ProductArrowEta (c d : C) (P : ProductCone c d) (x : C)
    (f : x --> ProductObject P) :
    f = ProductArrow P (f ;; ProductPr1 P) (f ;; ProductPr2 P).
Proof.
  apply ProductArrowUnique;
  apply idpath.
Qed.


Definition ProductOfArrows {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d) :
          ProductObject Pab --> ProductObject Pcd :=
    ProductArrow Pcd (ProductPr1 Pab ;; f) (ProductPr2 Pab ;; g).

Lemma ProductOfArrowsPr1 {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d) :
    ProductOfArrows Pcd Pab f g ;; ProductPr1 Pcd = ProductPr1 Pab ;; f.
Proof.
  unfold ProductOfArrows.
  rewrite ProductPr1Commutes.
  apply idpath.
Qed.

Lemma ProductOfArrowsPr2 {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d) :
    ProductOfArrows Pcd Pab f g ;; ProductPr2 Pcd = ProductPr2 Pab ;; g.
Proof.
  unfold ProductOfArrows.
  rewrite ProductPr2Commutes.
  apply idpath.
Qed.


Lemma postcompWithProductArrow {c d : C} (Pcd : ProductCone c d) {a b : C}
    (Pab : ProductCone a b) (f : a --> c) (g : b --> d)
    {x : C} (k : x --> a) (h : x --> b) :
        ProductArrow Pab k h ;; ProductOfArrows Pcd Pab f g =
         ProductArrow Pcd (k ;; f) (h ;; g).
Proof.
  apply ProductArrowUnique.
  - rewrite <- assoc, ProductOfArrowsPr1.
    rewrite assoc, ProductPr1Commutes.
    apply idpath.
  - rewrite <- assoc, ProductOfArrowsPr2.
    rewrite assoc, ProductPr2Commutes.
    apply idpath.
Qed.


Lemma precompWithProductArrow {c d : C} (Pcd : ProductCone c d) {a : C}
    (f : a --> c) (g : a --> d) {x : C} (k : x --> a)  :
       k ;; ProductArrow Pcd f g  = ProductArrow Pcd (k ;; f) (k ;; g).
Proof.
  apply ProductArrowUnique.
  -  rewrite <- assoc, ProductPr1Commutes;
     apply idpath.
  -  rewrite <- assoc, ProductPr2Commutes;
     apply idpath.
Qed.

End product_def.


Section Products.

Variable C : precategory.
Variable CC : Products C.
Variables a b c d x y : C.

Definition ProductOfArrows_comp (f : a ⇒ c) (f' : b ⇒ d) (g : c ⇒ x) (g' : d ⇒ y)
  : ProductOfArrows _ (CC c d) (CC a b) f f' ;;
    ProductOfArrows _ (CC _ _) (CC _ _) g g'
    =
    ProductOfArrows _ (CC _ _) (CC _ _)(f ;; g) (f' ;; g').
Proof.
  apply ProductArrowUnique.
  - rewrite <- assoc.
    rewrite ProductOfArrowsPr1.
    rewrite assoc.
    rewrite ProductOfArrowsPr1.
    apply pathsinv0.
    apply assoc.
  - rewrite <- assoc.
    rewrite ProductOfArrowsPr2.
    rewrite assoc.
    rewrite ProductOfArrowsPr2.
    apply pathsinv0.
    apply assoc.
Qed.

Definition ProductOfArrows_eq (f f' : a ⇒ c) (g g' : b ⇒ d)
  : f = f' → g = g' →
      ProductOfArrows _ _ _ f g = ProductOfArrows _ (CC _ _) (CC _ _) f' g'.
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

End Products.

Section Product_unique.

Variable C : precategory.
Variable CC : Products C.
Variables a b : C.

Lemma Product_endo_is_identity (P : ProductCone _ a b)
  (k : ProductObject _ P ⇒ ProductObject _ P)
  (H1 : k ;; ProductPr1 _ P = ProductPr1 _ P)
  (H2 : k ;; ProductPr2 _ P = ProductPr2 _ P)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply ProductArrowEta.
  apply pathsinv0.
  apply ProductArrowUnique; apply pathsinv0.
  + rewrite id_left. exact H1.
  + rewrite id_left. exact H2.
Qed.

End Product_unique.

Section Products_from_Lims.

Variable C : precategory.
Variable hsC : has_homsets C.

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

Definition ProdCone {a b c : C} (f : c --> a) (g : c --> b) : cone (product_diagram a b) c.
Proof.
simple refine (mk_cone _ _); simpl.
  + intros x; case x; [apply f | apply g].
  + abstract (intros x y e; destruct e).
Defined.

Lemma Products_from_Lims : Lims C -> Products C.
Proof.
intros H a b.
case (H _ (product_diagram a b)); simpl.
intros t; destruct t as [ab cc]; simpl; intros iscc.
apply (mk_ProductCone _ _ _ ab (coconeIn cc true) (coconeIn cc false)).
apply (mk_isProductCone _ hsC); simpl; intros c f g.
case (iscc c (ProdCone f g)); simpl; intros t Ht.
simple refine (tpair _ _ _).
+ apply (tpair _ (pr1 t)); split; [ apply (pr2 t true) | apply (pr2 t false) ].
+ intros t0.
  apply subtypeEquality; [intros aa; apply isapropdirprod; apply hsC|]; simpl.
  simple refine (let X : Σ x : c --> ab, ∀ v, coconeIn cc v ;; x =
            (if v as b0 return (c --> (if b0 then a else b)) then f else g) := _ in _).
  { apply (tpair _ (pr1 t0)); intro x; case x;
    [ apply (pr1 (pr2 t0)) | apply (pr2 (pr2 t0)) ]. }
apply (maponpaths pr1 (Ht X)).
Defined.

End Products_from_Lims.

Section test.

Variable C : precategory.
Variable H : Products C.
Arguments ProductObject [C] c d {_}.
Local Notation "c 'x' d" := (ProductObject  c d )(at level 5).
(*
Check (fun c d : C => c x d).
*)
End test.
