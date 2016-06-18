(* Direct implementation of products *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.limits.arbitrary_products.
Require Import UniMath.Foundations.Combinatorics.StandardFiniteSets.

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

Definition ProductOfArrows_comp (f : a --> c) (f' : b --> d) (g : c --> x) (g' : d --> y)
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

Definition ProductOfArrows_eq (f f' : a --> c) (g g' : b --> d)
  : f = f' → g = g' →
      ProductOfArrows _ _ _ f g = ProductOfArrows _ (CC _ _) (CC _ _) f' g'.
Proof.
  induction 1.
  induction 1.
  apply idpath.
Qed.

End Products.

(** In this section we construct a product from an arbitrary product and an
  arbitrary product from a product. *)
Section Products_ArbitraryProducts.

  (** Variables and definitions we are going to use in the proofs *)
  Variable C : precategory.
  Hypothesis hs : has_homsets C.
  Definition stn0 : stn 2 := stnpair 2 0 (natlthtolths _ _ (natlthnsn 0)).
  Definition stn1 : stn 2 := stnpair 2 1 (natlthnsn 1).

  (** We will use the following definitions to do induction.  *)
  Definition tworec (n : nat) (H' : n < 2) : (n = 0) ⨿ (n = 1).
  Proof.
    destruct n.
    exact (ii1 (idpath 0)).
    destruct n.
    exact (ii2 (idpath 1)).
    exact (fromempty (nopathsfalsetotrue H')).
  Defined.

  Definition stn2ind (i : stn 2) : (i = stn0) ⨿ (i = stn1).
  Proof.
    induction (tworec (pr1 i)).
    apply ii1. apply isinjstntonat, a.
    apply ii2. apply isinjstntonat, b.
    exact (pr2 i).
  Defined.


  (** Construct a family of 2 objects from a pair of objects. *)
  Definition pair_to_stn2 (c1 c2 : C) : (stn 2) -> C.
  Proof.
    intros X.
    induction (stn2ind X).
    exact c1.
    exact c2.
  Defined.

  (** The following lemmas verify that the above definition is correct.*)
  Lemma pair_to_stn2_1 (c1 c2 : C) : pair_to_stn2 c1 c2 stn0 = c1.
  Proof. apply idpath. Defined.
  Lemma pair_to_stn2_2 (c1 c2 : C) : pair_to_stn2 c1 c2 stn1 = c2.
  Proof. apply idpath. Defined.

  (** Construct a family of two morphisms with the same domain from
    two morphisms with the same domain. *)
  Definition pair_to_stn2_mors (c : C) (a : stn 2 -> C) (f : C⟦c, a stn0⟧)
             (g : C⟦c, a stn1⟧) : forall i : stn 2, C⟦c, a i⟧.
  Proof.
    intros i. induction (stn2ind i).
    rewrite <- a0 in f. apply f.
    rewrite <- b in g. apply g.
  Defined.

  (** The following lemmas verify that the above definition is correct. *)
  Lemma pair_to_stn2_mors_1 (c : C) (a : stn 2 -> C) (f : C⟦c, a stn0⟧)
        (g : C⟦c, a stn1⟧) :
    pair_to_stn2_mors c a f g stn0 = f.
  Proof. apply idpath. Defined.
  Lemma pair_to_stn2_mors_2 (c : C) (a : stn 2 -> C) (f : C⟦c, a stn0⟧)
        (g : C⟦c, a stn1⟧) :
    pair_to_stn2_mors c a f g stn1 = g.
  Proof. apply idpath. Defined.

  (** Construction of a product from an arbitrary product. *)
  Definition product_from_arbitrary_product (a : stn 2 -> C)
             (Cone : ArbitraryProductCone (stn 2) C a) :
    ProductCone C (a stn0) (a stn1).
  Proof.
    set (p1 := ArbitraryProductPr _ _ Cone stn0).
    set (p2 := ArbitraryProductPr _ _ Cone stn1).
    set (Coneob := (ArbitraryProductObject _ _ Cone)).
    refine (mk_ProductCone _ (a stn0) (a stn1) Coneob p1 p2 _).
    refine (mk_isProductCone _ hs _ _ _ _ _ _).
    intros c f g.
    set (mors := pair_to_stn2_mors c a f g).
    set (com1 := ArbitraryProductPrCommutes _ _ a Cone c mors stn0).
    set (com2 := ArbitraryProductPrCommutes _ _ a Cone c mors stn1).
    set (ar := (ArbitraryProductArrow _ _ Cone mors)).
    refine (tpair _ (tpair _ ar _)  _).
    intros t; eapply total2_paths.
    apply proofirrelevance, isapropdirprod; apply hs.

    Unshelve.

    (* Commutativity *)
    split.
    rewrite <- (pair_to_stn2_mors_1 c a f g). apply com1.
    rewrite <- (pair_to_stn2_mors_2 c a f g). apply com2.

    (* Uniqueness *)
    eapply ArbitraryProductArrowUnique. intros i. induction (stn2ind i).
    rewrite a0. fold p1. rewrite <- (pair_to_stn2_mors_1 c a f g).
    apply (dirprod_pr1 (pr2 t)).
    rewrite b. fold p2. rewrite <- (pair_to_stn2_mors_2 c a f g).
    apply (dirprod_pr2 (pr2 t)).
  Defined.

  (** Construction of an arbitrary product from a product. *)
  Definition arbitrary_product_from_product (c1 c2 : C)
             (Cone : ProductCone C c1 c2) :
    ArbitraryProductCone (stn 2) C (pair_to_stn2 c1 c2).
  Proof.
    set (a := pair_to_stn2 c1 c2).
    set (p1 := ProductPr1 _ Cone).
    set (p2 := ProductPr2 _ Cone).
    set (ConeOb := ProductObject _ Cone).
    set (f := pair_to_stn2_mors ConeOb a p1 p2).
    refine (mk_ArbitraryProductCone _ _ a ConeOb f _ ).
    refine (mk_isArbitraryProductCone _ _ hs _ _ _ _).
    intros c g.
    set (f1 := g stn0).
    set (f2 := g stn1).
    set (ar := ProductArrow _ Cone f1 f2).
    set (com1 := ProductPr1Commutes _ _ _ Cone _ f1 f2).
    set (com2 := ProductPr2Commutes _ _ _ Cone _ f1 f2).
    refine (tpair _ (tpair _ ar _ ) _).
    intros t. eapply total2_paths. apply proofirrelevance.
    apply impred_isaprop. intros t0. apply hs.

    Unshelve.
    (* Commutativity *)
    intros i. induction (stn2ind i).
    rewrite a0. unfold f. rewrite (pair_to_stn2_mors_1 ConeOb a p1 p2).
    apply com1.
    rewrite b. unfold f. rewrite (pair_to_stn2_mors_2 ConeOb a p1 p2).
    apply com2.

    (* Uniqueness *)
    apply ProductArrowUnique.
    fold p1. rewrite <- (pair_to_stn2_mors_1 ConeOb a p1 p2). fold f.
    apply (pr2 t stn0).
    fold p2. rewrite <- (pair_to_stn2_mors_2 ConeOb a p1 p2). fold f.
    apply (pr2 t stn1).
  Defined.
End Products_ArbitraryProducts.

(** In this section we construct an arbitrary product from two arbitrary
  products by taking the disjoint union of the objects. To do this, we need
  to assume that the product of the arbitrary products exists. *)
Section product_from_products.
  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  (** Disjoint union of the objects a1 and a2. *)
  Definition coprod_families {I1 I2 : UU} (a1 : I1 -> C) (a2 : I2 -> C):
    I1 ⨿ I2 -> C.
  Proof.
    intros X.
    induction X.
    apply (a1 a).
    apply (a2 b).
  Defined.

  (** Verify that we have the same objects. *)
  Lemma coprod_families_1 {I1 I2 : UU} (a1 : I1 -> C) (a2 : I2 -> C) (i : I1):
    coprod_families a1 a2 (ii1 i) = a1 i.
  Proof. apply idpath. Defined.
  Lemma coprod_families_2 {I1 I2 : UU} (a1 : I1 -> C) (a2 : I2 -> C) (i : I2):
    coprod_families a1 a2 (ii2 i) = a2 i.
  Proof. apply idpath. Defined.


  (** Construction of an arbitrary coproduct from two arbitrary coproducts and a
    product of the arbitrary products. *)
  Theorem arbitrary_product_from_arbitrary_products :
    forall (I1 I2 : UU) (a1 : I1 -> C) (a2 : I2 -> C)
      (A1 : ArbitraryProductCone _ C a1)
      (A2 : ArbitraryProductCone _ C a2)
      (Cone : ProductCone C (ArbitraryProductObject _ _ A1)
                          (ArbitraryProductObject _ _ A2)),
      ArbitraryProductCone _ C (coprod_families a1 a2).
  Proof.
    intros I1 I2 a1 a2 A1 A2 Cone.

    (* Set names from useful terms *)
    set (A1pr := ArbitraryProductPr _ _ A1).
    set (A2pr := ArbitraryProductPr _ _ A2).
    set (p1 := ProductPr1 _ Cone).
    set (p2 := ProductPr2 _ Cone).

    eapply (mk_ArbitraryProductCone _ _ _ (ProductObject _ Cone)).
    eapply mk_isArbitraryProductCone.
    apply hs.
    intros c g.

    (* Set names for useful terms *)
    set (g1 := fun i : I1 => g (ii1 i)).
    set (g2 := fun i : I2 => g (ii2 i)).
    set (ar1 := ArbitraryProductArrow _ _ A1 g1).
    set (ar2 := ArbitraryProductArrow _ _ A2 g2).
    set (ar := ProductArrow _ Cone ar1 ar2).
    set (com1 := ProductPr1Commutes _ _ _ Cone c ar1 ar2).
    set (com2 := ProductPr2Commutes _ _ _ Cone c ar1 ar2).

    refine (tpair _ _ _).
    intros t.
    eapply total2_paths. apply proofirrelevance.
    apply impred_isaprop. intros t0. apply hs.

    Unshelve.

    (* Morphisms to objects from the cone *)
    intros i. unfold coprod_families, coprod_rect. induction i.
    apply (p1 ;; A1pr a).
    apply (p2 ;; A2pr b).

    (* The unique arrow to the cone from c *)
    refine (tpair _ ar _ ).

    (* Commutativity of morphisms *)
    intros i. unfold coprod_rect. induction i.

    set (com'1 := ArbitraryProductPrCommutes _ _ _ A1 c g1 a).
    unfold A1pr. unfold p1. unfold ar. rewrite assoc. rewrite com1.
    unfold ar1. rewrite -> com'1. apply idpath.


    set (com'2 := ArbitraryProductPrCommutes _ _ _ A2 c g2 b).
    unfold A2pr, p2, ar. rewrite assoc. rewrite com2.
    unfold ar2. rewrite com'2. apply idpath.

    simpl.
    (* Uniqueness of the morphism to the cone *)
    eapply ProductArrowUnique.
    eapply ArbitraryProductArrowUnique.
    intros i. simpl in t. set (t2 := pr2 t (ii1 i)). simpl in t2.
    fold A1pr. rewrite <- assoc. apply t2.

    eapply ArbitraryProductArrowUnique.
    intros i. simpl in t. set (t2 := pr2 t (ii2 i)). simpl in t2.
    fold A2pr. rewrite <- assoc. apply t2.
  Defined.
End product_from_products.

Section Product_unique.

Variable C : precategory.
Variable CC : Products C.
Variables a b : C.

Lemma Product_endo_is_identity (P : ProductCone _ a b)
  (k : ProductObject _ P --> ProductObject _ P)
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

(* Section Products_from_Lims. *)

(* Require Import UniMath.CategoryTheory.limits.graphs.colimits. *)
(* Require Import UniMath.CategoryTheory.limits.graphs.limits. *)
(* Require Import UniMath.CategoryTheory.opp_precat. *)
(* Local Notation "C '^op'" := (opp_precat C) (at level 3, format "C ^op"). *)

(* Variable C : precategory. *)
(* Variable hsC : has_homsets C. *)

(* Definition two_graph : graph. *)
(* Proof. *)
(*   exists bool. *)
(*   exact (fun _ _ => empty). *)
(* Defined. *)

(* Definition product_diagram (a b : C) : diagram two_graph C^op. *)
(* Proof. *)
(*   exists (fun x : bool => if x then a else b). *)
(*   intros u v F. *)
(*   induction F. *)
(* Defined. *)

(* Definition ProdCone {a b c : C} (f : c --> a) (g : c --> b) : cone (product_diagram a b) c. *)
(* Proof. *)
(* simple refine (mk_cone _ _); simpl. *)
(*   + intros x; case x; [apply f | apply g]. *)
(*   + abstract (intros x y e; destruct e). *)
(* Defined. *)

(* Lemma Products_from_Lims : Lims C -> Products C. *)
(* Proof. *)
(* intros H a b. *)
(* case (H _ (product_diagram a b)); simpl. *)
(* intros t; destruct t as [ab cc]; simpl; intros iscc. *)
(* apply (mk_ProductCone _ _ _ ab (coconeIn cc true) (coconeIn cc false)). *)
(* apply (mk_isProductCone _ hsC); simpl; intros c f g. *)
(* case (iscc c (ProdCone f g)); simpl; intros t Ht. *)
(* simple refine (tpair _ _ _). *)
(* + apply (tpair _ (pr1 t)); split; [ apply (pr2 t true) | apply (pr2 t false) ]. *)
(* + intros t0. *)
(*   apply subtypeEquality; [intros aa; apply isapropdirprod; apply hsC|]; simpl. *)
(*   simple refine (let X : Σ x : c --> ab, ∀ v, coconeIn cc v ;; x = *)
(*             (if v as b0 return (c --> (if b0 then a else b)) then f else g) := _ in _). *)
(*   { apply (tpair _ (pr1 t0)); intro x; case x; *)
(*     [ apply (pr1 (pr2 t0)) | apply (pr2 (pr2 t0)) ]. } *)
(* apply (maponpaths pr1 (Ht X)). *)
(* Defined. *)

(* End Products_from_Lims. *)

Section test.

Variable C : precategory.
Variable H : Products C.
Arguments ProductObject [C] c d {_}.
Local Notation "c 'x' d" := (ProductObject  c d )(at level 5).
(*
Check (fun c d : C => c x d).
*)
End test.

(* The binary product functor: C * C -> C *)
Section binproduct_functor.

Context {C : precategory} (PC : Products C).

Definition binproduct_functor_data :
  functor_data (product_precategory C C) C.
Proof.
mkpair.
- intros p.
  apply (ProductObject _ (PC (pr1 p) (pr2 p))).
- simpl; intros p q f.
  apply (ProductOfArrows _ (PC (pr1 q) (pr2 q))
                           (PC (pr1 p) (pr2 p)) (pr1 f) (pr2 f)).
Defined.

Definition binproduct_functor : functor (product_precategory C C) C.
Proof.
apply (tpair _ binproduct_functor_data).
abstract (split;
  [ intro x; simpl; apply pathsinv0, Product_endo_is_identity;
    [ now rewrite ProductOfArrowsPr1, id_right
    | now rewrite ProductOfArrowsPr2, id_right ]
  | now intros x y z f g; simpl; rewrite ProductOfArrows_comp]).
Defined.

End binproduct_functor.

(* Defines the product of two functors by:
    x -> (x,x) -> (F x,G x) -> F x * G x

  For a direct definition see FunctorsPointwiseProduct.v

*)
Definition product_of_functors {C D : precategory} (HD : Products D)
  (F G : functor C D) : functor C D :=
  functor_composite (delta_functor C)
     (functor_composite (pair_functor F G) (binproduct_functor HD)).
