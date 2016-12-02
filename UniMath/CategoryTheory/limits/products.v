(**

Direct implementation of indexed products together with:

- The general product functor ([product_functor])
- Definition of a product structure on a functor category by taking pointwise products in the target
  category (adapted from the binary version) ([Products_functor_precat])
- Products from limits ([Products_from_Lims])

Written by: Anders Mörtberg 2016


*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

(** * Definition of indexed products of objects in a precategory *)
Section product_def.

Variable (I : UU) (C : precategory).

Definition isProductCone (c : Π (i : I), C) (p : C)
  (pi : Π i, p --> c i) :=
  Π (a : C) (f : Π i, a --> c i),
    iscontr (total2 (fun (fap : a --> p) => Π i, fap ;; pi i = f i)).

Definition ProductCone (ci : Π i, C) :=
   total2 (fun pp1p2 : total2 (fun p : C => Π i, p --> ci i) =>
             isProductCone ci (pr1 pp1p2) (pr2 pp1p2)).

Definition Products := Π (ci : Π i, C), ProductCone ci.
Definition hasProducts := ishinh Products.

Definition ProductObject {c : Π i, C} (P : ProductCone c) : C := pr1 (pr1 P).
Definition ProductPr {c : Π i, C} (P : ProductCone c) : Π i, ProductObject P --> c i :=
  pr2 (pr1 P).

Definition isProductCone_ProductCone {c : Π i, C} (P : ProductCone c) :
   isProductCone c (ProductObject P) (ProductPr P).
 Proof.
  exact (pr2 P).
Defined.

Definition ProductArrow {c : Π i, C} (P : ProductCone c) {a : C} (f : Π i, a --> c i)
  : a --> ProductObject P.
Proof.
  apply (pr1 (pr1 (isProductCone_ProductCone P _ f))).
Defined.

Lemma ProductPrCommutes (c : Π i, C) (P : ProductCone c) :
     Π (a : C) (f : Π i, a --> c i) i, ProductArrow P f ;; ProductPr P i = f i.
Proof.
  intros a f i.
  apply (pr2 (pr1 (isProductCone_ProductCone P _ f)) i).
Qed.

Lemma ProductPr_idtoiso {i1 i2 : I} (a : I -> C) (P : ProductCone a)
      (e : i1 = i2) :
  ProductPr P i1 ;; idtoiso (maponpaths a e) = ProductPr P i2.
Proof.
  induction e.
  apply id_right.
Qed.

Lemma ProductArrowUnique (c : Π i, C) (P : ProductCone c) (x : C)
    (f : Π i, x --> c i) (k : x --> ProductObject P)
    (Hk : Π i, k ;; ProductPr P i = f i) : k = ProductArrow P f.
Proof.
  set (H' := pr2 (isProductCone_ProductCone P _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Definition mk_ProductCone (a : Π i, C) :
  Π (c : C) (f : Π i, C⟦c,a i⟧), isProductCone _ _ f -> ProductCone a.
Proof.
  intros c f X.
  simple refine (tpair _ (c,,f) X).
Defined.

Definition mk_isProductCone (hsC : has_homsets C) (a : I -> C) (p : C)
  (pa : Π i, C⟦p,a i⟧) : (Π (c : C) (f : Π i, C⟦c,a i⟧),
                                  ∃! k : C⟦c,p⟧, Π i, k ;; pa i = f i) ->
                              isProductCone a p pa.
Proof.
intros H c cc; apply H.
Defined.

Lemma ProductArrowEta (c : Π i, C) (P : ProductCone c) (x : C)
    (f : x --> ProductObject P) :
    f = ProductArrow P (fun i => f ;; ProductPr P i).
Proof.
  now apply ProductArrowUnique.
Qed.

Definition ProductOfArrows {c : Π i, C} (Pc : ProductCone c) {a : Π i, C}
    (Pa : ProductCone a) (f : Π i, a i --> c i) :
      ProductObject Pa --> ProductObject Pc :=
    ProductArrow Pc (fun i => ProductPr Pa i ;; f i).

Lemma ProductOfArrowsPr {c : Π i, C} (Pc : ProductCone c) {a : Π i, C}
    (Pa : ProductCone a) (f : Π i, a i --> c i) :
    Π i, ProductOfArrows Pc Pa f ;; ProductPr Pc i = ProductPr Pa i ;; f i.
Proof.
  unfold ProductOfArrows; intro i.
  now rewrite (ProductPrCommutes _ _ _ _ i).
Qed.

Lemma postcompWithProductArrow {c : Π i, C} (Pc : ProductCone c) {a : Π i, C}
    (Pa : ProductCone a) (f : Π i, a i --> c i)
    {x : C} (k : Π i, x --> a i) :
        ProductArrow Pa k ;; ProductOfArrows Pc Pa f =
        ProductArrow Pc (fun i => k i ;; f i).
Proof.
apply ProductArrowUnique; intro i.
now rewrite <- assoc, ProductOfArrowsPr, assoc, ProductPrCommutes.
Qed.

Lemma precompWithProductArrow {c : Π i, C} (Pc : ProductCone c)
  {a : C} (f : Π i, a --> c i) {x : C} (k : x --> a)  :
       k ;; ProductArrow Pc f = ProductArrow Pc (fun i => k ;; f i).
Proof.
apply ProductArrowUnique; intro i.
now rewrite <- assoc, ProductPrCommutes.
Qed.

End product_def.

Section Products.

Variables (I : UU) (C : precategory) (CC : Products I C).

Definition ProductOfArrows_comp (a b c : Π (i : I), C)
  (f : Π i, a i --> b i) (g : Π i, b i --> c i)
  : ProductOfArrows _ _ _ _ f ;; ProductOfArrows _ _ _ (CC _) g
    = ProductOfArrows _ _ (CC _) (CC _) (fun i => f i ;; g i).
Proof.
apply ProductArrowUnique; intro i.
rewrite <- assoc, ProductOfArrowsPr.
now rewrite assoc, ProductOfArrowsPr, assoc.
Qed.

(* Definition ProductOfArrows_eq (f f' : a --> c) (g g' : b --> d) *)
(*   : f = f' → g = g' → *)
(*       ProductOfArrows _ _ _ f g = ProductOfArrows _ (CC _ _) (CC _ _) f' g'. *)
(* Proof. *)
(*   induction 1. *)
(*   induction 1. *)
(*   apply idpath. *)
(* Qed. *)

End Products.

Section Product_unique.

Variables (I : UU) (C : precategory).
Variable CC : Products I C.
Variables a : Π (i : I), C.

Lemma Product_endo_is_identity (P : ProductCone _ _ a)
  (k : ProductObject _ _ P --> ProductObject _ _ P)
  (H1 : Π i, k ;; ProductPr _ _ P i = ProductPr _ _ P i)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply ProductArrowEta.
  apply pathsinv0.
  apply ProductArrowUnique; intro i; apply pathsinv0.
  now rewrite id_left, H1.
Qed.

End Product_unique.

(** * The product functor: C^I -> C *)
Section product_functor.

Context (I : UU) {C : precategory} (PC : Products I C).

Definition product_functor_data :
  functor_data (power_precategory I C) C.
Proof.
mkpair.
- intros p.
  apply (ProductObject _ _ (PC p)).
- simpl; intros p q f.
  exact (ProductOfArrows _ _ _ _ f).
Defined.

Definition product_functor : functor (power_precategory I C) C.
Proof.
apply (tpair _ product_functor_data).
abstract (split;
  [ now intro x; simpl; apply pathsinv0, Product_endo_is_identity;
        intro i; rewrite ProductOfArrowsPr, id_right
  | now intros x y z f g; simpl; rewrite ProductOfArrows_comp]).
Defined.

End product_functor.

(* The product of a family of functors *)
Definition product_of_functors_alt
  (I : UU) {C D : precategory} (HD : Products I D)
  (F : Π (i : I), functor C D) : functor C D :=
   functor_composite (delta_functor I C)
     (functor_composite (family_functor _ F) (product_functor _ HD)).

(** * Products lift to functor categories *)
Section def_functor_pointwise_prod.

Variables (I : UU) (C D : precategory).
Variable HD : Products I D.
Variable hsD : has_homsets D.

Section product_of_functors.

Variables F : I -> functor C D.

Definition product_of_functors_ob (c : C) : D :=
  ProductObject _ _ (HD (fun i => F i c)).

Definition product_of_functors_mor (c c' : C) (f : c --> c') :
  product_of_functors_ob c --> product_of_functors_ob c' :=
    ProductOfArrows _ _ _ _ (fun i => # (F i) f).

Definition product_of_functors_data : functor_data C D.
Proof.
  exists product_of_functors_ob.
  exact product_of_functors_mor.
Defined.

Lemma is_functor_product_of_functors_data : is_functor product_of_functors_data.
Proof.
split; simpl; intros.
- unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply Product_endo_is_identity; intro i.
    unfold product_of_functors_mor.
    eapply pathscomp0; [apply (ProductOfArrowsPr _ _ (HD (λ i, (F i) a)))|].
    now simpl; rewrite functor_id, id_right.
- unfold functor_compax; simpl; unfold product_of_functors_mor.
  intros; simpl in *.
  apply pathsinv0.
  eapply pathscomp0.
  apply ProductOfArrows_comp.
  apply maponpaths, funextsec; intro i.
  now rewrite functor_comp.
Qed.

Definition product_of_functors : functor C D :=
  tpair _ _ is_functor_product_of_functors_data.

Lemma product_of_functors_alt_eq_product_of_functors :
  product_of_functors_alt _ HD F = product_of_functors.
Proof.
now apply (functor_eq _ _ hsD).
Defined.

Definition product_nat_trans_pr_data i (c : C) :
  D ⟦ product_of_functors c, (F i) c ⟧ :=
  ProductPr _ _ (HD (fun j => (F j) c)) i.

Lemma is_nat_trans_product_nat_trans_pr_data i :
  is_nat_trans _ _ (product_nat_trans_pr_data i).
Proof.
intros c c' f.
apply (ProductOfArrowsPr I _ (HD (λ i, F i c')) (HD (λ i, F i c))).
Qed.

Definition product_nat_trans_pr i : nat_trans product_of_functors (F i) :=
  tpair _ _ (is_nat_trans_product_nat_trans_pr_data i).

Section vertex.

(** The product morphism of a diagram with vertex [A] *)

Variable A : functor C D.
Variable f : Π i, nat_trans A (F i).

Definition product_nat_trans_data c :
  A c --> product_of_functors c:=
    ProductArrow _ _ _ (fun i => f i c).

Lemma is_nat_trans_product_nat_trans_data :
  is_nat_trans _ _ product_nat_trans_data.
Proof.
intros a b k; simpl.
eapply pathscomp0; [apply precompWithProductArrow|].
apply pathsinv0.
eapply pathscomp0; [apply postcompWithProductArrow|].
apply maponpaths, funextsec; intro i.
now rewrite (nat_trans_ax (f i)).
Qed.

Definition product_nat_trans : nat_trans A product_of_functors
  := tpair _ _ is_nat_trans_product_nat_trans_data.

End vertex.

Definition functor_precat_product_cone
  : ProductCone I [C, D, hsD] F.
Proof.
simple refine (mk_ProductCone _ _ _ _ _ _).
- apply product_of_functors.
- apply product_nat_trans_pr.
- simple refine (mk_isProductCone _ _ _ _ _ _ _).
  + apply functor_category_has_homsets.
  + intros A f.
    mkpair.
    * apply (tpair _ (product_nat_trans A f)).
      abstract (intro i; apply (nat_trans_eq hsD); intro c;
                apply (ProductPrCommutes I D _ (HD (λ j, (F j) c)))).
    * abstract (
        intro t; apply subtypeEquality; simpl;
          [intro; apply impred; intro; apply (isaset_nat_trans hsD)|];
        apply (nat_trans_eq hsD); intro c;
        apply ProductArrowUnique; intro i;
        apply (nat_trans_eq_pointwise (pr2 t i))).
Defined.

End product_of_functors.

Definition Products_functor_precat : Products I [C, D, hsD].
Proof.
intros F; apply functor_precat_product_cone.
Defined.

End def_functor_pointwise_prod.

(** * Products from limits *)
Section products_from_limits.

Variables (I : UU) (C : precategory) (hsC : has_homsets C).

Definition I_graph : graph := (I,,λ _ _,empty).

Definition products_diagram (F : I → C) : diagram I_graph C.
Proof.
exists F.
abstract (intros u v e; induction e).
Defined.

Definition productscone c (F : I → C) (H : Π i, c --> F i) :
  cone (products_diagram F) c.
Proof.
mkpair.
+ intro v; apply H.
+ abstract (intros u v e; induction e).
Defined.

Lemma Products_from_Lims : Lims_of_shape I_graph C -> Products I C.
Proof.
intros H F.
set (HF := H (products_diagram F)).
use mk_ProductCone.
+ apply (lim HF).
+ intros i; apply (limOut HF).
+ apply (mk_isProductCone _ _ hsC); intros c Fic.
  use unique_exists.
  - apply limArrow.
    use mk_cone.
    * simpl; intro i; apply Fic.
    * abstract (simpl; intros u v e; induction e).
  - abstract (simpl; intro i; apply (limArrowCommutes HF)).
  - abstract (intros y; apply impred; intro i; apply hsC).
  - abstract (intros f Hf; apply limArrowUnique; simpl in *; intros i; apply Hf).
Defined.

End products_from_limits.