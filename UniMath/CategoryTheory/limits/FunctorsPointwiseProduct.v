(** **********************************************************

Anders Mörtberg, 2016

************************************************************)


(** **********************************************************

Contents :

- Definition of a product structure on a functor category
  by taking pointwise products in the target category

Adapted from the binary version

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.products.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section def_functor_pointwise_prod.

Variables (I : UU) (C D : precategory).
Variable HD : Products I D.
Variable hsD : has_homsets D.

Section product_of_functors.

Variables F : I -> functor C D.

(* Local Notation "c ⊗ d" := (ProductObject _ (HD c d))(at level 45). *)

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
Variable f : forall i, nat_trans A (F i).

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
