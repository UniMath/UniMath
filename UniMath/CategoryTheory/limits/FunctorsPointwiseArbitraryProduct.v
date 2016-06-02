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
Require Import UniMath.CategoryTheory.limits.arbitrary_products.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section def_functor_pointwise_arbitrary_prod.

Variables (I : UU) (C D : precategory).
Variable HD : ArbitraryProducts I D.
Variable hsD : has_homsets D.

Section arbitrary_product_functor.

Variables F : I -> functor C D.

(* Local Notation "c ⊗ d" := (ProductObject _ (HD c d))(at level 45). *)

Definition arbitrary_product_functor_ob (c : C) : D :=
  ArbitraryProductObject _ _ (HD (fun i => F i c)).

Definition arbitrary_product_functor_mor (c c' : C) (f : c --> c') :
  arbitrary_product_functor_ob c --> arbitrary_product_functor_ob c' :=
    ArbitraryProductOfArrows _ _ _ _ (fun i => # (F i) f).

Definition arbitrary_product_functor_data : functor_data C D.
Proof.
  exists arbitrary_product_functor_ob.
  exact arbitrary_product_functor_mor.
Defined.

Lemma is_functor_arbitrary_product_functor_data : is_functor arbitrary_product_functor_data.
Proof.
split; simpl; intros.
- unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply ArbitraryProduct_endo_is_identity; intro i.
    unfold arbitrary_product_functor_mor.
    eapply pathscomp0; [apply (ArbitraryProductOfArrowsPr _ _ (HD (λ i, (F i) a)))|].
    now simpl; rewrite functor_id, id_right.
- unfold functor_compax; simpl; unfold arbitrary_product_functor_mor.
  intros; simpl in *.
  apply pathsinv0.
  eapply pathscomp0.
  apply ArbitraryProductOfArrows_comp.
  apply maponpaths, funextsec; intro i.
  now rewrite functor_comp.
Qed.

Definition arbitrary_product_functor : functor C D :=
  tpair _ _ is_functor_arbitrary_product_functor_data.

Lemma arbitrary_product_of_functors_eq_arbitrary_product_functor :
  arbitrary_product_of_functors _ HD F = arbitrary_product_functor.
Proof.
now apply (functor_eq _ _ hsD).
Defined.

Definition arbitrary_product_nat_trans_pr_data i (c : C) :
  D ⟦ arbitrary_product_functor c, (F i) c ⟧ :=
  ArbitraryProductPr _ _ (HD (fun j => (F j) c)) i.

Lemma is_nat_trans_arbitrary_product_nat_trans_pr_data i :
  is_nat_trans _ _ (arbitrary_product_nat_trans_pr_data i).
Proof.
intros c c' f.
apply (ArbitraryProductOfArrowsPr I _ (HD (λ i, F i c')) (HD (λ i, F i c))).
Qed.

Definition arbitrary_product_nat_trans_pr i : nat_trans arbitrary_product_functor (F i) :=
  tpair _ _ (is_nat_trans_arbitrary_product_nat_trans_pr_data i).

Section vertex.

(** The product morphism of a diagram with vertex [A] *)

Variable A : functor C D.
Variable f : forall i, nat_trans A (F i).

Definition arbitrary_product_nat_trans_data c :
  A c --> arbitrary_product_functor c:=
    ArbitraryProductArrow _ _ _ (fun i => f i c).

Lemma is_nat_trans_arbitrary_product_nat_trans_data :
  is_nat_trans _ _ arbitrary_product_nat_trans_data.
Proof.
intros a b k; simpl.
eapply pathscomp0; [apply precompWithArbitraryProductArrow|].
apply pathsinv0.
eapply pathscomp0; [apply postcompWithArbitraryProductArrow|].
apply maponpaths, funextsec; intro i.
now rewrite (nat_trans_ax (f i)).
Qed.

Definition arbitrary_product_nat_trans : nat_trans A arbitrary_product_functor
  := tpair _ _ is_nat_trans_arbitrary_product_nat_trans_data.

End vertex.

Definition functor_precat_arbitrary_product_cone
  : ArbitraryProductCone I [C, D, hsD] F.
Proof.
simple refine (mk_ArbitraryProductCone _ _ _ _ _ _).
- apply arbitrary_product_functor.
- apply arbitrary_product_nat_trans_pr.
- simple refine (mk_isArbitraryProductCone _ _ _ _ _ _ _).
  + apply functor_category_has_homsets.
  + intros A f.
    mkpair.
    * apply (tpair _ (arbitrary_product_nat_trans A f)).
      abstract (intro i; apply (nat_trans_eq hsD); intro c;
                apply (ArbitraryProductPrCommutes I D _ (HD (λ j, (F j) c)))).
    * abstract (
        intro t; apply subtypeEquality; simpl;
          [intro; apply impred; intro; apply (isaset_nat_trans hsD)|];
        apply (nat_trans_eq hsD); intro c;
        apply ArbitraryProductArrowUnique; intro i;
        apply (nat_trans_eq_pointwise (pr2 t i))).
Defined.

End arbitrary_product_functor.

Definition ArbitraryProducts_functor_precat : ArbitraryProducts I [C, D, hsD].
Proof.
intros F; apply functor_precat_arbitrary_product_cone.
Defined.

End def_functor_pointwise_arbitrary_prod.
