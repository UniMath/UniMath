(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Definition of a product structure on a functor category
  by taking pointwise products in the target category



************************************************************)


Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.products.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** Goal: lift coproducts from the target (pre)category to the functor (pre)category *)

Section def_functor_pointwise_prod.

Variable C D : precategory.
Variable HD : Products D.
Variable hsD : has_homsets D.

Section product_functor.

Variables F G : functor C D.


Local Notation "c ⊗ d" := (ProductObject _ (HD c d))(at level 45).

Definition product_functor_ob (c : C) : D := F c ⊗ G c.

Definition product_functor_mor (c c' : C) (f : c ⇒ c')
  : product_functor_ob c ⇒ product_functor_ob c'
  := ProductOfArrows _ _ _ (#F f) (#G f).

Definition product_functor_data : functor_data C D.
Proof.
  exists product_functor_ob.
  exact product_functor_mor.
Defined.


Lemma is_functor_product_functor_data : is_functor product_functor_data.
Proof.
  split; simpl; intros.
  - red; intros; simpl in *.
    apply pathsinv0.
    unfold product_functor_mor.
    apply Product_endo_is_identity.
    + rewrite ProductOfArrowsPr1.
      rewrite functor_id.
      apply id_right.
    + rewrite ProductOfArrowsPr2.
      rewrite functor_id.
      apply id_right.
  - red; intros; simpl in *.
    unfold product_functor_mor.
    do 2 rewrite functor_comp.
    apply pathsinv0.
    apply ProductOfArrows_comp.
Qed.

Definition product_functor : functor C D := tpair _ _ is_functor_product_functor_data.

Definition product_nat_trans_pr1_data : ∀ c, product_functor c ⇒ F c
  := λ c : C, ProductPr1 _ (HD (F c) (G c)).

Lemma is_nat_trans_product_nat_trans_pr1_data
  : is_nat_trans _ _ product_nat_trans_pr1_data.
Proof.
  red.
  intros c c' f.
  unfold product_nat_trans_pr1_data.
  unfold product_functor. simpl.
  unfold product_functor_mor.
  apply ProductOfArrowsPr1.
Qed.

Definition product_nat_trans_pr1 : nat_trans _ _
  := tpair _ _ is_nat_trans_product_nat_trans_pr1_data.


Definition product_nat_trans_pr2_data : ∀ c, product_functor c ⇒ G c
  := λ c : C, ProductPr2 _ (HD (F c) (G c)).

Lemma is_nat_trans_product_nat_trans_pr2_data
  : is_nat_trans _ _ product_nat_trans_pr2_data.
Proof.
  red.
  intros c c' f.
  unfold product_nat_trans_pr2_data.
  unfold product_functor. simpl.
  unfold product_functor_mor.
  apply ProductOfArrowsPr2.
Qed.

Definition product_nat_trans_pr2 : nat_trans _ _
  := tpair _ _ is_nat_trans_product_nat_trans_pr2_data.


Section vertex.

(** The product morphism of a diagram with vertex [A] *)

Variable A : functor C D.
Variable f : A ⟶ F.
Variable g : A ⟶ G.

Definition product_nat_trans_data : ∀ c,  A c ⇒ product_functor c.
Proof.
  intro c.
  apply ProductArrow.
  - exact (f c).
  - exact (g c).
Defined.

Lemma is_nat_trans_product_nat_trans_data : is_nat_trans _ _ product_nat_trans_data.
Proof.
  intros a b k.
  simpl.
  unfold product_functor_mor.
  unfold product_nat_trans_data.
  set (XX:=postcompWithProductArrow).
  set (X1 := XX D _ _ (HD (F b) (G b))).
  set (X2 := X1 _ _ (HD (F a) (G a))).
  rewrite X2.
  clear X2 X1 XX.
  set (XX:=precompWithProductArrow).
  set (X1 := XX D _ _ (HD (F b) (G b))).
  rewrite X1.
  rewrite (nat_trans_ax f).
  rewrite (nat_trans_ax g).
  apply idpath.
Qed.

Definition product_nat_trans : nat_trans _ _
  := tpair _ _ is_nat_trans_product_nat_trans_data.

Lemma product_nat_trans_Pr1Commutes :
  nat_trans_comp _ _ _ product_nat_trans product_nat_trans_pr1  = f.
Proof.
  apply nat_trans_eq.
  - apply hsD.
  - intro c; simpl.
    apply ProductPr1Commutes.
Qed.

Lemma product_nat_trans_Pr2Commutes :
  nat_trans_comp _ _ _ product_nat_trans product_nat_trans_pr2  = g.
Proof.
  apply nat_trans_eq.
  - apply hsD.
  - intro c; simpl.
    apply ProductPr2Commutes.
Qed.

End vertex.

Lemma product_nat_trans_univ_prop (A : [C, D, hsD])
  (f : (A ⇒ (F:[C,D,hsD]))) (g : A ⇒ (G:[C,D,hsD])) :
   ∀
   t : Σ fg : A ⇒ (product_functor:[C,D,hsD]),
       fg ;; (product_nat_trans_pr1 : (product_functor:[C,D,hsD]) ⇒ F) = f
      ×
       fg ;; (product_nat_trans_pr2 : (product_functor:[C,D,hsD]) ⇒ G) = g,
   t =
   tpair
     (λ fg : A ⇒ (product_functor:[C,D,hsD]),
      fg ;; (product_nat_trans_pr1 : (product_functor:[C,D,hsD]) ⇒ F) = f
   ×
      fg ;; (product_nat_trans_pr2 : (product_functor:[C,D,hsD]) ⇒ G) = g)
     (product_nat_trans A f g)
     (dirprodpair (product_nat_trans_Pr1Commutes A f g)
        (product_nat_trans_Pr2Commutes A f g)).
Proof.
  intro t.
  simpl in *.
  destruct t as [t1 [ta tb]].
  simpl in *.
  apply subtypeEquality.
  - intro.
    simpl.
    apply isapropdirprod;
    apply isaset_nat_trans;
    apply hsD.
  - simpl.
    apply nat_trans_eq.
    + apply hsD.
    + intro c.
      unfold product_nat_trans.
      simpl.
      unfold product_nat_trans_data.
      apply ProductArrowUnique.
      * apply (nat_trans_eq_pointwise ta).
      * apply (nat_trans_eq_pointwise tb).
Qed.

Definition functor_precat_product_cone
  : ProductCone [C, D, hsD] F G.
Proof.
unshelve refine (mk_ProductCone _ _ _ _ _ _ _).
- apply product_functor.
- apply product_nat_trans_pr1.
- apply product_nat_trans_pr2.
- unshelve refine (mk_isProductCone _ _ _ _ _ _ _ _).
  + apply functor_category_has_homsets.
  + intros A f g.
    exists (tpair _ (product_nat_trans A f g)
             (dirprodpair (product_nat_trans_Pr1Commutes _ _ _ )
                          (product_nat_trans_Pr2Commutes _ _ _ ))).
    simpl.
    apply product_nat_trans_univ_prop.
Defined.

End product_functor.

Definition Products_functor_precat : Products [C, D, hsD].
Proof.
  intros F G.
  apply functor_precat_product_cone.
Defined.


End def_functor_pointwise_prod.
