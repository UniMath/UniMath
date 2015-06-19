Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import UnicodeNotations.
Require Import UniMath.RezkCompletion.limits.products.
Require Import Auxiliary.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

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
    apply ProductArrowUnique.
    + rewrite id_left.
      rewrite functor_id.
      apply pathsinv0.
      apply id_right.
    + rewrite id_left.
      rewrite functor_id.
      apply pathsinv0.
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

End product_functor.

End def_functor_pointwise_prod.
