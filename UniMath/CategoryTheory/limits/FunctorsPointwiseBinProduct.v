(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Definition of a binary product structure on a functor category by
  taking pointwise binary products in the target category



************************************************************)


Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.binproducts.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

(** Goal: lift binary products from the target (pre)category to the
    functor (pre)category *)

Section def_functor_pointwise_binprod.

Variable C D : precategory.
Variable HD : BinProducts D.
Variable hsD : has_homsets D.

Section BinProduct_of_functors.

Variables F G : functor C D.


Local Notation "c ⊗ d" := (BinProductObject _ (HD c d))(at level 45).

Definition BinProduct_of_functors_ob (c : C) : D := F c ⊗ G c.

Definition BinProduct_of_functors_mor (c c' : C) (f : c --> c')
  : BinProduct_of_functors_ob c --> BinProduct_of_functors_ob c'
  := BinProductOfArrows _ _ _ (#F f) (#G f).

Definition BinProduct_of_functors_data : functor_data C D.
Proof.
  exists BinProduct_of_functors_ob.
  exact BinProduct_of_functors_mor.
Defined.


Lemma is_functor_BinProduct_of_functors_data : is_functor BinProduct_of_functors_data.
Proof.
  split; simpl; intros.
  - red; intros; simpl in *.
    apply pathsinv0.
    unfold BinProduct_of_functors_mor.
    apply BinProduct_endo_is_identity.
    + rewrite BinProductOfArrowsPr1.
      rewrite functor_id.
      apply id_right.
    + rewrite BinProductOfArrowsPr2.
      rewrite functor_id.
      apply id_right.
  - red; intros; simpl in *.
    unfold BinProduct_of_functors_mor.
    do 2 rewrite functor_comp.
    apply pathsinv0.
    apply BinProductOfArrows_comp.
Qed.

Definition BinProduct_of_functors : functor C D :=
  tpair _ _ is_functor_BinProduct_of_functors_data.

Lemma BinProduct_of_functors_alt_eq_BinProduct_of_functors :
  BinProduct_of_functors_alt HD F G = BinProduct_of_functors.
Proof.
now apply (functor_eq _ _ hsD).
Defined.

Definition binproduct_nat_trans_pr1_data : Π c, BinProduct_of_functors c --> F c
  := λ c : C, BinProductPr1 _ (HD (F c) (G c)).

Lemma is_nat_trans_binproduct_nat_trans_pr1_data
  : is_nat_trans _ _ binproduct_nat_trans_pr1_data.
Proof.
  red.
  intros c c' f.
  unfold binproduct_nat_trans_pr1_data.
  unfold BinProduct_of_functors. simpl.
  unfold BinProduct_of_functors_mor.
  apply BinProductOfArrowsPr1.
Qed.

Definition binproduct_nat_trans_pr1 : nat_trans _ _
  := tpair _ _ is_nat_trans_binproduct_nat_trans_pr1_data.


Definition binproduct_nat_trans_pr2_data : Π c, BinProduct_of_functors c --> G c
  := λ c : C, BinProductPr2 _ (HD (F c) (G c)).

Lemma is_nat_trans_binproduct_nat_trans_pr2_data
  : is_nat_trans _ _ binproduct_nat_trans_pr2_data.
Proof.
  red.
  intros c c' f.
  unfold binproduct_nat_trans_pr2_data.
  unfold BinProduct_of_functors. simpl.
  unfold BinProduct_of_functors_mor.
  apply BinProductOfArrowsPr2.
Qed.

Definition binproduct_nat_trans_pr2 : nat_trans _ _
  := tpair _ _ is_nat_trans_binproduct_nat_trans_pr2_data.


Section vertex.

(** The product morphism of a diagram with vertex [A] *)

Variable A : functor C D.
Variable f : A ⟶ F.
Variable g : A ⟶ G.

Definition binproduct_nat_trans_data : Π c,  A c --> BinProduct_of_functors c.
Proof.
  intro c.
  apply BinProductArrow.
  - exact (f c).
  - exact (g c).
Defined.

Lemma is_nat_trans_binproduct_nat_trans_data : is_nat_trans _ _ binproduct_nat_trans_data.
Proof.
  intros a b k.
  simpl.
  unfold BinProduct_of_functors_mor.
  unfold binproduct_nat_trans_data.
  set (XX:=postcompWithBinProductArrow).
  set (X1 := XX D _ _ (HD (F b) (G b))).
  set (X2 := X1 _ _ (HD (F a) (G a))).
  rewrite X2.
  clear X2 X1 XX.
  set (XX:=precompWithBinProductArrow).
  set (X1 := XX D _ _ (HD (F b) (G b))).
  rewrite X1.
  rewrite (nat_trans_ax f).
  rewrite (nat_trans_ax g).
  apply idpath.
Qed.

Definition binproduct_nat_trans : nat_trans _ _
  := tpair _ _ is_nat_trans_binproduct_nat_trans_data.

Lemma binproduct_nat_trans_Pr1Commutes :
  nat_trans_comp _ _ _ binproduct_nat_trans binproduct_nat_trans_pr1  = f.
Proof.
  apply nat_trans_eq.
  - apply hsD.
  - intro c; simpl.
    apply BinProductPr1Commutes.
Qed.

Lemma binproduct_nat_trans_Pr2Commutes :
  nat_trans_comp _ _ _ binproduct_nat_trans binproduct_nat_trans_pr2  = g.
Proof.
  apply nat_trans_eq.
  - apply hsD.
  - intro c; simpl.
    apply BinProductPr2Commutes.
Qed.

End vertex.

Lemma binproduct_nat_trans_univ_prop (A : [C, D, hsD])
  (f : (A --> (F:[C,D,hsD]))) (g : A --> (G:[C,D,hsD])) :
   Π
   t : Σ fg : A --> (BinProduct_of_functors:[C,D,hsD]),
       fg ;; (binproduct_nat_trans_pr1 : (BinProduct_of_functors:[C,D,hsD]) --> F) = f
      ×
       fg ;; (binproduct_nat_trans_pr2 : (BinProduct_of_functors:[C,D,hsD]) --> G) = g,
   t =
   tpair
     (λ fg : A --> (BinProduct_of_functors:[C,D,hsD]),
      fg ;; (binproduct_nat_trans_pr1 : (BinProduct_of_functors:[C,D,hsD]) --> F) = f
   ×
      fg ;; (binproduct_nat_trans_pr2 : (BinProduct_of_functors:[C,D,hsD]) --> G) = g)
     (binproduct_nat_trans A f g)
     (dirprodpair (binproduct_nat_trans_Pr1Commutes A f g)
        (binproduct_nat_trans_Pr2Commutes A f g)).
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
      unfold binproduct_nat_trans.
      simpl.
      unfold binproduct_nat_trans_data.
      apply BinProductArrowUnique.
      * apply (nat_trans_eq_pointwise ta).
      * apply (nat_trans_eq_pointwise tb).
Qed.

Definition functor_precat_binproduct_cone
  : BinProductCone [C, D, hsD] F G.
Proof.
simple refine (mk_BinProductCone _ _ _ _ _ _ _).
- apply BinProduct_of_functors.
- apply binproduct_nat_trans_pr1.
- apply binproduct_nat_trans_pr2.
- simple refine (mk_isBinProductCone _ _ _ _ _ _ _ _).
  + apply functor_category_has_homsets.
  + intros A f g.
    exists (tpair _ (binproduct_nat_trans A f g)
             (dirprodpair (binproduct_nat_trans_Pr1Commutes _ _ _ )
                          (binproduct_nat_trans_Pr2Commutes _ _ _ ))).
    simpl.
    apply binproduct_nat_trans_univ_prop.
Defined.

End BinProduct_of_functors.

Definition BinProducts_functor_precat : BinProducts [C, D, hsD].
Proof.
  intros F G.
  apply functor_precat_binproduct_cone.
Defined.


End def_functor_pointwise_binprod.
