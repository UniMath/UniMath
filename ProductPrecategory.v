Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import UnicodeNotations.
Require Import UniMath.RezkCompletion.whiskering.
Require Import SubstSystems.Auxiliary.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G ∙ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Section def_product_precategory.

Variables C D : precategory.

Definition product_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists (C × D).
  exact (λ cd cd', pr1 cd ⇒ pr1 cd' × pr2 cd ⇒ pr2 cd').
Defined.

Definition product_precategory_data : precategory_data.
Proof.
  exists product_precategory_ob_mor.
  split.
  - intro cd.
    exact (dirprodpair (identity (pr1 cd)) (identity (pr2 cd))).
  - intros cd cd' cd'' fg fg'.
    exact (dirprodpair (pr1 fg ;; pr1 fg') (pr2 fg ;; pr2 fg')).
Defined.

Lemma is_precategory_product_precategory_data : is_precategory product_precategory_data.
Proof.
  repeat split; simpl; intros.
  - apply dirprodeq; apply id_left.
  - apply dirprodeq; apply id_right.
  - apply dirprodeq; apply assoc.
Qed.

Definition product_precategory : precategory 
  := tpair _ _ is_precategory_product_precategory_data.

Definition has_homsets_product_precategory (hsC : has_homsets C) (hsD : has_homsets D) :
  has_homsets product_precategory.
Proof.
  intros a b.
  apply isasetdirprod.
  - apply hsC.
  - apply hsD.
Qed.
  

End def_product_precategory.

