Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.
Require Import UnicodeNotations.
Require Import RezkCompletion.limits.coproducts.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Section def_functor_pointwise_coprod.

Variable C D : precategory.
Variable HD : Coproducts D.

Section coproduct_functor.

Variables F G : functor C D.


Local Notation "c ⊗ d" := (CoproductObject _ (HD c d))(at level 45).

Definition coproduct_functor_ob (c : C) : D := F c ⊗ G c.

Definition coproduct_functor_mor (c c' : C) (f : c ⇒ c') 
  : coproduct_functor_ob c ⇒ coproduct_functor_ob c'
  := CoproductOfArrows _ _ _ (#F f) (#G f).

Definition coproduct_functor_data : functor_data C D.
Proof.
  exists coproduct_functor_ob.
  exact coproduct_functor_mor.
Defined.


Lemma is_functor_coproduct_functor_data : is_functor coproduct_functor_data.
Proof.
  split; simpl; intros.
  - apply pathsinv0.
    apply Coproduct_endo_is_identity.
    + unfold coproduct_functor_mor.
      rewrite CoproductOfArrowsIn1.
      rewrite functor_id.
      apply id_left.
    + unfold coproduct_functor_mor.
      rewrite CoproductOfArrowsIn2.
      rewrite functor_id.
      apply id_left.
  - unfold coproduct_functor_mor.
    unfold CoproductOfArrows.
    apply pathsinv0.
    apply CoproductArrowUnique.
    + rewrite assoc. simpl in *.
      set (H:= CoproductIn1Commutes ).
      set (H2 := H D _ _ (HD (F a) (G a))).
      rewrite H2. 
      rewrite <- assoc.
      rewrite functor_comp.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply CoproductIn1Commutes.
    + rewrite assoc.
      set (H:= CoproductIn2Commutes D _ _ (HD (F a) (G a))).
      rewrite H.
      rewrite functor_comp.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply CoproductIn2Commutes.
Qed.

Definition coproduct_functor : functor C D := tpair _ _ is_functor_coproduct_functor_data.

Variable A : functor C D.
Variable f : F ⟶ A.
Variable g : G ⟶ A.

Definition coproduct_nat_trans_data : ∀ c, coproduct_functor c ⇒ A c.
Proof.
  intro c.
  apply CoproductArrow.
  - exact (f c).
  - exact (g c).
Defined.

Lemma is_nat_trans_coproduct_nat_trans_data : is_nat_trans _ _ coproduct_nat_trans_data.
Proof.
  intros a b k.
  simpl.
  unfold coproduct_functor_mor.
  unfold coproduct_nat_trans_data.
  simpl.
  set (XX:=precompWithCoproductArrow).
  set (X1 := XX D _ _ (HD (F a) (G a))).
  set (X2 := X1 _ _ (HD (F b) (G b))).
  rewrite X2.
  admit.
Qed.

End coproduct_functor.


End def_functor_pointwise_coprod.













