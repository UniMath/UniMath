(** **********************************************************

Anders Mörtberg, 2016

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.arbitrary_coproducts.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section def_functor_pointwise_arbitrary_coprod.

Variables (I : UU) (C D : precategory).
Variable HD : ArbitraryCoproducts I D.
Variable hsD : has_homsets D.

Section arbitrary_coproduct_functor.

Variables (F : forall (i : I), functor C D).

Definition arbitrary_coproduct_functor_ob (c : C) : D
  := ArbitraryCoproductObject _ _ (HD (fun i => F i c)).

Definition arbitrary_coproduct_functor_mor (c c' : C) (f : c --> c')
  : arbitrary_coproduct_functor_ob c --> arbitrary_coproduct_functor_ob c' :=
  ArbitraryCoproductOfArrows _ _ _ _ (fun i => # (F i) f).

Definition arbitrary_coproduct_functor_data : functor_data C D.
Proof.
  exists arbitrary_coproduct_functor_ob.
  exact arbitrary_coproduct_functor_mor.
Defined.

Lemma is_functor_arbitrary_coproduct_functor_data :
  is_functor arbitrary_coproduct_functor_data.
Proof.
split; simpl; intros.
- unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply ArbitraryCoproduct_endo_is_identity; intro i.
    unfold arbitrary_coproduct_functor_mor.
    eapply pathscomp0; [apply (ArbitraryCoproductOfArrowsIn _ _ (HD (λ i, (F i) a)))|].
    now simpl; rewrite functor_id, id_left.
- unfold functor_compax; simpl; unfold arbitrary_coproduct_functor_mor.
  intros; simpl in *.
  apply pathsinv0.
  eapply pathscomp0.
  apply ArbitraryCoproductOfArrows_comp.
  apply maponpaths, funextsec; intro i.
  now rewrite functor_comp.
Qed.

Definition arbitrary_coproduct_functor : functor C D :=
  tpair _ _ is_functor_arbitrary_coproduct_functor_data.

Lemma arbitrary_coproduct_of_functors_eq_arbitrary_coproduct_functor :
  arbitrary_coproduct_of_functors _ HD F = arbitrary_coproduct_functor.
Proof.
now apply (functor_eq _ _ hsD).
Defined.

End arbitrary_coproduct_functor.
End def_functor_pointwise_arbitrary_coprod.