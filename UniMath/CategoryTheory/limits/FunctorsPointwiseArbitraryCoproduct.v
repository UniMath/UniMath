(** **********************************************************

Anders Mörtberg, 2016

************************************************************)

(** **********************************************************

Contents :

- Definition of a coproduct structure on a functor category
  by taking pointwise coproducts in the target category

Adapted from the binary version

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

Variables (F : I -> functor C D).

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

Definition arbitrary_coproduct_nat_trans_in_data i (c : C) :
  D ⟦ (F i) c, arbitrary_coproduct_functor c ⟧ :=
  ArbitraryCoproductIn _ _ (HD (fun j => (F j) c)) i.

Lemma is_nat_trans_arbitrary_coproduct_nat_trans_in_data i :
  is_nat_trans _ _ (arbitrary_coproduct_nat_trans_in_data i).
Proof.
intros c c' f; apply pathsinv0.
now eapply pathscomp0;[apply (ArbitraryCoproductOfArrowsIn I _ (HD (λ i, (F i) c)))|].
Qed.

Definition arbitrary_coproduct_nat_trans_in i : nat_trans (F i) arbitrary_coproduct_functor :=
  tpair _ _ (is_nat_trans_arbitrary_coproduct_nat_trans_in_data i).

Section vertex.

Variable A : functor C D.
Variable f : forall i, nat_trans (F i) A.

Definition arbitrary_coproduct_nat_trans_data c :
  arbitrary_coproduct_functor c --> A c :=
    ArbitraryCoproductArrow _ _ _ (fun i => f i c).

Lemma is_nat_trans_arbitrary_coproduct_nat_trans_data :
  is_nat_trans _ _ arbitrary_coproduct_nat_trans_data.
Proof.
intros a b k; simpl.
eapply pathscomp0.
apply (precompWithArbitraryCoproductArrow I D (HD (λ i : I, (F i) a)) (HD (λ i : I, (F i) b))).
apply pathsinv0.
eapply pathscomp0; [apply postcompWithArbitraryCoproductArrow|].
apply maponpaths, funextsec; intro i.
now rewrite (nat_trans_ax (f i)).
Qed.

Definition arbitrary_coproduct_nat_trans : nat_trans arbitrary_coproduct_functor A
  := tpair _ _ is_nat_trans_arbitrary_coproduct_nat_trans_data.

End vertex.

Definition functor_precat_arbitrary_coproduct_cocone
  : ArbitraryCoproductCocone I [C, D, hsD] F.
Proof.
simple refine (mk_ArbitraryCoproductCocone _ _ _ _ _ _).
- apply arbitrary_coproduct_functor.
- apply arbitrary_coproduct_nat_trans_in.
- simple refine (mk_isArbitraryCoproductCocone _ _ _ _ _ _ _).
  + apply functor_category_has_homsets.
  + intros A f.
    mkpair.
    * apply (tpair _ (arbitrary_coproduct_nat_trans A f)).
      abstract (intro i; apply (nat_trans_eq hsD); intro c;
                apply (ArbitraryCoproductInCommutes I D _ (HD (λ j, (F j) c)))).
    * abstract (
        intro t; apply subtypeEquality; simpl;
          [intro; apply impred; intro; apply (isaset_nat_trans hsD)|];
        apply (nat_trans_eq hsD); intro c;
        apply ArbitraryCoproductArrowUnique; intro i;
        apply (nat_trans_eq_pointwise (pr2 t i))).
Defined.

End arbitrary_coproduct_functor.

Definition ArbitraryCoproducts_functor_precat : ArbitraryCoproducts I [C, D, hsD].
Proof.
  intros F.
  apply functor_precat_arbitrary_coproduct_cocone.
Defined.

End def_functor_pointwise_arbitrary_coprod.