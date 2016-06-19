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
Require Import UniMath.CategoryTheory.limits.coproducts.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section def_functor_pointwise_coprod.

Variables (I : UU) (C D : precategory).
Variable HD : Coproducts I D.
Variable hsD : has_homsets D.

Section coproduct_functor.

Variables (F : I -> functor C D).

Definition coproduct_functor_ob (c : C) : D
  := CoproductObject _ _ (HD (fun i => F i c)).

Definition coproduct_functor_mor (c c' : C) (f : c --> c')
  : coproduct_functor_ob c --> coproduct_functor_ob c' :=
  CoproductOfArrows _ _ _ _ (fun i => # (F i) f).

Definition coproduct_functor_data : functor_data C D.
Proof.
  exists coproduct_functor_ob.
  exact coproduct_functor_mor.
Defined.

Lemma is_functor_coproduct_functor_data :
  is_functor coproduct_functor_data.
Proof.
split; simpl; intros.
- unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply Coproduct_endo_is_identity; intro i.
    unfold coproduct_functor_mor.
    eapply pathscomp0; [apply (CoproductOfArrowsIn _ _ (HD (λ i, (F i) a)))|].
    now simpl; rewrite functor_id, id_left.
- unfold functor_compax; simpl; unfold coproduct_functor_mor.
  intros; simpl in *.
  apply pathsinv0.
  eapply pathscomp0.
  apply CoproductOfArrows_comp.
  apply maponpaths, funextsec; intro i.
  now rewrite functor_comp.
Qed.

Definition coproduct_functor : functor C D :=
  tpair _ _ is_functor_coproduct_functor_data.

Lemma coproduct_of_functors_eq_coproduct_functor :
  coproduct_of_functors _ HD F = coproduct_functor.
Proof.
now apply (functor_eq _ _ hsD).
Defined.

Definition coproduct_nat_trans_in_data i (c : C) :
  D ⟦ (F i) c, coproduct_functor c ⟧ :=
  CoproductIn _ _ (HD (fun j => (F j) c)) i.

Lemma is_nat_trans_coproduct_nat_trans_in_data i :
  is_nat_trans _ _ (coproduct_nat_trans_in_data i).
Proof.
intros c c' f; apply pathsinv0.
now eapply pathscomp0;[apply (CoproductOfArrowsIn I _ (HD (λ i, (F i) c)))|].
Qed.

Definition coproduct_nat_trans_in i : nat_trans (F i) coproduct_functor :=
  tpair _ _ (is_nat_trans_coproduct_nat_trans_in_data i).

Section vertex.

Variable A : functor C D.
Variable f : forall i, nat_trans (F i) A.

Definition coproduct_nat_trans_data c :
  coproduct_functor c --> A c :=
    CoproductArrow _ _ _ (fun i => f i c).

Lemma is_nat_trans_coproduct_nat_trans_data :
  is_nat_trans _ _ coproduct_nat_trans_data.
Proof.
intros a b k; simpl.
eapply pathscomp0.
apply (precompWithCoproductArrow I D (HD (λ i : I, (F i) a)) (HD (λ i : I, (F i) b))).
apply pathsinv0.
eapply pathscomp0; [apply postcompWithCoproductArrow|].
apply maponpaths, funextsec; intro i.
now rewrite (nat_trans_ax (f i)).
Qed.

Definition coproduct_nat_trans : nat_trans coproduct_functor A
  := tpair _ _ is_nat_trans_coproduct_nat_trans_data.

End vertex.

Definition functor_precat_coproduct_cocone
  : CoproductCocone I [C, D, hsD] F.
Proof.
simple refine (mk_CoproductCocone _ _ _ _ _ _).
- apply coproduct_functor.
- apply coproduct_nat_trans_in.
- simple refine (mk_isCoproductCocone _ _ _ _ _ _ _).
  + apply functor_category_has_homsets.
  + intros A f.
    mkpair.
    * apply (tpair _ (coproduct_nat_trans A f)).
      abstract (intro i; apply (nat_trans_eq hsD); intro c;
                apply (CoproductInCommutes I D _ (HD (λ j, (F j) c)))).
    * abstract (
        intro t; apply subtypeEquality; simpl;
          [intro; apply impred; intro; apply (isaset_nat_trans hsD)|];
        apply (nat_trans_eq hsD); intro c;
        apply CoproductArrowUnique; intro i;
        apply (nat_trans_eq_pointwise (pr2 t i))).
Defined.

End coproduct_functor.

Definition Coproducts_functor_precat : Coproducts I [C, D, hsD].
Proof.
  intros F.
  apply functor_precat_coproduct_cocone.
Defined.

End def_functor_pointwise_coprod.