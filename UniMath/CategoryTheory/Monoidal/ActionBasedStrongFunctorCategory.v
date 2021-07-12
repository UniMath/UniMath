(** organizes the (action-based) strong functors between two fixed precategories into a (pre-)category

Author: Ralph Matthes 2021
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.Actions.
Require Import UniMath.CategoryTheory.Monoidal.ActionBasedStrength.

Local Open Scope cat.

Section Strong_Functor_Category.

Context (Mon_V : monoidal_precat).

Local Definition V := monoidal_precat_precat Mon_V.

Context {A A': precategory}.
Context (actn : action Mon_V A)(actn' : action Mon_V A').

Local Definition odot := pr1 actn.
Local Definition odot' := pr1 actn'.

Notation "X ⊙ Y" := (odot (X , Y)) (at level 31).
Notation "f #⊙ g" := (#odot (f #, g)) (at level 31).
Notation "X ⊙' Y" := (odot' (X , Y)) (at level 31).
Notation "f #⊙' g" := (#odot' (f #, g)) (at level 31).

Local Definition F (FF : actionbased_strong_functor Mon_V actn actn') : A ⟶ A' := pr1 FF.
Local Definition ζ (FF : actionbased_strong_functor Mon_V actn actn') := pr12 FF.

Section Strong_Functor_Category_mor.

  Context (FF GG : actionbased_strong_functor Mon_V actn actn').

  Context (η : F FF ⟹ F GG).

  Definition Strong_Functor_Category_mor_diagram (a: A) (v: V) : UU :=
    ζ FF (a,v) · η (a ⊙ v) = η a #⊙' id v · ζ GG (a,v).

End Strong_Functor_Category_mor.

Definition Strong_Functor_Category_Mor (FF GG : actionbased_strong_functor Mon_V actn actn'): UU :=
  ∑ (η : F FF ⟹ F GG), ∏ a v, Strong_Functor_Category_mor_diagram FF GG η a v.

Lemma Strong_Functor_Category_Mor_eq (hsA': has_homsets A') (FF GG : actionbased_strong_functor Mon_V actn actn')
      (sη sη' : Strong_Functor_Category_Mor FF GG) :
  pr1 sη = pr1 sη' -> sη = sη'.
Proof.
intros H.
apply subtypePath; trivial.
now intros α; repeat (apply impred; intro); apply hsA'.
Qed.

Local Lemma Strong_Functor_Category_Mor_id_subproof (FF : actionbased_strong_functor Mon_V actn actn') a v :
  Strong_Functor_Category_mor_diagram FF FF (nat_trans_id (F FF)) a v.
Proof.
  red.
  change (ζ FF (a, v) · nat_trans_id (F FF) (a ⊙ v) = # odot' (id (F FF a, v)) · ζ FF (a, v)).
  rewrite functor_id.
  now rewrite id_left, id_right.
Qed.

Definition Strong_Functor_Category_Mor_id (FF : actionbased_strong_functor Mon_V actn actn') :
  Strong_Functor_Category_Mor FF FF := (nat_trans_id (F FF),,Strong_Functor_Category_Mor_id_subproof FF).

Local Lemma Strong_Functor_Category_Mor_comp_subproof (FF GG HH : actionbased_strong_functor Mon_V actn actn')
      (sη : Strong_Functor_Category_Mor FF GG) (sη' : Strong_Functor_Category_Mor GG HH) a v :
  Strong_Functor_Category_mor_diagram FF HH (nat_trans_comp _ _ _ (pr1 sη) (pr1 sη')) a v.
Proof.
  induction sη as [η ηisstrong]; induction sη' as [η' η'isstrong].
  red.
  cbn.
  rewrite <- (id_left (id v)).
  change (ζ FF (a, v) · (η (a ⊙ v) · η' (a ⊙ v)) = # odot' ((η a #, id v) · (η' a #, id v))  · ζ HH (a, v)).
  rewrite functor_comp.
  etrans.
  { rewrite assoc. apply cancel_postcomposition. apply ηisstrong. }
  do 2 rewrite <- assoc.
  apply maponpaths.
  apply η'isstrong.
Qed.

Definition Strong_Functor_Category_Mor_comp  (FF GG HH : actionbased_strong_functor Mon_V actn actn')
           (sη : Strong_Functor_Category_Mor FF GG) (sη' : Strong_Functor_Category_Mor GG HH) :
  Strong_Functor_Category_Mor FF HH :=
  (nat_trans_comp _ _ _ (pr1 sη) (pr1 sη'),, Strong_Functor_Category_Mor_comp_subproof FF GG HH sη sη').

Definition Strong_Functor_precategory_data : precategory_data.
Proof.
  apply (tpair _ (actionbased_strong_functor Mon_V actn actn',, Strong_Functor_Category_Mor)),
  (Strong_Functor_Category_Mor_id,, Strong_Functor_Category_Mor_comp).
Defined.

Lemma is_precategory_Strong_Functor_precategory_data (hsA': has_homsets A') :
  is_precategory Strong_Functor_precategory_data.
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat split.
  - intros FF GG η; apply Strong_Functor_Category_Mor_eq; try assumption.
    apply (id_left(C:= functor_precategory A A' hsA')).
- intros FF GG η; apply Strong_Functor_Category_Mor_eq; try assumption.
    apply (id_right(C:= functor_precategory A A' hsA')).
- intros FF GG HH II η η' η''; apply Strong_Functor_Category_Mor_eq; try assumption.
  apply (assoc(C:= functor_precategory A A' hsA')).
Qed.

Definition Strong_Functor_precategory (hsA': has_homsets A') : precategory :=
  (Strong_Functor_precategory_data,, is_precategory_Strong_Functor_precategory_data hsA').

Lemma has_homsets_Strong_Functor_precategory (hsA': has_homsets A') :
  has_homsets (Strong_Functor_precategory hsA').
Proof.
  intros FF GG.
  apply (isofhleveltotal2 2).
  * apply isaset_nat_trans, hsA'.
  * intros η.
    apply isasetaprop.
    apply impred; intros a; apply impred; intros v.
    apply hsA'.
Qed.

Definition Strong_Functor_category (hsA': has_homsets A') : category :=
  (Strong_Functor_precategory hsA',, has_homsets_Strong_Functor_precategory hsA').

Definition Strong_FunctorForgetfulFunctor (hsA': has_homsets A') :
  functor (Strong_Functor_precategory hsA') (functor_precategory A A' hsA').
Proof.
use tpair.
- use tpair.
  + intros FF; apply(F FF).
  + intros FF GG η; apply η.
- abstract (now split).
Defined.

Lemma SignatureForgetfulFunctorFaithful (hsA': has_homsets A') :
  faithful (Strong_FunctorForgetfulFunctor hsA').
Proof.
  intros FF GG.
  apply isinclbetweensets.
  + apply has_homsets_Strong_Functor_precategory; try assumption.
  + apply functor_category_has_homsets.
  + apply Strong_Functor_Category_Mor_eq; try assumption.
Qed.

End Strong_Functor_Category.
