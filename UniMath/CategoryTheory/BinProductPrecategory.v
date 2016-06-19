
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Definition of the cartesian product of two precategories

- From a functor on a product of precategories to a functor on one of
  the categories by fixing the argument in the other component



************************************************************)


Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G ∙ F" := (functor_composite _ _ _ F G) (at level 35).

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Section one_binproduct_precategory.

Variables C D : precategory.

Definition binproduct_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists (C × D).
  exact (λ cd cd', pr1 cd --> pr1 cd' × pr2 cd --> pr2 cd').
Defined.

Definition binproduct_precategory_data : precategory_data.
Proof.
  exists binproduct_precategory_ob_mor.
  split.
  - intro cd.
    exact (dirprodpair (identity (pr1 cd)) (identity (pr2 cd))).
  - intros cd cd' cd'' fg fg'.
    exact (dirprodpair (pr1 fg ;; pr1 fg') (pr2 fg ;; pr2 fg')).
Defined.

Lemma is_precategory_binproduct_precategory_data : is_precategory binproduct_precategory_data.
Proof.
  repeat split; simpl; intros.
  - apply dirprodeq; apply id_left.
  - apply dirprodeq; apply id_right.
  - apply dirprodeq; apply assoc.
Qed.

Definition binproduct_precategory : precategory
  := tpair _ _ is_precategory_binproduct_precategory_data.

Definition has_homsets_binproduct_precategory (hsC : has_homsets C) (hsD : has_homsets D) :
  has_homsets binproduct_precategory.
Proof.
  intros a b.
  apply isasetdirprod.
  - apply hsC.
  - apply hsD.
Qed.

Definition ob1 (x : binproduct_precategory) : C := pr1 x.
Definition ob2 (x : binproduct_precategory) : D := pr2 x.
Definition mor1 (x x' : binproduct_precategory) (f : _ ⟦x, x'⟧) : _ ⟦ob1 x, ob1 x'⟧ := pr1 f.
Definition mor2 (x x' : binproduct_precategory) (f : _ ⟦x, x'⟧) : _ ⟦ob2 x, ob2 x'⟧ := pr2 f.

Section functor_fix_snd_arg.

Variable E : precategory.
Variable F: functor binproduct_precategory E.
Variable d: D.

Definition functor_fix_snd_arg_ob (c:C): E := F(tpair _ c d).
Definition functor_fix_snd_arg_mor (c c':C)(f: c --> c'): functor_fix_snd_arg_ob c --> functor_fix_snd_arg_ob c'.
Proof.
  apply (#F).
  split; simpl.
  exact f.
  exact (identity d).
Defined.
Definition functor_fix_snd_arg_data : functor_data C E.
Proof.
  red.
  exists functor_fix_snd_arg_ob.
  exact functor_fix_snd_arg_mor.
Defined.

Lemma is_functor_functor_fix_snd_arg_data: is_functor functor_fix_snd_arg_data.
Proof.
  red.
  split; red.
  + intros c.
    unfold functor_fix_snd_arg_data; simpl.
    unfold functor_fix_snd_arg_mor; simpl.
    unfold functor_fix_snd_arg_ob; simpl.
    assert (functor_id_inst := functor_id F).
    rewrite <- functor_id_inst.
    apply maponpaths.
    apply idpath.
  + intros c c' c'' f g.
    unfold functor_fix_snd_arg_data; simpl.
    unfold functor_fix_snd_arg_mor; simpl.
    assert (functor_comp_inst := functor_comp F (dirprodpair c d) (dirprodpair c' d) (dirprodpair c'' d)).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold binproduct_precategory; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_snd_arg: functor C E.
Proof.
  exists functor_fix_snd_arg_data.
  exact is_functor_functor_fix_snd_arg_data.
Defined.

End functor_fix_snd_arg.

Section nat_trans_fix_snd_arg.

Variable E : precategory.
Variable F F': functor binproduct_precategory E.
Variable α: F ⟶ F'.
Variable d: D.

Definition nat_trans_fix_snd_arg_data (c:C): functor_fix_snd_arg E F d c --> functor_fix_snd_arg E F' d c := α (tpair _ c d).

Lemma nat_trans_fix_snd_arg_ax: is_nat_trans _ _ nat_trans_fix_snd_arg_data.
Proof.
  red.
  intros c c' f.
  unfold nat_trans_fix_snd_arg_data, functor_fix_snd_arg; simpl.
  unfold functor_fix_snd_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_snd_arg: functor_fix_snd_arg E F d ⟶ functor_fix_snd_arg E F' d.
Proof.
  exists nat_trans_fix_snd_arg_data.
  exact nat_trans_fix_snd_arg_ax.
Defined.

End nat_trans_fix_snd_arg.

End one_binproduct_precategory.

Arguments ob1 { _ _ } _ .
Arguments ob2 { _ _ } _ .
Arguments mor1 { _ _ _ _ } _ .
Arguments mor2 { _ _ _ _ } _ .


(** Objects and morphisms in the product precategory of two precategories *)
Definition binprodcatpair {C D : precategory} (X : C) (Y : D) : binproduct_precategory C D.
Proof.
  exists X.
  exact Y.
Defined.

Local Notation "A ⊗ B" := (binprodcatpair A B) (at level 10).

Definition binprodcatmor {C D : precategory} {X X' : C} {Z Z' : D} (α : X --> X') (β : Z --> Z')
  : X ⊗ Z --> X' ⊗ Z'.
Proof.
  exists α.
  exact β.
Defined.

(* Define pairs of functors and functors from pr1 and pr2 *)
Section functors.

Definition binproduct_pair_functor_data {A B C D : precategory}
  (F : functor A C) (G : functor B D) :
  functor_data (binproduct_precategory A B) (binproduct_precategory C D).
Proof.
mkpair.
- intro x; apply (binprodcatpair (F (pr1 x)) (G (pr2 x))).
- intros x y f; simpl; apply (binprodcatmor (# F (pr1 f)) (# G (pr2 f))).
Defined.

Definition binproduct_pair_functor {A B C D : precategory}
  (F : functor A C) (G : functor B D) :
  functor (binproduct_precategory A B) (binproduct_precategory C D).
Proof.
apply (tpair _ (binproduct_pair_functor_data F G)).
abstract (split;
  [ intro x; simpl; rewrite !functor_id; apply idpath
  | intros x y z f g; simpl; rewrite !functor_comp; apply idpath]).
Defined.

Definition pr1_functor_data (A B : precategory) :
  functor_data (binproduct_precategory A B) A.
Proof.
mkpair.
- intro x; apply (pr1 x).
- intros x y f; simpl; apply (pr1 f).
Defined.

Definition pr1_functor (A B : precategory) :
  functor (binproduct_precategory A B) A.
Proof.
apply (tpair _ (pr1_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition pr2_functor_data (A B : precategory) :
  functor_data (binproduct_precategory A B) B.
Proof.
mkpair.
- intro x; apply (pr2 x).
- intros x y f; simpl; apply (pr2 f).
Defined.

Definition pr2_functor (A B : precategory) :
  functor (binproduct_precategory A B) B.
Proof.
apply (tpair _ (pr2_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition bindelta_functor_data (C : precategory) :
  functor_data C (binproduct_precategory C C).
Proof.
mkpair.
- intro x; apply (binprodcatpair x x).
- intros x y f; simpl; apply (binprodcatmor f f).
Defined.

Definition bindelta_functor (C : precategory) :
  functor C (binproduct_precategory C C).
Proof.
apply (tpair _ (bindelta_functor_data C)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

End functors.