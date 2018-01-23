
(** **********************************************************

Benedikt Ahrens, Ralph Matthes, Peter LeFanu Lumsdaine

SubstitutionSystems

2015

************************************************************)


(** **********************************************************

Contents :

- Definition of the cartesian product of two precategories

- From a functor on a product of precategories to a functor on one of
  the categories by fixing the argument in the other component

By PLL:

- Definition of the unit precategory

- Definition of the associator functors

- Definition of the pair of two functors: A × C → B × D
  given A → B and C → D

************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.

Definition precategory_binproduct_mor (C D : precategory_ob_mor) (cd cd' : C × D) := pr1 cd --> pr1 cd' × pr2 cd --> pr2 cd'.

Definition precategory_binproduct_ob_mor (C D : precategory_ob_mor) : precategory_ob_mor
  := tpair _ _ (precategory_binproduct_mor C D).

Definition precategory_binproduct_data (C D : precategory_data) : precategory_data.
Proof.
  exists (precategory_binproduct_ob_mor C D).
  split.
  - intro cd.
    exact (dirprodpair (identity (pr1 cd)) (identity (pr2 cd))).
  - intros cd cd' cd'' fg fg'.
    exact (dirprodpair (pr1 fg · pr1 fg') (pr2 fg · pr2 fg')).
Defined.

Section precategory_binproduct.

Variables C D : precategory.

Lemma is_precategory_precategory_binproduct_data : is_precategory (precategory_binproduct_data C D).
Proof.
  repeat split; simpl; intros.
  - apply dirprodeq; apply id_left.
  - apply dirprodeq; apply id_right.
  - apply dirprodeq; apply assoc.
Qed.

Definition precategory_binproduct : precategory
  := tpair _ _ is_precategory_precategory_binproduct_data.

Definition has_homsets_precategory_binproduct (hsC : has_homsets C) (hsD : has_homsets D) :
  has_homsets precategory_binproduct.
Proof.
  intros a b.
  apply isasetdirprod.
  - apply hsC.
  - apply hsD.
Qed.

Definition ob1 (x : precategory_binproduct) : C := pr1 x.
Definition ob2 (x : precategory_binproduct) : D := pr2 x.
Definition mor1 (x x' : precategory_binproduct) (f : _ ⟦x, x'⟧) : _ ⟦ob1 x, ob1 x'⟧ := pr1 f.
Definition mor2 (x x' : precategory_binproduct) (f : _ ⟦x, x'⟧) : _ ⟦ob2 x, ob2 x'⟧ := pr2 f.



End precategory_binproduct.

Arguments ob1 { _ _ } _ .
Arguments ob2 { _ _ } _ .
Arguments mor1 { _ _ _ _ } _ .
Arguments mor2 { _ _ _ _ } _ .
Local Notation "C × D" := (precategory_binproduct C D) (at level 75, right associativity).

(** Objects and morphisms in the product precategory of two precategories *)
Definition precatbinprodpair {C D : precategory} (X : C) (Y : D) : precategory_binproduct C D
  := dirprodpair X Y.

Local Notation "A ⊗ B" := (precatbinprodpair A B) (at level 10).

Definition precatbinprodmor {C D : precategory} {X X' : C} {Z Z' : D} (α : X --> X') (β : Z --> Z')
  : X ⊗ Z --> X' ⊗ Z'
  := dirprodpair α β.

(** Isos in product precategories *)
Definition precatbinprodiso {C D : precategory} {X X' : C} {Z Z' : D} (α : iso X X') (β : iso Z Z')
  : iso (X ⊗ Z) (X' ⊗ Z').
Proof.
  set (f := precatbinprodmor α β).
  set (g := precatbinprodmor (iso_inv_from_iso α) (iso_inv_from_iso β)).
  exists f.
  apply (is_iso_qinv f g).
  use tpair.
  - apply pathsdirprod.
    apply iso_inv_after_iso.
    apply iso_inv_after_iso.
  - apply pathsdirprod.
    apply iso_after_iso_inv.
    apply iso_after_iso_inv.
Defined.

Definition precatbinprodiso_inv {C D : precategory} {X X' : C} {Z Z' : D}
  (α : iso X X') (β : iso Z Z')
  : precatbinprodiso (iso_inv_from_iso α) (iso_inv_from_iso β)
  = iso_inv_from_iso (precatbinprodiso α β).
Proof.
  apply inv_iso_unique.
  apply pathsdirprod.
  - apply iso_inv_after_iso.
  - apply iso_inv_after_iso.
Defined.

(** Associativity functors *)
Section assoc.

Definition precategory_binproduct_assoc_data (C0 C1 C2 : precategory_data)
  : functor_data (precategory_binproduct_data C0 (precategory_binproduct_data C1 C2))
                 (precategory_binproduct_data (precategory_binproduct_data C0 C1) C2).
Proof.
  use tpair.
  (* functor_on_objects *) intros c. exact (tpair _ (tpair _ (pr1 c) (pr1 (pr2 c))) (pr2 (pr2 c))).
  (* functor_on_morphisms *) intros a b c. exact (tpair _ (tpair _ (pr1 c) (pr1 (pr2 c))) (pr2 (pr2 c))).
Defined.

Definition precategory_binproduct_assoc (C0 C1 C2 : precategory)
  : functor (C0 × (C1 × C2)) ((C0 × C1) × C2).
Proof.
  exists (precategory_binproduct_assoc_data _ _ _). split.
  (* functor_id *) intros c. simpl; apply paths_refl.
  (* functor_comp *) intros c0 c1 c2 f g. simpl; apply paths_refl.
Defined.

Definition precategory_binproduct_unassoc_data (C0 C1 C2 : precategory_data)
  : functor_data (precategory_binproduct_data (precategory_binproduct_data C0 C1) C2)
                 (precategory_binproduct_data C0 (precategory_binproduct_data C1 C2)).
Proof.
  use tpair.
  (* functor_on_objects *) intros c. exact (tpair _ (pr1 (pr1 c)) (tpair _ (pr2 (pr1 c)) (pr2 c))).
  (* functor_on_morphisms *) intros a b c. exact (tpair _ (pr1 (pr1 c)) (tpair _ (pr2 (pr1 c)) (pr2 c))).
Defined.

Definition precategory_binproduct_unassoc (C0 C1 C2 : precategory)
  : functor ((C0 × C1) × C2) (C0 × (C1 × C2)).
Proof.
  exists (precategory_binproduct_unassoc_data _ _ _). split.
  (* functor_id *) intros c. simpl; apply paths_refl.
  (* functor_comp *) intros c0 c1 c2 f g. simpl; apply paths_refl.
Defined.

End assoc.

(** The terminal precategory *)

Section unit_precategory.

Definition unit_precategory : precategory.
Proof.
  use tpair. use tpair.
  (* ob, mor *) exists unit. intros; exact unit.
  (* identity, comp *) split; intros; constructor.
  (* id_left *) simpl; split; try split; intros; apply isProofIrrelevantUnit.
Defined.

Definition unit_functor C : functor C unit_precategory.
Proof.
  use tpair. use tpair.
  (* functor_on_objects *) intros; exact tt.
  (* functor_on_morphisms *) intros F a b; apply identity.
  split.
  (* functor_id *) intros x; apply paths_refl.
  (* functor_comp *) intros x y z w v; apply paths_refl.
Defined.

End unit_precategory.

(** Fixing one argument of C × D -> E results in a functor *)
Section functor_fix_fst_arg.

Variable C D E : precategory.
Variable F : functor (precategory_binproduct C D) E.
Variable c : C.

Definition functor_fix_fst_arg_ob (d:D) : E := F (tpair _ c d).
Definition functor_fix_fst_arg_mor (d d' : D) (f : d --> d') : functor_fix_fst_arg_ob d --> functor_fix_fst_arg_ob d'.
Proof.
  apply (#F).
  exact (dirprodpair (identity c) f).
Defined.

Definition functor_fix_fst_arg_data : functor_data D E
  := tpair _ functor_fix_fst_arg_ob functor_fix_fst_arg_mor.

Lemma is_functor_functor_fix_fst_arg_data: is_functor functor_fix_fst_arg_data.
Proof.
  red.
  split; red.
  + intros d.
    unfold functor_fix_fst_arg_data; simpl.
    unfold functor_fix_fst_arg_mor; simpl.
    unfold functor_fix_fst_arg_ob; simpl.
    assert (functor_id_inst := functor_id F).
    rewrite <- functor_id_inst.
    apply maponpaths.
    apply idpath.
  + intros d d' d'' f g.
    unfold functor_fix_fst_arg_data; simpl.
    unfold functor_fix_fst_arg_mor; simpl.
    assert (functor_comp_inst := @functor_comp _ _ F (dirprodpair c d) (dirprodpair c d') (dirprodpair c d'')).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold precategory_binproduct; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_fst_arg : functor D E
  := tpair _ functor_fix_fst_arg_data is_functor_functor_fix_fst_arg_data.

End functor_fix_fst_arg.

Section nat_trans_fix_fst_arg.

Variable C D E : precategory.
Variable F F': functor (precategory_binproduct C D) E.
Variable α: F ⟹ F'.
Variable c: C.

Definition nat_trans_fix_fst_arg_data (d:D): functor_fix_fst_arg C D E F c d --> functor_fix_fst_arg C D E F' c d := α (tpair _ c d).

Lemma nat_trans_fix_fst_arg_ax: is_nat_trans _ _ nat_trans_fix_fst_arg_data.
Proof.
  red.
  intros d d' f.
  unfold nat_trans_fix_fst_arg_data, functor_fix_fst_arg; simpl.
  unfold functor_fix_fst_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_fst_arg: functor_fix_fst_arg C D E F c ⟹ functor_fix_fst_arg C D E F' c
  := tpair _ nat_trans_fix_fst_arg_data nat_trans_fix_fst_arg_ax.

End nat_trans_fix_fst_arg.

Section functor_fix_snd_arg.

Variable C D E : precategory.
Variable F: functor (precategory_binproduct C D) E.
Variable d: D.

Definition functor_fix_snd_arg_ob (c:C): E := F(tpair _ c d).
Definition functor_fix_snd_arg_mor (c c':C)(f: c --> c'): functor_fix_snd_arg_ob c --> functor_fix_snd_arg_ob c'.
Proof.
  apply (#F).
  exact (dirprodpair f (identity d)).
Defined.

Definition functor_fix_snd_arg_data : functor_data C E
  := tpair _ functor_fix_snd_arg_ob functor_fix_snd_arg_mor.

Lemma is_functor_functor_fix_snd_arg_data: is_functor functor_fix_snd_arg_data.
Proof.
  split.
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
    assert (functor_comp_inst := @functor_comp _ _ F (dirprodpair c d) (dirprodpair c' d) (dirprodpair c'' d)).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold precategory_binproduct; simpl.
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

Variable C D E : precategory.
Variable F F': functor (precategory_binproduct C D) E.
Variable α: F ⟹ F'.
Variable d: D.

Definition nat_trans_fix_snd_arg_data (c:C): functor_fix_snd_arg C D E F d c --> functor_fix_snd_arg C D E F' d c := α (tpair _ c d).

Lemma nat_trans_fix_snd_arg_ax: is_nat_trans _ _ nat_trans_fix_snd_arg_data.
Proof.
  red.
  intros c c' f.
  unfold nat_trans_fix_snd_arg_data, functor_fix_snd_arg; simpl.
  unfold functor_fix_snd_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_snd_arg: functor_fix_snd_arg C D E F d ⟹ functor_fix_snd_arg C D E F' d
  := tpair _ nat_trans_fix_snd_arg_data nat_trans_fix_snd_arg_ax.

End nat_trans_fix_snd_arg.

(* Define pairs of functors and functors from pr1 and pr2 *)
Section functors.

Definition pair_functor_data {A B C D : precategory}
  (F : functor A C) (G : functor B D) :
  functor_data (precategory_binproduct A B) (precategory_binproduct C D).
Proof.
use tpair.
- intro x; apply (precatbinprodpair (F (pr1 x)) (G (pr2 x))).
- intros x y f; simpl; apply (precatbinprodmor (# F (pr1 f)) (# G (pr2 f))).
Defined.

Definition pair_functor {A B C D : precategory}
  (F : functor A C) (G : functor B D) :
  functor (precategory_binproduct A B) (precategory_binproduct C D).
Proof.
apply (tpair _ (pair_functor_data F G)).
abstract (split;
  [ intro x; simpl; rewrite !functor_id; apply idpath
  | intros x y z f g; simpl; rewrite !functor_comp; apply idpath]).
Defined.

Definition pr1_functor_data (A B : precategory) :
  functor_data (precategory_binproduct A B) A.
Proof.
use tpair.
- intro x; apply (pr1 x).
- intros x y f; simpl; apply (pr1 f).
Defined.

Definition pr1_functor (A B : precategory) :
  functor (precategory_binproduct A B) A.
Proof.
apply (tpair _ (pr1_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition pr2_functor_data (A B : precategory) :
  functor_data (precategory_binproduct A B) B.
Proof.
use tpair.
- intro x; apply (pr2 x).
- intros x y f; simpl; apply (pr2 f).
Defined.

Definition pr2_functor (A B : precategory) :
  functor (precategory_binproduct A B) B.
Proof.
apply (tpair _ (pr2_functor_data A B)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition bindelta_functor_data (C : precategory) :
  functor_data C (precategory_binproduct C C).
Proof.
use tpair.
- intro x; apply (precatbinprodpair x x).
- intros x y f; simpl; apply (precatbinprodmor f f).
Defined.

Definition bindelta_functor (C : precategory) :
  functor C (precategory_binproduct C C).
Proof.
apply (tpair _ (bindelta_functor_data C)).
abstract (split; [ intro x; apply idpath | intros x y z f g; apply idpath ]).
Defined.

Definition bindelta_pair_functor_data (C D E : precategory)
  (F : functor C D)
  (G : functor C E) :
  functor_data C (precategory_binproduct D E).
Proof.
  use tpair.
  - intro c. apply (precatbinprodpair (F c) (G c)).
  - intros x y f. simpl. apply (precatbinprodmor (# F f) (# G f)).
Defined.

Definition bindelta_pair_functor {C D E : precategory}
  (F : functor C D)
  (G : functor C E) :
  functor C (precategory_binproduct D E).
Proof.
  apply (tpair _ (bindelta_pair_functor_data C D E F G)).
  split.
  - intro c.
    simpl.
    rewrite functor_id.
    rewrite functor_id.
    apply idpath.
  - intros c c' c'' f g.
    simpl.
    rewrite functor_comp.
    rewrite functor_comp.
    apply idpath.
Defined.

End functors.
