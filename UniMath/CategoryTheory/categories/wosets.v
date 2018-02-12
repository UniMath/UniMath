Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.OrderedSets.
Require Import UniMath.Combinatorics.WellOrderedSets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.covyoneda.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Section wosetcat.

Local Open Scope wosubset.

Definition iswofun {X Y : WellOrderedSet} (f : X → Y) : UU :=
  (iscomprelrelfun (WOrel X) (WOrel Y) f) ×
  (∏ x y, y < f x → ∃ z, z < x × f z = y).

Lemma isaprop_iswofun {X Y : WellOrderedSet} (f : X → Y) : isaprop (iswofun f).
Proof.
intros h; apply isapropdirprod; do 3 (apply impred_isaprop; intros).
- now apply propproperty.
- now apply isapropishinh.
Qed.

Definition wofun (X Y : WellOrderedSet) : UU :=
  ∑ (f : X → Y), iswofun f.

Definition pr1wofun (X Y : WellOrderedSet) : wofun X Y -> (X -> Y) := @pr1 _ _.

Lemma wofun_eq (X Y : WellOrderedSet) (f g : wofun X Y) : pr1 f = pr1 g → f = g.
Proof.
intros Heq.
apply subtypeEquality; trivial.
now intros h; apply isaprop_iswofun.
Qed.

Lemma iswofun_idfun (X : WellOrderedSet) : iswofun (idfun X).
Proof.
split.
- now intros x y.
- intros x y hxy.
  now apply hinhpr; exists y.
Qed.

Lemma iswofun_funcomp (X Y Z : WellOrderedSet) (f : wofun X Y) (g : wofun Y Z) :
  iswofun (pr1 g ∘ pr1 f).
Proof.
induction f as [f [h1f h2f]].
induction g as [g [h1g h2g]].
split.
- intros x y hxy.
  exact (h1g _ _ (h1f _ _ hxy)). (* TODO: state this as a separate lemma *)
- intros x z hf.
  generalize (h2g (f x) z hf).
  apply hinhuniv; intros [y [h1y h2y]].
  generalize (h2f x y h1y).
  apply hinhuniv; intros [x' [h1x' h2x']].
  apply hinhpr; exists x'; cbn.
  now rewrite h2x'.
Qed.

Definition woset_precategory : precategory.
Proof.
use mk_precategory.
- exists (WellOrderedSet,,wofun).
  split; simpl.
  + intros X.
    exists (idfun X).
    apply iswofun_idfun.
  + intros X Y Z f g.
    exists (pr1 g ∘ pr1 f).
    apply iswofun_funcomp.
- abstract (now repeat split; simpl; intros; apply wofun_eq).
Defined.

Lemma has_homsets_woset_precategory : has_homsets woset_precategory.
Proof.
intros X Y.
apply (isasetsubset (pr1wofun X Y)).
- apply isaset_set_fun_space.
- apply isinclpr1; intro f.
  apply isaprop_iswofun.
Qed.

End wosetcat.