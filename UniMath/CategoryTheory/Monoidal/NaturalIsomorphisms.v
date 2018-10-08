(* Natural isomorphisms *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

Notation "'id' X" := (identity X) (at level 30).

Definition is_nat_iso {C D : precategory} {F G : C ⟶ D} (μ : F ⟹ G) : UU :=
∏ (c : C), is_iso (μ c).

Definition is_nat_id {C D : precategory} {F : C ⟶ D} (μ : F ⟹ F) : UU :=
∏ (c : C), μ c = id (F c).

Definition mk_iso {C : precategory} {c c' : C} {f : c --> c'} (ii : is_iso f) : iso c c'.
Proof.
  exists f.
  exact ii.
Defined.

Definition nat_iso {C D : precategory} (F G : C ⟶ D) : UU
:= ∑ (μ : F ⟹ G), is_nat_iso μ.

Definition iso_inv_after_iso' {C : precategory} {a b : C} (f : a --> b) (f' : iso a b) (deref : pr1 f' = f) : f · inv_from_iso f' = id _.
Proof.
  rewrite <- deref.
  exact (iso_inv_after_iso f').
Defined.

Definition iso_after_iso_inv' {C : precategory} {a b : C} (f : a --> b) (f' : iso a b) (deref : pr1 f' = f) : inv_from_iso f' · f = id _.
Proof.
  rewrite <- deref.
  exact (iso_after_iso_inv f').
Defined.

Definition nat_iso_inv {C D : precategory} {F G : C ⟶ D} (μ : nat_iso F G) : nat_iso G F.
Proof.
  pose (iso := (λ c, mk_iso (pr2 μ c))).
  pose (inv := (λ c, inv_from_iso (iso c))).
  use tpair.
  - exists inv.
    intros c c' f.
    pose (coher := pr2 (pr1 μ) c c' f).
    pose (coher_inv := maponpaths (λ p, inv c · p · inv c') coher).
    simpl in coher_inv.
    repeat rewrite <- assoc in coher_inv.
    unfold inv in coher_inv.
    assert (coher_inv' : (inv_from_iso (iso c) · (# F f · ((pr1 μ) c' · inv_from_iso (iso c'))) = inv_from_iso (iso c) · (pr1 (pr1 μ) c · (# G f · inv_from_iso (iso c'))))) by assumption.
    clear coher_inv; rename coher_inv' into coher_inv.
    assert (deref' : pr1 (iso c') = (pr1 μ) c') by reflexivity.
    rewrite (iso_inv_after_iso' ((pr1 μ) c') (iso c') deref') in coher_inv.
    rewrite id_right in coher_inv.
    repeat rewrite assoc in coher_inv.
    assert (deref : pr1 (iso c) = (pr1 μ) c) by reflexivity.
    assert (coher_inv' : (inv_from_iso (iso c) · # F f = inv_from_iso (iso c) · (pr1 μ) c · # G f · inv_from_iso (iso c'))) by assumption.
    clear coher_inv; rename coher_inv' into coher_inv.
    rewrite (iso_after_iso_inv' ((pr1 μ) c) (iso c) deref) in coher_inv.
    rewrite id_left in coher_inv.
    unfold inv.
    symmetry.
    assumption.
  - intro c.
    exact (is_iso_inv_from_iso (iso c)).
Defined.

Definition nat_iso_to_trans {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : F ⟹ G :=
  pr1 ν.

(* ⁻¹ *)
Definition nat_iso_to_trans_inv {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : G ⟹ F :=
  pr1 (nat_iso_inv ν).

Definition is_nat_iso_id {C D : precategory} {F G : C ⟶ D} (ν : nat_iso F G) : UU :=
  ∏ (c : C), (nat_iso_to_trans ν c) · (nat_iso_to_trans_inv ν c) = id (F c).
