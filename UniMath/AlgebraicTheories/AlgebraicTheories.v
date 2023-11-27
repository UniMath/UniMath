(**************************************************************************************************

  Algebraic Theories

  These objects are known by many names: algebraic theories, abstract clones, cartesian operads
  and Lawvere theories. This file defines them and gives constructors, accessors and related
  definitions and lemmas.

  Contents
  1. The definition of algebraic theories [algebraic_theory]
  2. An alternate constructor [make_algebraic_theory']
  3. An equality lemma [algebraic_theory_eq]
  4. Some useful properties and definitions

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories2.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.Combinatorics.Tuples.

Declare Scope algebraic_theories.

Local Open Scope cat.
Local Open Scope algebraic_theories.

(** * 1. The definition of algebraic theories *)

Definition base_functor
  : UU
  := finite_set_skeleton_category ⟶ HSET.

Coercion base_functor_to_functor (T : base_functor) : finite_set_skeleton_category ⟶ HSET := T.

Definition pointed_functor
  : UU
  := ∑ (T : base_functor), (T 1 : hSet).

Coercion pointed_functor_to_base_functor (T : pointed_functor) : base_functor := pr1 T.

Definition id_pr {T : pointed_functor} : (T 1 : hSet) := pr2 T.

Definition pr {T : pointed_functor} {n : nat} (i : stn n) : (T n : hSet) := # T (λ _, i) id_pr.

Definition algebraic_theory_data
  : UU
  := ∑ (T : pointed_functor), ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet).

Coercion algebraic_theory_data_to_pointed_functor (T : algebraic_theory_data)
  : pointed_functor
  := pr1 T.

Definition comp {T : algebraic_theory_data} {m n : nat}
  : ((T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet))
  := pr2 T m n.

Notation "f • g" :=
  (comp f g)
  (at level 35) : algebraic_theories.

Definition comp_is_assoc (T : algebraic_theory_data) : UU := ∏
  (l m n : nat)
  (f_l : (T l : hSet))
  (f_m : stn l → T m : hSet)
  (f_n : stn m → T n : hSet),
    (f_l • f_m) • f_n = f_l • (λ t_l, (f_m t_l) • f_n).

Definition comp_is_unital (T : algebraic_theory_data) : UU := ∏
  (n : nat)
  (f : (T n : hSet)),
    id_pr • (λ _, f) = f.

Definition comp_identity_projections (T : algebraic_theory_data) : UU := ∏
  (n : nat)
  (f : (T n : hSet)),
    f • (λ i, pr i) = f.

Definition comp_is_natural_l (T : algebraic_theory_data) : UU := ∏
  (m m' n : finite_set_skeleton_category)
  (a : finite_set_skeleton_category⟦m, m'⟧)
  (f : (T m : hSet))
  (g : stn m' → T n : hSet),
  (# T a f) • g = f • (λ i, g (a i)).

Definition is_algebraic_theory (T : algebraic_theory_data) : UU :=
  comp_is_assoc T ×
  comp_is_unital T ×
  comp_identity_projections T ×
  comp_is_natural_l T.

Definition algebraic_theory : UU := ∑ (T : algebraic_theory_data), is_algebraic_theory T.

Coercion algebraic_theory_to_algebraic_theory_data (T : algebraic_theory)
  : algebraic_theory_data
  := pr1 T.

Definition make_algebraic_theory_data
  (T : base_functor)
  (id_pr : (T 1 : hSet))
  (comp : ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet))
  : algebraic_theory_data
  := ((T ,, id_pr) ,, comp).

Definition make_is_algebraic_theory
  (T : algebraic_theory_data)
  (H1 : comp_is_assoc T)
  (H2 : comp_is_unital T)
  (H3 : comp_identity_projections T)
  (H4 : comp_is_natural_l T)
  : is_algebraic_theory T
  := (H1 ,, H2 ,, H3 ,, H4).

Definition make_algebraic_theory
  (T : algebraic_theory_data)
  (H : is_algebraic_theory T)
  : algebraic_theory
  := T ,, H.

Definition algebraic_theory_comp_is_assoc (T : algebraic_theory) :
  comp_is_assoc T
  := pr12 T.

Definition algebraic_theory_comp_is_unital (T : algebraic_theory)
  : comp_is_unital T
  := pr122 T.

Definition algebraic_theory_comp_identity_projections (T : algebraic_theory)
  : comp_identity_projections T
  := pr1 (pr222 T).

Definition algebraic_theory_comp_is_natural_l (T : algebraic_theory)
  : comp_is_natural_l T
  := pr2 (pr222 T).

(** * 2. An alternate constructor *)

Section MakeAlgebraicTheory'.
  Definition algebraic_theory'_to_functor_data (C : algebraic_theory')
    : functor_data finite_set_skeleton_category HSET.
  Proof.
    use make_functor_data.
    - exact C.
    - exact (λ _ _ a f, comp' f (λ i, pr' (a i))).
  Defined.

  Lemma algebraic_theory'_to_is_functor (C : algebraic_theory')
    : is_functor (algebraic_theory'_to_functor_data C).
  Proof.
    split.
    - intro.
      apply funextfun.
      intro.
      apply algebraic_theory'_comp_identity_projections.
    - intros l m n f g.
      apply funextfun.
      intro h.
      rewrite (algebraic_theory'_comp_is_assoc _ _ _ _ _ _ _
        : (_ · (# (algebraic_theory'_to_functor_data C) g)) _ = _).
      apply (maponpaths (comp' h)), funextfun.
      intro.
      symmetry.
      apply algebraic_theory'_comp_project_component.
  Qed.

  Definition algebraic_theory'_to_algebraic_theory_data (C : algebraic_theory')
    : algebraic_theory_data.
  Proof.
    use make_algebraic_theory_data.
    - exact (make_functor _ (algebraic_theory'_to_is_functor C)).
    - exact (pr' firstelement).
    - exact (λ _ _, comp').
  Defined.

  Lemma algebraic_theory'_to_is_algebraic_theory (C : algebraic_theory')
    : is_algebraic_theory (algebraic_theory'_to_algebraic_theory_data C).
  Proof.
    use make_is_algebraic_theory.
    - apply algebraic_theory'_comp_is_assoc.
    - do 2 intro.
      apply algebraic_theory'_comp_project_component.
    - do 2 intro.
      rewrite <- algebraic_theory'_comp_identity_projections.
      apply maponpaths, funextfun.
      intro.
      apply algebraic_theory'_comp_project_component.
    - do 6 intro.
      simpl.
      rewrite (algebraic_theory'_comp_is_assoc C).
      apply maponpaths, funextfun.
      intro.
      apply algebraic_theory'_comp_project_component.
  Qed.

  Definition make_algebraic_theory' (C : algebraic_theory'_data) (H : is_algebraic_theory' C)
    : algebraic_theory
    := make_algebraic_theory _ (algebraic_theory'_to_is_algebraic_theory (C ,, H)).
End MakeAlgebraicTheory'.

Lemma isaprop_is_algebraic_theory (T : algebraic_theory_data) : isaprop (is_algebraic_theory T).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

(** * 3. An equality lemma *)

Lemma algebraic_theory_eq
  (X Y : algebraic_theory)
  (H1 : (X : nat → hSet) = (Y : nat → hSet))
  (H2 : transportf (λ T : nat → hSet, ∏ m n : nat, (stn m → stn n) → T m → T n) H1
    (@functor_on_morphisms _ _ X) = (@functor_on_morphisms _ _ Y))
  (H3 : transportf (λ (T : nat → hSet), T 1) H1 id_pr = id_pr)
  (H4 : transportf (λ (T : nat → hSet), ∏ m n : nat, T m → (stn m → T n) → T n) H1
    (@comp X) = (@comp Y))
  : X = Y.
Proof.
  use (subtypePath isaprop_is_algebraic_theory).
  use total2_paths_f.
  - use total2_paths_f.
    + apply (functor_eq _ _ (homset_property HSET)).
      exact (total2_paths_f H1 H2).
    + unfold functor_eq.
      rewrite (@transportf_total2_paths_f
        (functor_data finite_set_skeleton_category HSET)
        (λ T, is_functor T)
        (λ T, T 1 : hSet)
      ).
      rewrite (@transportf_total2_paths_f
        (nat → hSet)
        (λ T, ∏ m n, (stn m → stn n) → T m → T n)
        (λ T, T 1)
      ).
      exact H3.
  - unfold functor_eq.
    rewrite (@transportf_total2_paths_f
      base_functor
      (λ T, T 1 : hSet)
      (λ (T : base_functor), ∏ m n : nat, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet))
    ).
    rewrite (@transportf_total2_paths_f
      (functor_data finite_set_skeleton_category HSET)
      (λ T, is_functor T)
      (λ (T : functor_data _ _), ∏ m n : nat, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet))
    ).
    rewrite (@transportf_total2_paths_f
      (nat → hSet)
      (λ T, ∏ m n, (stn m → stn n) → T m → T n)
      (λ (T : nat → hSet), ∏ m n : nat, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet))
    ).
    exact H4.
Qed.

(** * 4. Some useful properties and definitions *)

Definition lift_constant {T : algebraic_theory_data} (n : nat) (f : (T 0 : hSet))
  : (T n : hSet)
  := f • (weqvecfun _ vnil).

Lemma algebraic_theory_functor_uses_projections
  (T : algebraic_theory)
  (m n : finite_set_skeleton_category)
  (a : finite_set_skeleton_category⟦m, n⟧)
  (f : T m : hSet)
  : #T a f = f • (λ i, pr (a i)).
Proof.
  rewrite <- (algebraic_theory_comp_identity_projections _ _ (#T _ _)).
  apply algebraic_theory_comp_is_natural_l.
Qed.

Lemma algebraic_theory_comp_projects_component
  (T : algebraic_theory)
  (m n : nat)
  (i : stn m)
  (f : stn m → T n : hSet)
  : (pr i) • f = f i.
Proof.
  unfold pr.
  rewrite algebraic_theory_comp_is_natural_l.
  apply algebraic_theory_comp_is_unital.
Qed.

Lemma algebraic_theory_comp_is_natural_r (T : algebraic_theory)
  (m n n' : finite_set_skeleton_category)
  (a: finite_set_skeleton_category⟦n, n'⟧)
  (f : (T m : hSet))
  (g : stn m → (T n : hSet))
  : f • (λ i, #T a (g i)) = #T a (f • g).
Proof.
  rewrite algebraic_theory_functor_uses_projections.
  rewrite algebraic_theory_comp_is_assoc.
  apply maponpaths, funextfun.
  intro.
  apply algebraic_theory_functor_uses_projections.
Qed.

Lemma algebraic_theory_id_pr_is_pr (T : algebraic_theory)
  : id_pr = pr (T := T) (@firstelement 0).
Proof.
  refine (eqtohomot (!functor_id T _) id_pr @ _).
  apply (maponpaths (λ x, # T x id_pr)).
  apply funextfun.
  intro.
  apply stn_eq.
  exact (natlth1tois0 _ (stnlt x)).
Qed.
