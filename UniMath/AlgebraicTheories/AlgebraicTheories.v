Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.

Declare Scope algebraic_theories.

Local Open Scope cat.
Local Open Scope algebraic_theories.

Definition base_functor
  : UU
  := finite_set_skeleton_category ⟶ HSET.

Coercion base_functor_to_functor (T : base_functor) : finite_set_skeleton_category ⟶ HSET := T.

Definition pointed_functor
  : UU
  := ∑ (T : base_functor), (T 1 : hSet).

Coercion pointed_functor_to_base_functor (T : pointed_functor) : base_functor := pr1 T.

Definition id_pr {T : pointed_functor} : (T 1 : hSet) := pr2 T.

(* Accessor for the projections *)
Definition pr {T : pointed_functor} {n : nat} (i : stn n) : (T n : hSet) := # T (λ _, i) id_pr.

Definition algebraic_theory_data
  : UU
  := ∑ (T : pointed_functor), ∏ m n, (T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet).

Coercion algebraic_theory_data_to_pointed_functor (T : algebraic_theory_data) : pointed_functor := pr1 T.

(* Accessor for the composition *)
Definition comp {T : algebraic_theory_data} {m n : nat} : ((T m : hSet) → (stn m → (T n : hSet)) → (T n : hSet)) := pr2 T m n.

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

Coercion algebraic_theory_to_algebraic_theory_data (T : algebraic_theory) : algebraic_theory_data := pr1 T.

(* Constructors for the algebraic theory type *)
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

Section MakeAlgebraicTheory'.
  Definition abstract_clone_to_functor_data (C : abstract_clone)
    : functor_data finite_set_skeleton_category HSET.
  Proof.
    use make_functor_data.
    - exact C.
    - exact (λ _ _ a f, clone_comp f (λ i, clone_pr (a i))).
  Defined.

  Lemma abstract_clone_to_is_functor (C : abstract_clone)
    : is_functor (abstract_clone_to_functor_data C).
  Proof.
    apply tpair.
    - intro.
      apply funextfun.
      intro.
      apply abstract_clone_comp_identity_projections.
    - do 5 intro.
      apply funextfun.
      intro.
      rewrite (abstract_clone_comp_is_assoc _ _ _ _ _ _ _ : (_ · (# (abstract_clone_to_functor_data C) g)) _ = _).
      apply (maponpaths (clone_comp x)), funextfun.
      intro.
      symmetry.
      apply abstract_clone_comp_project_component.
  Qed.

  Definition abstract_clone_to_algebraic_theory_data (C : abstract_clone)
    : algebraic_theory_data.
  Proof.
    use make_algebraic_theory_data.
    - exact (make_functor _ (abstract_clone_to_is_functor C)).
    - exact (clone_pr firstelement).
    - exact (λ _ _, clone_comp).
  Defined.

  Lemma abstract_clone_to_is_algebraic_theory (C : abstract_clone)
    : is_algebraic_theory (abstract_clone_to_algebraic_theory_data C).
  Proof.
    use make_is_algebraic_theory.
    - apply abstract_clone_comp_is_assoc.
    - do 2 intro.
      apply abstract_clone_comp_project_component.
    - do 2 intro.
      rewrite <- abstract_clone_comp_identity_projections.
      apply maponpaths, funextfun.
      intro.
      apply abstract_clone_comp_project_component.
    - do 6 intro.
      simpl.
      rewrite (abstract_clone_comp_is_assoc C).
      apply maponpaths, funextfun.
      intro.
      apply abstract_clone_comp_project_component.
  Qed.

  Definition make_algebraic_theory' (C : abstract_clone_data) (H : is_abstract_clone C)
    : algebraic_theory
    := make_algebraic_theory _ (abstract_clone_to_is_algebraic_theory (make_abstract_clone C H)).
End MakeAlgebraicTheory'.

Lemma isaprop_is_algebraic_theory (T : algebraic_theory_data) : isaprop (is_algebraic_theory T).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intro);
    apply setproperty.
Qed.

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

Lemma algebraic_theory_eq
  (X Y : algebraic_theory)
  (H1 : (X : nat → hSet) = (Y : nat → hSet))
  (H2 : transportf (λ T : nat → hSet, ∏ m n : nat, (stn m → stn n) → T m → T n) H1 (@functor_on_morphisms _ _ X) = (@functor_on_morphisms _ _ Y))
  (H3 : transportf (λ (T : nat → hSet), T 1) H1 id_pr = id_pr)
  (H4 : transportf (λ (T : nat → hSet), ∏ m n : nat, T m → (stn m → T n) → T n) H1 (@comp X) = (@comp Y))
  : X = Y.
Proof.
  use (subtypePairEquality' _ (isaprop_is_algebraic_theory _)).
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

Definition lift_constant {T : algebraic_theory_data} (n : nat) (f : (T 0 : hSet)) : (T n : hSet) := f • (weqvecfun _ vnil).


(* Properties of algebraic theories *)

Lemma functor_uses_projections
  (T : algebraic_theory)
  (m n : finite_set_skeleton_category)
  (a : finite_set_skeleton_category⟦m, n⟧)
  (f : T m : hSet)
  : #T a f = f • (λ i, pr (a i)).
Proof.
  rewrite <- (algebraic_theory_comp_identity_projections _ _ (#T _ _)).
  apply algebraic_theory_comp_is_natural_l.
Qed.

Lemma comp_projects_component
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

Lemma comp_is_natural_r (T : algebraic_theory)
  (m n n' : finite_set_skeleton_category)
  (a: finite_set_skeleton_category⟦n, n'⟧)
  (f : (T m : hSet))
  (g : stn m → (T n : hSet))
  : f • (λ i, #T a (g i)) = #T a (f • g).
Proof.
  rewrite functor_uses_projections.
  rewrite algebraic_theory_comp_is_assoc.
  apply maponpaths, funextfun.
  intro.
  apply functor_uses_projections.
Qed.
