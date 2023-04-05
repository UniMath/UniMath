Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.AlgebraicBases.

Local Open Scope cat.
Local Open Scope algebraic_theory.

Definition algebraic_theory_data := ∑ (T : algebraic_base),
  (T 1) × (∏ (m n : nat), (stn m → stn n) → T m → T n).

Definition make_algebraic_theory_data (T : algebraic_base)
  (id_pr : T 1) (T_on_morphisms : ∏ {m n : nat}, (stn m → stn n) → T m → T n) : algebraic_theory_data.
Proof.
  exact (T ,, id_pr ,, T_on_morphisms).
Defined.

Coercion algebraic_base_from_algebraic_theory_data
  (T : algebraic_theory_data)
  : algebraic_base
  := pr1 T.

Definition id_pr {T : algebraic_theory_data} : T 1 := pr12 T.

Definition T_on_morphisms {T : algebraic_theory_data} {m n} : (stn m → stn n) → T m → T n := pr22 T m n.

Definition theory_pr {T : algebraic_theory_data} {n : nat} (i : stn n) : T n := T_on_morphisms (λ (x : stn 1), i) id_pr.

Definition algebraic_theory_data_to_functor_data
  (T : algebraic_theory_data)
  : functor_data finite_set_skeleton_category HSET
  := make_functor_data (T : finite_set_skeleton_category → HSET) (@T_on_morphisms T).

(* Define the associativity property of the algebraic theory *)
Definition comp_is_assoc (T : algebraic_theory_data) : UU := ∏
  (l m n : nat)
  (f_l : T l)
  (f_m : stn l → T m)
  (f_n : stn m → T n),
    (f_l • f_m) • f_n = f_l • (λ t_l, (f_m t_l) • f_n).

(* Define the unitality property of the algebraic theory *)
Definition comp_is_unital (T : algebraic_theory_data) : UU := ∏
  (n : nat)
  (f : T n),
    id_pr • (λ _, f) = f.

(* Define the compatibility of the projection function with composition *)
Definition comp_identity_projections (T : algebraic_theory_data) : UU := ∏
  (n : nat)
  (f : T n),
    f • (λ i, theory_pr i) = f.

(* Define naturality of the composition in the first argument *)
Definition comp_is_natural_l (T : algebraic_theory_data) : UU := ∏
  (m m' n : finite_set_skeleton_category)
  (a : finite_set_skeleton_category⟦m, m'⟧)
  (f : T m)
  (g : stn m' → T n),
  (T_on_morphisms a f) • g = f • (λ i, g (a i)).

Definition is_algebraic_theory (T : algebraic_theory_data) :=
    (is_functor (algebraic_theory_data_to_functor_data T)) ×
    (comp_is_assoc T) ×
    (comp_is_unital T) ×
    (comp_identity_projections T) ×
    (comp_is_natural_l T).

Definition make_is_algebraic_theory
  {T : algebraic_theory_data}
  (H1 : (is_functor (algebraic_theory_data_to_functor_data T)))
  (H2 : comp_is_assoc T)
  (H3 : comp_is_unital T)
  (H4 : comp_identity_projections T)
  (H5 : comp_is_natural_l T) : is_algebraic_theory T := (H1 ,, H2 ,, H3 ,, H4 ,, H5).

Lemma isaprop_is_algebraic_theory (T : algebraic_theory_data) : isaprop (is_algebraic_theory T).
Proof.
  apply isapropdirprod.
  - apply isaprop_is_functor.
    apply SET.
  - repeat apply isapropdirprod;
      repeat (apply impred_isaprop; intro);
      apply setproperty.
Qed.

Definition algebraic_theory := ∑ T, is_algebraic_theory T.

Definition make_algebraic_theory
  (T : algebraic_theory_data)
  (H : is_algebraic_theory T)
  : algebraic_theory
  := (T ,, H).

Coercion algebraic_theory_data_from_algebraic_theory (T : algebraic_theory)
  : algebraic_theory_data
  := pr1 T.

Definition algebraic_theory_is_functor (T : algebraic_theory) :
  is_functor (algebraic_theory_data_to_functor_data T)
  := pr12 T.

Definition algebraic_theory_comp_is_assoc (T : algebraic_theory) :
  comp_is_assoc T
  := pr122 T.

Definition algebraic_theory_comp_is_unital (T : algebraic_theory)
  : comp_is_unital T
  := pr1 (pr222 T).

Definition algebraic_theory_comp_identity_projections (T : algebraic_theory)
  : comp_identity_projections T
  := pr12 (pr222 T).

Definition algebraic_theory_comp_is_natural_l (T : algebraic_theory)
  : comp_is_natural_l T
  := pr22 (pr222 T).

Lemma algebraic_theory_eq
  (X Y : algebraic_theory)
  (H1 : (X : nat → hSet) = (Y : nat → hSet))
  (H2 : transportf (λ (T : nat → hSet), ∏ m n : nat, T m → (stn m → T n) → T n) H1 (@comp X) = (@comp Y))
  (H3 : transportf (λ (T : nat → hSet), T 1) H1 id_pr = id_pr)
  (H4 : transportf
    (λ (T : nat → hSet), ∏ m n, (stn m → stn n) → T m → T n)
    H1
    (@T_on_morphisms X) = (@T_on_morphisms Y)
  )
  : X = Y.
Proof.
  use (subtypePairEquality' _ (isaprop_is_algebraic_theory _)).
  use total2_paths_f.
  - exact (total2_paths_f H1 H2).
  - rewrite (@transportf_total2_paths_f
        (nat → hSet)
        (λ C, ∏ m n, C m → (stn m → C n) → C n)
        (λ T, T 1 × (∏ m n : nat, ((⟦ m ⟧)%stn → (⟦ n ⟧)%stn) → T m → T n))
      ).
    rewrite (transportf_dirprod (nat → hSet) _ _ ((pr111 X) ,, pr21 X) ((pr111 Y) ,, pr21 Y)).
    exact (pathsdirprod H3 H4).
Qed.

Definition algebraic_theory_to_functor
  (T : algebraic_theory)
  : finite_set_skeleton_category ⟶ HSET
  := make_functor _ (algebraic_theory_is_functor T).

(* Properties of algebraic theories *)
Lemma functor_uses_projections
  (T : algebraic_theory)
  (m n : finite_set_skeleton_category)
  (a : finite_set_skeleton_category⟦m, n⟧)
  (f : T m)
  : T_on_morphisms a f = f • (λ i, theory_pr (a i)).
Proof.
  rewrite <- (algebraic_theory_comp_identity_projections _ _ (T_on_morphisms _ _)).
  apply algebraic_theory_comp_is_natural_l.
Qed.

Lemma comp_project_component
  (T : algebraic_theory)
  (m n : nat)
  (i : stn m)
  (f : stn m → T n)
  : (theory_pr i) • f = f i.
Proof.
  unfold theory_pr.
  rewrite algebraic_theory_comp_is_natural_l.
  apply algebraic_theory_comp_is_unital.
Qed.

(* The composition is natural in the second argument *)
Lemma comp_is_natural_r (T : algebraic_theory)
  (m n n' : finite_set_skeleton_category)
  (a: finite_set_skeleton_category⟦n, n'⟧)
  (f : T m)
  (g : stn m → T n)
  : f • (λ i, T_on_morphisms a (g i)) = T_on_morphisms a (f • g).
Proof.
  rewrite functor_uses_projections.
  rewrite algebraic_theory_comp_is_assoc.
  apply maponpaths.
  apply funextsec2.
  intro.
  rewrite functor_uses_projections.
  apply idpath.
Qed.
