Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.AlgebraicBase.

Local Open Scope cat.
Local Open Scope algebraic_theory.

Definition algebraic_theory_data := ∑ (T : algebraic_base),
  (T 1) × (∏ {m n : nat}, (stn m → stn n) → T m → T n).

Definition make_algebraic_theory_data (T : algebraic_base)
  (e : T 1) (Tmor : ∏ {m n : nat}, (stn m → stn n) → T m → T n) : algebraic_theory_data.
Proof.
  exact (T ,, e ,, Tmor).
Defined.

Definition algebraic_base_from_algebraic_theory_data (d : algebraic_theory_data) : algebraic_base := pr1 d.
Coercion algebraic_base_from_algebraic_theory_data : algebraic_theory_data >-> algebraic_base.

Definition e {T : algebraic_theory_data} : T 1 := pr12 T.

Definition Tmor {T : algebraic_theory_data} {m n} : (stn m → stn n) → T m → T n := pr22 T m n.

Definition pr {T : algebraic_theory_data} {n : nat} (i : stn n) : T n := Tmor (λ (x : stn 1), i) e.

(* Define the associativity property of the algebraic theory *)
Definition comp_is_assoc (T : algebraic_theory_data) : Prop := ∏
  (l m n : nat)
  (f_l : T l)
  (f_m : stn l → T m)
  (f_n : stn m → T n),
    (f_l • f_m) • f_n = f_l • (λ t_l, (f_m t_l) • f_n).

(* Define the unitality property of the algebraic theory *)
Definition comp_is_unital (T : algebraic_theory_data) : Prop := ∏
  (n : nat)
  (f : T n),
    e • (λ _, f) = f.

(* Define the compatibility of the projection function with composition *)
Definition comp_identity_projections (T : algebraic_theory_data) : Prop := ∏
  (n : nat)
  (f : T n),
    f • (λ i, pr i) = f.

(* Define naturality of the composition in the first argument *)
Definition comp_is_natural_l (T : algebraic_theory_data) : Prop := ∏
  (m m' n : finite_set_skeleton_category)
  (a : finite_set_skeleton_category⟦m, m'⟧)
  (f : T m)
  (g : stn m' → T n),
  (Tmor a f) • g = f • (λ i, g (a i)).

Definition is_algebraic_theory (T : algebraic_theory_data) :=
    (is_functor (make_functor_data (T : finite_set_skeleton_category → HSET) (@Tmor T))) ×
    (comp_is_assoc T) ×
    (comp_is_unital T) ×
    (comp_identity_projections T) ×
    (comp_is_natural_l T).

Definition make_is_algebraic_theory
  {T : algebraic_theory_data}
  (H1 : (is_functor (make_functor_data (T : finite_set_skeleton_category → HSET) (@Tmor T))))
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
      repeat (apply impred_isaprop; intros);
      try apply isapropisfunctor;
      try apply setproperty.
Qed.

Definition algebraic_theory := total2 is_algebraic_theory.

Definition make_algebraic_theory (T : algebraic_theory_data) (H : is_algebraic_theory T) : algebraic_theory := (T ,, H).

Definition algebraic_theory_data_from_algebraic_theory : algebraic_theory -> algebraic_theory_data := pr1.
Coercion algebraic_theory_data_from_algebraic_theory : algebraic_theory >-> algebraic_theory_data.

Lemma algebraic_theory_eq
  (X Y : algebraic_theory)
  (H1 : pr111 X = pr111 Y)
  (H2 : transportf _ H1 (pr211 X) = pr211 Y)
  (H3 : transportf (λ (T : nat → hSet), T 1) H1 (pr121 X) = (pr121 Y))
  (H4 : transportf (λ (T : nat → hSet), ∏ m n, (stn m → stn n) → T m → T n) H1 (pr221 X) = (pr221 Y))
  : X = Y.
Proof.
  destruct X as [[[Xf Xcomp] [Xe Xmor]] HX].
  destruct Y as [[[Yf Ycomp] [Ye Ymor]] HY].
  simpl in H1, H2, H3, H4.
  induction H1, H2, H3, H4.
  use (subtypePairEquality' _ (isaprop_is_algebraic_theory _)).
  repeat use total2_paths2_f;
    apply idpath.
Qed.

(* Properties of algebraic theories *)
Lemma functor_uses_projections (T : algebraic_theory) (m n : finite_set_skeleton_category) (a : finite_set_skeleton_category⟦m, n⟧) (f : T m) : Tmor a f = f • (λ i, pr (a i)).
Proof.
  rewrite <- (pr12 (pr222 T) n (Tmor a f)).
  apply T.
Qed.

Lemma comp_project_component (T : algebraic_theory) (m n : nat) (i : stn m) (f : (stn m → T n)) : (pr i) • f = f i.
Proof.
  unfold pr.
  rewrite (pr22 (pr222 T)).
  apply T.
Qed.

(* The composition is natural in the second argument *)
Lemma comp_is_natural_r (T : algebraic_theory)
  (m n n' : finite_set_skeleton_category)
  (a: finite_set_skeleton_category⟦n, n'⟧)
  (f : T m)
  (g : stn m → T n) :
    f • (λ i, Tmor a (g i)) = Tmor a (f • g).
Proof.
  rewrite functor_uses_projections.
  rewrite (pr122 T).
  apply maponpaths.
  apply funextsec2.
  intros i.
  rewrite functor_uses_projections.
  apply idpath.
Qed.
