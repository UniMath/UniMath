Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.

Local Open Scope algebraic_theory.

Definition abstract_clone_algebra_data (C : abstract_clone_data)
  : UU
  := ∑ (A : hSet), ∏ (n : nat), C n → (stn n → A) → A.

Definition make_abstract_clone_algebra_data
  {C : abstract_clone_data}
  (A : hSet)
  (action : ∏ (n : nat), C n → (stn n → A) → A)
  : abstract_clone_algebra_data C
  := (A ,, action).

Coercion abstract_clone_algebra_data_to_hset {C : abstract_clone_data} (A : abstract_clone_algebra_data C)
  : hSet
  := pr1 A.

Definition action {C : abstract_clone_data} {A : abstract_clone_algebra_data C} {n : nat}
  : C n → (stn n → A) → A
  := pr2 A n.

Definition action_projects_component {C : abstract_clone_data} (A : abstract_clone_algebra_data C)
  : UU
  := ∏ 
    (n : nat)
    (i : stn n)
    (a : stn n → A)
    , action (clone_pr i) a = a i.

Definition action_is_assoc {C : abstract_clone_data} (A : abstract_clone_algebra_data C)
  : UU
  := ∏ 
    (m n : nat)
    (f : C m)
    (g : stn m → C n)
    (a : stn n → A)
    , action (f • g) a = action f (λ i, action (g i) a).
  
Definition is_abstract_clone_algebra {C : abstract_clone_data} (A : abstract_clone_algebra_data C)
  : UU
  :=
    action_projects_component A ×
    action_is_assoc A.

Definition make_is_abstract_clone_algebra
  {C : abstract_clone_data}
  (A : abstract_clone_algebra_data C)
  (H1 : action_projects_component A)
  (H2 : action_is_assoc A)
  : is_abstract_clone_algebra A
  := (H1 ,, H2).

Definition abstract_clone_algebra (C : abstract_clone_data)
  : UU
  := ∑ (A : abstract_clone_algebra_data C), is_abstract_clone_algebra A.

Definition make_abstract_clone_algebra
  {C : abstract_clone_data}
  (A : abstract_clone_algebra_data C)
  (H : is_abstract_clone_algebra A)
  : abstract_clone_algebra C
  := (A ,, H).

Coercion abstract_clone_algebra_to_abstract_clone_algebra_data
  {C : abstract_clone_data}
  (A : abstract_clone_algebra C)
  : abstract_clone_algebra_data C
  := pr1 A.

Definition abstract_clone_algebra_action_projects_component
  {C : abstract_clone_data}
  (A : abstract_clone_algebra C)
  : action_projects_component A
  := pr12 A.

Definition abstract_clone_algebra_action_is_assoc
  {C : abstract_clone_data}
  (A : abstract_clone_algebra C)
  : action_is_assoc A
  := pr22 A.

Lemma is_abstract_clone_algebra_isaprop
  {C : abstract_clone_data}
  (A : abstract_clone_algebra_data C)
  : isaprop (is_abstract_clone_algebra A).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intros);
    apply setproperty.
Qed.

Lemma abstract_clone_algebra_eq
  {C : abstract_clone_data}
  (A B : abstract_clone_algebra C)
  (H1 : (pr1hSet A) = (pr1hSet B))
  (H2 : ∏ n, transportf (λ A, C n → (stn n → A) → A) H1 action = action)
  : A = B.
Proof.
  use (subtypePairEquality' _ (is_abstract_clone_algebra_isaprop _)).
  use total2_paths_f.
  - apply (total2_paths_f H1).
    apply isapropisaset.
  - rewrite transportf_sec_constant.
    apply funextsec.
    intro n.
    rewrite (@transportf_total2_paths_f
      UU
      (λ A, isaset A)
      (λ A, C n → (stn n → A) → A)
    ).
    apply H2.
Qed.

Lemma lift_constant_action
  {C : abstract_clone_data}
  {A : abstract_clone_algebra C}
  (n : nat)
  (f : C 0)
  (a : stn n → A)
  : action (lift_constant n f) a = action f (weqvecfun _ vnil).
Proof.
  unfold lift_constant.
  rewrite abstract_clone_algebra_action_is_assoc.
  apply maponpaths, funextfun.
  intro i.
  exact (fromempty (negnatlthn0 _ (stnlt i))).
Qed.
