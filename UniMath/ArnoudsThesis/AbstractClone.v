Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Section AbstractCloneData.

  Definition abstract_clone_data := ∑ (C : nat → hSet),
    (∏ n, stn n → C n) × (∏ m n, C m → (stn m → C n) → C n).

  Variable C : abstract_clone_data.

  Local Definition indexed_set := nat → hSet.
  Definition f_C (C0 : abstract_clone_data) : indexed_set := pr1 C0.
  Coercion f_C : abstract_clone_data >-> indexed_set.

  Definition pr {n : nat} := pr12 C n.
  Definition comp {m n : nat} := pr22 C m n.

  Notation "f • g" :=
    (comp f g)
    (at level 50).

  (* Define the unitality property of the algebraic theory *)
  Definition comp_project_component : Prop := ∏
    (m n : nat)
    (i : stn m)
    (f : stn m → (C : indexed_set) m),
      (pr i) • f = f i.

  (* Define the compatibility of the projection function with composition *)
  Definition comp_identity_projections : Prop := ∏
    (n : nat)
    (f : (C : indexed_set) n),
      f • (λ i, pr i) = f.

  (* Define the associativity property of the algebraic theory *)
  Definition comp_is_assoc : Prop := ∏
    (l m n : nat)
    (f_l : (C : indexed_set) l)
    (f_m : stn l → (C : indexed_set) m)
    (f_n : stn m → (C : indexed_set) n),
      (f_l • f_m) • f_n = f_l • (λ t_l, (f_m t_l) • f_n).

End AbstractCloneData.

Section AbstractClone.

  Definition is_abstract_clone (C: abstract_clone_data) :=
    (comp_project_component C) ×
    (comp_identity_projections C) ×
    (comp_is_assoc C).

  Lemma ispredicate_is_abstract_clone : isPredicate is_abstract_clone.
  Proof.
    intros ?.
    repeat apply isapropdirprod;
      repeat (apply impred_isaprop; intros);
      try apply setproperty.
  Qed.

  Definition abstract_clone := total2 is_abstract_clone.

End AbstractClone.