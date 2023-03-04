Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Section AbstractClone.

  Definition abstract_clone_data := ∑ (C : nat → hSet),
    (∏ {n}, stn n → C n) × (∏ {m n}, C m → (stn m → C n) → C n).

  Definition make_abstract_clone_data
    (C : nat → hSet)
    (pr : ∏ {n}, stn n → C n)
    (comp : ∏ {m n}, C m → (stn m → C n) → C n)
    : abstract_clone_data.
  Proof.
    exact (C ,, pr ,, comp).
  Defined.

  Local Definition indexed_set := nat → hSet.
  Definition f_C (C0 : abstract_clone_data) : indexed_set := pr1 C0.
  Coercion f_C : abstract_clone_data >-> indexed_set.

  Definition pr {C : abstract_clone_data} {n : nat} := pr12 C n.
  Definition comp {C : abstract_clone_data} {m n : nat} := pr22 C m n.

  Notation "f • g" :=
    (comp f g)
    (at level 50).

  Definition reindex {C : abstract_clone_data} {m n : nat} (a : stn m → stn n) : (C : indexed_set) m → (C : indexed_set) n := (λ f, f • (λ i, pr (a i))).

  (* Define the unitality property of the algebraic theory *)
  Definition comp_project_component (C : abstract_clone_data) : Prop := ∏
    (m n : nat)
    (i : stn m)
    (f : stn m → (C : indexed_set) n),
      (pr i) • f = f i.

  (* Define the compatibility of the projection function with composition *)
  Definition comp_identity_projections (C : abstract_clone_data) : Prop := ∏
    (n : nat)
    (f : (C : indexed_set) n),
      f • (λ i, pr i) = f.

  (* Define the associativity property of the algebraic theory *)
  Definition comp_is_assoc (C : abstract_clone_data) : Prop := ∏
    (l m n : nat)
    (f_l : (C : indexed_set) l)
    (f_m : stn l → (C : indexed_set) m)
    (f_n : stn m → (C : indexed_set) n),
      (f_l • f_m) • f_n = f_l • (λ t_l, (f_m t_l) • f_n).

  Definition is_abstract_clone (C : abstract_clone_data) :=
    (comp_project_component C) ×
    (comp_identity_projections C) ×
    (comp_is_assoc C).

  Definition make_is_abstract_clone
    (C : abstract_clone_data)
    (H1 : comp_project_component C)
    (H2 : comp_identity_projections C)
    (H3 : comp_is_assoc C)
    : is_abstract_clone C
    := (H1 ,, H2 ,, H3).

  Lemma ispredicate_is_abstract_clone : isPredicate is_abstract_clone.
  Proof.
    intros ?.
    repeat apply isapropdirprod;
      repeat (apply impred_isaprop; intros);
      try apply setproperty.
  Qed.

  Definition abstract_clone := total2 is_abstract_clone.

  Definition make_abstract_clone (T : abstract_clone_data) (H : is_abstract_clone T) : abstract_clone := (T ,, H).

  Definition abstract_clone_data_from_abstract_clone : abstract_clone -> abstract_clone_data := pr1.
  Coercion abstract_clone_data_from_abstract_clone : abstract_clone >-> abstract_clone_data.

End AbstractClone.