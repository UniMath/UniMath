Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.

Local Open Scope algebraic_theory.

Definition abstract_clone_data := ∑ (B: algebraic_base),
  (∏ n, stn n → B n).

Definition make_abstract_clone_data
  (C : algebraic_base)
  (pr : ∏ {n}, stn n → C n)
  : abstract_clone_data.
Proof.
  exact (C ,, pr).
Defined.

Definition algebraic_base_from_abstract_clone (C : abstract_clone_data) : algebraic_base := pr1 C.
Coercion algebraic_base_from_abstract_clone : abstract_clone_data >-> algebraic_base.

Definition pr {C : abstract_clone_data} {n : nat} := pr2 C n.

Definition reindex {C : abstract_clone_data} {m n : nat} (a : stn m → stn n) : C m → C n := (λ f, f • (λ i, pr (a i))).

(* Define the unitality property of the algebraic theory *)
Definition comp_project_component (C : abstract_clone_data) : Prop := ∏
  (m n : nat)
  (i : stn m)
  (f : stn m → C n),
    (pr i) • f = f i.

(* Define the compatibility of the projection function with composition *)
Definition comp_identity_projections (C : abstract_clone_data) : Prop := ∏
  (n : nat)
  (f : C n),
    f • (λ i, pr i) = f.

(* Define the associativity property of the algebraic theory *)
Definition comp_is_assoc (C : abstract_clone_data) : Prop := ∏
  (l m n : nat)
  (f_l : C l)
  (f_m : stn l → C m)
  (f_n : stn m → C n),
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

Lemma isaprop_is_abstract_clone (C : abstract_clone_data) : isaprop (is_abstract_clone C).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intros);
    apply setproperty.
Qed.

Definition abstract_clone := total2 is_abstract_clone.

Definition make_abstract_clone (T : abstract_clone_data) (H : is_abstract_clone T) : abstract_clone := (T ,, H).

Definition abstract_clone_data_from_abstract_clone : abstract_clone -> abstract_clone_data := pr1.
Coercion abstract_clone_data_from_abstract_clone : abstract_clone >-> abstract_clone_data.

Lemma abstract_clone_eq
  (X Y : abstract_clone)
  (H1 : pr111 X = pr111 Y)
  (H2 : transportf _ H1 (pr211 X) = (pr211 Y))
  (H3 : transportf (λ (T : nat → hSet), (∏ n, stn n → T n)) H1 (pr21 X) = (pr21 Y))
  : X = Y.
Proof.
  destruct X as [[[Xf Xcomp] Xpr] HX].
  destruct Y as [[[Yf Ycomp] Ypr] HY].
  simpl in H1, H2, H3.
  induction H1, H2, H3.
  use (subtypePairEquality' _ (isaprop_is_abstract_clone _)).
  repeat use total2_paths2_f;
    apply idpath.
Qed.