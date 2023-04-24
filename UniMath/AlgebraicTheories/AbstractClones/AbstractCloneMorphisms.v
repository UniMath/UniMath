Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.

Local Open Scope algebraic_theories.

Definition abstract_clone_morphism_data (T T' : algebraic_theory_data) := ∏ n, (T n : hSet) → (T' n : hSet).

Definition abstract_clone_morphism_data_to_function {T T'} (F : abstract_clone_morphism_data T T')
  : ∏ n, (T n : hSet) → (T' n : hSet)
  := F.
Coercion abstract_clone_morphism_data_to_function : abstract_clone_morphism_data >-> Funclass.

Definition preserves_composition {T T'} (F : abstract_clone_morphism_data T T') := ∏
    (m n : nat)
    (f : (T m : hSet))
    (g : stn m → (T n : hSet)),
    F _ (f • g) = (F _ f) • (λ i, F _ (g i)).

Definition preserves_projections {T T'} (F : abstract_clone_morphism_data T T') := ∏
    (n : nat)
    (i : stn n),
    F _ (pr i) = pr i.

Definition is_abstract_clone_morphism {T T'} (F : abstract_clone_morphism_data T T') :=
    preserves_composition F ×
    preserves_projections F.

Definition make_is_abstract_clone_morphism {T T'}
  (F : abstract_clone_morphism_data T T')
  (H1 : preserves_composition F)
  (H2 : preserves_projections F) : is_abstract_clone_morphism F := (H1 ,, H2).

Lemma isaprop_is_abstract_clone_morphism
  {T T'}
  (F : abstract_clone_morphism_data T T')
  : isaprop (is_abstract_clone_morphism F).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intros);
    apply setproperty.
Qed.

Definition abstract_clone_morphism
  (T T' : algebraic_theory_data)
  := ∑ F : abstract_clone_morphism_data T T', is_abstract_clone_morphism F.

Definition make_abstract_clone_morphism
  {T T'}
  (F : abstract_clone_morphism_data T T')
  (H : is_abstract_clone_morphism F)
  : abstract_clone_morphism T T'
  := (F ,, H).

Coercion abstract_clone_morphism_to_function
  {T T'}
  (F : abstract_clone_morphism T T')
  : abstract_clone_morphism_data T T'
  := pr1 F.

(* Without pr1 F, the implicit coercion will cause errors in, for example, AbstractCloneTategory. It is not clear why. *)
Definition abstract_clone_morphism_preserves_composition {T T'} (F : abstract_clone_morphism T T') : preserves_composition F := pr12 F.

Definition abstract_clone_morphism_preserves_projections {T T'} (F : abstract_clone_morphism T T') : preserves_projections F := pr22 F.
