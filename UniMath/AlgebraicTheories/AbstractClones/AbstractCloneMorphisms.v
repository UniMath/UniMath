Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.

Local Open Scope algebraic_theory.

Definition abstract_clone_morphism_data (C C' : abstract_clone_data) := ∏ n, C n → C' n.

Definition preserves_composition {C C'} (F : abstract_clone_morphism_data C C') := ∏
    (m n : nat)
    (f : C m)
    (g : stn m → C n),
    F _ (f • g) = (F _ f) • (λ i, F _ (g i)).

Definition preserves_projections {C C'} (F : abstract_clone_morphism_data C C') := ∏
    (n : nat)
    (i : stn n),
    F _ (@clone_pr C n i) = @clone_pr C' n i.

Definition is_abstract_clone_morphism {C C'} (F : abstract_clone_morphism_data C C') :=
    preserves_composition F ×
    preserves_projections F.

Definition make_is_abstract_clone_morphism {C C'}
  (F : abstract_clone_morphism_data C C')
  (H1 : preserves_composition F)
  (H2 : preserves_projections F) : is_abstract_clone_morphism F := (H1 ,, H2).

Lemma isaprop_is_abstract_clone_morphism
  {C C'}
  (F : abstract_clone_morphism_data C C')
  : isaprop (is_abstract_clone_morphism F).
Proof.
  repeat apply isapropdirprod;
    repeat (apply impred_isaprop; intros);
    apply setproperty.
Qed.

Definition abstract_clone_morphism
  (C C' : abstract_clone_data)
  := total2 (@is_abstract_clone_morphism C C').

Definition make_abstract_clone_morphism
  {C C'}
  (F : abstract_clone_morphism_data C C')
  (H : is_abstract_clone_morphism F)
  : abstract_clone_morphism C C'
  := (F ,, H).

Definition abstract_clone_morphism_to_function
  {C C'}
  (F : abstract_clone_morphism C C')
  : ∏ n, C n → C' n
  := pr1 F.
Coercion abstract_clone_morphism_to_function : abstract_clone_morphism >-> Funclass.

Definition abstract_clone_morphism_eq 
  {C C'} 
  (F F' : abstract_clone_morphism C C') 
  (H1 : ∏ n f, pr1 F n f = pr1 F' n f)
  : F = F'.
Proof.
  use (subtypePairEquality' _ (isaprop_is_abstract_clone_morphism _)).
  apply funextsec.
  intro.
  apply funextfun.
  intro.
  apply H1.
Qed.
