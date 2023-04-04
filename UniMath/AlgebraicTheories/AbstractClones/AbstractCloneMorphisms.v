Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicBases.
Require Import UniMath.AlgebraicTheories.AbstractClones.AbstractClones.

Local Open Scope algebraic_theory.

Definition abstract_clone_morphism_data (C C' : abstract_clone_data) := ∏ n, C n → C' n.

Definition abstract_clone_morphism_data_to_function {C C'} (F : abstract_clone_morphism_data C C')
  : ∏ n, C n → C' n
  := F.
Coercion abstract_clone_morphism_data_to_function : abstract_clone_morphism_data >-> Funclass.

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
  := ∑ F : abstract_clone_morphism_data C C', is_abstract_clone_morphism F.

Definition make_abstract_clone_morphism
  {C C'}
  (F : abstract_clone_morphism_data C C')
  (H : is_abstract_clone_morphism F)
  : abstract_clone_morphism C C'
  := (F ,, H).

Coercion abstract_clone_morphism_to_function
  {C C'}
  (F : abstract_clone_morphism C C')
  : abstract_clone_morphism_data C C'
  := pr1 F.

(* Without pr1 F, the implicit coercion will cause errors in, for example, AbstractCloneCategory. It is not clear why. *)
Definition abstract_clone_morphism_preserves_composition {C C'} (F : abstract_clone_morphism C C') : preserves_composition (pr1 F) := pr12 F. 

Definition abstract_clone_morphism_preserves_projections {C C'} (F : abstract_clone_morphism C C') : preserves_projections (pr1 F) := pr22 F.

Definition abstract_clone_morphism_eq 
  {C C'} 
  (F F' : abstract_clone_morphism C C') 
  (H1 : ∏ n f, F n f = F' n f)
  : F = F'.
Proof.
  use (subtypePairEquality' _ (isaprop_is_abstract_clone_morphism _)).
  apply funextsec.
  intro.
  apply funextfun.
  intro.
  apply H1.
Qed.
