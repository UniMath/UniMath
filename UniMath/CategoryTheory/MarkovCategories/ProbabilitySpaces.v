(*********************************************
Probability Spaces and Couplings

We define the categories of probability spaces and couplings over a Markov category with conditionals, 
and show that they are equivalent as dagger categories.

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics' 
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Categories.Quotient.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.
Require Import UniMath.CategoryTheory.MarkovCategories.InformationFlowAxioms.
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.
Require Import UniMath.CategoryTheory.MarkovCategories.Conditionals.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section ProbabilitySpaces.
  Context {C : markov_category}
          (causality : is_causal C).
  
  Definition states : category.
  Proof.
    use coslice_cat.
    + exact C.
    + exact I_{C}.
  Defined.

  Definition state : UU := states.

  Coercion state_ob (p : state) : C := pr1 p.

  Coercion state_to_mor (p : state) : I_{C} --> p := pr2 p.

  Definition state_mor (p q : state) : UU := p --> q.

  Coercion state_mor_to_mor {p q : state} (f : state_mor p q) : C ⟦ p, q ⟧ := pr1 f.

  Proposition state_mor_eq {p q : state} (f : state_mor p q) : p · f = q.
  Proof.
    exact (pr2 f).
  Qed.

  Definition ase_states (p q : state) : hrel (state_mor p q).
  Proof. 
    intros f g.
    use make_hProp.
    - exact (f =_{p} g).
    - apply isaprop_ase.
   Defined.

  Proposition is_eqrel_ase_states (p q : state) : iseqrel (ase_states p q).
  Proof.
    repeat split.
    - intros f g h.
      apply ase_trans.
    - intros f g.
      apply ase_symm.
  Qed.

  Proposition ase_states_cong
              {p q r : state}
              {f f' : state_mor p q}
              {g g' : state_mor q r}
              (e₁ : ase_states _ _ f f')
              (e₂ : ase_states _ _ g g')
    : ase_states _ _ (f · g) (f' · g').
  Proof.
    use ase_congruence.
    - exact causality.
    - exact q.
    - exact e₁.
    - exact e₂.
    - exact (!(state_mor_eq f)).
  Qed.

  Definition ase_cong : mor_cong_rel states.
  Proof.
    use make_mor_cong_rel.
    - intros p q.
      use make_eqrel.
      + apply ase_states.
      + apply is_eqrel_ase_states.
    - intros p q r f f' g g'. 
      cbn.
      apply ase_states_cong.
  Defined.   
    

  Definition prob_space : category.
  Proof.
    use mor_quot_category.
    - exact states.
    - exact ase_cong.
  Defined.

End ProbabilitySpaces.



