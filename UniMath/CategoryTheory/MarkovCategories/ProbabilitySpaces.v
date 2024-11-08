(*********************************************
Probability Spaces

We define the categories of probability spaces over a causal Markov category C.
- the objects are states (X,p) (i.e. objects equipped with a probability distribution)
  * this is definitionally the same as the type [state C] of `State.v`
  * it is also definitionally the same as the type of objects of the slice category I/C
- morphisms f : (X,p) --> (Y,q) are p-almost sure equivalence classes of morphisms f : X --> Y
  which preserve the state (i.e. pf = q)

To construct this category, we use the quotient construction [mor_quot_category] of
the slice category I/C under the congruence relation given by almost-sure equality.

TODO: 
* If C has conditionals, then probability spaces become a dagger category, 
* This category is equivalent as a dagger category to the category of couplings from Couplings.v

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
Require Import UniMath.CategoryTheory.MarkovCategories.State.
Require Import UniMath.CategoryTheory.MarkovCategories.InformationFlowAxioms.
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.
Require Import UniMath.CategoryTheory.MarkovCategories.Conditionals.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section ProbabilitySpaces.
  Context {C : markov_category}
          (causality : is_causal C).
  
  Definition states_cat : category.
  Proof.
    use coslice_cat.
    + exact C.
    + exact I_{C}.
  Defined.

  (**
  In the next definition we use that states are definitionally the same as objects of states_cat.
  If that was not the case, that definition would not type check.
   *)

  Definition state_mor (p q : state C) : UU := states_cat ⟦ p, q ⟧ .

  Coercion state_mor_to_mor {p q : state C} (f : state_mor p q)
    : C ⟦ state_ob p , state_ob q ⟧ := pr1 f.

  Proposition state_mor_eq {p q : state C} (f : state_mor p q) : p · f = q.
  Proof.
    exact (pr2 f).
  Qed.

  Definition ase_states (p q : state C) : hrel (state_mor p q).
  Proof. 
    intros f g.
    use make_hProp.
    - exact (f =_{p} g).
    - apply isaprop_ase.
   Defined.

  Proposition is_eqrel_ase_states (p q : state C) : iseqrel (ase_states p q).
  Proof.
    repeat split.
    - intros f g h.
      apply ase_trans.
    - intros f g.
      apply ase_symm.
  Qed.

  Proposition ase_states_cong
              {p q r : state C}
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

  Definition ase_cong : mor_cong_rel states_cat.
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
    - exact states_cat.
    - exact ase_cong.
  Defined.

End ProbabilitySpaces.
