(*********************************************
Conditionals

We define the notion of a Markov category with conditionals, 
interderivable notions such as Bayesian inverses, and derive various consequences,
such as the various information flow axioms.

1. Definition `markov_category_with_conditionals`
2. Accessors
3. Consequences and information flow axioms

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics' 
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.
Require Import UniMath.CategoryTheory.MarkovCategories.InformationFlowAxioms.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.


Section DefConditionals.
  Context {C : markov_category}.

  Definition is_conditional {a x y : C} (f : a --> x ⊗ y) (k : x ⊗ a --> y) : UU
    := f = copy a 
           · f #⊗ identity a
           · (identity x #⊗ del _) #⊗ identity a
           · mon_runitor _ #⊗ identity a
           · copy x #⊗ identity a
           · mon_lassociator _ _ _
           · identity x #⊗ k.
End DefConditionals.

Definition has_conditionals (C : markov_category) : UU :=
   ∏ (a x y : C) (f : a --> x ⊗ y),
   ∑ (k : x ⊗ a --> y), is_conditional f k.

Definition markov_category_with_conditionals : UU :=
   ∑ (C : markov_category), has_conditionals C. 

Coercion markov_cat_with_conditional_to_markov
         (C : markov_category_with_conditionals)
  : markov_category := pr1 C.

Section Accessors.
  Context {C : markov_category_with_conditionals}.

  Definition conditional {a x y : C} (f : a --> x ⊗ y) : x ⊗ a --> y
    := pr1 (pr2 C a x y f).

  Proposition conditional_eq {a x y : C} (f : a --> x ⊗ y)
    : f = copy a 
           · f #⊗ identity a
           · (identity x #⊗ del _) #⊗ identity a
           · mon_runitor _ #⊗ identity a
           · copy x #⊗ identity a
           · mon_lassociator _ _ _
           · identity x #⊗ conditional f.
  Proof.
    exact (pr2 (pr2 C a x y f)).
  Qed.
End Accessors.  

Section ConditionalsImplyPositivity.
  Context {C : markov_category_with_conditionals}.
  Context {x y z : C}.
  Context (f : x --> y) (g : y --> z).
  Context (det_fg : is_deterministic (f · g)).

  Let psi := f · copy y · g #⊗ identity _.
  Let s := conditional psi.

  Proposition K : psi
            = copy x 
              · (f · g · copy z) #⊗ identity x
              · mon_lassociator _ _ _
              · identity z #⊗ s.
  Proof. Admitted.

  Proposition pos_flipped : psi = copy x · (f · g) #⊗ f.
  Proof. Admitted.

  Proposition pos : f · copy y · identity y #⊗ g = copy x · (f #⊗ (f · g)).
  Proof.
    apply cancel_braiding.
    rewrite <- !assoc.
    rewrite! tensor_sym_mon_braiding.
    etrans. 
    { apply maponpaths.
      rewrite assoc.
      rewrite copy_comm.
      reflexivity. }
    symmetry.
    etrans.
    { rewrite assoc.
      rewrite copy_comm.
      reflexivity. }
    symmetry.
    rewrite assoc.
    apply pos_flipped.
  Qed.
  
  
End ConditionalsImplyPositivity.

(*
Section ConditionalProperties.
  Context {C : markov_category_with_conditionals}.


  Let Y := C.

  Proposition conditionals_imply_positive : is_positive C.
  Proof.
    unfold is_positive.
    intros x y z f g det_fg.
    pose(psi := f · copy y · g #⊗ identity _).
    pose(s := conditional psi).
    pose(K := conditional_eq psi).

    assert(KK : psi
            = copy x 
              · (f · g · copy z) #⊗ identity x
              · mon_lassociator _ _ _
              · identity z #⊗ s).
    {
      admit.
    }

    clear K.

    (* Main argument *)
    transitivity psi.
      
    
  
End ConditionalProperties.*)