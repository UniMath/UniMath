(*********************************************
Couplings

We define the category of couplings over a Markov category with conditionals

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

Definition state (C : markov_category) := ∑ (x : C), I_{C} --> x.

(* maybe not 
Coercion state_to_ob {C : markov_category} (p : state C) : C := pr1 p. *)

Coercion state_to_mor {C : markov_category} (p : state C) : I_{C} --> pr1 p
  := pr2 p.

Definition coupling {C : markov_category} {x y : C} (p : I_{C} --> x) (q : I_{C} --> y) : UU
  := ∑ (γ : I_{C} --> x ⊗ y), (γ · proj1 = p) × (γ · proj2 = q).

Proposition make_coupling {C : markov_category} {x y : C} {p : I_{C} --> x} {q : I_{C} --> y} 
    (γ : I_{C} --> x ⊗ y) (dom : γ · proj1 = p) (cod : γ · proj2 = q) : coupling p q.
Proof.
  exists γ.
  split; assumption.
Defined.

Coercion coupling_to_state {C : markov_category} {x y : C} 
        {p : I_{C} --> x} {q : I_{C} --> y} (γ : coupling p q) : I_{C} --> x ⊗ y := pr1 γ. 

Proposition coupling_ext {C : markov_category} {p q : state C} {β γ : coupling p q} :
  (coupling_to_state β) = (coupling_to_state γ) -> β = γ.
Proof.
  intros pf.
  Admitted.

Proposition coupling_dom {C : markov_category} {x y : C} 
        {p : I_{C} --> x} {q : I_{C} --> y} (γ : coupling p q) :
    γ · proj1 = p.
Proof.
  exact (pr12 γ).
Defined.

Proposition coupling_cod {C : markov_category} {x y : C} 
        {p : I_{C} --> x} {q : I_{C} --> y} (γ : coupling p q) :
    γ · proj2 = q.
Proof.
  exact (pr22 γ).
Defined.

Section CouplingCompositionLemmas.
  Context {C : markov_category_with_conditionals}.

  (* 
    Formally, the composition of couplings β and γ is only meaningful  
    if the codomain of β equals the domain of γ. 
    So it would make sense to add an extra argument
      `e : β · proj2 = γ · proj1`
    encoding this constraint to this definition.
    However, we chose to leave this out this `e` for convenience, 
    because the (opaque) definition of `coupling_composition` makes sense regardless, 
    and carrying around the proof `e` makes lemmas about `coupling_composition` harder to write.

    However, we will need the assumption `e` for the equivalent characterizations
    `coupling_composition_eq1`,`coupling_composition_eq12,`coupling_composition_eq_3`.
    
  *)
  Definition coupling_composition {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          : I_{C} --> x ⊗ z := β · proj2 · ⟨ β|2 , γ|1 ⟩.

  Proposition coupling_composition_eq {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) 
    : coupling_composition β γ = β · proj2 · ⟨ β|2 , γ|1 ⟩.
  Proof. 
    reflexivity.
  Qed.

  Proposition coupling_composition_eq_2 {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) 
    : coupling_composition β γ = β · (identity _ #⊗ γ|1).
  Proof. 
    unfold coupling_composition.
    rewrite pairing_split_r.
    rewrite assoc.
    apply maponpaths_2.
    rewrite <- conditional_distribution_2_eq.
    reflexivity.
  Qed.   

  Proposition coupling_composition_eq_3 {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) 
    : coupling_composition β γ = γ · (β|2 #⊗ identity _).
  Proof. 
    unfold coupling_composition.
    rewrite pairing_split_l.
    rewrite assoc.
    apply maponpaths_2.
    rewrite e.
    rewrite <- conditional_distribution_1_eq.
    reflexivity.
  Qed.

  Proposition coupling_composition_dom {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) :
    coupling_composition β γ · proj1 = β · proj1.
  Proof.
    rewrite coupling_composition_eq_2 ; [ | assumption ].
    rewrite assoc'.
    rewrite proj1_tensor.
    reflexivity.
  Qed.

  Proposition coupling_composition_cod {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) :
    coupling_composition β γ · proj2 = γ · proj2.
  Proof.
    rewrite coupling_composition_eq_3 ; [ | assumption ].
    rewrite assoc'.
    rewrite proj2_tensor.
    reflexivity.
  Qed.
    
  Definition identity_coupling {x : C} (p : I_{C} --> x) : I_{C} --> x ⊗ x := p · copy x.

  Proposition identity_coupling_dom {x : C} (p : I_{C} --> x) : identity_coupling p · proj1 = p.
  Proof.
    unfold identity_coupling.
    rewrite <- assoc.
    rewrite copy_proj1.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition identity_coupling_cod {x : C} (p : I_{C} --> x) : identity_coupling p · proj2 = p.
  Proof.
    unfold identity_coupling.
    rewrite <- assoc.
    rewrite copy_proj2.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition coupling_id_left {x y : C} (p : I_{C} --> x) (β : I_{C} --> x ⊗ y) 
      (e : identity_coupling p · proj2 = β · proj1) : 
    coupling_composition (identity_coupling p) β = β.
  Proof.
    assert (e2 : p = β · proj1).
    { rewrite <- e. rewrite identity_coupling_cod. reflexivity. }
    rewrite coupling_composition_eq_2 ; [ | assumption ].
    unfold identity_coupling.
    rewrite <- assoc.
    rewrite e2.
    rewrite conditional_distribution_1_eq.
    reflexivity.
  Qed.

  Proposition coupling_id_right {x y : C} (p : I_{C} --> y) (β : I_{C} --> x ⊗ y) 
      (e : β · proj2 = identity_coupling p · proj1) : 
    coupling_composition β (identity_coupling p) = β.
  Proof.
    assert (e2 : p = β · proj2).
    { rewrite e. rewrite identity_coupling_dom. reflexivity. }
    rewrite coupling_composition_eq_3 ; [ | assumption ].
    unfold identity_coupling.
    rewrite <- assoc.
    rewrite e2.
    rewrite conditional_distribution_2_eq.
    reflexivity.
  Qed.

  Local Lemma conditional_distribution_1_to_2 {x y x' y' : C}
    (β : I_{C} --> x ⊗ y)
    (f : x --> x') (g : y --> y') :
   β · proj1 · ⟨ f , β|1 · g ⟩ = β · proj2 · ⟨ β|2 · f, g ⟩.
  Proof.
    rewrite <- (id_left f).
    rewrite <- pairing_tensor.
    rewrite assoc.
    rewrite <- conditional_distribution_1_eq.
    rewrite id_left.
    rewrite <- (id_left g).
    rewrite <- pairing_tensor.
    rewrite assoc.
    rewrite <- conditional_distribution_2_eq.
    rewrite id_left.
    reflexivity.
  Qed.

  Proposition coupling_composition_assoc {x y z w : C} 
    (β : I_{C} --> x ⊗ y)
    (γ : I_{C} --> y ⊗ z)
    (δ : I_{C} --> z ⊗ w)
    (e1 : β · proj2 = γ · proj1)
    (e2 : γ · proj2 = δ · proj1)
    : coupling_composition (coupling_composition β γ) δ
      =
      coupling_composition β (coupling_composition γ δ).
  Proof.
    assert (coupling_composition β γ · proj2 = δ · proj1) as e3.
    { rewrite coupling_composition_cod ; assumption. }
    assert (β · proj2 = coupling_composition γ δ · proj1) as e4.
    { rewrite coupling_composition_dom ; assumption. }

    etrans.
    {
      repeat (rewrite coupling_composition_eq_2 ; [ | assumption ]).
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (conditional_distribution_1_eq β).
      }
      do 2 refine (assoc' _ _ _ @ _).
      rewrite <- tensor_comp_id_l.
      rewrite pairing_tensor_r.
      rewrite conditional_distribution_1_to_2.
      rewrite e1.
      rewrite conditional_distribution_1_to_2.
      rewrite e2.
      rewrite <- (id_right (δ |1)).
      rewrite conditional_distribution_1_to_2.
      rewrite id_right.
      rewrite <- pairing_tensor_l.
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (!(conditional_distribution_2_eq δ)).
    }
    repeat (rewrite coupling_composition_eq_3 ; [ | assumption ]).
    rewrite tensor_comp_id_r.
    rewrite assoc'.
    reflexivity.
  Qed.

End CouplingCompositionLemmas.


Section CouplingDaggerLemmas.
  Context {C : markov_category_with_conditionals}.

  Definition coupling_dagger {x y : C} 
          (γ : I_{C} --> x ⊗ y) : I_{C} --> y ⊗ x := γ · sym_mon_braiding _ _ _.

  Proposition coupling_dagger_dom {x y : C} (γ : I_{C} --> x ⊗ y) :
      coupling_dagger γ · proj1 = γ · proj2.
  Proof.
    unfold coupling_dagger.
    rewrite assoc', sym_mon_braiding_proj1.
    reflexivity.
  Qed.

  Proposition coupling_dagger_cod {x y : C} (γ : I_{C} --> x ⊗ y) :
      coupling_dagger γ · proj2 = γ · proj1.
  Proof.
    unfold coupling_dagger.
    rewrite assoc', sym_mon_braiding_proj2.
    reflexivity.
  Qed.

  Proposition coupling_dagger_involution {x y : C} (γ : I_{C} --> x ⊗ y) :
    coupling_dagger (coupling_dagger γ) = γ.
  Proof.
    unfold coupling_dagger.
    rewrite assoc'.
    rewrite sym_mon_braiding_inv.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition dagger_identity_coupling {x : C} {p : I_{C} --> x} :
      coupling_dagger (identity_coupling p) = identity_coupling p.
  Proof.
    unfold coupling_dagger, identity_coupling.
    rewrite assoc', copy_comm.
    reflexivity.
  Qed.

  Proposition dagger_coupling_composition {x y z : C} 
          (β : I_{C} --> x ⊗ y) (γ : I_{C} --> y ⊗ z)
          (e : β · proj2 = γ · proj1) :
      coupling_composition (coupling_dagger γ) (coupling_dagger β) 
    = coupling_dagger (coupling_composition β γ).
  Proof.
    assert(compat : coupling_dagger γ · proj2 = coupling_dagger β · proj1).
    { rewrite coupling_dagger_dom, coupling_dagger_cod, e.
      reflexivity. }

    assert(def_cond : (β · sym_mon_braiding C x y)|1 = β|2).
    { reflexivity. }

    etrans. 
    { rewrite coupling_composition_eq_2; [ | assumption ].
      unfold coupling_dagger.
      rewrite assoc'.
      rewrite <- tensor_sym_mon_braiding.
      rewrite def_cond.
      rewrite assoc.
      reflexivity.
    }
    symmetry.
    etrans.
    { rewrite coupling_composition_eq_2; [ | assumption ].
      unfold coupling_dagger.
      reflexivity. }
    apply maponpaths_2.

    rewrite <- coupling_composition_eq_2; [ | assumption ].
    rewrite <- coupling_composition_eq_3; [ | assumption ].
    reflexivity.
  Qed.

End CouplingDaggerLemmas.


Section BloomCouplingLemmas.
  Context {C : markov_category_with_conditionals}.

  Definition bloom_coupling {x y : C} (p : I_{C} --> x) (f : x --> y) : I_{C} --> x ⊗ y
    := p · ⟨identity _, f⟩.

  Proposition bloom_coupling_dom {x y : C} (p : I_{C} --> x) (f : x --> y) :
    bloom_coupling p f · proj1 = p.
  Proof.
    unfold bloom_coupling.
    rewrite assoc', pairing_proj1, id_right.
    reflexivity.
  Qed.

  Proposition bloom_coupling_cod {x y : C} (p : I_{C} --> x) (f : x --> y) :
    bloom_coupling p f · proj2 = p · f.
  Proof.
    unfold bloom_coupling.
    rewrite assoc', pairing_proj2.
    reflexivity.
  Qed.

  Proposition bloom_coupling_id {x : C} (p : I_{C} --> x) :
    bloom_coupling p (identity x) = identity_coupling p.
  Proof.
    unfold bloom_coupling, identity_coupling.
    rewrite pairing_id.
    reflexivity.
  Qed.

  Proposition bloom_coupling_conditional_1_ase {x y : C} (p : I_{C} --> x) (f : x --> y) :
    (bloom_coupling p f)|1 =_{p} f.
  Proof.
    unfold equal_almost_surely.

    assert(e :   p · ⟨ identity x, (bloom_coupling p f) |1 ⟩ 
               = bloom_coupling p f · proj1 · ⟨ identity x, (bloom_coupling p f) |1 ⟩).  
    { rewrite bloom_coupling_dom. reflexivity. }
    rewrite e. clear e.

    rewrite <- conditional_distribution_1_eq.
    reflexivity.
  Qed.

  Proposition bloom_coupling_conditional_2_ase {x y : C} (p : I_{C} --> x) (f : x --> y) :
    (bloom_coupling p f)|2 =_{p · f} bayesian_inverse p f.
  Proof.
    unfold equal_almost_surely.

    assert(e :    p · f · ⟨ identity y, (bloom_coupling p f) |2 ⟩ 
                = bloom_coupling p f · proj2 · ⟨ identity y, (bloom_coupling p f) |2 ⟩).  
    { rewrite bloom_coupling_cod. reflexivity. }
    rewrite e. clear e.

    apply cancel_braiding.
    rewrite !assoc', !pairing_sym_mon_braiding, !assoc.

    rewrite <- conditional_distribution_2_eq.
    rewrite bayesian_inverse_eq_l.
    reflexivity.
  Qed.
      
  Proposition bloom_coupling_composition {x y z : C}
            (p : I_{C} --> x) (f : x --> y) (g : y --> z) 
    :   coupling_composition (bloom_coupling p f) (bloom_coupling (p · f) g)
      = bloom_coupling p (f · g).
  Proof.
    assert(compat : bloom_coupling p f · proj2 = bloom_coupling (p · f) g · proj1).
    { rewrite bloom_coupling_dom, bloom_coupling_cod.
      reflexivity. }
  
    rewrite coupling_composition_eq_2; [ | assumption ].
    unfold bloom_coupling.
    rewrite assoc'.
    rewrite pairing_tensor.
    rewrite id_left.

    assert(target : f · (p · f · ⟨ identity y, g ⟩) |1 =_{p} f · g).
    { use ase_comp.
      - apply conditionals_imply_causality.
      - apply bloom_coupling_conditional_1_ase. }

    exact target.
  Qed.    

End BloomCouplingLemmas.

#[global] Opaque coupling_composition.

Section CouplingsCategory.
  Context {C : markov_category_with_conditionals}.

  Definition cat_couplings_identity (p : state C) : coupling p p.
    Proof.
      use make_coupling.
      - exact (identity_coupling p).
      - apply identity_coupling_dom.
      - apply identity_coupling_cod.
    Defined.

  Proposition couplings_composable {p q r : state C}
       (β : coupling p q) (γ : coupling q r) : β · proj2 = γ · proj1.
  Proof. 
    rewrite coupling_dom, coupling_cod.
    reflexivity.
  Qed.

  Definition cat_couplings_composition {p q r : state C}
       (β : coupling p q) (γ : coupling q r) : coupling p r.
  Proof.
    use make_coupling.
    - exact (coupling_composition β γ).
    - rewrite coupling_composition_dom.
      + apply coupling_dom.
      + apply couplings_composable.
    - rewrite coupling_composition_cod.
      + apply coupling_cod.
      + apply couplings_composable.
  Defined.

  Definition couplings_precategory_ob_mor
      : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (state C).
    - exact (λ p q, coupling p q).
  Defined.

  Definition couplings_precategory_data
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact couplings_precategory_ob_mor.
    - exact cat_couplings_identity.
    - intros p q r β γ. exact (cat_couplings_composition β γ).
  Defined.

  Proposition is_precategory_couplings
    : is_precategory couplings_precategory_data.
  Proof.
    use make_is_precategory_one_assoc.
    - intros p q β. 
      apply coupling_ext.
      apply coupling_id_left.
      rewrite identity_coupling_cod.
      rewrite coupling_dom.
      reflexivity.
    - intros p q β.
      apply coupling_ext.
      apply coupling_id_right.
      rewrite identity_coupling_dom.
      rewrite coupling_cod.
      reflexivity.
    - intros p q r s β γ δ.
      apply coupling_ext.
      cbn.
      rewrite coupling_composition_assoc.
      + reflexivity.
      + apply couplings_composable.
      + apply couplings_composable.
  Qed.

  Definition couplings_precategory
    : precategory.
  Proof.
    use make_precategory.
    - exact couplings_precategory_data.
    - exact is_precategory_couplings.
  Defined.

  Proposition has_homsets_couplings
    : has_homsets couplings_precategory.
  Proof.
    intros x y.
    admit. (* use coupling_ext *)
  Admitted.

  Definition couplings_category
    : category.
  Proof.
    use make_category.
    - exact couplings_precategory.
    - exact has_homsets_couplings.
  Defined.

End CouplingsCategory.
