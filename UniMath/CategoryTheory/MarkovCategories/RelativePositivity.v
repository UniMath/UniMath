(*********************************************
Relative Positivity

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
Require Import UniMath.CategoryTheory.MarkovCategories.AlmostSurely.
Require Import UniMath.CategoryTheory.MarkovCategories.Univalence.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

(** * 1. Definition of Relative Positivity *)

Section InformationFlowAxioms.
    Context (C : markov_category).

    Definition is_rel_positive : UU
        := ∏ (a x y z : C) (p : a --> x) (f : x --> y) (g : y --> z),
           is_deterministic_ase p (f · g) 
           -> f · ⟨identity _, g⟩ =_{p} ⟨f , f · g⟩.

    Proposition isaprop_is_rel_positive
      : isaprop is_rel_positive.
    Proof.
      repeat (use impred ; intro).
      apply isaprop_ase.
    Qed.

End InformationFlowAxioms.

(** * 2. Accessors *)
    
Section Accessors.
    Context (C : markov_category).

    Proposition rel_positivity_r {ispos : is_rel_positive C}
          {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z) :
      is_deterministic_ase p (f · g) -> f · ⟨identity _, g⟩ =_{p} ⟨f , f · g⟩.
    Proof. apply ispos. Qed.

    Proposition rel_positivity_l {ispos : is_rel_positive C}
          {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z) :
      is_deterministic_ase p (f · g) -> f · ⟨g, identity _⟩ =_{p} ⟨f · g, f⟩.
    Proof.
      intros det.
      apply cancel_braiding_ase.
      rewrite !assoc', !pairing_sym_mon_braiding.
      use rel_positivity_r; assumption.
    Qed.

    Proposition make_rel_positivity_r :
      (∏ {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z),
        is_deterministic_ase p (f · g) -> f · ⟨identity _, g⟩ =_{p} ⟨f , f · g⟩)
      -> is_rel_positive C.
    Proof.
      intros p. exact p.
    Qed.

    Proposition make_rel_positivity_l :
      (∏ {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z),
        is_deterministic_ase p (f · g) -> f · ⟨g, identity _⟩ =_{p} ⟨f · g, f⟩)
      -> is_rel_positive C.
    Proof.
      intros r. 
      apply make_rel_positivity_r.
      intros a x y z p f g d.
      apply cancel_braiding_ase.
      rewrite !assoc', !pairing_sym_mon_braiding.
      apply r.
      assumption.
    Qed.

End Accessors.

(** 4. Implications between the Axioms *)

Require Import UniMath.CategoryTheory.MarkovCategories.InformationFlowAxioms.

Section ImplicationsBetweenAxioms.

  Proposition rel_positive_implies_positive {C : markov_category}
    : is_rel_positive C -> is_positive C.
  Proof.
    intros rp.
    apply make_positivity_l.
    intros x y z f g det_fg.
    apply id_ase.
    apply rel_positivity_l. { exact rp. }
    apply ase_from_eq.
    exact det_fg.
  Qed.   

  (* TODO import bayesian_inverse definition? *)
  Proposition relpos_coisometry_lemma 
    (C : markov_category) (rp : is_rel_positive C) {a x y : C} (p : a --> x)
    (f : x --> y) (g : y --> x)
    (bayes_inv : p · ⟨f, identity _⟩ = p · f · ⟨identity _, g⟩)
    (inv_gf : g · f =_{p · f} identity y)
    : is_deterministic_ase p f.
  Proof.
    unfold is_deterministic_ase.

    assert(gf_det_ase : is_deterministic_ase (p · f) (g · f)).
    { apply is_deterministic_ase_stable with (identity _).
      - apply ase_symm. exact inv_gf.
      - apply deterministic_implies_determinstic_ase.
        apply is_deterministic_identity. } 

    apply make_equal_almost_surely_l.

    etrans. {
      rewrite <- pairing_tensor_l, assoc.
      rewrite bayes_inv.
      rewrite <- assoc, pairing_tensor_l.
      rewrite id_left.
      rewrite <- pairing_id.
      reflexivity.
    }

    rewrite <- pairing_eq.
    apply cancel_pairing_lassociator.

    symmetry.
    etrans. {
      rewrite pairing_split_r, assoc.
      rewrite bayes_inv.
      rewrite assoc', pairing_tensor_r.
      reflexivity.
    }
    symmetry.           

    apply equal_almost_surely_r.

    apply ase_trans with (⟨ g · f , g ⟩).
    { apply ase_pairing_l.
      apply ase_symm.
      exact inv_gf. }
    
    apply ase_symm.
    apply rel_positivity_l.
    - exact rp.
    - exact gf_det_ase.
  Qed. 

  Proposition coisometry_to_bayesian_inverse 
    (C : markov_category) (rp : is_rel_positive C) {a x y : C}
    (p : a --> x) (f : x --> y) (g : y --> x)
    : (f · g =_{p} identity x) -> p · ⟨f, identity _⟩ = p · f · ⟨identity _, g⟩.
  Proof. 
    intros inv_fg.
    rewrite <- assoc.
    apply equal_almost_surely_composition.
    apply ase_trans with ⟨f, f · g⟩.
      { apply ase_pairing_r.
        apply ase_symm.
        exact inv_fg. }
    apply ase_symm.
    apply rel_positivity_r.
      - exact rp.
      - apply is_deterministic_ase_stable with (identity _).
        apply ase_symm. exact inv_fg.
        apply deterministic_implies_determinstic_ase.
        apply is_deterministic_identity.
  Qed.
  
End ImplicationsBetweenAxioms.

Section CausalityImpliesRelPos.
  Context {C : markov_category}
          (caus : is_causal C).

  Context {a x y z : C}.
  Context (p : a --> x)
          (f : x --> y)
          (g : y --> z).
  Context (det_ase : is_deterministic_ase p (f · g)).

  Definition d : x --> z ⊗ z ⊗ y
    := ⟨f · g, f · ⟨g, identity _⟩⟩ · mon_rassociator _ _ _.

  Proposition d12 : d · proj1 = ⟨f · g, f · g⟩.
  Proof.
    unfold d.
    rewrite assoc', rassociator_proj.
    rewrite pairing_tensor.
    rewrite !assoc', pairing_proj1, id_right.
    reflexivity.
  Qed.

  Proposition aux1 : p · d · proj1 = p · f · g · copy _.
  Proof.
    rewrite !assoc'.
    apply ase_precomp.
    rewrite d12.
    rewrite assoc.
    apply ase_symm.
    exact det_ase.
  Qed.

  Proposition causality_assumption :
    p · d · proj1 · ⟨proj1, identity _⟩ = p · d · proj1 · ⟨proj2, identity _⟩.
  Proof.
    rewrite aux1.
    rewrite !assoc'.
    do 3 apply maponpaths.
    apply equal_almost_surely_l.
    apply copy_ase.
  Qed.

  Proposition causality_conclusion :
          d · ⟨proj1 · ⟨proj1, identity _⟩, identity _⟩
    =_{p} d · ⟨proj1 · ⟨proj2, identity _⟩, identity _⟩.
  Proof.
    apply make_equal_almost_surely_l.
    apply causality_l. { exact caus. }
    rewrite !assoc.
    apply causality_l. { exact caus. }
    rewrite !assoc.
    exact causality_assumption.
  Qed.

  Definition lhs : x --> z ⊗ y := d · ⟨proj1 · ⟨proj1, identity _⟩, identity _⟩ · (proj1 #⊗ proj2).
  Definition rhs : x --> z ⊗ y := d · ⟨proj1 · ⟨proj2, identity _⟩, identity _⟩ · (proj1 #⊗ proj2).

  Proposition lhs_simpl : lhs = ⟨f · g, f⟩.
  Proof. 
    unfold lhs.
    rewrite assoc'.
    rewrite pairing_tensor, id_left, assoc'.
    rewrite pairing_proj1.
    rewrite <- pairing_tensor_l, assoc.
    rewrite pairing_proj_id, id_right.
    unfold d.
    rewrite assoc', rassociator_proj1_tensor.
    rewrite pairing_tensor, !assoc'.
    rewrite pairing_proj2, !id_right.
    reflexivity.
  Qed.
      
  Proposition rhs_simpl : rhs = f · ⟨g, identity _⟩.
  Proof. 
    unfold rhs.
    rewrite assoc'.
    rewrite pairing_tensor, id_left, assoc'.
    rewrite pairing_proj1.
    rewrite <- pairing_tensor_l, assoc.
    rewrite pairing_proj_id, id_right.
    unfold d.
    rewrite assoc', rassociator_proj2_tensor.
    rewrite pairing_proj2.
    reflexivity.
  Qed.

  Proposition causality_rel_pos_aux :
    ⟨f · g, f⟩ =_{p} f · ⟨g, identity _⟩.
  Proof.
    rewrite <- lhs_simpl, <- rhs_simpl.
    unfold lhs, rhs.
    apply ase_postcomp.
    apply causality_conclusion.
  Qed.    

End CausalityImpliesRelPos.

#[global] Opaque is_rel_positive.