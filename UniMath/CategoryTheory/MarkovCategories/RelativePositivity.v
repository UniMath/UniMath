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

  (* TODO bayesian_inverse *)
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

  Proposition inverse_to_bayesian_inverse 
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

  (* TODO obsolete *)
  (* ase-inverses are ase-deterministic *)
  Proposition ase_inverses_are_ase_deterministic 
    (C : markov_category) (rp : is_rel_positive C) {x y : C}
    (p : I_{C} --> x) (q : I_{C} --> y)
    (f : x --> y) (g : y --> x)
    (pres_f : p · f = q) (pres_g : q · g = p)
    (inv_fg : f · g =_{p} identity x)
    (inv_gf : g · f =_{q} identity y)
    : is_deterministic_ase p f.
  Proof.
    unfold is_deterministic_ase.
    rewrite <- pres_f in inv_gf.

    assert(fg_det_ase : is_deterministic_ase p (f · g)).
    { apply is_deterministic_ase_stable with (identity _).
      - apply ase_symm. exact inv_fg.
      - apply deterministic_implies_determinstic_ase.
        apply is_deterministic_identity. } 
    
    assert (rel_pos_eq : p · ⟨f · ⟨identity _, g⟩ , identity _⟩ 
                       = p · ⟨⟨f, f · g⟩ , identity _⟩).
    { apply equal_almost_surely_l.
      apply rel_positivity_r.
      - exact rp.
      - exact fg_det_ase. }

    (* TODO make this a lemma somewhere *)
    (* Show that f, g are necessarily Bayesian inverses of each other *)
    assert(bayes_inv : p · ⟨f, identity _⟩ = p · f · ⟨identity _, g⟩).
    { rewrite <- assoc.
      apply equal_almost_surely_composition.
      apply ase_trans with ⟨f, f · g⟩.
      { apply ase_pairing_r.
        apply ase_symm.
        exact inv_fg. }
      apply ase_symm.
      apply rel_positivity_r.
      - exact rp.
      - exact fg_det_ase. }

    apply make_equal_almost_surely_l.
    etrans. {
      rewrite <- pairing_tensor_l, assoc.
      rewrite bayes_inv.
      rewrite <- assoc, pairing_tensor_l, id_left.
      rewrite <- pairing_id.
      reflexivity.
    }

    transitivity (p · f · ⟨ ⟨ identity y, g · f ⟩, g ⟩).
    { 
      apply equal_almost_surely_l2.
      apply ase_pairing_r.
      apply ase_symm.
      exact inv_gf. 
    }

    etrans. {
      rewrite pairing_split_l, assoc.
      rewrite <- bayes_inv.
      rewrite <- assoc, pairing_tensor_l.
      rewrite <- pairing_tensor_r, assoc.
      rewrite <- pairing_tensor_l, assoc.
      rewrite rel_pos_eq.
      rewrite <- assoc.
      rewrite pairing_tensor, pairing_tensor.
      rewrite !id_right.
      reflexivity.
    }

    apply equal_almost_surely_l.
    rewrite <- pairing_eq.
    eapply ase_trans. 
    { rewrite <- pairing_tensor_r.
      apply ase_postcomp.
      apply ase_pairing_r.
      exact inv_fg. }
      
    rewrite pairing_tensor_r, id_left.
    apply ase_refl. 
  Qed.    
  
End ImplicationsBetweenAxioms.

#[global] Opaque is_rel_positive.
