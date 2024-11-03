(*********************************************
Information Flow Axioms

In this file, we provide definitions for various information flow axioms in Markov categories.
1. Definition of the Information Flow Axioms 
   - causality (`is_causal`)
   - positivity (`is_positive`)
2. Accessors
   - each axiom has a left-associated and right-associated version
   - we provide both, and conversions between them
3. Consequences of Causality 
   - causality is needed for nontrivial reasoning about almost sure equality
4. Implications between the Axioms
   - causality implies positivity
   - positivity imples all isomorphisms are deterministic

References
- T. Fritz - 'A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics'
- T. Fritz, T. Gonda, N. Gauguin Houghton-Larsen, P. Perrone, D. Stein - 'Dilations and information flow axioms in categorical probability'
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

(* 1. Definition of the Information Flow Axioms *)

Section InformationFlowAxioms.
    Context (C : markov_category).

    Definition is_causal : UU
        := ∏ (x y z w : C) (f : x --> y) (g : y --> z) (h1 h2 : z --> w),
                  f · (g · ⟨h1, identity z⟩) = f · (g · ⟨h2, identity z⟩)
              ->  f · ⟨g · ⟨h1, identity z⟩, identity y⟩ = f · ⟨g · ⟨h2, identity z⟩, identity y⟩.

    Definition is_positive : UU
        := ∏ (x y z : C) (f : x --> y) (g : y --> z),
           is_deterministic (f · g) 
           -> f · ⟨identity _, g⟩ = ⟨f , f · g⟩.

End InformationFlowAxioms.

(* 2. Accessors *)

Section SwapLemmas.
    Context {C : markov_category}.
    
    Local Lemma aux_simp_l {x y z w : C} (f : x --> y) (g : y --> z) (h : z --> w) :
        f · ⟨ g · ⟨ h, identity z ⟩, identity y ⟩ 
      = f · ⟨ identity y, g · ⟨ identity z, h ⟩⟩ 
          · ((identity y #⊗ sym_mon_braiding _ _ _) · sym_mon_braiding _ _ _).
    Proof.
      rewrite !assoc, !assoc'.
      apply maponpaths.
      rewrite assoc.
      rewrite pairing_tensor.
      rewrite id_left.
      rewrite assoc'.
      rewrite !pairing_sym_mon_braiding.
      reflexivity.
    Qed.

    Local Lemma aux_simp_r {x y z w : C} (f : x --> y) (g : y --> z) (h : z --> w) :
        f · ⟨identity y, g · ⟨identity z, h⟩⟩
      = f · ⟨ g · ⟨ h, identity z ⟩, identity y ⟩ 
          · (sym_mon_braiding _ _ _ · (identity y #⊗ sym_mon_braiding _ _ _)).
    Proof.
      rewrite !assoc, !assoc'.
      apply maponpaths.
      rewrite assoc.
      rewrite pairing_sym_mon_braiding.
      rewrite pairing_tensor.
      rewrite assoc'.
      rewrite pairing_sym_mon_braiding.
      rewrite id_left.
      reflexivity.
    Qed.

    Local Lemma aux_swap_rl {x y z w : C} (f : x --> y) (g : y --> z) (h1 h2 : z --> w) :
        f · ⟨identity y, g · ⟨identity z, h1⟩⟩ = f · ⟨identity y, g · ⟨identity z, h2⟩⟩
     -> f · ⟨g · ⟨h1, identity z⟩, identity y⟩ = f · ⟨g · ⟨h2, identity z⟩, identity y⟩.
    Proof.
      intros e. 
      rewrite !aux_simp_l.
      rewrite e.
      reflexivity.
    Qed.

    Local Lemma aux_swap_lr {x y z w : C} (f : x --> y) (g : y --> z) (h1 h2 : z --> w) :
        f · ⟨g · ⟨h1, identity z⟩, identity y⟩ = f · ⟨g · ⟨h2, identity z⟩, identity y⟩
     -> f · ⟨identity y, g · ⟨identity z, h1⟩⟩ = f · ⟨identity y, g · ⟨identity z, h2⟩⟩.
    Proof. 
      intros e.
      rewrite !aux_simp_r.
      rewrite e.
      reflexivity.
    Qed.

End SwapLemmas.

Section Accessors.
    Context (C : markov_category).

    Proposition causality_l {iscaus : is_causal C} 
                    {x y z w : C} (f : x --> y) (g : y --> z) (h1 h2 : z --> w) :
           f · (g · ⟨h1, identity z⟩) = f · (g · ⟨h2, identity z⟩)
       ->  f · ⟨g · ⟨h1, identity z⟩, identity y⟩ = f · ⟨g · ⟨h2, identity z⟩, identity y⟩.
    Proof. apply iscaus. Qed.

    Proposition causality_r {iscaus : is_causal C} 
                    {x y z w : C} (f : x --> y) (g : y --> z) (h1 h2 : z --> w) :
           f · (g · ⟨identity z, h1⟩) = f · (g · ⟨identity z, h2⟩)
       ->  f · ⟨identity y, g · ⟨identity z, h1⟩⟩ = f · ⟨identity y, g · ⟨identity z, h2⟩⟩.
    Proof.
      intros e.
      apply aux_swap_lr.
      use causality_l.
      - assumption.
      - rewrite !assoc in *.
        apply pairing_flip.
        assumption.
    Qed.     

    Proposition make_causality_l :
      (∏ (x y z w : C) (f : x --> y) (g : y --> z) (h1 h2 : z --> w),
                  f · (g · ⟨h1, identity z⟩) = f · (g · ⟨h2, identity z⟩)
              ->  f · ⟨g · ⟨h1, identity z⟩, identity y⟩ = f · ⟨g · ⟨h2, identity z⟩, identity y⟩)
      -> is_causal C.
    Proof.
      intros e. exact e.
    Qed.

    Proposition make_causality_r :
      (∏ (x y z w : C) (f : x --> y) (g : y --> z) (h1 h2 : z --> w),
                  f · (g · ⟨identity z, h1⟩) = f · (g · ⟨identity z, h2⟩)
              ->  f · ⟨identity y, g · ⟨identity z, h1⟩⟩ = f · ⟨identity y, g · ⟨identity z, h2⟩⟩)
      -> is_causal C.
    Proof.
      intros caus_l. 
      apply make_causality_l.
      intros x y z w f h h1 h2 p.
      apply aux_swap_rl.
      apply caus_l.
      rewrite !assoc.
      rewrite !assoc in p.
      apply pairing_flip.
      exact p.
    Qed.

    Proposition positivity_r {ispos : is_positive C}
          {x y z : C} (f : x --> y) (g : y --> z) :
      is_deterministic(f · g) -> f · ⟨identity _, g⟩ = ⟨f , f · g⟩.
    Proof. apply ispos. Qed.

    Proposition positivity_l {ispos : is_positive C}
          {x y z : C} (f : x --> y) (g : y --> z) :
      is_deterministic(f · g) -> f · ⟨g, identity _⟩ = ⟨f · g, f⟩.
    Proof.
      intros det.
      apply cancel_braiding.
      rewrite !assoc', !pairing_sym_mon_braiding.
      use positivity_r; assumption.
    Qed.

    Proposition make_positivity_r :
      (forall {x y z : C} (f : x --> y) (g : y --> z),
        is_deterministic(f · g) -> f · ⟨identity _, g⟩ = ⟨f , f · g⟩)
      -> is_positive C.
    Proof.
      intros p. exact p.
    Qed.

    Proposition make_positivity_l :
      (forall {x y z : C} (f : x --> y) (g : y --> z),
        is_deterministic(f · g) -> f · ⟨g, identity _⟩ = ⟨f · g, f⟩)
      -> is_positive C.
    Proof.
      intros p. 
      apply make_positivity_r.
      intros x y z f g d.
      apply cancel_braiding.
      rewrite !assoc', !pairing_sym_mon_braiding.
      apply p.
      assumption.
    Qed.

End Accessors.

(* TODO Make this opaque? *)
(* #[global] Opaque is_causal is_positive. *)

(* 3. Consequences of Causality *)

Section CausalityProperties.
  Context {C : markov_category} {causality : is_causal C}.

  Proposition causal_ase {x y z w : C} (f : x --> y) (g : y --> z) (h1 h2 : z --> w) :
        h1 =_{f · g} h2
     -> g · ⟨h1, identity _⟩ =_{f} g · ⟨h2, identity _⟩.
  Proof.
    cbn.
    intros E.
    rewrite <- !assoc in E.
    apply pairing_flip.
    apply causality_l; [ assumption | ].
    rewrite assoc.
    symmetry. rewrite assoc. symmetry.
    apply pairing_flip.
    rewrite <- !assoc.
    exact E.
  Qed.

  Proposition ase_comp {x y z w : C} (f : x --> y) (g : y --> z) (h1 h2 : z --> w) :
        h1 =_{f · g} h2
     -> g · h1 =_{f} g · h2.
  Proof.
    intros E.
    assert(H2 : g · ⟨h1, identity _⟩ · proj1 =_{f} g · ⟨h2, identity _⟩ · proj1).
    { apply ase_postcomp. 
      apply causal_ase.
      exact E. }
    rewrite <- assoc in H2.
    rewrite pairing_proj1 in H2.
    rewrite <- assoc in H2.
    rewrite pairing_proj1 in H2.
    exact H2.
  Qed.

  Proposition ase_congruence
              {x y z : C}
              {f f' : x --> y}
              {g g' : y --> z}
              {p : I_{C} --> x}
              {q : I_{C} --> y}
              (e1 : f =_{p} f')
              (e2 : g =_{q} g')
              (e3 : q = p · f)
    : f · g =_{p} f' · g'.
  Proof.
    use ase_trans.
    - exact (f · g').
    - apply ase_comp.
      rewrite <- e3.
      exact e2. 
    - apply ase_postcomp.
      exact e1.
  Qed.

End CausalityProperties.

(* 4. Implications between the Axioms *)

Section ImplicationsBetweenAxioms.

  Proposition causal_implies_positive (C : markov_category) :
    is_causal C -> is_positive C.
  Proof.
  (* TODO Theorem 2.24 in [Fritz&al] *)
  Abort.

  Proposition positive_implies_all_isos_deterministic (C : markov_category) :
      is_positive C -> all_isos_deterministic C.
  Proof.
    intros pos x y f.
    unfold is_deterministic.
    pose (g := inv_from_z_iso f).

    transitivity (f · ⟨identity _ , identity _⟩).
    { rewrite pairing_id. reflexivity. }
    transitivity (f · ⟨identity _, g · f⟩).
    { unfold g. rewrite z_iso_after_z_iso_inv. reflexivity. } 
    etrans. 
    { Search pairing.
      rewrite <- pairing_tensor_l.
      rewrite !assoc.
      rewrite positivity_r.
      { rewrite pairing_tensor_l.
        unfold g.
        rewrite z_iso_inv_after_z_iso, id_left.
        reflexivity.
      }
      - exact pos.
      - rewrite z_iso_inv_after_z_iso.
        apply is_deterministic_identity.
    }
    reflexivity.
  Qed.

End ImplicationsBetweenAxioms.