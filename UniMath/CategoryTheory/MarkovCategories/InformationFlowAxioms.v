(*********************************************
Information Flow Axioms

We give definitions for relevant information flow axioms in Markov categories, such as
- causality
- relative positivity
- positivity
- the deterministic marginal property
and prove their various implications.

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
    apply causality.
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

End CausalityProperties.

Section ImplicationsBetweenAxioms.

  Proposition causal_implies_positive (C : markov_category) :
    is_causal C -> is_positive C.
  Proof.
  (* TODO *)
  Admitted.

  Proposition positive_implies_all_isos_deterministic (C : markov_category) :
      is_positive C -> all_isos_deterministic C.
  Proof.
    intros positivity x y f.
    unfold is_positive in *.
    unfold is_deterministic.
    pose (g := inv_from_z_iso f).

    transitivity (f · ⟨identity _ , identity _⟩).
    { rewrite tensor_id_id, id_right. reflexivity. }
    transitivity (f · ⟨identity _, g · f⟩).
    { unfold g. rewrite z_iso_after_z_iso_inv. reflexivity. } 
    etrans. 
    { rewrite tensor_comp_id_l.
      rewrite !assoc.
      assert (aux : f · copy y · identity y #⊗ g = f · ⟨identity y , g⟩).
      { rewrite assoc. reflexivity. }
      rewrite aux.
      rewrite positivity.
      { rewrite <- assoc, <- tensor_comp_mor, id_right.
        unfold g.
        rewrite z_iso_inv_after_z_iso, id_left.
        reflexivity.
      }
      unfold g.
      rewrite z_iso_inv_after_z_iso.
      apply is_deterministic_identity.
    }
    reflexivity.
  Qed.

End ImplicationsBetweenAxioms.