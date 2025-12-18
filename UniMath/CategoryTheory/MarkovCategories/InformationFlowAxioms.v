(*********************************************
Information Flow Axioms

In this file, we define a series of so-called information flow axioms in Markov categories, and derive some consequences.
Those axioms ensure that a Markov category supports some common probabilistic reasoning principles,  
which separates them from more exotic Markov categories (e.g. negative probability, fresh name generation, or comonoids).

Because all axioms in this file are derivable in the presence of conditionals (proved in `Conditionals/InformationFlow.v`), the axioms can be used
as powerful reasoning principles in Markov categories with conditionals. 

1. Definition of the Information Flow Axioms 
   - causality ([is_causal])
   - relative positivity ([is_rel_positive])
   - positivity ([is_positive])
   - all isomorphisms are deterministic ([all_isos_deterministic])
2. Accessors
   - each of the above axioms has a left-associated and right-associated version
     we provide both, and conversions between them.
   - we make the internal definitions opaque as to prevent a biased choice. 
3. Consequences of the Axioms 
   - causality is needed for nontrivial reasoning about almost sure equality
   - (relative) positivity implies deterministic marginal independence
4. Implications between the Axioms
   - causality => relative positivity => positivity => all isos_deterministic

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
Local Open Scope markov.

(** * 1. Definition of the Information Flow Axioms *)

Section InformationFlowAxioms.
    Context (C : markov_category).

    Definition is_causal : UU
        := ∏ (x y z w : C) (f : x --> y) (g : y --> z) (h1 h2 : z --> w),
                  f · (g · ⟨h1, identity z⟩) = f · (g · ⟨h2, identity z⟩)
              ->  f · ⟨g · ⟨h1, identity z⟩, identity y⟩ = f · ⟨g · ⟨h2, identity z⟩, identity y⟩.

    Definition is_rel_positive : UU
        := ∏ (a x y z : C) (p : a --> x) (f : x --> y) (g : y --> z),
           is_deterministic_ase p (f · g) 
           -> f · ⟨identity _, g⟩ =_{p} ⟨f , f · g⟩.

    Definition is_positive : UU
        := ∏ (x y z : C) (f : x --> y) (g : y --> z),
           is_deterministic (f · g) 
           -> f · ⟨identity _, g⟩ = ⟨f , f · g⟩.

    Proposition isaprop_is_causal : isaprop is_causal.
    Proof.
      repeat (use impred ; intro).
      apply homset_property.
    Qed.
    
    Proposition isaprop_is_rel_positive : isaprop is_rel_positive.
    Proof.
      repeat (use impred ; intro).
      apply isaprop_ase.
    Qed.

    Proposition isaprop_is_positive : isaprop is_positive.
    Proof.
      repeat (use impred ; intro).
      apply homset_property.
    Qed.

End InformationFlowAxioms.

(** * 2. Accessors *)

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

    (* Accessors for Causality *)

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

    (* Accessors for relative positivity *)
  
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

    (* Accessors for positivity *)

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
      (∏ {x y z : C} (f : x --> y) (g : y --> z),
        is_deterministic(f · g) -> f · ⟨identity _, g⟩ = ⟨f , f · g⟩)
      -> is_positive C.
    Proof.
      intros p. exact p.
    Qed.

    Proposition make_positivity_l :
      (∏ {x y z : C} (f : x --> y) (g : y --> z),
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

(** * 3. Consequences of the Axioms *)

Section CausalityConsequences.
  Context {C : markov_category} {causality : is_causal C}.

  Proposition causal_ase {x y z w : C} (f : x --> y) (g : y --> z) (h1 h2 : z --> w) :
        h1 =_{f · g} h2
     -> g · ⟨h1, identity _⟩ =_{f} g · ⟨h2, identity _⟩.
  Proof.
    cbn.
    intros E.
    apply make_equal_almost_surely_r.
    pose(F := equal_almost_surely_r _ _ _ E).
    rewrite <- !assoc in F.
    apply pairing_flip.
    apply causality_l; [ assumption | ].
    rewrite assoc.
    symmetry. rewrite assoc. symmetry.
    apply pairing_flip.
    rewrite <- !assoc.
    exact F.
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

  Proposition is_deterministic_ase_postcomp_ase
    {a x y z : C} (p : a --> x) (f : x --> y) (g : y --> z) 
    : is_deterministic_ase p f -> is_deterministic_ase (p · f) g -> is_deterministic_ase p (f · g).
  Proof.
    intros df dg.
    unfold is_deterministic_ase.
    apply ase_trans with (f · copy y · g #⊗ g).
    { 
      rewrite !assoc'.
      apply ase_comp.
      exact dg. 
    }
    rewrite !assoc', tensor_comp_mor, !assoc.
    apply ase_postcomp. 
    exact df.
  Qed.    

End CausalityConsequences.

Section PositivityConsequences.
  Context {C : markov_category}.

  (* Deterministic Marginal Independence: 
     If a morphism has a deterministic marginal, then it 
     displays the independence of its marginals. *)

  Proposition deterministic_marginal_independence_ase_1
    {a x y z : C} (relpos : is_rel_positive C)
    (p : a --> x) (f : x --> y ⊗ z)
    (det_f1 : is_deterministic_ase p (f · proj1))
    : f =_{p} ⟨f · proj1, f · proj2⟩.
  Proof.
    apply ase_trans with (f · ⟨proj1, identity _⟩ · (identity _ #⊗ proj2)).
    { apply ase_from_eq.
      rewrite assoc', <- pairing_split_r.
      rewrite pairing_proj_id.
      rewrite id_right.
      reflexivity. }
      
    apply ase_symm.
    apply ase_trans with (⟨f · proj1, f⟩ · (identity _ #⊗ proj2)).
    { apply ase_from_eq.
      rewrite pairing_tensor.
      rewrite id_right.
      reflexivity. }
    apply ase_symm.
    apply ase_postcomp.
    apply rel_positivity_l; assumption.
  Qed.

  Proposition deterministic_marginal_independence_ase_2
    {a x y z : C} (relpos : is_rel_positive C)
    (p : a --> x) (f : x --> y ⊗ z)
    (det_f2 : is_deterministic_ase p (f · proj2))
    : f =_{p} ⟨f · proj1, f · proj2⟩.
  Proof.
    pose(g := f · sym_mon_braiding _ _ _).
    assert(replace_f : f = g · sym_mon_braiding _ _ _).
    { unfold g.
      rewrite assoc', sym_mon_braiding_inv, id_right.
      reflexivity. }
    rewrite replace_f.
    rewrite !assoc', sym_mon_braiding_proj1, sym_mon_braiding_proj2.
    apply cancel_braiding_ase.
    rewrite assoc', sym_mon_braiding_inv, id_right.
    rewrite pairing_sym_mon_braiding.
    apply deterministic_marginal_independence_ase_1. { assumption. }
    rewrite <- sym_mon_braiding_proj2, assoc.
    rewrite <- replace_f.
    exact det_f2.
  Qed.

  Proposition deterministic_marginal_independence_1
    {x y z : C} (pos : is_positive C)
    (f : x --> y ⊗ z) (det_f1 : is_deterministic (f · proj1))
    : f = ⟨f · proj1, f · proj2⟩.
  Proof.
    transitivity (f · ⟨proj1, identity _⟩ · (identity _ #⊗ proj2)).
    { rewrite assoc', <- pairing_split_r.
      rewrite pairing_proj_id.
      rewrite id_right.
      reflexivity. }
      
    symmetry.
    transitivity (⟨f · proj1, f⟩ · (identity _ #⊗ proj2)).
    { rewrite pairing_tensor.
      rewrite id_right.
      reflexivity. }
    symmetry.
    apply maponpaths_2.
    apply positivity_l; assumption.
  Qed.

  Proposition deterministic_marginal_independence_2
    {x y z : C} (pos : is_positive C)
    (f : x --> y ⊗ z) (det_f2 : is_deterministic (f · proj2))
    : f = ⟨f · proj1, f · proj2⟩.
  Proof.
    pose(g := f · sym_mon_braiding _ _ _).
    assert(replace_f : f = g · sym_mon_braiding _ _ _).
    { unfold g.
      rewrite assoc', sym_mon_braiding_inv, id_right.
      reflexivity. }
    rewrite replace_f.
    rewrite !assoc', sym_mon_braiding_proj1, sym_mon_braiding_proj2.
    apply cancel_braiding.
    rewrite assoc', sym_mon_braiding_inv, id_right.
    rewrite pairing_sym_mon_braiding.
    apply deterministic_marginal_independence_1. { assumption. }
    rewrite <- sym_mon_braiding_proj2, assoc.
    rewrite <- replace_f.
    exact det_f2.
  Qed.

End PositivityConsequences.

(** 4. Implications between the Axioms *)

(* Auxiliary lemmas and definitions for the long proof that causality implies relative positivity*)
Section CausalityImpliesRelPosAux.
  Context {C : markov_category}
          (caus : is_causal C).

  Context {a x y z : C}.
  Context (p : a --> x)
          (f : x --> y)
          (g : y --> z).
  Context (det_ase : is_deterministic_ase p (f · g)).

  Local Definition d : x --> z ⊗ z ⊗ y
    := ⟨f · g, f · ⟨g, identity _⟩⟩ · mon_rassociator _ _ _.

  Local Proposition d12 : d · proj1 = ⟨f · g, f · g⟩.
  Proof.
    unfold d.
    rewrite assoc', rassociator_proj.
    rewrite pairing_tensor.
    rewrite !assoc', pairing_proj1, id_right.
    reflexivity.
  Qed.

  Local Proposition aux1 : p · d · proj1 = p · f · g · copy _.
  Proof.
    rewrite !assoc'.
    apply ase_precomp.
    rewrite d12.
    rewrite assoc.
    apply ase_symm.
    exact det_ase.
  Qed.

  Local Proposition causality_assumption :
    p · d · proj1 · ⟨proj1, identity _⟩ = p · d · proj1 · ⟨proj2, identity _⟩.
  Proof.
    rewrite aux1.
    rewrite !assoc'.
    do 3 apply maponpaths.
    apply equal_almost_surely_l.
    apply copy_ase.
  Qed.

  Local Proposition causality_conclusion :
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

  Local Definition lhs : x --> z ⊗ y := d · ⟨proj1 · ⟨proj1, identity _⟩, identity _⟩ · (proj1 #⊗ proj2).
  Local Definition rhs : x --> z ⊗ y := d · ⟨proj1 · ⟨proj2, identity _⟩, identity _⟩ · (proj1 #⊗ proj2).

  Local Proposition lhs_simpl : lhs = ⟨f · g, f⟩.
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
      
  Local Proposition rhs_simpl : rhs = f · ⟨g, identity _⟩.
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

  Local Proposition causality_rel_pos_aux :
    ⟨f · g, f⟩ =_{p} f · ⟨g, identity _⟩.
  Proof.
    rewrite <- lhs_simpl, <- rhs_simpl.
    unfold lhs, rhs.
    apply ase_postcomp.
    apply causality_conclusion.
  Qed.    

End CausalityImpliesRelPosAux.

Section ImplicationsBetweenAxioms.

  Proposition causal_implies_rel_positive {C : markov_category}
    : is_causal C -> is_rel_positive C.
  Proof.
    intros caus.
    apply make_rel_positivity_l.
    intros a x y z p f g ase.
    apply ase_symm.
    apply causality_rel_pos_aux; assumption.
  Qed.

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

  Proposition causal_implies_positive (C : markov_category) :
    is_causal C -> is_positive C.
  Proof.
    intros caus. 
    apply rel_positive_implies_positive.
    apply causal_implies_rel_positive.
    exact caus.
  Qed.    

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
    { rewrite <- pairing_tensor_r.
      rewrite !assoc.
      rewrite positivity_r.
      { rewrite pairing_tensor_r.
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

#[global] Opaque is_causal is_positive is_rel_positive.