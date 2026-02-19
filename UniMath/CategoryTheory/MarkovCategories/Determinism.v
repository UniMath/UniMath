(*********************************************
Determinism

In this file, we provide the definition of a deterministic morphisms in a Markov category.
A morphism f : x --> y is deterministic if it commutes with copying, i.e.
[f · copy y = copy x · f #⊗ f].

In probabilitic models, this condition accurately identifies those morphisms which behave deterministically. 
The determinism condition expresses that the following are equivalent: running a computation twice,
versus running it once and copying (sharing) the result.

We give proofs of determinism of all relevant structure morphisms of the Markov category C,
and prove various lemmas about composition of deterministic maps.

Table of Contents
1. Definition of Determinism
2. Examples and Properies
3. Automation
  - We provide a calculus for working with pairings 
  - A hint database [autodet] to automatically derive determinism proofs with [auto with autodet]
  - Tactics [pairing_proj_expand], [pairing_simpl] and [markov_coherence] which simplify
    or automatically solve some coherence equations by converting them into a form consisting only
    of pairings and projections.

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
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Import MonoidalNotations.
Import BifunctorNotations.

Local Open Scope cat.
Local Open Scope moncat.
Local Open Scope markov.

(** 1. Definition of Determinism *)

Section DefDeterminism.
  Context {C : markov_category}.

  Definition is_deterministic {x y : C} (f : x --> y) : UU
    := f · copy y = copy x · f #⊗ f.

  Proposition isaprop_is_deterministic
              {x y : C}
              (f : x --> y)
    : isaprop (is_deterministic f).
  Proof.
    apply homset_property.
  Qed.

  Definition deterministic_iso (x y : C) : UU
    := ∑ (f : z_iso x y), is_deterministic f. 

  Coercion deterministic_iso_to_z_iso {x y : C} 
    (f : deterministic_iso x y) : z_iso x y := pr1 f.
  
  Proposition deterministic_iso_to_z_iso_is_deterministic {x y : C}
    (f : deterministic_iso x y) : is_deterministic f.
  Proof.
    destruct f as [z d].
    exact d.
  Qed.

End DefDeterminism.

(** * 2. Examples and Properties *)

Create HintDb autodet.

Section ExamplesAndProperties.
  Context {C : markov_category}.

  Proposition is_deterministic_identity {x : C} : 
    is_deterministic (identity x).
  Proof.
    unfold is_deterministic.
    rewrite tensor_id_id, id_left, id_right.
    reflexivity.
  Qed.

  Definition identity_deterministic_iso (x : C) : deterministic_iso x x.
  Proof.
    simple refine (_ ,, _).
    + apply identity_z_iso.
    + apply is_deterministic_identity.
  Defined.

  Proposition is_deterministic_composition {x y z : C}
    {f : x --> y} {g : y --> z} 
    (df : is_deterministic f) (dg : is_deterministic g)
    : is_deterministic (f · g).
  Proof.
    unfold is_deterministic in *.
    rewrite tensor_comp_mor.
    rewrite assoc.
    rewrite <- df.
    rewrite !assoc'.
    rewrite <- dg.
    reflexivity.
  Qed.

  Proposition is_deterministic_to_terminal {x : C} (f : x --> I_{C}) :
    is_deterministic f.
  Proof.
    unfold is_deterministic.
    use cancel_z_iso.
    - apply I_{C}.
    - apply z_iso_from_mon_runitor. 
    - cbn.
      apply markov_category_unit_eq.
  Qed.

  Proposition is_deterministic_del (x : C) :
    is_deterministic (del x).
  Proof.
    apply is_deterministic_to_terminal.
  Qed.

  Proposition is_deterministic_sym_mon_braiding (x y : C) :
    is_deterministic (sym_mon_braiding _ x y).
  Proof.
    unfold is_deterministic.
    rewrite <- !copy_tensor.
    etrans.
    {
      rewrite !assoc.
      rewrite <- tensor_sym_mon_braiding.
      rewrite !assoc'.
      apply idpath. 
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite inner_swap_commute_with_swap.
    reflexivity.
  Qed.

  Proposition double_copy_assoc (x : C)
    : copy x
      · copy x #⊗ copy x
      =
      copy x
      · identity x #⊗ copy x
      · identity x #⊗ (copy x #⊗ identity x)
      · identity x #⊗ mon_lassociator x x x
      · mon_rassociator x x (x ⊗ x).
  Proof.
    etrans.
    {
      rewrite tensor_split'.
      rewrite assoc.
      rewrite copy_assoc.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite <- tensor_id_id.
        rewrite <- tensor_rassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- tensor_comp_id_l.
        apply maponpaths.
        apply copy_assoc'. 
      }
      rewrite !tensor_comp_id_l.
      reflexivity.
    }
    rewrite !assoc'.
    reflexivity.
  Qed.
      
  Proposition is_deterministic_copy (x : C) :
    is_deterministic (copy x).
  Proof.
    unfold is_deterministic.
    rewrite <- copy_tensor.
    etrans.
    {
      rewrite !assoc.
      rewrite double_copy_assoc.
      unfold inner_swap.
      etrans.
      {
        rewrite !assoc'.
        do 4 apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        rewrite tensor_mor_right.
        rewrite tensor_mor_left.
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_l.
        rewrite !assoc.
        rewrite mon_lassociator_rassociator.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- tensor_comp_id_l.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite copy_comm.
        apply idpath.
      }
      apply idpath. 
    }
    refine (!_).
    etrans.
    {
      rewrite double_copy_assoc.
      apply idpath.
    }
    rewrite tensor_comp_id_l.
    rewrite !assoc'.
    apply idpath.
  Qed.    
  
  Proposition is_deterministic_tensor {x1 x2 y1 y2 : C}
    {f1 : x1 --> y1} {f2 : x2 --> y2}
    (d1 : is_deterministic f1) (d2 : is_deterministic f2)
    : is_deterministic (f1 #⊗ f2).
  Proof.
    unfold is_deterministic in *.
    rewrite <- !copy_tensor.
    etrans.
    {
      rewrite assoc.
      rewrite <- tensor_comp_mor.
      rewrite d1, d2.
      rewrite tensor_comp_mor.
      apply idpath.
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite naturality_inner_swap.
    apply idpath.
  Qed.

  Proposition is_deterministic_mon_lunitor (x : C) :
    is_deterministic (mon_lunitor x).
  Proof.
    unfold is_deterministic.
    rewrite <- copy_tensor.
    rewrite <- precompose_inner_swap_with_lunitors_on_right.
    refine (!_).
    etrans.
    { 
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite inner_swap_inv.
      rewrite id_left.
      apply idpath.
    }
    rewrite tensor_mor_right.
    rewrite <- tensor_lunitor.
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      refine (!_).
      apply tensor_comp_mor.
    }
    rewrite id_right.
    apply maponpaths_2.
    apply markov_category_unit_eq.
  Qed.

  Proposition is_deterministic_mon_runitor (x : C) :
    is_deterministic (mon_runitor x).
  Proof.
    unfold is_deterministic.
    rewrite <- copy_tensor.
    rewrite <- precompose_inner_swap_with_lunitors_and_runitor.
    refine (!_).
    etrans.
    { 
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite inner_swap_inv.
      rewrite id_left.
      apply idpath.
    }
    rewrite tensor_mor_left.
    rewrite <- tensor_runitor.
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      refine (!_).
      apply tensor_comp_mor.
    }
    rewrite id_right.
    apply maponpaths.
    apply markov_category_unit_eq.
  Qed.

  Proposition is_deterministic_inverse {x y : C} 
    (f : z_iso x y) (df : is_deterministic f)
    : is_deterministic (inv_from_z_iso f).
  Proof.
    unfold is_deterministic in *.
    use z_iso_inv_on_right.
    rewrite assoc.
    rewrite df.
    rewrite assoc'.
    rewrite <- tensor_comp_mor.
    rewrite z_iso_inv_after_z_iso.
    rewrite tensor_id_id.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition is_deterministic_mon_linvunitor (x : C) :
    is_deterministic (mon_linvunitor x).
  Proof.
    refine (is_deterministic_inverse (z_iso_from_mon_lunitor x) _).
    cbn.
    apply is_deterministic_mon_lunitor.
  Qed.
        
  Proposition is_deterministic_mon_rinvunitor (x : C) :
    is_deterministic (mon_rinvunitor x).
  Proof.
    refine (is_deterministic_inverse (z_iso_from_mon_runitor x) _).
    cbn.
    apply is_deterministic_mon_runitor.
  Qed.  

  Proposition is_deterministic_mon_lassociator (x y z : C) :
    is_deterministic (mon_lassociator x y z).
  Proof.
    unfold is_deterministic.
    etrans.
    {
      rewrite <- !copy_tensor.
      rewrite tensor_comp_l_id_r.
      rewrite !assoc.
      rewrite <- tensor_lassociator.
      rewrite !assoc'.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite <- !copy_tensor.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      apply idpath.
    }
    apply maponpaths.
    rewrite !assoc.
    rewrite inner_swap_hexagon'.
    apply idpath.
  Qed.

  Proposition is_deterministic_mon_rassociator (x y z : C) :
    is_deterministic (mon_rassociator x y z).
  Proof.
    refine (is_deterministic_inverse (z_iso_from_mon_lassociator x y z) _).
    cbn.
    apply is_deterministic_mon_lassociator.
  Qed.

  Proposition is_deterministic_pairing {a x y : C} (f : a --> x) (g : a --> y)
    (df : is_deterministic f) (dg : is_deterministic g) : is_deterministic ⟨f, g⟩. 
  Proof.
    unfold pairing.
    apply is_deterministic_composition.
    - apply is_deterministic_copy.
    - apply is_deterministic_tensor ; assumption.
  Qed.

  Proposition is_deterministic_proj1 (x y : C) : is_deterministic (@proj1 C x y).
  Proof.
    unfold proj1.
    apply is_deterministic_composition.
    - apply is_deterministic_tensor.
      * apply is_deterministic_identity.
      * apply is_deterministic_del.
    - apply is_deterministic_mon_runitor.
  Qed.     

  Proposition is_deterministic_proj2 (x y : C) : is_deterministic (@proj2 C x y).
  Proof.
    unfold proj2.
    apply is_deterministic_composition.
    - apply is_deterministic_tensor.
      * apply is_deterministic_del.
      * apply is_deterministic_identity.
    - apply is_deterministic_mon_lunitor.
  Qed.
  
End ExamplesAndProperties.

(** * 3. Automation *)

#[global] Hint Resolve is_deterministic_identity : autodet.
#[global] Hint Resolve is_deterministic_composition : autodet.
#[global] Hint Resolve is_deterministic_del : autodet.
#[global] Hint Resolve is_deterministic_sym_mon_braiding : autodet.
#[global] Hint Resolve is_deterministic_copy : autodet.

#[global] Hint Resolve is_deterministic_mon_lassociator : autodet.
#[global] Hint Resolve is_deterministic_mon_lunitor : autodet.
#[global] Hint Resolve is_deterministic_mon_linvunitor : autodet.

#[global] Hint Resolve is_deterministic_mon_rassociator : autodet.
#[global] Hint Resolve is_deterministic_mon_runitor : autodet.
#[global] Hint Resolve is_deterministic_mon_rinvunitor : autodet.

#[global] Hint Resolve is_deterministic_tensor : autodet.
#[global] Hint Resolve is_deterministic_pairing : autodet.
#[global] Hint Resolve is_deterministic_proj1 : autodet.
#[global] Hint Resolve is_deterministic_proj2 : autodet.

#[global] Hint Resolve deterministic_iso_to_z_iso_is_deterministic : autodet.

(* A calculus for pairings, and some tactics *)

Section PairingCalculus.
  Context {C : markov_category}.

  Proposition pairing_proj_id (x y : C) :
    ⟨proj1, proj2⟩ = identity (x ⊗ y).
  Proof.
    unfold pairing.
    rewrite <- copy_tensor.
    assert(proj_inner_swap : inner_swap _ x x y y · proj1 #⊗ proj2 = proj1 #⊗ proj2).
    {
      unfold proj1, proj2.
      rewrite !tensor_comp_mor.
      rewrite !assoc.
      rewrite naturality_inner_swap.
      rewrite !assoc'.
      apply maponpaths.
      rewrite inner_swap_along_unit.
      rewrite id_left.
      apply idpath.
    }
    rewrite assoc', proj_inner_swap.
    rewrite <- tensor_comp_mor.
    rewrite copy_proj1, copy_proj2.
    rewrite tensor_id_id.
    reflexivity.
  Qed.

  Proposition pairing_proj_tensor
    {x1 x2 y1 y2 : C}
    (f : x1 --> y1) (g : x2 --> y2) 
    : ⟨proj1 · f, proj2 · g⟩ = f #⊗ g.
  Proof.
    rewrite <- pairing_tensor.
    rewrite pairing_proj_id, id_left.
    reflexivity.
  Qed.

  Proposition pairing_det {x y : C} (f : x --> y) :
    is_deterministic f -> ⟨f,f⟩ = f · ⟨identity y, identity y⟩.
  Proof.
    intros det.
    rewrite pairing_id.
    unfold pairing.
    rewrite det.
    reflexivity.
  Qed.

  Proposition pairing_precomp {x y z w : C} 
    (f : y --> z) (g : y --> w) (h : x --> y) 
    : is_deterministic h -> ⟨h · f, h · g⟩ = h · ⟨f, g⟩.
  Proof.
    intros det.
    rewrite <- pairing_tensor.
    unfold pairing.
    rewrite <- det, assoc.
    reflexivity.
  Qed.

  Proposition pairing_eta {x y z : C} (h : x --> y ⊗ z) :
    is_deterministic h -> h = ⟨h · proj1, h · proj2⟩.
  Proof.
    intros det.
    rewrite pairing_precomp ; [..|assumption].
    rewrite pairing_proj_id.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition det_eta {x y z : C} (f g : x --> y ⊗ z) 
    (df : is_deterministic f) (dg : is_deterministic g)
    : f · proj1 = g · proj1 -> f · proj2 = g · proj2 -> f = g.
  Proof.
    intros e1 e2.
    rewrite (pairing_eta f); [..|assumption].
    rewrite (pairing_eta g); [..|assumption].
    rewrite e1, e2.
    reflexivity.
  Qed.

  Proposition pairing_proj_braiding (x y : C) :
    ⟨proj2, proj1⟩ = sym_mon_braiding C x y.
  Proof.
    apply det_eta; try auto with autodet.
    - rewrite pairing_proj1.
      rewrite sym_mon_braiding_proj1.
      reflexivity.
    - rewrite pairing_proj2.
      rewrite sym_mon_braiding_proj2.
      reflexivity.
  Qed. 

  Proposition pairing_proj_rassociator {x y z : C} :
    ⟨⟨proj1, proj2 · proj1⟩, proj2 · proj2⟩ = mon_rassociator x y z.
  Proof.
    use cancel_z_iso.
    - exact (x ⊗ (y ⊗ z)).
    - apply z_iso_from_mon_lassociator.
    - cbn.
      rewrite mon_rassociator_lassociator, pairing_lassociator.
      rewrite pairing_precomp; [..|auto with autodet].
      rewrite pairing_proj_id, id_right.
      rewrite pairing_proj_id.
      reflexivity.
  Qed.

  Proposition pairing_proj_lassociator {x y z : C} :
    ⟨proj1 · proj1, ⟨proj1 · proj2, proj2⟩⟩ = mon_lassociator x y z.
  Proof.
    use cancel_z_iso.
    - exact ((x ⊗ y) ⊗ z).
    - apply z_iso_from_mon_rassociator.
    - cbn.
      rewrite mon_lassociator_rassociator, pairing_rassociator.
      rewrite pairing_precomp; [..|auto with autodet].
      rewrite pairing_proj_id, id_right.
      rewrite pairing_proj_id.
      reflexivity.
  Qed.

End PairingCalculus.

(* Some tactic automation for simplifying 
    some composites of structural maps, i.e.
    identities, braidings, pairings, 
    projections, tensors and associators *)

(* Expand out all all structural maps 
    in terms of just pairing and projections *)
Ltac pairing_proj_expand :=
  (rewrite <- !pairing_proj_id) ||
  (rewrite <- !pairing_eq) ||
  (rewrite <- !pairing_id) ||
  (rewrite <- !pairing_proj_braiding) ||
  (rewrite <- !pairing_proj_tensor) ||
  (rewrite <- !pairing_proj_lassociator) ||
  (rewrite <- !pairing_proj_rassociator).

(* Make some basic simplifications *)
Ltac pairing_simpl_basic := 
  (rewrite !pairing_proj1) ||
  (rewrite !pairing_proj2) ||
  (rewrite !id_left) ||
  (rewrite !id_right).

(* Try repeated simplification, and some
    shuffling around with associators *)
Ltac pairing_simpl := 
    repeat pairing_simpl_basic;
    try (rewrite !assoc'; pairing_simpl_basic; repeat pairing_simpl_basic);
    try (rewrite !assoc; pairing_simpl_basic; repeat pairing_simpl_basic).

(* This tactic tries to discharge or simplify 
    an equation between structural maps into tensors by eta-rule.
    - Expand both sides in terms of pairings and projections
    - Simplify
    - apply deterministic eta rule
    - dischage determinism assumptions using hints
    - simplify and see if that suffices *)
Ltac markov_coherence :=
  repeat pairing_proj_expand;
  repeat pairing_simpl;
  apply det_eta;
  try auto with autodet; 
  repeat pairing_simpl;
  try reflexivity.

(* Some lemmas that are solved by the tactic *)
Section Corollaries.
  Context {C : markov_category}.

  (* Proposition pairing_inner_swap {x y z w : C} : 
    ⟨ ⟨ proj1 · proj1 , proj2 · proj1 ⟩ , ⟨ proj1 · proj2, proj2 · proj2 ⟩ ⟩ 
    = inner_swap _ x y z w.
  Proof.
    Locate inner_swap.
    unfold inner_swap.
    rewrite tensor_mor_left, tensor_mor_right.
    markov_coherence; [auto 10 with autodet|..].
    - markov_coherence; [auto 10 with autodet|..].
      rewrite !assoc.
      pairing_simpl. *)
    

  Lemma rassociator_proj (x y z : C) :
    mon_rassociator x y z · proj1 = identity x #⊗ proj1.
  Proof.
    markov_coherence. 
  Qed.

  Lemma rassociator_proj1_tensor (x y z : C) :
    mon_rassociator x y z · proj1 #⊗ identity z = identity x #⊗ proj2.
  Proof.
    markov_coherence.
  Qed.

  Lemma rassociator_proj2_tensor (x y z : C) :
    mon_rassociator x y z · proj2 #⊗ identity z = proj2.
  Proof.
    markov_coherence.
  Qed.

  Proposition copy_copy (x : C)
    : copy x · copy (x ⊗ x) = copy x · copy x #⊗ copy x.
  Proof.
    markov_coherence; markov_coherence.
  Qed.
  
  Proposition copy_pairing 
      {x y z : C}
      {f : x ⊗ x --> y} {g : x ⊗ x --> z}
    : copy x · ⟨f,g⟩ = ⟨copy x · f, copy x · g⟩.
  Proof.
    unfold pairing.
    rewrite tensor_comp_mor, !assoc.
    apply maponpaths_2.
    rewrite copy_copy.
    reflexivity.
  Qed.

End Corollaries.