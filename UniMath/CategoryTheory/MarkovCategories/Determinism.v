(*********************************************
Determinism

In this file, we provide the definition of a deterministic morphisms in a Markov category.
A morphism f : x --> y is deterministic if it commutes with copying, i.e.
[f · copy y = copy x · f #⊗ f].

In probabilitic models, this condition accurately identifies those morphisms which behave deterministically. 
The determinism condition expresses that the following are equivalent: running a computation twice,
versus running it once and copying (sharing) the result.

We give proofs of determinism of all relevant structure morphisms of the Markov category C,
and prove various lemmas about composition of deterministic maps. These lemmas unlock some mild automation:
Using a hint database [autodet], we can solve some goals of the form [is_deterministic] automatically using.

By converting all structural morphisms into explicit pairing form [⟨...⟩], we can use a calculus in the style of 
cartesian categories to reason about equalities of structural morphisms in a simpler and semi-automatic form.

We lastly give some tactics [pairing_proj_expand], [pairing_simpl] and [markov_coherence] which solve some coherence
equations automatically. TODO The automation could be vastly improved (and even made complete for some class of morphisms).

Table of Contents
1. Definition of Determinism
2. Examples and Properies
3. Automation: We provide
  - 3.1 A Hint Database [autodet]
  - 3.2 Lemmas for a Calculus of Pairings
  - 3.3 Coherence Tactics

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

(** * 1. Definition of Determinism *)

Section DefDeterminism.
  Context {C : markov_category}.

  Definition is_deterministic {x y : C} (f : x --> y) : UU
    := f · copy y = copy x · f #⊗ f.

  (* Accessors *)
  
  Proposition is_deterministic_eq {x y : C} (f : x --> y) :
    is_deterministic f -> f · copy y = copy x · f #⊗ f.
  Proof.
    intros d. exact d.
  Qed.

  Proposition is_deterministic_eq' {x y : C} (f : x --> y) :
    is_deterministic f -> f · ⟨identity y, identity y⟩ = ⟨f, f⟩.
  Proof.
    intros d. rewrite pairing_id. exact d.
  Qed.

  Proposition make_is_deterministic {x y : C} (f : x --> y) :
    f · copy y = copy x · f #⊗ f -> is_deterministic f.
  Proof.
    intros e. exact e.
  Qed.

  Proposition make_is_deterministic' {x y : C} (f : x --> y) :
    f · ⟨identity y, identity y⟩ = ⟨f, f⟩ -> is_deterministic f.
  Proof.
    intros e. rewrite pairing_id in e. exact e.
  Qed.

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

#[global] Opaque is_deterministic.

(** * 2. Examples and Properties *)

Section ExamplesAndProperties.
  Context {C : markov_category}.

  Proposition is_deterministic_identity {x : C} : 
    is_deterministic (identity x).
  Proof.
    apply make_is_deterministic.
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
    apply make_is_deterministic.
    apply is_deterministic_eq in df, dg.
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
    apply make_is_deterministic.
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
    apply make_is_deterministic.
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
    apply make_is_deterministic.
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
    apply make_is_deterministic.
    apply is_deterministic_eq in d1, d2.
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
    apply make_is_deterministic.
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
    apply make_is_deterministic.
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
    apply make_is_deterministic.
    apply is_deterministic_eq in df.
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
    apply make_is_deterministic.
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

  Proposition is_deterministic_inner_swap (x y z w : C) : is_deterministic (inner_swap C x y z w).
  Proof.
    unfold inner_swap.
    apply is_deterministic_composition; try apply is_deterministic_mon_lassociator.
    apply is_deterministic_composition; try apply is_deterministic_mon_rassociator.
    rewrite tensor_mor_left, tensor_mor_right.
    apply is_deterministic_tensor; try apply is_deterministic_identity.
    apply is_deterministic_composition; try apply is_deterministic_mon_rassociator.
    apply is_deterministic_composition; try apply is_deterministic_mon_lassociator.
    apply is_deterministic_tensor; try apply is_deterministic_sym_mon_braiding.
    apply is_deterministic_identity.
  Qed.
  
End ExamplesAndProperties.

(** * 3. Automation *)

(** ** 3.1 A Hint Database [autodet] *)

(* We can automatically derive that some morphisms are deterministic by 
   composing various primitive determinism statements *)

Create HintDb autodet.

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

#[global] Hint Resolve is_deterministic_inner_swap : autodet.

#[global] Hint Resolve deterministic_iso_to_z_iso_is_deterministic : autodet.

(** ** 3.2 Lemmas for a Calculus of Pairings *)

(* By rewriting all (deterministic) structural maps into explicit pairing form, 
   we can reason equationally about such composites.
   
   Eta-expansion for deterministic maps says that two such maps are equal if and only if 
   their marginals are equal, which lets us reduce equations further 
*)

Section PairingCalculus.
  Context {C : markov_category}.

  Lemma pairing_proj_id (x y : C) :
    identity (x ⊗ y) = ⟨proj1, proj2⟩.
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
    rewrite <- pairing_proj_id.
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

  Lemma pairing_proj_tensor {x1 x2 y1 y2 : C} (f : x1 --> y1) (g : x2 --> y2) :
    f #⊗ g = ⟨proj1 · f, proj2 · g⟩.
  Proof.
    rewrite <- pairing_tensor.
    rewrite <- pairing_proj_id, id_left.
    reflexivity.
  Qed.

  Lemma pairing_proj_whisker_l {x y z : C} (g : y --> z) :
    x ⊗^{C}_{l} g = ⟨proj1, proj2 · g⟩.
  Proof.
    rewrite tensor_mor_left, pairing_proj_tensor, id_right.
    reflexivity.
  Qed.

  Lemma pairing_proj_whisker_r {x y z : C} (f : x --> y) :
    f ⊗^{C}_{r} z = ⟨proj1 · f, proj2⟩.
  Proof.
    rewrite tensor_mor_right, pairing_proj_tensor, id_right.
    reflexivity.
  Qed.

  Lemma pairing_proj_copy {x : C} :
    copy x = ⟨identity x, identity x⟩.
  Proof.
    rewrite pairing_id.
    reflexivity.
  Qed.

  Lemma pairing_proj_braiding (x y : C) :
    sym_mon_braiding C x y = ⟨proj2, proj1⟩.
  Proof.
    apply det_eta; try auto with autodet.
    - rewrite pairing_proj1.
      rewrite sym_mon_braiding_proj1.
      reflexivity.
    - rewrite pairing_proj2.
      rewrite sym_mon_braiding_proj2.
      reflexivity.
  Qed. 

  Lemma pairing_proj_rassociator {x y z : C} :
    mon_rassociator x y z = ⟨⟨proj1, proj2 · proj1⟩, proj2 · proj2⟩.
  Proof.
    use cancel_z_iso.
    - exact (x ⊗ (y ⊗ z)).
    - apply z_iso_from_mon_lassociator.
    - cbn.
      rewrite mon_rassociator_lassociator, pairing_lassociator.
      rewrite pairing_precomp; [..|auto with autodet].
      rewrite <- pairing_proj_id, id_right.
      rewrite <- pairing_proj_id.
      reflexivity.
  Qed.

  Lemma pairing_proj_lassociator {x y z : C} :
    mon_lassociator x y z = ⟨proj1 · proj1, ⟨proj1 · proj2, proj2⟩⟩.
  Proof.
    use cancel_z_iso.
    - exact ((x ⊗ y) ⊗ z).
    - apply z_iso_from_mon_rassociator.
    - cbn.
      rewrite mon_lassociator_rassociator, pairing_rassociator.
      rewrite pairing_precomp; [..|auto with autodet].
      rewrite <- pairing_proj_id, id_right.
      rewrite pairing_proj_id.
      reflexivity.
  Qed.

  Lemma pairing_proj_lunitor {x : C} :
    mon_lunitor x = proj2.
  Proof.
    unfold proj2.
    assert(e : del I_{C} = identity I_{C}). { apply markov_category_unit_eq. }
    rewrite e, tensor_id_id, id_left.
    reflexivity.
  Qed.

  Lemma pairing_proj_linvunitor {x : C} :
    mon_linvunitor x = ⟨del x, identity x⟩.
  Proof.
    apply det_eta; try auto with autodet.
    - apply markov_category_unit_eq.
    - rewrite pairing_proj2.
      rewrite <- pairing_proj_lunitor. 
      rewrite mon_linvunitor_lunitor.
      reflexivity.
  Qed.

  Lemma pairing_proj_runitor {x : C} :
    mon_runitor x = proj1.
  Proof.
    unfold proj1.
    assert(e : del I_{C} = identity I_{C}). { apply markov_category_unit_eq. }
    rewrite e, tensor_id_id, id_left.
    reflexivity.
  Qed.

  Lemma pairing_proj_rinvunitor {x : C} :
    mon_rinvunitor x = ⟨identity x, del x⟩.
  Proof.
    apply det_eta; try auto with autodet.
    - rewrite pairing_proj1.
      rewrite <- pairing_proj_runitor. 
      rewrite mon_rinvunitor_runitor.
      reflexivity.
    - apply markov_category_unit_eq.
  Qed.

  Lemma pairing_proj_inner_swap' {x y z w : C} :
    inner_swap C x y z w = ⟨ proj1 #⊗ proj1 , proj2 #⊗ proj2 ⟩.
  Proof.
    transitivity ((⟨proj1, proj2⟩ #⊗ ⟨proj1, proj2⟩) · inner_swap C x y z w). {
      rewrite <- !pairing_proj_id, tensor_id_id, id_left.
      reflexivity.
    }
    rewrite pairing_inner_swap.
    reflexivity.
  Qed.

  Lemma pairing_proj_inner_swap {x y z w : C} :
    inner_swap C x y z w = ⟨ ⟨ proj1 · proj1 , proj2 · proj1 ⟩ , ⟨ proj1 · proj2 , proj2 · proj2 ⟩ ⟩.
  Proof.
    rewrite <- !pairing_proj_tensor.
    apply pairing_proj_inner_swap'.
  Qed. 
  
End PairingCalculus.

(** ** 3.3 Coherence Tactics *)

(* Some tactic automation for simplifying 
    some composites of structural maps, i.e.
    identities, braidings, pairings, 
    projections, tensors and associators *)

(* Expand out all all structural maps 
    in terms of just pairing and projections *)
Ltac pairing_proj_expand :=
  (repeat rewrite pairing_proj_whisker_l);
  (repeat rewrite pairing_proj_whisker_r);
  (repeat rewrite pairing_proj_tensor);
  (repeat rewrite pairing_proj_copy);
  (repeat rewrite pairing_proj_id);
  (repeat rewrite pairing_proj_braiding);
  (repeat rewrite pairing_proj_lassociator);
  (repeat rewrite pairing_proj_rassociator);
  (repeat rewrite pairing_proj_lunitor);
  (repeat rewrite pairing_proj_linvunitor);
  (repeat rewrite pairing_proj_runitor);
  (repeat rewrite pairing_proj_rinvunitor);
  (repeat rewrite pairing_proj_inner_swap).

Ltac normalize_assoc :=
  repeat rewrite assoc.

Ltac markov_step :=
     (rewrite id_left)
  || (rewrite id_right)
  || (rewrite pairing_proj1)
  || (rewrite pairing_proj2)
  || (rewrite pairing_proj1_nested)
  || (rewrite pairing_proj2_nested).

(* never fails *)

Ltac markov_simpl :=
  repeat (normalize_assoc; markov_step).

(* Missing: discharge I goals *)

Ltac markov_split :=
  repeat (apply det_eta; try auto 20 with autodet).

Ltac markov_solve :=
  pairing_proj_expand; markov_simpl; 
  try apply markov_category_unit_eq;
  try reflexivity.

Ltac markov_coherence :=
  pairing_proj_expand; markov_simpl;
  markov_split; (* split goals with eta rule *)
  markov_solve.

(* Some lemmas that are solved by the tactic *)
Section Corollaries.
  Context {C : markov_category}.

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
    markov_coherence.
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

  Proposition inner_swap_proj {x y z w : C} : 
    ⟨ ⟨ proj1 · proj1 , proj2 · proj1 ⟩ , ⟨ proj1 · proj2, proj2 · proj2 ⟩ ⟩ 
    = inner_swap _ x y z w.
  Proof.
    markov_coherence.
  Qed.

End Corollaries.

Module TacticTests.
  Section Tests.
  Context {C : markov_category}.

  Goal ∏ (x : C), proj1 · ⟨ identity x, del x ⟩ = identity _.
  Proof.
    intros x. 
    markov_coherence.
  Qed.


  (* Pentagonator *)

  Definition quasicartesian_tensor_data : tensor_data C.
  Proof. 
    use make_bifunctor_data.
    - exact (λ x y , x ⊗ y).
    - intros a b1 b2 g. exact ⟨proj1, proj2 · g⟩.
    - intros b a1 a2 f. exact ⟨proj1 · f, proj2⟩.
  Defined.

  Definition quasicartesian_monoidal_data : monoidal_data C.
  Proof.
    use make_monoidal_data.
    - exact quasicartesian_tensor_data.
    - exact I_{C}.
    - intros x. exact proj2.
    - intros x. exact ⟨del x, identity x⟩.
    - intros x. exact proj1.
    - intros x. exact ⟨identity x, del x⟩.
    - intros x y z. exact ⟨ proj1 · proj1, ⟨ proj1 · proj2, proj2 ⟩ ⟩.
    - intros x y z. cbn. exact ⟨⟨ proj1, proj2 · proj1⟩, proj2 · proj2⟩.
  Defined.  

  Proposition pentagon : pentagon_identity α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z w. cbn. 
    markov_coherence.
  Qed.

  Lemma proj1_expand {x y z : C} :
    ⟨ proj1 · proj1 , proj1 · proj2 ⟩ = @proj1 C (x ⊗ y) z.
  Proof.
    markov_coherence.
  Qed.

  Lemma proj2_expand {x y z : C} :
    ⟨ proj2 · proj1 , proj2 · proj2 ⟩ = @proj2 C z (x ⊗ y).
  Proof.
    markov_coherence.
  Qed.

  Lemma pairing_nat : ∏ (a x1 x2 y1 y2 : C)
                           (f1 : a --> x1) (f2 : a --> x2)
                           (g1 : x1 --> y1) (g2 : x2 --> y2),
            ⟨f1,f2⟩ · ⟨proj1 · g1, proj2 · g2⟩ = ⟨f1·g1, f2·g2⟩.
  Proof.
    intros a x1 x2 y1 y2 f1 f2 g1 g2.
    rewrite <- pairing_proj_tensor, pairing_tensor.
    reflexivity.
  Qed.

Lemma pairing_nat_l {a x y z : C} (f1 : a --> x) (f2 : a --> y) (g : x --> z) :
    ⟨ f1 , f2 ⟩ · ⟨ proj1 · g, proj2 ⟩ = ⟨ f1 · g, f2 ⟩.
  Proof.
    now rewrite <- (id_right proj2), pairing_nat, id_right.
  Qed.

  Lemma pairing_nat_r {a x y z : C} (f1 : a --> x) (f2 : a --> y) (g : y --> z) :
    ⟨ f1 , f2 ⟩ · ⟨ proj1 , proj2 · g ⟩ = ⟨ f1 , f2 · g ⟩.
  Proof.
    now rewrite <- (id_right proj1), pairing_nat, id_right.
  Qed.

Proposition left_whisker_natural : associator_nat_leftwhisker α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z w f. cbn.
    symmetry. etrans. {
      rewrite <- proj1_expand.
      reflexivity.
    }
    rewrite <- pairing_proj_lassociator, pairing_lassociator.
    symmetry. etrans. {
      apply maponpaths.
      apply maponpaths_2.
      rewrite <- (id_right proj1).
      reflexivity.
    }
    rewrite pairing_nat.
    etrans. {
      apply maponpaths.
      apply maponpaths.
      apply maponpaths_2.
      rewrite <- (id_right proj1).
      reflexivity.
    }
    rewrite pairing_nat, !id_right.
    reflexivity.
  Qed.

  Proposition right_whisker_natural : associator_nat_rightwhisker α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z w f. cbn.
    symmetry. etrans. {
      apply maponpaths_2.
      rewrite <- pairing_precomp; try auto with autodet.
    }
    rewrite <- pairing_proj_lassociator, pairing_lassociator.
    (* rewrite pairing_tensor_l. *)
    admit.
  Admitted.

  Proposition left_right_whisker_natural : associator_nat_leftrightwhisker α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z z2 w. cbn.
    admit.
    (* rewrite <- pairing_nat_det with (f:=proj1); try auto with autodet.
    rewrite pairing_assoc.
    now rewrite pairing_nat_r, pairing_nat_l, assoc. *)
  Admitted. 
  

  Definition quasicartesian_monoidal_laws : monoidal_laws quasicartesian_monoidal_data.
  Proof.
    repeat split.
    - (* left identity*)
       intros x y. cbn. markov_coherence.
    - (* right identity *)
      intros x y. cbn. markov_coherence.
    - (* bifunctor_leftcompax *)
      intros x b1 b2 b3 g1 g2. cbn.
      admit.
    - (* bifunctor_rightcompax *)
      intros x a1 a2 a3 f1 f2. cbn.
      admit.
    - (* functoronmorphisms_are_equal *)
      intros a1 a2 b1 b2 f g.  
      unfold functoronmorphisms1, functoronmorphisms2; cbn.
      admit.
    - (* Left unitor natural *) 
      intros x y f. cbn. markov_solve.
    - (* Left unitor iso 1 *)    
      cbn. markov_coherence.
    - (* Left unitor iso 2 *) 
      cbn. markov_solve.
    - (* Right unitor natural *)
      intros x y f. cbn. markov_solve.
    - (* Right unitor iso 1 *) 
      cbn. markov_coherence.
    - (* Right unitor iso 2 *)
      cbn. markov_solve.
    - (* Left whiskering natural *)   
      apply left_whisker_natural.
    - (* Right whiskering natural *)
      apply right_whisker_natural.
    - (* Left right whisker *)
      apply left_right_whisker_natural.
    - (* Associator iso 1 *)
      cbn. markov_coherence.
    - (* Associator iso 2 *)  
      cbn. markov_coherence.
    - (* Triangle identity *)   
      intros x y. cbn. markov_coherence.
    - (* Pentagon identity *) 
      apply pentagon.
  Admitted.

  Definition quasicartesian_monoidal : monoidal C.
  Proof.
    exact (quasicartesian_monoidal_data ,, quasicartesian_monoidal_laws).
  Defined.

  Definition quasicartesian_monoidal_cat : monoidal_cat.
  Proof.
    refine ((C :> category) ,, _).
    apply quasicartesian_monoidal.
  Defined.

  (* Symmetry *)
       
  Definition swap {x y : C} : x ⊗ y --> y ⊗ x := ⟨ proj2, proj1 ⟩.

  Definition swap_laws : sym_mon_cat_laws_tensored
       quasicartesian_monoidal_cat (λ x y : C, swap).
  Proof.
    repeat split.
    - (* involution *)
      intros x y. cbn. unfold swap.
      markov_coherence.
    - intros x y z w f g. 
      unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1. cbn.
      (* rewrite pairing_proj_braiding. *)
      rewrite !pairing_nat_r, pairing_nat.
      rewrite <- pairing_proj_braiding.
      rewrite pairing_sym_mon_braiding.
      reflexivity.
    - intros x y z. cbn. 
      unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1. cbn.
      markov_coherence.
  Defined.      

  Definition sym : symmetric quasicartesian_monoidal.
  Proof.
    use (make_symmetric quasicartesian_monoidal_cat _ _).
    - intros x y. apply swap.
    - apply swap_laws.
  Defined.
  
  Definition quasicartesian_sym_monoidal_cat : sym_monoidal_cat.
  Proof.
    refine (quasicartesian_monoidal_cat ,, sym).
  Defined.

  (* Markov category *)

  Definition quasicartesian_markov_data : markov_category_data.
  Proof.
    refine (quasicartesian_sym_monoidal_cat ,, _ ,, _).
    - intros x. refine (del x ,, _).
      intros f. markov_coherence.
    - intros x. exact ⟨ identity x , identity x ⟩.
  Defined.

  Definition quasicartesian_markov_laws : markov_category_laws quasicartesian_markov_data.
  Proof.
    repeat split; cbn; unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1; cbn.
    - intros x. markov_coherence.
    - intros x. markov_coherence.
    - intros x. markov_coherence.
    - intros x. markov_coherence.
    - intros x y. unfold inner_swap. cbn. unfold swap. 
      markov_coherence. 
  Defined.
  
  Definition quasicartesian_markov : markov_category.
  Proof.
    refine (quasicartesian_markov_data ,, quasicartesian_markov_laws).
  Defined.
End Tests.
End TacticTests.