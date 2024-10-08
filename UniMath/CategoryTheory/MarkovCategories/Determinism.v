(*********************************************
Determinism

We give the definition of deterministic morphisms in a Markov category, 
and prove basic examples and lemmas. 

Table of Contents
1. Definition of Determinism
2. Examples and Properies

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

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCat.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.

Import MonoidalNotations.
Import BifunctorNotations.

Local Open Scope cat.
Local Open Scope moncat.


(** 1. Definition of Determinism **)

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

End DefDeterminism.


(** 2. Examples and Properties **)

Section ExamplesAndProperties.
  Context {C : markov_category}.

  Proposition is_deterministic_identity {x : C} : 
    is_deterministic (identity x).
  Proof.
    unfold is_deterministic.
    rewrite tensor_id_id, id_left, id_right.
    reflexivity.
  Qed.

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

  (***** Two helper isomorphisms -- should go in Monoidal/Categories.v? **)
  Definition z_iso_from_mon_lunitor (x : C) : 
    z_iso (I_{C} ⊗ x) x.
  Proof.
    use make_z_iso.
    + apply mon_lunitor.
    + apply mon_linvunitor.
    + split.
      * apply mon_lunitor_linvunitor.
      * apply mon_linvunitor_lunitor.
  Defined.

  Definition z_iso_from_mon_runitor (x : C) : 
    z_iso (x ⊗ I_{C}) x.
  Proof.
    use make_z_iso.
    + apply mon_runitor.
    + apply mon_rinvunitor.
    + split.
      * apply mon_runitor_rinvunitor.
      * apply mon_rinvunitor_runitor.
  Defined.
  (*****************)

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

  Proposition is_deterministic_mon_lassociator {x y z : C} :
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

End ExamplesAndProperties.
