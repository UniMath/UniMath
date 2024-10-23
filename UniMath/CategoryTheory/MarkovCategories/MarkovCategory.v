(*********************************************
Markov Categories

This file contains the basic definitions of the theory of Markov categories.

Table of Contents
1. Definition of Markov categories
2. Projections
3. Notations and helpers (marginals, pairing, cancellation properties)

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

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

(** 1. Definition of Markov categories **)

Definition markov_category_data : UU
  := ∑ (C : sym_monoidal_cat),
     is_semicartesian C
     ×
     ∏ (x : C), x --> x ⊗ x.

Coercion markov_category_data_to_sym_monoidal_cat
         (C : markov_category_data)
  : sym_monoidal_cat
  := pr1 C.

Proposition is_semicartesian_markov_category
            (C : markov_category_data)
  : is_semicartesian C.
Proof.
  exact (pr12 C).
Defined.

Definition copy
           {C : markov_category_data}
           (x : C)
  : x --> x ⊗ x
  := pr22 C x.

Definition del
           {C : markov_category_data}
           (x : C)
  : x --> I_{C}
  := semi_cart_to_unit (is_semicartesian_markov_category C) x.

Proposition markov_category_unit_eq
            {C : markov_category_data}
            {x : C}
            (f g : x --> I_{C})
  : f = g.
Proof.
  apply semi_cart_to_unit_eq.
  apply is_semicartesian_markov_category.
Qed.

Definition markov_category_laws
           (C : markov_category_data)
  : UU
  := (∏ (x : C),
      copy x · (identity _ #⊗ copy x)
      =
      copy x · (copy x #⊗ identity _) · mon_lassociator _ _ _)
     ×
     (∏ (x : C),
      copy x · (identity _ #⊗ del x) · mon_runitor _
      =
      identity _)
     ×
     (∏ (x : C),
      copy x · (del x #⊗ identity _) · mon_lunitor _
      =
      identity _)
     ×
     (∏ (x : C),
      copy x · sym_mon_braiding _ _ _
      =
      copy x)
     ×
     (∏ (x y : C),
      (copy x #⊗ copy y)
      · inner_swap _ _ _ _ _
      =
      copy (x ⊗ y)).

Definition markov_category
  : UU
  := ∑ (C : markov_category_data),
     markov_category_laws C.


(** 2. Projections **)

Coercion markov_category_to_data
         (C : markov_category)
  : markov_category_data
  := pr1 C.

Section MarkovCategoryLaws.
  Context (C : markov_category).

  Proposition copy_assoc'
              (x : C)
    : copy x · (identity _ #⊗ copy x)
      =
      copy x · (copy x #⊗ identity _) · mon_lassociator _ _ _.
  Proof.
    exact (pr12 C x).
  Defined.

  Proposition copy_assoc (x : C)
    : copy x · (copy x #⊗ identity _)
      =
      copy x · (identity _ #⊗ copy x) · mon_rassociator _ _ _.
  Proof.
    rewrite copy_assoc'.
    rewrite !assoc'.
    rewrite mon_lassociator_rassociator.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition copy_del_r
              (x : C)
    : copy x · (identity _ #⊗ del x) · mon_runitor _
      =
      identity _.
  Proof.
    exact (pr122 C x).
  Defined.

  Proposition copy_del_r_ex (x : C) :
    copy x · (identity _ #⊗ del x) = mon_rinvunitor _.
  Proof.
    transitivity (copy x · (identity _ #⊗ del x) · (mon_runitor _ · mon_rinvunitor _)).
    { rewrite mon_runitor_rinvunitor, id_right. reflexivity. }
    rewrite assoc.
    rewrite copy_del_r.
    rewrite id_left.
    reflexivity.
  Qed.

  Proposition copy_del_l
              (x : C)
    : copy x · (del x #⊗ identity _) · mon_lunitor _
      =
      identity _.
  Proof.
    exact (pr1 (pr222 C) x).
  Defined.

  Proposition copy_del_l_ex (x : C) :
    copy x · (del x #⊗ identity _) = mon_linvunitor _.
  Proof.
    transitivity (copy x · (del x #⊗ identity _) · (mon_lunitor _ · mon_linvunitor _)).
    { rewrite mon_lunitor_linvunitor, id_right. reflexivity. }
    rewrite assoc.
    rewrite copy_del_l.
    rewrite id_left.
    reflexivity.
  Qed.

  Proposition copy_comm
              (x : C)
    : copy x · sym_mon_braiding _ _ _
      =
      copy x.
  Proof.
    exact (pr12 (pr222 C) x).
  Defined.

  Proposition copy_tensor
              (x y : C)
    : (copy x #⊗ copy y)
      · inner_swap _ _ _ _ _
      =
      copy (x ⊗ y).
  Proof.
    exact (pr22 (pr222 C) x y).
  Defined.

  Proposition copy_I_mon_rinvunitor :
    copy (I_{C}) = mon_rinvunitor (I_{C}).
  Proof.
     use cancel_z_iso.
    - apply I_{C}.
    - use make_z_iso.
      + apply mon_runitor.
      + apply mon_rinvunitor.
      + split.
        * apply mon_runitor_rinvunitor.
        * apply mon_rinvunitor_runitor.
    - cbn.
      apply markov_category_unit_eq.
  Qed.

  Proposition copy_I_mon_linvunitor :
    copy (I_{C}) = mon_linvunitor (I_{C}).
  Proof.
    rewrite mon_linvunitor_I_mon_rinvunitor_I.
    apply copy_I_mon_rinvunitor.
  Qed.

  Proposition del_natural
            {x y : C}
            (f : x --> y)
  : f · del y = del x.
  Proof.
    apply markov_category_unit_eq.
  Qed.

End MarkovCategoryLaws.

(* Projections (marginals) *)

Section Marginals.
  Context {C : markov_category}.

  Definition proj1 {x y : C} : x ⊗ y --> x := (identity _ #⊗ del _) · mon_runitor _.
  Definition proj2 {x y : C} : x ⊗ y --> y := (del _ #⊗ identity _) · mon_lunitor _.

  Proposition copy_proj1 {x : C} : copy x · proj1 = identity x.
  Proof.
    unfold proj1.
    rewrite assoc.
    apply copy_del_r.
  Qed.

  Proposition copy_proj2 {x : C} : copy x · proj2 = identity x.
  Proof.
    unfold proj2.
    rewrite assoc.
    apply copy_del_l.
  Qed.

  Proposition proj2_naturality {x y z w : C}
                               {f : y ⊗ z --> w} :
    (proj2 #⊗ identity z) · f
    =
    mon_lassociator _ _ _ · (identity x #⊗ f) · proj2.
  Proof.
    unfold proj2.
    refine (!_).
    etrans.
    {
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_swap.
      rewrite !assoc'.
      rewrite tensor_lunitor.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_id_id.
    rewrite <- tensor_lassociator.
    rewrite tensor_comp_r_id_l.
    rewrite !assoc'.
    apply maponpaths.
    apply mon_lunitor_triangle.
  Qed.
End Marginals.

(* We define pairing notation ⟨f,g⟩ *)

Notation "⟨ f , g ⟩" := (copy _ · (f #⊗ g)).

Section PairingProperties.
  Context {C : markov_category}.

  Proposition pairing_id {x : C} : ⟨identity x, identity x⟩ = copy x.
  Proof.
    rewrite tensor_id_id, id_right.
    reflexivity.
  Qed.

  Proposition pairing_tensor {a x y x2 y2 : C} (f : a --> x) (g : a --> y)
                                               (f2 : x --> x2) (g2 : y --> y2) :
    ⟨f,g⟩ · (f2 #⊗ g2) = ⟨f · f2, g · g2⟩.
  Proof.
    rewrite <- assoc, <- tensor_comp_mor.
    reflexivity.
  Qed.

  Proposition pairing_tensor_l {a x y y2 : C} (f : a --> x) (g : a --> y)
                                                 (g2 : y --> y2) :
    ⟨f,g⟩ · (identity _ #⊗ g2) = ⟨f , g · g2⟩.
  Proof.
    rewrite pairing_tensor.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition pairing_tensor_r {a x y x2 : C} (f : a --> x) (g : a --> y)
                                               (f2 : x --> x2) :
    ⟨f,g⟩ · (f2 #⊗ identity _) = ⟨f · f2, g⟩.
  Proof.
    rewrite pairing_tensor.
    rewrite id_right.
    reflexivity.
  Qed.


  Proposition pairing_proj1 {a x y : C} (f : a --> x) (g : a --> y) :
    ⟨f,g⟩ · proj1 = f.
  Proof.
    unfold proj1.
    rewrite assoc.
    rewrite pairing_tensor.
    rewrite id_right, del_natural.
    etrans.
    { rewrite <- (id_left f).
      rewrite <- (id_right (del a)).
      rewrite tensor_comp_mor.
      rewrite assoc.
      rewrite copy_del_r_ex.
      rewrite <- assoc.
      rewrite tensor_runitor.
      rewrite assoc.
      rewrite mon_rinvunitor_runitor.
      rewrite id_left.
      reflexivity. }
    reflexivity.
  Qed.

   Proposition pairing_proj2 {a x y : C} (f : a --> x) (g : a --> y) :
    ⟨f,g⟩ · proj2 = g.
   Proof.
    unfold proj2.
    rewrite assoc.
    rewrite pairing_tensor.
    rewrite id_right, del_natural.
    etrans.
    { rewrite <- (id_left g).
      rewrite <- (id_right (del a)).
      rewrite tensor_comp_mor.
      rewrite assoc.
      rewrite copy_del_l_ex.
      rewrite <- assoc.
      rewrite tensor_lunitor.
      rewrite assoc.
      rewrite mon_linvunitor_lunitor.
      rewrite id_left.
      reflexivity. }
    reflexivity.
   Qed.

  Proposition pairing_sym_mon_braiding {a x y : C} (f : a --> x) (g : a --> y) :
    ⟨f,g⟩ · sym_mon_braiding _ _ _ = ⟨g,f⟩.
  Proof.
    rewrite <- assoc.
    rewrite tensor_sym_mon_braiding.
    rewrite assoc.
    rewrite copy_comm.
    reflexivity.
  Qed.

  Proposition pairing_lassociator {a x y z : C}
      (f : a --> x) (g : a --> y) (h : a --> z)
   : ⟨⟨f,g⟩,h⟩ · mon_lassociator _ _ _ = ⟨f,⟨g,h⟩⟩.
  Proof.
    rewrite <- (id_left h).
    rewrite <- pairing_tensor.
    rewrite copy_assoc.
    rewrite !assoc'.
    rewrite tensor_lassociator.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite mon_rassociator_lassociator.
      apply id_left.
    }
    rewrite <- tensor_comp_mor.
    rewrite !id_left.
    apply idpath.
  Qed.

  Proposition pairing_rassociator {a x y z : C}
      (f : a --> x) (g : a --> y) (h : a --> z)
   : ⟨f,⟨g,h⟩⟩ · mon_rassociator _ _ _ = ⟨⟨f,g⟩,h⟩.
  Proof.
    rewrite <- pairing_lassociator.
    rewrite !assoc'.
    rewrite mon_lassociator_rassociator.
    rewrite id_right.
    apply idpath.
  Qed.
  
  Proposition pairing_flip {a x1 x2 y z : C} (p : a --> x1) (q : a --> x2) 
        (f1 : x1 --> y) (f2 : x2 --> y)
        (g1 : x1 --> z) (g2 : x2 --> z) :
       p · ⟨f1 , g1⟩ = q · ⟨f2, g2⟩
    -> p · ⟨g1 , f1⟩ = q · ⟨g2, f2⟩.
  Proof.
    intro E.
    apply cancel_braiding.
    do 2 rewrite <- assoc, pairing_sym_mon_braiding.
    exact E.
  Qed.

End PairingProperties.
