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

(* Some useful helper functions *)

Section Helpers.
  Context {C : markov_category}.

  (* TODO: should be under braided monoidal categories *)
  Proposition cancel_braiding {a x y : C} (f g : a --> x ⊗ y) :
    (f · sym_mon_braiding _ _ _) = (g · sym_mon_braiding _ _ _) -> f = g.
  Proof.
    intros e.
    transitivity (f · sym_mon_braiding _ _ _ · sym_mon_braiding _ _ _).
    { rewrite <- assoc, sym_mon_braiding_inv, id_right. reflexivity. }
    rewrite e.
    rewrite <- assoc, sym_mon_braiding_inv, id_right.
    reflexivity.
  Qed.

End Helpers.

(* Projections (marginals) *)

Section Marginals.
  Context {C : markov_category}.

  (* TODO: Reuse from semicartesian? *)
  Definition proj1 {x y : C} : x ⊗ y --> x := (identity _ #⊗ del _) · mon_runitor _.
  Definition proj2 {x y : C} : x ⊗ y --> y := (del _ #⊗ identity _) · mon_lunitor _.

End Marginals.

(* We define pairing notation ⟨f,g⟩ *)

Notation "⟨ f , g ⟩" := (copy _ · (f #⊗ g)).

(* TODO *)
Lemma mon_runitor_tensor {C : markov_category} {x y : C} (f : x --> y) :
   mon_runitor _ · f = (f #⊗ identity _) · mon_runitor _.
Proof. Admitted. 
Lemma mon_lunitor_tensor {C : markov_category} {x y : C} (f : x --> y) :
   mon_lunitor _ · f = (identity _ #⊗ f) · mon_lunitor _.
Proof. Admitted. 

Section PairingProperties.
  Context {C : markov_category}.

  Proposition pairing_tensor {a x y x2 y2 : C} (f : a --> x) (g : a --> y)
                                               (f2 : x --> x2) (g2 : y --> y2) :
    ⟨f,g⟩ · (f2 #⊗ g2) = ⟨f · f2, g · g2⟩.
  Proof.
    rewrite <- assoc, <- tensor_comp_mor.
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
      rewrite <- mon_runitor_tensor.
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
      rewrite <- mon_lunitor_tensor.
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

End PairingProperties.