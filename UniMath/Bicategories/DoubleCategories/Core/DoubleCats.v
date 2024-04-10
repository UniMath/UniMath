(**********************************************************************************

 Double categories

 In this file, we provide an interface for double categories. Note that in this
 file, we do not assume they are univalent. The definition that we use in this file,
 is basically the same as an object in the bicategory of univalent double categories,
 but without the univalence conditions. The purpose of this is that we get a
 definition which is usable for both univalent and strict pseudo double categories. As
 a result, the following constructions and proofs can be proven uniformly for univalent
 and for strict pseudo double categories:
 - Laws on the unitors (right unitor and left unitor agree on the identity)
 - Horizontal bicategory
 - Vertical 2-category

 Contents
 1. Double categories
 2. Accessors for double categories
 2.1. The vertical category
 2.2. Horizontal morphisms
 2.3. Squares
 2.4. Functoriality of horizontal identities
 2.5. Functoriality of horizontal composition
 2.6. Left unitor
 2.7. Right unitor
 2.8. Associator
 2.9. Triangle and pentagon equations
 3. Builder for double categories
 4. Squares and equalities

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.

Local Open Scope cat.

Declare Scope double_cat.

Local Open Scope double_cat.

(** * 1. Double categories *)
Definition double_cat
  : UU
  := ∑ (C : category)
       (D : twosided_disp_cat C C)
       (I : hor_id D)
       (Cm : hor_comp D)
       (l : double_cat_lunitor I Cm)
       (r : double_cat_runitor I Cm)
       (a : double_cat_associator Cm),
     triangle_law l r a × pentagon_law a.

(** * 2. Accessors for double categories *)

(** ** 2.1. The vertical category *)
Definition ob_double_cat
           (C : double_cat)
  : category
  := pr1 C.

Coercion ob_double_cat : double_cat >-> category.

Definition ver_mor_double_cat
           {C : double_cat}
           (x y : C)
  : UU
  := x --> y.

Notation "x -->v y" := (ver_mor_double_cat x y) (at level 55) : double_cat.

Definition identity_v
           {C : double_cat}
           (x : C)
  : x -->v x
  := identity _.

Definition ver_comp_double_cat
           {C : double_cat}
           {x y z : C}
           (f : x -->v y)
           (g : y -->v z)
  : x -->v z
  := f · g.

Notation "f ·v g" := (ver_comp_double_cat f g) (at level 60) : double_cat.

Proposition id_v_left
            {C : double_cat}
            {x y : C}
            (f : x -->v y)
  : identity_v x · f = f.
Proof.
  apply id_left.
Defined.

Proposition id_v_right
            {C : double_cat}
            {x y : C}
            (f : x -->v y)
  : f ·v identity_v y = f.
Proof.
  apply id_right.
Defined.

Proposition assocl_v
            {C : double_cat}
            {w x y z : C}
            (f : w -->v x)
            (g : x -->v y)
            (h : y -->v z)
  : f ·v (g ·v h) = (f ·v g) ·v h.
Proof.
  apply assoc.
Defined.

Proposition assocr_v
            {C : double_cat}
            {w x y z : C}
            (f : w -->v x)
            (g : x -->v y)
            (h : y -->v z)
  : (f ·v g) ·v h = f ·v (g ·v h).
Proof.
  apply assoc'.
Defined.

Proposition isaset_ver_mor
            {C : double_cat}
            (x y : C)
  : isaset (x -->v y).
Proof.
  apply homset_property.
Qed.

(** ** 2.2. Horizontal morphisms *)
Definition hor_mor
           (C : double_cat)
  : twosided_disp_cat C C
  := pr12 C.

Notation "x -->h y" := (hor_mor _ x y) (at level 55) : double_cat.

Definition hor_id_double_cat
           (C : double_cat)
  : hor_id (hor_mor C)
  := pr122 C.

Definition identity_h
           {C : double_cat}
           (x : C)
  : x -->h x
  := double_id (hor_id_double_cat C) x.

Definition hor_comp_double_cat
           (C : double_cat)
  : hor_comp (hor_mor C)
  := pr1 (pr222 C).

Definition hor_mor_comp_double_cat
           {C : double_cat}
           {x y z : C}
           (f : x -->h y)
           (g : y -->h z)
  : x -->h z
  := double_hor_comp (hor_comp_double_cat C) f g.

Notation "f ·h g" := (hor_mor_comp_double_cat f g) (at level 60) : double_cat.

(** ** 2.3. Squares *)
Definition square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ : C}
           (v₁ : x₁ -->v y₁)
           (v₂ : x₂ -->v y₂)
           (h₁ : x₁ -->h x₂)
           (h₂ : y₁ -->h y₂)
  : UU
  := h₁ -->[ v₁ ][ v₂ ] h₂.

Proposition isaset_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            (v₁ : x₁ -->v y₁)
            (v₂ : x₂ -->v y₂)
            (h₁ : x₁ -->h x₂)
            (h₂ : y₁ -->h y₂)
  : isaset (square v₁ v₂ h₁ h₂).
Proof.
  apply isaset_disp_mor.
Qed.

Definition id_v_square
           {C : double_cat}
           {x y : C}
           (h : x -->h y)
  : square (identity_v x) (identity_v y) h h
  := id_two_disp _.

Definition comp_v_square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ z₁ z₂ : C}
           {v₁ : x₁ -->v y₁} {v₁' : y₁ --> z₁}
           {v₂ : x₂ -->v y₂} {v₂' : y₂ --> z₂}
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           {h₃ : z₁ -->h z₂}
           (s₁ : square v₁ v₂ h₁ h₂)
           (s₂ : square v₁' v₂' h₂ h₃)
  : square (v₁ ·v v₁') (v₂ ·v v₂') h₁ h₃
  := s₁ ;;2 s₂.

Notation "s₁ ⋆v s₂" := (comp_v_square s₁ s₂) (at level 40, left associativity) : double_cat.

Definition transportf_square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ : C}
           {v₁ v₁' : x₁ -->v y₁}
           {v₂ v₂' : x₂ -->v y₂}
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           (p : v₁ = v₁')
           (q : v₂ = v₂')
           (s : square v₁ v₂ h₁ h₂)
  : square v₁' v₂' h₁ h₂
  := transportf_disp_mor2 p q s.

Definition transportb_square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ : C}
           {v₁ v₁' : x₁ -->v y₁}
           {v₂ v₂' : x₂ -->v y₂}
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           (p : v₁ = v₁')
           (q : v₂ = v₂')
           (s : square v₁' v₂' h₁ h₂)
  : square v₁ v₂ h₁ h₂
  := transportf_square (!p) (!q) s.

Proposition transportfb_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ v₁' : x₁ -->v y₁}
            {v₂ v₂' : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p : v₁ = v₁')
            (q : v₂ = v₂')
            (s : square v₁' v₂' h₁ h₂)
  : transportf_square p q (transportb_square p q s) = s.
Proof.
  induction p, q.
  apply idpath.
Qed.

Proposition transportfb_square'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ v₁' : x₁ -->v y₁}
            {v₂ v₂' : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p p' : v₁ = v₁')
            (q q' : v₂ = v₂')
            (s : square v₁' v₂' h₁ h₂)
  : transportf_square p q (transportb_square p' q' s) = s.
Proof.
  induction p, q.
  assert (p' = idpath _) as r by apply isaset_ver_mor.
  rewrite r ; clear r.
  assert (q' = idpath _) as r by apply isaset_ver_mor.
  rewrite r ; clear r.
  apply idpath.
Qed.

Proposition transportbf_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ v₁' : x₁ -->v y₁}
            {v₂ v₂' : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p : v₁ = v₁')
            (q : v₂ = v₂')
            (s : square v₁ v₂ h₁ h₂)
  : transportb_square p q (transportf_square p q s) = s.
Proof.
  induction p, q.
  apply idpath.
Qed.

Proposition transportbf_square'
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ v₁' : x₁ -->v y₁}
            {v₂ v₂' : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (p p' : v₁ = v₁')
            (q q' : v₂ = v₂')
            (s : square v₁ v₂ h₁ h₂)
  : transportb_square p q (transportf_square p' q' s) = s.
Proof.
  induction p, q.
  assert (p' = idpath _) as r by apply isaset_ver_mor.
  rewrite r ; clear r.
  assert (q' = idpath _) as r by apply isaset_ver_mor.
  rewrite r ; clear r.
  apply idpath.
Qed.

Proposition square_id_left_v
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : id_v_square h₁ ⋆v s
    =
    transportb_square (id_left _) (id_left _) s.
Proof.
  apply id_two_disp_left.
Defined.

Proposition square_id_right_v
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : s ⋆v id_v_square h₂
    =
    transportb_square (id_right _) (id_right _) s.
Proof.
  apply id_two_disp_right.
Defined.

Proposition square_assoc_v
            {C : double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : w₁ -->v x₁} {v₁' : x₁ -->v y₁} {v₁'' : y₁ -->v z₁}
            {v₂ : w₂ -->v x₂} {v₂' : x₂ -->v y₂} {v₂'' : y₂ -->v z₂}
            {h₁ : w₁ -->h w₂}
            {h₂ : x₁ -->h x₂}
            {h₃ : y₁ -->h y₂}
            {h₄ : z₁ -->h z₂}
            (s₁ : square v₁ v₂ h₁ h₂)
            (s₂ : square v₁' v₂' h₂ h₃)
            (s₃ : square v₁'' v₂'' h₃ h₄)
  : s₁ ⋆v (s₂ ⋆v s₃)
    =
    transportb_square (assoc _ _ _) (assoc _ _ _) ((s₁ ⋆v s₂) ⋆v s₃).
Proof.
  exact (assoc_two_disp s₁ s₂ s₃).
Defined.

Definition globular_iso_square
           {C : double_cat}
           {x y : C}
           (h₁ h₂ : x -->h y)
  : UU
  := iso_twosided_disp (identity_z_iso _) (identity_z_iso _) h₁ h₂.

Coercion globular_iso_square_to_hor_mor
          {C : double_cat}
          {x y : C}
          {h₁ h₂ : x -->h y}
          (s : globular_iso_square h₁ h₂)
  : square (identity_v _) (identity_v _) h₁ h₂
  := pr1 s.

Definition globular_iso_square_inv
           {C : double_cat}
           {x y : C}
           {h₁ h₂ : x -->h y}
           (s : globular_iso_square h₁ h₂)
  : square (identity_v _) (identity_v _) h₂ h₁
  := pr12 s.

Proposition globular_iso_square_left
            {C : double_cat}
            {x y : C}
            {h₁ h₂ : x -->h y}
            (s : globular_iso_square h₁ h₂)
  : s ⋆v globular_iso_square_inv s
    =
    transportb_square (id_v_left _) (id_v_left _) (id_v_square _).
Proof.
  exact (pr122 s).
Defined.

Proposition globular_iso_square_right
            {C : double_cat}
            {x y : C}
            {h₁ h₂ : x -->h y}
            (s : globular_iso_square h₁ h₂)
  : globular_iso_square_inv s ⋆v s
    =
    transportb_square (id_v_left _) (id_v_left _) (id_v_square _).
Proof.
  exact (pr222 s).
Defined.

Definition path_to_globular_iso_square
           {C : double_cat}
           {x y : C}
           {h₁ h₂ : x -->h y}
           (p : h₁ = h₂)
  : globular_iso_square h₁ h₂
  := idtoiso_twosided_disp (idpath _) (idpath _) p.

(** ** 2.4. Functoriality of horizontal identities *)
Definition id_h_square
           {C : double_cat}
           {x y : C}
           (v : x -->v y)
  : square v v (identity_h x) (identity_h y)
  := double_id_mor (hor_id_double_cat C) v.

Proposition id_h_square_id
            {C : double_cat}
            (x : C)
  : id_h_square (identity_v x) = id_v_square (identity_h x).
Proof.
  apply double_id_mor_id.
Defined.

Proposition id_h_square_comp
            {C : double_cat}
            {x y z : C}
            (v₁ : x -->v y)
            (v₂ : y -->v z)
  : id_h_square (v₁ ·v v₂)
    =
    id_h_square v₁ ⋆v id_h_square v₂.
Proof.
  apply double_id_mor_id_comp.
Defined.

(** ** 2.5. Functoriality of horizontal composition *)
Definition comp_h_square
           {C : double_cat}
           {x₁ x₂ y₁ y₂ z₁ z₂ : C}
           {v₁ : x₁ -->v x₂}
           {v₂ : y₁ -->v y₂}
           {v₃ : z₁ -->v z₂}
           {h₁ : x₁ -->h y₁}
           {h₂ : y₁ -->h z₁}
           {k₁ : x₂ -->h y₂}
           {k₂ : y₂ -->h z₂}
           (s₁ : square v₁ v₂ h₁ k₁)
           (s₂ : square v₂ v₃ h₂ k₂)
  : square v₁ v₃ (h₁ ·h h₂) (k₁ ·h k₂)
  := double_hor_comp_mor (hor_comp_double_cat C) s₁ s₂.

Notation "s₁ ⋆h s₂" := (comp_h_square s₁ s₂) (at level 37, left associativity) : double_cat.

Proposition comp_h_square_id
            {C : double_cat}
            {x y z : C}
            (h₁ : x -->h y)
            (h₂ : y -->h z)
  : id_v_square h₁ ⋆h id_v_square h₂ = id_v_square (h₁ ·h h₂).
Proof.
  apply double_hor_comp_mor_id.
Defined.

Proposition comp_h_square_comp
            {C : double_cat}
            {x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C}
            {v₁ : x₁ -->v x₂} {v₁' : x₂ -->v x₃}
            {v₂ : y₁ -->v y₂} {v₂' : y₂ -->v y₃}
            {v₃ : z₁ -->v z₂} {v₃' : z₂ -->v z₃}
            {h₁ : x₁ -->h y₁} {h₂ : y₁ -->h z₁}
            {k₁ : x₂ -->h y₂} {k₂ : y₂ -->h z₂}
            {l₁ : x₃ -->h y₃} {l₂ : y₃ -->h z₃}
            (s₁ : square v₁ v₂ h₁ k₁)
            (s₁' : square v₁' v₂' k₁ l₁)
            (s₂ : square v₂ v₃ h₂ k₂)
            (s₂' : square v₂' v₃' k₂ l₂)
  : (s₁ ⋆v s₁') ⋆h (s₂ ⋆v s₂') = (s₁ ⋆h s₂) ⋆v (s₁' ⋆h s₂').
Proof.
  apply double_hor_comp_mor_comp.
Defined.

(** ** 2.6. Left unitor *)
Definition double_cat_double_lunitor
           (C : double_cat)
  : double_cat_lunitor (hor_id_double_cat C) (hor_comp_double_cat C)
  := pr12 (pr222 C).

Definition lunitor_h
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : square (identity_v x) (identity_v y) (identity_h x ·h f) f
  := double_lunitor (double_cat_double_lunitor C) f.

Definition lunitor_globular_iso_square
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : globular_iso_square (identity_h x ·h f) f
  := pr112 (pr222 C) x y f.

Definition linvunitor_h
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : square (identity_v x) (identity_v y) f (identity_h x ·h f)
  := globular_iso_square_inv (lunitor_globular_iso_square f).

Proposition lunitor_linvunitor_h
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : lunitor_h f ⋆v linvunitor_h f
    =
      transportb_square (id_v_left _) (id_v_left _) (id_v_square _).
Proof.
  apply globular_iso_square_left.
Defined.

Proposition linvunitor_lunitor_h
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : linvunitor_h f ⋆v lunitor_h f
    =
    transportb_square (id_v_left _) (id_v_left _) (id_v_square _).
Proof.
  apply globular_iso_square_right.
Defined.

Proposition lunitor_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : (id_h_square _ ⋆h s) ⋆v lunitor_h h₂
    =
    transportb_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (lunitor_h h₁ ⋆v s).
Proof.
  exact (!(double_lunitor_nat (double_cat_double_lunitor C) s)).
Defined.

(** ** 2.7. Right unitor *)
Definition double_cat_double_runitor
           (C : double_cat)
  : double_cat_runitor (hor_id_double_cat C) (hor_comp_double_cat C)
  := pr122 (pr222 C).

Definition runitor_h
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : square (identity_v x) (identity_v y) (f ·h identity_h y) f
  := double_runitor (double_cat_double_runitor C) f.

Definition runitor_globular_iso_square
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : globular_iso_square (f ·h identity_h y) f
  := pr1 (pr122 (pr222 C)) x y f.

Definition rinvunitor_h
           {C : double_cat}
           {x y : C}
           (f : x -->h y)
  : square (identity_v x) (identity_v y) f (f ·h identity_h y)
  := globular_iso_square_inv (runitor_globular_iso_square f).

Proposition runitor_rinvunitor_h
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : runitor_h f ⋆v rinvunitor_h f
    =
    transportb_square (id_v_left _) (id_v_left _) (id_v_square _).
Proof.
  apply globular_iso_square_left.
Defined.

Proposition rinvunitor_runitor_h
            {C : double_cat}
            {x y : C}
            (f : x -->h y)
  : rinvunitor_h f ⋆v runitor_h f
    =
    transportb_square (id_v_left _) (id_v_left _) (id_v_square _).
Proof.
  apply globular_iso_square_right.
Defined.

Proposition runitor_square
            {C : double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h₁ : x₁ -->h y₁}
            {h₂ : x₂ -->h y₂}
            (s : square v₁ v₂ h₁ h₂)
  : (s ⋆h id_h_square _) ⋆v runitor_h h₂
    =
    transportb_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (runitor_h h₁ ⋆v s).
Proof.
  exact (!(double_runitor_nat (double_cat_double_runitor C) s)).
Defined.

(** ** 2.8. Associator *)
Definition double_cat_double_associator
           (C : double_cat)
  : double_cat_associator (hor_comp_double_cat C)
  := pr1 (pr222 (pr222 C)).

Definition lassociator_h
           {C : double_cat}
           {w x y z : C}
           (f : w -->h x)
           (g : x -->h y)
           (h : y -->h z)
  : square (identity_v w) (identity_v z) (f ·h (g ·h h)) ((f ·h g) ·h h)
  := double_associator (double_cat_double_associator C) f g h.

Definition associator_globular_iso_square
           {C : double_cat}
           {w x y z : C}
           (f : w -->h x)
           (g : x -->h y)
           (h : y -->h z)
  : globular_iso_square (f ·h (g ·h h)) ((f ·h g) ·h h)
  := pr11 (pr222 (pr222 C)) w x y z f g h.

Definition rassociator_h
           {C : double_cat}
           {w x y z : C}
           (f : w -->h x)
           (g : x -->h y)
           (h : y -->h z)
  : square (identity_v w) (identity_v z) ((f ·h g) ·h h) (f ·h (g ·h h))
  := globular_iso_square_inv (associator_globular_iso_square f g h).

Proposition lassociator_rassociator_h
            {C : double_cat}
            {w x y z : C}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : lassociator_h f g h ⋆v rassociator_h f g h
    =
    transportb_square (id_v_left _) (id_v_left _) (id_v_square _).
Proof.
  apply globular_iso_square_left.
Defined.

Proposition rassociator_lassociator_h
            {C : double_cat}
            {w x y z : C}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : rassociator_h f g h ⋆v lassociator_h f g h
    =
    transportb_square (id_v_left _) (id_v_left _) (id_v_square _).
Proof.
  apply globular_iso_square_right.
Defined.

Proposition lassociator_square
            {C : double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {vw : w₁ -->v w₂} {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂} {vz : z₁ -->v z₂}
            {h₁ : w₁ -->h x₁} {h₂ : w₂ -->h x₂}
            {j₁ : x₁ -->h y₁} {j₂ : x₂ -->h y₂}
            {k₁ : y₁ -->h z₁} {k₂ : y₂ -->h z₂}
            (s₁ : square vw vx h₁ h₂)
            (s₂ : square vx vy j₁ j₂)
            (s₃ : square vy vz k₁ k₂)
  : (s₁ ⋆h (s₂ ⋆h s₃)) ⋆v lassociator_h h₂ j₂ k₂
    =
    transportb_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (lassociator_h h₁ j₁ k₁ ⋆v ((s₁ ⋆h s₂) ⋆h s₃)).
Proof.
  exact (!(double_associator_nat (double_cat_double_associator C) s₁ s₂ s₃)).
Defined.

Proposition lassociator_square'
            {C : double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {vw : w₁ -->v w₂} {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂} {vz : z₁ -->v z₂}
            {h₁ : w₁ -->h x₁} {h₂ : w₂ -->h x₂}
            {j₁ : x₁ -->h y₁} {j₂ : x₂ -->h y₂}
            {k₁ : y₁ -->h z₁} {k₂ : y₂ -->h z₂}
            (s₁ : square vw vx h₁ h₂)
            (s₂ : square vx vy j₁ j₂)
            (s₃ : square vy vz k₁ k₂)
  : transportf_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      ((s₁ ⋆h (s₂ ⋆h s₃)) ⋆v lassociator_h h₂ j₂ k₂)
    =
    lassociator_h h₁ j₁ k₁ ⋆v ((s₁ ⋆h s₂) ⋆h s₃).
Proof.
  rewrite lassociator_square.
  rewrite transportfb_square.
  apply idpath.
Qed.

(** ** 2.9. Triangle and pentagon equations *)
Proposition double_triangle
            {C : double_cat}
            {x y z : C}
            (h : x -->h y)
            (k : y -->h z)
  : lassociator_h h _ k ⋆v (runitor_h h ⋆h id_v_square _)
    =
    transportb_square
      (id_v_left _)
      (id_v_left _)
      (id_v_square h ⋆h lunitor_h k).
Proof.
  exact (pr12 (pr222 (pr222 C)) x y z h k).
Qed.

Proposition double_triangle'
            {C : double_cat}
            {x y z : C}
            (h : x -->h y)
            (k : y -->h z)
  : transportf_square
      (id_v_left _)
      (id_v_left _)
      (lassociator_h h _ k ⋆v (runitor_h h ⋆h id_v_square _))
    =
    id_v_square h ⋆h lunitor_h k.
Proof.
  rewrite double_triangle.
  rewrite transportfb_square.
  apply idpath.
Qed.

Proposition double_pentagon
            {C : double_cat}
            {v w x y z : C}
            (h₁ : v -->h w)
            (h₂ : w -->h x)
            (h₃ : x -->h y)
            (h₄ : y -->h z)
  : transportb_square
      (id_right _)
      (id_right _)
      (lassociator_h h₁ h₂ (h₃ ·h h₄) ⋆v lassociator_h (h₁ ·h h₂) h₃ h₄)
    =
    (id_v_square h₁ ⋆h lassociator_h h₂ h₃ h₄)
    ⋆v lassociator_h h₁ (h₂ ·h h₃) h₄
    ⋆v (lassociator_h h₁ h₂ h₃ ⋆h id_v_square h₄).
Proof.
  exact (pr22 (pr222 (pr222 C)) v w x y z h₁ h₂ h₃ h₄).
Qed.

Proposition double_pentagon'
            {C : double_cat}
            {v w x y z : C}
            (h₁ : v -->h w)
            (h₂ : w -->h x)
            (h₃ : x -->h y)
            (h₄ : y -->h z)
  : lassociator_h h₁ h₂ (h₃ ·h h₄) ⋆v lassociator_h (h₁ ·h h₂) h₃ h₄
    =
    transportf_square
      (id_right _)
      (id_right _)
      ((id_v_square h₁ ⋆h lassociator_h h₂ h₃ h₄)
       ⋆v lassociator_h h₁ (h₂ ·h h₃) h₄
       ⋆v (lassociator_h h₁ h₂ h₃ ⋆h id_v_square h₄)).
Proof.
  rewrite <- double_pentagon.
  rewrite transportfb_square.
  apply idpath.
Qed.

(** * 3. Builder for double categories *)
Definition make_double_cat
           (C : category)
           (D : twosided_disp_cat C C)
           (I : hor_id D)
           (Cm : hor_comp D)
           (l : double_cat_lunitor I Cm)
           (r : double_cat_runitor I Cm)
           (a : double_cat_associator Cm)
           (tr : triangle_law l r a)
           (pe : pentagon_law a)
  : double_cat
  := C ,, D ,, I ,, Cm ,, l ,, r ,, a ,, tr ,, pe.

(** * 4. Squares and equalities *)
Definition ver_eq_to_square
           {C : double_cat}
           {x y : C}
           {v₁ v₂ : x -->v y}
           (p : v₁ = v₂)
  : square v₁ v₂ (identity_h x) (identity_h y).
Proof.
  induction p.
  apply id_h_square.
Defined.

Definition ver_weq_square
           (C : double_cat)
  : UU
  := ∏ (x y : C)
       (v₁ v₂ : x -->v y),
     isweq (@ver_eq_to_square C x y v₁ v₂).

Definition isaprop_square_ver_weq_square
           {C : double_cat}
           (H : ver_weq_square C)
           {x y : C}
           (v₁ v₂ : x -->v y)
  : isaprop (square v₁ v₂ (identity_h x) (identity_h y)).
Proof.
  use (isofhlevelweqf 1 (make_weq _ (H x y v₁ v₂))).
  apply homset_property.
Qed.
