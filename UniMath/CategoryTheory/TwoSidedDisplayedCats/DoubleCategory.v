Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.

Local Open Scope cat.

Definition double_cat_mor
  : UU
  := ∑ (C : category),
     twosided_disp_cat C C.

Coercion double_cat_to_cat
         (C : double_cat_mor)
  : category
  := pr1 C.

Definition double_cat_ver_mor
           {C : double_cat_mor}
           (x y : C)
  : UU
  := pr2 C x y.

Notation "x -->v y" := (double_cat_ver_mor x y) (at level 55).

(*
 The squares in a double category looks as follows

         h₁        id
     w ------> x -------> x
     |         |          |
  v₁ |         | v₂       | v₂
     |         |          |
     V         V          V
     y ------> z -------> z
         h₂        id

 We reuse the infrastructure of two-sided displayed categories to deal with squares
 *)
Definition double_cat_square
           {C : double_cat_mor}
           {w x y z : C}
           (h₁ : w -->v x)
           (h₂ : y -->v z)
           (v₁ : w --> y)
           (v₂ : x --> z)
  : UU
  := h₁ -->[ v₁ ][ v₂ ] h₂.


Section DoubleCategoryIdComp.
  Context (C : double_cat_mor).

  Definition double_cat_id_type
    : UU
    := ∏ (x : C), x -->v x.

  Definition double_cat_comp_type
    : UU
    := ∏ (x y z : C), x -->v y → y -->v z → x -->v z.

  Definition double_cat_id_comp_type
    : UU
    := double_cat_id_type × double_cat_comp_type.
End DoubleCategoryIdComp.

Definition double_cat_id_comp
  : UU
  := ∑ (C : double_cat_mor), double_cat_id_comp_type C.

Coercion double_cat_id_comp_to_cat_mor
         (C : double_cat_id_comp)
  : double_cat_mor
  := pr1 C.

Section DoubleCatIdCompAccessors.
  Context (C : double_cat_id_comp).

  Definition double_id
             (x : C)
    : x -->v x
    := pr12 C x.

  Definition double_comp
             {x y z : C}
             (f : x -->v y)
             (g : y -->v z)
    : x -->v z
    := pr22 C x y z f g.
End DoubleCatIdCompAccessors.

Arguments double_id {C} x.
Notation "f ·v g" := (double_comp _ f g) (at level 60) : cat.

Section UnitorsAndAssociators.
  Context (C : double_cat_id_comp).

  Definition double_lunitor_type
    : UU
    := ∏ (x y : C)
         (f : x -->v y),
       (double_id x ·v f)
       -->[ identity x ][ identity y ]
       f.

  Definition double_linvunitor_type
    : UU
    := ∏ (x y : C)
         (f : x -->v y),
       f
       -->[ identity x ][ identity y ]
       (double_id x ·v f).

  Definition double_runitor_type
    : UU
    := ∏ (x y : C)
         (f : x -->v y),
       (f  ·v double_id y)
       -->[ identity x ][ identity y ]
       f.

  Definition double_rinvunitor_type
    : UU
    := ∏ (x y : C)
         (f : x -->v y),
       f
       -->[ identity x ][ identity y ]
       (f ·v double_id y).

  Definition double_lassociator_type
    : UU
    := ∏ (w x y z : C)
         (f : w -->v x)
         (g : x -->v y)
         (h : y -->v z),
       ((f ·v g) ·v h)
       -->[ identity w ][ identity z ]
       (f ·v (g ·v h)).

  Definition double_rassociator_type
    : UU
    := ∏ (w x y z : C)
         (f : w -->v x)
         (g : x -->v y)
         (h : y -->v z),
       (f ·v (g ·v h))
       -->[ identity w ][ identity z ]
       ((f ·v g) ·v h).

  Definition double_cat_id_mor_type
    : UU
    := ∏ (x y : C)
         (f : x --> y),
       double_id x -->[ f ][ f ] double_id y.

  Definition double_cat_square_comp_type
    : UU
    := ∏ (x₁ x₂ y₁ y₂ z₁ z₂ : C)
         (h₁ : x₁ -->v y₁)
         (h₂ : x₂ -->v y₂)
         (k₁ : y₁ -->v z₁)
         (k₂ : y₂ -->v z₂)
         (vx : x₁ --> x₂)
         (vy : y₁ --> y₂)
         (vz : z₁ --> z₂)
         (τ₁ : h₁ -->[ vx ][ vy ] h₂)
         (τ₂ : k₁ -->[ vy ][ vz ] k₂),
       (h₁ ·v k₁) -->[ vx ][ vz ] (h₂ ·v k₂).

  Definition double_unitors_and_associators
    : UU
    := double_lunitor_type
       ×
       double_linvunitor_type
       ×
       double_runitor_type
       ×
       double_rinvunitor_type
       ×
       double_lassociator_type
       ×
       double_rassociator_type
       ×
       double_cat_id_mor_type
       ×
       double_cat_square_comp_type.
End UnitorsAndAssociators.

Definition double_cat_data
  : UU
  := ∑ (C : double_cat_id_comp), double_unitors_and_associators C.

Coercion double_cat_data_to_id_comp
         (C : double_cat_data)
  : double_cat_id_comp
  := pr1 C.

Section DoubleCatDataAccessors.
  Context {C : double_cat_data}.

  Definition double_lunitor
             {x y : C}
             (f : x -->v y)
    : (double_id x ·v f)
      -->[ identity x ][ identity y ]
      f
    := pr12 C x y f.

  Definition double_linvunitor
             {x y : C}
             (f : x -->v y)
    : f
      -->[ identity x ][ identity y ]
      (double_id x ·v f)
    := pr122 C x y f.

  Definition double_runitor
             {x y : C}
             (f : x -->v y)
    : (f ·v double_id y)
      -->[ identity x ][ identity y ]
      f
    := pr1 (pr222 C) x y f.

  Definition double_rinvunitor
             {x y : C}
             (f : x -->v y)
    : f
      -->[ identity x ][ identity y ]
      (f ·v double_id y)
    := pr12 (pr222 C) x y f.

  Definition double_lassociator
             {w x y z : C}
             (f : w -->v x)
             (g : x -->v y)
             (h : y -->v z)
    : ((f ·v g) ·v h)
      -->[ identity w ][ identity z ]
      (f ·v (g ·v h))
    := pr122 (pr222 C) w x y z f g h.

  Definition double_rassociator
             {w x y z : C}
             (f : w -->v x)
             (g : x -->v y)
             (h : y -->v z)
    : (f ·v (g ·v h))
      -->[ identity w ][ identity z ]
      ((f ·v g) ·v h)
    := pr1 (pr222 (pr222 C)) w x y z f g h.

  Definition double_cat_id_mor
             {x y : C}
             (f : x --> y)
    : double_id x -->[ f ][ f ] double_id y
    := pr12 (pr222 (pr222 C)) x y f.

  Definition double_cat_square_comp
             {x₁ x₂ y₁ y₂ z₁ z₂ : C}
             {h₁ : x₁ -->v y₁}
             {h₂ : x₂ -->v y₂}
             {k₁ : y₁ -->v z₁}
             {k₂ : y₂ -->v z₂}
             {vx : x₁ --> x₂}
             {vy : y₁ --> y₂}
             {vz : z₁ --> z₂}
             (τ₁ : h₁ -->[ vx ][ vy ] h₂)
             (τ₂ : k₁ -->[ vy ][ vz ] k₂)
    : (h₁ ·v k₁) -->[ vx ][ vz ] (h₂ ·v k₂)
    := pr22 (pr222 (pr222 C)) x₁ x₂ y₁ y₂ z₁ z₂ h₁ h₂ k₁ k₂ vx vy vz τ₁ τ₂.
End DoubleCatDataAccessors.

Notation "τ₁ ⋆h τ₂" := (double_cat_square_comp τ₁ τ₂) (at level 50).

Section DoubleCatLaws.
  Context (C : double_cat_data).

  Definition double_lunitor_linvunitor_type
    : UU
    := ∏ (x y : C)
         (f : x -->v y),
       transportf
         (λ z, _ -->[ z ][ _ ] _)
         (id_right _)
         (transportf
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _)
            (double_lunitor f ;;2 double_linvunitor f))
       =
       id_two_disp _.

  Definition double_linvunitor_lunitor_type
    : UU
    := ∏ (x y : C)
         (f : x -->v y),
       transportf
         (λ z, _ -->[ z ][ _ ] _)
         (id_right _)
         (transportf
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _)
            (double_linvunitor f ;;2 double_lunitor f))
       =
       id_two_disp _.

  Definition double_runitor_rinvunitor_type
    : UU
    := ∏ (x y : C)
         (f : x -->v y),
       transportf
         (λ z, _ -->[ z ][ _ ] _)
         (id_right _)
         (transportf
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _)
            (double_runitor f ;;2 double_rinvunitor f))
       =
       id_two_disp _.

  Definition double_rinvunitor_runitor_type
    : UU
    := ∏ (x y : C)
         (f : x -->v y),
       transportf
         (λ z, _ -->[ z ][ _ ] _)
         (id_right _)
         (transportf
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _)
            (double_rinvunitor f ;;2 double_runitor f))
       =
       id_two_disp _.

  Definition double_lassociator_rassociator_type
    : UU
    := ∏ (w x y z : C)
         (f : w -->v x)
         (g : x -->v y)
         (h : y -->v z),
       transportf
         (λ z, _ -->[ z ][ _ ] _)
         (id_right _)
         (transportf
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _)
            (double_lassociator f g h ;;2 double_rassociator f g h))
       =
       id_two_disp _.

  Definition double_rassociator_lassociator_type
    : UU
    := ∏ (w x y z : C)
         (f : w -->v x)
         (g : x -->v y)
         (h : y -->v z),
       transportf
         (λ z, _ -->[ z ][ _ ] _)
         (id_right _)
         (transportf
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _)
            (double_rassociator f g h ;;2 double_lassociator f g h))
       =
       id_two_disp _.

  Definition double_cat_lunitor_nat_type
    : UU
    := ∏ (x₁ x₂ y₁ y₂ : C)
         (h₁ : x₁ -->v y₁)
         (h₂ : x₂ -->v y₂)
         (v₁ : x₁ --> x₂)
         (v₂ : y₁ --> y₂)
         (τ : h₁ -->[ v₁ ][ v₂ ] h₂),
       transportb
         (λ z, _ -->[ z ][ _ ] _)
         (id_right _ @ !(id_left _))
         (transportb
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _ @ !(id_left _))
            (double_lunitor h₁ ;;2 τ))
       =
       (double_cat_id_mor _ ⋆h τ) ;;2 double_lunitor h₂.

  Definition double_cat_runitor_nat_type
    : UU
    := ∏ (x₁ x₂ y₁ y₂ : C)
         (h₁ : x₁ -->v y₁)
         (h₂ : x₂ -->v y₂)
         (v₁ : x₁ --> x₂)
         (v₂ : y₁ --> y₂)
         (τ : h₁ -->[ v₁ ][ v₂ ] h₂),
       transportb
         (λ z, _ -->[ z ][ _ ] _)
         (id_right _ @ !(id_left _))
         (transportb
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _ @ !(id_left _))
            (double_runitor h₁ ;;2 τ))
       =
       (τ ⋆h double_cat_id_mor _) ;;2 double_runitor h₂.

  Definition double_cat_lassociator_nat_type
    : UU
    := ∏ (w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C)
         (f₁ : w₁ -->v x₁)
         (g₁ : x₁ -->v y₁)
         (h₁ : y₁ -->v z₁)
         (f₂ : w₂ -->v x₂)
         (g₂ : x₂ -->v y₂)
         (h₂ : y₂ -->v z₂)
         (vw : w₁ --> w₂)
         (vx : x₁ --> x₂)
         (vy : y₁ --> y₂)
         (vz : z₁ --> z₂)
         (τf : f₁ -->[ vw ][ vx ] f₂)
         (τg : g₁ -->[ vx ][ vy ] g₂)
         (τh : h₁ -->[ vy ][ vz ] h₂),
       transportb
         (λ z, _ -->[ z ][ _ ] _)
         (id_right _ @ !(id_left _))
         (transportb
            (λ z, _ -->[ _ ][ z ] _)
            (id_right _ @ !(id_left _))
            (double_lassociator f₁ g₁ h₁ ;;2 (τf ⋆h (τg ⋆h τh))))
       =
       ((τf ⋆h τg) ⋆h τh) ;;2 double_lassociator f₂ g₂ h₂.

  Definition double_cat_interchange_type
    : UU
    := ∏ (x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C)
         (fx : x₁ --> x₂)
         (gx : x₂ --> x₃)
         (fy : y₁ --> y₂)
         (gy : y₂ --> y₃)
         (fz : z₁ --> z₂)
         (gz : z₂ --> z₃)
         (h₁ : x₁ -->v y₁)
         (h₂ : x₂ -->v y₂)
         (h₃ : x₃ -->v y₃)
         (k₁ : y₁ -->v z₁)
         (k₂ : y₂ -->v z₂)
         (k₃ : y₃ -->v z₃)
         (α : h₁ -->[ fx ][ fy ] h₂)
         (β : h₂ -->[ gx ][ gy ] h₃)
         (γ : k₁ -->[ fy ][ fz ] k₂)
         (δ : k₂ -->[ gy ][ gz ] k₃),
       (α ;;2 β) ⋆h (γ ;;2 δ)
       =
       α ⋆h γ ;;2 (β ⋆h δ).

  Definition double_cat_triangle_type
    : UU
    := ∏ (x y z : C)
         (f : x -->v y)
         (g : y -->v z),
       transportf
         (λ z, _ -->[ z ][ _ ] _)
         (id_left _)
         (transportf
            (λ z, _ -->[ _ ][ z ] _)
            (id_left _)
            (double_lassociator _ _ _ ;;2 (id_two_disp f ⋆h double_lunitor g)))
       =
       double_runitor f ⋆h id_two_disp g.

  Definition double_cat_pentagon_type
    : UU
    := ∏ (v w x y z : C)
         (f : v -->v w)
         (g : w -->v x)
         (h : x -->v y)
         (k : y -->v z),
       transportb
         (λ z, _ -->[ z ][ _ ] _)
         (maponpaths (λ z, z · _) (id_left _))
         (transportb
            (λ z, _ -->[ _ ][ z ] _)
            (maponpaths (λ z, z · _) (id_left _))
            (double_lassociator (f ·v g) h k ;;2 double_lassociator f g (h ·v k)))
       =
       (double_lassociator f g h ⋆h id_two_disp k)
       ;;2 double_lassociator f (g ·v h) k
       ;;2 (id_two_disp f ⋆h double_lassociator g h k).

  Definition double_law_laws
    : UU
    := double_lunitor_linvunitor_type
       ×
       double_linvunitor_lunitor_type
       ×
       double_runitor_rinvunitor_type
       ×
       double_rinvunitor_runitor_type
       ×
       double_lassociator_rassociator_type
       ×
       double_rassociator_lassociator_type
       ×
       double_cat_lunitor_nat_type
       ×
       double_cat_runitor_nat_type
       ×
       double_cat_lassociator_nat_type
       ×
       double_cat_interchange_type
       ×
       double_cat_triangle_type
       ×
       double_cat_pentagon_type.
End DoubleCatLaws.

Definition double_cat
  : UU
  := ∑ (C : double_cat_data), double_law_laws C.

Coercion double_cat_to_double_cat_data
         (C : double_cat)
  : double_cat_data
  := pr1 C.

Section DoubleCatLawsAccessors.
  Context {C : double_cat}.

  Proposition double_lunitor_linvunitor
              {x y : C}
              (f : x -->v y)
    : transportf
        (λ z, _ -->[ z ][ _ ] _)
        (id_right _)
        (transportf
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _)
           (double_lunitor f ;;2 double_linvunitor f))
      =
      id_two_disp _.
  Proof.
    exact (pr12 C x y f).
  Qed.

  Definition double_linvunitor_lunitor
             {x y : C}
             (f : x -->v y)
    : transportf
        (λ z, _ -->[ z ][ _ ] _)
        (id_right _)
        (transportf
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _)
           (double_linvunitor f ;;2 double_lunitor f))
      =
      id_two_disp _.
  Proof.
    exact (pr122 C x y f).
  Qed.

  Proposition double_runitor_rinvunitor
              {x y : C}
              (f : x -->v y)
    : transportf
        (λ z, _ -->[ z ][ _ ] _)
        (id_right _)
        (transportf
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _)
           (double_runitor f ;;2 double_rinvunitor f))
      =
        id_two_disp _.
  Proof.
    exact (pr1 (pr222 C) x y f).
  Qed.

  Proposition double_rinvunitor_runitor
              {x y : C}
              (f : x -->v y)
    : transportf
        (λ z, _ -->[ z ][ _ ] _)
        (id_right _)
        (transportf
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _)
           (double_rinvunitor f ;;2 double_runitor f))
      =
      id_two_disp _.
  Proof.
    exact (pr12 (pr222 C) x y f).
  Qed.

  Proposition double_lassociator_rassociator
              {w x y z : C}
              (f : w -->v x)
              (g : x -->v y)
              (h : y -->v z)
    : transportf
        (λ z, _ -->[ z ][ _ ] _)
        (id_right _)
        (transportf
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _)
           (double_lassociator f g h ;;2 double_rassociator f g h))
      =
      id_two_disp _.
  Proof.
    exact (pr122 (pr222 C) w x y z f g h).
  Qed.

  Proposition double_rassociator_lassociator
              {w x y z : C}
              (f : w -->v x)
              (g : x -->v y)
              (h : y -->v z)
    : transportf
        (λ z, _ -->[ z ][ _ ] _)
        (id_right _)
        (transportf
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _)
           (double_rassociator f g h ;;2 double_lassociator f g h))
      =
      id_two_disp _.
  Proof.
    exact (pr1 (pr222 (pr222 C)) w x y z f g h).
  Qed.

  Proposition double_cat_lunitor_nat
              {x₁ x₂ y₁ y₂ : C}
              {h₁ : x₁ -->v y₁}
              {h₂ : x₂ -->v y₂}
              {v₁ : x₁ --> x₂}
              {v₂ : y₁ --> y₂}
              (τ : h₁ -->[ v₁ ][ v₂ ] h₂)
    : transportb
        (λ z, _ -->[ z ][ _ ] _)
        (id_right _ @ !(id_left _))
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _ @ !(id_left _))
           (double_lunitor h₁ ;;2 τ))
      =
      (double_cat_id_mor _ ⋆h τ) ;;2 double_lunitor h₂.
  Proof.
    exact (pr12 (pr222 (pr222 C)) x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ τ).
  Qed.

  Proposition double_cat_runitor_nat
              {x₁ x₂ y₁ y₂ : C}
              {h₁ : x₁ -->v y₁}
              {h₂ : x₂ -->v y₂}
              {v₁ : x₁ --> x₂}
              {v₂ : y₁ --> y₂}
              (τ : h₁ -->[ v₁ ][ v₂ ] h₂)
    : transportb
        (λ z, _ -->[ z ][ _ ] _)
        (id_right _ @ !(id_left _))
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _ @ !(id_left _))
           (double_runitor h₁ ;;2 τ))
      =
      (τ ⋆h double_cat_id_mor _) ;;2 double_runitor h₂.
  Proof.
    exact (pr122 (pr222 (pr222 C)) x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ τ).
  Qed.

  Proposition double_cat_lassociator_nat
              {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
              {f₁ : w₁ -->v x₁}
              {g₁ : x₁ -->v y₁}
              {h₁ : y₁ -->v z₁}
              {f₂ : w₂ -->v x₂}
              {g₂ : x₂ -->v y₂}
              {h₂ : y₂ -->v z₂}
              {vw : w₁ --> w₂}
              {vx : x₁ --> x₂}
              {vy : y₁ --> y₂}
              {vz : z₁ --> z₂}
              (τf : f₁ -->[ vw ][ vx ] f₂)
              (τg : g₁ -->[ vx ][ vy ] g₂)
              (τh : h₁ -->[ vy ][ vz ] h₂)
    : transportb
        (λ z, _ -->[ z ][ _ ] _)
        (id_right _ @ !(id_left _))
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (id_right _ @ !(id_left _))
           (double_lassociator f₁ g₁ h₁ ;;2 (τf ⋆h (τg ⋆h τh))))
      =
      ((τf ⋆h τg) ⋆h τh) ;;2 double_lassociator f₂ g₂ h₂.
  Proof.
    exact (pr1 (pr222 (pr222 (pr222 C))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ τf τg τh).
  Qed.

  Proposition double_cat_interchange
              {x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C}
              {fx : x₁ --> x₂}
              {gx : x₂ --> x₃}
              {fy : y₁ --> y₂}
              {gy : y₂ --> y₃}
              {fz : z₁ --> z₂}
              {gz : z₂ --> z₃}
              {h₁ : x₁ -->v y₁}
              {h₂ : x₂ -->v y₂}
              {h₃ : x₃ -->v y₃}
              {k₁ : y₁ -->v z₁}
              {k₂ : y₂ -->v z₂}
              {k₃ : y₃ -->v z₃}
              (α : h₁ -->[ fx ][ fy ] h₂)
              (β : h₂ -->[ gx ][ gy ] h₃)
              (γ : k₁ -->[ fy ][ fz ] k₂)
              (δ : k₂ -->[ gy ][ gz ] k₃)
    : (α ;;2 β) ⋆h (γ ;;2 δ)
      =
      α ⋆h γ ;;2 (β ⋆h δ).
  Proof.
    exact (pr12 (pr222 (pr222 (pr222 C))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ α β γ δ).
  Qed.

  Proposition double_cat_triangle
              {x y z : C}
              (f : x -->v y)
              (g : y -->v z)
    : transportf
        (λ z, _ -->[ z ][ _ ] _)
        (id_left _)
        (transportf
           (λ z, _ -->[ _ ][ z ] _)
           (id_left _)
           (double_lassociator _ _ _ ;;2 (id_two_disp f ⋆h double_lunitor g)))
      =
      double_runitor f ⋆h id_two_disp g.
  Proof.
    exact (pr122 (pr222 (pr222 (pr222 C))) x y z f g).
  Qed.

  Proposition double_cat_pentagon
              {v w x y z : C}
              (f : v -->v w)
              (g : w -->v x)
              (h : x -->v y)
              (k : y -->v z)
    : transportb
        (λ z, _ -->[ z ][ _ ] _)
        (maponpaths (λ z, z · _) (id_left _))
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (maponpaths (λ z, z · _) (id_left _))
           (double_lassociator (f ·v g) h k ;;2 double_lassociator f g (h ·v k)))
      =
      (double_lassociator f g h ⋆h id_two_disp k)
      ;;2 double_lassociator f (g ·v h) k
      ;;2 (id_two_disp f ⋆h double_lassociator g h k).
  Proof.
    exact (pr222 (pr222 (pr222 (pr222 C))) v w x y z f g h k).
  Qed.
End DoubleCatLawsAccessors.
