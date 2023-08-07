Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.

Local Open Scope cat.

(**
 1. Horizontal identities
 *)
Definition hor_id_data
           {C : category}
           (D : twosided_disp_cat C C)
  : UU
  := ∑ (Im : ∏ (x : C), D x x),
     ∏ (x y : C)
       (f : x --> y),
     Im x -->[ f ][ f ] Im y.

Definition double_id
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id_data D)
           (x : C)
  : D x x
  := pr1 I x.

Definition double_id_mor
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id_data D)
           {x y : C}
           (f : x --> y)
  : double_id I x -->[ f ][ f ] double_id I y
  := pr2 I x y f.

Definition hor_id_laws
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id_data D)
  : UU
  := (∏ (x : C), double_id_mor I (identity x) = id_two_disp _)
     ×
     (∏ (x y z : C)
        (f : x --> y)
        (g : y --> z),
      double_id_mor I (f · g)
      =
      double_id_mor I f ;;2 double_id_mor I g).

Definition hor_id
           {C : category}
           (D : twosided_disp_cat C C)
  : UU
  := ∑ (I : hor_id_data D), hor_id_laws I.

Coercion hor_id_to_data
         {C : category}
         {D : twosided_disp_cat C C}
         (I : hor_id D)
  : hor_id_data D
  := pr1 I.

Proposition double_id_mor_id
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (x : C)
  : double_id_mor I (identity x) = id_two_disp _.
Proof.
  exact (pr12 I x).
Defined.

Definition double_id_mor_id_comp
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           {x y z : C}
           (f : x --> y)
           (g : y --> z)
  : double_id_mor I (f · g) = double_id_mor I f ;;2 double_id_mor I g.
Proof.
  exact (pr22 I x y z f g).
Defined.

(**
 2. Horizontal composition
 *)
Definition hor_comp_data
           {C : category}
           (D : twosided_disp_cat C C)
  : UU
  := ∑ (Cm : ∏ (x y z : C), D x y → D y z → D x z),
     ∏ (x₁ x₂ y₁ y₂ z₁ z₂ : C)
       (v₁ : x₁ --> x₂)
       (v₂ : y₁ --> y₂)
       (v₃ : z₁ --> z₂)
       (h₁ : D x₁ y₁)
       (h₂ : D y₁ z₁)
       (k₁ : D x₂ y₂)
       (k₂ : D y₂ z₂)
       (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
       (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂),
     Cm _ _ _ h₁ h₂ -->[ v₁ ][ v₃ ] Cm _ _ _ k₁ k₂.

Definition double_hor_comp
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp_data D)
           {x y z : C}
           (h₁ : D x y)
           (h₂ : D y z)
  : D x z
  := pr1 Cm x y z h₁ h₂.

Definition double_hor_comp_mor
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp_data D)
           {x₁ x₂ y₁ y₂ z₁ z₂ : C}
           {v₁ : x₁ --> x₂}
           {v₂ : y₁ --> y₂}
           {v₃ : z₁ --> z₂}
           {h₁ : D x₁ y₁}
           {h₂ : D y₁ z₁}
           {k₁ : D x₂ y₂}
           {k₂ : D y₂ z₂}
           (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
           (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
  : double_hor_comp Cm h₁ h₂ -->[ v₁ ][ v₃ ] double_hor_comp Cm k₁ k₂
  := pr2 Cm x₁ x₂ y₁ y₂ z₁ z₂ v₁ v₂ v₃ h₁ h₂ k₁ k₂ s₁ s₂.

Definition hor_comp_laws
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp_data D)
  : UU
  := (∏ (x y z : C)
        (h₁ : D x y)
        (h₂ : D y z),
      double_hor_comp_mor Cm (id_two_disp h₁) (id_two_disp h₂)
      =
      id_two_disp (double_hor_comp Cm h₁ h₂))
     ×
     (∏ (x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C)
        (v₁ : x₁ --> x₂) (v₁' : x₂ --> x₃)
        (v₂ : y₁ --> y₂) (v₂' : y₂ --> y₃)
        (v₃ : z₁ --> z₂) (v₃' : z₂ --> z₃)
        (h₁ : D x₁ y₁)
        (h₂ : D y₁ z₁)
        (k₁ : D x₂ y₂)
        (k₂ : D y₂ z₂)
        (l₁ : D x₃ y₃)
        (l₂ : D y₃ z₃)
        (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
        (s₁' : k₁ -->[ v₁' ][ v₂' ] l₁)
        (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
        (s₂' : k₂ -->[ v₂' ][ v₃' ] l₂),
      double_hor_comp_mor Cm (s₁ ;;2 s₁') (s₂ ;;2 s₂')
      =
      double_hor_comp_mor Cm s₁ s₂ ;;2 double_hor_comp_mor Cm s₁' s₂').

Definition hor_comp
           {C : category}
           (D : twosided_disp_cat C C)
  : UU
  := ∑ (Cm : hor_comp_data D), hor_comp_laws Cm.

Coercion hor_comp_to_data
         {C : category}
         {D : twosided_disp_cat C C}
         (Cm : hor_comp D)
  : hor_comp_data D
  := pr1 Cm.

Proposition double_hor_comp_mor_id
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x y z : C}
            (h₁ : D x y)
            (h₂ : D y z)
  : double_hor_comp_mor Cm (id_two_disp h₁) (id_two_disp h₂)
    =
    id_two_disp (double_hor_comp Cm h₁ h₂).
Proof.
  exact (pr12 Cm x y z h₁ h₂).
Defined.

Proposition double_hor_comp_mor_comp
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C}
            {v₁ : x₁ --> x₂} {v₁' : x₂ --> x₃}
            {v₂ : y₁ --> y₂} {v₂' : y₂ --> y₃}
            {v₃ : z₁ --> z₂} {v₃' : z₂ --> z₃}
            {h₁ : D x₁ y₁}
            {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            {l₁ : D x₃ y₃}
            {l₂ : D y₃ z₃}
            (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
            (s₁' : k₁ -->[ v₁' ][ v₂' ] l₁)
            (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
            (s₂' : k₂ -->[ v₂' ][ v₃' ] l₂)
  : double_hor_comp_mor Cm (s₁ ;;2 s₁') (s₂ ;;2 s₂')
    =
    double_hor_comp_mor Cm s₁ s₂ ;;2 double_hor_comp_mor Cm s₁' s₂'.
Proof.
  exact ((pr22 Cm)
           x₁ x₂ x₃
           y₁ y₂ y₃
           z₁ z₂ z₃
           v₁ v₁'
           v₂ v₂'
           v₃ v₃'
           h₁ h₂
           k₁ k₂
           l₁ l₂
           s₁ s₁' s₂ s₂').
Defined.

Proposition double_hor_comp_mor_transportf_left_left
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ v₁' : x₁ --> x₂}
            (p : v₁ = v₁')
            {v₂ : y₁ --> y₂}
            {v₃ : z₁ --> z₂}
            {h₁ : D x₁ y₁}
            {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
            (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
  : double_hor_comp_mor
      Cm
      (transportf (λ z, _ -->[ z ][ _ ] _) p s₁)
      s₂
    =
    transportf
      (λ z, _ -->[ z ][ _ ] _)
      p
      (double_hor_comp_mor Cm s₁ s₂).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition double_hor_comp_mor_transportf_right_right
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : x₁ --> x₂}
            {v₂ : y₁ --> y₂}
            {v₃ v₃' : z₁ --> z₂}
            (p : v₃ = v₃')
            {h₁ : D x₁ y₁}
            {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
            (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
  : double_hor_comp_mor
      Cm
      s₁
      (transportf (λ z, _ -->[ _ ][ z ] _) p s₂)
    =
    transportf
      (λ z, _ -->[ _ ][ z ] _)
      p
      (double_hor_comp_mor Cm s₁ s₂).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

(**
 3. Left unitor
 *)
Definition double_lunitor_data
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := ∏ (x y : C)
       (h : D x y),
    iso_twosided_disp
      (identity_z_iso x)
      (identity_z_iso y)
      (double_hor_comp Cm (double_id I x) h)
      h.

Proposition isaset_double_lunitor_data
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (Cm : hor_comp D)
  : isaset (double_lunitor_data I Cm).
Proof.
  use impred_isaset ; intro x.
  use impred_isaset ; intro y.
  use impred_isaset ; intro h.
  apply isaset_iso_twosided_disp.
Qed.

Definition double_lunitor_laws
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (l : double_lunitor_data I Cm)
  : UU
  := ∏ (x₁ x₂ y₁ y₂ : C)
       (h₁ : D x₁ y₁)
       (h₂ : D x₂ y₂)
       (v₁ : x₁ --> x₂)
       (v₂ : y₁ --> y₂)
       (τ : h₁ -->[ v₁ ][ v₂ ] h₂),
     transportb
       (λ z, _ -->[ z ][ _ ] _)
       (id_right _ @ !(id_left _))
       (transportb
          (λ z, _ -->[ _ ][ z ] _)
          (id_right _ @ !(id_left _))
          (l _ _ h₁ ;;2 τ))
     =
     double_hor_comp_mor Cm (double_id_mor I _) τ ;;2 l _ _ h₂.

Proposition isaprop_double_lunitor_laws
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (l : double_lunitor_data I Cm)
  : isaprop (double_lunitor_laws l).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition double_cat_lunitor
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := ∑ (l : double_lunitor_data I Cm), double_lunitor_laws l.

Proposition isaset_double_cat_lunitor
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (Cm : hor_comp D)
  : isaset (double_cat_lunitor I Cm).
Proof.
  use isaset_total2.
  - apply isaset_double_lunitor_data.
  - intro.
    apply isasetaprop.
    apply isaprop_double_lunitor_laws.
Qed.

Definition make_double_lunitor
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (l : double_lunitor_data I Cm)
           (Hl : double_lunitor_laws l)
  : double_cat_lunitor I Cm
  := l ,, Hl.

Definition double_lunitor
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (l : double_cat_lunitor I Cm)
           {x y : C}
           (h : D x y)
  : double_hor_comp Cm (double_id I x) h
    -->[ identity x ][ identity y ]
    h
  := pr1 l x y h.

Proposition double_lunitor_nat
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (l : double_cat_lunitor I Cm)
            {x₁ x₂ y₁ y₂ : C}
            {h₁ : D x₁ y₁}
            {h₂ : D x₂ y₂}
            {v₁ : x₁ --> x₂}
            {v₂ : y₁ --> y₂}
            (τ : h₁ -->[ v₁ ][ v₂ ] h₂)
  : transportb
      (λ z, _ -->[ z ][ _ ] _)
      (id_right _ @ !(id_left _))
      (transportb
         (λ z, _ -->[ _ ][ z ] _)
         (id_right _ @ !(id_left _))
         (double_lunitor l h₁ ;;2 τ))
    =
    double_hor_comp_mor Cm (double_id_mor I _) τ ;;2 double_lunitor l h₂.
Proof.
  exact (pr2 l x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ τ).
Defined.
