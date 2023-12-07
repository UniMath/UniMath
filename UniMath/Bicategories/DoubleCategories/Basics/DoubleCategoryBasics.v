(**********************************************************************************

 Basics of double categories

 In this file, we define the basic notions for double categories. There are a
 couple of ideas behind the definition that we use:
 - First of all, a double category is a category with extra structure. This extra
   structure includes another collection of morphisms, and we use 2-sided displayed
   categories to represent these.
 - Second of all, ultimately, we use these definitions to define the bicategory of
   double categories. This bicategory is defined by adding structure to the
   bicategory of 2-sided displayed categories using the machinery of displayed
   bicategories.

 We identify which structure to add to a 2-sided displayed category in order to
 obtain a double category.

 Contents
 1. Horizontal identities
 2. Horizontal composition
 3. Left unitor
 4. Right unitor
 5. Associator
 6. Triangle and pentagon laws

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.

Local Open Scope cat.

(** * 1. Horizontal identities *)
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

Proposition isaprop_hor_id_laws
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id_data D)
  : isaprop (hor_id_laws I).
Proof.
  use isapropdirprod ; (repeat (use impred ; intro)) ; apply isaset_disp_mor.
Qed.

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

Definition make_hor_id_data
           {C : category}
           (D : twosided_disp_cat C C)
           (I : ∏ (x : C), D x x)
           (sI : ∏ (x y : C) (f : x --> y), I x -->[ f ][ f] I y)
  : hor_id_data D
  := I ,, sI.

Definition make_hor_id
           {C : category}
           (D : twosided_disp_cat C C)
           (I : hor_id_data D)
           (HI : hor_id_laws I)
  : hor_id D
  := I ,, HI.

(** * 2. Horizontal composition *)
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

Proposition isaprop_hor_comp_laws
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp_data D)
  : isaprop (hor_comp_laws Cm).
Proof.
  use isapropdirprod ; (repeat (use impred ; intro)) ; apply isaset_disp_mor.
Qed.

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

Definition make_hor_comp_data
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : ∏ (x y z : C), D x y → D y z → D x z)
           (sC : ∏ (x₁ x₂ y₁ y₂ z₁ z₂ : C)
                   (v₁ : x₁ --> x₂)
                   (v₂ : y₁ --> y₂)
                   (v₃ : z₁ --> z₂)
                   (h₁ : D x₁ y₁)
                   (h₂ : D y₁ z₁)
                   (k₁ : D x₂ y₂)
                   (k₂ : D y₂ z₂)
                   (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
                   (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂),
                 Cm _ _ _ h₁ h₂ -->[ v₁ ][ v₃ ] Cm _ _ _ k₁ k₂)
  : hor_comp_data D
  := Cm ,, sC.

Definition make_hor_comp
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp_data D)
           (HC : hor_comp_laws Cm)
  : hor_comp D
  := Cm ,, HC.

Proposition double_hor_comp_mor_transportf_disp_mor2_left
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ v₁' : x₁ --> x₂}
            (p : v₁ = v₁')
            {v₂ v₂' : y₁ --> y₂}
            (q : v₂ = v₂')
            {v₃ v₃' : z₁ --> z₂}
            (r : v₃ = v₃')
            {h₁ : D x₁ y₁}
            {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
            (s₂ : h₂ -->[ v₂' ][ v₃ ] k₂)
  : double_hor_comp_mor
      Cm
      (transportf_disp_mor2 p q s₁)
      s₂
    =
    transportf_disp_mor2
      p
      (!r)
      (double_hor_comp_mor
         Cm
         s₁
         (transportf_disp_mor2 (!q) r s₂)).
Proof.
  induction p, q, r ; cbn.
  apply idpath.
Qed.

Proposition double_hor_comp_mor_transportf_disp_mor2_right_idpath
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : x₁ --> x₂}
            {v₂ v₂' : y₁ --> y₂}
            (q : v₂ = v₂')
            {v₃ v₃' : z₁ --> z₂}
            (r : v₃ = v₃')
            {h₁ : D x₁ y₁}
            {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            (s₁ : h₁ -->[ v₁ ][ v₂' ] k₁)
            (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
  : double_hor_comp_mor
      Cm
      s₁
      (transportf_disp_mor2 q r s₂)
    =
    transportf_disp_mor2
      (idpath _)
      r
      (double_hor_comp_mor
         Cm
         (transportf_disp_mor2 (idpath _) (!q) s₁)
         s₂).
Proof.
  induction q, r ; cbn.
  apply idpath.
Qed.

Proposition double_hor_comp_mor_transportf_disp_mor2_right
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ v₁' : x₁ --> x₂}
            (p : v₁' = v₁)
            {v₂ v₂' : y₁ --> y₂}
            (q : v₂ = v₂')
            {v₃ v₃' : z₁ --> z₂}
            (r : v₃ = v₃')
            {h₁ : D x₁ y₁}
            {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂}
            {k₂ : D y₂ z₂}
            (s₁ : h₁ -->[ v₁' ][ v₂' ] k₁)
            (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
  : double_hor_comp_mor
      Cm
      s₁
      (transportf_disp_mor2 q r s₂)
    =
    transportf_disp_mor2
      (!p)
      r
      (double_hor_comp_mor
         Cm
         (transportf_disp_mor2 p (!q) s₁)
         s₂).
Proof.
  induction p, q, r ; cbn.
  apply idpath.
Qed.

Proposition double_hor_comp_transport_mor
            {C : category}
            {D : twosided_disp_cat C C}
            {Cm : hor_comp D}
            {x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C}
            {v₁ : x₁ --> x₂} {v₁' : x₂ --> x₃}
            {v₂ : y₁ --> y₂} {v₂' : y₂ --> y₃} {v₂'' : y₂ --> y₃}
            {v₃ : z₁ --> z₂} {v₃' : z₂ --> z₃}
            {u₁ : x₁ --> x₃}
            {u₂ : y₁ --> y₃}
            {u₃ : z₁ --> z₃}
            {h₁ : D x₁ y₁} {h₂ : D y₁ z₁}
            {k₁ : D x₂ y₂} {k₂ : D y₂ z₂}
            {l₁ : D x₃ y₃} {l₂ : D y₃ z₃}
            (s₁ : h₁ -->[ v₁ ][ v₂ ] k₁)
            (s₁' : k₁ -->[ v₁' ][ v₂'] l₁)
            (s₂ : h₂ -->[ v₂ ][ v₃ ] k₂)
            (s₂' : k₂ -->[ v₂'' ][ v₃' ] l₂)
            (p : v₁ · v₁' = u₁)
            (q : v₂ · v₂' = u₂)
            (q' : v₂ · v₂'' = u₂)
            (s : v₂' = v₂'')
            (r : v₃ · v₃' = u₃)
  : double_hor_comp_mor
      Cm
      (transportf_disp_mor2
         p
         q
         (s₁ ;;2 s₁'))
      (transportf_disp_mor2
         q'
         r
         (s₂ ;;2 s₂'))
    =
    transportf_disp_mor2
      p
      r
      (double_hor_comp_mor Cm s₁ s₂
       ;;2
       double_hor_comp_mor Cm (transportf_disp_mor2 (idpath _) s s₁') s₂').
Proof.
  induction p, q, s, r.
  assert (q' = idpath _) as H.
  {
    apply homset_property.
  }
  rewrite H.
  cbn.
  rewrite double_hor_comp_mor_comp.
  apply idpath.
Qed.

(** * 3. Left unitor *)
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
     transportb_disp_mor2
       (id_right _ @ !(id_left _))
       (id_right _ @ !(id_left _))
       (l _ _ h₁ ;;2 τ)
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
  : transportb_disp_mor2
      (id_right _ @ !(id_left _))
      (id_right _ @ !(id_left _))
      (double_lunitor l h₁ ;;2 τ)
    =
    double_hor_comp_mor Cm (double_id_mor I _) τ ;;2 double_lunitor l h₂.
Proof.
  exact (pr2 l x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ τ).
Defined.

(** * 4. Right unitor *)
Definition double_runitor_data
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
      (double_hor_comp Cm h (double_id I y))
      h.

Proposition isaset_double_runitor_data
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (Cm : hor_comp D)
  : isaset (double_runitor_data I Cm).
Proof.
  use impred_isaset ; intro x.
  use impred_isaset ; intro y.
  use impred_isaset ; intro h.
  apply isaset_iso_twosided_disp.
Qed.

Definition double_runitor_laws
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (r : double_runitor_data I Cm)
  : UU
  := ∏ (x₁ x₂ y₁ y₂ : C)
       (h₁ : D x₁ y₁)
       (h₂ : D x₂ y₂)
       (v₁ : x₁ --> x₂)
       (v₂ : y₁ --> y₂)
       (τ : h₁ -->[ v₁ ][ v₂ ] h₂),
     transportb_disp_mor2
       (id_right _ @ !(id_left _))
       (id_right _ @ !(id_left _))
       (r _ _ h₁ ;;2 τ)
     =
     double_hor_comp_mor Cm τ (double_id_mor I _) ;;2 r _ _ h₂.

Proposition isaprop_double_runitor_laws
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (r : double_runitor_data I Cm)
  : isaprop (double_runitor_laws r).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition double_cat_runitor
           {C : category}
           {D : twosided_disp_cat C C}
           (I : hor_id D)
           (Cm : hor_comp D)
  : UU
  := ∑ (r : double_runitor_data I Cm), double_runitor_laws r.

Proposition isaset_double_cat_runitor
            {C : category}
            {D : twosided_disp_cat C C}
            (I : hor_id D)
            (Cm : hor_comp D)
  : isaset (double_cat_runitor I Cm).
Proof.
  use isaset_total2.
  - apply isaset_double_runitor_data.
  - intro.
    apply isasetaprop.
    apply isaprop_double_runitor_laws.
Qed.

Definition make_double_runitor
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (l : double_runitor_data I Cm)
           (Hl : double_runitor_laws l)
  : double_cat_runitor I Cm
  := l ,, Hl.

Definition double_runitor
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (r : double_cat_runitor I Cm)
           {x y : C}
           (h : D x y)
  : double_hor_comp Cm h (double_id I y)
    -->[ identity x ][ identity y ]
    h
  := pr1 r x y h.

Proposition double_runitor_nat
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (r : double_cat_runitor I Cm)
            {x₁ x₂ y₁ y₂ : C}
            {h₁ : D x₁ y₁}
            {h₂ : D x₂ y₂}
            {v₁ : x₁ --> x₂}
            {v₂ : y₁ --> y₂}
            (τ : h₁ -->[ v₁ ][ v₂ ] h₂)
  : transportb_disp_mor2
      (id_right _ @ !(id_left _))
      (id_right _ @ !(id_left _))
      (double_runitor r h₁ ;;2 τ)
    =
    double_hor_comp_mor Cm τ (double_id_mor I _) ;;2 double_runitor r h₂.
Proof.
  exact (pr2 r x₁ x₂ y₁ y₂ h₁ h₂ v₁ v₂ τ).
Defined.

(** * 5. Associator *)
Definition double_associator_data
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp D)
  : UU
  := ∏ (w x y z : C)
       (h₁ : D w x)
       (h₂ : D x y)
       (h₃ : D y z),
    iso_twosided_disp
      (identity_z_iso w)
      (identity_z_iso z)
      (double_hor_comp
         Cm
         h₁
         (double_hor_comp
            Cm
            h₂
            h₃))
      (double_hor_comp
         Cm
         (double_hor_comp
            Cm
            h₁
            h₂)
         h₃).

Proposition isaset_double_associator_data
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
  : isaset (double_associator_data Cm).
Proof.
  repeat (use impred_isaset ; intro).
  apply isaset_iso_twosided_disp.
Qed.

Definition double_associator_laws
           {C : category}
           {D : twosided_disp_cat C C}
           {Cm : hor_comp D}
           (a : double_associator_data Cm)
  : UU
  := ∏ (w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C)
       (h₁ : D w₁ x₁)
       (h₂ : D w₂ x₂)
       (j₁ : D x₁ y₁)
       (j₂ : D x₂ y₂)
       (k₁ : D y₁ z₁)
       (k₂ : D y₂ z₂)
       (vw : w₁ --> w₂)
       (vx : x₁ --> x₂)
       (vy : y₁ --> y₂)
       (vz : z₁ --> z₂)
       (τ₁ : h₁ -->[ vw ][ vx ] h₂)
       (τ₂ : j₁ -->[ vx ][ vy ] j₂)
       (τ₃ : k₁ -->[ vy ][ vz ] k₂),
     transportb_disp_mor2
       (id_right _ @ !(id_left _))
       (id_right _ @ !(id_left _))
       (a _ _ _ _ h₁ j₁ k₁ ;;2 double_hor_comp_mor Cm (double_hor_comp_mor Cm τ₁ τ₂) τ₃)
     =
     double_hor_comp_mor Cm τ₁ (double_hor_comp_mor Cm τ₂ τ₃) ;;2 a _ _ _ _ h₂ j₂ k₂.

Proposition isaprop_double_associator_laws
            {C : category}
            {D : twosided_disp_cat C C}
            {Cm : hor_comp D}
            (a : double_associator_data Cm)
  : isaprop (double_associator_laws a).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition double_cat_associator
           {C : category}
           {D : twosided_disp_cat C C}
           (Cm : hor_comp D)
  : UU
  := ∑ (a : double_associator_data Cm), double_associator_laws a.

Proposition isaset_double_cat_associator
            {C : category}
            {D : twosided_disp_cat C C}
            (Cm : hor_comp D)
  : isaset (double_cat_associator Cm).
Proof.
  use isaset_total2.
  - apply isaset_double_associator_data.
  - intro.
    apply isasetaprop.
    apply isaprop_double_associator_laws.
Qed.

Definition make_double_associator
           {C : category}
           {D : twosided_disp_cat C C}
           {Cm : hor_comp D}
           (a : double_associator_data Cm)
           (Ha : double_associator_laws a)
  : double_cat_associator Cm
  := a ,, Ha.

Definition double_associator
           {C : category}
           {D : twosided_disp_cat C C}
           {Cm : hor_comp D}
           (a : double_cat_associator Cm)
           {w x y z : C}
           (h₁ : D w x)
           (h₂ : D x y)
           (h₃ : D y z)
  : double_hor_comp
      Cm
      h₁
      (double_hor_comp
         Cm
         h₂
         h₃)
    -->[ identity w ][ identity z ]
    double_hor_comp
      Cm
      (double_hor_comp
         Cm
         h₁
         h₂)
      h₃
  := pr1 a w x y z h₁ h₂ h₃.

Proposition double_associator_nat
            {C : category}
            {D : twosided_disp_cat C C}
            {Cm : hor_comp D}
            (a : double_cat_associator Cm)
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {h₁ : D w₁ x₁}
            {h₂ : D w₂ x₂}
            {j₁ : D x₁ y₁}
            {j₂ : D x₂ y₂}
            {k₁ : D y₁ z₁}
            {k₂ : D y₂ z₂}
            {vw : w₁ --> w₂}
            {vx : x₁ --> x₂}
            {vy : y₁ --> y₂}
            {vz : z₁ --> z₂}
            (τ₁ : h₁ -->[ vw ][ vx ] h₂)
            (τ₂ : j₁ -->[ vx ][ vy ] j₂)
            (τ₃ : k₁ -->[ vy ][ vz ] k₂)
  : transportb_disp_mor2
      (id_right _ @ !(id_left _))
      (id_right _ @ !(id_left _))
      (double_associator a h₁ j₁ k₁
       ;;2
       double_hor_comp_mor Cm (double_hor_comp_mor Cm τ₁ τ₂) τ₃)
    =
    double_hor_comp_mor Cm τ₁ (double_hor_comp_mor Cm τ₂ τ₃)
    ;;2
    double_associator a h₂ j₂ k₂.
Proof.
  apply (pr2 a).
Defined.

(** * 6. Triangle and pentagon laws *)
Definition triangle_law
           {C : category}
           {D : twosided_disp_cat C C}
           {I : hor_id D}
           {Cm : hor_comp D}
           (l : double_cat_lunitor I Cm)
           (r : double_cat_runitor I Cm)
           (a : double_cat_associator Cm)
  : UU
  := ∏ (x y z : C)
       (h : D x y)
       (k : D y z),
     double_associator a h _ k
     ;;2
     double_hor_comp_mor Cm (double_runitor r h) (id_two_disp _)
     =
     transportb_disp_mor2
       (id_left _)
       (id_left _)
       (double_hor_comp_mor Cm (id_two_disp _) (double_lunitor l k)).

Proposition isaprop_triangle_law
            {C : category}
            {D : twosided_disp_cat C C}
            {I : hor_id D}
            {Cm : hor_comp D}
            (l : double_cat_lunitor I Cm)
            (r : double_cat_runitor I Cm)
            (a : double_cat_associator Cm)
  : isaprop (triangle_law l r a).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.

Definition pentagon_law
           {C : category}
           {D : twosided_disp_cat C C}
           {Cm : hor_comp D}
           (a : double_cat_associator Cm)
  : UU
  := ∏ (v w x y z : C)
       (h₁ : D v w)
       (h₂ : D w x)
       (h₃ : D x y)
       (h₄ : D y z),
     transportb_disp_mor2
       (id_right _)
       (id_right _)
       (double_associator a h₁ h₂ (double_hor_comp Cm h₃ h₄)
        ;;2
        double_associator a (double_hor_comp Cm h₁ h₂) h₃ h₄)
     =
     double_hor_comp_mor Cm (id_two_disp _) (double_associator a h₂ h₃ h₄)
     ;;2 double_associator a h₁ (double_hor_comp Cm h₂ h₃) h₄
     ;;2 double_hor_comp_mor Cm (double_associator a h₁ h₂ h₃) (id_two_disp _).

Proposition isaprop_pentagon_law
            {C : category}
            {D : twosided_disp_cat C C}
            {Cm : hor_comp D}
            (a : double_cat_associator Cm)
  : isaprop (pentagon_law a).
Proof.
  repeat (use impred ; intro).
  apply isaset_disp_mor.
Qed.
