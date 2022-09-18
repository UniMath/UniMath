(*******************************************************************************

 Sections of displayed bicategories

 Contents:
 1. Definition of a section
 2. Builder for locally propositional/groupoidal displayed bicategories
 3. Every section gives a pseudofunctor from the base to the total bicategory

 *******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Local Open Scope cat.

(**
 1. Definition of a section
 *)
Definition section_disp_bicat_data
           {B : bicat}
           (D : disp_bicat B)
  : UU
  := ∑ (s_ob : ∏ (x : B), D x)
       (s_mor : ∏ (x y : B) (f : x --> y), s_ob x -->[ f ] s_ob y),
     (∏ (x y : B)
        (f g : x --> y)
        (τ : f ==> g),
      s_mor _ _ f ==>[ τ ] s_mor _ _ g)
     ×
     (∏ (x : B),
      disp_invertible_2cell
        (id2_invertible_2cell _)
        (id_disp _)
        (s_mor _ _ (id₁ x)))
     ×
     (∏ (x y z : B)
        (f : x --> y)
        (g : y --> z),
      disp_invertible_2cell
        (id2_invertible_2cell _)
        (s_mor _ _ f ;; s_mor _ _ g)
        (s_mor _ _ (f · g))).

Section SectionDataProjections.
  Context {B : bicat}
          {D : disp_bicat B}
          (s : section_disp_bicat_data D).

  Definition section_on_ob
             (x : B)
    : D x
    := pr1 s x.

  Definition section_on_mor
             {x y : B}
             (f : x --> y)
    : section_on_ob x -->[ f ] section_on_ob y
    := pr12 s _ _ f.

  Definition section_on_cell
             {x y : B}
             {f g : x --> y}
             (τ : f ==> g)
    : section_on_mor f ==>[ τ ] section_on_mor g
    := pr122 s _ _ _ _ τ.

  Definition section_on_id
             (x : B)
    : disp_invertible_2cell
        (id2_invertible_2cell _)
        (id_disp _)
        (section_on_mor (id₁ x))
    := pr1 (pr222 s) x.

  Definition section_on_comp
             {x y z : B}
             (f : x --> y)
             (g : y --> z)
    : disp_invertible_2cell
        (id2_invertible_2cell _)
        (section_on_mor f ;; section_on_mor g)
        (section_on_mor (f · g))
    := pr2 (pr222 s) _ _ _ f g.
End SectionDataProjections.

Definition section_disp_bicat_laws_id
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat_data D)
  : UU
  := ∏ (x y : B) (f : x --> y),
     section_on_cell s (id₂ f) = disp_id2 (section_on_mor s f).

Definition section_disp_bicat_laws_comp
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat_data D)
  : UU
  := ∏ (x y : B) (f g h : x --> y) (τ : f ==> g) (θ : g ==> h),
     section_on_cell s (τ • θ)
     =
     section_on_cell s τ •• section_on_cell s θ.

Definition section_disp_bicat_laws_lunitor_base
           {B : bicat}
           {x y : B}
           (f : x --> y)
  : lunitor f
    =
    ((id₂ _ ▹ f) • id₂ _) • lunitor f.
Proof.
  rewrite id2_rwhisker.
  rewrite !id2_left.
  apply idpath.
Qed.

Definition section_disp_bicat_laws_lunitor
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat_data D)
  : UU
  := ∏ (x y : B)
       (f : x --> y),
     transportf
       (λ z, _ ==>[ z ] _)
       (section_disp_bicat_laws_lunitor_base f)
       (disp_lunitor (section_on_mor s f))
     =
     ((pr1 (section_on_id s _) ▹▹ section_on_mor s f)
     •• pr1 (section_on_comp s (id₁ _) f))
     •• section_on_cell s (lunitor f).

Definition section_disp_bicat_laws_runitor_base
           {B : bicat}
           {x y : B}
           (f : x --> y)
  : runitor f
    =
    ((f ◃ id₂ _) • id₂ _) • runitor f.
Proof.
  rewrite lwhisker_id2.
  rewrite !id2_left.
  apply idpath.
Qed.

Definition section_disp_bicat_laws_runitor
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat_data D)
  : UU
  := ∏ (x y : B)
       (f : x --> y),
     transportf
       (λ z, _ ==>[ z ] _)
       (section_disp_bicat_laws_runitor_base f)
       (disp_runitor (section_on_mor s f))
     =
     ((section_on_mor s f ◃◃ pr1 (section_on_id s _))
     •• pr1 (section_on_comp s f (id₁ _)))
     •• section_on_cell s (runitor f).

Definition section_disp_bicat_laws_lassociator_base
           {B : bicat}             
           {w x y z : B}
           (f : w --> x)
           (g : x --> y)
           (h : y --> z)
  : ((f ◃ id₂ _) • id₂ _) • lassociator f g h
    =
    (lassociator f g h • (id₂ _ ▹ h)) • id₂ _.
Proof.
  rewrite id2_rwhisker, lwhisker_id2.
  rewrite !id2_left, !id2_right.
  apply idpath.
Qed.

Definition section_disp_bicat_laws_lassociator
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat_data D)
  := ∏ (w x y z : B)
       (f : w --> x)
       (g : x --> y)
       (h : y --> z),
     transportf
       (λ z, _ ==>[ z ] _)
       (section_disp_bicat_laws_lassociator_base f g h)
       (((section_on_mor s f ◃◃ pr1 (section_on_comp s g h))
        •• pr1 (section_on_comp s f (g · h)))
        •• section_on_cell s (lassociator f g h))
     =
     (disp_lassociator (section_on_mor s f) (section_on_mor s g) (section_on_mor s h)
     •• (pr1 (section_on_comp s f g) ▹▹ section_on_mor s h))
     •• pr1 (section_on_comp s (f · g) h).

Definition section_disp_bicat_laws_lwhisker_base
           {B : bicat}
           {x y z : B}
           (f : x --> y)
           {g₁ g₂ : y --> z}
           (η : g₁ ==> g₂)
  : id₂ _ • (f ◃ η) = (f ◃ η) • id₂ _.
Proof.
  rewrite id2_left, id2_right.
  apply idpath.
Qed.

Definition section_disp_bicat_laws_lwhisker
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat_data D)
  : UU
  := ∏ (x y z : B)
       (f : x --> y)
       (g₁ g₂ : y --> z)
       (η : g₁ ==> g₂),
    transportf
       (λ z, _ ==>[ z ] _)
       (section_disp_bicat_laws_lwhisker_base f η)
       (pr1 (section_on_comp s f g₁) •• section_on_cell s (f ◃ η))
     =
     (section_on_mor s f ◃◃ section_on_cell s η) •• pr1 (section_on_comp s f g₂).

Definition section_disp_bicat_laws_rwhisker_base
           {B : bicat}
           {x y z : B}
           {f₁ f₂ : x --> y}
           (g : y --> z)
           (η : f₁ ==> f₂)
  : id₂ _ • (η ▹ g) = (η ▹ g) • id₂ _.
Proof.
  rewrite id2_left, id2_right.
  apply idpath.
Qed.

Definition section_disp_bicat_laws_rwhisker
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat_data D)
  : UU
  := ∏ (x y z : B)
       (f₁ f₂ : x --> y)
       (g : y --> z)
       (η : f₁ ==> f₂),
     transportf
       (λ z, _ ==>[ z ] _)
       (section_disp_bicat_laws_rwhisker_base g η)
       (pr1 (section_on_comp s f₁ g) •• section_on_cell s (η ▹ g))
     =
     (section_on_cell s η ▹▹ section_on_mor s g) •• pr1 (section_on_comp s f₂ g).

Definition section_disp_bicat_laws
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat_data D)
  : UU
  := section_disp_bicat_laws_id s
     ×
     section_disp_bicat_laws_comp s
     ×
     section_disp_bicat_laws_lunitor s
     ×
     section_disp_bicat_laws_runitor s
     ×
     section_disp_bicat_laws_lassociator s
     ×
     section_disp_bicat_laws_lwhisker s
     ×
     section_disp_bicat_laws_rwhisker s.

Definition section_disp_bicat
           {B : bicat}
           (D : disp_bicat B)
  : UU
  := ∑ (s : section_disp_bicat_data D), section_disp_bicat_laws s.

Coercion section_to_section_data
          {B : bicat}
          {D : disp_bicat B}
          (s : section_disp_bicat D)
: section_disp_bicat_data D
  := pr1 s.

Definition section_disp_bicat_id
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat D)
  : section_disp_bicat_laws_id s
  := pr12 s.

Definition section_disp_bicat_comp
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat D)
  : section_disp_bicat_laws_comp s
  := pr122 s.

Definition section_disp_bicat_lunitor
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat D)
  : section_disp_bicat_laws_lunitor s
  := pr1 (pr222 s).

Definition section_disp_bicat_runitor
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat D)
  : section_disp_bicat_laws_runitor s
  := pr12 (pr222 s).

Definition section_disp_bicat_lassociator
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat D)
  : section_disp_bicat_laws_lassociator s
  := pr122 (pr222 s).

Definition section_disp_bicat_lwhisker
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat D)
  : section_disp_bicat_laws_lwhisker s
  := pr1 (pr222 (pr222 s)).

Definition section_disp_bicat_rwhisker
           {B : bicat}
           {D : disp_bicat B}
           (s : section_disp_bicat D)
  : section_disp_bicat_laws_rwhisker s
  := pr2 (pr222 (pr222 s)).

(**
 2. Builder for locally propositional/groupoidal displayed bicategories
 *)
Section MakeSection.
  Context {B : bicat}
          (D : disp_bicat B)
          (HD₁ : disp_2cells_isaprop D)
          (HD₂ : disp_locally_groupoid D)
          (s_ob : ∏ (x : B), D x)
          (s_mor : ∏ (x y : B) (f : x --> y), s_ob x -->[ f ] s_ob y)
          (s_cell : ∏ (x y : B)
                      (f g : x --> y)
                      (τ : f ==> g),
                    s_mor _ _ f ==>[ τ ] s_mor _ _ g)
          (s_id : ∏ (x : B), id_disp _ ==>[ id2 _ ] s_mor _ _ (id₁ x))
          (s_comp : ∏ (x y z : B)
                      (f : x --> y)
                      (g : y --> z),
                    s_mor _ _ f ;; s_mor _ _ g
                    ==>[ id2 _ ]
                    s_mor _ _ (f · g)).

  Definition make_section_disp_bicat_data
    : section_disp_bicat_data D.
  Proof.
    simple refine (s_ob ,, s_mor ,, s_cell ,, _ ,, _).
    - intro x.
      refine (s_id x ,, _).
      apply HD₂.
    - intros x y z f g.
      refine (s_comp _ _ _ f g ,, _).
      apply HD₂.
  Defined.

  Definition make_section_disp_bicat_laws
    : section_disp_bicat_laws make_section_disp_bicat_data.
  Proof.
    repeat split ; intro ; intros ; apply HD₁.
  Qed.

  Definition make_section_disp_bicat
    : section_disp_bicat D.
  Proof.
    simple refine (_ ,, _).
    - exact make_section_disp_bicat_data.
    - exact make_section_disp_bicat_laws.
  Defined.
End MakeSection.

(**
 3. Every section gives a pseudofunctor from the base to the total bicategory
 *)
Section SectionToPsfunctor.
  Context {B : bicat}
          {D : disp_bicat B}
          (s : section_disp_bicat D).

  Definition section_to_psfunctor_data
    : psfunctor_data B (total_bicat D).
  Proof.
    use make_psfunctor_data.
    - exact (λ x, x ,, section_on_ob s x).
    - exact (λ x y f, f ,, section_on_mor s f).
    - exact (λ x y f g τ, τ ,, section_on_cell s τ).
    - exact (λ x, id2 _ ,, pr1 (section_on_id s x)).
    - exact (λ x y z f g, id2 _ ,, pr1 (section_on_comp s f g)).
  Defined.

  Definition section_to_psfunctor_laws
    : psfunctor_laws section_to_psfunctor_data.
  Proof.
    repeat split ; intro ; intros ; cbn.
    - apply maponpaths.
      apply (section_disp_bicat_id s).
    - apply maponpaths.
      apply (section_disp_bicat_comp s).
    - use total2_paths_f.
      + apply section_disp_bicat_laws_lunitor_base.
      + apply (section_disp_bicat_lunitor s).
    - use total2_paths_f.
      + apply section_disp_bicat_laws_runitor_base.
      + apply (section_disp_bicat_runitor s).
    - use total2_paths_f.
      + apply section_disp_bicat_laws_lassociator_base.
      + apply (section_disp_bicat_lassociator s).
    - use total2_paths_f.
      + apply section_disp_bicat_laws_lwhisker_base.
      + apply (section_disp_bicat_lwhisker s).
    - use total2_paths_f.
      + apply section_disp_bicat_laws_rwhisker_base.
      + apply (section_disp_bicat_rwhisker s).
  Qed.

  Definition section_to_psfunctor_invertible_cells
    : invertible_cells section_to_psfunctor_data.
  Proof.
    split.
    - intro x ; cbn.
      use is_invertible_disp_to_total.
      simple refine (_ ,, _).
      + apply is_invertible_2cell_id₂.
      + exact (pr2 (section_on_id s x)).
    - intros x y z f g ; cbn.
      use is_invertible_disp_to_total.
      simple refine (_ ,, _).
      + apply is_invertible_2cell_id₂.
      + exact (pr2 (section_on_comp s f g)).
  Defined.
  
  Definition section_to_psfunctor
    : psfunctor B (total_bicat D).
  Proof.
    use make_psfunctor.
    - exact section_to_psfunctor_data.
    - exact section_to_psfunctor_laws.
    - exact section_to_psfunctor_invertible_cells.
  Defined.
End SectionToPsfunctor.
