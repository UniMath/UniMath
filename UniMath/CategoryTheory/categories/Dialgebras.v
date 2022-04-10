Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

Section Dialgebra.
  Context {C₁ C₂ : category}
          (F G : C₁ ⟶ C₂).

  Definition dialgebra_disp_cat_ob_mor : disp_cat_ob_mor C₁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, F x --> G x).
    - exact (λ x y hx hy f, hx · #G f = #F f · hy).
  Defined.

  Definition dialgebra_disp_cat_id_comp
    : disp_cat_id_comp C₁ dialgebra_disp_cat_ob_mor.
  Proof.
    split.
    - intros x hx ; cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x y z f g hx hy hz hf hg ; cbn in *.
      rewrite !functor_comp.
      rewrite !assoc.
      rewrite hf.
      rewrite !assoc'.
      rewrite hg.
      apply idpath.
  Qed.

  Definition dialgebra_disp_cat_data : disp_cat_data C₁.
  Proof.
    simple refine (_ ,, _).
    - exact dialgebra_disp_cat_ob_mor.
    - exact dialgebra_disp_cat_id_comp.
  Defined.

  Definition dialgebra_disp_cat_axioms
    : disp_cat_axioms C₁ dialgebra_disp_cat_data.
  Proof.
    repeat split ; intros ; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
  Qed.

  Definition dialgebra_disp_cat : disp_cat C₁.
  Proof.
    simple refine (_ ,, _).
    - exact dialgebra_disp_cat_data.
    - exact dialgebra_disp_cat_axioms.
  Defined.

  Definition is_iso_disp_dialgebra
             {x y : C₁}
             {f : x --> y}
             (Hf : is_iso f)
             {hx : dialgebra_disp_cat x}
             {hy : dialgebra_disp_cat y}
             (hf : hx -->[ f ] hy)
    : is_iso_disp (make_iso f Hf) hf.
  Proof.
    simple refine (_ ,, (_ ,, _)) ; cbn in *.
    - rewrite !functor_on_inv_from_iso.
      refine (!_).
      use iso_inv_on_left.
      refine (!_).
      rewrite !assoc'.
      use iso_inv_on_right.
      exact hf.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition is_univalent_dialgebra_disp_cat
    : is_univalent_disp dialgebra_disp_cat.
  Proof.
    intros x y e hx hy ; induction e.
    use isweqimplimpl.
    - intro i.
      refine (_ @ pr1 i @ _) ; cbn.
      + rewrite functor_id.
        rewrite id_right.
        apply idpath.
      + rewrite functor_id.
        apply id_left.
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition dialgebra : category
    := total_category dialgebra_disp_cat.

  Definition is_univalent_dialgebra
             (H₁ : is_univalent C₁)
    : is_univalent dialgebra.
  Proof.
    use is_univalent_total_category.
    - exact H₁.
    - apply is_univalent_dialgebra_disp_cat.
  Defined.
End Dialgebra.

Definition univalent_dialgebra
           {C₁ C₂ : univalent_category}
           (F G : C₁ ⟶ C₂)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (dialgebra F G).
  - apply is_univalent_dialgebra.
    exact (pr2 C₁).
Defined.

Definition eq_dialgebra
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : dialgebra F G}
           {f g : x --> y}
           (p : pr1 f = pr1 g)
  : f = g.
Proof.
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  exact p.
Qed.

Definition is_iso_dialgebra
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : dialgebra F G}
           (f : x --> y)
           (Hf : is_iso (pr1 f))
  : is_iso f.
Proof.
  use is_iso_total.
  - exact Hf.
  - apply is_iso_disp_dialgebra.
Defined.

Definition iso_dialgebra
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : dialgebra F G}
           (f : x --> y)
           (Hf : is_iso (pr1 f))
  : iso x y.
Proof.
  use make_iso.
  - exact f.
  - apply is_iso_dialgebra.
    exact Hf.
Defined.

Definition dialgebra_pr1
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : dialgebra F G ⟶ C₁
  := pr1_category _.

Definition dialgebra_nat_trans_data
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : nat_trans_data
      (dialgebra_pr1 F G ∙ F)
      (dialgebra_pr1 F G ∙ G)
  := λ x, pr2 x.

Definition dialgebra_nat_trans_is_nat_trans
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : is_nat_trans _ _ (dialgebra_nat_trans_data F G).
Proof.
  intros x y f.
  exact (!(pr2 f)).
Qed.

Definition dialgebra_nat_trans
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : dialgebra_pr1 F G ∙ F ⟹ dialgebra_pr1 F G ∙ G.
Proof.
  use make_nat_trans.
  - exact (dialgebra_nat_trans_data F G).
  - exact (dialgebra_nat_trans_is_nat_trans F G).
Defined.

Definition functor_to_dialgebra_data
           {C₁ C₂ C₃ : category}
           {F G : C₂ ⟶ C₃}
           (K : C₁ ⟶ C₂)
           (α : K ∙ F ⟹ K ∙ G)
  : functor_data C₁ (dialgebra F G).
Proof.
  use make_functor_data.
  - exact (λ x, K x ,, α x).
  - refine (λ x y f, #K f ,, _).
    abstract
      (cbn ;
       exact (!(nat_trans_ax α _ _ f))).
Defined.

Definition functor_to_dialgebra_is_functor
           {C₁ C₂ C₃ : category}
           {F G : C₂ ⟶ C₃}
           (K : C₁ ⟶ C₂)
           (α : K ∙ F ⟹ K ∙ G)
  : is_functor (functor_to_dialgebra_data K α).
Proof.
  split ; intro ; intros ; use eq_dialgebra.
  - apply functor_id.
  - apply functor_comp.
Qed.

Definition functor_to_dialgebra
           {C₁ C₂ C₃ : category}
           {F G : C₂ ⟶ C₃}
           (K : C₁ ⟶ C₂)
           (α : K ∙ F ⟹ K ∙ G)
  : C₁ ⟶ dialgebra F G.
Proof.
  use make_functor.
  - exact (functor_to_dialgebra_data K α).
  - exact (functor_to_dialgebra_is_functor K α).
Defined.

Definition functor_to_dialgebra_pr1
           {C₁ C₂ C₃ : category}
           {F G : C₂ ⟶ C₃}
           (K : C₁ ⟶ C₂)
           (α : K ∙ F ⟹ K ∙ G)
  : functor_to_dialgebra K α ∙ dialgebra_pr1 F G ⟹ K.
Proof.
  use make_nat_trans.
  - exact (λ _, identity _).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition functor_to_dialgebra_pr1_nat_iso
           {C₁ C₂ C₃ : category}
           {F G : C₂ ⟶ C₃}
           (K : C₁ ⟶ C₂)
           (α : K ∙ F ⟹ K ∙ G)
  : nat_iso
      (functor_to_dialgebra K α ∙ dialgebra_pr1 F G)
      K.
Proof.
  use make_nat_iso.
  - exact (functor_to_dialgebra_pr1 K α).
  - intro.
    apply identity_is_iso.
Defined.

Definition nat_trans_to_dialgebra
           {C₁ C₂ C₃ : category}
           {F G : C₂ ⟶ C₃}
           (K₁ K₂ : C₁ ⟶ dialgebra F G)
           (α : K₁ ∙ dialgebra_pr1 F G ⟹ K₂ ∙ dialgebra_pr1 F G)
           (p : ∏ (x : C₁), pr2 (K₁ x) · # G (α x) = # F (α x) · pr2 (K₂ x))
  : K₁ ⟹ K₂.
Proof.
  use make_nat_trans.
  - exact (λ x, α x ,, p x).
  - abstract
      (intros x₁ x₂ f ;
       use eq_dialgebra ;
       exact (nat_trans_ax α _ _ f)).
Defined.
