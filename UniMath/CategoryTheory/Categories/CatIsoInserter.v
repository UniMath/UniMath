Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.

Section CatIsoInserter.
  Context {C₁ C₂ : category}
          (F G : C₁ ⟶ C₂).

  Definition cat_iso_inserter_disp_cat_ob_mor : disp_cat_ob_mor C₁.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, z_iso (F x) (G x)).
    - exact (λ x y hx hy f, hx · #G f = #F f · hy).
  Defined.

  Definition cat_iso_inserter_disp_cat_id_comp
    : disp_cat_id_comp C₁ cat_iso_inserter_disp_cat_ob_mor.
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

  Definition cat_iso_inserter_disp_cat_data : disp_cat_data C₁.
  Proof.
    simple refine (_ ,, _).
    - exact cat_iso_inserter_disp_cat_ob_mor.
    - exact cat_iso_inserter_disp_cat_id_comp.
  Defined.

  Definition cat_iso_inserter_disp_cat_axioms
    : disp_cat_axioms C₁ cat_iso_inserter_disp_cat_data.
  Proof.
    repeat split ; intros ; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
  Qed.

  Definition cat_iso_inserter_disp_cat : disp_cat C₁.
  Proof.
    simple refine (_ ,, _).
    - exact cat_iso_inserter_disp_cat_data.
    - exact cat_iso_inserter_disp_cat_axioms.
  Defined.

  Definition is_z_iso_disp_cat_iso_inserter
             {x y : C₁}
             {f : x --> y}
             (Hf : is_z_isomorphism f)
             {hx : cat_iso_inserter_disp_cat x}
             {hy : cat_iso_inserter_disp_cat y}
             (hf : hx -->[ f ] hy)
    : is_z_iso_disp (make_z_iso' f Hf) hf.
  Proof.
    simple refine (_ ,, (_ ,, _)) ; cbn in *.
    - rewrite !functor_on_inv_from_z_iso.
      refine (!_).
      use z_iso_inv_on_left.
      refine (!_).
      rewrite !assoc'.
      use z_iso_inv_on_right.
      exact hf.
    - apply homset_property.
    - apply homset_property.
  Qed.

  Definition is_univalent_cat_iso_inserter_disp_cat
    : is_univalent_disp cat_iso_inserter_disp_cat.
  Proof.
    intros x y e hx hy ; induction e.
    use isweqimplimpl.
    - intro i.
      use z_iso_eq.
      refine (_ @ pr1 i @ _) ; cbn.
      + rewrite functor_id.
        rewrite id_right.
        apply idpath.
      + rewrite functor_id.
        apply id_left.
    - use isaset_z_iso.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition cat_iso_inserter : category
    := total_category cat_iso_inserter_disp_cat.

  Definition is_univalent_cat_iso_inserter
             (H₁ : is_univalent C₁)
    : is_univalent cat_iso_inserter.
  Proof.
    use is_univalent_total_category.
    - exact H₁.
    - apply is_univalent_cat_iso_inserter_disp_cat.
  Defined.

  Definition make_cat_iso_inserter
             (x : C₁)
             (f : z_iso (F x) (G x))
    : cat_iso_inserter
    := x ,, f.

  Definition cat_iso_inserter_mor_path
             {x y : cat_iso_inserter}
             (f : pr1 x --> pr1 y)
    : UU
    := pr12 x · # G f = # F f · pr12 y.

  Definition make_cat_iso_inserter_mor
             {x y : cat_iso_inserter}
             (f : pr1 x --> pr1 y)
             (p : cat_iso_inserter_mor_path f)
    : x --> y
    := f ,, p.

  Definition cat_iso_inserter_pr1 : cat_iso_inserter ⟶ C₁ := pr1_category _.
End CatIsoInserter.

Definition univalent_cat_iso_inserter
           {C₁ C₂ : univalent_category}
           (F G : C₁ ⟶ C₂)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (cat_iso_inserter F G).
  - apply is_univalent_cat_iso_inserter.
    exact (pr2 C₁).
Defined.

Definition eq_cat_iso_inserter
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : cat_iso_inserter F G}
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

Definition is_z_iso_cat_iso_inserter
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : cat_iso_inserter F G}
           (f : x --> y)
           (Hf : is_z_isomorphism (pr1 f))
  : is_z_isomorphism f.
Proof.
  use is_z_iso_total.
  - exact Hf.
  - apply is_z_iso_disp_cat_iso_inserter.
Defined.

Definition z_iso_cat_iso_inserter
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : cat_iso_inserter F G}
           (f : x --> y)
           (Hf : is_z_isomorphism (pr1 f))
  : z_iso x y.
Proof.
  use make_z_iso'.
  - exact f.
  - apply is_z_iso_cat_iso_inserter.
    exact Hf.
Defined.


Definition from_is_z_iso_cat_iso_inserter
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : cat_iso_inserter F G}
           (f : x --> y)
           (Hf : is_z_isomorphism f)
  : is_z_isomorphism (pr1 f)
  := pr2 (functor_on_z_iso (cat_iso_inserter_pr1 F G) (make_z_iso' _ Hf)).

Definition from_z_iso_cat_iso_inserter
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : cat_iso_inserter F G}
           (f : z_iso x y)
  : z_iso (pr1 x) (pr1 y)
  := functor_on_z_iso (cat_iso_inserter_pr1 F G) f.

Definition cat_iso_inserter_nat_trans_data
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : nat_trans_data
      (cat_iso_inserter_pr1 F G ∙ F)
      (cat_iso_inserter_pr1 F G ∙ G)
  := λ x, pr12 x.

Definition cat_iso_inserter_nat_trans_is_nat_trans
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : is_nat_trans _ _ (cat_iso_inserter_nat_trans_data F G).
Proof.
  intros x y f.
  exact (!(pr2 f)).
Qed.

Definition cat_iso_inserter_nat_trans
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : cat_iso_inserter_pr1 F G ∙ F ⟹ cat_iso_inserter_pr1 F G ∙ G.
Proof.
  use make_nat_trans.
  - exact (cat_iso_inserter_nat_trans_data F G).
  - exact (cat_iso_inserter_nat_trans_is_nat_trans F G).
Defined.

Definition cat_iso_inserter_nat_iso
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : nat_z_iso
      (cat_iso_inserter_pr1 F G ∙ F)
      (cat_iso_inserter_pr1 F G ∙ G).
Proof.
  use make_nat_z_iso.
  - exact (cat_iso_inserter_nat_trans F G).
  - intro x.
    apply z_iso_is_z_isomorphism.
Defined.

Section CatIsoInserterFunctor.
  Context {C₁ C₂ C₃ : category}
          {F G : C₂ ⟶ C₃}
          (H : C₁ ⟶ C₂)
          (α : nat_z_iso (H ∙ F) (H ∙ G)).

  Definition functor_to_cat_iso_inserter_data
    : functor_data C₁ (cat_iso_inserter F G).
  Proof.
    use make_functor_data.
    - exact (λ x, H x ,, nat_z_iso_pointwise_z_iso α x).
    - refine (λ x y f, # H f ,, _).
      abstract
        (cbn ;
         exact (!(nat_trans_ax α _ _ f))).
  Defined.

  Definition functor_to_cat_iso_inserter_is_functor
    : is_functor functor_to_cat_iso_inserter_data.
  Proof.
    split.
    - intros x.
      use eq_cat_iso_inserter ; cbn.
      apply functor_id.
    - intros x y z f g.
      use eq_cat_iso_inserter ; cbn.
      apply functor_comp.
  Qed.

  Definition functor_to_cat_iso_inserter
    : C₁ ⟶ cat_iso_inserter F G.
  Proof.
    use make_functor.
    - exact functor_to_cat_iso_inserter_data.
    - exact functor_to_cat_iso_inserter_is_functor.
  Defined.

  Definition functor_to_cat_iso_inserter_pr1
    : functor_to_cat_iso_inserter ∙ cat_iso_inserter_pr1 F G ⟹ H.
  Proof.
    use make_nat_trans.
    - exact (λ x, identity _).
    - abstract
        (intros x y f ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition functor_to_cat_iso_inserter_pr1_nat_z_iso
    : nat_z_iso
        (functor_to_cat_iso_inserter ∙ cat_iso_inserter_pr1 F G)
        H.
  Proof.
    use make_nat_z_iso.
    - exact functor_to_cat_iso_inserter_pr1.
    - intro x.
      apply is_z_isomorphism_identity.
  Defined.
End CatIsoInserterFunctor.

Definition nat_trans_to_cat_iso_inserter
           {C₁ C₂ C₃ : category}
           {F G : C₂ ⟶ C₃}
           {H₁ H₂ : C₁ ⟶ cat_iso_inserter F G}
           (α : H₁ ∙ cat_iso_inserter_pr1 F G ⟹ H₂ ∙ cat_iso_inserter_pr1 F G)
           (p : ∏ (x : C₁), pr12 (H₁ x) · # G (α x) = # F (α x) · pr12 (H₂ x))
  : H₁ ⟹ H₂.
Proof.
  use make_nat_trans.
  - exact (λ x, α x ,, p x).
  - abstract
      (intros x y f ;
       use eq_cat_iso_inserter ; cbn ;
       exact (nat_trans_ax α _ _ f)).
Defined.
