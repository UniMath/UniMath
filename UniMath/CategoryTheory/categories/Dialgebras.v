Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.CompositesAndInverses.
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

  Definition is_z_iso_disp_dialgebra
             {x y : C₁}
             {f : x --> y}
             (Hf : is_z_isomorphism f)
             {hx : dialgebra_disp_cat x}
             {hy : dialgebra_disp_cat y}
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
        apply isaprop_is_z_iso_disp.
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

  Definition make_dialgebra
             (x : C₁)
             (f : F x --> G x)
    : dialgebra
    := x ,, f.

  Definition dialgebra_mor_path
             {x y : dialgebra}
             (f : pr1 x --> pr1 y)
    : UU
    := pr2 x · # G f = # F f · pr2 y.

  Definition make_dialgebra_mor
             {x y : dialgebra}
             (f : pr1 x --> pr1 y)
             (p : dialgebra_mor_path f)
    : x --> y
    := f ,, p.
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

Definition is_z_iso_dialgebra
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : dialgebra F G}
           (f : x --> y)
           (Hf : is_z_isomorphism (pr1 f))
  : is_z_isomorphism f.
Proof.
  use is_z_iso_total.
  - exact Hf.
  - apply is_z_iso_disp_dialgebra.
Defined.

Definition z_iso_dialgebra
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : dialgebra F G}
           (f : x --> y)
           (Hf : is_z_isomorphism (pr1 f))
  : z_iso x y.
Proof.
  use make_z_iso'.
  - exact f.
  - apply is_z_iso_dialgebra.
    exact Hf.
Defined.

Definition dialgebra_pr1
           {C₁ C₂ : category}
           (F G : C₁ ⟶ C₂)
  : dialgebra F G ⟶ C₁
  := pr1_category _.

Definition from_is_z_iso_dialgebra
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : dialgebra F G}
           (f : x --> y)
           (Hf : is_z_isomorphism f)
  : is_z_isomorphism (pr1 f)
  := pr2 (functor_on_z_iso (dialgebra_pr1 F G) (make_z_iso' _ Hf)).

Definition from_z_iso_dialgebra
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {x y : dialgebra F G}
           (f : z_iso x y)
  : z_iso (pr1 x) (pr1 y)
  := functor_on_z_iso (dialgebra_pr1 F G) f.

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

Definition functor_to_dialgebra_pr1_nat_z_iso
           {C₁ C₂ C₃ : category}
           {F G : C₂ ⟶ C₃}
           (K : C₁ ⟶ C₂)
           (α : K ∙ F ⟹ K ∙ G)
  : nat_z_iso
      (functor_to_dialgebra K α ∙ dialgebra_pr1 F G)
      K.
Proof.
  use make_nat_z_iso.
  - exact (functor_to_dialgebra_pr1 K α).
  - intro.
    apply identity_is_z_iso.
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

Section DialgebraEquivalence.
  Context {C₁ C₁' C₂ C₂' : category}
          {F G : C₁ ⟶ C₁'}
          {F' G' : C₂ ⟶ C₂'}
          {L : C₁ ⟶ C₂}
          (HL : adj_equivalence_of_cats L)
          {L' : C₁' ⟶ C₂'}
          (HL' : adj_equivalence_of_cats L')
          (α : nat_z_iso (L ∙ F') (F ∙ L'))
          (β : nat_z_iso (L ∙ G') (G ∙ L')).

  Let R : C₂ ⟶ C₁
    := right_adjoint HL.
  Let R' : C₂' ⟶ C₁'
    := right_adjoint HL'.
  Let η : nat_z_iso (functor_identity _) (L ∙ R)
    := unit_nat_z_iso_from_adj_equivalence_of_cats HL.
  Let η' : nat_z_iso (functor_identity _) (L' ∙ R')
    := unit_nat_z_iso_from_adj_equivalence_of_cats HL'.
  Let ε : nat_z_iso  (R ∙ L) (functor_identity _)
    := counit_nat_z_iso_from_adj_equivalence_of_cats HL.
  Let ε' : nat_z_iso (R' ∙ L') (functor_identity _)
    := counit_nat_z_iso_from_adj_equivalence_of_cats HL'.
  Let ηinv : nat_z_iso (L ∙ R) (functor_identity _)
    := nat_z_iso_inv η.
  Let ηinv' : nat_z_iso (L' ∙ R') (functor_identity _)
    := nat_z_iso_inv η'.
  Let εinv : nat_z_iso  (functor_identity _) (R ∙ L)
    := nat_z_iso_inv ε.
  Let εinv' : nat_z_iso (functor_identity _) (R' ∙ L')
    := nat_z_iso_inv ε'.
  Let αinv : nat_z_iso (F ∙ L') (L ∙ F')
    := nat_z_iso_inv α.
  Let βinv : nat_z_iso (G ∙ L') (L ∙ G')
    := nat_z_iso_inv β.

  Definition dialgebra_equivalence_nat_trans_data
    : nat_trans_data
        (dialgebra_pr1 F G ∙ L ∙ F')
        (dialgebra_pr1 F G ∙ L ∙ G')
    := λ x,
       α (pr1 x)
       · #L' (pr2 x)
       · βinv (pr1 x).

  Definition dialgebra_equivalence_is_nat_trans
    : is_nat_trans _ _ dialgebra_equivalence_nat_trans_data.
  Proof.
    intros x y f ; cbn.
    unfold dialgebra_equivalence_nat_trans_data.
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      apply (nat_trans_ax α).
    }
    rewrite !assoc'.
    apply maponpaths.
    cbn.
    rewrite !assoc.
    rewrite <- (functor_comp L').
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      exact (!(pr2 f)).
    }
    rewrite (functor_comp L').
    rewrite !assoc'.
    apply maponpaths.
    apply (nat_trans_ax βinv).
  Qed.

  Definition dialgebra_equivalence_nat_trans
    : dialgebra_pr1 F G ∙ L ∙ F'
      ⟹
      dialgebra_pr1 F G ∙ L ∙ G'.
  Proof.
    use make_nat_trans.
    - exact dialgebra_equivalence_nat_trans_data.
    - exact dialgebra_equivalence_is_nat_trans.
  Defined.

  Definition dialgebra_equivalence_of_cats_functor
    : dialgebra F G ⟶ dialgebra F' G'
    := functor_to_dialgebra
         (dialgebra_pr1 _ _ ∙ L)
         dialgebra_equivalence_nat_trans.

  Definition dialgebra_equivalence_of_cats_inv_nat_trans_data
    : nat_trans_data
        (dialgebra_pr1 F' G' ∙ R ∙ F)
        (dialgebra_pr1 F' G' ∙ R ∙ G)
    := λ x,
       η' (F (R (pr1 x)))
       · #R' (αinv _ · #F' (ε _) · pr2 x · #G' (εinv _) · β _)
       · ηinv' _.

  Definition dialgebra_equivalence_of_cats_inv_is_nat_trans
    : is_nat_trans
        _ _
        dialgebra_equivalence_of_cats_inv_nat_trans_data.
  Proof.
    intros x₁ x₂ f.
    cbn -[η] ; unfold dialgebra_equivalence_of_cats_inv_nat_trans_data.
    rewrite !functor_comp.
    rewrite !assoc.
    etrans.
    {
      do 6 apply maponpaths_2.
      apply (nat_trans_ax η').
    }
    rewrite !assoc'.
    apply maponpaths.
    cbn -[η αinv εinv ε ηinv'].
    rewrite !assoc.
    etrans.
    {
      do 5 apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      apply (nat_trans_ax αinv).
    }
    rewrite functor_comp.
    rewrite !assoc'.
    apply maponpaths.
    cbn -[η αinv εinv ε ηinv'].
    rewrite !assoc.
    etrans.
    {
      do 4 apply maponpaths_2.
      rewrite <- !functor_comp.
      do 2 apply maponpaths.
      apply (nat_trans_ax ε).
    }
    rewrite !functor_comp.
    rewrite !assoc'.
    apply maponpaths.
    cbn -[η αinv εinv ηinv'].
    rewrite !assoc.
    etrans.
    {
      do 3 apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      exact (!(pr2 f)).
    }
    rewrite !functor_comp.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      do 2 apply maponpaths_2.
      rewrite <- !functor_comp.
      do 2 apply maponpaths.
      apply (nat_trans_ax εinv).
    }
    rewrite !functor_comp.
    rewrite !assoc'.
    apply maponpaths.
    cbn -[η αinv εinv ηinv'].
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      rewrite <- functor_comp.
      apply maponpaths.
      apply (nat_trans_ax β).
    }
    rewrite functor_comp.
    rewrite !assoc'.
    apply maponpaths.
    apply (nat_trans_ax ηinv').
  Qed.

  Definition dialgebra_equivalence_of_cats_inv_nat_trans
    : dialgebra_pr1 F' G' ∙ R ∙ F
      ⟹
      dialgebra_pr1 F' G' ∙ R ∙ G.
  Proof.
    use make_nat_trans.
    - exact dialgebra_equivalence_of_cats_inv_nat_trans_data.
    - exact dialgebra_equivalence_of_cats_inv_is_nat_trans.
  Defined.

  Definition dialgebra_equivalence_of_cats_inv_functor
    : dialgebra F' G' ⟶ dialgebra F G
    := functor_to_dialgebra
         (dialgebra_pr1 _ _ ∙ R)
         dialgebra_equivalence_of_cats_inv_nat_trans.

  Definition dialgebra_equivalence_of_cats_unit_data_path
             (x : dialgebra F G)
    : @dialgebra_mor_path
        _ _ _ _ _
        ((dialgebra_equivalence_of_cats_functor
          ∙
          dialgebra_equivalence_of_cats_inv_functor)
          x)
        (η (pr1 x)).
  Proof.
    unfold dialgebra_mor_path.
    cbn -[η] ; unfold dialgebra_equivalence_of_cats_inv_nat_trans_data.
    unfold dialgebra_equivalence_nat_trans_data.
    cbn -[η ε η' ε' ηinv εinv ηinv' εinv' αinv βinv].
    rewrite !assoc'.
    refine (!_).
    assert (H₁ : εinv (L (pr1 x)) = #L (η (pr1 x))).
    {
      refine (!(id_left _) @ _).
      refine (!_).
      apply (z_iso_inv_on_left _ _ _ _ (_,,dirprod_pr2 (pr2 HL) (L (pr1 x)))).
      exact (!(triangle_id_left_ad (pr21 HL) (pr1 x))).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      do 5 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        exact H₁.
      }
      etrans.
      {
        apply maponpaths.
        apply (nat_trans_ax β).
      }
      cbn.
      rewrite !assoc.
      etrans.
      { apply cancel_postcomposition.
        apply (z_iso_after_z_iso_inv (_,,pr2 β (pr1 x))). }
      apply id_left.
    }
    clear H₁.
    assert (H₂ : ε (L (pr1 x)) = #L (ηinv (pr1 x))).
    {
      cbn -[ε].
      etrans.
      2: { apply pathsinv0, (functor_on_inv_from_z_iso L (_,,dirprod_pr1 (pr2 HL) (pr1 x))). }
      refine (_ @ id_right _).
      refine (!_).
      apply z_iso_inv_on_right.
      exact (!(triangle_id_left_ad (pr21 HL) (pr1 x))).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        exact H₂.
      }
      rewrite assoc'.
      etrans.
      {
        apply maponpaths.
        apply (nat_trans_ax α).
      }
      rewrite !assoc.
      cbn -[ηinv].
      etrans.
      { apply cancel_postcomposition.
        apply (z_iso_after_z_iso_inv (_,,pr2 α (R (L (pr1 x))))). }
      apply id_left.
    }
    rewrite !functor_comp.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 3 apply maponpaths_2.
      apply (!(nat_trans_ax η' _ _ _)).
    }
    cbn -[η ε η' ε' ηinv εinv ηinv' εinv'].
    rewrite !assoc.
    rewrite <- functor_comp.
    etrans.
    {
      do 3 apply maponpaths_2.
      cbn -[η η'].
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (z_iso_inv_after_z_iso (make_z_iso' _ _)).
      }
      rewrite functor_id.
      apply id_left.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax η').
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (nat_trans_ax η').
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      cbn -[η'].
      exact (z_iso_inv_after_z_iso (make_z_iso' _ _)).
    }
    apply id_right.
  Qed.

  Definition dialgebra_equivalence_of_cats_unit_data
    : nat_trans_data
        (functor_identity _)
        (dialgebra_equivalence_of_cats_functor
         ∙ dialgebra_equivalence_of_cats_inv_functor).
  Proof.
    simple refine (λ x, make_dialgebra_mor _ _ _ _).
    - exact (η (pr1 x)).
    - exact (dialgebra_equivalence_of_cats_unit_data_path x).
  Defined.

  Definition dialgebra_equivalence_of_cats_unit_is_nat_trans
    : is_nat_trans
        _ _
        dialgebra_equivalence_of_cats_unit_data.
  Proof.
    intros x₁ x₂ f.
    use eq_dialgebra ; cbn.
    apply (nat_trans_ax η).
  Qed.

  Definition dialgebra_equivalence_of_cats_unit
    : functor_identity _
      ⟹
      dialgebra_equivalence_of_cats_functor
      ∙ dialgebra_equivalence_of_cats_inv_functor.
  Proof.
    use make_nat_trans.
    - exact dialgebra_equivalence_of_cats_unit_data.
    - exact dialgebra_equivalence_of_cats_unit_is_nat_trans.
  Defined.

  Definition dialgebra_equivalence_of_cats_counit_path
             (x : dialgebra F' G')
    : @dialgebra_mor_path
        _ _ _ _
        ((dialgebra_equivalence_of_cats_inv_functor
          ∙ dialgebra_equivalence_of_cats_functor)
         x)
        _
        (ε (pr1 x)).
  Proof.
    unfold dialgebra_mor_path.
    cbn -[ε] ; unfold dialgebra_equivalence_of_cats_inv_nat_trans_data.
    unfold dialgebra_equivalence_nat_trans_data.
    cbn -[η ε η' ε' ηinv εinv ηinv' εinv' αinv βinv].
    rewrite !(functor_comp L').
    rewrite !assoc'.
    assert (# L' (ηinv' (G (R (pr1 x))))
            =
            ε' (L' (G (R (pr1 x)))))
      as H₁.
    {
      refine (!(id_right _) @ !_).
      unfold ηinv' ; cbn -[η' ε'].
      etrans.
      2: { apply cancel_postcomposition, pathsinv0, (functor_on_inv_from_z_iso L' (_,,pr2 η' (G (R (pr1 x))))). }
      refine (!_).
      use z_iso_inv_on_right.
      exact (!(triangle_id_left_ad (pr21 HL') (G (R (pr1 x))))).
    }
    etrans.
    {
      do 3 apply maponpaths.
      apply maponpaths_2.
      exact H₁.
    }
    clear H₁.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      do 2 apply maponpaths_2.
      apply (nat_trans_ax ε').
    }
    cbn -[η ε η' ε' ηinv εinv ηinv' εinv' αinv βinv].
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      do 7 apply maponpaths_2.
      exact (triangle_id_left_ad (pr21 HL') (F (R (pr1 x)))).
    }
    rewrite id_left.
    rewrite !assoc.
    etrans.
    {
      do 6 apply maponpaths_2.
      apply (z_iso_inv_after_z_iso (make_z_iso' _ _)).
    }
    rewrite id_left.
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ id_right _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      apply (z_iso_inv_after_z_iso (make_z_iso' _ _)).
    }
    rewrite id_left.
    rewrite <- functor_comp.
    etrans.
    {
      apply maponpaths.
      apply (z_iso_after_z_iso_inv (make_z_iso' _ _)).
    }
    apply functor_id.
  Qed.

  Definition dialgebra_equivalence_of_cats_counit_data
    : nat_trans_data
        (dialgebra_equivalence_of_cats_inv_functor
         ∙ dialgebra_equivalence_of_cats_functor)
        (functor_identity _).
  Proof.
    simple refine (λ x, make_dialgebra_mor _ _ _ _).
    - exact (ε (pr1 x)).
    - exact (dialgebra_equivalence_of_cats_counit_path x).
  Defined.

  Definition dialgebra_equivalence_of_cats_counit_is_nat_trans
    : is_nat_trans
        _ _
        dialgebra_equivalence_of_cats_counit_data.
  Proof.
    intros x₁ x₂ f.
    use eq_dialgebra ; cbn.
    apply (nat_trans_ax ε).
  Qed.

  Definition dialgebra_equivalence_of_cats_counit
    : dialgebra_equivalence_of_cats_inv_functor
      ∙ dialgebra_equivalence_of_cats_functor
      ⟹
      functor_identity _.
  Proof.
    use make_nat_trans.
    - exact dialgebra_equivalence_of_cats_counit_data.
    - exact dialgebra_equivalence_of_cats_counit_is_nat_trans.
  Defined.

  Definition dialgebra_equivalence_of_cats_unit_is_nat_z_iso
    : is_nat_z_iso dialgebra_equivalence_of_cats_unit.
  Proof.
    intro x.
    use is_z_iso_dialgebra.
    apply η.
  Defined.

  Definition dialgebra_equivalence_of_cats_counit_is_nat_z_iso
    : is_nat_z_iso dialgebra_equivalence_of_cats_counit.
  Proof.
    intro x.
    use is_z_iso_dialgebra.
    apply ε.
  Defined.

  Definition dialgebra_equivalence_of_cats
    : equivalence_of_cats (dialgebra F G) (dialgebra F' G').
  Proof.
    use make_equivalence_of_cats.
    - use make_adjunction_data.
      + exact dialgebra_equivalence_of_cats_functor.
      + exact dialgebra_equivalence_of_cats_inv_functor.
      + exact dialgebra_equivalence_of_cats_unit.
      + exact dialgebra_equivalence_of_cats_counit.
    - split.
      + exact dialgebra_equivalence_of_cats_unit_is_nat_z_iso.
      + exact dialgebra_equivalence_of_cats_counit_is_nat_z_iso.
  Defined.

  Definition dialgebra_adj_equivalence_of_cats
    : adj_equivalence_of_cats dialgebra_equivalence_of_cats_functor
    := adjointificiation dialgebra_equivalence_of_cats.
End DialgebraEquivalence.
