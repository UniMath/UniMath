(*****************************************************************************************

 Examples of profunctors

 In this file, we collect numerous examples of profunctors. We also give computation rules
 for their left and right actions.

 Contents
 1. The constant profunctor
 2. The identity profunctor
 3. Representable profunctors
 4. Precomposition of a profunctor with functors
 5. Product of profunctors

 *****************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Profunctors.Core.

Local Open Scope cat.

(** * 1. The constant profunctor *)
Section ConstantProfunctor.
  Context (C D : category)
          (X : hSet).

  Definition const_profunctor_data
    : profunctor_data C D.
  Proof.
    use make_profunctor_data.
    - exact (λ _ _, X).
    - exact (λ _ _ _ _ _ _ x, x).
  Defined.

  Proposition const_profunctor_laws
    : profunctor_laws const_profunctor_data.
  Proof.
    repeat split.
    intros.
    apply setproperty.
  Qed.

  Definition const_profunctor
    : C ↛ D.
  Proof.
    use make_profunctor.
    - exact const_profunctor_data.
    - exact const_profunctor_laws.
  Defined.

  Proposition lmap_const_profunctor
              {x : C}
              {y₁ y₂ : D}
              (f : y₂ --> y₁)
              (h : X)
    : lmap const_profunctor f (h : const_profunctor y₁ x) = h.
  Proof.
    cbn.
    apply idpath.
  Qed.

  Proposition rmap_const_profunctor
              {x₁ x₂: C}
              {y : D}
              (f : x₁ --> x₂)
              (h : X)
    : rmap const_profunctor f (h : const_profunctor y x₁) = h.
  Proof.
    cbn.
    apply idpath.
  Qed.
End ConstantProfunctor.

(** * 2. The identity profunctor *)
Section IdentityProfunctor.
  Context (C : category).

  Definition id_profunctor_data
    : profunctor_data C C.
  Proof.
    use make_profunctor_data.
    - exact (λ x y, x --> y).
    - exact (λ y₁ y₂ g x₁ x₂ f h, g · h · f).
  Defined.

  Proposition id_profunctor_laws
    : profunctor_laws id_profunctor_data.
  Proof.
    repeat split ; intros ; cbn.
    - rewrite id_left, id_right.
      apply idpath.
    - rewrite !assoc'.
      apply idpath.
    - apply homset_property.
  Qed.

  Definition id_profunctor
    : C ↛ C.
  Proof.
    use make_profunctor.
    - exact id_profunctor_data.
    - exact id_profunctor_laws.
  Defined.

  Proposition lmap_id_profunctor
              {x y₁ y₂ : C}
              (f : y₂ --> y₁)
              (h : y₁ --> x)
    : lmap id_profunctor f h = f · h.
  Proof.
    cbn.
    rewrite id_right.
    apply idpath.
  Qed.

  Proposition rmap_id_profunctor
              {x₁ x₂ y : C}
              (f : x₁ --> x₂)
              (h : y --> x₁)
    : rmap id_profunctor f h = h · f.
  Proof.
    cbn.
    rewrite id_left.
    apply idpath.
  Qed.
End IdentityProfunctor.

(** * 3. Representable profunctors *)
Section RepresentableProfunctor.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂).

  Definition representable_profunctor_left_data
    : profunctor_data C₁ C₂.
  Proof.
    use make_profunctor_data.
    - exact (λ y x, y --> F x).
    - exact (λ y₁ y₂ g x₁ x₂ f h, g · h · #F f).
  Defined.

  Proposition representable_profunctor_left_laws
    : profunctor_laws representable_profunctor_left_data.
  Proof.
    repeat split ; intros ; cbn.
    - rewrite functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    - apply homset_property.
  Qed.

  Definition representable_profunctor_left
    : C₁ ↛ C₂.
  Proof.
    use make_profunctor.
    - exact representable_profunctor_left_data.
    - exact representable_profunctor_left_laws.
  Defined.

  Proposition lmap_representable_profunctor_left
              {x : C₁}
              {y₁ y₂ : C₂}
              (g : y₂ --> y₁)
              (h : y₁ --> F x)
    : lmap representable_profunctor_left g h = g · h.
  Proof.
    cbn.
    rewrite functor_id.
    rewrite id_right.
    apply idpath.
  Qed.

  Proposition rmap_representable_profunctor_left
              {x₁ x₂ : C₁}
              {y : C₂}
              (f : x₁ --> x₂)
              (h : y --> F x₁)
    : rmap representable_profunctor_left f h = h · #F f.
  Proof.
    cbn.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition representable_profunctor_right_data
    : profunctor_data C₂ C₁.
  Proof.
    use make_profunctor_data.
    - exact (λ y x, F y --> x).
    - exact (λ y₁ y₂ g x₁ x₂ f h, #F g · h · f).
  Defined.

  Proposition representable_profunctor_right_laws
    : profunctor_laws representable_profunctor_right_data.
  Proof.
    repeat split ; intros ; cbn.
    - rewrite functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    - apply homset_property.
  Qed.

  Definition representable_profunctor_right
    : C₂ ↛ C₁.
  Proof.
    use make_profunctor.
    - exact representable_profunctor_right_data.
    - exact representable_profunctor_right_laws.
  Defined.

  Proposition lmap_representable_profunctor_right
              {x : C₂}
              {y₁ y₂ : C₁}
              (g : y₂ --> y₁)
              (h : F y₁ --> x)
    : lmap representable_profunctor_right g h = #F g · h.
  Proof.
    cbn.
    rewrite id_right.
    apply idpath.
  Qed.

  Proposition rmap_representable_profunctor_right
              {x₁ x₂ : C₂}
              {y : C₁}
              (f : x₁ --> x₂)
              (h : F y --> x₁)
    : rmap representable_profunctor_right f h = h · f.
  Proof.
    cbn.
    rewrite functor_id.
    rewrite id_left.
    apply idpath.
  Qed.
End RepresentableProfunctor.

(** * 4. Precomposition of a profunctor with functors *)
Section PrecompProfunctor.
  Context {C₁ C₂ D₁ D₂ : category}
          (F : C₁ ⟶ C₂)
          (G : D₁ ⟶ D₂)
          (P : C₂ ↛ D₂).

  Definition precomp_profunctor_data
    : profunctor_data C₁ D₁.
  Proof.
    use make_profunctor_data.
    - exact (λ y x, P (G y) (F x)).
    - exact (λ y₁ y₂ g x₁ x₂ f h, lmap P (#G g) (rmap P (#F f) h)).
  Defined.

  Proposition precomp_profunctor_laws
    : profunctor_laws precomp_profunctor_data.
  Proof.
    repeat split ; intros ; cbn -[lmap rmap].
    - rewrite !functor_id.
      rewrite lmap_id, rmap_id.
      apply idpath.
    - rewrite !functor_comp.
      rewrite lmap_comp.
      rewrite rmap_comp.
      apply maponpaths.
      rewrite lmap_rmap.
      apply idpath.
    - apply setproperty.
  Qed.

  Definition precomp_profunctor
    : C₁ ↛ D₁.
  Proof.
    use make_profunctor.
    - exact precomp_profunctor_data.
    - exact precomp_profunctor_laws.
  Defined.

  Proposition lmap_precomp_profunctor
              {x : C₁}
              {y₁ y₂ : D₁}
              (f : y₂ --> y₁)
              (h : P (G y₁) (F x))
    : lmap precomp_profunctor f h = lmap P (#G f) h.
  Proof.
    cbn.
    rewrite functor_id.
    rewrite rmap_id.
    apply idpath.
  Qed.

  Proposition rmap_precomp_profunctor
              {x₁ x₂ : C₁}
              {y : D₁}
              (f : x₁ --> x₂)
              (h : P (G y) (F x₁))
    : rmap precomp_profunctor f h = rmap P (#F f) h.
  Proof.
    cbn.
    rewrite functor_id.
    rewrite lmap_id.
    apply idpath.
  Qed.
End PrecompProfunctor.

(** * 5. Product of profunctors *)
Section ProdProfunctor.
  Context {C₁ C₂ : category}
          (P Q : C₁ ↛ C₂).

  Definition prod_profunctor_data
    : profunctor_data C₁ C₂.
  Proof.
    use make_profunctor_data.
    - exact (λ y x, P y x × Q y x).
    - exact (λ y₁ y₂ g x₁ x₂ f h, P #[ g , f ] (pr1 h) ,, Q #[ g , f ] (pr2 h)).
  Defined.

  Proposition prod_profunctor_laws
    : profunctor_laws prod_profunctor_data.
  Proof.
    repeat split ; cbn.
    - intros y x h.
      rewrite !profunctor_id.
      apply idpath.
    - intros y₁ y₂ y₃ g₁ g₂ x₁ x₂ x₃ f₁ f₂ h.
      rewrite !profunctor_comp.
      apply idpath.
    - intros y x.
      apply isaset_dirprod ; apply setproperty.
  Qed.

  Definition prod_profunctor
    : C₁ ↛ C₂.
  Proof.
    use make_profunctor.
    - exact prod_profunctor_data.
    - exact prod_profunctor_laws.
  Defined.
End ProdProfunctor.
