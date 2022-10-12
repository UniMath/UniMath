(**
 Morphisms in the bicat of univalent categories

 Contents:
 1. Faithful 1-cells
 2. Fully faithful 1-cells
 3. Esos in 1-types
 4. (eso, ff)-factorization
 5. Esos are closed under pullback
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.Eso.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Examples.OneTypesLimits.

Local Open Scope cat.

Definition pr1_image
           {X Y : UU}
           (f : X → Y)
  : image f → Y
  := pr1.

Definition isInjective_pr1_image
           {X Y : UU}
           (f : X → Y)
  : isInjective (pr1_image f).
Proof.
  intros y₁ y₂.
  refine (pr2 (path_sigma_hprop
                 (λ (y : Y), ∥ hfiber f y ∥)
                 y₁ y₂
                 _)).
  apply ishinh.
Qed.

Definition isofhlevel_image
           {X Y : UU}
           (f : X → Y)
           {n : nat}
           (HY : isofhlevel (S n) Y)
  : isofhlevel (S n) (image f).
Proof.
  unfold image.
  use isofhleveltotal2.
  - exact HY.
  - intro y.
    apply isofhlevelsnprop.
    apply ishinh.
Defined.

Definition HLevel_image
           {n : nat}
           {X : UU}
           {Y : HLevel (S n)}
           (f : X → pr1 Y)
  : HLevel (S n).
Proof.
  refine (image f ,, _).
  apply isofhlevel_image.
  exact (pr2 Y).
Defined.


Section ImageMap.
  Context {X I₁ I₂ Y : UU}
          {f₁ : X → I₁}
          (Hf₁ : issurjective f₁)
          (f₂ : X → I₂)
          (m₁ : I₁ → Y)
          {m₂ : I₂ → Y}
          (Hm₂ : isInjective m₂)
          (p : ∏ (x : X), m₂(f₂ x) = m₁(f₁ x)).

  Definition image_function_help
             (i : I₁)
    : ∃! (x : I₂), m₂ x = m₁ i.
  Proof.
    use (factor_through_squash _ _ (Hf₁ i)).
    {
      apply isapropiscontr.
    }
    intros x.
    use iscontraprop1.
    - apply (isinclweqonpaths _ Hm₂).
    - simple refine (f₂ (pr1 x) ,, _).
      exact (p (pr1 x) @ maponpaths m₁ (pr2 x)).
  Defined.

  Definition image_function
    : I₁ → I₂
    := λ i, pr11 (image_function_help i).
End ImageMap.



(**
 1. Faithful 1-cells
 *)
Definition one_types_is_incl_faithful_1cell
           {X Y : one_types}
           (f : X --> Y)
           (Hf : ∏ (x y : (X : one_type)), isincl (@maponpaths _ _ f x y))
  : faithful_1cell f.
Proof.
  intros z g₁ g₂ α₁ α₂ p.
  use funextsec.
  intro x.
  cbn in * ; unfold homotfun in *.
  pose (Hf (g₁ x) (g₂ x) (maponpaths f (α₂ x))) as i.
  pose (proofirrelevance _ i (α₁ x ,, eqtohomot p x) (α₂ x ,, idpath _)) as k.
  exact (maponpaths pr1 k).
Qed.

Definition one_types_faithful_1cell_is_incl
           {X Y : one_types}
           (f : X --> Y)
           (Hf : faithful_1cell f)
  : ∏ (x y : (X : one_type)), isincl (@maponpaths _ _ f x y).
Proof.
  intros x y ; cbn in *.
  use isinclweqonpaths.
  intros p q.
  use isweqimplimpl.
  - intros α.
    pose (eqtohomot
            (Hf X (λ _, x) (λ _, y)
                (λ _, p) (λ _, q)
                (funextsec _ _ _ (λ _, α)))
            x)
      as fp.
    exact fp.
  - use invproofirrelevance.
    intros ? ?.
    apply X.
  - use invproofirrelevance.
    intros ? ?.
    apply Y.
Qed.

Definition one_types_is_incl_weq_faithful_1cell
           {X Y : one_types}
           (f : X --> Y)
  : (∏ (x y : (X : one_type)), isincl (@maponpaths _ _ f x y))
    ≃
    faithful_1cell f.
Proof.
  use weqimplimpl.
  - exact (one_types_is_incl_faithful_1cell f).
  - exact (one_types_faithful_1cell_is_incl f).
  - do 2 (use impred ; intro).
    apply isapropisincl.
  - apply isaprop_faithful_1cell.
Qed.

(**
 2. Fully faithful 1-cells
 *)
Definition one_types_isInjective_fully_faithful_1cell
           {X Y : one_types}
           (f : X --> Y)
           (Hf : isInjective f)
  : fully_faithful_1cell f.
Proof.
  use make_fully_faithful.
  - apply one_types_is_incl_faithful_1cell.
    intros x y.
    apply isinclweq.
    apply Hf.
  - intros Z g₁ g₂ αf ; cbn in * ; unfold homotfun in *.
    simple refine (_ ,, _).
    + intro x.
      apply (invmap (make_weq _ (Hf (g₁ x) (g₂ x)))).
      exact (αf x).
    + use funextsec.
      intro x.
      apply (homotweqinvweq (make_weq _ (Hf (g₁ x) (g₂ x)))).
Qed.

Definition one_types_fully_faithful_isInjective
           {X Y : one_types}
           (f : X --> Y)
           (Hf : fully_faithful_1cell f)
  : isInjective f.
Proof.
  intros x y ; cbn in *.
  use isweq_iso.
  - intro p.
    exact (pr1 (pr2 Hf X (λ _, x) (λ _, y) (λ _, p)) x).
  - intro p ; simpl.
    pose (pr1 Hf
               _ _ _
               (pr1 (pr2 Hf X (λ _ : X, x) (λ _ : X, y) (λ _ : X, maponpaths f p)))
               (λ _, p))
      as q.
    cbn in q.
    refine (eqtohomot (q _) x).
    unfold homotfun.
    use funextsec.
    intro ; cbn.
    exact (eqtohomot (pr2 (pr2 Hf X (λ _, x) (λ _, y) (λ _, maponpaths f p))) _).
  - intros p.
    exact (eqtohomot (pr2 (pr2 Hf X (λ _, x) (λ _, y) (λ _, p))) x).
Qed.

Definition one_types_isInjective_weq_fully_faithful
           {X Y : one_types}
           (f : X --> Y)
  : isInjective f ≃ fully_faithful_1cell f.
Proof.
  use weqimplimpl.
  - exact (one_types_isInjective_fully_faithful_1cell f).
  - exact (one_types_fully_faithful_isInjective f).
  - apply isaprop_isInjective.
  - apply isaprop_fully_faithful_1cell.
Qed.

(**
 3. Esos in 1-types
 *)
Section IsSurjectiveEsoFull.
  Context {X Y : one_types}
          {f : X --> Y}
          (Hf : issurjective f)
          {W₁ W₂ : one_types}
          {m : W₁ --> W₂}
          (Hm : fully_faithful_1cell m)
          {g₁ g₂ : Y --> W₁}
          (p₁ : f · g₁ ==> f · g₂)
          (p₂ : g₁ · m ==> g₂ · m)
          (q : (p₁ ▹ m) • rassociator f g₂ m = rassociator f g₁ m • (f ◃ p₂)).

  Definition issurjective_is_eso_full_lift_2
    : g₁ ==> g₂.
  Proof.
    intro x.
    apply (invmap
             (make_weq
                _
                (one_types_fully_faithful_isInjective _ Hm (g₁ x) (g₂ x)))).
    exact (p₂ x).
  Defined.

  Definition issurjective_is_eso_full_lift_2_left
    : f ◃ issurjective_is_eso_full_lift_2 = p₁.
  Proof.
    use funextsec.
    intro x.
    pose (H := homotinvweqweq
                 (make_weq
                    _
                    (one_types_fully_faithful_isInjective _ Hm (g₁(f x)) (g₂(f x))))).
    refine (!(H _) @ _ @ H _).
    apply maponpaths.
    etrans.
    {
      apply homotweqinvweq.
    }
    refine (!(eqtohomot q x) @ _).
    apply pathscomp0rid.
  Qed.

  Definition issurjective_is_eso_full_lift_2_right
    : issurjective_is_eso_full_lift_2 ▹ m = p₂.
  Proof.
    use funextsec.
    intro x.
    apply (homotweqinvweq
             (make_weq
                _
                (one_types_fully_faithful_isInjective _ Hm (g₁ x) (g₂ x)))).
  Qed.
End IsSurjectiveEsoFull.

Definition issurjective_is_eso_full
           {X Y : one_types}
           {f : X --> Y}
           (Hf : issurjective f)
  : is_eso_full f.
Proof.
  intros W₁ W₂ m Hm g₁ g₂ p₁ p₂ q.
  simple refine (_ ,, _ ,, _).
  - exact (issurjective_is_eso_full_lift_2 Hm p₂).
  - exact (issurjective_is_eso_full_lift_2_left Hm _ _ q).
  - apply issurjective_is_eso_full_lift_2_right.
Qed.

Definition issurjective_is_eso_faithful
           {X Y : one_types}
           {f : X --> Y}
           (Hf : issurjective f)
  : is_eso_faithful f.
Proof.
  intros W₁ W₂ m Hm g₁ g₂ p₁ p₂ q₁ q₂.
  use funextsec.
  intro x.
  use (invmaponpathsincl
         _
         (one_types_faithful_1cell_is_incl
            m
            (pr1 Hm)
            (g₁ x) (g₂ x))).
  exact (eqtohomot q₂ x).
Qed.

Section IsSurjectiveIsEsoEssentiallySurjective.
  Context {X₁ X₂ Y₁ Y₂ : one_types}
          {f : X₁ --> X₂}
          (Hf : issurjective f)
          {m : Y₁ --> Y₂}
          (Hm : isInjective m)
          {g₁ : X₁ --> Y₁}
          {g₂ : X₂ --> Y₂}
          (p : invertible_2cell (g₁ · m) (f · g₂)).

  Let I₁ : UU := image g₁.
  Let I₂ : UU := image g₂.

  Definition issurjective_is_eso_lift_1
    : X₂ --> Y₁
    := image_function Hf g₁ g₂ Hm (pr1 p).

  Definition issurjective_is_eso_lift_1_right
    : issurjective_is_eso_lift_1 · m ==> g₂.
  Proof.
    intro x.
    exact (pr21 (image_function_help Hf g₁ g₂ Hm (pr1 p) x)).
  Defined.

  (**
   The equation of this one is derived from `issurjective_is_eso_lift_1_eq`
   *)
  Definition issurjective_is_eso_lift_1_left
    : f · issurjective_is_eso_lift_1 ==> g₁.
  Proof.
    intro x.
    exact (invmap
             (make_weq
                _
                (Hm (issurjective_is_eso_lift_1 (f x)) (g₁ x)))
             (issurjective_is_eso_lift_1_right (f x) @ ! pr1 p x)).
  Defined.

  Definition issurjective_is_eso_lift_1_eq
    : (issurjective_is_eso_lift_1_left ▹ m) • p
      =
      rassociator _ _ _ • (f ◃ issurjective_is_eso_lift_1_right).
  Proof.
    use funextsec.
    intro x.
    cbn ; unfold homotcomp, homotfun, funhomotsec.
    use hornRotation_rr.
    use (invmaponpathsweq
           (invweq (make_weq _ (Hm (issurjective_is_eso_lift_1 (f x)) (g₁ x))))).
    apply (homotinvweqweq
             (make_weq _ (Hm (issurjective_is_eso_lift_1 (f x)) (g₁ x)))).
  Qed.
End IsSurjectiveIsEsoEssentiallySurjective.

Definition issurjective_is_eso_essentially_surjective
           {X₁ X₂ : one_types}
           {f : X₁ --> X₂}
           (Hf : issurjective f)
  : is_eso_essentially_surjective f.
Proof.
  intros Y₁ Y₂ m Hm' g₁ g₂ p.
  pose (Hm := one_types_fully_faithful_isInjective _ Hm').
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (issurjective_is_eso_lift_1 Hf Hm p).
  - use make_invertible_2cell.
    + exact (issurjective_is_eso_lift_1_left Hf Hm p).
    + apply one_type_2cell_iso.
  - use make_invertible_2cell.
    + exact (issurjective_is_eso_lift_1_right Hf Hm p).
    + apply one_type_2cell_iso.
  - exact (issurjective_is_eso_lift_1_eq Hf Hm p).
Defined.

Definition issurjective_is_eso
           {X Y : one_types}
           {f : X --> Y}
           (Hf : issurjective f)
  : is_eso f.
Proof.
  use make_is_eso.
  - exact one_types_is_univalent_2_1.
  - exact (issurjective_is_eso_full Hf).
  - exact (issurjective_is_eso_faithful Hf).
  - exact (issurjective_is_eso_essentially_surjective Hf).
Defined.

Section IsEsoIsSurjective.
  Context {X Y : one_types}
          {f : X --> Y}
          (Hf : is_eso f).

  Let im : one_types := HLevel_image f.
  Let fim : X --> im := prtoimage f.
  Let π : im --> Y := pr1_image f.

  Definition is_eso_issurjective_inv2cell
    : invertible_2cell
        (fim · π)
        (f · id₁ Y).
  Proof.
    use make_invertible_2cell.
    - exact (λ _, idpath _).
    - apply one_type_2cell_iso.
  Defined.

  Local Definition is_eso_issurjective_help_map
    : Y --> im
    := is_eso_lift_1
         _
         Hf
         (one_types_isInjective_fully_faithful_1cell
            π
            (isInjective_pr1_image f))
         (prtoimage f)
         (id₁ _)
         is_eso_issurjective_inv2cell.

  Let φ := is_eso_issurjective_help_map.

  Definition is_eso_issurjective
    : issurjective f.
  Proof.
    intro y.
    use (factor_through_squash _ _ (pr2 (φ y))).
    {
      apply ishinh.
    }
    intros x.
    apply hinhpr.
    refine (pr1 x ,, _).
    refine (pr2 x @ _).
    exact (pr1 (is_eso_lift_1_comm_right
                  _
                  Hf
                  (one_types_isInjective_fully_faithful_1cell
                     π
                     (isInjective_pr1_image f))
                  (prtoimage f)
                  (id₁ _)
                  is_eso_issurjective_inv2cell)
               y).
  Qed.
End IsEsoIsSurjective.

Definition issurjective_weq_is_eso
           {X Y : one_types}
           (f : X --> Y)
  : issurjective f ≃ is_eso f.
Proof.
  use weqimplimpl.
  - exact issurjective_is_eso.
  - exact is_eso_issurjective.
  - apply isapropissurjective.
  - apply isaprop_is_eso.
    exact one_types_is_univalent_2_1.
Defined.

(**
 4. (eso, ff)-factorization
 *)
Definition eso_ff_factorization_one_types
  : eso_ff_factorization one_types.
Proof.
  intros X Y f.
  refine (HLevel_image f ,, _).
  refine (pr1_image f ,, prtoimage f ,, _ ,, _ ,, _).
  - apply one_types_isInjective_fully_faithful_1cell.
    apply isInjective_pr1_image.
  - apply issurjective_is_eso.
    apply issurjprtoimage.
  - use make_invertible_2cell.
    + intro x.
      apply idpath.
    + apply one_type_2cell_iso.
Defined.

(**
 5. Esos are closed under pullback
 *)
Definition is_eso_closed_under_pb_one_types
  : is_eso_closed_under_pb (_ ,, one_types_has_pb).
Proof.
  intros X Y Z f Hf' g ; cbn in *.
  use issurjective_is_eso.
  pose (Hf := is_eso_issurjective Hf').
  intros y.
  use (factor_through_squash _ _ (Hf (g y))).
  {
    apply ishinh.
  }
  intros x.
  apply hinhpr.
  exact (((pr1 x ,, y) ,, !(pr2 x)) ,, idpath _).
Defined.
