(************************************************************************************

 Properties of pseudofunctors

 In this file, we define several properties on pseudofunctors.

 The first one is the notion of local equivalence. A pseudofunctor is called a
 local equivalence if it induces an adjoint equivalence on every hom category. More
 specifically, every `F x y : B₁ ⟦ x , y ⟧ ⟶ B₂ ⟦ F x , F y ⟧` is an adjoint
 equivalence of categories.

 This definition is a categorification is the notion of fully faithful functor
 of categories. A functor `F : C₁ ⟶ C₂` is called fully faithful if every map
 `F x y : C₁ ⟦ x , y ⟧ → C₂ ⟦ F x , F y ⟧` is an equivalence of sets. The notion
 of local equivalence is similar: the only difference is that the dimension is
 one higher.

 We also define local weak equivalences. These induce a weak equivalence on every
 hom-category rather than an adjoint equivalence.

 Next we define essentially surjective pseudofunctors. We use this notion 
 to define several classes of weak equivalences of bicategories.

 Contents
 1. Local equivalences
 2. Projections for local equivalences
 3. Local weak equivalences
 4. Essentially surjective pseudofunctors
 5. Weak equivalences of bicategories

 ************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Equivalences.FullyFaithful.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope bicategory_scope.
Local Open Scope cat.

(** * 1. Local equivalences *)
Section LocalEquivalence.
  Context {B₁ B₂ : bicat}
          (HB₁ : is_univalent_2_1 B₁)
          (HB₂ : is_univalent_2_1 B₂)
          (F : psfunctor B₁ B₂).

  Definition local_equivalence
    : UU
    := ∏ (x y : B₁),
       @left_adjoint_equivalence
         bicat_of_univ_cats
         _ _
         (Fmor_univ F x y HB₁ HB₂).

  Definition make_local_equivalence
             (Fi₁ : ∏ (x y : B₁)
                      (f : F x --> F y),
                    x --> y)
             (Finv : ∏ (x y : B₁)
                       (f : F x --> F y),
                     invertible_2cell (# F (Fi₁ x y f)) f)
             (Fi₂ : ∏ (x y : B₁)
                      (f g : x --> y)
                      (τ : #F f ==> #F g),
                    f ==> g)
             (Fp₁ : ∏ (x y : B₁)
                      (f g : x --> y)
                      (τ : #F f ==> #F g),
                    ##F (Fi₂ x y f g τ) = τ)
             (Fp₂ : ∏ (x y : B₁)
                      (f g : x --> y)
                      (τ : f ==> g),
                    Fi₂ x y f g (##F τ) = τ)
    : local_equivalence.
  Proof.
    intros x y.
    use equiv_cat_to_adj_equiv.
    use rad_equivalence_of_cats.
    - apply univalent_category_is_univalent.
    - intros f g ; cbn in f, g.
      use isweq_iso.
      + exact (Fi₂ x y f g).
      + apply Fp₂.
      + apply Fp₁.
    - intros f ; cbn in f ; cbn.
      use hinhpr.
      simple refine (_ ,, _) ; cbn.
      + exact (Fi₁ x y f).
      + use inv2cell_to_z_iso.
        exact (Finv x y f).
  Defined.
End LocalEquivalence.

(** * 2. Projections for local equivalences *)
Section LocalEquivalenceProjections.
  Context {B₁ B₂ : bicat}
          {HB₁ : is_univalent_2_1 B₁}
          {HB₂ : is_univalent_2_1 B₂}
          {F : psfunctor B₁ B₂}
          (HF : local_equivalence HB₁ HB₂ F)
          (x y : B₁).

  Definition local_equivalence_right_adjoint
    : hom (F x) (F y) ⟶ hom x y
    := left_adjoint_right_adjoint (HF x y).

  Definition local_equivalence_unit
    : nat_z_iso (functor_identity _) (Fmor F x y ∙ local_equivalence_right_adjoint)
    := invertible_2cell_to_nat_z_iso _ _ (left_equivalence_unit_iso (HF x y)).

  Definition local_equivalence_counit
    : nat_z_iso (local_equivalence_right_adjoint ∙ Fmor F x y) (functor_identity _)
    := invertible_2cell_to_nat_z_iso _ _ (left_equivalence_counit_iso (HF x y)).
End LocalEquivalenceProjections.

(** * 3. Local weak equivalences *)
Definition local_weak_equivalence
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
  : UU
  := ∏ (x y : B₁),
     essentially_surjective (Fmor F x y)
     ×
     fully_faithful (Fmor F x y).

Definition make_local_weak_equivalence
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
           (HF₁ : ∏ (x y : B₁),
                  essentially_surjective (Fmor F x y))
           (HF₂ : ∏ (x y : B₁),
                  fully_faithful (Fmor F x y))
  : local_weak_equivalence F
  := λ x y, HF₁ x y ,, HF₂ x y.

(** * 4. Essentially surjective pseudofunctors *)
Definition essentially_surjective_psfunctor
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
  : hProp
  := ∀ (y : B₂), ∃ (x : B₁), adjoint_equivalence (F x) y.

(** * 5. Weak equivalences of bicategories *)
Definition weak_equivalence
           {B₁ B₂ : bicat}
           (HB₁ : is_univalent_2_1 B₁)
           (HB₂ : is_univalent_2_1 B₂)
           (F : psfunctor B₁ B₂)
  : UU
  := local_equivalence HB₁ HB₂ F
     ×
     essentially_surjective_psfunctor F.

Definition make_weak_equivalence
           {B₁ B₂ : bicat}
           {HB₁ : is_univalent_2_1 B₁}
           {HB₂ : is_univalent_2_1 B₂}
           {F : psfunctor B₁ B₂}
           (HF₁ : local_equivalence HB₁ HB₂ F)
           (HF₂ : essentially_surjective_psfunctor F)
  : weak_equivalence HB₁ HB₂ F
  := HF₁ ,, HF₂.

Definition weak_biequivalence
           {B₁ B₂ : bicat}
           (F : psfunctor B₁ B₂)
  : UU
  := essentially_surjective_psfunctor F × local_weak_equivalence F.

Lemma weak_equivalence_to_is_weak_biequivalence
      {B₁ B₂ : bicat}
      {HB₁ : is_univalent_2_1 B₁}
      {HB₂ : is_univalent_2_1 B₂}
      (F : psfunctor B₁ B₂)
      (HF : weak_equivalence HB₁ HB₂ F)
  : weak_biequivalence F.
Proof.
  exists (pr2 HF).
  intros x y.
  split.
  - apply functor_from_equivalence_is_essentially_surjective.
    apply (adj_equiv_to_equiv_cat (Fmor_univ F x y HB₁ HB₂)).
    exact (pr1 HF x y).
  - apply fully_faithful_from_equivalence.
    apply (adj_equiv_to_equiv_cat (Fmor_univ F x y HB₁ HB₂)).
    exact (pr1 HF x y).
Qed.
