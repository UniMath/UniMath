Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Slice.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.ConstProduct.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PullbackFunctor.
Import Products.Notations.

Local Open Scope cat.

Definition is_cartesian_closed_bicat
           (B : bicat_with_binprod)
  : UU
  := ∏ (x : B),
     right_universal_arrow
       (const_prod_psfunctor B x).

Definition make_is_cartesian_closed_bicat
           (B : bicat_with_binprod)
           (HB : is_univalent_2_1 B)
           (exp : B -> B → B)
           (app : ∏ (x y : B), exp x y ⊗ x --> y)
           (app2 : ∏ (x y₁ y₂ : B)
                     (f g : y₁ --> exp x y₂)
                     (α : f ⊗₁ id₁ x · app x y₂ ==> g ⊗₁ id₁ x · app x y₂),
                   f ==> g)
           (app2_eq : ∏ (x y₁ y₂ : B)
                        (f g : y₁ --> exp x y₂)
                        (α : f ⊗₁ id₁ x · app x y₂ ==> g ⊗₁ id₁ x · app x y₂),
                      app2 x y₁ y₂ f g α ⊗₂ id₂ (id₁ x) ▹ app x y₂ = α)
           (H : ∏ (x y₁ y₂ : B)
                  (f g : y₁ --> exp x y₂)
                  (α : f ⊗₁ id₁ x · app x y₂ ==> g ⊗₁ id₁ x · app x y₂)
                  (β₁ β₂ : f ==> g)
                  (p₁ : β₁ ⊗₂ id₂ (id₁ x) ▹ app x y₂ = α)
                  (p₂ : β₂ ⊗₂ id₂ (id₁ x) ▹ app x y₂ = α),
                β₁ = β₂)
           (lam : ∏ (x y₁ y₂ : B)
                    (f : y₁ ⊗ x --> y₂),
                  y₁ --> exp x y₂)
           (app_lam : ∏ (x y₁ y₂ : B)
                        (f : y₁ ⊗ x --> y₂),
                      invertible_2cell (lam x y₁ y₂ f ⊗₁ id₁ x · app x y₂) f)
  : is_cartesian_closed_bicat B.
Proof.
  intro x.
  use make_right_universal_arrow'.
  - exact HB.
  - exact (exp x).
  - exact (app x).
  - intros y₁ y₂ f g α.
    simple refine (_ ,, _).
    + exact (app2 x y₁ y₂ f g α).
    + exact (app2_eq x y₁ y₂ f g α).
  - exact (H x).
  - intros y₁ y₂ f.
    simple refine (_ ,, _).
    + exact (lam x y₁ y₂ f).
    + exact (app_lam x y₁ y₂ f).
Defined.

Definition exponentiable_morphism
           (B : bicat_with_pb)
           {b₁ b₂ : B}
           (f : b₁ --> b₂)
  : UU
  := right_universal_arrow (pb_psfunctor B f).

Definition locally_cartesian_closed_bicat
           (B : bicat_with_pb)
  : UU
  := ∏ (b₁ b₂ : B)
       (f : b₁ --> b₂),
     exponentiable_morphism B f.

Definition bicat_has_exponentials
           (B : bicat_with_pb)
  : UU
  := ∏ (b₁ b₂ : B)
       (f : b₁ --> b₂),
     (internal_sfib f → exponentiable_morphism B f)
     ×
     (internal_sopfib f → exponentiable_morphism B f).


(*
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Limits.Examples.OneTypesLimits.

Definition HLevel_fun
           {n : nat}
           (X Y : HLevel n)
  : HLevel n.
Proof.
  simple refine (_ ,, _).
  - exact (pr1 X → pr1 Y).
  - apply impredfun.
    exact (pr2 Y).
Defined.

Definition app_fun
           {X Y : UU}
  : (X → Y) × X → Y
  := λ fx, pr1 fx (pr2 fx).

Definition app_homot
           {X Y₁ Y₂ : UU}
           {f g : Y₁ → X → Y₂}
           (p : ∏ (z : Y₁ × X), f (pr1 z) (pr2 z) = g (pr1 z) (pr2 z))
           (y : Y₁)
  : f y = g y
  := funextsec _ _ _ (λ x, p (y ,, x)).

Definition maponpaths_app_homot
           {X Y₁ Y₂ : UU}
           {f g : Y₁ → X → Y₂}
           (p : ∏ (z : Y₁ × X), f (pr1 z) (pr2 z) = g (pr1 z) (pr2 z))
           (x : X)
           (y : Y₁)
  : maponpaths (λ f, f x) (app_homot p y)
    =
    p (y ,, x).
Proof.
  apply (maponpaths_funextsec (f y)).
Defined.

Definition maponpaths_app_fun
           {X Y : UU}
           {fx gx : (X → Y) × X}
           (p : fx = gx)
  : maponpaths (λ (fx : (X → Y) × X), app_fun fx) p
    =
    maponpaths (λ z, z (pr2 fx)) (maponpaths dirprod_pr1 p)
    @
    maponpaths (pr1 gx) (maponpaths dirprod_pr2 p).
Proof.
  induction p.
  apply idpath.
Defined.

Definition paths_pathsdirprod
           {X Y : UU}
           {x₁ x₂ : X}
           {y₁ y₂ : Y}
           {p₁ p₂ : x₁ = x₂}
           {q₁ q₂ : y₁ = y₂}
           (r₁ : p₁ = p₂)
           (r₂ : q₁ = q₂)
  : pathsdirprod p₁ q₁
    =
    pathsdirprod p₂ q₂.
Proof.
  induction r₁, r₂.
  apply idpath.
Defined.

Definition one_types_pair_2cell
           {X₁ X₂ Y₁ Y₂ : one_type}
           {f₁ f₂ : X₁ → Y₁}
           {g₁ g₂ : X₂ → Y₂}
           (p : f₁ ~ f₂)
           (q : g₁ ~ g₂)
           (x₁ : X₁)
           (x₂ : X₂)
  : @pair_2cell
      (_ ,, has_binprod_one_types)
      X₁ X₂ Y₁ Y₂
      f₁ f₂
      g₁ g₂
      p
      q
      (x₁ ,, x₂)
    =
    pathsdirprod
      (p x₁)
      (q x₂).
Proof.
  refine (pathsdirprod_eta _ @ _).
  use paths_pathsdirprod.
  - pose (@pair_2cell_pr1
            (_ ,, has_binprod_one_types)
            X₁ X₂ Y₁ Y₂
            f₁ f₂
            g₁ g₂
            p
            q)
      as r.
    etrans.
    {
      apply (eqtohomot r (x₁ ,, x₂)).
    }
    apply pathscomp0rid.
  - pose (@pair_2cell_pr2
            (_ ,, has_binprod_one_types)
            X₁ X₂ Y₁ Y₂
            f₁ f₂
            g₁ g₂
            p
            q)
      as r.
    etrans.
    {
      apply (eqtohomot r (x₁ ,, x₂)).
    }
    apply pathscomp0rid.
Qed.

Definition test
           {X Y : UU}
           {f g : X → Y}
           {e₁ e₂ : f = g}
           (h : ∏ (x : X), eqtohomot e₁ x = eqtohomot e₂ x)
  : e₁ = e₂.
Proof.
  refine (!(@funextsec_toforallpaths X (λ _, Y) f g e₁) @ _).
  refine (_ @ @funextsec_toforallpaths X (λ _, Y) f g e₂).
  apply maponpaths.
  use funextsec.
  intro x.
  apply h.
Defined.

Definition is_cartesian_closed_one_types
  : is_cartesian_closed_bicat (_ ,, has_binprod_one_types).
Proof.
  use make_is_cartesian_closed_bicat.
  - exact one_types_is_univalent_2_1.
  - intros X Y.
    exact (HLevel_fun X Y).
  - exact (λ X Y fx, app_fun fx).
  - exact (λ X Y₁ Y₂ f g p, app_homot p).
  - simpl ; intros X Y₁ Y₂ f g p.
    cbn in p.
    unfold homotsec in p.
    cbn -[pair_2cell].
    unfold homotfun.
    use funextsec.
    intro yx.
    rewrite one_types_pair_2cell.
    rewrite maponpaths_app_fun.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_pr2_pathsdirprod.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_pr1_pathsdirprod.
    }
    cbn.
    rewrite pathscomp0rid.
    apply maponpaths_app_homot.
  - simpl ; intros X Y₁ Y₂ f g p q₁ q₂ r₁ r₂.
    use funextsec.
    intro y.
    use test.
    intro x.
    refine (_ @ eqtohomot r₁ (y ,, x) @ !(eqtohomot r₂ (y ,, x)) @ _).
    + cbn -[pair_2cell].
      unfold homotfun, homotrefl.
      rewrite one_types_pair_2cell.
      rewrite maponpaths_app_fun.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_pr2_pathsdirprod.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
      }
      cbn.
      apply pathscomp0rid.
    + cbn -[pair_2cell].
      unfold homotfun, homotrefl.
      rewrite one_types_pair_2cell.
      rewrite maponpaths_app_fun.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_pr2_pathsdirprod.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
      }
      cbn.
      apply pathscomp0rid.
  - exact (λ X Y₁ Y₂ f y x, f (y ,, x)).
  - simpl ; intros X Y₁ Y₂ f.
    use make_invertible_2cell.
    + apply homotrefl.
    + apply one_type_2cell_iso.
Defined.
*)
