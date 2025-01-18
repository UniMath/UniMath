(*********************************************************************

 Fiberwise equivalences between fibrations are equivalences

 As an application of the Grothendieck construction, we can show that
 whenever we have cartesian functor between two fibrations which
 induces equivalences on the fibers, then this functor is actually an
 equivalence in the bicategory of fibrations.

 The proof goes as follows.

 Suppose that we have two fibrations `P₁` and `P₂` over `C` and a
 cartesian functor `F` from `P₁` to `P₂` that lives over the identity.
 In addition, note that `F` induces for every `x : C` a functor from
 the fiber of `x` along `P₁` and the fiber of `x` along `P₂` (this is
 [fiber_functor]). Now assume that for every object `x` this functor
 between the fibers is an equivalence.

 We want to prove that `F` is an adjoint equivalence in the bicategory
 of fibrations over `C`. Since the Grothendieck construction gives
 rise to a biequivalence and since biequivalences reflect adjoint
 equivalences, it suffices to check whether the image of `F` along the
 Grothendieck constructor is an adjoint equivalence. Note that the
 image of `F` is a pseudotransformation and that we can check
 pointwise whether a pseudotransformation is an adjoint equivalence.
 The action on objects of this pseudotransformation is actually given
 by the fiber functor mentioned before, so to check whether `F` is an
 adjoint equivalence, we need to check whether the fiber functor is
 an equivalence. This is precisely what we assumed.

 Note that to check whether the fiber functor is an equivalence, it
 suffices to check whether it is fully faithful and essentially
 surjective. For displayed categories, we have a similar statement:
 a displayed functor between displayed categories is an equivalence if
 that functor is fully faithful and essentially surjective. However,
 there is a slight difference between the statement that we obtain in
 this file and the corresponding statement for displayed categories:
 for displayed categories, we need to check fullness and faithfulness
 for all morphisms, whereas for fibrations, it suffices to check it
 only for those morphisms lying above the identity.

 Note the following as well: another version of the Grothendieck
 construction says that the bicategory of fibrations over `C` with all
 functors is equivalent to the bicategory of pseudofunctors with oplax
 transformations. However, using this version would not give a stronger
 statement than the one in this file. That is because to check whether
 an oplax transformation is an adjoint equivalence, we need to check
 whether it is a pointwise equivalence and whether it is a
 pseudotransformation. Checking whether the corresponding oplax
 transformation is a pseudotransformation, amounts to proving that the
 functor in question is cartesian.

 *********************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.FibSlice.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.Grothendieck.Biequivalence.

Local Open Scope cat.

Definition fiberwise_equiv_to_adjequiv
           {C : univalent_category}
           {P₁ P₂ : fib_slice_bicat C}
           (F : P₁ --> P₂)
           (HF : ∏ (x : C), adj_equivalence_of_cats (fiber_functor (pr1 F) x))
  : left_adjoint_equivalence F.
Proof.
  use (biequiv_reflect_adjequiv (grothendieck_construction C)).
  use pointwise_adjequiv_to_adjequiv.
  - exact univalent_cat_is_univalent_2.
  - intros x ; cbn.
    use equiv_cat_to_adj_equiv.
    exact (HF x).
Defined.

Definition ff_and_eso_to_adjequiv
           {C : univalent_category}
           {P₁ P₂ : fib_slice_bicat C}
           (F : P₁ --> P₂)
           (F_full : ∏ (x : C), full (fiber_functor (pr1 F) x))
           (F_faithful : ∏ (x : C), faithful (fiber_functor (pr1 F) x))
           (F_eso : ∏ (x : C), Functors.essentially_surjective (fiber_functor (pr1 F) x))
  : left_adjoint_equivalence F.
Proof.
  use fiberwise_equiv_to_adjequiv.
  intro x.
  use rad_equivalence_of_cats.
  - use is_univalent_fiber.
    apply (pr1 P₁).
  - use full_and_faithful_implies_fully_faithful.
    split.
    + exact (F_full x).
    + exact (F_faithful x).
  - exact (F_eso x).
Defined.
