(*
This is the first of 4 files, to conclude that the Rezk completion for (cartesian) categories, lifts to a Rezk completion for cartesian closed categories.

In this file, we show that if F : C -> D is a weak equivalence (with D univalent!), between cartesian categories, then:
If (x₀ : C) is exponentiable, then so is (F x₀ : D).

Caveat:
We've proven analogous results about finite (co)limits and subobject classifiers.
However, the preservation of exponentials requires a different approach.
Indeed, the evaluation morphism is ony unique up to a (appriori) non-trivial identity.
(Nonetheless, one can prove that "is_a_left_adjoint" is a proposition, for bicategorical reasons)
Hence, we have to use the universal property of weak equivalences.

Approach:
Fix x₀ : C. We have to show that (F x₀ ⊗D -) : D → D is a left adjoint.

By assumption on C, (x₀ ⊗C -) : C -> C has a right adjoint, denoted R_C := [x₀, -] : C → C.

Lemma: RC(x ⊗C -) -| RC([x, -]) : RC(C) → RC(C) is an adjunction in Cat_univ.
Proof.
        Pseudofunctors preserve (internal) adjunctions, hence also RC : Cat -> Cat_univ.
Qed.

Lemma: The unique functor i := lift_η(F) : RC(C) → D is an equiv (iso).
Proof. Rezk completions are unique. Qed.

CLAIM: R_D := i^{-1} · #RC ( R_C · F ) · i,  is the right adjoint of (F x₀ ⊗D -).

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.
Import DispBicat.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrow.
Require Import UniMath.Bicategories.DisplayedBicats.DisplayedUniversalArrowOnCat.

Require Import UniMath.Bicategories.DisplayedBicats.Examples.CategoriesWithStructure.Exponentials.
Require Import UniMath.Bicategories.RezkCompletions.DisplayedRezkCompletions.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.BinProducts.

(* If we want to use lift_functor_along, etc. *)
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Local Open Scope cat.

Section WeakEquivalencesIntoUnivalentCatsCreatesExponentials.

  Context {C₀ : category}
    {P₀ : BinProducts C₀}
    (E₀ : Exponentials P₀).

  Context (LUR : left_universal_arrow univ_cats_to_cats).

  Let C₁ : univalent_category := (pr1 LUR C₀).
  Let η : functor C₀ C₁ := pr12 LUR C₀.
  Let αL := (pr1 (pr22 LUR C₀ C₁)).
  Let α : functor _ _ := right_adjoint αL.

  Context (P₁ : BinProducts C₁).
  Context (x₀ : C₀).

  Lemma weak_equiv_into_univ_preserves_exponentials
    : is_left_adjoint (constprod_functor1 P₁ (η x₀)).
  Proof.
  Admitted.

End WeakEquivalencesIntoUnivalentCatsCreatesExponentials.


Section WeakEquivalencesIntoUnivalentCatsCreatesExponentials.

  (* Require Import UniMath.CategoryTheory.Limits.Terminal.
  Require Import UniMath.CategoryTheory.Limits.BinProducts.
  Require Import UniMath.CategoryTheory.Limits.Preservation.
  Require Import UniMath.CategoryTheory.Adjunctions.Core.
  Require Import UniMath.CategoryTheory.exponentials.
  Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.BinProducts. *)

  Context {C₀ C₁ : category}
    {F : functor C₀ C₁} (F_weq : is_weak_equiv F)
    (C₁_univ : is_univalent C₁)
    {P₀ : BinProducts C₀}
    (E₀ : Exponentials P₀).

  Context (LUR : left_universal_arrow univ_cats_to_cats).

  (* Let P₁ := weak_equiv_into_univ_creates_binproducts C₁_univ F_weq P₀. *)
  Context (P₁ : BinProducts C₁).

  Lemma weak_equiv_into_univ_preserves_exponentials
    (x₀ : C₀)
    : is_left_adjoint (constprod_functor1 P₁ (pr111 (pr12 LUR _) x₀)).
  Proof.
    set (p := E₀ x₀ : is_left_adjoint _) ; simpl in p.

    unfold left_universal_arrow in LUR.
    simpl in LUR.

    Check right_adjoint (pr1 (pr22 LUR _ (_ ,, C₁_univ))).

  Lemma weak_equiv_into_univ_preserves_exponentials
    (x₀ : C₀)
    : is_left_adjoint (constprod_functor1 P₁ (F x₀)).
  Proof.
    set (p := E₀ x₀ : is_left_adjoint _) ; simpl in p.

    unfold left_universal_arrow in LUR.
    simpl in LUR.

    Check right_adjoint (pr1 (pr22 LUR _ (_ ,, C₁_univ))).



    (* Adjoints are preserved by any pseudofunctor.
     In particular, so does RC : Cat → Cat_univ, and the lift to Cat_{×}

   *)

    exists (lift_functor_along (_ ,, C₁_univ) _ (pr1 F_weq) (pr2 F_weq) (functor_composite (pr1 p) F)).
    simple refine ((_ ,, _) ,, _).
    - use (lift_nat_trans_along (_ ,, C₁_univ) _ (pr1 F_weq) (pr2 F_weq)).
      Check (lift_functor_along_comm (_ ,, C₁_univ) _ (pr1 F_weq) (pr2 F_weq) (functor_composite (pr1 p) F)).
      refine (nat_trans_comp _ _ _ _ (nat_z_iso_inv (nat_z_iso_functor_comp_assoc _ _ _))).
      Check pr112 p.

      Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.LiftedTensor.
      Check TransportedTensor C₁_univ (pr1 F_weq) (pr2 F_weq).


  Admitted.

  Lemma weak_equiv_into_univ_creates_exponentials
    : Exponentials P₁.
  Proof.
    intro x₁.
    use (factor_through_squash _ _ (pr1 F_weq x₁)).
    {
      (* use isaprop_is_left_adjoint. exact C₁_univ. *)
      admit.
    }
    intros [x₀ ix].
    apply (is_exponentiable_closed_under_iso P₁ ix).
    exact (weak_equiv_into_univ_preserves_exponentials x₀).
  Admitted.

  Lemma weak_equiv_into_univ_creates_exponentials'
    (Q₁ : BinProducts C₁)
    : Exponentials Q₁.
  Proof.
    exact (exponentials_independent P₁ Q₁ weak_equiv_into_univ_creates_exponentials).
  Defined.

End WeakEquivalencesIntoUnivalentCatsCreatesExponentials.
