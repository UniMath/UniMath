(***************************************************************************************

 Fiberwise limits in the displayed category of monomorphisms

 We construct fiberwise terminal objects and fiberwise binary products in the displayed
 category of monomorphisms. They are constructed the same way as fiberwise terminal
 objects and binary products are constructed in the displayed category of morphisms.

 The interesting aspect in the construction is the preservation of terminal objects and
 of binary products by the pullback functors. In the displayed category of morphisms, we
 can prove this quite directly. The pullback functors have a left adjoint, which is given
 by composition. As such, the pullback functors preserve limits since right adjoints
 preserve limits. However, if we want to use this argument for monomorphisms, then we need
 an additional assumption, namely that `C` is regular. The reason for that is that for
 monomorphisms the left adjoint of pullback should be given by the existential quantifier.
 This quantifier is constructed as a quotient of the sigma type, which is why we want the
 category to be regular.

 We can still prove the preservation of terminal objects and binary products by the
 pullback functors even without assuming that `C` is regular. For this, we use two facts:
 - The pullback functor for the displayed category of monomorphisms has the same on
   morphisms as the pullback functor for the displayed category of all morphisms.
 - The second of these two pullback functors preserves limits, because it has a left
   adjoint.

 Contents
 1. Fiberwise terminal objects
 2. Fiberwise binary products

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.Inclusion.

Local Open Scope cat.

Section CodomainStructure.
  Context {C : category}
          (HC : Pullbacks C).

  Let HD : cleaving (disp_mono_codomain C) := mono_cod_disp_cleaving HC.

  (** * 1. Fiberwise terminal objects *)
  Proposition isTerminal_mono_codomain_fib
              {x : C}
              (yf : C /m x)
              (H : is_z_isomorphism (pr21 yf))
    : isTerminal (C /m x) yf.
  Proof.
    pose (f := (_ ,, H) : z_iso _ _).
    intro zg.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use eq_mor_mono_cod_fib ;
         use (cancel_z_iso _ _ f) ;
         exact (pr2 φ₁ @ !(pr2 φ₂))).
    - use make_mono_cod_fib_mor.
      + exact (mono_cod_mor zg · inv_from_z_iso f).
      + abstract
          (rewrite assoc' ;
           refine (_ @ id_right _) ;
           apply maponpaths ;
           exact (z_iso_after_z_iso_inv f)).
  Defined.

  Definition mono_codomain_fib_terminal
             (x : C)
    : Terminal (C /m x).
  Proof.
    use make_Terminal.
    - exact (mono_cod_fib_id x).
    - use isTerminal_mono_codomain_fib.
      apply identity_is_z_iso.
  Defined.

  Proposition mono_codomain_fib_preserves_terminal
              {x y : C}
              (f : x --> y)
    : preserves_terminal (mono_cod_pb HC f).
  Proof.
    use preserves_terminal_if_preserves_chosen.
    {
      apply mono_codomain_fib_terminal.
    }
    unfold preserves_chosen_terminal.
    use isTerminal_mono_codomain_fib.
    use (is_z_iso_from_isTerminal_codomain (_ ,, _)).
    use (codomain_fib_preserves_terminal HC f (_ ,, _)).
    apply isTerminal_codomain_fib.
    apply identity_is_z_iso.
  Qed.

  Definition mono_codomain_fiberwise_terminal
    : fiberwise_terminal HD.
  Proof.
    split.
    - exact mono_codomain_fib_terminal.
    - exact (λ x y, mono_codomain_fib_preserves_terminal).
  Defined.

  (** * 2. Fiberwise binary products *)
  Section Prod.
    Context {x : C}
            {fy₁ fy₂ pz : C /m x}
            (π₁ : pz --> fy₁)
            (π₂ : pz --> fy₂).

    Let fy₁' : C / x := mono_cod_to_cod_fib _ fy₁.
    Let fy₂' : C / x := mono_cod_to_cod_fib _ fy₂.
    Let pz' : C / x := mono_cod_to_cod_fib _ pz.
    Let π₁' : pz' --> fy₁' := pr1 π₁.
    Let π₂' : pz' --> fy₂' := pr1 π₂.

    Context (H : isBinProduct (C / x) _ _ _ π₁' π₂').

    Let P : BinProduct _ _ _ := make_BinProduct _ _ _ _ _ _ H.

    Definition mono_codomain_fib_binproducts_prod
      : isBinProduct (C /m x) _ _ _ π₁ π₂.
    Proof.
      intros h φ ψ.
      use iscontraprop1.
      - abstract
          (use isaproptotal2 ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           intros ;
           apply locally_propositional_mono_cod_disp_cat).
      - simple refine ((_ ,, tt) ,, _ ,, _).
        + exact (BinProductArrow _ P (#(mono_cod_to_cod_fib _) φ) (#(mono_cod_to_cod_fib _) ψ)).
        + apply locally_propositional_mono_cod_disp_cat.
        + apply locally_propositional_mono_cod_disp_cat.
    Defined.
  End Prod.

  Definition mono_codomain_fib_binproducts
             (x : C)
    : BinProducts (C /m x).
  Proof.
    intros fy₁ fy₂.
    pose (fy₁' := mono_cod_dom fy₁ ,, pr1 (mono_cod_mor fy₁) : C / x).
    pose (fy₂' := mono_cod_dom fy₂ ,, pr1 (mono_cod_mor fy₂) : C / x).
    pose (P := codomain_fib_binproducts HC x fy₁' fy₂').
    use make_BinProduct.
    - use make_mono_cod_fib_ob.
      + exact (cod_dom P).
      + use (make_Monic _ (cod_mor P)).
        abstract
          (use isMonic_comp ; [ | apply (MonicisMonic _ (monic_of_mono_in_cat fy₁)) ] ;
           apply (MonicPullbackisMonic' _ _ (monic_of_mono_in_cat fy₂))).
    - exact (BinProductPr1 _ P ,, tt).
    - exact (BinProductPr2 _ P ,, tt).
    - apply mono_codomain_fib_binproducts_prod.
      apply isBinProduct_BinProduct.
  Defined.

  Proposition mono_codomain_fib_preserves_binproduct
              {x y : C}
              (f : x --> y)
    : preserves_binproduct (mono_cod_pb HC f).
  Proof.
    use preserves_binproduct_if_preserves_chosen.
    {
      apply mono_codomain_fib_binproducts.
    }
    intros m₁ m₂.
    pose (π₁ := BinProductPr1 (C /m y) (mono_codomain_fib_binproducts y m₁ m₂)).
    pose (π₂ := BinProductPr2 (C /m y) (mono_codomain_fib_binproducts y m₁ m₂)).
    pose (π₁' := #(mono_cod_to_cod_fib _) π₁).
    pose (π₂' := #(mono_cod_to_cod_fib _) π₂).
    Locate mono_cod_fiber_functor_on_mor.
    rewrite !mono_cod_fiber_functor_on_mor.
    use mono_codomain_fib_binproducts_prod.
    use codomain_fib_preserves_binproduct.
    apply isBinProduct_BinProduct.
  Qed.

  Definition mono_codomain_fiberwise_binproducts
    : fiberwise_binproducts HD.
  Proof.
    split.
    - exact mono_codomain_fib_binproducts.
    - exact (λ x y, mono_codomain_fib_preserves_binproduct).
  Defined.
End CodomainStructure.
