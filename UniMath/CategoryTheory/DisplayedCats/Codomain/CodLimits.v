(***************************************************************************************

 Fiberwise limits of codomain fibration

 In this file, we study limits of the fiber categories of the codomain fibration (more
 concretely, we study limits in slice categories). We look at terminal objects, binary
 products, and equalizers. For each of these:
 - We characterize limiting cones.
 - We give sufficient conditions for when the desired limits exist.
 - We show that pullback preserves these limits (this follows from the fact that the
   pullback functor is a right adjoint).

 Contents
 1. Preservation of limits by substitution
 2. Fiberwise terminal objects
 3. Fiberwise binary products
 4. Fiberwise equalizers

 ***************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.PullbackConstructions.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLeftAdjoint.

Local Open Scope cat.

Section CodomainStructure.
  Context {C : category}
          (HC : Pullbacks C).

  Let HD : cleaving (disp_codomain C) := disp_codomain_cleaving HC.

  (** * 1. Preservation of limits by substitution *)
  Proposition codomain_fib_preserves_terminal
              {x y : C}
              (f : x --> y)
    : preserves_terminal (cod_pb HC f).
  Proof.
    exact (right_adjoint_preserves_terminal _ (cod_fiber_sigma_adjunction HC f)).
  Qed.

  Proposition codomain_fib_preserves_binproduct
              {x y : C}
              (f : x --> y)
    : preserves_binproduct (cod_pb HC f).
  Proof.
    exact (right_adjoint_preserves_binproduct _ (cod_fiber_sigma_adjunction HC f)).
  Qed.

  Proposition codomain_fib_preserves_equalizer
              {x y : C}
              (f : x --> y)
    : preserves_equalizer (cod_pb HC f).
  Proof.
    exact (right_adjoint_preserves_equalizer _ (cod_fiber_sigma_adjunction HC f)).
  Qed.

  (** * 2. Fiberwise terminal objects *)
  Proposition isTerminal_codomain_fib
              {x : C}
              (yf : C/x)
              (H : is_z_isomorphism (pr2 yf))
    : isTerminal (C/x) yf.
  Proof.
    pose (f := (_ ,, H) : z_iso _ _).
    intro zg.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use eq_mor_cod_fib ;
         use (cancel_z_iso _ _ f) ;
         exact (pr2 φ₁ @ !(pr2 φ₂))).
    - use make_cod_fib_mor.
      + exact (cod_mor zg · inv_from_z_iso f).
      + abstract
          (rewrite assoc' ;
           refine (_ @ id_right _) ;
           apply maponpaths ;
           exact (z_iso_after_z_iso_inv f)).
  Defined.

  Proposition is_z_iso_from_isTerminal_codomain
              {x : C}
              (yf : C/x)
              (H : isTerminal (C/x) yf)
    : is_z_isomorphism (pr2 yf).
  Proof.
    pose (T := (_ ,, H) : Terminal _).
    pose (φ := TerminalArrow T (cod_fib_id x)).
    use make_is_z_isomorphism.
    - exact (dom_mor φ).
    - split.
      + abstract
          (use (maponpaths dom_mor (TerminalArrowEq (T := T) (_ · _ ,, _) (identity _))) ;
           cbn ;
           rewrite !assoc' ;
           apply maponpaths ;
           exact (mor_eq φ)).
      + abstract
          (exact (mor_eq φ)).
  Defined.

  Definition codomain_fib_terminal
             (x : C)
    : Terminal (C/x).
  Proof.
    use make_Terminal.
    - exact (cod_fib_id x).
    - use isTerminal_codomain_fib.
      apply identity_is_z_iso.
  Defined.

  Definition codomain_fiberwise_terminal
    : fiberwise_terminal HD.
  Proof.
    split.
    - exact codomain_fib_terminal.
    - exact (λ x y, codomain_fib_preserves_terminal).
  Defined.

  (** * 3. Fiberwise binary products *)
  Definition fib_isPullback
             {x : C}
             {fy₁ fy₂ gp : C/x}
             (π₁ : gp --> fy₁)
             (π₂ : gp --> fy₂)
    : dom_mor π₁ · cod_mor fy₁ = dom_mor π₂ · cod_mor fy₂.
  Proof.
    exact (pr2 π₁ @ !(pr2 π₂)).
  Qed.

  Section ToIsProd.
    Context {x : C}
            {fy₁ fy₂ gp : C/x}
            {π₁ : gp --> fy₁}
            {π₂ : gp --> fy₂}
            (H : isPullback (fib_isPullback π₁ π₂))
            {wh : C/x}
            (φq : wh --> fy₁)
            (ψr : wh --> fy₂).

    Let P : Pullback (cod_mor fy₁) (cod_mor fy₂)
      := make_Pullback _ H.

    Proposition isPullback_to_isBinproduct_cod_fib_unique
      : isaprop (∑ (fg : wh --> gp), fg · π₁ = φq × fg · π₂ = ψr).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use eq_mor_cod_fib.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback P)).
      - pose (s := maponpaths dom_mor (pr12 ζ₁ @ !(pr12 ζ₂))).
        rewrite !comp_in_cod_fib in s.
        exact s.
      - pose (s := maponpaths dom_mor (pr22 ζ₁ @ !(pr22 ζ₂))).
        rewrite !comp_in_cod_fib in s.
        exact s.
    Qed.

    Definition isPullback_to_isBinproduct_cod_fib_mor
      : wh --> gp.
    Proof.
      use make_cod_fib_mor.
      - use (PullbackArrow P).
        + exact (dom_mor φq).
        + exact (dom_mor ψr).
        + abstract
            (exact (mor_eq φq @ !(mor_eq ψr))).
      - abstract
          (cbn ;
           pose (mor_eq π₁) as s ;
           cbn in s ;
           rewrite <- s ;
           rewrite !assoc ;
           rewrite (PullbackArrow_PullbackPr1 P) ;
           exact (mor_eq φq)).
    Defined.

    Proposition isPullback_to_isBinproduct_cod_fib_pr1
      : isPullback_to_isBinproduct_cod_fib_mor · π₁ = φq.
    Proof.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      apply (PullbackArrow_PullbackPr1 P).
    Qed.

    Proposition isPullback_to_isBinproduct_cod_fib_pr2
      : isPullback_to_isBinproduct_cod_fib_mor · π₂ = ψr.
    Proof.
      use eq_mor_cod_fib.
      rewrite comp_in_cod_fib.
      apply (PullbackArrow_PullbackPr2 P).
    Qed.
  End ToIsProd.

  Definition isPullback_to_isBinProduct_cod_fib
             {x : C}
             {fy₁ fy₂ gp : C/x}
             (π₁ : gp --> fy₁)
             (π₂ : gp --> fy₂)
             (H : isPullback (fib_isPullback π₁ π₂))
    : isBinProduct _ fy₁ fy₂ gp π₁ π₂.
  Proof.
    intros wh φq ψr.
    use iscontraprop1.
    - apply (isPullback_to_isBinproduct_cod_fib_unique H).
    - simple refine (_ ,, _ ,, _).
      + exact (isPullback_to_isBinproduct_cod_fib_mor H φq ψr).
      + apply isPullback_to_isBinproduct_cod_fib_pr1.
      + apply isPullback_to_isBinproduct_cod_fib_pr2.
  Defined.

  Section ToIsPb.
    Context {x : C}
            {fy₁ fy₂ gp : C/x}
            {π₁ : gp --> fy₁}
            {π₂ : gp --> fy₂}
            (H : isBinProduct _ fy₁ fy₂ gp π₁ π₂)
            {w : C}
            (φ : w --> cod_dom fy₁)
            (ψ : w --> cod_dom fy₂)
            (s : φ · cod_mor fy₁ = ψ · cod_mor fy₂).

    Let P : BinProduct _ _ _ := make_BinProduct _ _ _ _ _ _ H.

    Let wh : C/x := make_cod_fib_ob (φ · cod_mor fy₁).

    Local Definition φq
      : wh --> fy₁.
    Proof.
      use make_cod_fib_mor.
      - exact φ.
      - abstract
          (cbn ;
           apply idpath).
    Defined.

    Local Definition ψr
      : wh --> fy₂.
    Proof.
      use make_cod_fib_mor.
      - exact ψ.
      - abstract
          (cbn ;
           rewrite s ;
           apply idpath).
    Defined.

    Proposition isBinProduct_to_isPullback_cod_fib_unique
      : isaprop (∑ (hk : w --> pr1 gp), hk · pr1 π₁ = φ × hk · pr1 π₂ = ψ).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use (maponpaths
             dom_mor
             (BinProductArrowsEq _ _ _ P wh (_ ,, _) (_ ,, _) _ _)).
      - cbn.
        etrans.
        {
          apply maponpaths.
          exact (!(mor_eq π₁)).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (pr12 ζ₁).
        }
        rewrite id_right.
        apply idpath.
      - cbn.
        etrans.
        {
          apply maponpaths.
          exact (!(mor_eq π₁)).
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          exact (pr12 ζ₂).
        }
        rewrite id_right.
        apply idpath.
      - use eq_mor_cod_fib.
        refine (comp_in_cod_fib _ _ @ _ @ !(comp_in_cod_fib _ _)).
        cbn.
        exact (pr12 ζ₁ @ !(pr12 ζ₂)).
      - use eq_mor_cod_fib.
        refine (comp_in_cod_fib _ _ @ _ @ !(comp_in_cod_fib _ _)).
        cbn.
        exact (pr22 ζ₁ @ !(pr22 ζ₂)).
    Qed.

    Definition isBinProduct_to_isPullback_cod_fib_mor
      : cod_dom wh --> cod_dom gp
      := dom_mor (BinProductArrow _ P φq ψr).

    Proposition isBinProduct_to_isPullback_cod_fib_pr1
      : isBinProduct_to_isPullback_cod_fib_mor · dom_mor π₁ = φ.
    Proof.
      refine (_ @ maponpaths dom_mor (BinProductPr1Commutes _ _ _ P _ φq ψr)).
      rewrite comp_in_cod_fib.
      apply idpath.
    Qed.

    Proposition isBinProduct_to_isPullback_cod_fib_pr2
      : isBinProduct_to_isPullback_cod_fib_mor · dom_mor π₂ = ψ.
    Proof.
      refine (_ @ maponpaths dom_mor (BinProductPr2Commutes _ _ _ P _ φq ψr)).
      rewrite comp_in_cod_fib.
      apply idpath.
    Qed.
  End ToIsPb.

  Definition isBinProduct_to_isPullback_cod_fib
             {x : C}
             {fy₁ fy₂ gp : C/x}
             (π₁ : gp --> fy₁)
             (π₂ : gp --> fy₂)
             (H : isBinProduct _ fy₁ fy₂ gp π₁ π₂)
    : isPullback (fib_isPullback π₁ π₂).
  Proof.
    intros w φ ψ s.
    use iscontraprop1.
    - apply (isBinProduct_to_isPullback_cod_fib_unique H).
    - simple refine (_ ,, _ ,, _).
      + exact (isBinProduct_to_isPullback_cod_fib_mor H φ ψ s).
      + apply isBinProduct_to_isPullback_cod_fib_pr1.
      + apply isBinProduct_to_isPullback_cod_fib_pr2.
  Defined.

  Definition codomain_fib_binproducts
             (x : C)
    : BinProducts (C/x).
  Proof.
    intros fy₁ fy₂.
    pose (P := HC _ _ _ (cod_mor fy₁) (cod_mor fy₂)).
    use make_BinProduct.
    - refine (PullbackObject P ,, _).
      exact (PullbackPr1 P · cod_mor fy₁).
    - refine (PullbackPr1 P ,, _).
      abstract
        (cbn ;
         rewrite id_right ;
         apply idpath).
    - refine (PullbackPr2 P ,, _).
      abstract
        (cbn ;
         rewrite PullbackSqrCommutes ;
         rewrite id_right ;
         apply idpath).
    - use isPullback_to_isBinProduct_cod_fib.
      apply P.
  Defined.

  Definition codomain_fiberwise_binproducts
    : fiberwise_binproducts HD.
  Proof.
    split.
    - exact codomain_fib_binproducts.
    - exact (λ x y, codomain_fib_preserves_binproduct).
  Defined.

  (** * 4. Fiberwise equalizers *)
  Section EqualizerCodFib.
    Context {x : C}
            {ee fy₁ fy₂ : C/x}
            (φp ψq : fy₁ --> fy₂)
            (ρr : ee --> fy₁)
            (s : ρr · φp = ρr · ψq).

    Let y₁ : C := cod_dom fy₁.
    Let f₁ : y₁ --> x := cod_mor fy₁.

    Let y₂ : C := cod_dom fy₂.
    Let f₂ : y₂ --> x := cod_mor fy₂.

    Let e : C := cod_dom ee.
    Let m : e --> x := cod_mor ee.

    Let φ : y₁ --> y₂ := dom_mor φp.
    Let ψ : y₁ --> y₂ := dom_mor ψq.
    Let ρ : e --> y₁ := dom_mor ρr.

    Context (s' : ρ · φ = ρ · ψ).

    Section ToEqCodFib.
      Context (H : isEqualizer φ ψ ρ s')
              {wh : C/x}
              (τp : wh --> fy₁)
              (p : τp · φp = τp · ψq).

      Let E : Equalizer φ ψ := make_Equalizer _ _ _ _ H.

      Let w : C := cod_dom wh.
      Let h : w --> x := cod_mor wh.
      Let τ : w --> y₁ := dom_mor τp.

      Proposition to_isEqualizer_cod_fib_unique
        : isaprop (∑ (ζ : wh --> ee), ζ · ρr = τp).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use eq_mor_cod_fib.
        use (EqualizerInsEq E).
        refine (_ @ maponpaths dom_mor (pr2 ζ₁ @ !(pr2 ζ₂)) @ _).
        - rewrite comp_in_cod_fib.
          apply idpath.
        - rewrite comp_in_cod_fib.
          apply idpath.
      Qed.

      Definition to_isEqualizer_cod_fib_mor
        : wh --> ee.
      Proof.
        use make_cod_fib_mor.
        - use (EqualizerIn E _ τ).
          abstract
            (refine (_ @ maponpaths dom_mor p @ _) ;
             rewrite comp_in_cod_fib ;
             apply idpath).
        - abstract
            (rewrite <- (mor_eq ρr) ;
             rewrite !assoc ;
             etrans ;
             [ apply maponpaths_2 ;
               apply (EqualizerCommutes E)
             | ] ;
             exact (mor_eq τp)).
      Defined.

      Proposition to_isEqualizer_cod_fib_comm
        : to_isEqualizer_cod_fib_mor · ρr = τp.
      Proof.
        use eq_mor_cod_fib.
        rewrite comp_in_cod_fib.
        apply (EqualizerCommutes E).
      Qed.
    End ToEqCodFib.

    Definition to_isEqualizer_cod_fib
               (H : isEqualizer φ ψ ρ s')
      : isEqualizer φp ψq ρr s.
    Proof.
      intros wh τp p.
      use iscontraprop1.
      - exact (to_isEqualizer_cod_fib_unique H τp).
      - simple refine (_ ,, _).
        + exact (to_isEqualizer_cod_fib_mor H τp p).
        + exact (to_isEqualizer_cod_fib_comm H τp p).
    Defined.

    Section FromEqCodFib.
      Context (H : isEqualizer φp ψq ρr s)
              {w : C}
              (h : w --> y₁)
              (p : h · φ = h · ψ).

      Let E : Equalizer φp ψq := make_Equalizer _ _ _ _ H.

      Local Definition w' : C/x
        := make_cod_fib_ob (h · f₁).

      Local Definition h'
        : w' --> fy₁.
      Proof.
        use make_cod_fib_mor.
        - exact h.
        - abstract
            (cbn ;
             apply idpath).
      Defined.

      Local Lemma p'
        : h' · φp = h' · ψq.
      Proof.
        use eq_mor_cod_fib.
        rewrite !comp_in_cod_fib.
        exact p.
      Qed.

      Proposition from_isEqualizer_cod_fib_unique
        : isaprop (∑ (ζ : w --> e), ζ · ρ = h).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        assert (H₁ : pr1 ζ₁ · cod_mor ee = h · f₁).
        {
          etrans.
          {
            apply maponpaths.
            exact (!(mor_eq ρr)).
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (pr2 ζ₁).
          }
          apply idpath.
        }
        assert (H₂ : pr1 ζ₂ · cod_mor ee = h · f₁).
        {
          etrans.
          {
            apply maponpaths.
            exact (!(mor_eq ρr)).
          }
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (pr2 ζ₂).
          }
          apply idpath.
        }
        pose (ζ₁' := @make_cod_fib_mor _ _ w' ee (pr1 ζ₁) H₁).
        pose (ζ₂' := @make_cod_fib_mor _ _ w' ee (pr1 ζ₂) H₂).
        refine (maponpaths pr1 (EqualizerInsEq E ζ₁' ζ₂' _)).
        use eq_mor_cod_fib.
        rewrite !comp_in_cod_fib.
        exact (pr2 ζ₁ @ !(pr2 ζ₂)).
      Qed.

      Definition from_isEqualizer_cod_fib_mor
        : w --> e
        := pr1 (EqualizerIn E w' h' p').

      Proposition from_isEqualizer_cod_fib_comm
        : from_isEqualizer_cod_fib_mor · ρ = h.
      Proof.
        refine (_ @ maponpaths dom_mor (EqualizerCommutes E w' h' p')).
        rewrite comp_in_cod_fib.
        apply idpath.
      Qed.
    End FromEqCodFib.

    Definition from_isEqualizer_cod_fib
               (H : isEqualizer φp ψq ρr s)
      : isEqualizer φ ψ ρ s'.
    Proof.
      intros w h p.
      use iscontraprop1.
      - apply (from_isEqualizer_cod_fib_unique H).
      - simple refine (_ ,, _).
        + exact (from_isEqualizer_cod_fib_mor H h p).
        + exact (from_isEqualizer_cod_fib_comm H h p).
    Defined.
  End EqualizerCodFib.

  Definition codomain_fib_equalizer
             (H : Equalizers C)
             (x : C)
    : Equalizers (C/x).
  Proof.
    intros fy₁ fy₂ φp ψq.
    pose (E := H (cod_dom fy₁) (cod_dom fy₂) (dom_mor φp) (dom_mor ψq)).
    use make_Equalizer.
    - refine (EqualizerObject E ,, _).
      exact (EqualizerArrow E · cod_mor fy₁).
    - refine (EqualizerArrow E ,, _).
      abstract
        (cbn ;
         rewrite id_right ;
         apply idpath).
    - abstract
        (use eq_mor_cod_fib ;
         rewrite !comp_in_cod_fib ;
         cbn ;
         apply EqualizerEqAr).
    - use to_isEqualizer_cod_fib.
      + apply EqualizerEqAr.
      + exact (isEqualizer_Equalizer E).
  Defined.

  Definition codomain_fiberwise_equalizers_from_equalizers
             (H : Equalizers C)
    : fiberwise_equalizers HD.
  Proof.
    split.
    - exact (codomain_fib_equalizer H).
    - exact (λ x y, codomain_fib_preserves_equalizer).
  Defined.

  Definition codomain_fiberwise_equalizers
             (T : Terminal C)
    : fiberwise_equalizers HD.
  Proof.
    use codomain_fiberwise_equalizers_from_equalizers.
    use equalizers_from_pullbacks_terminal.
    - exact HC.
    - exact T.
  Defined.
End CodomainStructure.
