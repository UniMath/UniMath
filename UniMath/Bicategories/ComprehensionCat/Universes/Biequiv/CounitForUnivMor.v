(**

 Categories with universes versus comprehension categories with universes: the counit

 Our goal is to establish a biequivalence between the bicategories of univalent categories
 with finite limits and a universe type and the bicategory of univalent full DFL comprehension
 categories that have a universe.

 The mathematical development of the counit is rather straightforward. However, there are
 some technical issues, namely keeping the memory consumption and the running time acceptable.
 Tricks to decrease the running time are documented in the file, and the development of the
 pointwise morphism and the naturality squares are split up into separate files. In this file,
 we contruct the pointwise morphism of the counit.

 Contents
 1. Coherence for the universe object
 2. Calculational lemmas
 3. Preservation of the associated type
 4. Coherence
 5. Preservation of the universe type

                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.
Require Import UniMath.Bicategories.ComprehensionCat.FinLimToCompCatLemmas.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Unit.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.Counit.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivActions.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivCell.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUnivIdent.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.ToCatFinLimUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

Section CounitMor.
  Context {C : dfl_full_comp_cat}
          (u : ty ([] : C)).

  Let Cu : comp_cat_with_ob := pr11 C ,, u.
  Let CCu : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C ,, dfl_full_comp_cat_to_finlim_ob u.

  Context (el : comp_cat_univ_type Cu).

  (** * 1. Coherence for the universe object *)
  Definition finlim_dfl_comp_cat_counit_ob
    : z_iso_disp
        (comp_cat_functor_empty_context_z_iso
           (finlim_dfl_comp_cat_counit_mor_comp_cat C))
        (comp_cat_type_functor
           (finlim_dfl_comp_cat_counit_mor_terminal_disp_cat C)
           []
           u)
        (finlim_to_comp_cat_universe_ob CCu).
  Proof.
    use make_z_iso_disp.
    - simple refine (_ ,, _).
      + apply identity.
      + abstract
          (apply TerminalArrowEq).
    - use is_z_iso_disp_codomain'.
      apply is_z_isomorphism_identity.
  Defined.

  Let F
    : comp_cat_functor_ob
        Cu
        (finlim_to_comp_cat_with_ob CCu)
    := pr11 (finlim_dfl_comp_cat_counit C) ,, finlim_dfl_comp_cat_counit_ob.

  (** * 2. Calculational lemmas *)

  (**
     The following lemmas simplify certain standard combinators of comprehension
     categories. The lemmas are chosen so that they are usable for calculations
     regarding the counit.
   *)
  Proposition comp_cat_functor_subst_ty_counit_pr1
              {x y : C}
              (s : x --> y)
              (A : ty y)
    : dom_mor (comp_cat_functor_subst_ty F s A : _ -->[ _ ] _)
      · PullbackPr1 _
      =
      comprehension_functor_mor (comp_cat_comprehension C) (comp_cat_subst A s).
  Proof.
    etrans.
    {
      exact (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _) _ _ _ _).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition comp_cat_functor_subst_ty_counit_pr2
              {x y : C}
              (s : x --> y)
              (A : ty y)
    : dom_mor (comp_cat_functor_subst_ty F s A : _ -->[ _ ] _)
      · PullbackPr2 _
      =
      π _.
  Proof.
    exact (mor_eq (comp_cat_functor_subst_ty F s A : _ -->[ _ ] _)).
  Qed.

  Proposition subst_ty_eq_disp_iso_counit_pr1
              {Γ Δ : finlim_to_comp_cat (dfl_full_comp_cat_to_finlim C)}
              {s₁ s₂ : Γ --> Δ}
              (p : s₁ = s₂)
              (A : ty Δ)
    : pr11 (subst_ty_eq_disp_iso A p)
      · PullbackPr1 _
      =
      PullbackPr1 _.
  Proof.
    pose (maponpaths
            (comprehension_functor_mor (comp_cat_comprehension _))
            (subst_ty_eq_disp_iso_comm p A))
      as q.
    rewrite comprehension_functor_mor_transportf in q.
    rewrite comprehension_functor_mor_comp in q.
    exact q.
  Qed.

  Proposition subst_ty_eq_disp_iso_counit_pr2
              {Γ Δ : finlim_to_comp_cat (dfl_full_comp_cat_to_finlim C)}
              {s₁ s₂ : Γ --> Δ}
              (p : s₁ = s₂)
              (A : ty Δ)
    : dom_mor (subst_ty_eq_disp_iso A p : _ -->[ _ ] _)
      · PullbackPr2 _
      =
      PullbackPr2 _.
  Proof.
    exact (mor_eq (subst_ty_eq_disp_iso A p : _ -->[ _ ] _)).
  Qed.

  Proposition subst_ty_iso_counit_pr1
              {Γ Δ Δ' : finlim_to_comp_cat (dfl_full_comp_cat_to_finlim C)}
              (s : Γ --> Δ)
              {A : ty Δ}
              {B : ty Δ'}
              {f : z_iso Δ Δ'}
              (ff : z_iso_disp f A B)
    : pr11 (subst_ty_iso s f ff)
      · PullbackPr1 _
      =
      PullbackPr1 _ · pr11 ff.
  Proof.
    etrans.
    {
      exact (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _) _ _ _ _).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition subst_ty_iso_counit_pr2
              {Γ Δ Δ' : finlim_to_comp_cat (dfl_full_comp_cat_to_finlim C)}
              (s : Γ --> Δ)
              {A : ty Δ}
              {B : ty Δ'}
              {f : z_iso Δ Δ'}
              (ff : z_iso_disp f A B)
    : dom_mor (subst_ty_iso s f ff : _ -->[ _ ] _)
      · PullbackPr2 _
      =
      PullbackPr2 _.
  Proof.
    exact (mor_eq (subst_ty_iso s f ff : _ -->[ _ ] _)).
  Qed.

  Proposition comp_cat_functor_coerce_counit
              {Γ : C}
              {A B : ty Γ}
              (f : A <: B)
    : dom_mor (comp_cat_functor_coerce F f)
      =
      comp_cat_comp_mor f.
  Proof.
    apply idpath.
  Qed.

  Proposition coerce_subst_ty_counit_pr1
              {Γ Δ : finlim_to_comp_cat (dfl_full_comp_cat_to_finlim C)}
              (s : Γ --> Δ)
              {A B : ty Δ}
              (f : A <: B)
    : dom_mor (coerce_subst_ty (#F s) f) · PullbackPr1 _
      =
      PullbackPr1 _ · dom_mor f.
  Proof.
    etrans.
    {
      (**
         The following three lines reduce the compilation time (for some reason).
       *)
      apply maponpaths_2.
      simpl.
      apply idpath.
    }
    etrans.
    {
      exact (PullbackArrow_PullbackPr1
               (pullbacks_univ_cat_with_finlim
                  (dfl_full_comp_cat_to_finlim C)
                  _ _ _ _ _)
               _ _ _ _).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition coerce_subst_ty_counit_pr2
              {Γ Δ : finlim_to_comp_cat (dfl_full_comp_cat_to_finlim C)}
              (s : Γ --> Δ)
              {A B : ty Δ}
              (f : A <: B)
    : dom_mor (coerce_subst_ty (#F s) f) · PullbackPr2 _
      =
      PullbackPr2 _.
  Proof.
    exact (mor_eq (coerce_subst_ty (#F s) f)).
  Qed.

  Proposition comp_cat_functor_subst_ty_coe_counit_pr1
              {Γ Δ : C}
              (s : Γ --> Δ)
              (A : ty Δ)
    : dom_mor (comp_cat_functor_subst_ty_coe F s A) · PullbackPr1 _
      =
      comprehension_functor_mor _ (comp_cat_subst A s).
  Proof.
    etrans.
    {
      exact (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _) _ _ _ _).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition comp_cat_functor_subst_ty_coe_counit_pr2
              {Γ Δ : C}
              (s : Γ --> Δ)
              (A : ty Δ)
    : dom_mor (comp_cat_functor_subst_ty_coe F s A) · PullbackPr2 _
      =
      π _.
  Proof.
    exact (mor_eq (comp_cat_functor_subst_ty_coe F s A)).
  Qed.

  Proposition comp_cat_univ_el_stable_counit
              {Γ Δ : finlim_to_comp_cat_with_ob CCu}
              (s : Γ --> Δ)
              (t : tm Δ (comp_cat_univ Δ))
    : ∑ p,
      dom_mor
        (comp_cat_univ_el_stable
           (finlim_to_comp_cat_univ_type
              (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el))
           s
           t
          : _ --> _)
      =
      finlim_to_comp_cat_stable_el_map_mor_mor
        (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el)
        s
        _
      · cat_el_map_el_eq _ p.
  Proof.
    eexists.
    apply idpath.
  Qed.

  Lemma comp_cat_el_map_on_eq_counit_eq
        {Γ : finlim_to_comp_cat_with_ob CCu}
        {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
        (p : t₁ = t₂)
    : dfl_full_comp_cat_mor_to_tm u (finlim_univ_tm_to_mor t₁)
      =
      dfl_full_comp_cat_mor_to_tm u (finlim_univ_tm_to_mor t₂).
  Proof.
    do 2 apply maponpaths.
    exact p.
  Qed.

  Proposition comp_cat_el_map_on_eq_counit
              {Γ : finlim_to_comp_cat_with_ob CCu}
              {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
              (p : t₁ = t₂)
    : dom_mor (comp_cat_el_map_on_eq
                 (finlim_to_comp_cat_el_map
                    (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el))
                 p)
      =
      comprehension_functor_mor
        (comp_cat_comprehension C)
        (comp_cat_el_map_on_eq el (comp_cat_el_map_on_eq_counit_eq p)).
  Proof.
    induction p.
    simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (comp_cat_el_map_on_idpath el).
    }
    apply comprehension_functor_mor_id.
  Qed.

  Proposition cat_el_map_el_eq_counit
              {Γ : CCu}
              {t₁ t₂ : Γ --> dfl_full_comp_cat_to_finlim_ob u}
              (p : t₁ = t₂)
    : (cat_el_map_el_eq (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el) p : _ --> _)
      =
      comprehension_functor_mor
        (comp_cat_comprehension C)
        (comp_cat_el_map_on_eq
           el
           (maponpaths (dfl_full_comp_cat_mor_to_tm u) p)).
  Proof.
    induction p.
    simpl.
    refine (!_).
    apply comprehension_functor_mor_id.
  Qed.

  Proposition functor_comp_cat_on_univ_counit
              (Γ : C)
    : pr1 (functor_comp_cat_on_univ F Γ)
      =
      dom_mor (comp_cat_functor_subst_ty F _ (ob_of_comp_cat_ob Cu) : _ -->[ _ ] _)
      · dom_mor (subst_ty_iso _ _ (ob_of_functor_comp_cat_ob F) : _ -->[ _ ] _)
      · pr11 (subst_ty_eq_disp_iso
                (ob_of_comp_cat_ob (finlim_to_comp_cat_with_ob CCu))
                (functor_comp_cat_on_univ_z_iso_terminal_eq F Γ)).
  Proof.
    etrans.
    {
      apply transportf_cod_disp.
    }
    rewrite assoc'.
    unfold dom_mor.
    apply idpath.
  Qed.

  (** 3. Preservation of the associated type *)
  Proposition finlim_dfl_comp_cat_counit_preserves_el_eq
              {Γ : Cu}
              (t : tm Γ (comp_cat_univ Γ))
    : t
      =
      dfl_full_comp_cat_mor_to_tm
        u
        (finlim_univ_tm_to_mor
           (comp_cat_functor_tm (finlim_dfl_comp_cat_counit_mor_comp_cat C) t
            ↑ functor_comp_cat_on_univ F Γ)).
  Proof.
    use eq_comp_cat_tm.
    simpl.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback _ _))).
    - rewrite PullbackArrow_PullbackPr1.
      unfold finlim_univ_tm_to_mor.
      simpl.
      rewrite !assoc'.
      apply maponpaths.
      refine (!_).
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply id_left.
      }
      etrans.
      {
        apply maponpaths_2.
        unfold comp_cat_comp_mor.
        simpl.
        unfold finlim_comprehension.
        simpl.
        unfold comprehension_functor_mor.
        simpl.
        apply idpath.
      }

      etrans.
      {
        apply maponpaths_2.
        exact (functor_comp_cat_on_univ_counit Γ).
      }
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        apply subst_ty_eq_disp_iso_counit_pr1.
      }
      etrans.
      {
        apply maponpaths.
        exact (subst_ty_iso_counit_pr1 (#F (TerminalArrow [] Γ)) (ob_of_functor_comp_cat_ob F)).
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply comp_cat_functor_subst_ty_counit_pr1.
      }
      simpl.
      apply id_right.
    - rewrite PullbackArrow_PullbackPr2.
      exact (comp_cat_tm_eq t).
  Qed.

  Definition finlim_dfl_comp_cat_counit_preserves_el
    : comp_cat_functor_preserves_el
        F
        el
        (finlim_to_comp_cat_univ_type
           (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el)).
  Proof.
    intros Γ t.
    exact (comp_cat_comp_fiber_z_iso_fib
             (comp_cat_el_map_on_eq_iso
                el
                (finlim_dfl_comp_cat_counit_preserves_el_eq t))).
  Defined.

  (** 4. Coherence *)
  Proposition finlim_dfl_comp_cat_counit_preserves_stable_el
    : comp_cat_functor_preserves_stable_el
        el
        (finlim_to_comp_cat_univ_type
           (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el))
        finlim_dfl_comp_cat_counit_preserves_el.
  Proof.
    intros Γ Δ s t.
    use eq_mor_cod_fib.
    etrans.
    {
      apply comp_in_cod_fib.
    }
    etrans.
    {
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    refine (!_).
    etrans.
    {
      apply comp_in_cod_fib.
    }
    etrans.
    {
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    refine (!_).
    rewrite assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      exact (pr2 (comp_cat_univ_el_stable_counit _ _)).
    }
    rewrite !assoc.
    use z_iso_inv_to_right.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply maponpaths.
      exact (dom_mor_comp_cat_comp_fiber_z_iso_fib
               (comp_cat_el_map_on_eq_iso
                  el
                  _)).
    }
    etrans.
    {
      do 3 apply maponpaths_2.
      apply comp_cat_functor_coerce_counit.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (!_).
      apply (comp_cat_comp_mor_comp (pr1 (comp_cat_univ_el_stable el s t))).
    }
    etrans.
    {
      apply maponpaths.
      use cat_el_map_el_eq_inv.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      exact (comp_cat_el_map_on_eq_counit
               (comp_cat_functor_preserves_stable_el_path F s t)).
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (comprehension_functor_mor_comp (comp_cat_comprehension C)).
    }
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_el_eq_counit.
    }
    etrans.
    {
      refine (!_).
      apply (comprehension_functor_mor_comp (comp_cat_comprehension C)).
    }
    refine (!_).
    use (MorphismsIntoPullbackEqual
           (isPullback_Pullback
              (cat_stable_el_map_pb
                 (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el)
                 _
                 _))).
    - etrans.
      {
        rewrite !assoc'.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply (PullbackArrow_PullbackPr1
                 (cat_stable_el_map_pb
                    (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el)
                    _
                    _)).
      }
      etrans.
      {
        apply maponpaths.
        apply coerce_subst_ty_counit_pr1.
      }
      etrans.
      {
        apply (assoc (C := C) _ _).
      }
      etrans.
      {
        apply maponpaths_2.
        apply comp_cat_functor_subst_ty_coe_counit_pr1.
      }
      etrans.
      {
        apply maponpaths.
        exact (dom_mor_comp_cat_comp_fiber_z_iso_fib
               (comp_cat_el_map_on_eq_iso el _)).
      }
      etrans.
      {
        refine (!_).
        apply (comprehension_functor_mor_comp (comp_cat_comprehension C)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        unfold compose.
        simpl.
        rewrite !mor_disp_transportf_postwhisker.
        apply idpath.
      }
      rewrite comprehension_functor_mor_transportf.
      rewrite assoc_disp_var.
      rewrite comprehension_functor_mor_transportf.
      rewrite assoc_disp_var.
      rewrite comprehension_functor_mor_transportf.
      rewrite (comp_cat_el_map_on_disp_concat el).
      rewrite !mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        apply (comp_cat_el_map_on_disp_concat el).
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        refine (!_).
        apply (comprehension_functor_mor_comp (comp_cat_comprehension C)).
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        rewrite !assoc_disp.
        unfold transportb.
        rewrite comprehension_functor_mor_transportf.
        rewrite mor_disp_transportf_postwhisker.
        rewrite comprehension_functor_mor_transportf.
        apply maponpaths.
        do 2 apply maponpaths_2.
        rewrite assoc_disp_var.
        do 2 apply maponpaths.
        apply (comp_cat_el_map_on_disp_concat el).
      }
      rewrite !mor_disp_transportf_postwhisker.
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        apply maponpaths.
        do 2 apply maponpaths_2.
        use (comp_cat_univ_el_stable_natural_disp_alt el).
        apply finlim_dfl_comp_cat_counit_preserves_el_eq.
      }
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        rewrite assoc_disp_var.
        do 2 apply maponpaths.
        exact (inv_mor_after_z_iso_disp
                 (z_iso_disp_from_z_iso_fiber
                    _ _ _ _
                    (comp_cat_univ_el_stable el _ _))).
      }
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite comprehension_functor_mor_transportf.
      rewrite id_right_disp.
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        apply maponpaths.
        apply (comp_cat_subst_natural_alt el).
      }
      unfold transportb.
      rewrite comprehension_functor_mor_transportf.
      apply idpath.
    - etrans.
      {
        rewrite !assoc'.
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply (PullbackArrow_PullbackPr2
                 (cat_stable_el_map_pb
                    (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el)
                    _
                    _)).
      }
      etrans.
      {
        apply maponpaths.
        apply coerce_subst_ty_counit_pr2.
      }
      etrans.
      {
        apply comp_cat_functor_subst_ty_coe_counit_pr2.
      }
      refine (!_).
      etrans.
      {
        apply (comprehension_functor_mor_comm (comp_cat_comprehension C)).
      }
      rewrite !id_right.
      apply idpath.
  Qed.

  (** * 5. Preservation of the universe type *)
  Definition finlim_dfl_comp_cat_counit_preserves_univ_type
    : comp_cat_functor_preserves_univ_type
        F
        el
        (finlim_to_comp_cat_univ_type
           (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u el)).
  Proof.
    use make_comp_cat_functor_preserves_univ_type.
    - exact finlim_dfl_comp_cat_counit_preserves_el.
    - exact finlim_dfl_comp_cat_counit_preserves_stable_el.
  Defined.
End CounitMor.
