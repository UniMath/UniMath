(**

 Categories with universes versus comprehension categories with universes: the counit

 Our goal is to establish a biequivalence between the bicategories of univalent categories
 with finite limits and a universe type and the bicategory of univalent full DFL comprehension
 categories that have a universe.

 The mathematical development of the counit is rather straightforward. However, there are
 some technical issues, namely keeping the memory consumption and the running time acceptable.
 Tricks to decrease the running time are documented in the file, and the development of the
 pointwise morphism and the naturality squares are split up into separate files. In this file,
 we contruct the naturality square of the counit.

 Contents
 1. Coherence for the universe object
 2. Calculational lemmas
 3. Coherence for the associated type map
                                                                                            *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
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
Require Import UniMath.Bicategories.ComprehensionCat.Universes.Biequiv.CounitForUnivMor.

Local Open Scope cat.
Local Open Scope comp_cat.

Section CounitCell.
  Context {C₁ C₂ : dfl_full_comp_cat}
          (F : dfl_full_comp_cat_functor C₁ C₂)
          {u₁ : ty ([] : C₁)}
          {u₂ : ty ([] : C₂)}.

  Let Cu₁ : comp_cat_with_ob := pr11 C₁ ,, u₁.
  Let Cu₂ : comp_cat_with_ob := pr11 C₂ ,, u₂.
  Let CCu₁ : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C₁ ,, dfl_full_comp_cat_to_finlim_ob u₁.
  Let CCu₂ : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C₂ ,, dfl_full_comp_cat_to_finlim_ob u₂.
  Let FCCu₁ : comp_cat_with_ob
    := finlim_to_comp_cat_with_ob CCu₁.
  Let FCCu₂ : comp_cat_with_ob
    := finlim_to_comp_cat_with_ob CCu₂.

  Let ηC₁
    : comp_cat_functor_ob Cu₁ FCCu₁
    := pr11 (finlim_dfl_comp_cat_counit C₁) ,, finlim_dfl_comp_cat_counit_ob _.
  Let ηC₂
    : comp_cat_functor_ob Cu₂ FCCu₂
    := pr11 (finlim_dfl_comp_cat_counit C₂) ,, finlim_dfl_comp_cat_counit_ob _.

  Context {el₁ : comp_cat_univ_type Cu₁}
          {el₂ : comp_cat_univ_type Cu₂}
          (F_u : z_iso_disp
                  (comp_cat_functor_empty_context_z_iso F)
                  (comp_cat_type_functor F [] u₁)
                  u₂).

  Let Fu : comp_cat_functor_ob Cu₁ Cu₂ := pr11 F ,, F_u.
  Let FFu : functor_finlim_ob CCu₁ CCu₂
    := dfl_functor_comp_cat_to_finlim_functor F
       ,,
       dfl_full_comp_cat_functor_preserves_ob _ F_u.
  Let FFFu : comp_cat_functor_ob FCCu₁ FCCu₂
    := finlim_to_comp_cat_functor_ob FFu.

  Context (Fel : comp_cat_functor_preserves_univ_type Fu el₁ el₂).

  (** * 1. Coherence for the universe object *)
  Proposition finlim_dfl_comp_cat_counit_natural_ob_lem
    : pr2 (ηC₁ · FFFu) ==>[ pr11 (finlim_dfl_comp_cat_counit_natural F)] pr2 (Fu · ηC₂).
  Proof.
    use eq_cod_mor.
    rewrite transportf_cod_disp.
    refine (disp_codomain_comp _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply transportf_cod_disp.
    }
    refine (assoc _ _ _ @ _).
    refine (id_right _ @ _).
    refine (_ @ !(transportf_cod_disp _ _ _)).
    simpl.
    rewrite functor_id.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition finlim_dfl_comp_cat_counit_natural_ob
    : comp_cat_nat_trans_ob
        (ηC₁ · FFFu)
        (Fu · ηC₂).
  Proof.
    refine (pr11 (finlim_dfl_comp_cat_counit_natural F) ,, _).
    apply finlim_dfl_comp_cat_counit_natural_ob_lem.
  Defined.

  Proposition finlim_dfl_comp_cat_counit_natural_ob_pr1
              {Γ : Cu₁}
              (A : ty Γ)
              {Δ : Cu₂}
              (f : _ --> Δ)
    : dom_mor (comp_cat_type_fib_nat_trans finlim_dfl_comp_cat_counit_natural_ob A)
      · (PullbackPr1 _ · f)
      =
      dom_mor (comp_cat_functor_comprehension F _ A) · f.
  Proof.
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
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
                  _
                  _ _ _ _ _)
               _ _ _ _).
    }
    apply transportf_cod_disp.
  Qed.

  Let FFFel
    : comp_cat_functor_preserves_univ_type
         FFFu
         (finlim_to_comp_cat_univ_type
            (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₁ el₁))
         (finlim_to_comp_cat_univ_type
            (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₂ el₂))
    := finlim_to_comp_cat_functor_preserves_univ_type
         (el₁ := dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₁ el₁)
         (el₂ := dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₂ el₂)
         (dfl_full_comp_cat_functor_preserves_el F F_u Fel).

  (** 2. Calculational lemmas *)
  Proposition comp_cat_functor_preserves_univ_type_el_mor_counit_nat
              {Γ : FCCu₁}
              (t : tm Γ (comp_cat_univ Γ))
    : ∑ p,
      dom_mor (comp_cat_functor_preserves_univ_type_el_mor FFFel t)
      =
      comprehension_nat_trans_mor
        (comp_cat_functor_comprehension F)
        (comp_cat_univ_el
           el₁
           (dfl_full_comp_cat_mor_to_tm_univ u₁ (finlim_univ_tm_to_mor t)))
      · comprehension_functor_mor
          (comp_cat_comprehension C₂)
          (comp_cat_functor_preserves_univ_type_el_iso
             Fel
             (dfl_full_comp_cat_mor_to_tm_univ u₁ (finlim_univ_tm_to_mor t))
           · comp_cat_el_map_on_eq
               el₂
               (dfl_full_comp_cat_functor_preserves_el_map_eq
                  F F_u
                  (finlim_univ_tm_to_mor t)))
      · cat_el_map_el_eq (dfl_full_comp_cat_to_finlim_el_map u₂ el₂) p.
  Proof.
    eexists.
    apply idpath.
  Qed.

  Proposition comp_cat_functor_preserves_univ_type_el_mor_counit_nat_alt
              {Γ : FCCu₁}
              (t : tm Γ (comp_cat_univ Γ))
    : ∑ p,
      dom_mor (comp_cat_functor_preserves_univ_type_el_mor FFFel t)
      =
      comprehension_nat_trans_mor
        (comp_cat_functor_comprehension F)
        (comp_cat_univ_el
           el₁
           (dfl_full_comp_cat_mor_to_tm_univ u₁ (finlim_univ_tm_to_mor t)))
      · comprehension_functor_mor
          (comp_cat_comprehension C₂)
          (comp_cat_functor_preserves_univ_type_el_iso
             Fel
             (dfl_full_comp_cat_mor_to_tm_univ u₁ (finlim_univ_tm_to_mor t))
           · comp_cat_el_map_on_eq
               el₂
               p).
  Proof.
    eexists.
    refine (pr2 (comp_cat_functor_preserves_univ_type_el_mor_counit_nat t) @ _).
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_el_eq_counit.
    }
    etrans.
    {
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    etrans.
    {
      apply maponpaths.
      apply mor_disp_transportf_postwhisker.
    }
    rewrite comprehension_functor_mor_transportf.
    rewrite assoc_disp_var.
    rewrite comprehension_functor_mor_transportf.
    etrans.
    {
      do 2 apply maponpaths.
      apply (comp_cat_el_map_on_disp_concat el₂).
    }
    rewrite mor_disp_transportf_prewhisker.
    rewrite comprehension_functor_mor_transportf.
    refine (!_).
    apply comprehension_functor_mor_transportf.
  Qed.

  Proposition comp_cat_functor_preserves_univ_type_el_mor_counit_natural
              {Γ : Cu₁}
              (t : tm Γ (comp_cat_univ Γ))
    : ∑ p,
      dom_mor
        (comp_cat_functor_preserves_univ_type_el_mor
           (comp_comp_cat_functor_preserves_univ_type Fel
              (finlim_dfl_comp_cat_counit_preserves_univ_type u₂ el₂))
           t)
      =
      comprehension_functor_mor
        (comp_cat_comprehension C₂)
        (comp_cat_functor_preserves_univ_type_el_mor Fel t
         ;; comp_cat_el_map_on_eq el₂ p)%mor_disp.
  Proof.
    eexists.
    refine (comp_in_cod_fib _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply comp_in_cod_fib.
    }
    etrans.
    {
      apply maponpaths_2.
      apply transportf_cod_disp.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply transportf_cod_disp.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply comp_cat_el_map_on_eq_counit.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (comprehension_functor_mor_comp (comp_cat_comprehension C₂)).
    }
    etrans.
    {
      refine (!_).
      apply (comprehension_functor_mor_comp (comp_cat_comprehension C₂)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply (comp_cat_el_map_on_disp_concat el₂).
    }
    rewrite mor_disp_transportf_prewhisker.
    rewrite comprehension_functor_mor_transportf.
    apply idpath.
  Qed.

  (** * 3. Coherence for the associated type map *)
  Proposition finlim_dfl_comp_cat_counit_natural_preserves_univ_type_lem_lhs
              {Γ : Cu₁}
              (t : tm Γ (comp_cat_univ Γ))
    : ∑ p,
      dom_mor
        (comp_cat_functor_coerce
           FFFu
           (comp_cat_functor_preserves_univ_type_el_mor
              (finlim_dfl_comp_cat_counit_preserves_univ_type u₁ el₁) t))
      · dom_mor
          (comp_cat_functor_preserves_univ_type_el_mor
             FFFel
             (comp_cat_functor_tm ηC₁ t ↑ functor_comp_cat_on_univ ηC₁ Γ))
      · dom_mor
          (comp_cat_el_map_on_eq
             (finlim_to_comp_cat_univ_type
                (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₂ el₂))
             (comp_comp_cat_functor_preserves_el_path _ FFFu t))
      · dom_mor
          (comp_cat_el_map_on_eq
             (finlim_to_comp_cat_univ_type
                (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₂ el₂))
             (comp_cat_nat_trans_preserves_univ_type_path
                finlim_dfl_comp_cat_counit_natural_ob
                t))
      =
      comprehension_nat_trans_mor (comp_cat_functor_comprehension F) (comp_cat_univ_el el₁ t)
      · comprehension_functor_mor
          (comp_cat_comprehension C₂)
          (♯(comp_cat_type_functor F)
              (comp_cat_el_map_on_eq
                 el₁
                 (finlim_dfl_comp_cat_counit_preserves_el_eq u₁ t))
           ;; (pr1 (comp_cat_functor_preserves_univ_type_el_iso Fel _)
           ;; comp_cat_el_map_on_eq el₂ p))%mor_disp.
  Proof.
    eexists.
    etrans.
    {
      apply maponpaths.
      apply comp_cat_el_map_on_eq_counit.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply comp_cat_el_map_on_eq_counit.
    }
    etrans.
    {
      rewrite !assoc'.
      do 2 apply maponpaths.
      refine (!(comprehension_functor_mor_comp _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply (comp_cat_el_map_on_disp_concat el₂).
      }
      apply comprehension_functor_mor_transportf.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (pr2 (comp_cat_functor_preserves_univ_type_el_mor_counit_nat_alt _)).
    }
    etrans.
    {
      rewrite !assoc'.
      do 2 apply maponpaths.
      refine (!(comprehension_functor_mor_comp _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply mor_disp_transportf_postwhisker.
      }
      rewrite comprehension_functor_mor_transportf.
      rewrite assoc_disp_var.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        do 2 apply maponpaths.
        apply (comp_cat_el_map_on_disp_concat el₂).
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      apply idpath.
    }
    etrans.
    {
      apply maponpaths_2.
      apply (finlim_to_comp_cat_functor_coerce (dfl_functor_comp_cat_to_finlim_functor F)).
    }
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      apply (comprehension_nat_trans_comm (comp_cat_functor_comprehension F)).
    }
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      apply (comprehension_functor_mor_comp (comp_cat_comprehension C₂)).
    }
    apply idpath.
  Qed.

  Local Notation "'comp_el_eq' el" := (comp_cat_el_map_on_eq el _) (at level 0, only printing).

  Proposition finlim_dfl_comp_cat_counit_natural_preserves_univ_type_lem
              {Γ : Cu₁}
              (t : tm Γ (comp_cat_univ Γ))
    : comp_cat_functor_preserves_univ_type_el_mor
        (comp_comp_cat_functor_preserves_univ_type
           (finlim_dfl_comp_cat_counit_preserves_univ_type u₁ el₁)
           FFFel)
        t
      · comp_cat_el_map_on_eq
          (finlim_to_comp_cat_univ_type
             (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₂ el₂))
          (comp_cat_nat_trans_preserves_univ_type_path
             finlim_dfl_comp_cat_counit_natural_ob
             t)
      =
      comp_cat_type_fib_nat_trans
        finlim_dfl_comp_cat_counit_natural_ob
        (comp_cat_univ_el el₁ t)
      · coerce_subst_ty
          (finlim_dfl_comp_cat_counit_natural_ob Γ)
          (comp_cat_functor_preserves_univ_type_el_mor
             (comp_comp_cat_functor_preserves_univ_type Fel
                (finlim_dfl_comp_cat_counit_preserves_univ_type u₂ el₂))
             t)
      · finlim_to_comp_cat_stable_el_map_mor
          (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₂ el₂)
          (finlim_dfl_comp_cat_counit_natural_ob Γ)
          (comp_cat_functor_tm (pr11 F · finlim_dfl_comp_cat_counit_mor_comp_cat C₂) t
           ↑ functor_comp_cat_on_univ (Fu · ηC₂) Γ).
  Proof.
    etrans.
    {
      apply maponpaths_2.
      apply eq_comp_comp_cat_functor_preserves_univ.
    }
    use eq_mor_cod_fib.
    etrans.
    {
      refine (comp_in_cod_fib _ _ @ _).
      apply maponpaths_2.
      refine (comp_in_cod_fib _ _ @ _).
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    refine (!_).
    etrans.
    {
      refine (comp_in_cod_fib _ _ @ _).
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    refine (!_).
    etrans.
    {
      refine (_ @ pr2 (finlim_dfl_comp_cat_counit_natural_preserves_univ_type_lem_lhs t)).
      (**
         The following helps reducing the time necessary for compilation.
       *)
      do 2 refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      do 2 apply maponpaths.
      refine (maponpaths
                (λ z,
                 z
                 · dom_mor
                     (comp_cat_el_map_on_eq
                        (finlim_to_comp_cat_univ_type
                           (dfl_full_comp_cat_to_finlim_stable_el_map_coherent u₂ el₂))
                        _))
                _).
      Opaque finlim_to_comp_cat_univ_type dfl_full_comp_cat_to_finlim_stable_el_map_coherent.
      apply idpath.
    }
    refine (_ @ assoc _ _ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply assoc.
    }
    refine (assoc _ _ _ @ _).
    use z_iso_inv_to_right.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      use cat_el_map_el_eq_inv.
    }
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_el_eq_counit.
    }
    etrans.
    {
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      apply (comprehension_functor_mor_comp (comp_cat_comprehension C₂)).
    }
    etrans.
    {
      apply maponpaths.
      rewrite assoc_disp_var.
      rewrite comprehension_functor_mor_transportf.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        do 3 apply maponpaths.
        apply (comp_cat_el_map_on_disp_concat el₂).
      }
      rewrite !mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      apply idpath.
    }
    use (MorphismsIntoPullbackEqual
           (isPullback_Pullback
              (cat_stable_el_map_pb
                 (dfl_full_comp_cat_to_finlim_stable_el_map_coherent _ _)
                 _
                 _))).
    - refine (!_).
      etrans.
      {
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          apply (PullbackArrow_PullbackPr1
                   (cat_stable_el_map_pb
                      (dfl_full_comp_cat_to_finlim_stable_el_map_coherent _ _)
                      _
                      _)).
        }
        etrans.
        {
          apply maponpaths.
          apply (coerce_subst_ty_counit_pr1 u₂).
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          simpl.
          apply idpath.
        }
        apply finlim_dfl_comp_cat_counit_natural_ob_pr1.
      }
      refine (_ @ assoc _ _ _).
      apply maponpaths.
      etrans.
      {
        exact (pr2 (comp_cat_functor_preserves_univ_type_el_mor_counit_natural _)).
      }
      refine (!_).
      etrans.
      {
        refine (!_).
        apply (comprehension_functor_mor_comp (comp_cat_comprehension C₂)).
      }
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        rewrite !assoc_disp.
        unfold transportb.
        rewrite comprehension_functor_mor_transportf.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !comprehension_functor_mor_transportf.
        etrans.
        {
          apply maponpaths.
          do 4 apply maponpaths_2.
          apply (comp_cat_functor_preserves_univ_type_el_iso_natural _ Fel).
        }
        rewrite !mor_disp_transportf_postwhisker.
        rewrite comprehension_functor_mor_transportf.
        rewrite !assoc_disp_var.
        rewrite !comprehension_functor_mor_transportf.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc_disp.
          unfold transportb.
          rewrite transport_f_f.
          apply idpath.
        }
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !comprehension_functor_mor_transportf.
        etrans.
        {
          do 2 apply maponpaths.
          do 3 apply maponpaths_2.
          apply (comp_cat_el_map_on_disp_concat el₂).
        }
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite comprehension_functor_mor_transportf.
        etrans.
        {
          do 2 apply maponpaths.
          do 2 apply maponpaths_2.
          apply (comp_cat_el_map_on_disp_concat el₂).
        }
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite comprehension_functor_mor_transportf.
        rewrite assoc_disp_var.
        rewrite mor_disp_transportf_prewhisker.
        rewrite comprehension_functor_mor_transportf.
        etrans.
        {
          do 2 apply maponpaths.
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply (comp_cat_univ_el_stable_id_coh_inv el₂).
          }
          apply mor_disp_transportf_postwhisker.
        }
        rewrite !mor_disp_transportf_prewhisker.
        rewrite comprehension_functor_mor_transportf.
        rewrite assoc_disp_var.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite comprehension_functor_mor_transportf.
        etrans.
        {
          do 4 apply maponpaths.
          apply cartesian_factorisation_commutes.
        }
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite comprehension_functor_mor_transportf.
        rewrite id_right_disp.
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite comprehension_functor_mor_transportf.
        etrans.
        {
          do 2 apply maponpaths.
          apply (comp_cat_el_map_on_disp_concat el₂).
        }
        rewrite mor_disp_transportf_prewhisker.
        apply comprehension_functor_mor_transportf.
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply (eq_comp_cat_el_map_on_eq el₂).
      }
      apply idpath.
    - etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        apply comprehension_functor_mor_comm.
      }
      etrans.
      {
        rewrite functor_id.
        rewrite !id_right.
        apply (comprehension_nat_trans_mor_comm (comp_cat_functor_comprehension F)).
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          apply (PullbackArrow_PullbackPr2
                   (cat_stable_el_map_pb
                      (dfl_full_comp_cat_to_finlim_stable_el_map_coherent _ _)
                      _
                      _)).
        }
        apply maponpaths.
        apply (coerce_subst_ty_counit_pr2 u₂).
      }
      apply (mor_eq (comp_cat_type_fib_nat_trans finlim_dfl_comp_cat_counit_natural_ob _)).
  Qed.

  Definition finlim_dfl_comp_cat_counit_natural_preserves_univ_type
    : comp_cat_nat_trans_preserves_univ_type
        finlim_dfl_comp_cat_counit_natural_ob
        (comp_comp_cat_functor_preserves_univ_type
           (finlim_dfl_comp_cat_counit_preserves_univ_type u₁ el₁)
           FFFel)
        (comp_comp_cat_functor_preserves_univ_type
           Fel
           (finlim_dfl_comp_cat_counit_preserves_univ_type u₂ el₂)).
  Proof.
    intros Γ t.
    exact (finlim_dfl_comp_cat_counit_natural_preserves_univ_type_lem t).
  Qed.
End CounitCell.
