(**

 Universes in the comprehension category associated to a category with finite limits

 In this file, we construct a displayed pseudofunctor from the displayed bicategory of
 universes for univalent categories with finite limits to the displayed bicategory of
 universes for univalent DFL comprehension categories.

 The idea behind this construction is as follows. We have a category `C` with finite
 limits and a universe `u`. We need to construct a universe in the comprehension category
 given by the codomain functor. This constitutes the following:
 - A type in the empty context, so an object together with a morphism to the terminal
   object. This is given by the object `u`.
 - For context `Γ` and term `t` of type `u` in context `Γ`, we type in context `Γ`. Terms
   of type `u` in context `Γ` are the same as morphisms `Γ --> u`, and hence, we get a
   morphism `el t --> Γ` in `C`, which constitutes a type in context `Γ`. The reason why
   we have this morphism, is by assumption that `u` is a universe.
 There also are stability conditions saying that the type associated to a term is stable
 under substitution up to isomorphism. There is some work in constructing the stability
 isomorphism. This is because the stability is formulated slightly different in the case
 for categories with finite limits and for comprehension categories. Specifically, for
 categories with finite limits, stability is expressed by saying that a certain square is
 a pullback, whereas for comprehension categories stability is expressed by postulating
 the existence of a certain isomorphism. This difference also affects the verification
 of the coherence conditions.

 Contents
 1. Action on objects
 1.1. Construction of the universe object
 1.2. Terms of the universe correspond to morphisms
 1.3. Calculational lemma
 1.4. The type associated to a term of the universe
 1.5. Calculational lemma for equalities of the associated type
 1.6. Stability of the type associated to a term of the universe
 1.7. The coherences
 2. Action on 1-cells
 2.1. Preservation of the universe type
 2.2. A calculational lemma
 2.3. Preservation of the associated type
 2.4. The coherences
 3. The action on 2-cells
 4. The identitor
 5. The compositor
 6. The displayed pseudofunctor

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
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.FinLimToCompCatLemmas.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.CatWithOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseInCat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CatWithUniv.UniverseDispBicat.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatWithUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.FinLimToDFLCompCat.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Action on objects *)
Section UniverseInCod.
  Context {C : univ_cat_with_finlim_ob}
          (el : cat_stable_el_map_coherent C).

  (** ** 1.1. Construction of the universe object *)
  Definition finlim_to_comp_cat_universe_ob
    : ty ([] : finlim_to_comp_cat C).
  Proof.
    use make_cod_fib_ob.
    - exact (univ_cat_universe C).
    - apply TerminalArrow.
  Defined.

  Definition finlim_to_comp_cat_with_ob
    : comp_cat_with_ob.
  Proof.
    simple refine (_ ,, _).
    - exact (finlim_to_comp_cat C).
    - exact finlim_to_comp_cat_universe_ob.
  Defined.

  Let u (Γ : C) : comp_cat_ty (C := finlim_to_comp_cat_with_ob) Γ
    := comp_cat_univ (C := finlim_to_comp_cat_with_ob) Γ.

  (** ** 1.2. Terms of the universe correspond to morphisms *)
  Definition finlim_univ_tm_to_mor
             {Γ : C}
             (t : comp_cat_tm
                    (C := finlim_to_comp_cat C)
                    Γ
                    (u Γ))
    : Γ --> univ_cat_universe _
    := t · PullbackPr1 _.

  Definition finlim_mor_to_univ_tm
             {Γ : C}
             (t : Γ --> univ_cat_universe _)
    : comp_cat_tm
        (C := finlim_to_comp_cat C)
        Γ
        (u Γ).
  Proof.
    use make_comp_cat_tm.
    - use (PullbackArrow (comp_cat_pullback _ _)).
      + exact t.
      + apply identity.
      + abstract
          (apply TerminalArrowEq).
    - abstract
        (exact (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _) _ _ _ _)).
  Defined.

  Proposition finlim_mor_to_univ_tm_to_mor
              {Γ : C}
              (t : Γ --> univ_cat_universe _)
    : finlim_univ_tm_to_mor (finlim_mor_to_univ_tm t) = t.
  Proof.
    exact (PullbackArrow_PullbackPr1
             (comp_cat_pullback finlim_to_comp_cat_universe_ob _)
             _ _ _ _).
  Qed.

  Proposition finlim_univ_tm_to_mor_to_tm
              {Γ : C}
              (t : comp_cat_tm
                     (C := finlim_to_comp_cat C)
                     Γ
                     (u Γ))
    : finlim_mor_to_univ_tm (finlim_univ_tm_to_mor t) = t.
  Proof.
    use eq_comp_cat_tm.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback _ _))).
    - apply PullbackArrow_PullbackPr1.
    - etrans.
      {
        apply PullbackArrow_PullbackPr2.
      }
      refine (!_).
      exact (comp_cat_tm_eq t).
  Qed.

  Definition finlim_univ_tm_weq_mor
             (Γ : C)
    : (Γ --> univ_cat_universe _)
      ≃
      comp_cat_tm
        (C := finlim_to_comp_cat C)
        Γ
        (u Γ).
  Proof.
    use weq_iso.
    - apply finlim_mor_to_univ_tm.
    - apply finlim_univ_tm_to_mor.
    - apply finlim_mor_to_univ_tm_to_mor.
    - apply finlim_univ_tm_to_mor_to_tm.
  Defined.

  (** ** 1.3. Calculational lemma for stability *)

  (**
     We simplify `sub_comp_cat_univ` in the comprehension category associated to a category
     with finite limits. The morphism `sub_comp_cat_univ` expresses stability of the universe
     type under isomorphism, and it is used frequently in the development. Simplifying this
     term is useful technically, because it simplifies calculations.
   *)
  Definition finlim_to_comp_cat_sub_comp_cat_univ_mor
             {Γ Δ : finlim_to_comp_cat_with_ob}
             (s : Γ --> Δ)
    : cod_dom (comp_cat_univ Δ [[ s ]])
      -->
      cod_dom (comp_cat_univ Γ).
  Proof.
    use (PullbackArrow (comp_cat_pullback finlim_to_comp_cat_universe_ob _)).
    - exact (PullbackPr1 _ · PullbackPr1 _).
    - exact (PullbackPr2 _).
    - abstract
        (apply TerminalArrowEq).
  Defined.

  Proposition finlim_to_comp_cat_sub_comp_cat_univ_eq_lemma
              {Γ Δ : finlim_to_comp_cat_with_ob}
              (s : Γ --> Δ)
    : dom_mor (sub_comp_cat_univ s)
      =
      dom_mor (comp_subst_ty_iso s (TerminalArrow [] Δ) (ob_of_comp_cat_ob _))
      · dom_mor (eq_subst_ty_iso
                   (ob_of_comp_cat_ob finlim_to_comp_cat_with_ob)
                   (TerminalArrowEq _ _)).
  Proof.
    rewrite <- comp_in_cod_fib.
    apply idpath.
  Qed.

  Proposition finlim_to_comp_cat_sub_comp_cat_univ_eq
              {Γ Δ : finlim_to_comp_cat_with_ob}
              (s : Γ --> Δ)
    : dom_mor (sub_comp_cat_univ s)
      =
      finlim_to_comp_cat_sub_comp_cat_univ_mor s.
  Proof.
    rewrite finlim_to_comp_cat_sub_comp_cat_univ_eq_lemma.
    use (MorphismsIntoPullbackEqual
           (isPullback_Pullback
              (comp_cat_pullback finlim_to_comp_cat_universe_ob _))).
    - refine (_ @ !(PullbackArrow_PullbackPr1 _ _ _ _ _)).
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply finlim_to_comp_cat_eq_subst_ty_pullback_pr1.
      }
      apply finlim_to_comp_cat_comp_subst_ty_pullback_pr1.
    - refine (_ @ !(PullbackArrow_PullbackPr2 _ _ _ _ _)).
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply finlim_to_comp_cat_eq_subst_ty_pullback_pr2.
      }
      apply finlim_to_comp_cat_comp_subst_ty_pullback_pr2.
  Qed.

  (** ** 1.4. The type associated to a term of the universe *)
  Definition finlim_to_comp_cat_el_map
    : comp_cat_el_map finlim_to_comp_cat_with_ob.
  Proof.
    intros Γ t.
    use make_cod_fib_ob.
    - exact (cat_el_map_el el (finlim_univ_tm_to_mor t)).
    - exact (cat_el_map_mor el (finlim_univ_tm_to_mor t)).
  Defined.

  Let elC {Γ : finlim_to_comp_cat_with_ob} (t : tm Γ (comp_cat_univ Γ))
    : ty Γ
    := finlim_to_comp_cat_el_map Γ t.

  (** ** 1.5. Calculational lemma for equalities of the associated type *)
  Lemma finlim_comp_cat_el_map_on_eq
        {Γ : finlim_to_comp_cat_with_ob}
        {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
        (p : t₁ = t₂)
    : dom_mor (comp_cat_el_map_on_eq finlim_to_comp_cat_el_map p)
      =
      cat_el_map_el_eq el (maponpaths finlim_univ_tm_to_mor p).
  Proof.
    induction p.
    apply idpath.
  Qed.

  (** ** 1.6. Stability of the type associated to a term of the universe *)

  (**
     We need to make an isomorphism in the slice category between [elC t [[ s ]]]
     and [elC (t [[ s ]]tm ↑ sub_comp_cat_univ s)]. The relevant morphisms are
     given in
     - [finlim_to_comp_cat_stable_el_map_mor]
     - [finlim_to_comp_cat_stable_el_map_inv]
   *)
  Definition finlim_to_comp_cat_stable_el_map_mor_mor
             {Γ Δ : finlim_to_comp_cat_with_ob}
             (s : Γ --> Δ)
             (t : tm Δ (comp_cat_univ Δ))
    : cod_dom (elC t [[ s ]])
      -->
      cat_el_map_el el (s · finlim_univ_tm_to_mor t).
  Proof.
    use (PullbackArrow (cat_stable_el_map_pb el s (finlim_univ_tm_to_mor t))).
    - apply PullbackPr1.
    - apply PullbackPr2.
    - abstract
        (apply PullbackSqrCommutes).
  Defined.

  Proposition finlim_to_comp_cat_stable_el_map_equality
              {Γ Δ : C}
              (s : Γ --> Δ)
              (t : comp_cat_tm (C := finlim_to_comp_cat_with_ob) Δ (comp_cat_univ _))
    : finlim_univ_tm_to_mor (t [[ s ]]tm ↑ sub_comp_cat_univ _)
      =
      s · finlim_univ_tm_to_mor t.
  Proof.
    unfold finlim_univ_tm_to_mor.
    etrans.
    {
      apply maponpaths_2.
      apply finlim_to_comp_cat_coerce_eq.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply finlim_to_comp_cat_sub_comp_cat_univ_eq.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      exact (PullbackArrow_PullbackPr1
               (comp_cat_pullback finlim_to_comp_cat_universe_ob _)
               _ _ _ _).
    }
    rewrite !assoc.
    apply maponpaths_2.
    exact (finlim_to_comp_cat_subst_tm_pullback_pr1 s t).
  Qed.

  Definition finlim_to_comp_cat_stable_el_map_mor
             {Γ Δ : finlim_to_comp_cat_with_ob}
             (s : Γ --> Δ)
             (t : tm Δ (comp_cat_univ Δ))
    : fiber_category _ _
        ⟦ elC t [[ s ]]
          ,
          elC (t [[ s ]]tm ↑ sub_comp_cat_univ s) ⟧.
  Proof.
    use make_cod_fib_mor.
    - exact (finlim_to_comp_cat_stable_el_map_mor_mor s t
             · cat_el_map_el_eq el (!(finlim_to_comp_cat_stable_el_map_equality s t))).
    - abstract
        (refine (assoc' _ _ _ @ _) ;
         refine (maponpaths (λ z, _ · z) (cat_el_map_mor_eq _ _) @ _) ;
         apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el s _))).
  Defined.

  Definition finlim_to_comp_cat_stable_el_map_inv
             {Γ Δ : finlim_to_comp_cat_with_ob}
             (s : Γ --> Δ)
             (t : tm Δ (comp_cat_univ Δ))
    : cat_el_map_el el (s · finlim_univ_tm_to_mor t)
      -->
      cod_dom (elC t [[s]]).
  Proof.
    use PullbackArrow.
    - exact (PullbackPr1 (cat_stable_el_map_pb el s (finlim_univ_tm_to_mor t))).
    - exact (PullbackPr2 (cat_stable_el_map_pb el s (finlim_univ_tm_to_mor t))).
    - abstract
        (apply (PullbackSqrCommutes (cat_stable_el_map_pb el s (finlim_univ_tm_to_mor t)))).
  Defined.

  Proposition is_z_iso_finlim_to_comp_cat_stable_el_map_mor_eqs
              {Γ Δ : finlim_to_comp_cat_with_ob}
              (s : Γ --> Δ)
              (t : tm Δ (comp_cat_univ Δ))
    : is_inverse_in_precat
        (finlim_to_comp_cat_stable_el_map_mor_mor s t)
        (finlim_to_comp_cat_stable_el_map_inv s t).
  Proof.
    split.
    - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      + rewrite id_left.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply PullbackArrow_PullbackPr1.
        }
        apply (PullbackArrow_PullbackPr1
                 (cat_stable_el_map_pb el s (finlim_univ_tm_to_mor t))).
      + rewrite id_left.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply PullbackArrow_PullbackPr2.
        }
        apply (PullbackArrow_PullbackPr2
                 (cat_stable_el_map_pb el s (finlim_univ_tm_to_mor t))).
    - use (MorphismsIntoPullbackEqual
             (isPullback_Pullback
                (cat_stable_el_map_pb el s (finlim_univ_tm_to_mor t)))).
      + rewrite id_left.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1
                   (cat_stable_el_map_pb el s (finlim_univ_tm_to_mor t))).
        }
        apply PullbackArrow_PullbackPr1.
      + rewrite id_left.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2
                   (cat_stable_el_map_pb el s (finlim_univ_tm_to_mor t))).
        }
        apply PullbackArrow_PullbackPr2.
  Qed.

  Definition finlim_to_comp_cat_stable_el_map_mor_z_iso
             {Γ Δ : finlim_to_comp_cat_with_ob}
             (s : Γ --> Δ)
             (t : tm Δ (comp_cat_univ Δ))
    : z_iso
        (cod_dom (elC t [[ s ]]))
        (cat_el_map_el el (s · finlim_univ_tm_to_mor t)).
  Proof.
    use make_z_iso.
    - exact (finlim_to_comp_cat_stable_el_map_mor_mor s t).
    - exact (finlim_to_comp_cat_stable_el_map_inv s t).
    - apply is_z_iso_finlim_to_comp_cat_stable_el_map_mor_eqs.
  Defined.

  Definition is_z_iso_finlim_to_comp_cat_stable_el_map_mor
             {Γ Δ : finlim_to_comp_cat_with_ob}
             (s : Γ --> Δ)
             (t : tm Δ (comp_cat_univ Δ))
    : is_z_isomorphism (dom_mor (finlim_to_comp_cat_stable_el_map_mor s t)).
  Proof.
    use is_z_isomorphism_comp.
    - use make_is_z_isomorphism.
      + exact (finlim_to_comp_cat_stable_el_map_inv s t).
      + apply is_z_iso_finlim_to_comp_cat_stable_el_map_mor_eqs.
    - apply z_iso_is_z_isomorphism.
  Defined.

  Definition finlim_to_comp_cat_stable_el_map
    : comp_cat_stable_el_map finlim_to_comp_cat_el_map.
  Proof.
    intros Γ Δ s t.
    simple refine (_ ,, _).
    - exact (finlim_to_comp_cat_stable_el_map_mor s t).
    - use is_z_iso_fiber_from_is_z_iso_disp.
      use is_z_iso_disp_codomain.
      apply is_z_iso_finlim_to_comp_cat_stable_el_map_mor.
  Defined.

  (** ** 1.7. The coherences *)
  Proposition finlim_to_comp_cat_coherent_el_map
    : comp_cat_coherent_el_map finlim_to_comp_cat_stable_el_map.
  Proof.
    split.
    - intros Γ t.
      use eq_mor_cod_fib.
      refine (comp_in_cod_fib _ _ @ _).
      refine (!_).
      etrans.
      {
        apply finlim_comp_cat_el_map_on_eq.
      }
      refine (!_).
      refine (assoc _ _ _ @ _).
      use z_iso_inv_to_right.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_el_eq_inv.
      }
      refine (cat_el_map_el_eq_comp _ _ _ @ _).
      refine (!_).
      use (MorphismsIntoPullbackEqual
             (isPullback_Pullback
                (cat_stable_el_map_pb el _ _))).
      + rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (cat_stable_el_map_pb el _ _)).
        }
        etrans.
        {
          apply finlim_to_comp_cat_id_subst_ty_pullback_pr1.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply cat_el_map_pb_mor_id.
        }
        refine (cat_el_map_el_eq_comp _ _ _ @ _).
        apply cat_el_map_el_eq_id.
      + rewrite assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el _ _)).
        }
        etrans.
        {
          apply finlim_to_comp_cat_id_subst_ty_pullback_pr2.
        }
        refine (!_).
        apply cat_el_map_mor_eq.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
      use eq_mor_cod_fib.
      refine (comp_in_cod_fib _ _ @ _).
      refine (!_).
      refine (comp_in_cod_fib _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply comp_in_cod_fib.
      }
      etrans.
      {
        apply maponpaths.
        apply finlim_comp_cat_el_map_on_eq.
      }
      etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        apply cat_el_map_el_eq_comp.
      }
      refine (!_).
      refine (assoc _ _ _ @ _).
      use z_iso_inv_to_right.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_el_eq_inv.
      }
      etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        apply cat_el_map_el_eq_comp.
      }
      refine (!_).
      use (MorphismsIntoPullbackEqual
             (isPullback_Pullback
                (cat_stable_el_map_pb el _ _))).
      + rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr1 (cat_stable_el_map_pb el _ _)).
        }
        etrans.
        {
          apply finlim_to_comp_cat_comp_subst_ty_pullback_pr1.
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          apply cat_el_map_pb_mor_comp.
        }
        etrans.
        {
          apply maponpaths.
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          etrans.
          {
            apply maponpaths_2.
            apply cat_el_map_el_eq_comp.
          }
          use cat_el_map_pb_mor_eq.
          apply finlim_to_comp_cat_stable_el_map_equality.
        }
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply (PullbackArrow_PullbackPr1 (cat_stable_el_map_pb el _ _)).
        }
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr1.
        }
        do 2 refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (cat_el_map_el_eq_comp _ _ _ @ _).
          apply cat_el_map_el_eq_id.
        }
        rewrite id_left.
        apply (PullbackArrow_PullbackPr1 (cat_stable_el_map_pb el _ _)).
      + rewrite assoc'.
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el _ _)).
        }
        etrans.
        {
          apply finlim_to_comp_cat_comp_subst_ty_pullback_pr2.
        }
        refine (!_).
        etrans.
        {
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          refine (assoc' _ _ _ @ _).
          apply maponpaths.
          apply cat_el_map_mor_eq.
        }
        etrans.
        {
          apply maponpaths.
          apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb el _ _)).
        }
        apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr2.
  Qed.

  Definition finlim_to_comp_cat_univ_type
    : comp_cat_univ_type finlim_to_comp_cat_with_ob.
  Proof.
    use make_comp_cat_univ_type.
    - exact finlim_to_comp_cat_el_map.
    - exact finlim_to_comp_cat_stable_el_map.
    - exact finlim_to_comp_cat_coherent_el_map.
  Defined.
End UniverseInCod.

Arguments finlim_to_comp_cat_universe_ob _ : clear implicits.
Arguments finlim_to_comp_cat_with_ob _ : clear implicits.

(** * 2. Action on 1-cells *)
Section UniverseInCodFunctor.
  Context {C₁ C₂ : univ_cat_with_finlim_ob}
          {F : functor_finlim_ob C₁ C₂}
          {el₁ : cat_stable_el_map_coherent C₁}
          {el₂ : cat_stable_el_map_coherent C₂}
          (Fu : functor_preserves_el el₁ el₂ F).

  (** ** 2.1. Preservation of the universe type *)
  Definition finlim_to_comp_cat_functor_ob_mor
    : mor_disp
        (D := disp_bicat_comp_cat_with_ob)
        (finlim_to_comp_cat_universe_ob C₁)
        (finlim_to_comp_cat_universe_ob C₂)
        (finlim_to_comp_cat_functor F).
  Proof.
    use z_iso_disp_codomain.
    - exact (functor_on_universe F).
    - abstract
        (apply TerminalArrowEq).
  Defined.

  Definition finlim_to_comp_cat_functor_ob
    : comp_cat_functor_ob
        (finlim_to_comp_cat_with_ob C₁)
        (finlim_to_comp_cat_with_ob C₂)
    := _ ,, finlim_to_comp_cat_functor_ob_mor.

  (** ** 2.2. A calculational lemma *)

  (**
     We compute the action of a functor on morphisms constructed using [finlim_univ_tm_to_mor].
     This is needed for various calculations. We use the following lemma.
   *)
  Lemma finlim_to_comp_cat_functor_comp_cat_on_univ
        (Γ : C₁)
    : dom_mor (functor_comp_cat_on_univ finlim_to_comp_cat_functor_ob Γ)
      =
      dom_mor (comp_cat_functor_subst_ty_coe
                 finlim_to_comp_cat_functor_ob _ _)
      · dom_mor (subst_ty_coe
                   _ _
                   (ob_of_functor_comp_cat_ob finlim_to_comp_cat_functor_ob))
      · dom_mor (eq_subst_ty
                   (ob_of_comp_cat_ob (finlim_to_comp_cat_with_ob C₂))
                   (functor_comp_cat_on_univ_z_iso_terminal_eq
                      finlim_to_comp_cat_functor_ob
                      Γ)).
  Proof.
    etrans.
    {
      apply transportf_cod_disp.
    }
    refine (assoc _ _ _ @ _).
    apply idpath.
  Qed.

  Proposition functor_finlim_univ_tm_to_mor
              {Γ : finlim_to_comp_cat_with_ob C₁}
              (t : comp_cat_tm Γ (comp_cat_univ Γ))
    : #F (finlim_univ_tm_to_mor t)
      · functor_on_universe F
      =
      finlim_univ_tm_to_mor
        (comp_cat_functor_tm(finlim_to_comp_cat_functor F) t
         ↑ functor_comp_cat_on_univ finlim_to_comp_cat_functor_ob Γ).
  Proof.
    unfold finlim_univ_tm_to_mor.
    rewrite functor_comp.
    simpl.
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ !(id_left _)).
    refine (!_).
    rewrite finlim_to_comp_cat_comp_mor.
    rewrite finlim_to_comp_cat_functor_comp_cat_on_univ.
    rewrite !assoc'.
    etrans.
    {
      do 2 apply maponpaths.
      apply finlim_to_comp_cat_eq_subst_ty_pullback_pr1.
    }
    etrans.
    {
      apply maponpaths.
      exact (finlim_to_comp_cat_subst_ty_coe_pr1
               _ _
               (ob_of_functor_comp_cat_ob finlim_to_comp_cat_functor_ob)).
    }
    rewrite !assoc.
    apply maponpaths_2.
    exact (finlim_to_comp_cat_functor_subst_ty_coe_pr1 _ _ _).
  Qed.

  (** ** 2.3. Preservation of the associated type *)
  Definition finlim_to_comp_cat_functor_preserves_el_cod_mor
             {Γ : finlim_to_comp_cat_with_ob C₁}
             (t : tm Γ (comp_cat_univ Γ))
    : z_iso
        (F (cat_el_map_el el₁ (finlim_univ_tm_to_mor t)))
        (cat_el_map_el
           el₂
           (finlim_univ_tm_to_mor
              (comp_cat_functor_tm (finlim_to_comp_cat_functor F) t
               ↑ functor_comp_cat_on_univ finlim_to_comp_cat_functor_ob Γ))).
  Proof.
    refine (z_iso_comp
              (functor_el_map_iso Fu (finlim_univ_tm_to_mor t))
              _).
    use cat_el_map_el_eq.
    exact (functor_finlim_univ_tm_to_mor t).
  Defined.

  Proposition finlim_to_comp_cat_functor_preserves_el_cod_mor_eq
              {Γ : finlim_to_comp_cat_with_ob C₁}
              (t : tm Γ (comp_cat_univ Γ))
    : finlim_to_comp_cat_functor_preserves_el_cod_mor t
      · cod_mor
          (comp_cat_univ_el
             (finlim_to_comp_cat_univ_type el₂)
             (comp_cat_functor_tm finlim_to_comp_cat_functor_ob t
              ↑ functor_comp_cat_on_univ finlim_to_comp_cat_functor_ob Γ))
      =
      # F (cat_el_map_mor el₁ (finlim_univ_tm_to_mor t)).
  Proof.
    refine (assoc' _ _ _ @ _).
    refine (!_).
    etrans.
    {
      exact (functor_el_map_comm Fu (finlim_univ_tm_to_mor t)).
    }
    apply maponpaths.
    refine (!_).
    simpl.
    apply cat_el_map_mor_eq.
  Qed.

  Definition finlim_to_comp_cat_functor_preserves_el_mor
             {Γ : finlim_to_comp_cat_with_ob C₁}
             (t : tm Γ (comp_cat_univ Γ))
    : fiber_category _ _
        ⟦ comp_cat_type_functor
            finlim_to_comp_cat_functor_ob
            Γ
            (comp_cat_univ_el (finlim_to_comp_cat_univ_type el₁) t)
          ,
          comp_cat_univ_el
            (finlim_to_comp_cat_univ_type el₂)
            (comp_cat_functor_tm finlim_to_comp_cat_functor_ob t
             ↑ functor_comp_cat_on_univ finlim_to_comp_cat_functor_ob Γ) ⟧.
  Proof.
    use make_cod_fib_mor.
    - exact (finlim_to_comp_cat_functor_preserves_el_cod_mor t).
    - exact (finlim_to_comp_cat_functor_preserves_el_cod_mor_eq t).
  Defined.

  Definition finlim_to_comp_cat_functor_preserves_el
    : comp_cat_functor_preserves_el
        finlim_to_comp_cat_functor_ob
        (finlim_to_comp_cat_univ_type el₁)
        (finlim_to_comp_cat_univ_type el₂).
  Proof.
    intros Γ t.
    simple refine (_ ,, _).
    - exact (finlim_to_comp_cat_functor_preserves_el_mor t).
    - use is_z_iso_fiber_from_is_z_iso_disp.
      use is_z_iso_disp_codomain.
      exact (z_iso_is_z_isomorphism (finlim_to_comp_cat_functor_preserves_el_cod_mor t)).
  Defined.

  (** ** 2.4. The coherences *)
  Proposition finlim_to_comp_cat_functor_preserves_stable_el
    : comp_cat_functor_preserves_stable_el
        (finlim_to_comp_cat_univ_type el₁)
        (finlim_to_comp_cat_univ_type el₂)
        finlim_to_comp_cat_functor_preserves_el.
  Proof.
    intros Γ Δ s t.
    use eq_mor_cod_fib.
    refine (comp_in_cod_fib _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    refine (!_).
    refine (comp_in_cod_fib _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    etrans.
    {
      simpl.
      etrans.
      {
        apply maponpaths.
        apply finlim_comp_cat_el_map_on_eq.
      }
      rewrite !assoc'.
      rewrite cat_el_map_el_eq_comp.
      etrans.
      {
        apply maponpaths_2.
        exact (finlim_to_comp_cat_functor_coerce
                 F
                 (finlim_to_comp_cat_stable_el_map_mor el₁ s t)).
      }
      simpl.
      rewrite functor_comp.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply functor_el_map_iso_eq_alt.
      }
      rewrite assoc'.
      rewrite cat_el_map_el_eq_comp.
      rewrite assoc.
      apply idpath.
    }
    refine (!_).
    refine (assoc _ _ _ @ _).
    use z_iso_inv_to_right.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply cat_el_map_el_eq_inv.
    }
    rewrite !assoc'.
    rewrite cat_el_map_el_eq_comp.
    refine (!_).
    use (z_iso_inv_to_left
           _ _ _
           (functor_on_z_iso
              F
              (finlim_to_comp_cat_stable_el_map_mor_z_iso el₁ s t))).
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (cat_stable_el_map_pb _ _ _))).
    - rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        apply (PullbackArrow_PullbackPr1 (cat_stable_el_map_pb _ _ _)).
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr1.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply (finlim_to_comp_cat_functor_subst_ty_coe_pr1 F).
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (!(functor_comp _ _ _) @ _).
        apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        exact (functor_preserves_el_path Fu s (finlim_univ_tm_to_mor t)).
      }
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        use cat_el_map_pb_mor_eq.
        abstract
          (apply maponpaths ;
           apply functor_finlim_univ_tm_to_mor).
      }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      rewrite cat_el_map_el_eq_comp.
      apply cat_el_map_el_eq_eq.
    - rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        apply (PullbackArrow_PullbackPr2 (cat_stable_el_map_pb _ _ _)).
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr2.
      }
      etrans.
      {
        apply maponpaths.
        apply (finlim_to_comp_cat_functor_subst_ty_coe_pr2 F).
      }
      etrans.
      {
        refine (!(functor_comp _ _ _) @ _).
        apply maponpaths.
        apply PullbackArrow_PullbackPr2.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_mor_eq.
      }
      refine (!_).
      apply functor_el_map_comm.
  Qed.

  Definition finlim_to_comp_cat_functor_preserves_univ_type
    : comp_cat_functor_preserves_univ_type
        finlim_to_comp_cat_functor_ob
        (finlim_to_comp_cat_univ_type el₁)
        (finlim_to_comp_cat_univ_type el₂).
  Proof.
    use make_comp_cat_functor_preserves_univ_type.
    - exact finlim_to_comp_cat_functor_preserves_el.
    - exact finlim_to_comp_cat_functor_preserves_stable_el.
  Defined.
End UniverseInCodFunctor.

Arguments finlim_to_comp_cat_functor_ob_mor {C₁ C₂} F.
Arguments finlim_to_comp_cat_functor_ob {C₁ C₂} F.
Arguments finlim_to_comp_cat_functor_comp_cat_on_univ {C₁ C₂} F Γ.
Arguments functor_finlim_univ_tm_to_mor {C₁ C₂} F {Γ} t.

(** * 3. The action on 2-cells *)
Section UniverseInCodNatTrans.
  Context {C₁ C₂ : univ_cat_with_finlim_ob}
          {F G : functor_finlim_ob C₁ C₂}
          {τ : nat_trans_finlim_ob F G}
          {el₁ : cat_stable_el_map_coherent C₁}
          {el₂ : cat_stable_el_map_coherent C₂}
          {Fu : functor_preserves_el el₁ el₂ F}
          {Gu : functor_preserves_el el₁ el₂ G}
          (τu : nat_trans_preserves_el τ Fu Gu).

  Proposition finlim_to_comp_cat_nat_trans_ob
    : comp_cat_nat_trans_ob
        (finlim_to_comp_cat_functor_ob F)
        (finlim_to_comp_cat_functor_ob G).
  Proof.
    simple refine (_ ,, _).
    - apply (finlim_to_dfl_comp_cat_nat_trans τ).
    - abstract
        (use subtypePath ;
         [ intro ;
           apply homset_property
         | ] ;
         etrans ;
         [ apply transportf_cod_disp
         | ] ;
         exact (nat_trans_universe_eq τ)).
  Defined.

  Proposition finlim_to_comp_cat_nat_trans_preserves_univ_type
    : comp_cat_nat_trans_preserves_univ_type
        finlim_to_comp_cat_nat_trans_ob
        (finlim_to_comp_cat_functor_preserves_univ_type Fu)
        (finlim_to_comp_cat_functor_preserves_univ_type Gu).
  Proof.
    intros Γ t.
    use eq_mor_cod_fib.
    refine (comp_in_cod_fib _ _ @ _).
    refine (!_).
    etrans.
    {
      refine (comp_in_cod_fib _ _ @ _).
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    refine (assoc _ _ _ @ _).
    use z_iso_inv_to_right.
    use (MorphismsIntoPullbackEqual
           (isPullback_Pullback
              (cat_stable_el_map_pb el₂ _ _))).
    - do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        apply maponpaths.
        apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr1.
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply (finlim_to_comp_cat_fib_nat_trans_pr1 τ).
      }
      etrans.
      {
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        exact (τu Γ (finlim_univ_tm_to_mor t)).
      }
      simpl.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        use cat_el_map_pb_mor_eq.
        abstract
          (apply maponpaths ;
           apply (functor_finlim_univ_tm_to_mor G)).
      }
      refine (!_).
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply finlim_comp_cat_el_map_on_eq.
      }
      rewrite cat_el_map_el_eq_inv.
      rewrite !cat_el_map_el_eq_comp.
      apply cat_el_map_el_eq_eq.
    - do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        apply PullbackArrow_PullbackPr2.
      }
      etrans.
      {
        apply maponpaths.
        apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr2.
      }
      etrans.
      {
        apply (finlim_to_comp_cat_fib_nat_trans_pr2 τ).
      }
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply finlim_comp_cat_el_map_on_eq.
          }
          etrans.
          {
            apply maponpaths.
            apply cat_el_map_el_eq_inv.
          }
          apply cat_el_map_el_eq_comp.
        }
        apply cat_el_map_mor_eq.
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_mor_eq.
      }
      refine (!_).
      apply functor_el_map_comm.
  Qed.
End UniverseInCodNatTrans.

(** * 4. The identitor *)
Section UniverseIdentitor.
  Context {C : univ_cat_with_finlim_ob}
          (el : cat_stable_el_map_coherent C).

  Proposition finlim_to_comp_cat_identitor_ob
    : comp_cat_nat_trans_ob
        (identity _)
        (finlim_to_comp_cat_functor_ob (identity C)).
  Proof.
    simple refine (_ ,, _).
    - apply (finlim_to_dfl_comp_cat_identitor C).
    - abstract
        (use subtypePath ;
         [ intro ;
           apply homset_property
         | ] ;
         etrans ;
         [ apply transportf_cod_disp
         | ] ;
         simpl ;
         rewrite id_left ;
         rewrite pr1_transportf ;
         rewrite transportf_const ;
         apply idpath).
  Defined.

  Proposition finlim_to_comp_cat_identitor_ob_pr1
              {Γ : finlim_to_comp_cat_with_ob C}
              (A : ty Γ)
    : dom_mor (comp_cat_type_fib_nat_trans finlim_to_comp_cat_identitor_ob A)
      · PullbackPr1 _
      =
      identity _.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition finlim_to_comp_cat_identitor_ob_pr2
              {Γ : finlim_to_comp_cat_with_ob C}
              (A : ty Γ)
    : dom_mor (comp_cat_type_fib_nat_trans finlim_to_comp_cat_identitor_ob A)
      · PullbackPr2 _
      =
      cod_mor A.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply id_right.
  Qed.

  Proposition comp_cat_functor_preserves_univ_type_el_mor_on_id
              {Γ : finlim_to_comp_cat_with_ob C}
              (t : tm Γ (comp_cat_univ Γ))
    : dom_mor
        (comp_cat_functor_preserves_univ_type_el_mor
           (id_comp_cat_functor_preserves_univ_type (finlim_to_comp_cat_univ_type el))
           t)
      =
      cat_el_map_el_eq
        _
        (maponpaths
           finlim_univ_tm_to_mor
           (id_comp_cat_functor_preserves_el_lem
              (finlim_to_comp_cat_univ_type el)
              t)).
  Proof.
    unfold comp_cat_functor_preserves_univ_type_el_mor.
    simpl.
    unfold id_comp_cat_functor_preserves_el.
    apply finlim_comp_cat_el_map_on_eq.
  Qed.

  Proposition finlim_to_comp_cat_identitor_preserves_univ_type
    : comp_cat_nat_trans_preserves_univ_type
        finlim_to_comp_cat_identitor_ob
        (id_comp_cat_functor_preserves_univ_type _)
        (finlim_to_comp_cat_functor_preserves_univ_type (id_functor_preserves_el el)).
  Proof.
    intros Γ t.
    use eq_mor_cod_fib.
    refine (comp_in_cod_fib _ _ @ _).
    refine (!_).
    etrans.
    {
      refine (comp_in_cod_fib _ _ @ _).
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    refine (assoc _ _ _ @ _).
    use z_iso_inv_to_right.
    use (MorphismsIntoPullbackEqual
           (isPullback_Pullback
              (cat_stable_el_map_pb el _ _))).
    - do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        apply maponpaths.
        apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr1.
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply finlim_to_comp_cat_identitor_ob_pr1.
      }
      refine (id_left _ @ _).
      etrans.
      {
        apply cat_el_map_el_eq_comp.
      }
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply finlim_comp_cat_el_map_on_eq.
        }
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply cat_el_map_el_eq_inv.
        }
        apply maponpaths_2.
        apply cat_el_map_el_eq_comp.
      }
      etrans.
      {
        apply maponpaths_2.
        apply comp_cat_functor_preserves_univ_type_el_mor_on_id.
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply cat_el_map_el_eq_comp.
      }
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_pb_mor_id.
      }
      refine (cat_el_map_el_eq_comp _ _ _ @ _).
      apply cat_el_map_el_eq_eq.
    - do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        apply PullbackArrow_PullbackPr2.
      }
      etrans.
      {
        apply maponpaths.
        apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr2.
      }
      etrans.
      {
        apply finlim_to_comp_cat_identitor_ob_pr2.
      }
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            apply finlim_comp_cat_el_map_on_eq.
          }
          etrans.
          {
            apply maponpaths.
            apply cat_el_map_el_eq_inv.
          }
          apply cat_el_map_el_eq_comp.
        }
        apply cat_el_map_mor_eq.
      }
      etrans.
      {
        apply maponpaths_2.
        apply comp_cat_functor_preserves_univ_type_el_mor_on_id.
      }
      apply cat_el_map_mor_eq.
  Qed.
End UniverseIdentitor.

(** * 5. The compositor *)
Section UniverseCompositor.
  Context {C₁ C₂ C₃ : univ_cat_with_finlim_ob}
          {F : functor_finlim_ob C₁ C₂}
          {G : functor_finlim_ob C₂ C₃}
          {el₁  : cat_stable_el_map_coherent C₁}
          {el₂  : cat_stable_el_map_coherent C₂}
          {el₃  : cat_stable_el_map_coherent C₃}
          (Fu : functor_preserves_el el₁ el₂ F)
          (Gu : functor_preserves_el el₂ el₃ G).

  Proposition finlim_to_comp_cat_compositor_ob
    : comp_cat_nat_trans_ob
        (finlim_to_comp_cat_functor_ob F · finlim_to_comp_cat_functor_ob G)
        (finlim_to_comp_cat_functor_ob (F · G)).
  Proof.
    simple refine (_ ,, _).
    - apply (finlim_to_dfl_comp_cat_compositor F G).
    - abstract
        (use subtypePath ;
         [ intro ;
           apply homset_property
         | ] ;
         etrans ;
         [ apply transportf_cod_disp
         | ] ;
         simpl ;
         rewrite id_left ;
         rewrite pr1_transportf ;
         rewrite transportf_const ;
         apply idpath).
  Defined.

  Proposition finlim_to_comp_cat_compositor_ob_pr1
              {Γ : finlim_to_comp_cat_with_ob C₁}
              (A : ty Γ)
    : dom_mor (comp_cat_type_fib_nat_trans finlim_to_comp_cat_compositor_ob A)
      · PullbackPr1 _
      =
      identity _.
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr1 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply transportf_cod_disp.
  Qed.

  Proposition finlim_to_comp_cat_compositor_ob_pr2
              {Γ : finlim_to_comp_cat_with_ob C₁}
              (A : ty Γ)
    : dom_mor (comp_cat_type_fib_nat_trans finlim_to_comp_cat_compositor_ob A)
      · PullbackPr2 _
      =
      #G(#F(cod_mor A)).
  Proof.
    etrans.
    {
      apply (PullbackArrow_PullbackPr2 (pullbacks_univ_cat_with_finlim _ _ _ _ _ _)).
    }
    apply id_right.
  Qed.

  Proposition finlim_to_comp_cat_compositor_preserves_univ_type
    : comp_cat_nat_trans_preserves_univ_type
        finlim_to_comp_cat_compositor_ob
        (comp_comp_cat_functor_preserves_univ_type
           (finlim_to_comp_cat_functor_preserves_univ_type Fu)
           (finlim_to_comp_cat_functor_preserves_univ_type Gu))
        (finlim_to_comp_cat_functor_preserves_univ_type
           (comp_functor_preserves_el Fu Gu)).
  Proof.
    intros Γ t.
    use eq_mor_cod_fib.
    refine (comp_in_cod_fib _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (eq_comp_comp_cat_functor_preserves_univ
                   (finlim_to_comp_cat_functor_preserves_univ_type Fu)
                   (finlim_to_comp_cat_functor_preserves_univ_type Gu)
                   t).
      }
      refine (comp_in_cod_fib _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply comp_in_cod_fib.
      }
      etrans.
      {
        apply maponpaths.
        apply finlim_comp_cat_el_map_on_eq.
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply (finlim_to_comp_cat_functor_coerce G).
      }
      etrans.
      {
        apply maponpaths_2.
        apply functor_comp.
      }
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (functor_on_cat_el_map_el_eq Gu).
      }
      do 2 refine (assoc' _ _ _ @ _).
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      refine (comp_in_cod_fib _ _ @ _).
      apply maponpaths_2.
      apply comp_in_cod_fib.
    }
    refine (assoc _ _ _ @ _).
    use z_iso_inv_to_right.
    use (MorphismsIntoPullbackEqual
           (isPullback_Pullback
              (cat_stable_el_map_pb el₃ _ _))).
    - do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        apply PullbackArrow_PullbackPr1.
      }
      etrans.
      {
        apply maponpaths.
        apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr1.
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply finlim_to_comp_cat_compositor_ob_pr1.
      }
      refine (id_left _ @ _).
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        apply cat_el_map_el_eq_comp.
      }
      refine (!_).
      do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        apply cat_el_map_el_eq_inv.
      }
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply finlim_comp_cat_el_map_on_eq.
      }
      etrans.
      {
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply cat_el_map_el_eq_comp.
      }
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      etrans.
      {
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc' _ _ _ @ _).
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply cat_el_map_el_eq_comp.
      }
      etrans.
      {
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply z_iso_after_z_iso_inv.
      }
      rewrite id_left.
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply cat_el_map_el_eq_comp.
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply cat_el_map_el_eq_comp.
      }
      etrans.
      {
        apply maponpaths.
        apply cat_el_map_pb_mor_id.
      }
      refine (cat_el_map_el_eq_comp _ _ _ @ _).
      apply cat_el_map_el_eq_eq.
    - do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        apply PullbackArrow_PullbackPr2.
      }
      etrans.
      {
        apply maponpaths.
        apply finlim_to_comp_cat_coerce_subst_ty_pullback_pr2.
      }
      etrans.
      {
        apply finlim_to_comp_cat_compositor_ob_pr2.
      }
      refine (!_).
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        do 4 apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply z_iso_after_z_iso_inv.
        }
        apply id_left.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        etrans.
        {
          do 4 apply maponpaths_2.
          apply cat_el_map_el_eq_comp.
        }
        etrans.
        {
          do 3 apply maponpaths_2.
          apply cat_el_map_el_eq_comp.
        }
        etrans.
        {
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply finlim_comp_cat_el_map_on_eq.
          }
          apply cat_el_map_el_eq_comp.
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            apply cat_el_map_el_eq_inv.
          }
          apply cat_el_map_el_eq_comp.
        }
        apply cat_el_map_mor_eq.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply functor_el_map_comm.
      }
      refine (!(functor_comp _ _ _) @ _).
      apply maponpaths.
      refine (!_).
      apply functor_el_map_comm.
  Qed.
End UniverseCompositor.

(** * 6. The displayed pseudofunctor *)
Definition finlim_to_dfl_comp_cat_disp_psfunctor_universe
  : disp_psfunctor
      disp_bicat_finlim_universe
      disp_bicat_dfl_full_comp_cat_with_univ
      finlim_to_dfl_comp_cat_psfunctor.
Proof.
  use make_disp_psfunctor.
  - exact disp_2cells_isaprop_disp_bicat_dfl_full_comp_cat_with_univ.
  - exact disp_locally_groupoid_disp_bicat_dfl_full_comp_cat_with_univ.
  - intros C u.
    refine (_ ,, _).
    exact (finlim_to_comp_cat_univ_type (pr2 u)).
  - intros C₁ C₂ F u₁ u₂ Fu.
    refine (_ ,, _).
    exact (finlim_to_comp_cat_functor_preserves_univ_type (pr2 Fu)).
  - intros C₁ C₂ F₁ F₂ τ u₁ u₂ Fu Gu τu.
    refine (_ ,, _).
    exact (finlim_to_comp_cat_nat_trans_preserves_univ_type (pr2 τu)).
  - intros C u.
    refine (_ ,, _).
    exact (finlim_to_comp_cat_identitor_preserves_univ_type (pr2 u)).
  - intros C₁ C₂ C₃ F G u₁ u₂ u₃ Fu Gu.
    refine (_ ,, _).
    exact (finlim_to_comp_cat_compositor_preserves_univ_type (pr2 Fu) (pr2 Gu)).
Defined.
