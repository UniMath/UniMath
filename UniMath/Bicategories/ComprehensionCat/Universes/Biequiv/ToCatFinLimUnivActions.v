(**

 From comprehension categories with a universe to categories with a universe

 Our goal is to define a pseudofunctor from the bicategory of (DFL, full, univalent)
 comprehension categories with a universe to the bicategory of univalent categories with
 finite limits and a universe. This is one of the necessary ingredients to extend the
 biequivalence between DFL full comprehension categories and categories with finite limits
 to universes.

 To construct the desired pseudofunctor, we construct a displayed pseudofunctor over the
 pseudofunctor from DFL comprehension categories to categories with finite limits maps. This
 pseudofunctor maps every DFL comprehension category to its category of contexts. As such.
 it suffices to show that whenever a comprehension category `χ : D ⟶ C^→` is equipped with
 a universe, then we can equip the category `C` of contexts with a universe type. Similarly,
 we must show that functors between DFL comprehension categories preserve universe types and
 that natural transformations satisfy a suitable coherence condition.

 To get insight in the construction, let's look at some details. A universe in the
 comprehension category `χ : D ⟶ C^→` gives us a type `u : ty []` in the empty context. By
 using the comprehension functor, we obtain a morphism `χ u : dom(χ u) --> []` to the empty
 context. The domain of this morphism is the universe object in `C`. The next important
 observation is that terms of type `u` in context `Γ` are the same as morphisms from `Γ` to
 `χ u` (note that, technically, we need to talk about a term of type `u [[ ! ]]` where `!` is
 the unique map from `Γ` to the empty context). To understand why, note that we have the
 following pullback square

<<

    Γ & u [[ ! ]] -----> dom(χ u)
       |                   |
     π |                   | χ u
       |                   |
       V                   V
       Γ ---------------> []
           !
>>

 Terms of type `u [[ ! ]]` are sections of the projection `π` displayed in the diagram. As
 a result, terms of type `u [[ ! ]]` are the same as morphisms from `Γ` to `dom(χ u)`. This
 correspondence allows us to show that every morphism `Γ --> dom(χ u)` gives rise to a
 morphism to `Γ`. A morphism `Γ --> dom(χ u)` gives rise to a term `u [[ ! ]]` in context `Γ`,
 which gives rise to a type in context `Γ` and that type gives us a morphism to `Γ` via `χ`.
 The main technical work lies in establishing the necessary coherences.

 This file defines the actions on objects and 1-cells of the desired pseudofunctor. The
 construction has been split up so that the resulting files are smaller and so that they
 can be compiled concurrently.

 Contents
 1. Action on objects
 1.1. Construction of the universe object
 1.2. Terms of the universe type versus morphisms
 1.3. The type associated to a term of the universe
 1.4. Calculational lemmas
 1.5. Stability of the type associated to a term of the universe
 1.6. Coherence of the stability isomorphisms
 2. Action on 1-cells
 2.1. Preservation of the universe object
 2.2. Preservation of the associated type
 2.3. Coherences

                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
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
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Action on objects *)
Section ToFinLimUniv.
  Context {C : dfl_full_comp_cat}
          (u : ty ([] : C)).

  Let Cu : comp_cat_with_ob := pr11 C ,, u.

  Context (el : comp_cat_univ_type Cu).

  (** ** 1.1. Construction of the universe object *)
  Definition dfl_full_comp_cat_to_finlim_ob
    : C
    := [] & u.

  Let CCu : univ_cat_with_finlim_ob
    := dfl_full_comp_cat_to_finlim C ,, dfl_full_comp_cat_to_finlim_ob.

  (** ** 1.2. Terms of the universe type versus morphisms *)
  Definition dfl_full_comp_cat_mor_to_tm_univ
             {Γ : Cu}
             (t : Γ --> [] & u)
    : tm Γ (comp_cat_univ Γ).
  Proof.
    use make_comp_cat_tm.
    - use (PullbackArrow (comp_cat_pullback _ _)).
      + exact t.
      + apply identity.
      + abstract
          (apply TerminalArrowEq).
    - abstract
        (apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _))).
  Defined.

  Definition dfl_full_comp_cat_tm_to_mor_univ
             {Γ : Cu}
             (t : tm Γ (comp_cat_univ Γ))
    : Γ --> [] & u
    := t · PullbackPr1 (comp_cat_pullback _ _).

  Proposition dfl_full_comp_cat_mor_to_tm_to_mor_univ
              {Γ : Cu}
              (t : Γ --> [] & u)
    : dfl_full_comp_cat_tm_to_mor_univ (dfl_full_comp_cat_mor_to_tm_univ t) = t.
  Proof.
    unfold dfl_full_comp_cat_mor_to_tm_univ, dfl_full_comp_cat_tm_to_mor_univ.
    cbn.
    apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
  Qed.

  Proposition dfl_full_comp_cat_tm_to_mor_to_tm_univ
              {Γ : Cu}
              (t : tm Γ (comp_cat_univ Γ))
    : dfl_full_comp_cat_mor_to_tm_univ (dfl_full_comp_cat_tm_to_mor_univ t) = t.
  Proof.
    use eq_comp_cat_tm ; cbn.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback _ _))).
    - apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
    - rewrite (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _)).
      cbn.
      exact (!(comp_cat_tm_eq t)).
  Qed.

  Definition dfl_full_comp_cat_mor_weq_tm_univ
             (Γ : Cu)
    : (Γ --> [] & u) ≃ tm Γ (comp_cat_univ Γ).
  Proof.
    use weq_iso.
    - exact dfl_full_comp_cat_mor_to_tm_univ.
    - exact dfl_full_comp_cat_tm_to_mor_univ.
    - exact dfl_full_comp_cat_mor_to_tm_to_mor_univ.
    - exact dfl_full_comp_cat_tm_to_mor_to_tm_univ.
  Defined.

  (** ** 1.3. The type associated to a term of the universe *)
  Definition dfl_full_comp_cat_to_finlim_el_map
    : cat_el_map CCu.
  Proof.
    intros Γ t.
    simple refine (_ ,, _).
    - exact (Γ & comp_cat_univ_el el (dfl_full_comp_cat_mor_to_tm_univ t)).
    - exact (π _).
  Defined.

  (** ** 1.4. Calculational lemmas *)
  Proposition dfl_full_comp_cat_cat_el_map_el_eq
              {Γ : Cu}
              {t₁ t₂ : Γ --> univ_cat_universe CCu}
              (p : t₁ = t₂)
    : (cat_el_map_el_eq
         dfl_full_comp_cat_to_finlim_el_map
         p : _ --> _)
      =
      comprehension_functor_mor
        (comp_cat_comprehension C)
        (comp_cat_el_map_on_eq el (maponpaths _ p)).
  Proof.
    induction p.
    cbn.
    rewrite comprehension_functor_mor_id.
    apply idpath.
  Qed.

  (**
     Every morphism gives rise to a term. In the following lemma, we simplify how
     this acts on the composition of morphisms, and we relate it to substitution
     of terms.
   *)
  Proposition sub_comp_cat_univ_cleaving_of_types
              {Γ Δ : Cu}
              (s : Γ --> Δ)
    : (sub_comp_cat_univ s ;; cleaving_of_types _ _ _ _ _)%mor_disp
      =
      transportf
        (λ z, _ -->[ z ] _)
        (TerminalArrowEq _ _)
        (cleaving_of_types _ _ _ _ _ ;; cleaving_of_types _ _ _ _ _)%mor_disp.
  Proof.
    cbn -[eq_subst_ty_iso].
    rewrite mor_disp_transportf_postwhisker.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      apply subst_ty_eq_disp_iso_comm.
    }
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  Qed.

  Proposition dfl_full_comp_cat_mor_to_sub_tm
              {Γ Δ : Cu}
              (s : Γ --> Δ)
              (t : Δ --> [] & u)
    : dfl_full_comp_cat_mor_to_tm_univ t [[ s ]]tm ↑ sub_comp_cat_univ s
      =
      dfl_full_comp_cat_mor_to_tm_univ (s · t).
  Proof.
    use eq_comp_cat_tm.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback _ _))).
    - refine (_ @ !(PullbackArrow_PullbackPr1 (comp_cat_pullback _ _) _ _ _ _)).
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply comprehension_functor_mor_comp.
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply sub_comp_cat_univ_cleaving_of_types.
      }
      rewrite comprehension_functor_mor_transportf.
      cbn.
      etrans.
      {
        apply maponpaths.
        apply comprehension_functor_mor_comp.
      }
      rewrite !assoc.
      etrans.
      {
        apply maponpaths_2.
        apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
      }
      rewrite !assoc'.
      apply maponpaths.
      apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
    - refine (_ @ !(PullbackArrow_PullbackPr2 (comp_cat_pullback _ _) _ _ _ _)).
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply comp_cat_comp_mor_comm.
      }
      apply comp_cat_tm_eq.
  Qed.

  (** ** 1.5. Stability of the type associated to a term of the universe *)
  Section Stability.
    Context {Γ Δ : CCu}
            (s : Γ --> Δ)
            (t : Δ --> univ_cat_universe CCu).

    Definition dfl_full_comp_cat_to_finlim_el_map_stable_mor
      : cat_el_map_el dfl_full_comp_cat_to_finlim_el_map (s · t)
        -->
        cat_el_map_el dfl_full_comp_cat_to_finlim_el_map t.
    Proof.
      simple refine (comprehension_functor_mor (comp_cat_comprehension C) _).
      - exact s.
      - refine (transportf
                  _
                  _
                  (comp_cat_el_map_on_eq el (!dfl_full_comp_cat_mor_to_sub_tm s t)
                   ;;
                   comp_cat_univ_el_stable_inv el s (dfl_full_comp_cat_mor_to_tm_univ t)
                   ;;
                   comp_cat_subst _ _)%mor_disp).
        abstract
          (rewrite !id_left ;
           apply idpath).
    Defined.

    Definition dfl_full_comp_cat_to_finlim_el_map_stable_z_iso
      : z_iso
          (comp_cat_pullback
             (comp_cat_univ_el el (dfl_full_comp_cat_mor_to_tm_univ t))
             s)
          (cat_el_map_el dfl_full_comp_cat_to_finlim_el_map (s · t))
      := comp_cat_comp_fiber_z_iso
           (z_iso_comp
              (comp_cat_univ_el_stable el s (dfl_full_comp_cat_mor_to_tm_univ t))
              (comp_cat_el_map_on_eq_iso el (dfl_full_comp_cat_mor_to_sub_tm s t))).

    Proposition dfl_full_comp_cat_to_finlim_el_map_stable_comm
      : dfl_full_comp_cat_to_finlim_el_map_stable_z_iso
        · dfl_full_comp_cat_to_finlim_el_map_stable_mor
        =
        PullbackPr1 _.
    Proof.
      cbn.
      refine (!(comprehension_functor_mor_comp _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        rewrite mor_disp_transportf_prewhisker.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite !assoc_disp_var.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc_disp.
          unfold transportb.
          rewrite transport_f_f.
          apply maponpaths.
          do 2 apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            exact (comp_cat_el_map_on_inv el (dfl_full_comp_cat_mor_to_sub_tm s t)).
          }
          exact (inv_mor_after_z_iso_disp
                   (z_iso_disp_from_z_iso_fiber
                      _ _ _ _
                      (comp_cat_el_map_on_eq_iso
                         el
                         (dfl_full_comp_cat_mor_to_sub_tm s t)))).
        }
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        rewrite id_left_disp.
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        rewrite assoc_disp.
        unfold transportb.
        rewrite transport_f_f.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (inv_mor_after_z_iso_disp
                   (z_iso_disp_from_z_iso_fiber
                      _ _ _ _
                      (comp_cat_univ_el_stable el s (dfl_full_comp_cat_mor_to_tm_univ t)))).
        }
        unfold transportb.
        rewrite mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite id_left_disp.
        unfold transportb.
        rewrite transport_f_f.
        apply idpath.
      }
      rewrite comprehension_functor_mor_transportf.
      apply idpath.
    Qed.
  End Stability.

  Definition dfl_full_comp_cat_to_finlim_el_map_stable
    : cat_el_map_stable dfl_full_comp_cat_to_finlim_el_map.
  Proof.
    intros Γ Δ s t.
    simple refine (_ ,, _ ,, _).
    - exact (dfl_full_comp_cat_to_finlim_el_map_stable_mor s t).
    - abstract
        (apply comprehension_functor_mor_comm).
    - use (isPullback_z_iso
           _
           _
           (isPullback_Pullback
              (comp_cat_pullback
                 (comp_cat_univ_el el (dfl_full_comp_cat_mor_to_tm_univ t)) s))).
      + exact (dfl_full_comp_cat_to_finlim_el_map_stable_z_iso s t).
      + exact (dfl_full_comp_cat_to_finlim_el_map_stable_comm s t).
      + abstract
          (apply comp_cat_comp_mor_comm).
  Defined.

  Definition dfl_full_comp_cat_to_finlim_stable_el_map
    : cat_stable_el_map CCu.
  Proof.
    use make_cat_stable_el_map.
    - exact dfl_full_comp_cat_to_finlim_el_map.
    - exact dfl_full_comp_cat_to_finlim_el_map_stable.
  Defined.

  (** ** 1.6. Coherence of the stability isomorphisms *)
  Proposition dfl_full_comp_cat_to_finlim_is_coherent_stable_el_map
    : is_coherent_cat_stable_el_map
        dfl_full_comp_cat_to_finlim_stable_el_map.
  Proof.
    split.
    - intros Γ t.
      unfold cat_el_map_pb_mor.
      cbn.
      unfold dfl_full_comp_cat_to_finlim_el_map_stable_mor.
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        exact (comp_cat_univ_el_stable_id_coh_inv el (dfl_full_comp_cat_mor_to_tm_univ t)).
      }
      cbn -[id_subst_ty].
      rewrite mor_disp_transportf_prewhisker.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite comprehension_functor_mor_transportf.
      rewrite assoc_disp_var.
      rewrite comprehension_functor_mor_transportf.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        do 3 apply maponpaths.
        apply cartesian_factorisation_commutes.
      }
      unfold transportb.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      rewrite id_right_disp.
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite comprehension_functor_mor_transportf.
      etrans.
      {
        apply maponpaths.
        apply (comp_cat_el_map_on_disp_concat el).
      }
      rewrite comprehension_functor_mor_transportf.
      refine (_ @ !(dfl_full_comp_cat_cat_el_map_el_eq _)).
      apply maponpaths.
      apply (eq_comp_cat_el_map_on_eq el).
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
      unfold cat_el_map_pb_mor.
      cbn.
      unfold dfl_full_comp_cat_to_finlim_el_map_stable_mor.
      etrans.
      {
        apply comprehension_functor_mor_transportf.
      }
      refine (!_).
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply comprehension_functor_mor_transportf.
        }
        etrans.
        {
          apply maponpaths_2.
          apply comprehension_functor_mor_transportf.
        }
        refine (!_).
        apply comprehension_functor_mor_comp.
      }
      etrans.
      {
        apply maponpaths_2.
        apply dfl_full_comp_cat_cat_el_map_el_eq.
      }
      etrans.
      {
        refine (!_).
        apply comprehension_functor_mor_comp.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply (comp_cat_univ_el_stable_comp_coh_inv el).
      }
      etrans.
      {
        cbn -[coerce_subst_ty comp_subst_ty sub_comp_cat_univ].
        rewrite !assoc_disp_var.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        rewrite mor_disp_transportf_prewhisker.
        rewrite transport_f_f.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        rewrite !assoc_disp_var.
        rewrite !mor_disp_transportf_prewhisker.
        rewrite !transport_f_f.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        etrans.
        {
          do 5 apply maponpaths.
          apply cartesian_factorisation_commutes.
        }
        unfold transportb.
        rewrite !mor_disp_transportf_prewhisker.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        etrans.
        {
          do 4 apply maponpaths.
          rewrite assoc_disp.
          apply maponpaths.
          apply maponpaths_2.
          apply cartesian_factorisation_commutes.
        }
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite transport_f_f.
        rewrite !mor_disp_transportf_prewhisker.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        rewrite !assoc_disp.
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          do 4 apply maponpaths_2.
          apply (comp_cat_el_map_on_disp_concat el).
        }
        rewrite !mor_disp_transportf_postwhisker.
        apply comprehension_functor_mor_transportf.
      }
      refine (!_).
      etrans.
      {
        rewrite !assoc_disp.
        unfold transportb.
        rewrite !mor_disp_transportf_postwhisker.
        rewrite !transport_f_f.
        apply comprehension_functor_mor_transportf.
      }
      refine (comprehension_functor_mor_comp _ _ _ @ _).
      refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
      apply maponpaths_2.
      refine (comprehension_functor_mor_comp _ _ _ @ _).
      refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc_disp_var.
        rewrite !transport_f_f.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        etrans.
        {
          do 4 apply maponpaths.
          apply (comp_cat_subst_natural el).
        }
        rewrite !mor_disp_transportf_prewhisker.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        rewrite !assoc_disp.
        unfold transportb.
        rewrite !transport_f_f.
        apply comprehension_functor_mor_transportf.
      }
      refine (comprehension_functor_mor_comp _ _ _ @ _).
      refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
      apply maponpaths_2.
      etrans.
      {
        rewrite !assoc_disp_var.
        rewrite !transport_f_f.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        etrans.
        {
          do 3 apply maponpaths.
          apply (comp_cat_univ_el_stable_natural_inv_disp el).
        }
        rewrite !mor_disp_transportf_prewhisker.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        rewrite !assoc_disp.
        unfold transportb.
        rewrite !transport_f_f.
        apply comprehension_functor_mor_transportf.
      }
      refine (comprehension_functor_mor_comp _ _ _ @ _).
      refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (comp_cat_el_map_on_disp_concat el).
      }
      rewrite mor_disp_transportf_postwhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply (comp_cat_el_map_on_disp_concat el).
      }
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      apply maponpaths.
      apply (eq_comp_cat_el_map_on_eq el).
  Qed.

  Definition dfl_full_comp_cat_to_finlim_stable_el_map_coherent
    : cat_stable_el_map_coherent CCu.
  Proof.
    use make_cat_stable_el_map_coherent.
    - exact dfl_full_comp_cat_to_finlim_stable_el_map.
    - exact dfl_full_comp_cat_to_finlim_is_coherent_stable_el_map.
  Defined.
End ToFinLimUniv.

(** * 2. Action on 1-cells *)
Section ToFunctorFinLimUniv.
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

  Context {el₁ : comp_cat_univ_type Cu₁}
          {el₂ : comp_cat_univ_type Cu₂}
          (F_u : z_iso_disp
                  (comp_cat_functor_empty_context_z_iso F)
                  (comp_cat_type_functor F [] u₁)
                  u₂).

  Let Fu : comp_cat_functor_ob Cu₁ Cu₂ := pr11 F ,, F_u.

  Context (Fel : comp_cat_functor_preserves_univ_type Fu el₁ el₂).

  (** * 2.1. Preservation of the universe object *)
  Definition dfl_full_comp_cat_functor_preserves_ob_F_iso
    : z_iso (F [] & comp_cat_type_functor F [] u₁) ([] & u₂).
  Proof.
    use make_z_iso.
    - exact (comprehension_functor_mor _ F_u).
    - exact (comprehension_functor_mor _ (inv_mor_disp_from_z_iso F_u)).
    - split.
      + abstract
          (refine (!(comprehension_functor_mor_comp _ _ _) @ _) ;
           refine (_ @ comprehension_functor_mor_id _ _) ;
           rewrite inv_mor_after_z_iso_disp ;
           apply comprehension_functor_mor_transportf).
      + abstract
          (refine (!(comprehension_functor_mor_comp _ _ _) @ _) ;
           refine (_ @ comprehension_functor_mor_id _ _) ;
           rewrite z_iso_disp_after_inv_mor ;
           apply comprehension_functor_mor_transportf).
  Defined.

  Let Fi : z_iso (F [] & comp_cat_type_functor F [] u₁) ([] & u₂)
    := dfl_full_comp_cat_functor_preserves_ob_F_iso.

  Definition dfl_full_comp_cat_functor_preserves_ob
    : z_iso (F ([] & u₁)) ([] & u₂)
    := z_iso_comp
         (comp_cat_functor_extension F _ _)
         Fi.

  Definition dfl_full_comp_cat_functor_finlim_ob
    : functor_finlim_ob CCu₁ CCu₂
    := dfl_functor_comp_cat_to_finlim_functor F
       ,,
       dfl_full_comp_cat_functor_preserves_ob.

  Arguments dfl_full_comp_cat_functor_finlim_ob /.

  Let Fob : functor_finlim_ob CCu₁ CCu₂
    := dfl_full_comp_cat_functor_finlim_ob.

  (** * 2.2. Preservation of the associated type *)
  Section PreservesElMap.
    Context {Γ : Cu₁}
            (t : Γ --> dfl_full_comp_cat_to_finlim_ob u₁).

    Let tu : tm Γ (comp_cat_univ Γ)
      := dfl_full_comp_cat_mor_to_tm_univ _ t.

    Proposition dfl_full_comp_cat_functor_preserves_el_map_eq
      : comp_cat_functor_tm Fu
          (dfl_full_comp_cat_mor_to_tm_univ u₁ t)
        ↑ functor_comp_cat_on_univ Fu Γ
        =
        dfl_full_comp_cat_mor_to_tm_univ
          u₂
          (# F t
           · (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) u₁
           · comprehension_functor_mor (comp_cat_comprehension C₂) F_u)).
    Proof.
      use eq_comp_cat_tm.
      simpl.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback (comp_cat_pullback _ _))).
      - rewrite PullbackArrow_PullbackPr1.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          refine (!(comprehension_functor_mor_comp _ _ _) @ _).
          unfold functor_comp_cat_on_univ, functor_comp_cat_on_univ_z_iso.
          cbn -[subst_ty_eq_disp_iso].
          rewrite mor_disp_transportf_postwhisker.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          rewrite !assoc_disp_var.
          rewrite mor_disp_transportf_prewhisker.
          rewrite !transport_f_f.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          etrans.
          {
            do 3 apply maponpaths.
            apply subst_ty_eq_disp_iso_comm.
          }
          rewrite !mor_disp_transportf_prewhisker.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          rewrite cartesian_factorisation_commutes.
          rewrite mor_disp_transportf_prewhisker.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          etrans.
          {
            apply maponpaths.
            rewrite assoc_disp.
            apply maponpaths.
            apply maponpaths_2.
            apply cartesian_factorisation_commutes.
          }
          unfold transportb.
          rewrite mor_disp_transportf_postwhisker.
          rewrite transport_f_f.
          refine (comprehension_functor_mor_transportf _ _ _ @ _).
          apply comprehension_functor_mor_comp.
        }
        etrans.
        {
          apply maponpaths.
          rewrite assoc.
          apply maponpaths_2.
          refine (!_).
          apply comprehension_nat_trans_comm.
        }
        rewrite !assoc.
        rewrite <- functor_comp.
        do 2 apply maponpaths_2.
        apply maponpaths.
        apply (PullbackArrow_PullbackPr1 (comp_cat_pullback _ _)).
      - rewrite PullbackArrow_PullbackPr2.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          apply comp_cat_comp_mor_comm.
        }
        etrans.
        {
          apply maponpaths.
          apply comprehension_nat_trans_mor_comm.
        }
        rewrite <- functor_comp, <- functor_id.
        apply maponpaths.
        apply (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _)).
    Qed.

    Definition dfl_full_comp_cat_functor_preserves_el_map_iso
      : z_iso
          (F (Γ & comp_cat_univ_el el₁ tu))
          (F Γ & comp_cat_univ_el
                   el₂
                   (dfl_full_comp_cat_mor_to_tm_univ u₂
                      (# F t
                       · (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) u₁
                       · comprehension_functor_mor (comp_cat_comprehension C₂) F_u)))).
    Proof.
      refine (z_iso_comp
                (comp_cat_functor_extension F _ _)
                _).
      use comp_cat_comp_z_iso.
      use z_iso_disp_from_z_iso_fiber.
      refine (z_iso_comp
                (comp_cat_functor_preserves_univ_type_el_iso
                   Fel
                   (dfl_full_comp_cat_mor_to_tm_univ _ t))
                _).
      use comp_cat_el_map_on_eq_iso.
      exact dfl_full_comp_cat_functor_preserves_el_map_eq.
    Defined.

    Proposition dfl_full_comp_cat_functor_preserves_el_map_comm
      : #F (cat_el_map_mor (dfl_full_comp_cat_to_finlim_el_map u₁ el₁) t)
        =
        comprehension_nat_trans_mor
          (comp_cat_functor_comprehension F)
          (comp_cat_univ_el el₁ tu)
        · comprehension_functor_mor
            _
            (comp_cat_functor_preserves_univ_type_el_iso
               Fel
               (dfl_full_comp_cat_mor_to_tm_univ u₁ t)
             · comp_cat_el_map_on_eq_iso
                 _
                 dfl_full_comp_cat_functor_preserves_el_map_eq)
        · cat_el_map_mor
            (dfl_full_comp_cat_to_finlim_el_map u₂ el₂)
            (# F t
             · (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) u₁
             · comprehension_functor_mor (comp_cat_comprehension C₂) F_u)).
    Proof.
      refine (!_).
      etrans.
      {
        rewrite !assoc'.
        apply maponpaths.
        apply comprehension_functor_mor_comm.
      }
      rewrite id_right.
      apply comprehension_nat_trans_mor_comm.
    Qed.
  End PreservesElMap.

  Definition dfl_full_comp_cat_functor_preserves_el_map
    : functor_el_map
        (dfl_full_comp_cat_to_finlim_stable_el_map u₁ el₁)
        (dfl_full_comp_cat_to_finlim_stable_el_map u₂ el₂)
        Fob.
  Proof.
    intros Γ t.
    simple refine (_ ,, _).
    - exact (dfl_full_comp_cat_functor_preserves_el_map_iso t).
    - exact (dfl_full_comp_cat_functor_preserves_el_map_comm t).
  Defined.

  Proposition dfl_full_comp_cat_functor_preserves_el_map_on_iso
              {Γ : Cu₁}
              (t : Γ --> dfl_full_comp_cat_to_finlim_ob u₁)
    : pr1 (functor_el_map_iso dfl_full_comp_cat_functor_preserves_el_map t)
      =
      comprehension_nat_trans_mor (comp_cat_functor_comprehension F) _
      · comprehension_functor_mor
          (comp_cat_comprehension C₂)
          (pr1 (comp_cat_functor_preserves_univ_type_el_iso
                  Fel
                  (dfl_full_comp_cat_mor_to_tm_univ u₁ t))
           ;; pr1 (comp_cat_el_map_on_eq_iso el₂
                     (dfl_full_comp_cat_functor_preserves_el_map_eq t)))%mor_disp.
  Proof.
    simpl.
    apply maponpaths.
    apply comprehension_functor_mor_transportf.
  Qed.

  (** * 2.3. Coherences *)
  Lemma dfl_full_comp_cat_functor_stable_el_map_lemma
        {Γ Δ : C₁}
        (s : Γ --> Δ)
        (t : Δ --> dfl_full_comp_cat_to_finlim_ob u₁)
        p
    : #F (cat_el_map_pb_mor (dfl_full_comp_cat_to_finlim_stable_el_map u₁ el₁) s t)
      · comprehension_nat_trans_mor
          (comp_cat_functor_comprehension F)
          (comp_cat_univ_el el₁ (dfl_full_comp_cat_mor_to_tm_univ u₁ t))
      · comprehension_functor_mor
          (comp_cat_comprehension C₂)
          (comp_cat_functor_preserves_univ_type_el_mor
             Fel
             (dfl_full_comp_cat_mor_to_tm_univ u₁ t)
           ;; comp_cat_el_map_on_eq
                _
                (dfl_full_comp_cat_functor_preserves_el_map_eq t))%mor_disp
      =
      comprehension_nat_trans_mor
        (comp_cat_functor_comprehension F)
        (comp_cat_univ_el el₁ (dfl_full_comp_cat_mor_to_tm_univ u₁ (s · t)))
      · comprehension_functor_mor
          (comp_cat_comprehension C₂)
          (comp_cat_functor_preserves_univ_type_el_mor
             Fel
             (dfl_full_comp_cat_mor_to_tm_univ u₁ (s · t))
           ;; comp_cat_el_map_on_eq
                _
                (dfl_full_comp_cat_functor_preserves_el_map_eq (s · t)))%mor_disp
      · cat_el_map_el_eq (dfl_full_comp_cat_to_finlim_el_map _ _) p
      · cat_el_map_pb_mor
          (dfl_full_comp_cat_to_finlim_stable_el_map u₂ el₂)
          (# F s)
          (# F t
           · (comprehension_nat_trans_mor (comp_cat_functor_comprehension F) u₁
           · comprehension_functor_mor (comp_cat_comprehension C₂) F_u)).
  Proof.
    etrans.
    {
      apply maponpaths_2.
      apply comprehension_nat_trans_comm.
    }
    refine (assoc' _ _ _ @ _).
    do 2 refine (_ @ assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply disp_functor_transportf.
        }
        apply comprehension_functor_mor_transportf.
      }
      exact (!(comprehension_functor_mor_comp _ _ _)).
    }
    etrans.
    {
      rewrite disp_functor_comp.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      rewrite !assoc_disp_var.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      refine (comprehension_functor_mor_comp _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        rewrite assoc_disp.
        unfold transportb.
        refine (comprehension_functor_mor_transportf _ _ _ @ _).
        refine (comprehension_functor_mor_comp _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply (comp_cat_functor_preserves_univ_type_el_stable_alt_inv_disp_alt
                   Fel
                   s
                   (dfl_full_comp_cat_mor_to_tm_univ _ t)).
        }
        refine (!_).
        apply comprehension_functor_mor_comp.
      }
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    etrans.
    {
      rewrite !assoc_disp_var.
      rewrite !mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        do 6 apply maponpaths.
        apply (comp_cat_subst_natural el₂).
      }
      rewrite !mor_disp_transportf_prewhisker.
      apply comprehension_functor_mor_transportf.
    }
    etrans.
    {
      rewrite assoc_disp.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        do 4 (refine (assoc_disp _ _ _ @ _) ; apply maponpaths).
        do 5 apply maponpaths_2.
        apply mor_disp_transportf_prewhisker.
      }
      unfold transportb.
      rewrite !mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        do 5 apply maponpaths_2.
        refine (!_).
        apply disp_functor_comp_var.
      }
      rewrite !mor_disp_transportf_postwhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        do 5 apply maponpaths_2.
        rewrite assoc_disp_var.
        apply disp_functor_transportf.
      }
      rewrite !mor_disp_transportf_postwhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        do 5 apply maponpaths_2.
        do 2 apply maponpaths.
        exact (z_iso_disp_after_inv_mor
                 (z_iso_disp_from_z_iso_fiber
                    _ _ _ _
                    (comp_cat_univ_el_stable
                       el₁
                       s
                       (dfl_full_comp_cat_mor_to_tm_univ u₁ t)))).
      }
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite disp_functor_transportf.
      rewrite !mor_disp_transportf_postwhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      rewrite id_right_disp.
      unfold transportb.
      rewrite disp_functor_transportf.
      rewrite !mor_disp_transportf_postwhisker.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        do 4 apply maponpaths_2.
        apply (comp_cat_functor_preserves_univ_type_el_mor_natural_disp Fel).
      }
      rewrite !mor_disp_transportf_postwhisker.
      apply comprehension_functor_mor_transportf.
    }
    refine (comprehension_functor_mor_comp _ _ _ @ _).
    rewrite !assoc_disp_var.
    rewrite !transport_f_f.
    etrans.
    {
      apply maponpaths_2.
      refine (comprehension_functor_mor_transportf _ _ _ @ _).
      apply comprehension_functor_mor_comp.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply comprehension_functor_mor_comp.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply dfl_full_comp_cat_cat_el_map_el_eq.
      }
      refine (!_).
      apply comprehension_functor_mor_comp.
    }
    rewrite mor_disp_transportf_prewhisker.
    rewrite comprehension_functor_mor_transportf.
    refine (!(comprehension_functor_mor_comp _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      do 2 (refine (assoc_disp _ _ _ @ _) ; apply maponpaths).
      apply idpath.
    }
    unfold transportb.
    rewrite !transport_f_f.
    rewrite comprehension_functor_mor_transportf.
    refine (comprehension_functor_mor_comp _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (comp_cat_el_map_on_disp_concat el₂).
    }
    rewrite mor_disp_transportf_postwhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply assoc_disp.
    }
    unfold transportb.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (comp_cat_el_map_on_disp_concat el₂).
    }
    rewrite mor_disp_transportf_postwhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      apply (comp_cat_univ_el_stable_natural_inv_disp el₂).
    }
    rewrite !mor_disp_transportf_prewhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (assoc_disp _ _ _ @ _).
      apply maponpaths.
      apply assoc_disp.
    }
    unfold transportb.
    rewrite transport_f_f.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    refine (comprehension_functor_mor_comp _ _ _ @ _).
    refine (_ @ !(comprehension_functor_mor_comp _ _ _)).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (comp_cat_el_map_on_disp_concat el₂).
    }
    rewrite mor_disp_transportf_postwhisker.
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply (comp_cat_el_map_on_disp_concat el₂).
    }
    refine (comprehension_functor_mor_transportf _ _ _ @ _).
    apply maponpaths.
    apply (eq_comp_cat_el_map_on_eq el₂).
  Qed.

  Proposition dfl_full_comp_cat_functor_stable_el_map
    : functor_stable_el_map
        dfl_full_comp_cat_functor_preserves_el_map.
  Proof.
    intros Γ Δ s t.
    refine (_ @ dfl_full_comp_cat_functor_stable_el_map_lemma s t _ @ _).
    - refine (_ @ assoc _ _ _).
      apply maponpaths.
      simpl.
      apply maponpaths.
      apply comprehension_functor_mor_transportf.
    - do 2 refine (_ @ assoc _ _ _).
      do 2 refine (assoc' _ _ _ @ _).
      apply maponpaths.
      simpl.
      refine (assoc _ _ _ @ _ @ assoc' _ _ _).
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply comprehension_functor_mor_transportf.
      }
      apply maponpaths.
      apply idpath.
  Qed.

  Definition dfl_full_comp_cat_functor_preserves_el
    : functor_preserves_el
        (dfl_full_comp_cat_to_finlim_stable_el_map u₁ el₁)
        (dfl_full_comp_cat_to_finlim_stable_el_map u₂ el₂)
        Fob.
  Proof.
    use make_functor_preserves_el.
    - exact dfl_full_comp_cat_functor_preserves_el_map.
    - exact dfl_full_comp_cat_functor_stable_el_map.
  Defined.
End ToFunctorFinLimUniv.
