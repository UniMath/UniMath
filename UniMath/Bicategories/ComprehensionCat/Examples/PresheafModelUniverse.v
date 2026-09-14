(**

 Universe in the set model of type theory

 We show how to construct a universe type in the set model. We start with a set `u`
 and a map that assigns a set to terms of type `u` (this is called a `set_universe`
 in the file `Combinatorics.SetUniverses`), and we show that this data gives rise
 to an universe type in the comprehension category of sets and families of sets. We
 also provide various calculational lemmas that are useful when showing that the
 resulting universe is closed under various type formers.

 Note that we can instantiate this construction with either the universe of iterative
 sets and with an inductive-recursive universe.

 Content
 1. The universe type
 2. The elements map
 3. Stability
 4. The comprehension category with a universe
 5. Useful calculational lemmas

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.SetUniverses.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Categories.UniverseToCat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SigmaTypes.
Require Import UniMath.CategoryTheory.Presheaves.PiTypes.
Require Import UniMath.CategoryTheory.Presheaves.PiTypesStable.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.NaturalNumbers.
Require Import UniMath.CategoryTheory.Presheaves.Precomposition.
Require Import UniMath.CategoryTheory.Presheaves.UniverseLifting.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Examples.PresheafModel.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

#[local] Opaque sub_comp_cat_univ.

Section PresheafUniverse.
  Context (C : category)
          (u : set_universe).

  (** * 1. The universe type *)
  Definition psh_comp_cat_universe
    : ty ([] : psh_comp_cat C)
    := presheaf_universe C u.

  Definition psh_comp_cat_with_ob
    : comp_cat_with_ob
    := psh_comp_cat C ,, psh_comp_cat_universe.

  (** * 2. The elements map *)
  Definition psh_comp_cat_el_map
    : comp_cat_el_map psh_comp_cat_with_ob
    := λ Γ t, presheaf_el_map (psh_comp_cat_tm_to_sec t).

  Arguments psh_comp_cat_el_map /.

  (** * 3. Stability *)
  Definition psh_sub_comp_cat_univ
             {Γ Δ : C^op ⟶ HSET}
             (s : Γ ⟹ Δ)
    : dep_psh_nat_trans
        (dep_psh_subst
           s
           (dep_psh_subst
              (TerminalArrow Terminal_PreShv _)
              psh_comp_cat_universe))
        (dep_psh_subst
           (TerminalArrow Terminal_PreShv _)
           psh_comp_cat_universe)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx F, F).
    - abstract
        (intros x y xx yy f p q F ; cbn ;
         apply idpath).
  Defined.

  Proposition psh_sub_comp_cat_univ_eq
              {Γ Δ : C^op ⟶ HSET}
              (s : Γ ⟹ Δ)
    : sub_comp_cat_univ (C := psh_comp_cat_with_ob) s
      =
      psh_sub_comp_cat_univ s.
  Proof.
    use dep_psh_nat_trans_eq.
    intros x xx F.
    refine (dep_psh_fiber_comp _ _ _ _ @ _).
    etrans.
    {
      apply psh_comp_cat_eq_subst_ty.
    }
    etrans.
    {
      apply maponpaths.
      exact (psh_comp_cat_comp_subst_ty
               C
               s (TerminalArrow Terminal_PreShv _)
               psh_comp_cat_universe
               F).
    }
    simpl.
    rewrite transportf_const.
    apply idpath.
  Qed.

  Lemma psh_comp_cat_stable_eq
        {Γ Δ : C^op ⟶ HSET}
        (s : Γ ⟹ Δ)
        (t : comp_cat_tm
               _
               (comp_cat_univ (C := psh_comp_cat_with_ob) Δ))
        {x : C}
        (xx : ((Γ : _ ⟶ _) x : hSet))
    : psh_comp_cat_tm_to_sec t x (s x xx)
      =
      psh_comp_cat_tm_to_sec
        (t [[s ]]tm ↑ sub_comp_cat_univ (C := psh_comp_cat_with_ob) s)
        x xx.
  Proof.
    refine (!_).
    etrans.
    {
      refine (psh_term_eq_pt (A := comp_cat_univ (C := psh_comp_cat_with_ob) Γ) _ xx).
      etrans.
      {
        apply maponpaths.
        exact (psh_comp_cat_tm_coerce _ _ _).
      }
      rewrite psh_comp_cat_sec_to_tm_to_sec.
      etrans.
      {
        do 2 apply maponpaths.
        apply psh_comp_cat_tm_subst.
      }
      rewrite psh_comp_cat_sec_to_tm_to_sec.
      apply maponpaths_2.
      apply psh_sub_comp_cat_univ_eq.
    }
    apply idpath.
  Qed.

  Definition psh_comp_cat_stable_el_map_mor
             {Γ Δ : psh_comp_cat_with_ob}
             (s : Γ --> Δ)
             (t : tm Δ (comp_cat_univ Δ))
    : dep_psh_nat_trans
        (dep_psh_subst s (presheaf_el_map (psh_comp_cat_tm_to_sec t)))
        (presheaf_el_map (psh_comp_cat_tm_to_sec (t [[ s ]]tm ↑ sub_comp_cat_univ s)))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - refine (λ x xx a, set_universe_eq _ a).
      abstract
        (use functor_to_set_universe_eq_ob ;
         exact (psh_comp_cat_stable_eq s t xx)).
    - abstract
        (intros x y xx yy f p q a ;
         refine (set_universe_eq_comp _ _ _ @ _) ;
         etrans ;
         [ apply maponpaths ;
           apply (functor_to_set_universe_eq (psh_comp_cat_stable_eq s t xx))
         | ] ;
         refine (set_universe_eq_comp _ _ _ @ _) ;
         use set_universe_eq_path' ;
         apply maponpaths ;
         apply set_universe_eq_path).
  Defined.

  Definition psh_comp_cat_stable_el_map_inv
             {Γ Δ : psh_comp_cat_with_ob}
             (s : Γ --> Δ)
             (t : tm Δ (comp_cat_univ Δ))
    : dep_psh_nat_trans
        (presheaf_el_map (psh_comp_cat_tm_to_sec (t [[ s ]]tm ↑ sub_comp_cat_univ s)))
        (dep_psh_subst s (presheaf_el_map (psh_comp_cat_tm_to_sec t)))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - refine (λ x xx a, set_universe_eq _ a).
      abstract
        (use functor_to_set_universe_eq_ob ;
         exact (!(psh_comp_cat_stable_eq s t xx))).
    - abstract
        (intros x y xx yy f p q a ;
         refine (set_universe_eq_comp _ _ _ @ _) ;
         etrans ;
         [ apply maponpaths ;
           apply (functor_to_set_universe_eq (!(psh_comp_cat_stable_eq s t xx)))
         | ] ;
         refine (set_universe_eq_comp _ _ _ @ _) ;
         use set_universe_eq_path' ;
         apply maponpaths ;
         apply set_universe_eq_path).
  Defined.

  Definition psh_comp_cat_stable_el_map
    : comp_cat_stable_el_map psh_comp_cat_el_map.
  Proof.
    intros Γ Δ s t.
    use make_z_iso.
    - exact (psh_comp_cat_stable_el_map_mor s t).
    - exact (psh_comp_cat_stable_el_map_inv s t).
    - abstract
        (split ;
         use dep_psh_nat_trans_eq ;
         intros ;
         refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
         refine (set_universe_eq_comp _ _ _ @ _) ;
         apply set_universe_eq_idpath).
  Defined.

  Definition psh_comp_cat_el_map_eq
             {Γ : psh_comp_cat_with_ob}
             {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
             (p : t₁ = t₂)
    : dep_psh_nat_trans
        (presheaf_el_map (psh_comp_cat_tm_to_sec t₁))
        (presheaf_el_map (psh_comp_cat_tm_to_sec t₂))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - refine (λ x γ a, set_universe_eq _ a).
      abstract
        (induction p ;
         apply idpath).
    - intros x y xx yy f q₁ q₂ a.
      abstract
        (induction p ;
         refine (set_universe_eq_comp _ _ _ @ _) ;
         apply set_universe_eq_path' ;
         apply maponpaths ;
         refine (!_) ;
         apply set_universe_eq_idpath).
  Defined.

  Proposition psh_comp_cat_el_map_on_eq
              {Γ : psh_comp_cat_with_ob}
              {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
              (p : t₁ = t₂)
    : comp_cat_el_map_on_eq psh_comp_cat_el_map p
      =
      psh_comp_cat_el_map_eq p.
  Proof.
    induction p.
    use dep_psh_nat_trans_eq.
    intros x γ a.
    refine (!_).
    apply set_universe_eq_idpath.
  Qed.

  Proposition psh_comp_cat_coherent_el_map
    : comp_cat_coherent_el_map psh_comp_cat_stable_el_map.
  Proof.
    split.
    - intros Γ t.
      rewrite psh_comp_cat_el_map_on_eq.
      use dep_psh_nat_trans_eq.
      intros x γ a.
      refine (dep_psh_fiber_comp _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply psh_comp_cat_id_subst_ty.
      }
      apply set_universe_eq_path.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply psh_comp_cat_el_map_on_eq.
      }
      use dep_psh_nat_trans_eq.
      intros x γ a.
      refine (dep_psh_fiber_comp _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        exact (dep_psh_fiber_comp _ _ _ _).
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply psh_comp_cat_coerce_subst_ty.
      }
      refine (!_).
      refine (dep_psh_fiber_comp _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply psh_comp_cat_comp_subst_ty.
      }
      refine (!_).
      do 2 refine (set_universe_eq_comp _ _ _ @ _).
      apply set_universe_eq_path.
  Qed.

  (** * 4. The comprehension category with a universe *)
  Definition psh_comp_cat_univ_type
    : comp_cat_univ_type psh_comp_cat_with_ob.
  Proof.
    use make_comp_cat_univ_type.
    - exact psh_comp_cat_el_map.
    - exact psh_comp_cat_stable_el_map.
    - exact psh_comp_cat_coherent_el_map.
  Defined.

  Definition psh_dfl_full_comp_cat_with_univ
    : dfl_full_comp_cat_with_univ
    := make_dfl_full_comp_cat_with_univ
         (psh_dfl_full_comp_cat C)
         _
         psh_comp_cat_univ_type.

  (*
  (** * 5. Useful calculational lemmas *)
  Definition set_sub_dfl_comp_cat_univ
             {Γ Δ : hSet}
             (s : Γ → Δ)
    : sub_dfl_comp_cat_univ
        (C := set_dfl_full_comp_cat_with_univ)
        s
      =
      λ γ z, z.
  Proof.
    use funextsec ; intro γ.
    use funextsec ; intro z.
    refine (fam_disp_cat_fiber_comp _ _ _ @ _).
    cbn -[eq_subst_ty_iso comp_subst_ty_iso].
    etrans.
    {
      apply maponpaths.
      exact (set_comp_cat_comp_subst_ty s _ set_comp_cat_universe z).
    }
    refine (set_comp_cat_eq_subst_ty set_comp_cat_universe (TerminalArrowEq _ _) _ @ _).
    rewrite transportf_set.
    - apply idpath.
    - apply setproperty.
  Qed.

  Proposition set_univ_tm_subst_eq
              {Γ Δ : set_dfl_full_comp_cat_with_univ}
              (s : Γ --> Δ)
              (t : tm Δ (dfl_full_comp_cat_univ Δ))
    : t [[ s ]]tm ↑ sub_dfl_comp_cat_univ s
      =
      set_comp_cat_sec_to_tm (λ γ, set_comp_cat_tm_to_sec t (s γ)).
  Proof.
    refine (maponpaths (λ z, z ↑ _) (set_comp_cat_tm_subst _ _) @ _).
    refine (maponpaths (λ z, _ ↑ z) (set_sub_dfl_comp_cat_univ s) @ _).
    refine (set_comp_cat_tm_coerce _ _ @ _).
    rewrite set_comp_cat_sec_to_tm_to_sec.
    apply idpath.
  Qed.

  Proposition set_comp_cat_univ_el_stable_inv_path
              {Γ Δ : set_dfl_full_comp_cat_with_univ}
              (s : Γ --> Δ)
              (t : tm Δ (dfl_full_comp_cat_univ Δ))
              (γ : (Γ : hSet))
    : set_comp_cat_tm_to_sec (t [[ s ]]tm ↑ sub_dfl_comp_cat_univ s) γ
      =
      set_comp_cat_tm_to_sec t (s γ).
  Proof.
    etrans.
    {
      refine (maponpaths (λ z, set_comp_cat_tm_to_sec z γ) _).
      exact (set_univ_tm_subst_eq s t).
    }
    rewrite set_comp_cat_sec_to_tm_to_sec.
    apply idpath.
  Qed.

  Proposition set_comp_cat_univ_el_stable_inv
              {Γ Δ : set_dfl_full_comp_cat_with_univ}
              (s : Γ --> Δ)
              (t : tm Δ (dfl_full_comp_cat_univ Δ))
    : comp_cat_univ_el_stable_inv
        (dfl_full_comp_cat_el set_dfl_full_comp_cat_with_univ)
        s
        t
      =
      λ γ, set_universe_eq (set_comp_cat_univ_el_stable_inv_path s t γ).
  Proof.
    use funextsec ; intro γ.
    use funextsec ; intro x.
    cbn.
    apply set_universe_eq_path.
  Qed.

  Proposition set_comp_cat_univ_el_stable_mor
              {Γ Δ : set_dfl_full_comp_cat_with_univ}
              (s : Γ --> Δ)
              (t : tm Δ (dfl_full_comp_cat_univ Δ))
              (γ : (Γ : hSet))
    : comp_cat_univ_el_stable_mor
        (dfl_full_comp_cat_el set_dfl_full_comp_cat_with_univ)
        s
        t
        γ
      =
      set_universe_eq (!(set_comp_cat_univ_el_stable_inv_path s t γ)).
  Proof.
    use funextsec ; intro x.
    apply set_universe_eq_path.
  Qed.
   *)
End PresheafUniverse.
