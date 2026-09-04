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
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.SetFams.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.Examples.SetModel.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.

Local Open Scope cat.
Local Open Scope comp_cat.

Section SetUniverseToUniverse.
  Context (u : set_universe).

  (** * 1. The universe type *)
  Definition set_comp_cat_universe
    : ty ([] : set_comp_cat)
    := λ _, u.

  Definition set_comp_cat_with_ob
    : comp_cat_with_ob
    := set_comp_cat ,, set_comp_cat_universe.

  (** * 2. The elements map *)
  Definition set_comp_cat_el_map
    : comp_cat_el_map set_comp_cat_with_ob
    := λ Γ t γ, set_universe_el (set_comp_cat_tm_to_sec t γ).

  Arguments set_comp_cat_el_map /.

  (** * 3. Stability *)
  Lemma set_comp_cat_stable_eq
        {Γ Δ : set_comp_cat_with_ob}
        (s : Γ --> Δ)
        (t : tm Δ (comp_cat_univ Δ))
        (γ : (Γ : hSet))
    : set_comp_cat_tm_to_sec t (s γ)
      =
      set_comp_cat_tm_to_sec (t [[s ]]tm ↑ sub_comp_cat_univ s) γ.
  Proof.
    rewrite set_comp_cat_tm_coerce.
    rewrite set_comp_cat_sec_to_tm_to_sec.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (set_comp_cat_tm_subst t s).
    }
    rewrite set_comp_cat_sec_to_tm_to_sec.
    cbn -[set_comp_cat_tm_to_sec eq_subst_ty_iso comp_subst_ty_iso fiber_category].
    rewrite fam_disp_cat_fiber_comp.
    etrans.
    {
      exact (set_comp_cat_eq_subst_ty set_comp_cat_universe _ _).
    }
    etrans.
    {
      apply maponpaths.
      exact (set_comp_cat_comp_subst_ty _ _ set_comp_cat_universe _).
    }
    apply (transportf_set set_comp_cat_universe).
    apply setproperty.
  Qed.

  Definition set_comp_cat_stable_el_map
    : comp_cat_stable_el_map set_comp_cat_el_map.
  Proof.
    intros Γ Δ s t.
    use make_z_iso.
    - intros γ x.
      refine (set_universe_eq _ x).
      exact (set_comp_cat_stable_eq s t γ).
    - intros γ x.
      refine (set_universe_eq _ x).
      refine (!(set_comp_cat_stable_eq s t γ)).
    - split.
      + abstract
          (use funextsec ; intro γ ;
           use funextsec ; intro  ;
           rewrite fam_disp_cat_fiber_comp ;
           cbn ;
           rewrite set_universe_eq_comp ;
           apply set_universe_eq_idpath).
      + abstract
          (use funextsec ; intro γ ;
           use funextsec ; intro a ;
           rewrite fam_disp_cat_fiber_comp ;
           cbn ;
           rewrite set_universe_eq_comp ;
           apply set_universe_eq_idpath).
  Defined.

  Proposition set_comp_cat_el_map_on_eq
              {Γ : set_comp_cat_with_ob}
              {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
              (p : t₁ = t₂)
              {γ : (Γ : hSet)}
              (x : set_comp_cat_el_map Γ t₁ γ)
    : comp_cat_el_map_on_eq set_comp_cat_el_map p γ x
      =
      set_universe_eq (maponpaths (λ z, set_comp_cat_tm_to_sec z γ) p) x.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition set_comp_cat_el_map_on_eq'
              {Γ : set_comp_cat_with_ob}
              {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
              (p : t₁ = t₂)
    : comp_cat_el_map_on_eq set_comp_cat_el_map p
      =
      λ γ x, set_universe_eq (maponpaths (λ z, set_comp_cat_tm_to_sec z γ) p) x.
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Proposition set_comp_cat_coherent_el_map
    : comp_cat_coherent_el_map set_comp_cat_stable_el_map.
  Proof.
    split.
    - intros Γ t.
      use funextsec ; intro γ.
      use funextsec ; intro x.
      rewrite fam_disp_cat_fiber_comp.
      rewrite set_comp_cat_id_subst_ty.
      rewrite set_comp_cat_el_map_on_eq.
      cbn.
      apply set_universe_eq_path.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂ t.
      use funextsec ; intro γ.
      use funextsec ; intro x.
      rewrite !fam_disp_cat_fiber_comp.
      etrans.
      {
        apply maponpaths.
        apply set_comp_cat_comp_subst_ty.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply set_comp_cat_coerce_subst_ty.
      }
      rewrite set_comp_cat_el_map_on_eq.
      cbn.
      rewrite !set_universe_eq_comp.
      apply set_universe_eq_path.
  Qed.

  (** * 4. The comprehension category with a universe *)
  Definition set_comp_cat_univ_type
    : comp_cat_univ_type set_comp_cat_with_ob.
  Proof.
    use make_comp_cat_univ_type.
    - exact set_comp_cat_el_map.
    - exact set_comp_cat_stable_el_map.
    - exact set_comp_cat_coherent_el_map.
  Defined.

  Definition set_dfl_full_comp_cat_with_univ
    : dfl_full_comp_cat_with_univ
    := make_dfl_full_comp_cat_with_univ
         set_dfl_full_comp_cat
         _
         set_comp_cat_univ_type.

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
End SetUniverseToUniverse.
