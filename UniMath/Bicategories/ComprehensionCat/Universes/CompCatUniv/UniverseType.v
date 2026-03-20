(**

 Univeres types in comprehension categories

 In this file, we define the basic notions for universe types in comprehension categories. Let
 us start with a definition. Let `C` be a comprehension category whose displayed category of
 types is `D`. A universe in this comprehension category consists of
 - A type `u` in the empty context. Note that `u` gives rise to a type `u_Γ` in every
   context `Γ`.
 - For every term `t` of type `u_Γ` in context `Γ` a type `el t` in context `Γ`.
 - For every context morphism `s` from `Γ` to `Δ` and term `t` of type `u_Δ` in context `Δ`,
   an isomorphism, call it `f_{s , t}` between `el (t [[ s ]]tm)` and `(el t) [[ s ]]`.
 This data is required to satisfy suitable coherences regarding `f_{ identity _ , t }` and
 `f_{ s₁ · s₂ , t}`.

 This definition is a rephrasing of universe types to the language of comprehension categories.
 We have a type `u` in the empty context and we have a map assigning to each term `t` of type
 `u_Γ` a new type `el t` in context `Γ`. The main difference between our definition and the
 usual definition in Martin-Löf type theory is that our version is only weakly preserved by
 substitution. More specifically, rather than requiring `(el t) [[ s ]]` and `el (t [[ s ]])`
 to be equal, we only demand that they are isomorphic. The chosen isomorphism are required to
 satisfy coherences.

 Our goal is to define the bicategory of comprehension categories with a universe, and prove
 that it is univalent, and this file is a stepping-stone towards that goal. Specifically, we
 define when a comprehension category has a universe and when functors and natural
 transformations preserve universes.

 Contents
 1. Comprehension categories with a universe and an elements map
 2. Stability of the elements map
 3. Coherent stability of the elements map
 4. Universes in comprehension categories
 5. Accessors for universes
 6. Proving that two universe types are equal
 7. Preservation of universes by functors
 8. Preservation of universes by identity and composition
 9. Preservation by natural transformations

                                                                                            *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.

Local Open Scope cat.
Local Open Scope comp_cat.

(** * 1. Comprehension categories with a universe and an elements map *)
Definition comp_cat_el_map
           (C : comp_cat_with_ob)
  : UU
  := ∏ (Γ : C),
     tm Γ (comp_cat_univ Γ)
     →
     ty Γ.

Definition comp_cat_el_map_on_eq_iso
           {C : comp_cat_with_ob}
           (el : comp_cat_el_map C)
           {Γ : C}
           {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
           (p : t₁ = t₂)
  : z_iso
      (C := fiber_category _ _)
      (el _ t₁)
      (el _ t₂).
Proof.
  induction p.
  apply identity_z_iso.
Defined.

Definition comp_cat_el_map_on_eq
           {C : comp_cat_with_ob}
           (el : comp_cat_el_map C)
           {Γ : C}
           {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
           (p : t₁ = t₂)
  : el _ t₁ <: el _ t₂
  := (comp_cat_el_map_on_eq_iso el p : _ --> _).

Definition comp_cat_el_map_on_eq_inv
           {C : comp_cat_with_ob}
           (el : comp_cat_el_map C)
           {Γ : C}
           {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
           (p : t₁ = t₂)
  : el _ t₂ <: el _ t₁
  := inv_from_z_iso (comp_cat_el_map_on_eq_iso el p).

Proposition comp_cat_el_map_on_idpath
            {C : comp_cat_with_ob}
            (el : comp_cat_el_map C)
            {Γ : C}
            {t : tm Γ (comp_cat_univ Γ)}
            (p : t = t)
  : comp_cat_el_map_on_eq el p = identity _.
Proof.
  assert (p = idpath _) as ->.
  {
    apply isaset_comp_cat_tm.
  }
  apply idpath.
Qed.

Proposition comp_cat_el_map_on_inv
            {C : comp_cat_with_ob}
            (el : comp_cat_el_map C)
            {Γ : C}
            {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
  : comp_cat_el_map_on_eq el (!p)
    =
    comp_cat_el_map_on_eq_inv el p.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition comp_cat_el_map_on_concat
            {C : comp_cat_with_ob}
            (el : comp_cat_el_map C)
            {Γ : C}
            {t₁ t₂ t₃ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
            (q : t₂ = t₃)
  : comp_cat_el_map_on_eq el (p @ q)
    =
    comp_cat_el_map_on_eq el p · comp_cat_el_map_on_eq el q.
Proof.
  induction p.
  refine (!_).
  apply id_left.
Qed.

Proposition eq_comp_cat_el_map_on_eq
            {C : comp_cat_with_ob}
            (el : comp_cat_el_map C)
            {Γ : C}
            {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
            (p q : t₁ = t₂)
  : comp_cat_el_map_on_eq el p = comp_cat_el_map_on_eq el q.
Proof.
  assert (p = q) as ->.
  {
    apply isaset_comp_cat_tm.
  }
  apply idpath.
Qed.

(** * 2. Stability of the elements map *)
Definition comp_cat_stable_el_map
           {C : comp_cat_with_ob}
           (el : comp_cat_el_map C)
  : UU
  := ∏ (Γ Δ : C)
       (s : Γ --> Δ)
       (t : tm Δ (comp_cat_univ Δ)),
     z_iso
       (C := fiber_category _ _)
       ((el _ t) [[ s ]])
       (el _ (t [[ s ]]tm ↑ (sub_comp_cat_univ s))).

Proposition comp_cat_stable_el_map_on_eq
            {C : comp_cat_with_ob}
            {el : comp_cat_el_map C}
            (el_s : comp_cat_stable_el_map el)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {t₁ t₂ : tm Δ (comp_cat_univ Δ)}
            (p : t₁ = t₂)
            (q : t₁ [[ s ]]tm ↑ sub_comp_cat_univ s
                 =
                 t₂ [[ s ]]tm ↑ sub_comp_cat_univ s)
  : el_s Γ Δ s t₁ · comp_cat_el_map_on_eq el q
    =
    coerce_subst_ty s (comp_cat_el_map_on_eq el p) · el_s Γ Δ s t₂.
Proof.
  induction p.
  etrans.
  {
    apply maponpaths.
    apply comp_cat_el_map_on_idpath.
  }
  refine (id_right _ @ _).
  refine (!_).
  refine (_ @ id_left _).
  apply maponpaths_2.
  apply id_coerce_subst_ty.
Qed.

Proposition comp_cat_stable_el_map_on_eq'
            {C : comp_cat_with_ob}
            {el : comp_cat_el_map C}
            (el_s : comp_cat_stable_el_map el)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {t₁ t₂ : tm Δ (comp_cat_univ Δ)}
            (p : t₁ = t₂)
  : el_s Γ Δ s t₁
    · comp_cat_el_map_on_eq el (maponpaths (λ z, z [[ s ]]tm ↑ sub_comp_cat_univ s) p)
    =
    coerce_subst_ty s (comp_cat_el_map_on_eq el p)
    · el_s Γ Δ s t₂.
Proof.
  apply comp_cat_stable_el_map_on_eq.
Qed.

(** * 3. Coherent stability of the elements map *)
Proposition comp_cat_univ_id_coherence
            {C : comp_cat_with_ob}
            {Γ : C}
            (t : tm Γ (comp_cat_univ Γ))
  : t = t [[ identity Γ ]]tm ↑ sub_comp_cat_univ (identity Γ).
Proof.
  rewrite id_sub_comp_cat_tm.
  rewrite comp_coerce_comp_cat_tm.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    unfold sub_comp_cat_univ.
    cbn -[id_subst_ty eq_subst_ty compose comp_subst_ty].
    refine (_ @ id_left_subst_ty _ _).
    rewrite !assoc'.
    do 2 apply maponpaths.
    unfold eq_subst_ty.
    cbn.
    do 3 apply maponpaths.
    apply homset_property.
  }
  cbn.
  rewrite id_coerce_comp_cat_tm.
  apply idpath.
Qed.

Proposition comp_cat_univ_comp_coherence
            {C : comp_cat_with_ob}
            {Γ₁ Γ₂ Γ₃ : C}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (t : tm Γ₃ (comp_cat_univ Γ₃))
  : (t [[ s₂ ]]tm ↑ sub_comp_cat_univ s₂) [[ s₁ ]]tm ↑ sub_comp_cat_univ s₁
    =
    t [[ s₁ · s₂ ]]tm ↑ sub_comp_cat_univ (s₁ · s₂).
Proof.
  rewrite comp_sub_comp_cat_tm.
  rewrite subst_coerce_comp_cat_tm.
  rewrite !comp_coerce_comp_cat_tm.
  apply maponpaths_2.
  unfold sub_comp_cat_univ.
  cbn -[comp_subst_ty eq_subst_ty compose].
  refine (!_).
  etrans.
  {
    apply (assoc (C := fiber_category _ _)).
  }
  etrans.
  {
    apply maponpaths_2.
    apply assoc_subst_ty.
  }
  etrans.
  {
    apply (assoc' (C := fiber_category _ _)).
  }
  etrans.
  {
    apply maponpaths.
    apply eq_subst_ty_concat.
  }
  etrans.
  {
    apply (assoc' (C := fiber_category _ _)).
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply comp_coerce_subst_ty.
  }
  etrans.
  {
    apply (assoc' (C := fiber_category _ _)).
  }
  apply maponpaths.
  etrans.
  {
    apply assoc.
  }
  etrans.
  {
    apply maponpaths_2.
    apply coerce_comp_subst_ty.
  }
  etrans.
  {
    apply assoc'.
  }
  apply maponpaths.
  etrans.
  {
    apply eq_subst_ty_concat.
  }
  apply eq_subst_ty_eq.
Qed.

Definition comp_cat_coherent_el_map
           {C : comp_cat_with_ob}
           {el : comp_cat_el_map C}
           (el_s : comp_cat_stable_el_map el)
  : UU
  := (∏ (Γ : C)
        (t : comp_cat_tm Γ (comp_cat_univ Γ)),
      id_subst_ty _ · (el_s _ _ (identity Γ) t : _ --> _)
      =
      comp_cat_el_map_on_eq el (comp_cat_univ_id_coherence t))
     ×
     (∏ (Γ₁ Γ₂ Γ₃ : C)
        (s₁ : Γ₁ --> Γ₂)
        (s₂ : Γ₂ --> Γ₃)
        (t : comp_cat_tm Γ₃ (comp_cat_univ Γ₃)),
      comp_subst_ty _ _ _ · (el_s _ _ (s₁ · s₂) t : _ --> _)
      =
      coerce_subst_ty s₁ (el_s _ _ s₂ t : _ --> _)
      · el_s _ _ s₁ _
      · comp_cat_el_map_on_eq el (comp_cat_univ_comp_coherence s₁ s₂ t)).

Proposition isaprop_comp_cat_coherent_el_map
            {C : comp_cat_with_ob}
            {el : comp_cat_el_map C}
            (el_s : comp_cat_stable_el_map el)
  : isaprop (comp_cat_coherent_el_map el_s).
Proof.
  use isapropdirprod ; repeat (use impred ; intro) ; apply homset_property.
Qed.

(** * 4. Universes in comprehension categories *)
Definition comp_cat_univ_type
           (C : comp_cat_with_ob)
  : UU
  := ∑ (el_s : ∑ (el : comp_cat_el_map C), comp_cat_stable_el_map el),
     comp_cat_coherent_el_map (pr2 el_s).

Definition make_comp_cat_univ_type
           {C : comp_cat_with_ob}
           (el : comp_cat_el_map C)
           (el_s : comp_cat_stable_el_map el)
           (el_c : comp_cat_coherent_el_map el_s)
  : comp_cat_univ_type C
  := (el ,, el_s) ,, el_c.

(** * 5. Accessors for universes *)
Definition comp_cat_univ_el
           {C : comp_cat_with_ob}
           (el : comp_cat_univ_type C)
           {Γ : C}
           (t : tm Γ (comp_cat_univ Γ))
  : ty Γ
  := pr11 el Γ t.

Coercion comp_cat_univ_el_map
         {C : comp_cat_with_ob}
         (el : comp_cat_univ_type C)
  : comp_cat_el_map C
  := pr11 el.

Definition comp_cat_univ_el_stable
           {C : comp_cat_with_ob}
           (el : comp_cat_univ_type C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (t : tm Δ (comp_cat_univ Δ))
  : z_iso
      (C := fiber_category _ _)
      ((comp_cat_univ_el el t) [[ s ]])
      (comp_cat_univ_el el (t [[ s ]]tm ↑ (sub_comp_cat_univ s)))
  := pr21 el Γ Δ s t.

Definition comp_cat_univ_el_stable_mor
           {C : comp_cat_with_ob}
           (el : comp_cat_univ_type C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (t : tm Δ (comp_cat_univ Δ))
  : ((comp_cat_univ_el el t) [[ s ]]
     <:
     comp_cat_univ_el el (t [[ s ]]tm ↑ (sub_comp_cat_univ s)))
  := comp_cat_univ_el_stable el s t : _ --> _.

Definition comp_cat_univ_el_stable_inv
           {C : comp_cat_with_ob}
           (el : comp_cat_univ_type C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (t : tm Δ (comp_cat_univ Δ))
  : (comp_cat_univ_el el (t [[ s ]]tm ↑ (sub_comp_cat_univ s))
     <:
     (comp_cat_univ_el el t) [[ s ]])
  := inv_from_z_iso (comp_cat_univ_el_stable el s t).

Definition extend_sub_univ
           {C : comp_cat_with_ob}
           (el : comp_cat_univ_type C)
           {Γ Δ : C}
           (s : Γ --> Δ)
           (a : tm Δ (comp_cat_univ Δ))
  : Γ & comp_cat_univ_el el (a [[ s ]]tm ↑ sub_comp_cat_univ s)
    -->
    Δ & comp_cat_univ_el el a
  := comp_cat_comp_mor (inv_from_z_iso (comp_cat_univ_el_stable el s a))
     · comp_cat_extend_over (comp_cat_univ_el el a) s.

Proposition comp_cat_univ_el_stable_natural
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ Δ : C}
            (s : Γ --> Δ)
            {t₁ t₂ : tm Δ (comp_cat_univ Δ)}
            (p : t₁ = t₂)
            (q : t₁ [[ s ]]tm ↑ sub_comp_cat_univ s
                 =
                 t₂ [[ s ]]tm ↑ sub_comp_cat_univ s)
  : coerce_subst_ty s (comp_cat_el_map_on_eq el p)
    · comp_cat_univ_el_stable el s t₂
    =
    comp_cat_univ_el_stable el s t₁
    · comp_cat_el_map_on_eq el q.
Proof.
  induction p.
  etrans.
  {
    apply maponpaths_2.
    apply id_coerce_subst_ty.
  }
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply comp_cat_el_map_on_idpath.
  }
  rewrite id_left, id_right.
  apply idpath.
Qed.

Proposition comp_cat_univ_el_stable_id_coh
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ : C}
            (t : comp_cat_tm Γ (comp_cat_univ Γ))
  : id_subst_ty _
    · (comp_cat_univ_el_stable el (identity Γ) t : _ --> _)
    =
    comp_cat_el_map_on_eq el (comp_cat_univ_id_coherence t).
Proof.
  exact (pr12 el Γ t).
Qed.

Proposition comp_cat_univ_el_stable_id_coh_alt
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ : C}
            (t : comp_cat_tm Γ (comp_cat_univ Γ))
  : (comp_cat_univ_el_stable el (identity Γ) t : _ --> _)
    =
    id_subst_ty_inv _ · comp_cat_el_map_on_eq el (comp_cat_univ_id_coherence t).
Proof.
  rewrite <- comp_cat_univ_el_stable_id_coh.
  rewrite !assoc.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply z_iso_after_z_iso_inv.
  }
  apply id_left.
Qed.

Proposition comp_cat_univ_el_stable_id_coh_inv
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ : C}
            (t : comp_cat_tm Γ (comp_cat_univ Γ))
  : inv_from_z_iso (comp_cat_univ_el_stable el (identity Γ) t)
    =
    comp_cat_el_map_on_eq el (!(comp_cat_univ_id_coherence t))
    · id_subst_ty _.
Proof.
  refine (!(id_left _) @ _).
  refine (!_).
  use z_iso_inv_on_left.
  rewrite assoc'.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    exact (comp_cat_univ_el_stable_id_coh el t).
  }
  rewrite <- comp_cat_el_map_on_concat.
  apply comp_cat_el_map_on_idpath.
Qed.

Proposition comp_cat_univ_el_stable_id_coh_inv_alt_eq
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ : C}
            (s : Γ --> Γ)
            (p : identity _ = s)
            (t : comp_cat_tm Γ (comp_cat_univ Γ))
  : t [[ s ]]tm ↑ sub_comp_cat_univ s
    =
    t.
Proof.
  induction p.
  exact (!(comp_cat_univ_id_coherence t)).
Defined.

Proposition comp_cat_univ_el_stable_id_coh_inv_alt
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ : C}
            (s : Γ --> Γ)
            (p : identity _ = s)
            (t : comp_cat_tm Γ (comp_cat_univ Γ))
  : inv_from_z_iso (comp_cat_univ_el_stable el s t)
    =
    comp_cat_el_map_on_eq el (comp_cat_univ_el_stable_id_coh_inv_alt_eq el s p t)
    · id_subst_ty _
    · eq_subst_ty _ p.
Proof.
  induction p.
  refine (comp_cat_univ_el_stable_id_coh_inv el t @ _).
  rewrite eq_subst_ty_idpath.
  rewrite id_right.
  apply idpath.
Qed.

Proposition comp_cat_univ_el_stable_comp_coh
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ₁ Γ₂ Γ₃ : C}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (t : comp_cat_tm Γ₃ (comp_cat_univ Γ₃))
  : comp_subst_ty _ _ _ · (comp_cat_univ_el_stable el (s₁ · s₂) t : _ --> _)
    =
    coerce_subst_ty s₁ (comp_cat_univ_el_stable el s₂ t : _ --> _)
    · comp_cat_univ_el_stable el s₁ _
    · comp_cat_el_map_on_eq el (comp_cat_univ_comp_coherence s₁ s₂ t).
Proof.
  exact (pr22 el Γ₁ Γ₂ Γ₃ s₁ s₂ t).
Qed.

Proposition comp_cat_univ_el_stable_comp_coh_inv
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ₁ Γ₂ Γ₃ : C}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (t : comp_cat_tm Γ₃ (comp_cat_univ Γ₃))
  : inv_from_z_iso (comp_cat_univ_el_stable el (s₁ · s₂) t)
    =
    comp_cat_el_map_on_eq el (!(comp_cat_univ_comp_coherence s₁ s₂ t))
    · inv_from_z_iso (comp_cat_univ_el_stable el s₁ _)
    · coerce_subst_ty s₁ (inv_from_z_iso (comp_cat_univ_el_stable el s₂ t))
    · comp_subst_ty _ _ _.
Proof.
  refine (!(id_left _) @ _).
  refine (!_).
  use z_iso_inv_on_left.
  rewrite !assoc'.
  refine (!_).
  rewrite comp_cat_univ_el_stable_comp_coh.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- comp_coerce_subst_ty.
    rewrite z_iso_after_z_iso_inv.
    rewrite id_coerce_subst_ty.
    apply id_left.
  }
  etrans.
  {
    apply maponpaths.
    rewrite !assoc.
    rewrite z_iso_after_z_iso_inv.
    apply id_left.
  }
  rewrite <- comp_cat_el_map_on_concat.
  apply comp_cat_el_map_on_idpath.
Qed.

Proposition transportf_comp_cat_univ_el
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ Δ : C}
            {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
            (f : Γ & comp_cat_univ_el el t₁ --> Δ)
  : transportf
      (λ z, Γ & comp_cat_univ_el el z --> Δ)
      p
      f
    =
    comp_cat_comp_mor (comp_cat_el_map_on_eq el (!p)) · f.
Proof.
  induction p ; cbn.
  rewrite comp_cat_comp_mor_id.
  rewrite id_left.
  apply idpath.
Qed.

Proposition transportf_comp_cat_univ_el'
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ Δ : C}
            {t₁ t₂ : tm Δ (comp_cat_univ Δ)}
            (p : t₁ = t₂)
            (f : Γ --> Δ & comp_cat_univ_el el t₁)
  : transportf
      (λ z, Γ --> Δ& comp_cat_univ_el el z)
      p
      f
    =
    f · comp_cat_comp_mor (comp_cat_el_map_on_eq el p).
Proof.
  induction p ; cbn.
  rewrite comp_cat_comp_mor_id.
  rewrite id_right.
  apply idpath.
Qed.

(** * 6. Proving that two universe types are equal *)
Proposition path_comp_cat_univ_type_weq
            {C : comp_cat_with_ob}
            (el₁ el₂ : comp_cat_univ_type C)
  : (el₁ = el₂)
    ≃
    ∑ (p : ∏ (Γ : C)
             (t : tm Γ (comp_cat_univ Γ)),
           z_iso
             (C := fiber_category _ _)
             (comp_cat_univ_el el₁ t)
             (comp_cat_univ_el el₂ t)),
    ∏ (Γ Δ : C)
      (s : Γ --> Δ)
      (t : tm Δ (comp_cat_univ Δ)),
    comp_cat_univ_el_stable el₁ s t
    · p Γ (t [[s ]]tm ↑ sub_comp_cat_univ s)
    =
    coerce_subst_ty s (p Δ t : _ --> _)
    · comp_cat_univ_el_stable el₂ s t.
Proof.
  induction el₁ as [ el₁ H₁ ].
  induction el₂ as [ el₂ H₂ ].
  induction el₁ as [ el₁ r₁ ].
  induction el₂ as [ el₂ r₂ ].
  refine (_ ∘ path_sigma_hprop _ _ _ _)%weq.
  {
    apply isaprop_comp_cat_coherent_el_map.
  }
  refine (_ ∘ total2_paths_equiv _ _ _)%weq.
  use weqtotal2.
  - refine (_ ∘ weqtoforallpaths _ _ _)%weq.
    use weqonsecfibers.
    intro Γ.
    refine (_ ∘ weqtoforallpaths _ _ _)%weq.
    use weqonsecfibers.
    intro t ; cbn.
    use make_weq.
    + exact (λ p, idtoiso (C := fiber_category _ _) p).
    + use is_univalent_fiber.
      apply disp_univalent_category_is_univalent_disp.
  - intro p ; cbn in p.
    induction p.
    refine (_ ∘ weqtoforallpaths _ _ _)%weq.
    use weqonsecfibers.
    intros Γ.
    refine (_ ∘ weqtoforallpaths _ _ _)%weq.
    use weqonsecfibers.
    intros Δ.
    refine (_ ∘ weqtoforallpaths _ _ _)%weq.
    use weqonsecfibers.
    intros s.
    refine (_ ∘ weqtoforallpaths _ _ _)%weq.
    use weqonsecfibers.
    intros t.
    refine (_ ∘ path_sigma_hprop _ _ _ _)%weq.
    {
      apply isaprop_is_z_isomorphism.
    }
    cbn -[coerce_subst_ty compose].
    use weqimplimpl.
    + abstract
        (intro p ;
         refine (id_right (C := fiber_category _ _) _ @ _) ;
         refine (p @ _) ;
         refine (!(id_left (C := fiber_category _ _) _) @ _) ;
         apply maponpaths_2 ;
         refine (!_) ;
         apply id_coerce_subst_ty).
    + abstract
        (intro p ;
         refine (!(id_right (C := fiber_category _ _) _) @ _) ;
         refine (p @ _) ;
         refine (_ @ id_left (C := fiber_category _ _) _) ;
         apply maponpaths_2 ;
         apply id_coerce_subst_ty).
    + apply (homset_property (fiber_category _ _)).
    + apply (homset_property (fiber_category _ _)).
Defined.

Proposition path_comp_cat_univ_type
            {C : comp_cat_with_ob}
            {el₁ el₂ : comp_cat_univ_type C}
            (p : ∏ (Γ : C)
                   (t : tm Γ (comp_cat_univ Γ)),
                 z_iso
                   (C := fiber_category _ _)
                   (comp_cat_univ_el el₁ t)
                   (comp_cat_univ_el el₂ t))
            (q : ∏ (Γ Δ : C)
                   (s : Γ --> Δ)
                   (t : tm Δ (comp_cat_univ Δ)),
                 comp_cat_univ_el_stable el₁ s t
                 · p Γ (t [[s ]]tm ↑ sub_comp_cat_univ s)
                 =
                 coerce_subst_ty s (p Δ t : _ --> _)
                 · comp_cat_univ_el_stable el₂ s t)
  : el₁ = el₂.
Proof.
  exact (invmap (path_comp_cat_univ_type_weq el₁ el₂) (p ,, q)).
Defined.

(** * 7. Preservation of universes by functors *)
Definition comp_cat_functor_preserves_el
           {C₁ C₂ : comp_cat_with_ob}
           (F : comp_cat_functor_ob C₁ C₂)
           (el₁ : comp_cat_univ_type C₁)
           (el₂ : comp_cat_univ_type C₂)
  : UU
  := ∏ (Γ : C₁)
       (t : tm Γ (comp_cat_univ Γ)),
     z_iso
       (C := fiber_category _ _)
       (comp_cat_type_functor
          F
          _
          (comp_cat_univ_el el₁ t))
       (comp_cat_univ_el
          el₂
          (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Γ)).

Proposition isaset_comp_cat_functor_preserves_el
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            (el₁ : comp_cat_univ_type C₁)
            (el₂ : comp_cat_univ_type C₂)
  : isaset (comp_cat_functor_preserves_el F el₁ el₂).
Proof.
  use impred_isaset ; intro Γ₁.
  use impred_isaset ; intro Γ₂.
  apply isaset_z_iso.
Qed.

Proposition comp_cat_functor_preserves_el_natural_path
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {Γ : C₁}
            {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
  : comp_cat_functor_tm F t₁ ↑ functor_comp_cat_on_univ F Γ
    =
    comp_cat_functor_tm F t₂ ↑ functor_comp_cat_on_univ F Γ.
Proof.
  induction p.
  apply idpath.
Qed.

Proposition comp_cat_functor_preserves_el_natural
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            (Fi : comp_cat_functor_preserves_el F el₁ el₂)
            {Γ : C₁}
            {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
  : comp_cat_functor_coerce F (comp_cat_el_map_on_eq_iso el₁ p : _ --> _)
    · Fi _ t₂
    =
    Fi _ t₁
    · comp_cat_el_map_on_eq_iso el₂ (comp_cat_functor_preserves_el_natural_path p).
Proof.
  induction p ; simpl.
  etrans.
  {
    apply maponpaths_2.
    apply comp_cat_functor_coerce_on_id.
  }
  refine (id_left (C := fiber_category _ _) _ @ _).
  refine (!(id_right (C := fiber_category _ _) _) @ _).
  apply maponpaths.
  refine (!_).
  apply comp_cat_el_map_on_idpath.
Qed.

Local Arguments transportf {_ _ _ _ _} _.

Proposition comp_cat_functor_preserves_stable_el_path
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : comp_cat_functor_tm F (t [[s ]]tm ↑ sub_comp_cat_univ s) ↑ functor_comp_cat_on_univ F Γ
    =
    (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Δ) [[# F s ]]tm
    ↑ sub_comp_cat_univ (# F s).
Proof.
  rewrite subst_coerce_comp_cat_tm.
  rewrite comp_coerce_comp_cat_tm.
  rewrite comp_cat_functor_coerce_tm.
  rewrite comp_coerce_comp_cat_tm.
  rewrite comp_cat_functor_subst_tm_alt.
  rewrite comp_coerce_comp_cat_tm.
  apply maponpaths_2.
  cbn -[eq_subst_ty_iso] ; unfold transportb.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite mor_disp_transportf_postwhisker.
  rewrite mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  use (cartesian_factorisation_unique (cleaving_of_types _ _ _ _ _)).
  rewrite !mor_disp_transportf_postwhisker.
  rewrite !assoc_disp_var.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    do 5 apply maponpaths.
    apply subst_ty_eq_disp_iso_comm.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    do 3 apply maponpaths.
    rewrite assoc_disp.
    unfold comp_cat_subst, fiber_functor_natural_inv, transportb.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply idpath.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite assoc_disp.
    unfold transportb.
    rewrite disp_functor_transportf.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite <- disp_functor_comp_var.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      rewrite assoc_disp_var.
      do 2 apply maponpaths.
      apply subst_ty_eq_disp_iso_comm.
    }
    rewrite mor_disp_transportf_prewhisker.
    rewrite cartesian_factorisation_commutes.
    rewrite !transport_f_f.
    rewrite disp_functor_transportf.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply idpath.
  }
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    rewrite !assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite disp_functor_comp.
    unfold transportb.
    rewrite mor_disp_transportf_prewhisker.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    apply idpath.
  }
  refine (!_).
  etrans.
  {
    do 3 apply maponpaths.
    apply subst_ty_eq_disp_iso_comm.
  }
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  rewrite cartesian_factorisation_commutes.
  rewrite !mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  etrans.
  {
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite mor_disp_transportf_postwhisker.
    rewrite transport_f_f.
    rewrite assoc_disp_var.
    rewrite transport_f_f.
    rewrite assoc_disp_var.
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite assoc_disp_var.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    etrans.
    {
      do 4 apply maponpaths.
      apply subst_ty_eq_disp_iso_comm.
    }
    rewrite !mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite cartesian_factorisation_commutes.
    rewrite !mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      rewrite assoc_disp.
      unfold comp_cat_subst, fiber_functor_natural_inv, transportb.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      apply idpath.
    }
    rewrite mor_disp_transportf_prewhisker.
    rewrite transport_f_f.
    rewrite assoc_disp.
    unfold transportb.
    rewrite transport_f_f.
    apply idpath.
  }
  apply maponpaths_2.
  apply homset_property.
Qed.

Definition comp_cat_functor_preserves_stable_el
           {C₁ C₂ : comp_cat_with_ob}
           {F : comp_cat_functor_ob C₁ C₂}
           (el₁ : comp_cat_univ_type C₁)
           (el₂ : comp_cat_univ_type C₂)
           (Fi : comp_cat_functor_preserves_el F el₁ el₂)
  : UU
  := ∏ (Γ Δ : C₁)
       (s : Γ --> Δ)
       (t : tm Δ (comp_cat_univ Δ)),
     comp_cat_functor_subst_ty_coe F s _
     · coerce_subst_ty (#F s) (Fi Δ t : _ --> _)
     · comp_cat_univ_el_stable el₂ (#F s) (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Δ)
     =
     comp_cat_functor_coerce F (comp_cat_univ_el_stable el₁ s t : _ --> _)
     · Fi Γ (t [[ s ]]tm ↑ sub_comp_cat_univ _)
     · comp_cat_el_map_on_eq_iso _ (comp_cat_functor_preserves_stable_el_path F s t).

Proposition isaprop_comp_cat_functor_preserves_stable_el
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            (el₁ : comp_cat_univ_type C₁)
            (el₂ : comp_cat_univ_type C₂)
            (Fi : comp_cat_functor_preserves_el F el₁ el₂)
  : isaprop (comp_cat_functor_preserves_stable_el el₁ el₂ Fi).
Proof.
  do 4 (use impred ; intro).
  apply homset_property.
Qed.

Proposition comp_cat_functor_preserves_stable_el_alt
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            {Fi : comp_cat_functor_preserves_el F el₁ el₂}
            (Fii : comp_cat_functor_preserves_stable_el el₁ el₂ Fi)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : comp_cat_functor_coerce F (comp_cat_univ_el_stable el₁ s t : _ --> _)
    · Fi Γ (t [[ s ]]tm ↑ sub_comp_cat_univ _)
    =
    comp_cat_functor_subst_ty_coe F s _
    · coerce_subst_ty (#F s) (Fi Δ t : _ --> _)
    · comp_cat_univ_el_stable el₂ (#F s) (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Δ)
    · comp_cat_el_map_on_eq_iso _ (!comp_cat_functor_preserves_stable_el_path F s t).
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply Fii.
  }
  rewrite !assoc'.
  etrans.
  {
    do 2 apply maponpaths.
    refine (!_).
    apply comp_cat_el_map_on_concat.
  }
  rewrite comp_cat_el_map_on_idpath.
  rewrite id_right.
  apply idpath.
Qed.

Definition comp_cat_functor_preserves_univ_type
           {C₁ C₂ : comp_cat_with_ob}
           (F : comp_cat_functor_ob C₁ C₂)
           (el₁ : comp_cat_univ_type C₁)
           (el₂ : comp_cat_univ_type C₂)
  : UU
  := ∑ (Fi : comp_cat_functor_preserves_el F _ _),
     comp_cat_functor_preserves_stable_el el₁ el₂ Fi.

Proposition isaset_comp_cat_functor_preserves_univ_type
            {C₁ C₂ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            (el₁ : comp_cat_univ_type C₁)
            (el₂ : comp_cat_univ_type C₂)
  : isaset (comp_cat_functor_preserves_univ_type F el₁ el₂).
Proof.
  use isaset_total2.
  - apply isaset_comp_cat_functor_preserves_el.
  - intro.
    apply isasetaprop.
    apply isaprop_comp_cat_functor_preserves_stable_el.
Qed.

Definition make_comp_cat_functor_preserves_univ_type
           {C₁ C₂ : comp_cat_with_ob}
           (F : comp_cat_functor_ob C₁ C₂)
           {el₁ : comp_cat_univ_type C₁}
           {el₂ : comp_cat_univ_type C₂}
           (Fi : comp_cat_functor_preserves_el F _ _)
           (Fii : comp_cat_functor_preserves_stable_el el₁ el₂ Fi)
  : comp_cat_functor_preserves_univ_type F el₁ el₂
  := Fi ,, Fii.

Definition comp_cat_functor_preserves_univ_type_el_iso
           {C₁ C₂ : comp_cat_with_ob}
           {F : comp_cat_functor_ob C₁ C₂}
           {el₁ : comp_cat_univ_type C₁}
           {el₂ : comp_cat_univ_type C₂}
           (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
           {Γ : C₁}
           (t : tm Γ (comp_cat_univ Γ))
  : z_iso
      (C := fiber_category _ _)
      (comp_cat_type_functor
         F
         _
         (comp_cat_univ_el el₁ t))
      (comp_cat_univ_el
         el₂
         (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Γ))
  := pr1 Fi Γ t.

Definition comp_cat_functor_preserves_univ_type_el_mor
           {C₁ C₂ : comp_cat_with_ob}
           {F : comp_cat_functor_ob C₁ C₂}
           {el₁ : comp_cat_univ_type C₁}
           {el₂ : comp_cat_univ_type C₂}
           (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
           {Γ : C₁}
           (t : tm Γ (comp_cat_univ Γ))
  : comp_cat_type_functor
      F
      _
      (comp_cat_univ_el el₁ t)
    <:
    comp_cat_univ_el
      el₂
      (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Γ).
Proof.
  exact (comp_cat_functor_preserves_univ_type_el_iso Fi t : _ --> _).
Defined.

Proposition comp_cat_functor_preserves_univ_type_eq
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            {Fi₁ Fi₂ : comp_cat_functor_preserves_univ_type F el₁ el₂}
            (p : ∏ (Γ : C₁)
                   (t : tm Γ (comp_cat_univ Γ)),
                 comp_cat_functor_preserves_univ_type_el_mor Fi₁ t
                 =
                 comp_cat_functor_preserves_univ_type_el_mor Fi₂ t)
  : Fi₁ = Fi₂.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_comp_cat_functor_preserves_stable_el.
  }
  use funextsec ; intro Γ.
  use funextsec ; intro t.
  use z_iso_eq.
  exact (p Γ t).
Qed.

Lemma comp_cat_functor_preserves_univ_type_el_mor_natural_path
      {C₁ C₂ : comp_cat_with_ob}
      (F : comp_cat_functor_ob C₁ C₂)
      {Γ : C₁}
      {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
      (p : t₁ = t₂)
  : comp_cat_functor_tm F t₁ ↑ functor_comp_cat_on_univ F Γ
    =
    comp_cat_functor_tm F t₂ ↑ functor_comp_cat_on_univ F Γ.
Proof.
  induction p.
  apply idpath.
Qed.

Proposition comp_cat_functor_preserves_univ_type_el_mor_natural
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {u₁ : comp_cat_univ_type C₁}
            {u₂ : comp_cat_univ_type C₂}
            (Fu : comp_cat_functor_preserves_univ_type F u₁ u₂)
            {Γ : C₁}
            {t₁ t₂ : tm Γ (comp_cat_univ Γ)}
            (p : t₁ = t₂)
  : comp_cat_functor_coerce F (comp_cat_el_map_on_eq _ p)
    · comp_cat_functor_preserves_univ_type_el_mor Fu t₂
    =
    comp_cat_functor_preserves_univ_type_el_mor Fu t₁
    · comp_cat_el_map_on_eq _ (comp_cat_functor_preserves_univ_type_el_mor_natural_path F p).
Proof.
  induction p.
  rewrite !comp_cat_el_map_on_idpath.
  rewrite comp_cat_functor_coerce_on_id.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Proposition comp_cat_functor_preserves_univ_type_el_stable
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : comp_cat_functor_subst_ty_coe F s _
    · coerce_subst_ty (#F s) (comp_cat_functor_preserves_univ_type_el_mor Fi t)
    · comp_cat_univ_el_stable el₂ (#F s) (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Δ)
    =
    comp_cat_functor_coerce F (comp_cat_univ_el_stable el₁ s t : _ --> _)
    · comp_cat_functor_preserves_univ_type_el_iso Fi (t [[ s ]]tm ↑ sub_comp_cat_univ _)
    · comp_cat_el_map_on_eq_iso _ (comp_cat_functor_preserves_stable_el_path F s t).
Proof.
  exact (pr2 Fi Γ Δ s t).
Qed.

Proposition comp_cat_functor_preserves_univ_type_el_stable_alt
            {C₁ C₂ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
            {Γ Δ : C₁}
            (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : comp_cat_functor_coerce F (comp_cat_univ_el_stable el₁ s t : _ --> _)
    · comp_cat_functor_preserves_univ_type_el_iso Fi (t [[ s ]]tm ↑ sub_comp_cat_univ _)
    =
    comp_cat_functor_subst_ty_coe F s _
    · coerce_subst_ty (#F s) (comp_cat_functor_preserves_univ_type_el_mor Fi t)
    · comp_cat_univ_el_stable el₂ (#F s) (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Δ)
    · comp_cat_el_map_on_eq_inv _ (comp_cat_functor_preserves_stable_el_path F s t).
Proof.
  rewrite comp_cat_functor_preserves_univ_type_el_stable.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_inv.
    }
    refine (!(comp_cat_el_map_on_concat _ _ _) @ _).
    apply comp_cat_el_map_on_idpath.
  }
  rewrite id_right.
  apply idpath.
Qed.

(** * 8. Preservation of universes by identity and composition *)
Proposition id_comp_cat_functor_preserves_el_lem
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
            {Γ : C}
            (t : tm Γ (comp_cat_univ Γ))
  : t = comp_cat_functor_tm (id₁ _) t ↑ functor_comp_cat_on_univ (id₁ C) Γ.
Proof.
  refine (!_).
  rewrite id_comp_cat_functor_tm.
  rewrite id_functor_comp_cat_on_univ.
  rewrite id_coerce_comp_cat_tm.
  apply idpath.
Qed.

Definition id_comp_cat_functor_preserves_el
           {C : comp_cat_with_ob}
           (el : comp_cat_univ_type C)
  : comp_cat_functor_preserves_el (id₁ C) el el.
Proof.
  intros Γ t ; simpl.
  use comp_cat_el_map_on_eq_iso.
  exact (id_comp_cat_functor_preserves_el_lem el t).
Defined.

Definition id_comp_cat_functor_ob
           (C : comp_cat_with_ob)
  : comp_cat_functor_ob C C
  := id₁ C.

Lemma id_comp_cat_functor_preserves_stable_el_eq
      {C : comp_cat_with_ob}
      (el : comp_cat_univ_type C)
      {Γ Δ : C}
      (s : Γ --> Δ)
            (t : tm Δ (comp_cat_univ Δ))
  : comp_cat_functor_subst_ty_coe (id₁ _) s (comp_cat_univ_el el t)
    · coerce_subst_ty
        (#(id_comp_cat_functor_ob C) s)
        (id_comp_cat_functor_preserves_el el Δ t : _ --> _)
    · comp_cat_univ_el_stable el s (comp_cat_functor_tm (id₁ _) t
      ↑ functor_comp_cat_on_univ (id₁ C) Δ)
    =
    comp_cat_functor_coerce (id₁ _) (comp_cat_univ_el_stable el s t : _ --> _)
    · id_comp_cat_functor_preserves_el el Γ (t [[ s ]]tm ↑ sub_comp_cat_univ s)
    · comp_cat_el_map_on_eq_iso
        (@comp_cat_univ_el C el)
        (comp_cat_functor_preserves_stable_el_path (id₁ C) s t).
Proof.
  etrans.
  {
    do 2 apply maponpaths_2.
    exact (id_comp_cat_functor_subst_ty_coe s (comp_cat_univ_el el t)).
  }
  etrans.
  {
    apply maponpaths_2.
    apply (id_left (coerce_subst_ty s (id_comp_cat_functor_preserves_el el Δ t : _ --> _))).
  }
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths_2.
    apply id_comp_cat_functor_coerce.
  }
  unfold id_comp_cat_functor_preserves_el.
  refine (assoc' _ _ _ @ _).
  etrans.
  {
    apply maponpaths.
    refine (!_).
    exact (comp_cat_el_map_on_concat el _ _).
  }
  etrans.
  {
    use comp_cat_stable_el_map_on_eq.
    abstract
      (rewrite id_comp_cat_functor_tm ;
       rewrite id_functor_comp_cat_on_univ ;
       rewrite id_coerce_comp_cat_tm ;
       apply idpath).
  }
  refine (maponpaths (λ z, z · comp_cat_univ_el_stable el s _) _).
  cbn -[coerce_subst_ty].
  apply maponpaths.
  apply eq_comp_cat_el_map_on_eq.
Qed.

Proposition id_comp_cat_functor_preserves_stable_el
            {C : comp_cat_with_ob}
            (el : comp_cat_univ_type C)
  : comp_cat_functor_preserves_stable_el
      el
      el
      (id_comp_cat_functor_preserves_el el).
Proof.
  intros Γ Δ s t.
  refine (_ @ id_comp_cat_functor_preserves_stable_el_eq el s t).
  refine (maponpaths (λ z, z · comp_cat_univ_el_stable el s _) _).
  apply idpath.
Qed.

Definition id_comp_cat_functor_preserves_univ_type
           {C : comp_cat_with_ob}
           (el : comp_cat_univ_type C)
  : comp_cat_functor_preserves_univ_type (id₁ C) el el.
Proof.
  use make_comp_cat_functor_preserves_univ_type.
  - apply id_comp_cat_functor_preserves_el.
  - apply id_comp_cat_functor_preserves_stable_el.
Defined.

Proposition comp_comp_cat_functor_preserves_el_path
            {C₁ C₂ C₃ : comp_cat_with_ob}
            (F : comp_cat_functor_ob C₁ C₂)
            (G : comp_cat_functor_ob C₂ C₃)
            {Γ : C₁}
            (t : tm Γ (comp_cat_univ Γ) )
  : comp_cat_functor_tm G (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Γ)
    ↑ functor_comp_cat_on_univ G (F Γ)
    =
    comp_cat_functor_tm (pr1 F · pr1 G) t ↑ functor_comp_cat_on_univ (F · G) Γ.
Proof.
  rewrite comp_comp_cat_functor_tm.
  rewrite comp_functor_comp_cat_on_univ.
  rewrite <- comp_coerce_comp_cat_tm.
  apply maponpaths.
  rewrite comp_cat_functor_coerce_tm.
  apply idpath.
Qed.

Definition comp_comp_cat_functor_preserves_el
           {C₁ C₂ C₃ : comp_cat_with_ob}
           {F : comp_cat_functor_ob C₁ C₂}
           {G : comp_cat_functor_ob C₂ C₃}
           {el₁ : comp_cat_univ_type C₁}
           {el₂ : comp_cat_univ_type C₂}
           {el₃ : comp_cat_univ_type C₃}
           (Fi : comp_cat_functor_preserves_el F el₁ el₂)
           (Gi : comp_cat_functor_preserves_el G el₂ el₃)
  : comp_cat_functor_preserves_el (F · G) el₁ el₃.
Proof.
  intros Γ t ; simpl.
  refine (z_iso_comp
            (functor_on_z_iso
               (fiber_functor (comp_cat_type_functor G) _)
               (Fi Γ t))
            _).
  refine (z_iso_comp (Gi _ _) _).
  use comp_cat_el_map_on_eq_iso.
  apply comp_comp_cat_functor_preserves_el_path.
Defined.

Proposition eq_comp_comp_cat_functor_preserves_el
            {C₁ C₂ C₃ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {G : comp_cat_functor_ob C₂ C₃}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            {el₃ : comp_cat_univ_type C₃}
            (Fi : comp_cat_functor_preserves_el F el₁ el₂)
            (Gi : comp_cat_functor_preserves_el G el₂ el₃)
            {Γ : C₁}
            (t : tm Γ (comp_cat_univ Γ) )
  : (comp_comp_cat_functor_preserves_el Fi Gi Γ t : _ --> _)
    =
    comp_cat_functor_coerce G (Fi _ _ : _ --> _)
    · Gi _ _
    · comp_cat_el_map_on_eq_iso _ (comp_comp_cat_functor_preserves_el_path F G t).
Proof.
  rewrite assoc'.
  assert (comp_cat_functor_coerce G (Fi Γ t : _ --> _)
          =
          #(fiber_functor (comp_cat_type_functor G) (F Γ)) (Fi Γ t)) as ->.
  {
    apply idpath.
  }
  refine (maponpaths (λ z, #(fiber_functor (comp_cat_type_functor G) (F Γ)) (Fi Γ t) · z) _).
  refine (maponpaths (λ z, _ · z) _).
  simpl.
  apply idpath.
Qed.

#[local] Opaque coerce_subst_ty.

Lemma comp_comp_cat_functor_preserves_stable_el_path
      {C₁ C₂ C₃ : comp_cat_with_ob}
      (F : comp_cat_functor_ob C₁ C₂)
      (G : comp_cat_functor_ob C₂ C₃)
      {Γ : C₁}
      (t : tm Γ (comp_cat_univ Γ))
  : comp_cat_functor_tm G (comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Γ)
    ↑ functor_comp_cat_on_univ G (F Γ)
    =
    comp_cat_functor_tm (F · G : comp_cat_functor_ob C₁ C₃) t
    ↑ functor_comp_cat_on_univ (F · G) Γ.
Proof.
  rewrite comp_functor_comp_cat_on_univ.
  rewrite <- comp_coerce_comp_cat_tm.
  apply maponpaths.
  rewrite comp_cat_functor_coerce_tm.
  apply maponpaths.
  refine (!_).
  exact (comp_comp_cat_functor_tm F G t).
Qed.

Proposition comp_comp_cat_functor_preserves_stable_el
            {C₁ C₂ C₃ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {G : comp_cat_functor_ob C₂ C₃}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            {el₃ : comp_cat_univ_type C₃}
            {Fi : comp_cat_functor_preserves_el F el₁ el₂}
            (Fii : comp_cat_functor_preserves_stable_el el₁ el₂ Fi)
            {Gi : comp_cat_functor_preserves_el G el₂ el₃}
            (Gii : comp_cat_functor_preserves_stable_el el₂ el₃ Gi)
  : comp_cat_functor_preserves_stable_el
      el₁ el₃
      (comp_comp_cat_functor_preserves_el Fi Gi).
Proof.
  intros Γ Δ s t.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply comp_comp_cat_functor_subst_ty_coe.
  }
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    unfold comp_comp_cat_functor_preserves_el.
    apply (comp_coerce_subst_ty
             _
             (comp_cat_functor_coerce G (Fi Δ t : _ --> _))).
  }
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths_2.
    apply comp_comp_cat_functor_coerce.
  }
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    apply eq_comp_comp_cat_functor_preserves_el.
  }
  rewrite !assoc.
  etrans.
  {
    do 3 apply maponpaths_2.
    refine (!_).
    apply (comp_cat_functor_coerce_on_comp G).
  }
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    exact (comp_cat_functor_preserves_stable_el_alt Fii s t).
  }
  rewrite !comp_cat_functor_coerce_on_comp.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      do 2 refine (assoc (C := fiber_category _ _) _ _ _ @ _).
      do 2 apply maponpaths_2.
      apply comp_cat_functor_preserves_el_natural.
    }
    refine (assoc (C := fiber_category _ _) _ _ _ @ _).
    apply maponpaths_2.
    refine (assoc (C := fiber_category _ _) _ _ _ @ _).
    apply maponpaths_2.
    refine (assoc (C := fiber_category _ _) _ _ _ @ _).
    apply maponpaths_2.
    apply (comp_cat_functor_preserves_stable_el_alt Gii).
  }
  rewrite !assoc'.
  etrans.
  {
    do 4 apply maponpaths.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply comp_cat_el_map_on_concat.
    }
    refine (!_).
    apply comp_cat_el_map_on_concat.
  }
  etrans.
  {
    do 3 apply maponpaths.
    refine (!_).
    use comp_cat_univ_el_stable_natural.
    exact (comp_comp_cat_functor_preserves_stable_el_path F G t).
  }
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    do 2 apply maponpaths_2.
    apply comp_cat_functor_subst_ty_natural.
  }
  rewrite !assoc'.
  apply maponpaths.
  rewrite <- !comp_coerce_subst_ty.
  do 2 apply maponpaths.
  refine (maponpaths (λ z, _ · z) _).
  apply eq_comp_cat_el_map_on_eq.
Qed.

Definition comp_comp_cat_functor_preserves_univ_type
           {C₁ C₂ C₃ : comp_cat_with_ob}
           {F : comp_cat_functor_ob C₁ C₂}
           {G : comp_cat_functor_ob C₂ C₃}
           {el₁ : comp_cat_univ_type C₁}
           {el₂ : comp_cat_univ_type C₂}
           {el₃ : comp_cat_univ_type C₃}
           (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
           (Gi : comp_cat_functor_preserves_univ_type G el₂ el₃)
  : comp_cat_functor_preserves_univ_type (F · G) el₁ el₃.
Proof.
  use make_comp_cat_functor_preserves_univ_type.
  - exact (comp_comp_cat_functor_preserves_el (pr1 Fi) (pr1 Gi)).
  - exact (comp_comp_cat_functor_preserves_stable_el (pr2 Fi) (pr2 Gi)).
Defined.

Proposition eq_comp_comp_cat_functor_preserves_univ
            {C₁ C₂ C₃ : comp_cat_with_ob}
            {F : comp_cat_functor_ob C₁ C₂}
            {G : comp_cat_functor_ob C₂ C₃}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            {el₃ : comp_cat_univ_type C₃}
            (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
            (Gi : comp_cat_functor_preserves_univ_type G el₂ el₃)
            {Γ : C₁}
            (t : tm Γ (comp_cat_univ Γ) )
  : (comp_comp_cat_functor_preserves_el (pr1 Fi) (pr1 Gi) Γ t : _ --> _)
    =
    comp_cat_functor_coerce G (comp_cat_functor_preserves_univ_type_el_mor Fi _)
    · comp_cat_functor_preserves_univ_type_el_mor Gi _
    · comp_cat_el_map_on_eq_iso _ (comp_comp_cat_functor_preserves_el_path F G t).
Proof.
  apply eq_comp_comp_cat_functor_preserves_el.
Qed.

(** * 9. Preservation by natural transformations *)
Proposition comp_cat_nat_trans_preserves_univ_type_path
            {C₁ C₂ : comp_cat_with_ob}
            {F G : comp_cat_functor_ob C₁ C₂}
            (τ : comp_cat_nat_trans_ob F G)
            {Γ : C₁}
            (t : tm Γ (comp_cat_univ Γ))
  : comp_cat_functor_tm F t ↑ functor_comp_cat_on_univ F Γ
    =
    (comp_cat_functor_tm G t ↑ functor_comp_cat_on_univ G Γ) [[ τ Γ ]]tm
    ↑ sub_comp_cat_univ (τ Γ).
Proof.
  rewrite subst_coerce_comp_cat_tm.
  rewrite <- comp_cat_nat_trans_tm.
  rewrite !comp_coerce_comp_cat_tm.
  apply maponpaths_2.
  rewrite !assoc.
  rewrite <- comp_cat_nat_trans_on_univ_comm.
  rewrite !assoc'.
  refine (!(id_right _) @ _).
  apply maponpaths.
  refine (!_).
  apply z_iso_after_z_iso_inv.
Qed.

Definition comp_cat_nat_trans_preserves_univ_type
           {C₁ C₂ : comp_cat_with_ob}
           {F G : comp_cat_functor_ob C₁ C₂}
           (τ : comp_cat_nat_trans_ob F G)
           {el₁ : comp_cat_univ_type C₁}
           {el₂ : comp_cat_univ_type C₂}
           (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
           (Gi : comp_cat_functor_preserves_univ_type G el₁ el₂)
  : UU
  := ∏ (Γ : C₁)
       (t : tm Γ (comp_cat_univ Γ)),
     comp_cat_functor_preserves_univ_type_el_mor Fi t
     · comp_cat_el_map_on_eq el₂ (comp_cat_nat_trans_preserves_univ_type_path τ t)
     =
     comp_cat_type_fib_nat_trans τ _
     · coerce_subst_ty _ (comp_cat_functor_preserves_univ_type_el_mor Gi t)
     · comp_cat_univ_el_stable el₂ (τ Γ) _.

Proposition comp_cat_nat_trans_preserves_univ_type_alt
            {C₁ C₂ : comp_cat_with_ob}
            {F G : comp_cat_functor_ob C₁ C₂}
            {τ : comp_cat_nat_trans_ob F G}
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            {Fi : comp_cat_functor_preserves_univ_type F el₁ el₂}
            {Gi : comp_cat_functor_preserves_univ_type G el₁ el₂}
            (τi : comp_cat_nat_trans_preserves_univ_type τ Fi Gi)
            {Γ : C₁}
            (t : tm Γ (comp_cat_univ Γ))
  : comp_cat_functor_preserves_univ_type_el_mor Fi t
    =
    comp_cat_type_fib_nat_trans τ _
    · coerce_subst_ty _ (comp_cat_functor_preserves_univ_type_el_mor Gi t)
    · comp_cat_univ_el_stable el₂ (τ Γ) _
    · comp_cat_el_map_on_eq el₂ (!(comp_cat_nat_trans_preserves_univ_type_path τ t)).
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    apply τi.
  }
  rewrite !assoc'.
  rewrite <- comp_cat_el_map_on_concat.
  rewrite comp_cat_el_map_on_idpath.
  apply id_right.
Qed.

Proposition isaprop_comp_cat_nat_trans_preserves_univ_type
            {C₁ C₂ : comp_cat_with_ob}
            {F G : comp_cat_functor_ob C₁ C₂}
            (τ : comp_cat_nat_trans_ob F G)
            {el₁ : comp_cat_univ_type C₁}
            {el₂ : comp_cat_univ_type C₂}
            (Fi : comp_cat_functor_preserves_univ_type F el₁ el₂)
            (Gi : comp_cat_functor_preserves_univ_type G el₁ el₂)
  : isaprop (comp_cat_nat_trans_preserves_univ_type τ Fi Gi).
Proof.
  do 2 (use impred ; intro).
  apply homset_property.
Qed.
