(** Universe in Comprehension Categories

  Let C be a comprehension category with a terminal empty context [].
  We say C has a universe if we have :
  - U : ty [], which gives rise to U_Γ : ty Γ
  - a function el : tm U_Γ ➙ ty Γ
  - for each s : Γ → Δ and t : tm U_Δ, an isomorphism i : el (t) [s] ≃ el (t[s])
  such that i commutes with i_id and i_comp.
  - a coherence condition

  This definition is similar to the definition of universe in comprehension bicategories
  presented in "The Internal Language of Univalent Categories" by Van der Weide.
  A similar definition for CwFs is presented in "Principles of Dependent Type Theory"
  by Angiuli and Gratzer.

  We also define the universe being closed under type formers similar to Van der Weide. 
  We look at unit, Σ and Π.

  References
  - "The Internal Languages of Univalent Categories" by Van der Weide
  - "Principles of Dependent Type Theory" by Angiuli and Gratzer

  Contents
  0. Lemmas about Isomorphisms
  1. Empty Context in Comprehension Categories
  2. Comprehension Category with a Universe
  3. Lemmas about Universes
  4. Universes being closed under Σ-types
  5. Lemmas about universes closed under Σ-types
  6. Universes being closed under unit types
  7. Universes being closed under Π-types
  8. Lemmas about universes closed under Π-types
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.

Require Import UniMath.CategoryTheory.ComprehensionCats.CompCats.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatTypeFormers.

Local Open Scope cat.
Local Open Scope comp_cat.


(** * 0. Lemmas about Isomorphisms *)

Lemma z_iso_comp_assoc' {C : category} {a b c d : C}
  (f : z_iso a b) (g : z_iso b c) (h : z_iso c d)
  : z_iso_comp (z_iso_comp f g) h = z_iso_comp f (z_iso_comp g h).
Proof.
  use z_iso_eq.
  apply assoc'.
Qed.

Lemma z_iso_inv_after_z_iso' {C : category} {a b : C}
  (f : z_iso a b)
  : z_iso_comp (f) (z_iso_inv f) = identity_z_iso _.
Proof.
  use z_iso_eq.
  apply z_iso_inv_after_z_iso.
Qed.

Lemma z_iso_id_left {C: category} {a b : C}
  (f : z_iso a b)
  : z_iso_comp (identity_z_iso _) f = f.
Proof.
  use z_iso_eq.
  apply id_left.
Qed.

Lemma z_iso_id_right {C: category} {a b : C}
  (f : z_iso a b)
  : z_iso_comp f (identity_z_iso _) = f.
Proof.
  use z_iso_eq.
  apply id_right.
Qed.

(** * 1. Comprehension category with a terminal context  *)

Definition comp_cat_with_terminal : UU :=  ∑ (C : comp_cat), Terminal C.

Coercion comp_cat_with_terminal_to_comp_cat (C : comp_cat_with_terminal) : comp_cat := pr1 C.

Definition empty_context (C : comp_cat_with_terminal) : Terminal C := pr2 C.

Notation "'[]'" := (empty_context _) : comp_cat.

Definition weakened_from_empty {C: comp_cat_with_terminal} (A : comp_cat_ty ([] : C)) (Γ : C)
  : comp_cat_ty Γ
  := A [[ TerminalArrow (empty_context C) Γ ]].

Definition sub_comp_cat_univ_iso {C : comp_cat_with_terminal} {Γ Δ : C}
  (U : comp_cat_ty []) (s : Γ --> Δ)
  : z_iso (C := fiber_category _ _) ((weakened_from_empty U _) [[ s ]]) (weakened_from_empty U Γ).
Proof.
  set (T := empty_context C).
  set (tΔ := TerminalArrow T Δ : Δ --> ([] : C)).
  set (tΓ := TerminalArrow T Γ : Γ --> ([] : C)).
  assert (p : s · tΔ = tΓ) by apply TerminalArrowEq.

  (* (U[[tΔ]])[[s]]  ≅  U[[s·tΔ]]  ≅  U[[tΓ]] *)
  refine (z_iso_comp (comp_cat_subst_ty_comp_iso U tΔ s) _).
  exact (comp_cat_subst_ty_iso U p).
Defined.


(** Lemmas about [sub_comp_cat_univ_iso] *)

Lemma sub_comp_cat_univ_iso_eq
  {C : comp_cat_with_terminal} {Γ Δ : C}
  (U : comp_cat_ty ([] : C)) (s : Γ --> Δ)
  (p : s · TerminalArrow (empty_context C) Δ = TerminalArrow (empty_context C) Γ)
  : ⌈sub_comp_cat_univ_iso U s⌉
    = ⌈comp_cat_subst_ty_comp_iso U (TerminalArrow (empty_context C) Δ) s⌉
        · ⌈comp_cat_subst_ty_iso U p⌉.
Proof.
  unfold sub_comp_cat_univ_iso.
  apply cancel_precomposition.
  apply maponpaths.
  apply comp_cat_subst_ty_iso_path_eq.
Qed.

Lemma sub_comp_cat_univ_iso_natural
  {C : comp_cat_with_terminal} {Γ Δ : C}
  (U : comp_cat_ty ([] : C))
  {s s' : Γ --> Δ} (p : s = s')
  : ⌈comp_cat_subst_ty_iso (weakened_from_empty U Δ) p⌉
      · ⌈sub_comp_cat_univ_iso U s'⌉
    = ⌈sub_comp_cat_univ_iso U s⌉.
Proof.
  induction p.
  apply id_left.
Qed.

Lemma sub_comp_cat_univ_iso_comp
  {C : comp_cat_with_terminal} {Γ Δ Θ : C}
  (U : comp_cat_ty ([] : C))
  (s₁ : Γ --> Δ) (s₂ : Θ --> Γ)
  : comp_cat_reindex_coercion s₂ (⌈sub_comp_cat_univ_iso U s₁⌉)
      · ⌈sub_comp_cat_univ_iso U s₂⌉
    = ⌈comp_cat_subst_ty_comp_iso (weakened_from_empty U Δ) s₁ s₂⌉
        · ⌈sub_comp_cat_univ_iso U (s₂ · s₁)⌉.
Proof.
  rewrite (sub_comp_cat_univ_iso_eq U s₁ (TerminalArrowEq _ _)).
  rewrite (sub_comp_cat_univ_iso_eq U s₂ (TerminalArrowEq _ _)).
  rewrite (sub_comp_cat_univ_iso_eq U (s₂ · s₁) (TerminalArrowEq _ _)).
  rewrite comp_cat_reindex_coercion_comp_witness.
  do 2 rewrite assoc.
  etrans.
  { apply maponpaths_2.
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply (comp_cat_reindex_coercion_subst_ty_iso (C := C)). }
  rewrite assoc.
  etrans.
  { do 2 apply maponpaths_2.
    refine (!_).
    apply (comp_cat_assoc'_subst_ty (C := C)). }
  do 3 (etrans; [ apply assoc'|]).
  refine (!_).
  (etrans; [ apply assoc'|]).
  do 2 apply maponpaths.
  refine (!_).
  etrans. {
    apply maponpaths.
    apply comp_cat_subst_ty_iso_comp. }
  etrans. { apply comp_cat_subst_ty_iso_comp. }
  apply maponpaths.
  apply comp_cat_subst_ty_iso_path_eq.
Qed.

(** *  2. Comprehension category with a terminal context and universe *)

(*
Let C be a comprehension category with a terminal empty context [].
We say C has a universe if we have :
  - U : ty [], which gives rise to U_Γ : ty Γ
  - a function el : tm U_Γ \to ty Γ
  - for each s : Γ → Δ and t : tm U_Δ, an isomorphism i : el (t) [s] ≃ el (t[s])
  such that i commutes with i_id and i_comp.
  - coherence
 *)

Definition comp_cat_universe_data (C: comp_cat_with_terminal) : UU
  := ∑ (U : comp_cat_ty []),
    ∑ (el : ∏ (Γ : C), comp_cat_tm (weakened_from_empty U _) -> comp_cat_ty Γ),
    (∏ (Γ Δ : C) (s : Γ --> Δ) (t : comp_cat_tm (weakened_from_empty U _)),
      @z_iso (fiber_category _ _)
        ((el _ t) [[ s ]])
        (el _ (t [[ s ]]tm ↑ ⌈sub_comp_cat_univ_iso U s⌉))).

Local Definition el_map {C: comp_cat_with_terminal} (universe: comp_cat_universe_data C)
  (Γ : C) {a b : comp_cat_tm (weakened_from_empty (pr1 universe) _)}
  (p : a = b)
  : (( pr12 universe) Γ a) -->[identity Γ] (( pr12 universe) Γ b).
Proof.
  induction p.
  apply id_disp.
Defined.

Section Universe_Coherence.
  Context {C : comp_cat_with_terminal}
    (universe : comp_cat_universe_data C)
    (U := pr1 universe)
    (el := pr12 universe)
    (i := pr22 universe).

  Lemma elmaplemma {Γ : C}
    {t : comp_cat_tm (weakened_from_empty U Γ)} :
    t [[identity Γ ]]tm
      ↑ ⌈ sub_comp_cat_univ_iso (pr1 universe) (identity Γ)⌉ = t.
  Proof.
    rewrite comp_cat_subst_tm_id.
    rewrite comp_cat_comp_coerce_tm.
    unfold sub_comp_cat_univ_iso.
    rewrite <- comp_cat_id_coerce_tm.
    apply comp_cat_coerce_eq.
    refine (_ @ comp_cat_id_left_subst_ty _ _).
    rewrite assoc'.
    cbn.
    do 6 apply maponpaths.
    apply homset_property.
  Qed.

  Definition coherent_id
    : UU
    := ∏ (Γ : C)
         (t : comp_cat_tm (weakened_from_empty U _)),
      @identity (fiber_category _ _) (el _ t ) =
        comp_cat_subst_ty_id_iso _
          · i _ _ (identity Γ) t
          · el_map _ _ elmaplemma.

  Lemma elmaplemmacomp
    {Γ Δ Θ : C}
    {s₁ : Γ --> Δ} {s₂ : Θ --> Γ}
    {t : comp_cat_tm (weakened_from_empty U _)} :
    t [[ s₂ · s₁ ]]tm ↑ ⌈ sub_comp_cat_univ_iso U (s₂ · s₁) ⌉
    = (t [[ s₁ ]]tm ↑ ⌈ sub_comp_cat_univ_iso U s₁ ⌉)
        [[ s₂ ]]tm ↑ ⌈ sub_comp_cat_univ_iso U s₂ ⌉.
  Proof.
    rewrite comp_cat_subst_coerce_tm.
    rewrite comp_cat_comp_coerce_tm.
    etrans.
    { apply maponpaths.
      apply comp_cat_subst_tm_comp. }
    rewrite comp_cat_comp_coerce_tm.
    apply comp_cat_coerce_eq.
    unfold " ⌈ _ ⌉".
    unfold sub_comp_cat_univ_iso.
    refine ( assoc _ _ _ @ _).
    etrans.
    { apply maponpaths_2.
      apply (comp_cat_assoc_subst_ty _ _ _ U). }
    etrans.
    2: {
      apply maponpaths_2.
      refine (!_).
      refine (_ @  comp_cat_reindex_coercion_comp_witness _ _ _).
      apply maponpaths.
      apply idpath.
    }
    do 3 rewrite assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply comp_cat_subst_ty_iso_comp. }
    etrans.
    2 : {
      apply (assoc' _ (comp_cat_subst_ty_comp_iso U (TerminalArrow [] Γ) s₂) _ ).
    }
    etrans.
    2: {
      apply maponpaths_2.
      refine (!_).
      apply (comp_cat_reindex_coercion_subst_ty_iso _ U).
    }
    etrans.
    2:
      {
      rewrite assoc'.
      apply maponpaths.
      refine (!_).
      apply comp_cat_subst_ty_iso_comp.
    }
    do 3 apply maponpaths.
    apply homset_property.
  Qed.

  Definition coherent_comp : UU
    := ∏ (Γ Δ Θ : C) (s₁ : Γ --> Δ) (s₂ : Θ --> Γ)
         (t : comp_cat_tm (weakened_from_empty U _)),
      comp_cat_reindex_iso s₂ (i _ _ s₁ t) · (i _ _ s₂ _)
      = comp_cat_subst_ty_comp_iso (el _ t) s₁ s₂
          · (i _ _ (s₂ · s₁) t)
          · el_map _ _ elmaplemmacomp.

End Universe_Coherence.

Definition comp_cat_universe_coherent
  {C : comp_cat_with_terminal}
  (universe : comp_cat_universe_data C) : UU
  := coherent_id universe × coherent_comp universe.

Definition comp_cat_universe (C : comp_cat_with_terminal) : UU
  := ∑ (universe : comp_cat_universe_data C), comp_cat_universe_coherent universe.

Definition comp_cat_with_universe : UU := total2 comp_cat_universe.

Coercion comp_cat_with_universe_to_comp_cat (C : comp_cat_with_universe)
  : comp_cat_with_terminal := pr1 C.

Definition comp_cat_empty_ctx (C : comp_cat_with_universe) : Terminal C := pr21 C.

Definition comp_cat_U {C : comp_cat_with_universe} (Γ : C) : comp_cat_ty Γ
  := weakened_from_empty (pr112 C) Γ.

Definition comp_cat_el {C : comp_cat_with_universe} {Γ : pr1 C}
  (t : comp_cat_tm (comp_cat_U Γ))
  : comp_cat_ty Γ
  := (pr1 (pr212 C)) Γ t.

Definition comp_cat_el_iso {C : comp_cat_with_universe} {Γ Δ : C} (s : Γ --> Δ)
  (t : comp_cat_tm (comp_cat_U _))
  : @z_iso (fiber_category _ _)
      ((comp_cat_el t) [[ s ]])
      (comp_cat_el (t [[ s ]]tm ↑ ⌈sub_comp_cat_univ_iso _ s⌉))
  := (pr2 (pr212 C)) Γ Δ s t.

Definition comp_cat_univ_sub_iso
  {C : comp_cat_with_universe} {Γ Δ : C} (s : Γ --> Δ)
  : (z_iso (C := fiber_category _ _) ((comp_cat_U Δ) [[ s ]]) (comp_cat_U Γ)).
Proof.
  apply sub_comp_cat_univ_iso.
Defined.

Definition comp_cat_el_map {C: comp_cat_with_universe} {Γ : C} {a b : comp_cat_tm (comp_cat_U Γ)}
  (p : a = b)
  : (fiber_category _ _) ⟦( comp_cat_el a), (comp_cat_el b)⟧.
Proof.
  apply (el_map _ _ p).
Defined.


(** Lemmas about [comp_cat_el_map] and [comp_cat_el_z_iso_from_eq] *)

Lemma comp_cat_el_map_comp
  {C: comp_cat_with_universe} {Γ : C} {a b c : comp_cat_tm (comp_cat_U Γ)}
  (p : a = b) (q : b = c)
  : comp_cat_el_map p · comp_cat_el_map q = comp_cat_el_map (p @ q).
Proof.
  induction p , q.
  cbn.
  rewrite id_left_disp.
  assert (H : id_right (identity Γ) = id_left (identity Γ)) by apply homset_property.
  etrans.
  { apply maponpaths_2.
    apply H.
  }
  apply transportfbinv.
Qed.

Lemma comp_cat_el_map_id
  {C : comp_cat_with_universe}
  {Γ : C}
  (t : comp_cat_tm (comp_cat_U Γ))
  (p : t = t)
  : comp_cat_el_map (p) = identity (C := fiber_category _ _) (comp_cat_el t).
Proof.
  assert (H : p = idpath t) by apply comp_cat_tm_isaset.
  rewrite H.
  apply idpath.
Qed.

(* any two composites of el_maps with the same endpoints agree *)
Lemma comp_cat_el_map_eq_comp3 {C : comp_cat_with_universe}
  {Γ' : C} {a b c d : comp_cat_tm (comp_cat_U Γ')}
  (p : a = b) (p' : b = c) (p'' : c = d) (t : a = d)
  : comp_cat_el_map t
    = comp_cat_el_map p · comp_cat_el_map p' · comp_cat_el_map p''.
Proof.
  refine (_ @ ! maponpaths (λ z, z · comp_cat_el_map p'')
                (comp_cat_el_map_comp p p')).
  refine (_ @ ! comp_cat_el_map_comp _ _).
  apply maponpaths.
  apply comp_cat_tm_isaset.
Qed.

Definition comp_cat_el_z_iso_from_eq
  {C : comp_cat_with_universe}
  {Γ : C} {t t' : comp_cat_tm (comp_cat_U Γ)}
  (p : t = t')
  : z_iso (C := fiber_category _ _) (comp_cat_el t) (comp_cat_el t').
Proof.
  exact (idtoiso (C := fiber_category _ _) (maponpaths comp_cat_el p)).
Defined.

Lemma coe_comp_cat_el_z_iso_from_eq
  {C' : comp_cat_with_universe} {Γ' : C'}
  {t t' : comp_cat_tm (comp_cat_U Γ')} (p : t = t')
  : ⌈ comp_cat_el_z_iso_from_eq p ⌉ = comp_cat_el_map p.
Proof.
  induction p.
  apply idpath.
Qed.

Definition comp_cat_el_z_iso_from_eq_comp
  {C : comp_cat_with_universe}
  {Γ : C} {t t' t'': comp_cat_tm (comp_cat_U Γ)}
  (p : t = t') (p' : t' = t'')
  : comp_cat_el_z_iso_from_eq p
      · comp_cat_el_z_iso_from_eq p' = comp_cat_el_map (p @ p').
Proof.
  induction p , p'.
  cbn.
  rewrite id_left_disp.
  unfold transportb.
  rewrite transport_f_f.
  apply transportf_set.
  apply homset_property.
Qed.

Lemma comp_cat_el_z_iso_from_eq_comp'
  {C' : comp_cat_with_universe} {Γ' : C'}
  {t t' t'' : comp_cat_tm (comp_cat_U Γ')}
  (p : t = t') (p' : t' = t'')
  : z_iso_comp (comp_cat_el_z_iso_from_eq p) (comp_cat_el_z_iso_from_eq p')
    = comp_cat_el_z_iso_from_eq (p @ p').
Proof.
  induction p, p'.
  use z_iso_eq.
  apply id_left.
Qed.

Lemma comp_cat_el_z_iso_from_eq_id'
  {C : comp_cat_with_universe}
  {Γ : C}
  (t : comp_cat_tm (comp_cat_U Γ))
  (p : t = t)
  : comp_cat_el_z_iso_from_eq p
    = identity_z_iso (C := fiber_category _ _) (comp_cat_el t).
Proof.
  refine (maponpaths comp_cat_el_z_iso_from_eq
            (proofirrelevance _ (comp_cat_tm_isaset _ _) _ (idpath t)) @ _).
  apply idpath.
Qed.

Lemma comp_cat_el_z_iso_from_eq_inv
  { C : comp_cat_with_universe}
  {Γ : C}
  {a b : comp_cat_tm (comp_cat_U Γ)} (p : a = b)
  : ⌈comp_cat_el_z_iso_from_eq p⌉⁻¹ = comp_cat_el_map (! p).
Proof.
  induction p.
  apply idpath.
Qed.

Lemma comp_cat_el_z_iso_from_eq_pr1_comp_mor
  { C : comp_cat_with_universe}
  {Γ : C}
  {a b : comp_cat_tm (comp_cat_U Γ)} (p : a = b)
  : pr1 (comp_cat_comp_iso (comp_cat_el_z_iso_from_eq p)) = comp_cat_comp_mor (comp_cat_el_map p).
Proof.
  induction p.
  apply idpath.
Qed.

Definition comp_cat_univ_coherent_id
  {C : comp_cat_with_universe}
  (Γ : C)
  (t : comp_cat_tm (comp_cat_U Γ))
  : @identity (fiber_category _ _) (comp_cat_el t)
    = comp_cat_subst_ty_id_iso _
        · comp_cat_el_iso (identity Γ) t
        · comp_cat_el_map (elmaplemma _)
  := (pr122 C) Γ t.

Definition comp_cat_univ_coherent_comp
  {C : comp_cat_with_universe}
  {Γ Δ Θ : C}
  (s₁ : Γ --> Δ) (s₂ : Θ --> Γ)
  (t : comp_cat_tm (comp_cat_U _))
  : comp_cat_reindex_iso s₂ (comp_cat_el_iso s₁ t)
      · comp_cat_el_iso s₂ _
    = comp_cat_subst_ty_comp_iso (comp_cat_el t) s₁ s₂
        · comp_cat_el_iso (s₂ · s₁) t
        · comp_cat_el_map (elmaplemmacomp _)
  := (pr222 C) Γ Δ Θ s₁ s₂ t.

Definition comp_cat_univ_coherent_comp'
  {C : comp_cat_with_universe}
  {Γ Δ Θ : C}
  (s₁ : Γ --> Δ) (s₂ : Θ --> Γ)
  (t : comp_cat_tm (comp_cat_U _))
  : comp_cat_reindex_coercion s₂ (⌈comp_cat_el_iso s₁ t⌉)
      · comp_cat_el_iso s₂ _
    = comp_cat_subst_ty_comp_iso (comp_cat_el t) s₁ s₂
        · comp_cat_el_iso (s₂ · s₁) t
        · comp_cat_el_map (elmaplemmacomp _ ).
Proof.
  rewrite comp_cat_reindex_coercion_iso_eq.
  unfold "⌈ _ ⌉".
  apply (comp_cat_univ_coherent_comp (C:=C)).
Qed.

Definition comp_cat_univ_coherent_comp''
  {C : comp_cat_with_universe}
  {Γ Δ Θ : C} (s₁ : C ⟦ Γ, Δ ⟧) (s₂ : C ⟦ Θ, Γ ⟧)
  (t : comp_cat_tm (comp_cat_U Δ)) :
  z_iso_inv (comp_cat_subst_ty_comp_iso (comp_cat_el _) s₁ s₂)
    · comp_cat_reindex_iso s₂ (comp_cat_el_iso s₁ t)
    · comp_cat_el_iso s₂ (_ [[s₁ ]]tm ↑ ⌈ sub_comp_cat_univ_iso _ s₁ ⌉) ·
    comp_cat_el_map (! elmaplemmacomp _)
  = comp_cat_el_iso (s₂ · s₁) t.
Proof.
  (* the coherence of the universe, with the isos moved to the other side *)
  do 2 rewrite assoc'.
  use z_iso_inv_on_right.
  rewrite assoc.
  etrans.
  { apply maponpaths_2.
    apply comp_cat_univ_coherent_comp. }
  do 2 rewrite assoc'.
  etrans.
  { do 2 apply maponpaths.
    etrans.
    { apply comp_cat_el_map_comp. }
    etrans.
    { apply maponpaths.
      apply pathsinv0r. }
    apply (comp_cat_el_map_id _ (idpath _)). }
  apply maponpaths.
  apply id_right.
Qed.


(** * 3. Lemmas about Universes *)

Lemma comp_cat_univ_sub_iso_comp
  {C : comp_cat_with_universe} {Γ Δ Θ : C}
  (s₁ : Γ --> Δ) (s₂ : Θ --> Γ)
  :  ⌈comp_cat_univ_sub_iso (s₂ · s₁)⌉ =
       ⌈comp_cat_subst_ty_comp_iso (comp_cat_U Δ) s₁ s₂⌉⁻¹ ·
         comp_cat_reindex_coercion s₂ (⌈comp_cat_univ_sub_iso s₁⌉)
         · ⌈comp_cat_univ_sub_iso s₂⌉.
Proof.
  refine (!(id_left _) @ _).
  etrans.
  { apply maponpaths_2.
    refine (!_).
    apply (z_iso_after_z_iso_inv (comp_cat_subst_ty_comp_iso (comp_cat_U Δ) s₁ s₂)). }
  do 2 rewrite assoc'.
  apply maponpaths.
  refine (!_).
  exact (sub_comp_cat_univ_iso_comp (pr112 C) s₁ s₂).
Qed.

Lemma comp_cat_el_iso_natural
  { C : comp_cat_with_universe}
  {Γ Δ : C}
  (s : Γ --> Δ)
  {t₁ t₂ : comp_cat_tm (comp_cat_U Δ)}
  (p : t₁ = t₂)
  (q : t₁ [[ s ]]tm ↑ ⌈comp_cat_univ_sub_iso s⌉
       = t₂ [[ s ]]tm ↑ ⌈comp_cat_univ_sub_iso s⌉)
  : ⌈comp_cat_el_iso s t₁⌉ · comp_cat_el_map q =
      comp_cat_reindex_coercion (C:=C) _ (comp_cat_el_map p) · ⌈comp_cat_el_iso s t₂⌉.
Proof.
  induction p.
  assert (H : q = idpath _) by apply comp_cat_tm_isaset.
  unfold comp_cat_el_map.
  etrans.
  2: { apply maponpaths_2.
       refine (!_).
       apply maponpaths.
       apply (comp_cat_el_map_id _ (idpath _)). }
  rewrite comp_cat_reindex_coercion_id.
  rewrite id_left.
  rewrite H.
  rewrite <- id_right.
  apply maponpaths.
  apply idpath.
Qed.

Lemma comp_cat_el_iso_subst_path
  {C : comp_cat_with_universe} {Γ Δ : C}
  {s s' : Δ --> Γ} (p : s = s')
  (t : comp_cat_tm (comp_cat_U Γ))
  : ⌈comp_cat_el_iso s t⌉
      · comp_cat_el_map
      (maponpaths (fun f => t [[ f ]]tm ↑ ⌈comp_cat_univ_sub_iso f⌉) p)
    =
      ⌈comp_cat_subst_ty_iso (comp_cat_el t) p⌉
        · ⌈comp_cat_el_iso s' t⌉.
Proof.
  induction p.
  change (comp_cat_subst_ty_iso (comp_cat_el t) (idpath s)) with
    (idtoiso (C := fiber_category _ _) (idpath (comp_cat_el t [[s]]))).
  rewrite id_left, id_right.
  apply idpath.
Qed.

Lemma comp_cat_el_iso_el_map_el_iso_inv
  {C : comp_cat_with_universe}
  {Γ Δ : C} (t : comp_cat_tm (comp_cat_U Γ))
  {s s' : Δ --> Γ} (Hs : s = s')
  (p : t [[s]]tm ↑ ⌈comp_cat_univ_sub_iso s⌉
       =
         t [[s']]tm ↑ ⌈comp_cat_univ_sub_iso s'⌉)
  : ⌈comp_cat_el_iso s t⌉
      · comp_cat_el_map p
      · ⌈comp_cat_el_iso s' t⌉⁻¹
    = ⌈comp_cat_subst_ty_iso (comp_cat_el t) Hs⌉.
Proof.
  induction Hs.
  assert (Hp : p = idpath _) by apply comp_cat_tm_isaset.
  rewrite Hp.
  rewrite id_right.
  apply z_iso_inv_after_z_iso.
Qed.

Lemma transportf_tm_el_map
  { C : comp_cat_with_universe}
  {Γ : C}
  {a b : comp_cat_tm (comp_cat_U Γ)}
  (p : a = b) (t : comp_cat_tm (comp_cat_el a))
  : transportf (λ B : comp_cat_tm (comp_cat_U Γ), comp_cat_tm (comp_cat_el B)) p t
    = t ↑ comp_cat_el_map p.
Proof.
  induction p.
  refine (!_).
  apply comp_cat_id_coerce_tm.
Qed.

Lemma comp_cat_tm_subst_coerce_inv
  { C : comp_cat_with_universe}
  {Γ Δ : C} (i : z_iso Γ Δ) (t : comp_cat_tm (comp_cat_U Δ))
  : t = (t [[ i ]]tm ↑ ⌈comp_cat_univ_sub_iso i⌉)
          [[ inv_from_z_iso i ]]tm
          ↑ ⌈comp_cat_univ_sub_iso (inv_from_z_iso i)⌉.
Proof.
  refine (! elmaplemma (pr12 C) @ _).
  refine ((comp_cat_subst_coerce_tm_eq (! z_iso_after_z_iso_inv i) (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉) (sub_comp_cat_univ_iso_natural _ (! z_iso_after_z_iso_inv i)) t) @ _).
  rewrite comp_cat_subst_coerce_tm.
  refine (elmaplemmacomp _ @ _).
  rewrite comp_cat_subst_coerce_tm.
  rewrite !comp_cat_comp_coerce_tm.
  refine (comp_cat_coerce_eq _).
  apply idpath.
Qed.

Lemma comp_cat_tm_subst_coerce_inv'
  { C : comp_cat_with_universe}
  {Γ Δ : C} (i : z_iso Γ Δ) (t : comp_cat_tm (comp_cat_U Γ))
  : t = (t [[ inv_from_z_iso i ]]tm ↑ ⌈comp_cat_univ_sub_iso (inv_from_z_iso i)⌉)
          [[ i ]]tm
          ↑ ⌈comp_cat_univ_sub_iso i⌉.
Proof.
  refine (! elmaplemma (pr12 C) @ _).
  refine ((comp_cat_subst_coerce_tm_eq (! z_iso_inv_after_z_iso i) (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉) (sub_comp_cat_univ_iso_natural _ (! z_iso_inv_after_z_iso i)) t) @ _).
  rewrite comp_cat_subst_coerce_tm.
  refine (elmaplemmacomp _ @ _).
  rewrite comp_cat_subst_coerce_tm.
  rewrite !comp_cat_comp_coerce_tm.
  refine (comp_cat_coerce_eq _).
  apply idpath.
Qed.


(** Terms of the universe pulled back along substitutions *)

Definition comp_cat_pb_term_univ
  {C : comp_cat_with_universe} {Γ Δ : C}
  (t : comp_cat_tm (comp_cat_U Δ))
  (s : Γ --> Δ)
  : comp_cat_tm (comp_cat_U Γ)
  := t [[ s ]]tm ↑ ⌈ comp_cat_univ_sub_iso s ⌉.

Lemma comp_cat_pb_term_univ_comp
  {C : comp_cat_with_universe} {Γ Δ Θ : C}
  (t : comp_cat_tm (comp_cat_U Δ)) (s₁ : Γ --> Δ) (s₂ : Θ --> Γ)
  : comp_cat_pb_term_univ (comp_cat_pb_term_univ t s₁) s₂
    = comp_cat_pb_term_univ t (s₂ · s₁).
Proof.
  refine (!_).
  apply elmaplemmacomp.
Qed.

Lemma comp_cat_pb_term_univ_id
  {C : comp_cat_with_universe} {Γ : C} (t : comp_cat_tm (comp_cat_U Γ))
  : comp_cat_pb_term_univ t (identity Γ) = t.
Proof.
  apply elmaplemma.
Qed.

Definition comp_cat_el_pb_term_univ_comp
  {C : comp_cat_with_universe} {Γ Δ Θ : C}
  (t : comp_cat_tm (comp_cat_U Δ)) (s₁ : Γ --> Δ) (s₂ : Θ --> Γ)
  : z_iso (C := fiber_category _ _)
      (comp_cat_el (comp_cat_pb_term_univ (comp_cat_pb_term_univ t s₁) s₂))
      (comp_cat_el (comp_cat_pb_term_univ t (s₂ · s₁)))
  := comp_cat_el_z_iso_from_eq (comp_cat_pb_term_univ_comp t s₁ s₂).

Lemma comp_cat_el_pb_tm_comp
  {C : comp_cat_with_universe}
  {Γ Δ Θ : C}
  (t : comp_cat_tm (comp_cat_U Δ))
  (s₁ : Γ --> Δ) (s₂ : Θ --> Γ)
  (u : comp_cat_tm (comp_cat_el t))
  : (u [[ s₁ ]]tm ↑ ⌈ comp_cat_el_iso s₁ t ⌉) [[ s₂ ]]tm
      ↑ ⌈ comp_cat_el_iso s₂ (comp_cat_pb_term_univ t s₁) ⌉
      ↑ ⌈ comp_cat_el_pb_term_univ_comp t s₁ s₂ ⌉
    = u [[ s₂ · s₁ ]]tm ↑ ⌈ comp_cat_el_iso (s₂ · s₁) t ⌉.
Proof.
  unfold comp_cat_el_pb_term_univ_comp.
  rewrite comp_cat_subst_coerce_tm.
  rewrite !comp_cat_comp_coerce_tm.
  refine (!_).
  etrans.
  { apply maponpaths.
    apply comp_cat_subst_tm_comp. }
  rewrite comp_cat_comp_coerce_tm.
  refine (!_).
  apply comp_cat_coerce_eq.
  etrans.
  {
    rewrite assoc.
    apply maponpaths_2.
    apply (comp_cat_univ_coherent_comp' (C := C)). }
  do 2 rewrite assoc'.
  apply maponpaths.
  refine (_ @ id_right _).
  apply maponpaths.
  etrans.
  { apply maponpaths.
    apply coe_comp_cat_el_z_iso_from_eq. }
  etrans.
  { apply comp_cat_el_map_comp. }
  apply comp_cat_el_map_id.
Qed.

Lemma comp_cat_el_iso_reindex_inv {C : comp_cat_with_universe}
  {Γ Δ Θ : C} (s : Γ --> Δ) {σ σ' : Θ --> Γ}
  (e : σ' = σ) (t : comp_cat_tm (comp_cat_U Δ))
  (p : (t [[ s ]]tm ↑ ⌈comp_cat_univ_sub_iso s⌉) [[ σ ]]tm
         ↑ ⌈comp_cat_univ_sub_iso σ⌉
       = t [[ σ' · s ]]tm ↑ ⌈comp_cat_univ_sub_iso (σ' · s)⌉)
  : ⌈comp_cat_el_iso σ (t [[ s ]]tm ↑ ⌈comp_cat_univ_sub_iso s⌉)⌉
      · comp_cat_el_map p
      · ⌈comp_cat_el_iso (σ' · s) t⌉⁻¹
      · ⌈comp_cat_subst_ty_comp_iso (comp_cat_el t) s σ'⌉⁻¹
      · ⌈comp_cat_subst_ty_iso (comp_cat_el t [[ s ]]) e⌉
    = comp_cat_reindex_coercion σ (⌈comp_cat_el_iso s t⌉⁻¹).
Proof.
  induction e.
  rewrite id_right.
  assert (Hp : p = ! elmaplemmacomp (pr12 C)) by apply comp_cat_tm_isaset.
  rewrite Hp.
  assert (HX :
           ⌈comp_cat_el_iso σ' (t [[ s ]]tm ↑ ⌈comp_cat_univ_sub_iso s⌉)⌉
           = comp_cat_reindex_coercion σ' (⌈comp_cat_el_iso s t⌉⁻¹)
               · (⌈comp_cat_subst_ty_comp_iso (comp_cat_el t) s σ'⌉
                    · ⌈comp_cat_el_iso (σ' · s) t⌉
                    · comp_cat_el_map (elmaplemmacomp (pr12 C)))).
  { refine (! id_left _ @ _).
    etrans.
    { apply maponpaths_2.
      refine (!_).
      exact (pr2 (comp_cat_reindex_coercion_is_inverse
                    σ' (comp_cat_el_iso s t))). }
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    apply comp_cat_univ_coherent_comp'. }
  rewrite HX.
  do 5 rewrite assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  etrans.
  { do 2 apply maponpaths.
    refine (assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (comp_cat_el_map_comp _ _ @ _).
    etrans.
    { apply maponpaths.  apply pathsinv0r. }
    apply (comp_cat_el_map_id _ (idpath _)). }
  rewrite id_left.
  etrans.
  { apply maponpaths.
    rewrite assoc.
    apply maponpaths_2.
    apply z_iso_inv_after_z_iso. }
  rewrite assoc.
  rewrite id_right.
  apply z_iso_inv_after_z_iso.
Qed.

Lemma comp_cat_univ_sub_iso_lemma {C : comp_cat_with_universe}
  {Γ Δ Θ Ω : C}
  (s₁ : Γ --> Δ) (s₂ : Θ --> Γ) (s₃ : Ω --> Θ)
  : ⌈comp_cat_subst_ty_comp_iso (comp_cat_U Δ [[ s₁ ]]) s₂ s₃⌉
      · ⌈comp_cat_subst_ty_comp_iso (comp_cat_U Δ) s₁ (s₃ · s₂)⌉
      · ⌈comp_cat_univ_sub_iso (s₃ · s₂ · s₁)⌉
    = comp_cat_reindex_coercion s₃
        (comp_cat_reindex_coercion s₂ (⌈comp_cat_univ_sub_iso s₁⌉))
        · comp_cat_reindex_coercion s₃ (⌈comp_cat_univ_sub_iso s₂⌉)
        · ⌈comp_cat_univ_sub_iso s₃⌉.
Proof.
  refine (!_).
  etrans.
  { apply maponpaths_2.
    refine (! comp_cat_reindex_coercion_comp_witness _ _ _ @ _).
    apply idpath. }
  etrans.
  { apply maponpaths_2. apply maponpaths.
    etrans; [refine (!_); apply id_left | ].
    apply maponpaths_2.
    refine (!_).
    apply (z_iso_inv_after_z_iso ( comp_cat_subst_ty_comp_iso _ _ _ )). }
  do 2 rewrite assoc'.
  etrans.
  { rewrite assoc.
    apply maponpaths_2.
    apply maponpaths.
    rewrite assoc'.
    apply maponpaths.
    refine (!_).
    rewrite assoc.
    exact (comp_cat_univ_sub_iso_comp (C := C) s₁ s₂). }
  rewrite comp_cat_reindex_coercion_comp_witness.
  rewrite assoc'.
  etrans.
  { apply maponpaths.
    etrans; [refine (!_); apply id_left | ].
    apply maponpaths_2.
    refine (!_).
    apply (z_iso_inv_after_z_iso ( comp_cat_subst_ty_comp_iso _ _ _ )). }
  rewrite assoc'.
  etrans. {
    do 2 apply maponpaths.
    refine (!_).
    rewrite assoc.
    exact (comp_cat_univ_sub_iso_comp (C := C) _ _). }
  etrans.
  { do 2 apply maponpaths.
    refine (!_).
    apply (sub_comp_cat_univ_iso_natural _ (assoc s₃ s₂ s₁)). }
  etrans. {
    do 2 (etrans; [apply assoc|]).
    apply maponpaths_2.
    refine (!_).
    exact (comp_cat_assoc_subst_ty (C:=C) _ _ _ _). }
  rewrite assoc'.
  apply idpath.
Qed.

Lemma comp_cat_univ_sub_iso_lemma' {C : comp_cat_with_universe}
  {Γ Δ Θ Ω : C}
  (s₁ : Γ --> Δ) (s₂ : Θ --> Γ) (s₃ : Ω --> Θ)
  : ⌈comp_cat_subst_ty_comp_iso (comp_cat_U Δ) s₁ (s₃ · s₂)⌉⁻¹
      · (⌈comp_cat_subst_ty_comp_iso (comp_cat_U Δ [[ s₁ ]]) s₂ s₃⌉⁻¹
           · (comp_cat_reindex_coercion s₃
                (comp_cat_reindex_coercion s₂ (⌈comp_cat_univ_sub_iso s₁⌉))
                · (comp_cat_reindex_coercion s₃ (⌈comp_cat_univ_sub_iso s₂⌉)
                     · ⌈comp_cat_univ_sub_iso s₃⌉)))
    = ⌈comp_cat_univ_sub_iso (s₃ · s₂ · s₁)⌉.
Proof.
  do 2 apply z_iso_inv_on_right.
  do 2 rewrite assoc.
  refine (!_).
  exact (comp_cat_univ_sub_iso_lemma s₁ s₂ s₃).
Qed.

Lemma comp_cat_univ_sub_iso_lemma'' {C : comp_cat_with_universe}
  {Γ Δ Θ Ω : C}
  {s₁ s₁' : Γ --> Δ} (p : s₁ = s₁')
  (s₂ : Θ --> Γ) (s₃ : Ω --> Θ)
  : ⌈comp_cat_subst_ty_comp_iso (comp_cat_U Δ) s₁ (s₃ · s₂)⌉⁻¹
      · (⌈comp_cat_subst_ty_comp_iso (comp_cat_U Δ [[ s₁ ]]) s₂ s₃⌉⁻¹
           · (comp_cat_reindex_coercion s₃
                (comp_cat_reindex_coercion s₂
                   (⌈comp_cat_subst_ty_iso (comp_cat_U Δ) p⌉))
                · (comp_cat_reindex_coercion s₃
                     (comp_cat_reindex_coercion s₂ (⌈comp_cat_univ_sub_iso s₁'⌉))
                     · (comp_cat_reindex_coercion s₃ (⌈comp_cat_univ_sub_iso s₂⌉)
                          · ⌈comp_cat_univ_sub_iso s₃⌉))))
    = ⌈comp_cat_univ_sub_iso (s₃ · s₂ · s₁)⌉.
Proof.
  induction p.
  etrans.  {
    apply maponpaths.
    rewrite assoc.
    apply maponpaths_2.
    do 2 apply maponpaths.
    apply comp_cat_reindex_coercion_id. }
  rewrite comp_cat_reindex_coercion_id.
  rewrite id_right.
  apply comp_cat_univ_sub_iso_lemma'.
Qed.

Lemma comp_cat_el_map_move {C : comp_cat_with_universe}
  {Γ : C} {x y : comp_cat_tm (comp_cat_U Γ)}
  (p : x = y) (q : y = x)
  (t : comp_cat_tm (comp_cat_el x)) (t' : comp_cat_tm (comp_cat_el y))
  (h : t ↑ comp_cat_el_map p = t')
  : t = t' ↑ comp_cat_el_map q.
Proof.
  induction p.
  assert (Hq : q = idpath _) by apply comp_cat_tm_isaset.
  rewrite Hq.
  refine (! comp_cat_id_coerce_tm t @ h @ ! comp_cat_id_coerce_tm t').
Qed.

Lemma comp_cat_el_map_merge {C : comp_cat_with_universe}
  {Γ : C} {x y z : comp_cat_tm (comp_cat_U Γ)}
  (p : x = y) (p' : y = z) (q : x = z)
  (t : comp_cat_tm (comp_cat_el x))
  : t ↑ comp_cat_el_map p ↑ comp_cat_el_map p' = t ↑ comp_cat_el_map q.
Proof.
  refine (comp_cat_comp_coerce_tm _ _ _ @ _).
  apply comp_cat_coerce_eq.
  refine (comp_cat_el_map_comp _ _ @ _).
  apply maponpaths.
  apply comp_cat_tm_isaset.
Qed.

(* substituting a term along equal morphisms *)
Lemma comp_cat_el_subst_tm_eq {C : comp_cat_with_universe}
  {Γ Δ : C} {σ σ' : Γ --> Δ} (P : σ = σ')
  (t : comp_cat_tm (comp_cat_U Δ)) (u : comp_cat_tm (comp_cat_el t))
  (q : comp_cat_pb_term_univ t σ = comp_cat_pb_term_univ t σ')
  : u [[σ ]]tm ↑ ⌈ comp_cat_el_iso σ t ⌉ ↑ comp_cat_el_map q
    = u [[σ' ]]tm ↑ ⌈ comp_cat_el_iso σ' t ⌉.
Proof.
  induction P.
  assert (Hq : q = idpath _) by apply comp_cat_tm_isaset.
  rewrite Hq.
  apply comp_cat_id_coerce_tm.
Qed.

(* collapsing two substitutions of a term *)
Lemma comp_cat_el_pb_tm_collapse {C : comp_cat_with_universe}
  {Γ Δ Θ : C} (t : comp_cat_tm (comp_cat_U Δ))
  (s₁ : Γ --> Δ) (s₂ : Θ --> Γ) (u : comp_cat_tm (comp_cat_el t))
  (q : comp_cat_pb_term_univ t (s₂ · s₁)
       = comp_cat_pb_term_univ (comp_cat_pb_term_univ t s₁) s₂)
  : (u [[s₁ ]]tm ↑ ⌈ comp_cat_el_iso s₁ t ⌉) [[s₂ ]]tm
      ↑ ⌈ comp_cat_el_iso s₂ (comp_cat_pb_term_univ t s₁) ⌉
    = u [[s₂ · s₁ ]]tm ↑ ⌈ comp_cat_el_iso (s₂ · s₁) t ⌉ ↑ comp_cat_el_map q.
Proof.
  refine (comp_cat_el_map_move (comp_cat_pb_term_univ_comp t s₁ s₂) q _ _ _).
  refine (_ @ comp_cat_el_pb_tm_comp t s₁ s₂ u).
  apply comp_cat_coerce_eq.
  refine (!_).
  apply (coe_comp_cat_el_z_iso_from_eq (C':=C)).
Qed.

(* a coercion of the code may be pushed through a substitution *)
Lemma comp_cat_el_pb_tm_coerce {C : comp_cat_with_universe}
  {Γ Δ : C} (σ : Δ --> Γ)
  {x y : comp_cat_tm (comp_cat_U Γ)} (p : x = y)
  (u : comp_cat_tm (comp_cat_el x))
  (q : comp_cat_pb_term_univ x σ = comp_cat_pb_term_univ y σ)
  : (u ↑ comp_cat_el_map p) [[σ ]]tm ↑ ⌈ comp_cat_el_iso σ y ⌉
    = u [[σ ]]tm ↑ ⌈ comp_cat_el_iso σ x ⌉ ↑ comp_cat_el_map q.
Proof.
  induction p.
  assert (Hq : q = idpath _) by apply comp_cat_tm_isaset.
  rewrite Hq.
  refine (_ @ ! comp_cat_id_coerce_tm _).
  apply (maponpaths (λ z, z [[σ ]]tm ↑ ⌈ comp_cat_el_iso σ x ⌉)).
  apply comp_cat_id_coerce_tm.
Qed.

Definition comp_cat_pb_term_univ_comp3 {C : comp_cat_with_universe}
  {Γ1 Γ2 Γ3 Γ4 : C} (t : comp_cat_tm (comp_cat_U Γ1))
  (f : Γ2 --> Γ1) (g : Γ3 --> Γ2) (h : Γ4 --> Γ3)
  : comp_cat_pb_term_univ t (h · (g · f))
    = comp_cat_pb_term_univ
        (comp_cat_pb_term_univ (comp_cat_pb_term_univ t f) g) h
  := ! comp_cat_pb_term_univ_comp t (g · f) h
       @ maponpaths (λ z, comp_cat_pb_term_univ z h)
           (! comp_cat_pb_term_univ_comp t f g).

(* collapsing three substitutions of a term *)
Lemma comp_cat_el_pb_tm_comp3 {C : comp_cat_with_universe}
  {Γ1 Γ2 Γ3 Γ4 : C} (t : comp_cat_tm (comp_cat_U Γ1))
  (f : Γ2 --> Γ1) (g : Γ3 --> Γ2) (h : Γ4 --> Γ3)
  (u : comp_cat_tm (comp_cat_el t))
  : ((u [[f ]]tm ↑ ⌈ comp_cat_el_iso f t ⌉) [[g ]]tm
       ↑ ⌈ comp_cat_el_iso g (comp_cat_pb_term_univ t f) ⌉) [[h ]]tm
      ↑ ⌈ comp_cat_el_iso h
            (comp_cat_pb_term_univ (comp_cat_pb_term_univ t f) g) ⌉
    = u [[h · (g · f) ]]tm ↑ ⌈ comp_cat_el_iso (h · (g · f)) t ⌉
        ↑ comp_cat_el_map (comp_cat_pb_term_univ_comp3 t f g h).
Proof.
  etrans.
  { exact (maponpaths
             (λ z : comp_cat_tm
                      (comp_cat_el
                         (comp_cat_pb_term_univ
                            (comp_cat_pb_term_univ t f) g)),
                z [[h ]]tm
                  ↑ ⌈ comp_cat_el_iso h
                        (comp_cat_pb_term_univ
                           (comp_cat_pb_term_univ t f) g) ⌉)
             (comp_cat_el_pb_tm_collapse t f g u
                (! comp_cat_pb_term_univ_comp t f g))). }
  etrans.
  { apply (comp_cat_el_pb_tm_coerce h (! comp_cat_pb_term_univ_comp t f g)
             _ (maponpaths (λ z, comp_cat_pb_term_univ z h)
                  (! comp_cat_pb_term_univ_comp t f g))). }
  etrans.
  { exact (maponpaths
             (λ z : comp_cat_tm
                      (comp_cat_el (comp_cat_pb_term_univ
                                      (comp_cat_pb_term_univ t (g · f)) h)),
                z ↑ comp_cat_el_map
                      (maponpaths (λ w, comp_cat_pb_term_univ w h)
                         (! comp_cat_pb_term_univ_comp t f g)))
             (comp_cat_el_pb_tm_collapse t (g · f) h u
                (! comp_cat_pb_term_univ_comp t (g · f) h))). }
  apply comp_cat_el_map_merge.
Qed.

(* a term is unchanged by coercing along a path and back *)
Lemma comp_cat_coerce_el_map_inv {C : comp_cat_with_universe}
  {Γ : C} {a b : comp_cat_tm (comp_cat_U Γ)}
  (p : a = b) (t : comp_cat_tm (comp_cat_el a))
  : t = t ↑ comp_cat_el_map p ↑ comp_cat_el_map (! p).
Proof.
  induction p.
  refine (!_).
  refine (comp_cat_id_coerce_tm _ @ _).
  apply comp_cat_id_coerce_tm.
Qed.

Section Universe_Lift.

  Context (C : comp_cat_with_universe).

  Definition comp_cat_univ_lift {Γ Δ : C} (s : Γ --> Δ) (A : comp_cat_tm (comp_cat_U Δ))
    : Γ & comp_cat_el (A [[s]]tm ↑ ⌈comp_cat_univ_sub_iso s⌉) --> Δ & comp_cat_el A
    := comp_cat_comp_mor (⌈comp_cat_el_iso s A⌉⁻¹)
         · comp_cat_ext_subst s (comp_cat_el A).

End Universe_Lift.

Lemma comp_cat_univ_lift_el_map_natural
  {C : comp_cat_with_universe}
  {Γ Δ : C} (i : Γ --> Δ)
  {t t' : comp_cat_tm (comp_cat_U Δ)} (p : t = t')
  (q : t [[i]]tm ↑ ⌈comp_cat_univ_sub_iso i⌉
       = t' [[i]]tm ↑ ⌈comp_cat_univ_sub_iso i⌉)
  : comp_cat_comp_mor (comp_cat_el_map q) · comp_cat_univ_lift C i t'
    = comp_cat_univ_lift C i t · comp_cat_comp_mor (comp_cat_el_map p).
Proof.
  induction p.
  assert (Hq : q = idpath _) by apply comp_cat_tm_isaset.
  rewrite Hq.
  rewrite !(comp_cat_el_map_id _ (idpath _)).
  etrans.
  { apply maponpaths_2. apply comp_cat_comp_mor_id. }
  etrans.
  2 : { apply maponpaths. refine (!_). apply comp_cat_comp_mor_id. }
  rewrite id_left.
  rewrite id_right.
  apply idpath.
Qed.

Lemma comp_cat_univ_lift_is_z_iso {C : comp_cat_with_universe}
  {Γ Δ : C} (i : z_iso Γ Δ) (t : comp_cat_tm (comp_cat_U Δ))
  : is_z_isomorphism (comp_cat_univ_lift C i t).
Proof.
  unfold comp_cat_univ_lift.
  use is_z_isomorphism_comp.
  - exact (pr2 (comp_cat_comp_iso (z_iso_inv (comp_cat_el_iso i t)))).
  - exact (pr2 (comp_cat_ext_subst_z_iso i (comp_cat_el t))).
Qed.

Definition comp_cat_univ_lift_z_iso {C : comp_cat_with_universe}
  {Γ Δ : C} (i : z_iso Γ Δ) (t : comp_cat_tm (comp_cat_U Δ))
  : z_iso (Γ & comp_cat_el (t [[i]]tm ↑ ⌈comp_cat_univ_sub_iso i⌉)) (Δ & comp_cat_el t)
  := comp_cat_univ_lift C i t ,, comp_cat_univ_lift_is_z_iso i t.

Lemma comp_cat_univ_lift_comp {C : comp_cat_with_universe}
  {Γ Δ Θ : C} (f : Δ --> Θ) (g : Γ --> Δ)
  (t : comp_cat_tm (comp_cat_U Θ))
  : (comp_cat_univ_lift C (g · f) t
     = comp_cat_comp_mor (comp_cat_el_map (elmaplemmacomp (pr12 C)) )
         · comp_cat_univ_lift C g (t [[ f ]]tm ↑ ⌈comp_cat_univ_sub_iso f⌉)
         · comp_cat_univ_lift C f t).
Proof.
  unfold comp_cat_univ_lift.
  rewrite comp_cat_ext_subst_comp.
  do 4 rewrite assoc.
  apply maponpaths_2.
  etrans.
  2 : { do 2 rewrite assoc'.
        do 2 apply maponpaths.
        refine (!_).
        apply (! comp_cat_ext_subst_coercion g (⌈comp_cat_el_iso f t⌉⁻¹)). }
  do 2 rewrite assoc.
  apply maponpaths_2.
  rewrite <- !comp_cat_comp_mor_comp'.
  apply maponpaths.
  use z_iso_inv_on_right.
  rewrite <- comp_cat_univ_coherent_comp''.
  do 4 rewrite assoc'.
  etrans.
  2: { do 3 apply maponpaths.
       rewrite assoc.
       apply maponpaths_2.
       refine (!_).
       etrans. { apply comp_cat_el_map_comp. }
       etrans. { apply maponpaths. apply pathsinv0l. }
       apply (comp_cat_el_map_id _ (idpath _)). }
  rewrite id_left.
  etrans.
  2: { do 2 apply maponpaths.
       rewrite assoc.
       apply maponpaths_2.
       refine (!_).
       apply z_iso_inv_after_z_iso. }
  rewrite id_left.
  etrans. { refine (!_). apply id_right. }
  apply maponpaths.
  rewrite comp_cat_reindex_coercion_iso_inv_eq.
  refine (!_).
  apply z_iso_inv_after_z_iso.
Qed.

Lemma comp_cat_univ_lift_comp' {C : comp_cat_with_universe}
  {Γ Δ Θ : C} (f : z_iso Δ Θ) (g : z_iso Γ Δ)
  (t : comp_cat_tm (comp_cat_U Θ))
  : comp_cat_univ_lift_z_iso (z_iso_comp g f) t
    = z_iso_comp
        (z_iso_comp (comp_cat_comp_iso (comp_cat_el_z_iso_from_eq (elmaplemmacomp (pr12 C)) ))
           (comp_cat_univ_lift_z_iso g (t [[ f ]]tm ↑ ⌈comp_cat_univ_sub_iso f⌉)))
        (comp_cat_univ_lift_z_iso f t).
Proof.
  use z_iso_eq.
  refine ( _ @ idpath ((_ · _) · _)).
  refine (comp_cat_univ_lift_comp f g t @ _).
  do 2 apply maponpaths_2.
  cbn.
  apply maponpaths.
  refine (! coe_comp_cat_el_z_iso_from_eq _).
Qed.

Lemma comp_cat_univ_lift_eq {C : comp_cat_with_universe}
  {Γ Δ : C} (s s': C ⟦ Γ, Δ ⟧) (A : comp_cat_tm (comp_cat_U Δ)) (p : s = s')
  : comp_cat_univ_lift _ s A = comp_cat_comp_mor (comp_cat_el_map ((comp_cat_subst_coerce_tm_eq p (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉) (sub_comp_cat_univ_iso_natural _ p) _)))
                                 · comp_cat_univ_lift _ s' A.
Proof.
  induction p.
  assert (H : (comp_cat_subst_coerce_tm_eq (idpath s) (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉) (sub_comp_cat_univ_iso_natural _ (idpath s)) A) = idpath _)
    by apply comp_cat_tm_isaset.
  rewrite H.
  refine (! id_left _ @ _).
  apply maponpaths_2.
  refine (! comp_cat_comp_mor_id).
Qed.

Lemma comp_cat_univ_lift_id {C : comp_cat_with_universe} {Γ : C} (t : comp_cat_tm (comp_cat_U Γ))
  : comp_cat_univ_lift C (identity Γ) t
    = comp_cat_comp_mor (comp_cat_el_map (elmaplemma (pr12 C))).
Proof.
  unfold comp_cat_univ_lift.
  rewrite comp_cat_ext_subst_id.
  rewrite <- comp_cat_comp_mor_comp'.
  apply maponpaths.
  etrans.
  { refine (!_). apply id_right. }
  etrans.
  { apply maponpaths.
    apply comp_cat_univ_coherent_id. }
  rewrite assoc.
  etrans.
  { apply maponpaths_2.
    rewrite assoc.
    apply maponpaths_2.
    rewrite assoc'.
    apply maponpaths.
    apply z_iso_after_z_iso_inv. }
  rewrite id_right.
  etrans.
  { apply maponpaths_2.
    apply z_iso_after_z_iso_inv. }
  rewrite id_left.
  apply idpath.
Qed.

Lemma comp_cat_univ_lift_inv {C : comp_cat_with_universe}
  {Γ Δ : C} (i : z_iso Γ Δ) (t : comp_cat_tm (comp_cat_U Γ))
  : comp_cat_univ_lift C (inv_from_z_iso i) t =
      inv_from_z_iso (comp_cat_univ_lift_z_iso i (t [[inv_from_z_iso i]]tm ↑ ⌈comp_cat_univ_sub_iso (inv_from_z_iso i)⌉))
        · comp_cat_comp_mor (comp_cat_el_map (!comp_cat_tm_subst_coerce_inv' _ _)).
Proof.
  refine (!_).
  use z_iso_inv_on_right.
  use (cancel_z_iso'
         (comp_cat_comp_iso
            (comp_cat_el_z_iso_from_eq (elmaplemmacomp (pr12 C))))).
  etrans.
  2: { apply maponpaths_2.
       refine (! (comp_cat_el_z_iso_from_eq_pr1_comp_mor (C:=C)) _). }
  etrans.
  2: { rewrite assoc.
       exact (comp_cat_univ_lift_comp (inv_from_z_iso i) i t). }
  etrans.
  2: { refine (!_).
       refine (comp_cat_univ_lift_eq _ _ t (z_iso_inv_after_z_iso i) @ _).
       exact (maponpaths
                (λ z, comp_cat_comp_mor
                        (comp_cat_el_map
                           ((comp_cat_subst_coerce_tm_eq (z_iso_inv_after_z_iso i) (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉) (sub_comp_cat_univ_iso_natural _ (z_iso_inv_after_z_iso i)) t)))
                        · z)
                (comp_cat_univ_lift_id t)). }
  etrans.
  2: { refine (_ @ comp_cat_comp_mor_comp' _ _).
       apply maponpaths.
       refine (! comp_cat_el_map_comp _ _). }
  etrans.
  { apply maponpaths_2.
    apply (comp_cat_el_z_iso_from_eq_pr1_comp_mor (C:=C)). }
  etrans.
  { refine (! comp_cat_comp_mor_comp' _ _ @ _).
    apply maponpaths.
    apply comp_cat_el_map_comp. }
  apply maponpaths.
  apply maponpaths.
  apply comp_cat_tm_isaset.
Qed.

Lemma comp_cat_univ_lift_inv' {C : comp_cat_with_universe}
  {Γ Δ : C} (i : z_iso Γ Δ) (t : comp_cat_tm (comp_cat_U Γ))
  : comp_cat_univ_lift_z_iso (z_iso_inv i) t =
      z_iso_comp (z_iso_inv (comp_cat_univ_lift_z_iso i (t [[inv_from_z_iso i]]tm ↑ ⌈comp_cat_univ_sub_iso (inv_from_z_iso i)⌉)))
        (comp_cat_comp_iso (comp_cat_el_z_iso_from_eq (!comp_cat_tm_subst_coerce_inv' _ _))).
Proof.
  use z_iso_eq.
  refine (_ @ idpath (_ · _)).
  refine (comp_cat_univ_lift_inv i t @ _).
  apply maponpaths.
  refine (! (comp_cat_el_z_iso_from_eq_pr1_comp_mor (C:=C)) _).
Qed.

Lemma comp_cat_univ_lift_tm_eq {C : comp_cat_with_universe}
  {Γ Δ : C} (s : C ⟦ Γ, Δ ⟧) (A A': comp_cat_tm (comp_cat_U Δ))
  (p : A = A') :
  comp_cat_univ_lift _ s A =
    comp_cat_comp_mor (comp_cat_el_map (maponpaths _ (maponpaths _ p)))
      · comp_cat_univ_lift _ s A'
      · (comp_cat_comp_mor (comp_cat_el_map (!p))).
Proof.
  induction p.
  refine (!_).
  etrans.
  { apply maponpaths_2.
    apply maponpaths_2.
    apply comp_cat_comp_mor_id. }
  etrans.
  { apply maponpaths.
    apply comp_cat_comp_mor_id. }
  rewrite id_left.
  apply id_right.
Qed.

Lemma comp_cat_univ_lift_z_iso_inv {C : comp_cat_with_universe}
  {Γ Δ : C} (i : z_iso Γ Δ) (t : comp_cat_tm (comp_cat_U Δ))
  : inv_from_z_iso (comp_cat_univ_lift_z_iso i t)
    = z_iso_inv_from_z_iso (comp_cat_ext_subst_z_iso i (comp_cat_el t))
        · comp_cat_comp_mor (⌈comp_cat_el_iso i t⌉).
Proof.
  (* the right hand side is an inverse of the lift, and inverses are unique *)
  assert (H : comp_cat_univ_lift C i t
                · (inv_from_z_iso (comp_cat_ext_subst_z_iso i (comp_cat_el t))
                     · comp_cat_comp_mor (⌈comp_cat_el_iso i t⌉))
              = identity _).
  { unfold comp_cat_univ_lift.
    rewrite assoc.
    etrans.
    { apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply (z_iso_inv_after_z_iso
               (comp_cat_ext_subst_z_iso i (comp_cat_el t))). }
    rewrite id_right.
    apply comp_cat_comp_mor_z_iso_after_z_iso_inv. }
  refine (! id_right _ @ _).
  etrans.
  { apply maponpaths.
    exact (! H). }
  rewrite assoc.
  etrans.
  { apply maponpaths_2.
    apply (z_iso_after_z_iso_inv (comp_cat_univ_lift_z_iso i t)). }
  apply id_left.
Qed.

Lemma comp_cat_univ_lift_z_iso_comp {C : comp_cat_with_universe}
  {Γ Δ Θ : C} (f : z_iso Δ Θ) (g : z_iso Γ Δ)
  (t : comp_cat_tm (comp_cat_U Θ))
  : z_iso_comp
      (comp_cat_univ_lift_z_iso g (t [[f]]tm ↑ ⌈comp_cat_univ_sub_iso f⌉))
      (comp_cat_univ_lift_z_iso f t)
    = z_iso_comp
        (comp_cat_comp_iso (comp_cat_el_z_iso_from_eq (! elmaplemmacomp (pr12 C))))
        (comp_cat_univ_lift_z_iso (z_iso_comp g f) t).
Proof.
  use z_iso_eq.
  refine (idpath (_ · _) @ _ @ idpath (_ · _)).
  refine (!_).
  etrans.
  { apply maponpaths.
    apply (comp_cat_univ_lift_comp f g t). }
  do 2 rewrite assoc.
  etrans.
  { do 2 apply maponpaths_2.
    etrans.
    { apply maponpaths_2.
      apply (comp_cat_el_z_iso_from_eq_pr1_comp_mor (C:=C)). }
    refine (! comp_cat_comp_mor_comp' _ _ @ _).
    etrans.
    { apply maponpaths.
      apply comp_cat_el_map_comp. }
    etrans.
    { do 2 apply maponpaths.
      apply pathsinv0l. }
    apply comp_cat_comp_mor_id. }
  rewrite id_left.
  apply idpath.
Qed.

(**  * 5. Universe Being Closed under Σ-Types  *)

Section Universe_Sigma_Closure.

  Context (C : comp_cat_with_universe).
  Context (Σ : comp_cat_sigma C).

  (* 1. Sigma code in the universe *)
  (* Γ ⊢ A : U , Γ.el(A) ⊢ B : U  => Γ ⊢ Σ(A,B) : U *)
  Definition univ_sigma_form : UU :=
    ∏ (Γ : C)
      (A : comp_cat_tm (comp_cat_U Γ))
      (B : comp_cat_tm (comp_cat_U (Γ & comp_cat_el A))),
      comp_cat_tm (comp_cat_U Γ).

  (* 2. el commutes with sigma  *)
  (* el(Σ(A,B)) ≃ Σ_el(A) el(B) *)
  Definition univ_sigma_el_iso (ΣU : univ_sigma_form) : UU :=
    ∏ (Γ : C)
      (A : comp_cat_tm (comp_cat_U _))
      (B : comp_cat_tm (comp_cat_U _)),
      @z_iso (fiber_category _ _) (comp_cat_el (ΣU Γ A B))
        ((pr1 Σ) Γ (comp_cat_el A) (comp_cat_el B)).

  (* 3. Σ-codes commute with substitution  *)
  (* Σ(A,B)[s] = Σ(A[s],B[s.el(A)])  *)
  (* modulo some coercions *)
  Definition univ_sigma_subst_law (ΣU : univ_sigma_form) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ)
      (A : comp_cat_tm (comp_cat_U _))
      (B : comp_cat_tm (comp_cat_U _)),
      let e := ⌈sub_comp_cat_univ_iso _ s⌉ in
      let As := (A [[ s ]]tm) ↑ e in
      let el_iso := comp_cat_el_iso s A in
      let sA := comp_cat_ext_subst s (comp_cat_el A) in
      let e' := ⌈sub_comp_cat_univ_iso _ (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉ in
      let BsA := B [[ comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA ]]tm ↑ e' in
      (ΣU Δ A B) [[ s ]]tm ↑ e = ΣU Γ As BsA.

  (** 4. coherence for Σ-codes *)
  Definition univ_sigma_coherent
    (ΣU : univ_sigma_form)
    (Σeli : univ_sigma_el_iso ΣU)
    (Σlaw : univ_sigma_subst_law ΣU)
    : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ)
    (A : comp_cat_tm (comp_cat_U Δ))
    (B : comp_cat_tm (comp_cat_U (Δ & comp_cat_el A))),
    let As := (A [[ s ]]tm) ↑ ⌈sub_comp_cat_univ_iso _ s⌉ in
    let el_iso := comp_cat_el_iso s A in
    let sA := comp_cat_ext_subst s (comp_cat_el A) in
    let BsA := B [[ comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA ]]tm ↑ (⌈sub_comp_cat_univ_iso _ (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉) in
    comp_cat_comp_mor (⌈Σeli Γ As BsA⌉)
         · comp_cat_sigma_pair_proj_iso (comp_cat_el As) (comp_cat_el BsA)
         · comp_cat_univ_lift C (comp_cat_univ_lift C s A) B
         · inv_from_z_iso
             (comp_cat_sigma_pair_proj_iso (comp_cat_el A) (comp_cat_el B))
         · comp_cat_comp_mor (⌈Σeli Δ A B⌉⁻¹)
             = comp_cat_comp_mor (comp_cat_el_map (! Σlaw Γ Δ s A B))
           · comp_cat_univ_lift C s (ΣU Δ A B).

  Definition comp_cat_universe_closed_sigma : UU :=
    ∑ (ΣU : univ_sigma_form),
      ∑ (eliso : univ_sigma_el_iso ΣU),
      ∑ (law : univ_sigma_subst_law ΣU),
      (univ_sigma_coherent ΣU eliso law).

  Coercion comp_cat_with_sigma_to_comp_cat (SigmaU : comp_cat_universe_closed_sigma)
    : univ_sigma_form := pr1 SigmaU.

  (** accessors for sigma codes  *)

  Definition comp_cat_sigma_code (SigmaU : comp_cat_universe_closed_sigma)
    {Γ : C} (A : comp_cat_tm (comp_cat_U _))
    (B : comp_cat_tm (comp_cat_U _)) :
    comp_cat_tm (comp_cat_U _)
    := (pr1 SigmaU) Γ A B.

  Definition comp_cat_sigma_el_iso
    (SigmaU : comp_cat_universe_closed_sigma)
    {Γ : C} (A : comp_cat_tm (comp_cat_U _))
    (B : comp_cat_tm (comp_cat_U _)):
    @z_iso (fiber_category _ _) (comp_cat_el (comp_cat_sigma_code SigmaU A B))
      ((pr1 Σ) Γ (comp_cat_el A)
         (comp_cat_el B))
    := (pr12 SigmaU) Γ A B.

   Definition comp_cat_univ_sigma_subst (SigmaU : comp_cat_universe_closed_sigma)
    {Γ Δ : C} (s : Γ --> Δ)
    (A : comp_cat_tm (comp_cat_U _))
    (B : comp_cat_tm (comp_cat_U _)) :
    let e := ⌈sub_comp_cat_univ_iso _ s⌉ in
    let As := (A [[ s ]]tm) ↑ e in
    let el_iso := comp_cat_el_iso s A in
    let sA := comp_cat_ext_subst s (comp_cat_el A) in
    let e' := ⌈sub_comp_cat_univ_iso _ (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉ in
    let BsA := B [[ comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA ]]tm ↑ e' in
    let ΣU := (@comp_cat_sigma_code SigmaU) in
    (ΣU Δ A B) [[ s ]]tm ↑ e = (ΣU Γ As BsA)
    := (pr122 SigmaU) _ _ s A B.

  Definition comp_cat_univ_sigma_coherent (SigmaU : comp_cat_universe_closed_sigma)
    {Γ Δ : C} (s : Γ --> Δ)
    (A : comp_cat_tm (comp_cat_U Δ))
    (B : comp_cat_tm (comp_cat_U (Δ & comp_cat_el A))) :
    let As := (A [[ s ]]tm) ↑ ⌈sub_comp_cat_univ_iso _ s⌉ in
    let el_iso := comp_cat_el_iso s A in
    let sA := comp_cat_ext_subst s (comp_cat_el A) in
    let BsA := B [[ comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA ]]tm ↑ (⌈sub_comp_cat_univ_iso _ (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉) in
    let ΣU := (@comp_cat_sigma_code SigmaU) in
    let Σeli := @comp_cat_sigma_el_iso SigmaU in
    let Σlaw := comp_cat_univ_sigma_subst SigmaU in
    comp_cat_comp_mor (⌈Σeli Γ As BsA⌉)
         · comp_cat_sigma_pair_proj_iso (comp_cat_el As) (comp_cat_el BsA)
         · comp_cat_univ_lift C (comp_cat_univ_lift C s A) B
         · inv_from_z_iso
             (comp_cat_sigma_pair_proj_iso (comp_cat_el A) (comp_cat_el B))
         · comp_cat_comp_mor (⌈Σeli Δ A B⌉⁻¹)
             = comp_cat_comp_mor (comp_cat_el_map (! Σlaw s A B))
           · comp_cat_univ_lift C s (ΣU Δ A B)
    := (pr222 SigmaU) _ _ s A B.

End Universe_Sigma_Closure.

(** Lemmas about universes closed under Σ-types *)

Section Universe_Sigma_Closure_Lemmas.

  Context (C : comp_cat_with_universe)
    (Sigma : comp_cat_sigma C)
    (SigmaU : comp_cat_universe_closed_sigma C Sigma).

  Definition comp_cat_sigma_unpack
    {Γ : C} (A : comp_cat_tm (comp_cat_U Γ))
    (B : comp_cat_tm (comp_cat_U (Γ & comp_cat_el A)))
  : z_iso (Γ & comp_cat_el (comp_cat_sigma_code C Sigma SigmaU A B))
    ((Γ & comp_cat_el A) & comp_cat_el B)
  := z_iso_comp
     (comp_cat_comp_iso (comp_cat_sigma_el_iso C Sigma SigmaU A B))
     (comp_cat_sigma_pair_proj_iso (comp_cat_el A) (comp_cat_el B)).

  Lemma comp_cat_sigma_unpack_mor
    {Γ : C} (A : comp_cat_tm (comp_cat_U Γ))
    (B : comp_cat_tm (comp_cat_U (Γ & comp_cat_el A)))
    : pr1 (comp_cat_sigma_unpack A B)
      = comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU A B ⌉)
          · comp_cat_sigma_proj (comp_cat_el A) (comp_cat_el B).
  Proof.
    apply idpath.
  Qed.

  Lemma comp_cat_sigma_unpack_inv_mor
    {Γ : C} (A : comp_cat_tm (comp_cat_U Γ))
    (B : comp_cat_tm (comp_cat_U (Γ & comp_cat_el A)))
    : inv_from_z_iso (comp_cat_sigma_unpack A B)
      = comp_cat_sigma_pair (comp_cat_el A) (comp_cat_el B)
          · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU A B ⌉⁻¹).
  Proof.
    apply idpath.
  Qed.

  Lemma comp_cat_sigma_unpack_eq
    {Γ : C} (A : comp_cat_tm (comp_cat_U Γ))
    {B B' : comp_cat_tm (comp_cat_U (Γ & comp_cat_el A))}
    (p : B = B')
    : comp_cat_sigma_unpack A B
      =
        z_iso_comp(
            z_iso_comp (comp_cat_comp_iso
                          (comp_cat_el_z_iso_from_eq
                             (maponpaths (comp_cat_sigma_code C Sigma SigmaU A) p)))
              (comp_cat_sigma_unpack A B'))
          (comp_cat_comp_iso (comp_cat_el_z_iso_from_eq (!p))).
  Proof.
    induction p.
    rewrite (comp_cat_el_z_iso_from_eq_id' _
               (maponpaths (comp_cat_sigma_code C Sigma SigmaU A) (idpath B))).
    rewrite (comp_cat_el_z_iso_from_eq_id' _ (! idpath B)).
    rewrite !comp_cat_comp_iso_id.
    rewrite z_iso_id_left.
    refine (! z_iso_id_right _).
  Qed.

  Lemma comp_cat_sigma_code_eq
    {Γ : C}
    (A : comp_cat_tm (comp_cat_U Γ)) (B B' : comp_cat_tm (comp_cat_U (Γ & comp_cat_el A)))
    (p : B = B')
    : comp_cat_sigma_code _ _ SigmaU A B =  comp_cat_sigma_code _ _ SigmaU A B'.
  Proof.
    apply maponpaths.
    apply p.
  Qed.

  Definition comp_cat_univ_sigma_coherent'
    {Γ Δ : C} {s : C ⟦ Γ, Δ ⟧} (A : comp_cat_tm (comp_cat_U Δ))
    (B : comp_cat_tm (comp_cat_U (Δ & comp_cat_el A)))
    (As := A [[s ]]tm ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) s ⌉)
    (el_iso := comp_cat_el_iso s A)
    (sA := comp_cat_ext_subst s (comp_cat_el A))
    (BsA :=
       B [[comp_cat_comp_mor (⌈ el_iso ⌉⁻¹) · sA ]]tm
         ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) (comp_cat_comp_mor (⌈ el_iso ⌉⁻¹) · sA) ⌉)
    (ΣU := comp_cat_sigma_code _ _ SigmaU)
    (Σeli := @comp_cat_sigma_el_iso _ _ SigmaU)
    (Σlaw := comp_cat_univ_sigma_subst _ _ SigmaU)
    : comp_cat_univ_lift C (comp_cat_univ_lift C s A) B
      =
        inv_from_z_iso (comp_cat_sigma_pair_proj_iso (comp_cat_el As) (comp_cat_el BsA))
          · comp_cat_comp_mor (⌈ Σeli Γ As BsA ⌉⁻¹)
          · comp_cat_comp_mor (comp_cat_el_map (! Σlaw s A B))
          · comp_cat_univ_lift C s (ΣU _ B)
          · comp_cat_comp_mor (⌈ Σeli Δ A B ⌉)
          · (comp_cat_sigma_pair_proj_iso (comp_cat_el A) (comp_cat_el B)).
  Proof.
    (* the coherence of Σ-codes, with the isos moved to the other side *)
    refine (!_).
    etrans.
    { do 4 rewrite assoc'.
      do 2 apply maponpaths.
      do 2 rewrite assoc.
      do 2 apply maponpaths_2.
      refine (! comp_cat_univ_sigma_coherent C Sigma SigmaU s A B). }
    do 5 rewrite assoc'.
    etrans.
    { do 6 apply maponpaths.
      rewrite assoc.
      etrans.
      { apply maponpaths_2.
        apply comp_cat_comp_mor_z_iso_after_z_iso_inv. }
      apply id_left. }
    etrans.
    { do 5 apply maponpaths.
      apply (z_iso_after_z_iso_inv
               (comp_cat_sigma_pair_proj_iso (comp_cat_el A) (comp_cat_el B))). }
    etrans.
    { do 4 apply maponpaths.
      apply id_right. }
    etrans.
    { apply maponpaths.
      rewrite assoc.
      etrans.
      { apply maponpaths_2.
        apply comp_cat_comp_mor_z_iso_after_z_iso_inv. }
      apply id_left. }
    rewrite assoc.
    etrans.
    { apply maponpaths_2.
      apply (z_iso_after_z_iso_inv
               (comp_cat_sigma_pair_proj_iso (comp_cat_el As) (comp_cat_el BsA))). }
    apply id_left.
  Qed.

End Universe_Sigma_Closure_Lemmas.


(**  * 6. Universe Being Closed under Unit Types  *)

Section Universe_Unit_Closure.

  Context (C : comp_cat_with_universe).

  Context (Unit : comp_cat_unit C).

  (* 1) Unit code in the universe  *)
  Definition univ_unit_code : UU := comp_cat_tm (comp_cat_U ([] : C)).

  (* 2) el commutes with unit *)
  Definition univ_unit_el_iso (OneU : univ_unit_code) : UU :=
    @z_iso (fiber_category _ _) (comp_cat_el OneU) ((pr1 Unit) []).

  Definition comp_cat_universe_closed_unit : UU :=
    ∑ (OneU : univ_unit_code),
      (univ_unit_el_iso OneU).

  Coercion unit_unit_code_from_comp_cat {UnivU : comp_cat_universe_closed_unit}
    : univ_unit_code := pr1 UnivU.

  (** accessors for unit codes  *)

  Definition comp_cat_unit_code (UnitU : comp_cat_universe_closed_unit)
    : comp_cat_tm (comp_cat_U []) := pr1 UnitU.

  Definition comp_cat_unit_el_iso (UnitU : comp_cat_universe_closed_unit)
    : @z_iso (fiber_category _ _)
        (comp_cat_el (comp_cat_unit_code UnitU)) ((pr1 Unit) [])
    := (pr2 UnitU).

  Section weaken_unit.

    (* The code of unit weakened to Γ *)
    Definition comp_cat_unit_code_weakened (UnitU : comp_cat_universe_closed_unit) (Γ : C)
      : comp_cat_tm (comp_cat_U Γ)
      := (comp_cat_unit_code UnitU [[ TerminalArrow (empty_context C) Γ ]]tm)
           ↑ ⌈comp_cat_univ_sub_iso (TerminalArrow (empty_context C) Γ)⌉.

    (* el_iso weakened to Γ *)
    Definition comp_cat_unit_el_iso_w (UnitU : comp_cat_universe_closed_unit) (Γ : C) :
      @z_iso (fiber_category _ _) (comp_cat_el (comp_cat_unit_code_weakened UnitU Γ)) ((pr1 Unit) Γ).
    Proof.
      unfold comp_cat_unit_code_weakened.
      set (tΓ := TerminalArrow (empty_context C) Γ).
      refine (z_iso_comp (z_iso_inv (comp_cat_el_iso tΓ (comp_cat_unit_code UnitU))) _).
      refine (z_iso_comp (comp_cat_reindex_iso tΓ (comp_cat_unit_el_iso UnitU)) _).
      exact (comp_cat_unit_sub_iso tΓ).
    Defined.

    (* Reindexing commutes with unit codes *)
    (*  1_Δ [s] coerced along U-iso = 1_Γ *)
    Proposition comp_cat_unit_subst_law (UnitU : comp_cat_universe_closed_unit) {Γ Δ : C}
      (s : Γ --> Δ) :
      ((comp_cat_unit_code_weakened UnitU Δ) [[ s ]]tm) ↑ ⌈comp_cat_univ_sub_iso s⌉ =
        (comp_cat_unit_code_weakened UnitU Γ).
    Proof.
      unfold comp_cat_unit_code_weakened.
      rewrite comp_cat_subst_coerce_tm.
      rewrite comp_cat_comp_coerce_tm.
      etrans.
      { apply maponpaths.
        refine (!_).
        apply comp_cat_id_coerce_tm.
      }
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        apply (@z_iso_inv_after_z_iso (fiber_category _ _) _ _ (comp_cat_subst_ty_comp_iso _ _ _)).
      }
      do 2 rewrite <- comp_cat_comp_coerce_tm.
      etrans.
      { do 3 apply maponpaths.
        refine (!_).
        apply (@comp_cat_subst_tm_comp C ).
      }
      do 2 rewrite comp_cat_comp_coerce_tm.
      assert (p :TerminalArrow (empty_context C) Γ =  s · TerminalArrow (empty_context C) Δ )
        by apply TerminalArrowEq.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (comp_cat_subst_tm_eq _ p).
      }
      rewrite comp_cat_comp_coerce_tm.
      apply comp_cat_coerce_eq.
      set (U := comp_cat_U _).
      unfold comp_cat_univ_sub_iso.
      unfold sub_comp_cat_univ_iso.
      rewrite assoc.
      assert (H: ⌈ comp_cat_subst_ty_iso U p ⌉=  ⌈ comp_cat_subst_ty_iso U (!p) ⌉⁻¹) by (induction p; apply idpath).
      rewrite H.
      unfold "⌈ _ ⌉⁻¹".
      rewrite assoc'.
      do 2 use z_iso_inv_on_right.
      rewrite assoc.
      etrans.
      { apply maponpaths_2.
        apply comp_cat_reindex_coercion_comp_witness.
      }
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply (comp_cat_reindex_coercion_subst_ty_iso (C:=C)).
      }
      rewrite assoc'.
      etrans.
      { do 2 apply maponpaths.
        apply comp_cat_subst_ty_iso_comp.
      }
      etrans.
      2: { refine (!_). refine (assoc _ _ _ @ _). apply idpath. }
      rewrite assoc'.
      etrans.
      { rewrite assoc.
        apply maponpaths_2.
        refine (!_).
        apply (comp_cat_assoc'_subst_ty (C:=C)).
      }
      etrans.
      { do 2 refine (assoc' _ _ _ @ _).
        do 2 apply maponpaths.
        apply comp_cat_subst_ty_iso_comp.
      }
      do 2 rewrite assoc.
      etrans.
      2: {
        refine (!_).
        apply maponpaths_2.
        rewrite assoc'.
        apply maponpaths.
        apply comp_cat_comp_iso_natural. }
      etrans.
      2: {
        refine (!_).
        do 2 rewrite assoc'.
        do 2 apply maponpaths.
        apply comp_cat_subst_ty_iso_comp.
      }
      rewrite assoc.
      apply cancel_precomposition.
      do 2 apply maponpaths.
      apply homset_property.
    Qed.

  End weaken_unit.

  Section Unit_Code_Unique_Term.
    (* We show that el(unit code) has a unique term *)

    Context (UnitU : comp_cat_universe_closed_unit).

    Definition term_unit_code (Γ : C) :
      comp_cat_tm (comp_cat_el (comp_cat_unit_code_weakened UnitU Γ)).
    Proof.
      use tpair.
      - exact ( (comp_cat_unit_tt Γ) ↑ ( ⌈ (comp_cat_unit_el_iso_w UnitU Γ) ⌉⁻¹ ) ).
      - abstract(
            cbn;
            rewrite <- assoc;
            rewrite comp_cat_comp_mor_law;
            exact (pr2 (comp_cat_unit_tt Γ))).
    Defined.

    Lemma unique_term_unit_code :
      ∏ {Γ : C} (t : comp_cat_tm (comp_cat_el (comp_cat_unit_code_weakened UnitU Γ))),
        t = (term_unit_code Γ).
    Proof.
      (* Uniqueness follows from el(unit_code) being iso to 1 and tt being unique. *)
      intros Γ t.
      unfold term_unit_code.
      assert (HOneΓ : iscontr (comp_cat_tm ((pr1 Unit) Γ))).
      {
        use tpair.
        - exact ( comp_cat_unit_tt Γ).
        - intro u.
          exact (comp_cat_unit_unique u).
      }
      set (HElΓ :=
             @iscontr_tm_of_iso _ Γ ((pr1 Unit) Γ) (comp_cat_el (comp_cat_unit_code_weakened UnitU Γ))
               HOneΓ (z_iso_inv (comp_cat_unit_el_iso_w UnitU Γ))).
      use subtypePath.
      - unfold isPredicate; intros; apply (homset_property C).
      - cbn.
        change (pr1 t = pr1 (term_unit_code Γ)).
        set (c := pr1 HElΓ).
        refine (maponpaths pr1 (_)).
        exact ((pr2 HElΓ t) @ !(pr2 HElΓ (term_unit_code Γ))).
    Qed.

  End Unit_Code_Unique_Term.

End Universe_Unit_Closure.

(** * 7. Universe Being Closed under Pi Types  *)

Section Universe_Pi_Closure.

  Context (C : comp_cat_with_universe).

  Context (Π : comp_cat_pi C).

  (* 1. Pi code in the universe *)
  (* Γ ⊢ A : U , Γ.el(A) ⊢ B : U  => Γ ⊢ Π(A,B) : U *)
  Definition univ_pi_form : UU :=
    ∏ (Γ : C)
      (A : comp_cat_tm (comp_cat_U Γ))
      (B : comp_cat_tm (comp_cat_U (Γ & comp_cat_el A))),
      comp_cat_tm (comp_cat_U Γ).

  (* 2. el commutes with pi  *)
  (* el(Π(A,B)) ≃ Π_el(A) el(B) *)
  Definition univ_pi_el_iso (ΠU : univ_pi_form) : UU :=
    ∏ (Γ : C)
      (A : comp_cat_tm (comp_cat_U _))
      (B : comp_cat_tm (comp_cat_U _)),
      @z_iso (fiber_category _ _) (comp_cat_el (ΠU Γ A B))
        ((pr1 Π) Γ (comp_cat_el A)
           (comp_cat_el B)).

  (* 3. Π-codes commute with substitution  *)
  (* Π(A,B)[s] = Π(A[s],B[s.el(A)])  *)
  (* modulo some coercions *)
  Definition univ_pi_subst_law (ΠU : univ_pi_form) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ)
      (A : comp_cat_tm (comp_cat_U _))
      (B : comp_cat_tm (comp_cat_U _)),
      let e := ⌈sub_comp_cat_univ_iso _ s⌉ in
      let As := (A [[ s ]]tm) ↑ e in
      let el_iso := comp_cat_el_iso s A in
      let sA := comp_cat_ext_subst s (comp_cat_el A) in
      let e' := ⌈sub_comp_cat_univ_iso _ (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉ in
      let BsA := B [[ comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA ]]tm ↑ e' in
      (ΠU Δ A B) [[ s ]]tm ↑ e = ΠU Γ As BsA.

  (** 4. coherence for Π-codes *)
  Definition univ_pi_coherent
    (ΠU : univ_pi_form)
    (Πeli : univ_pi_el_iso ΠU)
    (Πlaw : univ_pi_subst_law ΠU)
    : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ)
    (A : comp_cat_tm (comp_cat_U Δ))
    (B : comp_cat_tm (comp_cat_U (Δ & comp_cat_el A)))
    (t : comp_cat_tm (comp_cat_el B)),
      let As  := (A [[ s ]]tm) ↑ ⌈sub_comp_cat_univ_iso _ s⌉ in
       let sA := comp_cat_ext_subst s (comp_cat_el A) in
  let lift   := comp_cat_univ_lift _ s A in
  let el_iso := comp_cat_el_iso s A in
  let BsA := B [[ comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA ]]tm ↑ (⌈sub_comp_cat_univ_iso _ (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉) in
  (comp_cat_pi_lam t ↑ ⌈Πeli Δ A B⌉⁻¹) [[ s ]]tm
      ↑ ⌈comp_cat_el_iso s (ΠU Δ A B)⌉
      ↑ comp_cat_el_map (Πlaw Γ Δ s A B)
  = comp_cat_pi_lam (t [[ lift ]]tm ↑ ⌈comp_cat_el_iso lift B⌉)
      ↑ ⌈Πeli Γ As BsA⌉⁻¹.

  Definition comp_cat_universe_closed_pi : UU :=
    ∑ (ΠU : univ_pi_form),
      ∑ (eliso : univ_pi_el_iso ΠU),
      ∑ (law : univ_pi_subst_law ΠU ),
            univ_pi_coherent ΠU eliso law.

  Coercion comp_cat_with_pi_to_comp_cat (PiU : comp_cat_universe_closed_pi)
    : univ_pi_form := pr1 PiU.

  (** accessors for pi codes  *)

  Definition comp_cat_pi_code (PiU : comp_cat_universe_closed_pi)
    {Γ : C} (A : comp_cat_tm (comp_cat_U _))
    (B : comp_cat_tm (comp_cat_U _)) :
    comp_cat_tm (comp_cat_U _)
    := (pr1 PiU) Γ A B.

  Definition comp_cat_pi_el_iso (PiU : comp_cat_universe_closed_pi)
    {Γ : C} (A : comp_cat_tm (comp_cat_U _))
    (B : comp_cat_tm (comp_cat_U _)):
    @z_iso (fiber_category _ _) (comp_cat_el (comp_cat_pi_code PiU A B))
      ((pr1 Π) Γ (comp_cat_el A)
         (comp_cat_el B))
    := (pr12 PiU) Γ A B.

  Definition comp_cat_univ_pi_subst (PiU : comp_cat_universe_closed_pi)
    {Γ Δ : C} (s : Γ --> Δ)
    (A : comp_cat_tm (comp_cat_U _))
    (B : comp_cat_tm (comp_cat_U _)) :
    let e := ⌈sub_comp_cat_univ_iso _ s⌉ in
    let As := (A [[ s ]]tm) ↑ e in
    let el_iso := comp_cat_el_iso s A in
    let sA := comp_cat_ext_subst s (comp_cat_el A) in
    let e' := ⌈sub_comp_cat_univ_iso _ (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉ in
    let BsA := B [[ comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA ]]tm ↑ e' in
    let ΣU := (@comp_cat_pi_code PiU) in
    (ΣU Δ A B) [[ s ]]tm ↑ e = (ΣU Γ As BsA)
    := (pr122 PiU) _ _ s A B.

  Definition comp_cat_univ_pi_coherent (PiU : comp_cat_universe_closed_pi)
    {Γ Δ : C} (s : Γ --> Δ)
    (A : comp_cat_tm (comp_cat_U Δ))
    (B : comp_cat_tm (comp_cat_U (Δ & comp_cat_el A)))
      (t : comp_cat_tm (comp_cat_el B)):
    let As := (A [[ s ]]tm) ↑ ⌈sub_comp_cat_univ_iso _ s⌉ in
    let el_iso := comp_cat_el_iso s A in
    let sA := comp_cat_ext_subst s (comp_cat_el A) in
    let BsA := B [[ comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA ]]tm ↑ (⌈sub_comp_cat_univ_iso _ (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉) in
    let lift   := comp_cat_univ_lift _ s A in
    let ΠU := (@comp_cat_pi_code PiU) in
    let Πeli := @comp_cat_pi_el_iso PiU in
    let Πlaw := comp_cat_univ_pi_subst PiU in
    (comp_cat_pi_lam t ↑ ⌈Πeli Δ A B⌉⁻¹) [[ s ]]tm
      ↑ ⌈comp_cat_el_iso s (ΠU Δ A B)⌉
      ↑ comp_cat_el_map (Πlaw s A B)
  = comp_cat_pi_lam (t [[ lift ]]tm ↑ ⌈comp_cat_el_iso lift B⌉)
      ↑ ⌈Πeli Γ As BsA⌉⁻¹
    := (pr222 PiU) _ _ s A B t.

End Universe_Pi_Closure.

(** 8. Lemmas about universes closed under Π-types *)

Section Universe_Pi_Closure_Lemmas.

  Context (C : comp_cat_with_universe)
    (Pi : comp_cat_pi C)
    (PiU : comp_cat_universe_closed_pi C Pi).

  Lemma comp_cat_pi_lam_el_map
    {Γ : C} (A : comp_cat_tm (comp_cat_U Γ))
    {B B' : comp_cat_tm (comp_cat_U (Γ & comp_cat_el A))}
    (p : B = B') (t : comp_cat_tm (comp_cat_el B))
    : comp_cat_pi_lam (Π := Pi) (t ↑ comp_cat_el_map p)
        ↑ ⌈ comp_cat_pi_el_iso C Pi PiU A B' ⌉⁻¹
      = comp_cat_pi_lam (Π := Pi) t
          ↑ ⌈ comp_cat_pi_el_iso C Pi PiU A B ⌉⁻¹
          ↑ comp_cat_el_map (maponpaths (comp_cat_pi_code C Pi PiU A) p).
  Proof.
    induction p.
    etrans.
    { do 2 apply maponpaths.
      apply comp_cat_id_coerce_tm. }
    refine (!_).
    apply comp_cat_id_coerce_tm.
  Qed.

End Universe_Pi_Closure_Lemmas.

Close Scope comp_cat.
