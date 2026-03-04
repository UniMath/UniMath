(*

  Universe in Comprehension Categories

  Let C be a comprehension category with a terminal empty context [].
  We say C has a universe if we have :
  - U : ty [], which gives rise to U_Γ : ty Γ
  - a function el : tm U_Γ ➙ ty Γ
  - for each s : Γ → Δ and t : tm U_Δ, an isomorphism i : el (t) [s] ≃ el (t[s])
  such that i commutes with i_id and i_comp.

  This definition is similar to the definition of universe in comprehension bicategories
  presented in "The Internal Language of Univalent Categories" by Van der Weide.
  A similar definition for CwFs is presented in "Principles of Dependent Type Theory"
  by Angiuli and Gratzer.

  We also define the universe being closed type formers similar to Van der Weide.

  References
  - "The Internal Languages of Univalent Categories" by Van der Weide
  - "Principles of Dependent Type Theory" by Angiuli and Gratzer

  Contents
  - Empty Context in Comprehension Categories
  - Comprehension Category with a Universe
  - Universes being closed under type formers: Π, Σ, unit, TODO: id

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
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.

Require Import UniMath.CategoryTheory.ComprehensionCats.CompCats.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatTypeFormers.

Local Open Scope cat.
Local Open Scope comp_cat.

(**  Comprehension category with a terminal context  *)

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

  (* using terminal-arrow uniqueness *)
  assert (p : s · tΔ = tΓ) by apply TerminalArrowEq.

  (* (U[[tΔ]])[[s]]  ≅  U[[s·tΔ]]  ≅  U[[tΓ]] *)
  refine (z_iso_comp (comp_cat_subst_ty_comp_iso U tΔ s) _).
  exact (comp_cat_subst_ty_iso U p).
Defined.

(**  Comprehension category with a terminal context and universe *)

(*
Let C be a comprehension category with a terminal empty context [].
We say C has a universe if we have :
  - U : ty [], which gives rise to U_Γ : ty Γ
  - a function el : tm U_Γ \to ty Γ
  - for each s : Γ → Δ and t : tm U_Δ, an isomorphism i : el (t) [s] ≃ el (t[s])
  such that i commutes with i_id and i_comp.
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

Section universe_coherence.
  Context (C : comp_cat_with_terminal)
    (universe : comp_cat_universe_data C).

  Let U := pr1 universe.
  Let el := pr12 universe.
  Let i := pr22 universe.

  Local Lemma elmaplemma {Γ : C}
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

  Definition comp_cat_universe_coherent_id
    : UU
    := ∏ (Γ : C)
         (t : comp_cat_tm (weakened_from_empty U _)),
      @identity (fiber_category _ _) (el _ t ) =
        comp_cat_subst_ty_id_iso _
          · i _ _ (identity Γ) t
          · el_map _ _ elmaplemma.

  Local Lemma elmaplemmacomp
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
    rewrite !assoc'.
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

  Definition comp_cat_universe_coherent_comp : UU
    :=
    ∏ (Γ Δ Θ : C) (s₁ : Γ --> Δ) (s₂ : Θ --> Γ)
        (t : comp_cat_tm (weakened_from_empty U _)),
      comp_cat_reindex_iso s₂ (i _ _ s₁ t)
        · (i _ _ s₂ _)
        =
          comp_cat_subst_ty_comp_iso (el _ t) s₁ s₂
            · (i _ _ (s₂ · s₁) t)
            · el_map _ _ elmaplemmacomp.

End universe_coherence.

Definition comp_cat_universe_coherent
  {C : comp_cat_with_terminal}
  (universe : comp_cat_universe_data C) : UU
  := comp_cat_universe_coherent_id _ universe
     ×
     comp_cat_universe_coherent_comp _ universe.

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

Definition comp_cat_univ_eq_ty_el_map
  (C : comp_cat_with_universe)
  {Γ : C} {a b : comp_cat_tm (comp_cat_U _)}
  (p : a = b)
  : (comp_cat_el a) -->[identity _] (comp_cat_el b)
  := (el_map (pr12 C) Γ p).

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

(**  Universe Being Closed under Sigma-Types  *)

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

  (* 4. Coherence of the isos  *)
  Definition univ_sigma_iso_coh
             (ΣU : univ_sigma_form)
             (eliso : univ_sigma_el_iso ΣU)
             (Σsubst : univ_sigma_subst_law ΣU) : UU.
  Proof.
  Admitted.

  Definition comp_cat_universe_closed_sigma : UU :=
    ∑ (ΣU : univ_sigma_form),
    ∑ (eliso : univ_sigma_el_iso ΣU),
    ∑ (Σsubst : univ_sigma_subst_law ΣU),
      univ_sigma_iso_coh ΣU eliso Σsubst.

  Coercion comp_cat_with_sigma_to_comp_cat (SigmaU : comp_cat_universe_closed_sigma)
    : univ_sigma_form := pr1 SigmaU.

   (** accessors for sigma codes  *)

  Definition comp_cat_sigma_code (SigmaU : comp_cat_universe_closed_sigma)
    {Γ : C} (A : comp_cat_tm (comp_cat_U _))
    (B : comp_cat_tm (comp_cat_U _)) :
    comp_cat_tm (comp_cat_U _)
    := (pr1 SigmaU) Γ A B.

  Definition comp_cat_sigma_el_iso (SigmaU : comp_cat_universe_closed_sigma)
    {Γ : C} (A : comp_cat_tm (comp_cat_U _))
    (B : comp_cat_tm (comp_cat_U _)):
    @z_iso (fiber_category _ _) (comp_cat_el (comp_cat_sigma_code SigmaU A B))
      ((pr1 Σ) Γ (comp_cat_el A)
         (comp_cat_el B))
      := (pr12 SigmaU) Γ A B.

  Definition comp_cat_sigma_subst (SigmaU : comp_cat_universe_closed_sigma)
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
      := (pr1 (pr22 SigmaU)) _ _ s A B.

End Universe_Sigma_Closure.


(**  Universe Being Closed under Unit Types  *)

Section Universe_Unit_Closure.

  Context (C : comp_cat_with_universe).

  Context (Unit : comp_cat_unit C).


  (* 1) Unit code in the universe  *)
  Definition univ_unit_code : UU := comp_cat_tm (comp_cat_U ([] : C)).

  (* 2) el commutes with unit *)
  Definition univ_unit_el_iso (OneU : univ_unit_code) : UU :=
    @z_iso (fiber_category _ _) (comp_cat_el OneU) ((pr1 Unit) []).

  (* 3) Coherence of the isos  *)
  Definition univ_unit_iso_coh
             (OneU : univ_unit_code)
             (eliso : univ_unit_el_iso OneU) : UU.
  Proof.
  Admitted.

  Definition comp_cat_universe_closed_unit : UU :=
    ∑ (OneU : univ_unit_code),
    ∑ (eliso : univ_unit_el_iso OneU),
      univ_unit_iso_coh OneU eliso.

  Coercion unit_unit_code_from_comp_cat {UnivU : comp_cat_universe_closed_unit}
    : univ_unit_code := pr1 UnivU.

  (** accessors for pi codes  *)

  Definition comp_cat_unit_code (UnitU : comp_cat_universe_closed_unit)
    : comp_cat_tm (comp_cat_U []) := pr1 UnitU.

  Definition comp_cat_unit_el_iso (UnitU : comp_cat_universe_closed_unit)
    : @z_iso (fiber_category _ _)
        (comp_cat_el (comp_cat_unit_code UnitU)) ((pr1 Unit) [])
    := (pr12 UnitU).

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

      (*
    Proposition comp_coerce_subst_ty
              {C : comp_cat}
              {Γ₁ Γ₂ : C}
              (s : Γ₁ --> Γ₂)
              {A₁ A₂ A₃ : ty Γ₂}
              (f : A₁ <: A₂)
              (g : A₂ <: A₃)
    : coerce_subst_ty s (f · g)
      =
      coerce_subst_ty s f · coerce_subst_ty s g.
  Proof.
    apply (functor_comp (fiber_functor_from_cleaving _ (cleaving_of_types C) s)).
  Qed.
 *)

    (*

Proposition assoc'_subst_ty
            {C : comp_cat}
            {Γ₁ Γ₂ Γ₃ Γ₄ : C}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (s₃ : Γ₃ --> Γ₄)
            (A : ty Γ₄)
  : comp_subst_ty s₁ s₂ (A [[ s₃ ]])
    · comp_subst_ty (s₁ · s₂) s₃ A
    · eq_subst_ty A (assoc' _ _ _)
    =
    coerce_subst_ty s₁ (comp_subst_ty s₂ s₃ A)
    · comp_subst_ty s₁ (s₂ · s₃) A.
Proof.
  exact (indexed_cat_lassociator (cleaving_to_indexed_cat _ (cleaving_of_types C)) _ _ _ _).
Qed.

Proposition assoc_subst_ty
            {C : comp_cat}
            {Γ₁ Γ₂ Γ₃ Γ₄ : C}
            (s₁ : Γ₁ --> Γ₂)
            (s₂ : Γ₂ --> Γ₃)
            (s₃ : Γ₃ --> Γ₄)
            (A : ty Γ₄)
  : comp_subst_ty s₁ s₂ (A [[ s₃ ]])
    · comp_subst_ty (s₁ · s₂) s₃ A
    =
    coerce_subst_ty s₁ (comp_subst_ty s₂ s₃ A)
    · comp_subst_ty s₁ (s₂ · s₃) A
    · eq_subst_ty A (assoc _ _ _).
Proof.
  rewrite <- assoc'_subst_ty.
  refine (!(id_right _) @ _ @ assoc _ _ _).
  apply maponpaths.
  rewrite eq_subst_ty_concat.
  rewrite eq_subst_ty_idpath.
  apply idpath.
Qed.

     *)

    Admitted.

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

    Lemma iscontr_tm_of_iso {Γ : C} {A B : comp_cat_ty Γ}
      (HA : iscontr (comp_cat_tm A))
      (i : z_iso (C := fiber_category _ _) A B)
      : iscontr (comp_cat_tm B).
    Proof.
      set (toB := (λ u : comp_cat_tm A, u ↑ ⌈ i ⌉)).
      set (toA := (λ v : comp_cat_tm B, v ↑ ⌈ i ⌉⁻¹)).
      assert (toB_toA : ∏ v : comp_cat_tm B, toB (toA v) = v) by apply coerce_tm_after_inv.
      assert (toA_toB : ∏ u : comp_cat_tm A, toA (toB u) = u) by apply coerce_tm_inv_after.
      set (w := weq_iso toB toA toA_toB toB_toA).
      exact (iscontrweqf w HA).
    Qed.

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
        @iscontr_tm_of_iso Γ ((pr1 Unit) Γ) (comp_cat_el (comp_cat_unit_code_weakened UnitU Γ))
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

(**  Universe Being Closed under Pi Types  *)

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

  (* 4. Coherence of the isos  *)
  Definition univ_pi_iso_coh
             (ΠU : univ_pi_form)
             (eliso : univ_pi_el_iso ΠU)
             (Πsubst : univ_pi_subst_law ΠU) : UU.
  Proof.
  Admitted.

  Definition comp_cat_universe_closed_pi : UU :=
    ∑ (ΠU : univ_pi_form),
    ∑ (eliso : univ_pi_el_iso ΠU),
    ∑ (Πsubst : univ_pi_subst_law ΠU),
      univ_pi_iso_coh ΠU eliso Πsubst.

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

  Definition comp_cat_pi_subst (PiU : comp_cat_universe_closed_pi)
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
      := (pr1 (pr22 PiU)) _ _ s A B.

End Universe_Pi_Closure.

Close Scope comp_cat.
