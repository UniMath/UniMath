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
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Export UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.

Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
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
  exact (comp_cat_subst_ty_iso (C:=C) U p).
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

Definition comp_cat_universe_data (C : comp_cat_with_terminal) : UU
  := ∑ (U : comp_cat_ty []),
    ∑ (el : ∏ (Γ : C), comp_cat_tm Γ (weakened_from_empty U _) -> comp_cat_ty Γ),
      (∏ (Γ Δ : C) (s : Γ --> Δ) (t : comp_cat_tm Δ (weakened_from_empty U _)),
        @z_iso (fiber_category _ _)
              ((el _ t) [[ s ]])
              (el _ (t [[ s ]]tm ↑ ⌈sub_comp_cat_univ_iso U s⌉))).

(* This will probably not be needed in the mapping to CwFs. *)
Definition comp_cat_universe_coherent {C : comp_cat_with_terminal} (universe : comp_cat_universe_data C) : UU.
Proof.
  Admitted.

Definition comp_cat_universe (C : comp_cat_with_terminal) : UU
  := ∑ (universe : comp_cat_universe_data C), comp_cat_universe_coherent universe.

Definition comp_cat_with_universe : UU := total2 comp_cat_universe.

Coercion comp_cat_with_universe_to_comp_cat (C : comp_cat_with_universe) : comp_cat_with_terminal := pr1 C.

Definition comp_cat_empty_ctx (C : comp_cat_with_universe) : Terminal C := pr21 C.

Definition comp_cat_U (C : comp_cat_with_universe) : comp_cat_ty [] := pr112 C.

Definition comp_cat_El (C : comp_cat_with_universe) :
  ∏ (Γ : pr1 C), comp_cat_tm Γ (weakened_from_empty (comp_cat_U C) _) -> comp_cat_ty Γ
  := pr1 (pr212 C).

Definition comp_cat_El_iso (C : comp_cat_with_universe) :
  ∏ (Γ Δ : C) (s : Γ --> Δ) (t : comp_cat_tm Δ (weakened_from_empty (comp_cat_U _) _)),
    @z_iso (fiber_category _ _)
      (((comp_cat_El _) _ t) [[ s ]])
      ((comp_cat_El _) _ (t [[ s ]]tm ↑ ⌈sub_comp_cat_univ_iso (comp_cat_U _) s⌉))
  := pr2 (pr212 C).

Close Scope comp_cat.


(**  Universe Being Closed under Sigma-Types  *)

Open Scope comp_cat.

Section Universe_Sigma_Closure.

  Context (C : comp_cat_with_universe).
  Let CC := (pr1 C).

  Context (Σ : comp_cat_sigma CC).
  Let Σty := (pr1 Σ).

  (* 1. Sigma code in the universe *)
  (* Γ ⊢ A : U , Γ.el(A) ⊢ B : U  => Γ ⊢ Σ(A,B) : U *)
  Definition univ_sigma_form : UU :=
    ∏ (Γ : CC)
      (A : comp_cat_tm Γ (weakened_from_empty (comp_cat_U C) _))
      (B : comp_cat_tm (Γ & comp_cat_El C Γ A)
                       (weakened_from_empty (comp_cat_U C) _)),
      comp_cat_tm Γ (weakened_from_empty (comp_cat_U C) _).

  (* 2. el commutes with sigma  *)
  (* el(Σ(A,B)) ≃ Σ_el(A) el(B) *)
  Definition univ_sigma_el_iso (ΣU : univ_sigma_form) : UU :=
    ∏ (Γ : CC)
      (A : comp_cat_tm Γ (weakened_from_empty (comp_cat_U C) _))
      (B : comp_cat_tm (Γ & comp_cat_El C Γ A)
                       (weakened_from_empty (comp_cat_U C) _)),
      @z_iso (fiber_category _ _) (comp_cat_El C Γ (ΣU Γ A B))
        (Σty Γ (comp_cat_El C Γ A)
           (comp_cat_El C (Γ & comp_cat_El C Γ A) B)).

  (* 3. Σ-codes commute with substitution  *)
  (* Σ(A,B)[s] = Σ(A[s],B[s.el(A)])  *)
  (* modulo some coercions *)
  Definition univ_sigma_subst_law (ΣU : univ_sigma_form) : UU :=
    ∏ (Γ Δ : CC) (s : Γ --> Δ)
      (A : comp_cat_tm Δ (weakened_from_empty (comp_cat_U C) _))
      (B : comp_cat_tm (Δ & comp_cat_El C Δ A)
             (weakened_from_empty (comp_cat_U C) _)),
      let e := ⌈sub_comp_cat_univ_iso (comp_cat_U C) s⌉ in
      let As := (A [[ s ]]tm) ↑ e in
      let el_iso := comp_cat_El_iso _ _ _ s A in
      let sA := comp_cat_ext_subst Δ Γ s (comp_cat_El C Δ A) in
      let e' := ⌈sub_comp_cat_univ_iso (comp_cat_U C) (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉ in
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

End Universe_Sigma_Closure.

Close Scope comp_cat.

(**  Universe Being Closed under Unit Types  *)

Open Scope comp_cat.

Section Universe_Unit_Closure.

  Context (C : comp_cat_with_universe).

  Context (Unit : comp_cat_unit C).
  Let One : ∏ Γ : C, comp_cat_ty Γ := pr1 Unit.
  Let tt  : ∏ Γ : C, comp_cat_tm Γ (One Γ) := pr12 Unit.

  (* 1) Unit code in the universe  *)
  Definition univ_unit_code : UU :=
    ∏ (Γ : C),
      comp_cat_tm Γ (weakened_from_empty (comp_cat_U C) _).

  (* 2) el commutes with unit *)
  Definition univ_unit_el_iso (OneU : univ_unit_code) : UU :=
    ∏ (Γ : C), z_iso (C := fiber_category _ _) (comp_cat_El C Γ (OneU Γ)) (One Γ).

  (* 3) Reindexing commutes with unit codes *)
  (*  1_Δ [s] coerced along U-iso = 1_Γ *)
  Definition univ_unit_subst_law (OneU : univ_unit_code) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ),
      (OneU Δ [[ s ]]tm) ↑ ⌈sub_comp_cat_univ_iso (comp_cat_U C) s⌉ = OneU Γ.

  (* 4) Coherence of the isos  *)
  Definition univ_unit_iso_coh
             (OneU : univ_unit_code)
             (eliso : univ_unit_el_iso OneU)
             (OneSub : univ_unit_subst_law OneU) : UU.
  Proof.
  Admitted.

  Definition comp_cat_universe_closed_unit : UU :=
    ∑ (OneU : univ_unit_code),
    ∑ (eliso : univ_unit_el_iso OneU),
    ∑ (OneSub : univ_unit_subst_law OneU),
      univ_unit_iso_coh OneU eliso OneSub.

  Coercion unit_unit_code_from_comp_cat {UnivU : comp_cat_universe_closed_unit}
    : univ_unit_code := pr1 UnivU.

  Section Unit_Code_Unique_Term.
    (* We show that el(unit code) has a unique term *)

    Context (UnitU : comp_cat_universe_closed_unit).

    Definition term_unit_code (Γ : C) : comp_cat_tm _  (comp_cat_El _ _ (pr1 UnitU Γ)).
    Proof.
      use tpair.
      - exact ( (tt Γ) ↑ ( ⌈ ((pr12 UnitU) Γ) ⌉⁻¹ ) ).
      - abstract(
            cbn;
            rewrite <- assoc;
            rewrite comp_cat_comp_mor_law;
            exact (pr2 (tt Γ))).
    Defined.

    Definition iscontr_tm_of_iso {Γ : C} {A B : comp_cat_ty Γ}
      (HA : iscontr (comp_cat_tm Γ A))
      (i : z_iso (C := fiber_category _ _) A B)
      : iscontr (comp_cat_tm Γ B).
    Proof.
      set (toB := (λ u : comp_cat_tm Γ A, u ↑ ⌈ i ⌉)).
      set (toA := (λ v : comp_cat_tm Γ B, v ↑ ⌈ i ⌉⁻¹)).
      assert (toB_toA : ∏ v : comp_cat_tm Γ B, toB (toA v) = v) by apply coerce_tm_after_inv.
      assert (toA_toB : ∏ u : comp_cat_tm Γ A, toA (toB u) = u) by apply coerce_tm_inv_after.
      set (w := weq_iso toB toA toA_toB toB_toA).
      exact (iscontrweqf w HA).
    Defined.

    Lemma unique_term_unit_code :
      ∏ {Γ : C} (t : comp_cat_tm _  (comp_cat_El _ _ (pr1 UnitU Γ))),
        t = (term_unit_code Γ).
    Proof.
      (* Uniqueness follows from el(unit_code) being iso to 1 and tt being unique. *)
      intros Γ t.
      unfold term_unit_code.
      set (iso := pr12 UnitU).
      set (unit_unique := pr12 (pr222 Unit)).
      assert (HOneΓ : iscontr (comp_cat_tm Γ (One Γ))).
      {
         use tpair.
          - exact (tt Γ).
          - intro u.
            exact (unit_unique Γ u).
      }
      set (HElΓ :=
        iscontr_tm_of_iso (Γ:=Γ) (A:=One Γ) (B:=comp_cat_El C Γ (pr1 UnitU Γ))
          HOneΓ (z_iso_inv (iso Γ))).
      use subtypePath.
      - unfold isPredicate. intros. apply (homset_property C).
      - cbn.
        change (pr1 t = pr1 (term_unit_code Γ)).
        set (c := pr1 HElΓ).
        refine (maponpaths pr1 (_)).
        exact ((pr2 HElΓ t) @ !(pr2 HElΓ (term_unit_code Γ))).
   Defined.

End Unit_Code_Unique_Term.

End Universe_Unit_Closure.

Close Scope comp_cat.


(**  Universe Being Closed under Pi Types  *)

Open Scope comp_cat.

Section Universe_Pi_Closure.

  Context (C : comp_cat_with_universe).
  Let CC := (pr1 C).

  Context (Π : comp_cat_pi CC).
  Let Πty := (pr1 Π).

  (* 1. Pi code in the universe *)
  (* Γ ⊢ A : U , Γ.el(A) ⊢ B : U  => Γ ⊢ Π(A,B) : U *)
  Definition univ_pi_form : UU :=
    ∏ (Γ : CC)
      (A : comp_cat_tm Γ (weakened_from_empty (comp_cat_U C) _))
      (B : comp_cat_tm (Γ & comp_cat_El C Γ A)
                       (weakened_from_empty (comp_cat_U C) _)),
      comp_cat_tm Γ (weakened_from_empty (comp_cat_U C) _).

  (* 2. el commutes with pi  *)
  (* el(Π(A,B)) ≃ Π_el(A) el(B) *)
  Definition univ_pi_el_iso (ΠU : univ_pi_form) : UU :=
    ∏ (Γ : CC)
      (A : comp_cat_tm Γ (weakened_from_empty (comp_cat_U C) _))
      (B : comp_cat_tm (Γ & comp_cat_El C Γ A)
                       (weakened_from_empty (comp_cat_U C) _)),
      @z_iso (fiber_category _ _) (comp_cat_El C Γ (ΠU Γ A B))
        (Πty Γ (comp_cat_El C Γ A)
           (comp_cat_El C (Γ & comp_cat_El C Γ A) B)).

  (* 3. Π-codes commute with substitution  *)
  (* Π(A,B)[s] = Π(A[s],B[s.el(A)])  *)
  (* modulo some coercions *)
  Definition univ_pi_subst_law (ΠU : univ_pi_form) : UU :=
    ∏ (Γ Δ : CC) (s : Γ --> Δ)
      (A : comp_cat_tm Δ (weakened_from_empty (comp_cat_U C) _))
      (B : comp_cat_tm (Δ & comp_cat_El C Δ A)
             (weakened_from_empty (comp_cat_U C) _)),
      let e := ⌈sub_comp_cat_univ_iso (comp_cat_U C) s⌉ in
      let As := (A [[ s ]]tm) ↑ e in
      let el_iso := comp_cat_El_iso _ _ _ s A in
      let sA := comp_cat_ext_subst Δ Γ s (comp_cat_El C Δ A) in
      let e' := ⌈sub_comp_cat_univ_iso (comp_cat_U C) (comp_cat_comp_mor (⌈el_iso⌉⁻¹) · sA)⌉ in
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

End Universe_Pi_Closure.

Close Scope comp_cat.
