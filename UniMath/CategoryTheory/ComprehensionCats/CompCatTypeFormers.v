

(*

  Type Formers in Comprehension Categories

  This developement follows "From Semantics to Syntax: A Type Theory for Comprehension
  Categories" by Najmaei, Van der Weide, Ahrens, and North

  Contents

  1. Sigma Types
  2. Pi Types
  3. TODO: Id Types
  4. Unit Types

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

(** Sigma-types for comprehension categories  *)

Local Open Scope comp_cat.
Local Open Scope cat.

Section Sigma_For_Comp_Cat.

  (* The rules are from Figure 2 of "From Semantics to Syntax : A Type Theory for Comprehension Categories" *)

  Context (C : comp_cat).

  (* 1. Formation rule for sigma: Γ ⊢ A type, Γ.A ⊢ B type  =>  Γ ⊢ Σ(A,B) type *)
  Definition sigma_form : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      comp_cat_ty Γ.

  (* 2. Introduction rule for sigma: pairing map pair : Γ.A.B → Γ.Σ(A,B)  *)
  (*    plus a law saying: πΣ ∘ pair = πA ∘ πB *)
  Definition sigma_pair_data
             (Σty : sigma_form) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      (((Γ & A) & B) --> (Γ & (Σty _ A B))).

  Definition sigma_pair_law
             (Σty : sigma_form)
             (pair : sigma_pair_data Σty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      (pair Γ A B) · π (Σty Γ A B) = (π B) · (π A).

  (* 3. Elimination rule for sigma: projΣ : Γ.Σ(A,B) → Γ.A.B *)
  Definition sigma_proj_data
             (Σty : sigma_form) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      (Γ & (Σty Γ A B)) --> ((Γ & A) & B).

  (* β rule: proj ∘ pair ≡ 1_{Γ.A.B}  *)
  Definition sigma_beta_law
             (Σty : sigma_form)
             (pair : sigma_pair_data Σty)
             (proj : sigma_proj_data Σty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      (pair Γ A B) · (proj Γ A B) = identity (((Γ & A) & B)).

  (* η rule: pair ∘ proj ≡ 1_{Γ.Σ(A,B)} *)
  Definition sigma_eta_law
             (Σty : sigma_form)
             (pair : sigma_pair_data Σty)
             (proj : sigma_proj_data Σty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      (proj Γ A B) · (pair Γ A B) = identity (Γ & (Σty Γ A B)).

  (* 4. Stability of Sigma under substitution : Σ(A,B)[s] ≃ Σ(A[s], B[s.A]) *)
  Definition sigma_sub_iso
             (Σty : sigma_form) : UU :=
    ∏ (Γ Δ : C) (s : Δ --> Γ)
      (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      z_iso (C := fiber_category _ _)
        ((Σty Γ A B) [[ s ]])
        (Σty Δ (A [[ s ]])
           (B [[ comp_cat_ext_subst _ _ s A ]])).

  (* 5. Stability of pair under substitution*)
  Definition sigma_sub_pair_law
             (Σty : sigma_form)
             (pair : sigma_pair_data Σty)
             (σiso : sigma_sub_iso Σty) : UU :=
    ∏ (Γ Δ : C) (s : Δ --> Γ)
      (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),

      let sA  := comp_cat_ext_subst Γ Δ s A in
      let sAB := comp_cat_ext_subst (Γ & A) (Δ & (A [[ s ]]))
                 sA B in
      let i := σiso Γ Δ s A B in
      (pair Δ (A [[ s ]]) (B [[ sA ]]) ·
         comp_cat_comp_mor (C:=C) (Γ:=Δ)
           (inv_from_z_iso i : _ -->[ identity _ ] _)·
         comp_cat_ext_subst (C:=C) Γ Δ s (Σty Γ A B) = sAB · pair Γ A B).

  Definition comp_cat_sigma : UU :=
    ∑ (Σty : sigma_form),
    ∑ (pair : sigma_pair_data Σty),
    ∑ (pair_π : sigma_pair_law Σty pair),
    ∑ (proj : sigma_proj_data Σty),
      ( sigma_beta_law Σty pair proj )
      × ( sigma_eta_law  Σty pair proj )
      × (∑ (σiso : sigma_sub_iso Σty),
        sigma_sub_pair_law Σty pair σiso).

  Coercion sigma_ty_from_sigma (Sigma: comp_cat_sigma) : sigma_form := pr1 Sigma.

  (* from sigma_proj, we can derive the usual first projections of sigma *)
  Definition comp_cat_sigma_proj_1
    {Γ : C}
    (Σ : comp_cat_sigma)
    : ∏ (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      C ⟦ Γ & (pr1 Σ Γ A B) , Γ & A ⟧.
  Proof.
    intros A B.
    unfold comp_cat_sigma in Σ.
    set (proj := pr1 (pr222 Σ) Γ A B).
    exact (proj · π B).
  Defined.

  Definition comp_cat_sigma_proj_1_law
    {Γ : C}
    (Σ : comp_cat_sigma)
    (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
    : (comp_cat_sigma_proj_1 _ A B) · (π A) = π (pr1 Σ Γ A B).
  Proof.
    unfold comp_cat_sigma_proj_1.
    set (proj := (pr122 (pr2 Σ))).
    set (pairlaw := pr122 Σ).
    set (η := pr122 (pr222 Σ)).
    rewrite assoc'.
    rewrite <- pairlaw.
    rewrite assoc.
    rewrite η.
    apply id_left.
  Qed.


End Sigma_For_Comp_Cat.


(** Pi-types for comprehension categories  *)

Open Scope comp_cat.

Section Pi_For_Comp_Cat.

  (* The rules are from Figure 1 of "From Semantics to Syntax : A Type Theory for Comprehension Categories" *)

  Context (C : comp_cat).

  (* 1. Formation rule for pi: Γ ⊢ A type, Γ.A ⊢ B type  =>  Γ ⊢ Π(A,B) type *)
  Definition pi_form : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      comp_cat_ty Γ.

  (* 2. Introduction rule for pi: lambda abstraction *)
  (*    Γ.A ⊢ b : B  =>  Γ ⊢ λb : Π(A,B) *)
  Definition pi_lam_data
             (Πty : pi_form) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      comp_cat_tm ((Γ & A)) B ->
      comp_cat_tm Γ (Πty Γ A B).

  (* 3. Elimination rule for pi: application *)
  (*    Γ ⊢ f : Π(A,B)  =>  Γ.A ⊢ app(f) : B *)
  Definition pi_app_data
             (Πty : pi_form) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      comp_cat_tm Γ (Πty Γ A B) ->
      comp_cat_tm (Γ & A) B.

  (* β rule: app (λ b) ≡ b *)
  Definition pi_beta_law
             (Πty : pi_form)
             (lam : pi_lam_data Πty)
             (app : pi_app_data Πty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
      (b : comp_cat_tm (Γ & A) B),
      app Γ A B (lam Γ A B b) = b.

  (* η rule: λ (app f) ≡ f *)
  Definition pi_eta_law
             (Πty : pi_form)
             (lam : pi_lam_data Πty)
             (app : pi_app_data Πty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
      (f : comp_cat_tm Γ (Πty Γ A B)),
      lam Γ A B (app Γ A B f) = f.

  (* 4. Stability of Pi under substitution  *)
  (*    Π(A,B)[s] ≃ Π(A[s], B[s.A]) *)
  Definition pi_sub_iso
             (Πty : pi_form) : UU :=
    ∏ (Γ Δ : C) (s : Δ --> Γ)
      (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      z_iso (C := fiber_category _ _)
        ((Πty Γ A B) [[ s ]])
        (Πty Δ (A [[ s ]])
           (B [[ comp_cat_ext_subst _ _ s A ]])).

  (* 5. Stability of lambda under substitution *)
  Definition pi_sub_lam
             (Πty : pi_form)
             (lam : pi_lam_data Πty)
             (πiso : pi_sub_iso Πty) : UU :=
    ∏ (Γ Δ : C) (s : Δ --> Γ)
      (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
      (b : comp_cat_tm (Γ & A) B),
      let sA := comp_cat_ext_subst Γ Δ s A in
      let i  := πiso Γ Δ s A B in
      (lam Δ (A [[ s ]]) (B [[ sA ]]) (b [[ sA ]]tm)) ↑ (inv_from_z_iso i) = (lam Γ A B b) [[ s ]]tm.

  Definition comp_cat_pi : UU :=
    ∑ (Πty : pi_form),
    ∑ (lam : pi_lam_data Πty),
    ∑ (app : pi_app_data Πty),
      (pi_beta_law Πty lam app)
      × (pi_eta_law  Πty lam app)
      × (∑ (πiso : pi_sub_iso Πty),
        pi_sub_lam Πty lam πiso).

  Coercion pi_ty_from_pi (Pi: comp_cat_pi) : pi_form := pr1 Pi.

End Pi_For_Comp_Cat.


(** Id-types for comprehension categories  *)

(* TODO: This can also be similarly done  from Figure 3 of "From Semantics to Syntax" *)
(* This requires defining things like s.A.A[π]. *)


(** Unit types for comprehension categories  *)

Open Scope comp_cat.

Section Unit_For_Comp_Cat.

  Context (C : comp_cat).

  (* 1. Formation rule for unit: Γ ⊢ 1 type *)
  Definition unit_form : UU :=
    ∏ (Γ : C), comp_cat_ty Γ.

  (* 2. Introduction rule for unit: Γ ⊢ tt : 1 *)
  Definition unit_intro_data
             (One : unit_form) : UU :=
    ∏ (Γ : C), comp_cat_tm Γ (One Γ).

  (* 3. Elimination rule for unit: *)
  Definition unit_elim_data
             (One : unit_form)
             (tt : unit_intro_data One) : UU :=
    ∏ (Γ : C)
      (Cty : comp_cat_ty (Γ & (One Γ)))
      (c   : comp_cat_tm Γ (Cty [[ tt Γ ]])),
      comp_cat_tm (Γ & (One Γ)) Cty.

  (* 4. Computation rule: *)
  Definition unit_comp_law
             (One : unit_form)
             (tt : unit_intro_data One)
             (ind : unit_elim_data One tt) : UU :=
    ∏ (Γ : C)
      (Cty : comp_cat_ty (Γ & (One Γ)))
      (c   : comp_cat_tm Γ (Cty [[ tt Γ ]])),
      (ind Γ Cty c) [[ tt Γ ]]tm = c.

  (* 5. uniqueness *)
  Definition unit_uniqueness
    (One : unit_form) (tt : unit_intro_data One) : UU
    := ∏ (Γ : C) (u : comp_cat_tm Γ (One Γ)), u = tt Γ.

  (* Stability under reindexing *)
  Definition unit_sub_iso
             (One : unit_form) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ),
      z_iso (C := fiber_category _ _) ((One Δ) [[ s ]]) (One Γ).

  (* Stability of tt under reindexing *)
  Definition unit_sub_tt
             (One : unit_form)
             (tt : unit_intro_data One)
             (uiso : unit_sub_iso One) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ),
      (tt Δ [[ s ]]tm) · comp_cat_comp_mor ( ⌈uiso Γ Δ s⌉ ) = tt Γ.

  (* Helper lemma for the next definition to do some isomorphism bureaucracy*)
  Lemma unit_tt_ext_path
      (One : ∏ Γ : C, comp_cat_ty Γ)
      (tt  : ∏ Γ : C, comp_cat_tm Γ (One Γ))
      (uiso : unit_sub_iso One)
      (usubtt : unit_sub_tt One tt uiso)
      {Γ Δ : C} (s : Γ --> Δ)
    : s · tt Δ = tt Γ · (comp_cat_comp_mor ( ⌈uiso Γ Δ s⌉⁻¹)) · comp_cat_ext_subst Δ Γ s (One Δ).
  Proof.
    rewrite <- (comp_cat_ext_subst_term_commute s (One Δ) (tt Δ)).
    apply cancel_postcomposition.
    rewrite <- (usubtt _ _ s).
    rewrite assoc'.
    rewrite (comp_cat_comp_mor_z_iso_inv_after_z_iso (uiso Γ Δ s)).
    rewrite id_right.
    apply idpath.
  Qed.

  (* Stability of the eliminator under reindexing *)
  Definition unit_sub_elim
             (One : unit_form)
             (tt : unit_intro_data One)
             (ind : unit_elim_data One tt)
             (uiso : unit_sub_iso One)
             (usubtt : unit_sub_tt One tt uiso) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ)
      (C : comp_cat_ty (Δ & (One Δ)))
      (d   : comp_cat_tm Δ (C [[ tt Δ ]])),
      let s1 := comp_cat_comp_mor ( ⌈uiso Γ Δ s⌉⁻¹) · comp_cat_ext_subst Δ Γ s (One Δ) in
      let p := pathscomp0 (unit_tt_ext_path One tt uiso usubtt s) (! assoc (tt Γ) _ _) in
      let icompiso := comp_cat_subst_ty_eq_comp_iso C (tt Δ) (s) (s1) (tt Γ) (p) in
      (ind Δ C d) [[ s1 ]]tm = ind Γ (C [[ s1 ]]) (d [[ s ]]tm ↑ ⌈icompiso⌉).

  Definition comp_cat_unit : UU :=
    ∑ (One  : unit_form),
      ∑ (tt : unit_intro_data One),
      ∑ (ind  : unit_elim_data One tt),
      ∑ (comp :unit_comp_law One tt ind),
      ∑ (uniq : unit_uniqueness One tt),
      ∑ (uiso : unit_sub_iso One),
      ∑ (usubtt : unit_sub_tt One tt uiso),
      (unit_sub_elim One tt ind uiso usubtt).

  Coercion unit_ty_from_unit (Unit: comp_cat_unit) : unit_form := pr1 Unit.

End Unit_For_Comp_Cat.
