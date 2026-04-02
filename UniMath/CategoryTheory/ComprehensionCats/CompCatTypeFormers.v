

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

Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.

Require Import UniMath.CategoryTheory.ComprehensionCats.CompCats.

Local Open Scope comp_cat.
Local Open Scope cat.


(** * 1. Sigma-types for comprehension categories *)

(**
  The rules are from Figure 2 of
  "From Semantics to Syntax: A Type Theory for Comprehension Categories".
*)

Section Sigma_For_Comp_Cat.

  Context (C : comp_cat).

  (* Formation: Γ ⊢ A type,  Γ.A ⊢ B type  ⟹  Γ ⊢ Σ(A,B) type *)
  Definition sigma_form : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      comp_cat_ty Γ.

  (* Introduction: pairing map  pair : Γ.A.B → Γ.Σ(A,B) *)
  Definition sigma_pair_data (Σty : sigma_form) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      ((Γ & A) & B) --> (Γ & (Σty _ A B)).

  (* Law: πΣ ∘ pair = πB ∘ πA *)
  Definition sigma_pair_law
             (Σty : sigma_form)
             (pair : sigma_pair_data Σty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      pair Γ A B · π (Σty Γ A B) = π B · π A.

  (* Elimination: projΣ : Γ.Σ(A,B) → Γ.A.B *)
  Definition sigma_proj_data (Σty : sigma_form) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      (Γ & (Σty Γ A B)) --> ((Γ & A) & B).

  (* β-rule: proj ∘ pair = id *)
  Definition sigma_beta_law
             (Σty : sigma_form)
             (pair : sigma_pair_data Σty)
             (proj : sigma_proj_data Σty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      pair Γ A B · proj Γ A B = identity _.

  (* η-rule: pair ∘ proj = id *)
  Definition sigma_eta_law
             (Σty : sigma_form)
             (pair : sigma_pair_data Σty)
             (proj : sigma_proj_data Σty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      proj Γ A B · pair Γ A B = identity _.

  (* Stability under substitution: Σ(A,B)[s] ≃ Σ(A[s], B[s.A]) *)
  Definition sigma_sub_iso (Σty : sigma_form) : UU :=
    ∏ (Γ Δ : C) (s : Δ --> Γ)
      (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      z_iso (C := fiber_category _ _)
        ((Σty Γ A B) [[ s ]])
        (Σty Δ (A [[ s ]]) (B [[ comp_cat_ext_subst s A ]])).

  (* Stability of pairing under substitution *)
  Definition sigma_sub_pair_law
             (Σty : sigma_form)
             (pair : sigma_pair_data Σty)
             (σiso : sigma_sub_iso Σty) : UU :=
    ∏ (Γ Δ : C) (s : Δ --> Γ)
      (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      let sA  := comp_cat_ext_subst s A in
      let sAB := comp_cat_ext_subst sA B in
      let i   := σiso Γ Δ s A B in
      pair Δ (A [[ s ]]) (B [[ sA ]]) ·
        comp_cat_comp_mor (C:=C) (Γ:=Δ) (inv_from_z_iso i : _ -->[ identity _ ] _) ·
        comp_cat_ext_subst s (Σty Γ A B)
      = sAB · pair Γ A B.

  Definition comp_cat_sigma : UU :=
    ∑ (Σty    : sigma_form),
    ∑ (pair   : sigma_pair_data Σty),
    ∑ (pair_π : sigma_pair_law Σty pair),
    ∑ (proj   : sigma_proj_data Σty),
      sigma_beta_law Σty pair proj
      × sigma_eta_law Σty pair proj
      × ∑ (σiso : sigma_sub_iso Σty),
          sigma_sub_pair_law Σty pair σiso.

  Coercion sigma_ty_from_sigma (Σ : comp_cat_sigma) : sigma_form := pr1 Σ.

End Sigma_For_Comp_Cat.

(** Accessors for comp_cat_sigma *)

Definition comp_cat_sigma_pair
    {C : comp_cat} {Σ : comp_cat_sigma C}
    {Γ : C} (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : ((Γ & A) & B) --> Γ & ((pr1 Σ) Γ A B)
  := pr12 Σ Γ A B.

Definition comp_cat_sigma_pair_π
    {C : comp_cat} {Σ : comp_cat_sigma C}
    {Γ : C} (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : comp_cat_sigma_pair A B · π ((pr1 Σ) Γ A B) = π B · π A
  := pr122 Σ Γ A B.

Definition comp_cat_sigma_proj
    {C : comp_cat} {Σ : comp_cat_sigma C}
    {Γ : C} (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : Γ & ((pr1 Σ) Γ A B) --> (Γ & A) & B
  := pr1 (pr222 Σ) Γ A B.

Definition comp_cat_sigma_beta
    {C : comp_cat} {Σ : comp_cat_sigma C}
    {Γ : C} (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : comp_cat_sigma_pair A B · comp_cat_sigma_proj A B = identity _
  := pr12 (pr222 Σ) Γ A B.

Definition comp_cat_sigma_eta
    {C : comp_cat} {Σ : comp_cat_sigma C}
    {Γ : C} (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : comp_cat_sigma_proj A B · comp_cat_sigma_pair A B = identity _
  := pr122 (pr222 Σ) Γ A B.

Definition comp_cat_sigma_sub_iso
    {C : comp_cat} {Σ : comp_cat_sigma C}
    {Γ Δ : C} (s : Δ --> Γ) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : z_iso (C := fiber_category _ _)
      (((pr1 Σ) Γ A B) [[ s ]])
      ((pr1 Σ) Δ (A [[ s ]]) (B [[ comp_cat_ext_subst s A ]]))
  := pr1 (pr222 (pr222 Σ)) Γ Δ s A B.

Definition comp_cat_sigma_sub_pair
    {C : comp_cat} {Σ : comp_cat_sigma C}
    {Γ Δ : C} (s : Δ --> Γ) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : let sA  := comp_cat_ext_subst s A in
    let sAB := comp_cat_ext_subst sA B in
    let i   := comp_cat_sigma_sub_iso s A B in
    comp_cat_sigma_pair (A [[ s ]]) (B [[ sA ]]) ·
      comp_cat_comp_mor (C:=C) (Γ:=Δ) (inv_from_z_iso i : _ -->[ identity _ ] _) ·
      comp_cat_ext_subst s ((pr1 Σ) Γ A B)
    = sAB · comp_cat_sigma_pair A B
  := pr2 (pr222 (pr222 Σ)) Γ Δ s A B.

Definition comp_cat_sigma_pair_proj_iso
  { C : comp_cat} {Σ : comp_cat_sigma C} {Γ : C} (A : comp_cat_ty Γ)
  (B : comp_cat_ty (Γ & A))
  :  z_iso (Γ & ((pr1 Σ) _ A B)) ((Γ & A) & B).
Proof.
use make_z_iso.
    - apply comp_cat_sigma_proj.
    - apply comp_cat_sigma_pair.
    - use tpair.
      + apply comp_cat_sigma_eta.
      + apply comp_cat_sigma_beta.
Defined.

(** First projection, derived from the eliminator *)

Definition comp_cat_sigma_proj_1
    {C : comp_cat} {Σ : comp_cat_sigma C}
    {Γ : C} (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : C ⟦ Γ & ((pr1 Σ) Γ A B), Γ & A ⟧
  := comp_cat_sigma_proj A B · π B.

Lemma comp_cat_sigma_proj_1_law
    {C : comp_cat} {Σ : comp_cat_sigma C}
    {Γ : C} (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : comp_cat_sigma_proj_1 A B · π A = π ((pr1 Σ) Γ A B).
Proof.
  unfold comp_cat_sigma_proj_1.
  rewrite assoc'.
  rewrite <- (@comp_cat_sigma_pair_π _ Σ).
  rewrite assoc.
  rewrite comp_cat_sigma_eta.
  apply id_left.
Qed.

Lemma comp_cat_sigma_proj_law
  {C : comp_cat} {Σ : comp_cat_sigma C}
   {Γ : C} (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : comp_cat_sigma_proj A B · π _ · π A = π ((pr1 Σ) Γ A B).
Proof.
  apply comp_cat_sigma_proj_1_law.
Qed.

(** * 2. Pi-types for comprehension categories *)

(*
  The rules are from Figure 1 of
  "From Semantics to Syntax: A Type Theory for Comprehension Categories".
*)

Section Pi_For_Comp_Cat.

  Context (C : comp_cat).

  (* Formation: Γ ⊢ A type,  Γ.A ⊢ B type  ⟹  Γ ⊢ Π(A,B) type *)
  Definition pi_form : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      comp_cat_ty Γ.

  (* Introduction: lambda abstraction  Γ.A ⊢ b : B  ⟹  Γ ⊢ λb : Π(A,B) *)
  Definition pi_lam_data (Πty : pi_form) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      comp_cat_tm B -> comp_cat_tm (Πty Γ A B).

  (* Elimination: application  Γ ⊢ f : Π(A,B)  ⟹  Γ.A ⊢ app(f) : B *)
  Definition pi_app_data (Πty : pi_form) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      comp_cat_tm (Πty Γ A B) -> comp_cat_tm B.

  (* β-rule: app(λb) = b *)
  Definition pi_beta_law
             (Πty : pi_form)
             (lam : pi_lam_data Πty)
             (app : pi_app_data Πty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
      (b : comp_cat_tm B),
      app Γ A B (lam Γ A B b) = b.

  (* η-rule: λ(app f) = f *)
  Definition pi_eta_law
             (Πty : pi_form)
             (lam : pi_lam_data Πty)
             (app : pi_app_data Πty) : UU :=
    ∏ (Γ : C) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
      (f : comp_cat_tm (Πty Γ A B)),
      lam Γ A B (app Γ A B f) = f.

  (* Stability under substitution: Π(A,B)[s] ≃ Π(A[s], B[s.A]) *)
  Definition pi_sub_iso (Πty : pi_form) : UU :=
    ∏ (Γ Δ : C) (s : Δ --> Γ)
      (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)),
      z_iso (C := fiber_category _ _)
        ((Πty Γ A B) [[ s ]])
        (Πty Δ (A [[ s ]]) (B [[ comp_cat_ext_subst s A ]])).

  (* Stability of lambda under substitution *)
  Definition pi_sub_lam
             (Πty : pi_form)
             (lam : pi_lam_data Πty)
             (πiso : pi_sub_iso Πty) : UU :=
    ∏ (Γ Δ : C) (s : Δ --> Γ)
      (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
      (b : comp_cat_tm B),
      let sA := comp_cat_ext_subst s A in
      let i  := πiso Γ Δ s A B in
      lam Δ (A [[ s ]]) (B [[ sA ]]) (b [[ sA ]]tm) ↑ inv_from_z_iso i
      = (lam Γ A B b) [[ s ]]tm.

  Definition comp_cat_pi : UU :=
    ∑ (Πty  : pi_form),
    ∑ (lam  : pi_lam_data Πty),
    ∑ (app  : pi_app_data Πty),
      pi_beta_law Πty lam app
      × pi_eta_law Πty lam app
      × ∑ (πiso : pi_sub_iso Πty),
          pi_sub_lam Πty lam πiso.

  Coercion pi_ty_from_pi (Π : comp_cat_pi) : pi_form := pr1 Π.

End Pi_For_Comp_Cat.

(** Accessors for comp_cat_pi *)

Definition comp_cat_pi_lam
    {C : comp_cat} {Π : comp_cat_pi C}
    {Γ : C} {A : comp_cat_ty Γ} {B : comp_cat_ty (Γ & A)}
    (b : comp_cat_tm B)
  : comp_cat_tm ((pr1 Π) Γ A B)
  := pr12 Π Γ A B b.

Definition comp_cat_pi_app
    {C : comp_cat} {Π : comp_cat_pi C}
    {Γ : C} {A : comp_cat_ty Γ} {B : comp_cat_ty (Γ & A)}
    (f : comp_cat_tm ((pr1  Π) Γ A B))
  : comp_cat_tm B
  := pr122 Π Γ A B f.

Definition comp_cat_pi_beta
    {C : comp_cat} {Π : comp_cat_pi C}
    {Γ : C} {A : comp_cat_ty Γ} {B : comp_cat_ty (Γ & A)}
    (b : comp_cat_tm B)
  : comp_cat_pi_app (comp_cat_pi_lam b) = b
  := pr1 (pr222 Π) Γ A B b.

Definition comp_cat_pi_eta
    {C : comp_cat} {Π : comp_cat_pi C}
    {Γ : C} {A : comp_cat_ty Γ} {B : comp_cat_ty (Γ & A)}
    (f : comp_cat_tm ((pr1 Π) Γ A B))
  : comp_cat_pi_lam (comp_cat_pi_app f) = f
  := pr12 (pr222 Π) Γ A B f.

Definition comp_cat_pi_sub_iso
    {C : comp_cat} {Π : comp_cat_pi C}
    {Γ Δ : C} (s : Δ --> Γ) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : z_iso (C := fiber_category _ _)
      (((pr1 Π) Γ A B) [[ s ]])
      ((pr1 Π) Δ (A [[ s ]]) (B [[ comp_cat_ext_subst s A ]]))
  := pr1 (pr22 (pr222 Π)) Γ Δ s A B.

Definition comp_cat_pi_sub_lam
    {C : comp_cat} {Π : comp_cat_pi C}
    {Γ Δ : C} (s : Δ --> Γ) (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
    (b : comp_cat_tm B)
  : let sA := comp_cat_ext_subst s A in
    let i  := comp_cat_pi_sub_iso s A B in
    comp_cat_pi_lam (b [[ sA ]]tm) ↑ inv_from_z_iso i
    = (comp_cat_pi_lam b) [[ s ]]tm
  := pr2 (pr22 (pr222 Π)) Γ Δ s A B b.


(** * 3. TODO: Id Types *)

(* Can be done similarly from Figure 3 of "From Semantics to Syntax". *)


(** * 4. Unit types for comprehension categories *)

Section Unit_For_Comp_Cat.

  Context (C : comp_cat).

  (* Formation: Γ ⊢ 1 type *)
  Definition unit_form : UU :=
    ∏ (Γ : C), comp_cat_ty Γ.

  (* Introduction: Γ ⊢ tt : 1 *)
  Definition unit_intro_data (One : unit_form) : UU :=
    ∏ (Γ : C), comp_cat_tm (One Γ).

  (* Elimination *)
  Definition unit_elim_data
             (One : unit_form)
             (tt  : unit_intro_data One) : UU :=
    ∏ (Γ : C)
      (Cty : comp_cat_ty (Γ & (One Γ)))
      (c   : comp_cat_tm (Cty [[ tt Γ ]])),
      comp_cat_tm Cty.

  (* Computation rule *)
  Definition unit_comp_law
             (One : unit_form)
             (tt  : unit_intro_data One)
             (ind : unit_elim_data One tt) : UU :=
    ∏ (Γ : C)
      (Cty : comp_cat_ty (Γ & (One Γ)))
      (c   : comp_cat_tm (Cty [[ tt Γ ]])),
      ind Γ Cty c [[ tt Γ ]]tm = c.

  (* Uniqueness of the introduction term *)
  Definition unit_uniqueness
             (One : unit_form)
             (tt  : unit_intro_data One) : UU :=
    ∏ (Γ : C) (u : comp_cat_tm (One Γ)), u = tt Γ.

  (* Stability under reindexing: 1[s] ≃ 1 *)
  Definition unit_sub_iso (One : unit_form) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ),
      z_iso (C := fiber_category _ _) ((One Δ) [[ s ]]) (One Γ).

  (* Stability of tt under reindexing *)
  Definition unit_sub_tt
             (One   : unit_form)
             (tt    : unit_intro_data One)
             (uiso  : unit_sub_iso One) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ),
      tt Δ [[ s ]]tm · comp_cat_comp_mor (⌈uiso Γ Δ s⌉) = tt Γ.

  (* Helper: tt commutes with extended substitution *)
  Lemma unit_tt_ext_path
      (One    : unit_form)
      (tt     : unit_intro_data One)
      (uiso   : unit_sub_iso One)
      (usubtt : unit_sub_tt One tt uiso)
      {Γ Δ : C} (s : Γ --> Δ)
    : s · tt Δ =
      tt Γ · comp_cat_comp_mor (⌈uiso Γ Δ s⌉⁻¹) · comp_cat_ext_subst s (One Δ).
  Proof.
    rewrite <- (comp_cat_ext_subst_term_commute s (One Δ) (tt Δ)).
    apply cancel_postcomposition.
    rewrite <- (usubtt _ _ s).
    rewrite assoc'.
    rewrite (comp_cat_comp_mor_z_iso_inv_after_z_iso (uiso Γ Δ s)).
    rewrite id_right.
    apply idpath.
  Defined.

  (* Stability of the eliminator under reindexing *)
  Definition unit_sub_elim
             (One    : unit_form)
             (tt     : unit_intro_data One)
             (ind    : unit_elim_data One tt)
             (uiso   : unit_sub_iso One)
             (usubtt : unit_sub_tt One tt uiso) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ)
      (Cty : comp_cat_ty (Δ & (One Δ)))
      (d   : comp_cat_tm (Cty [[ tt Δ ]])),
      let s1       := comp_cat_comp_mor (⌈uiso Γ Δ s⌉⁻¹) · comp_cat_ext_subst s (One Δ) in
      let p        := pathscomp0 (unit_tt_ext_path One tt uiso usubtt s) (! assoc (tt Γ) _ _) in
      let icompiso := comp_cat_subst_ty_eq_comp_iso Cty p in
      ind Δ Cty d [[ s1 ]]tm = ind Γ (Cty [[ s1 ]]) (d [[ s ]]tm ↑ ⌈icompiso⌉).

  Definition comp_cat_unit : UU :=
    ∑ (One    : unit_form),
    ∑ (tt     : unit_intro_data One),
    ∑ (ind    : unit_elim_data One tt),
    ∑ (comp   : unit_comp_law One tt ind),
    ∑ (uniq   : unit_uniqueness One tt),
    ∑ (uiso   : unit_sub_iso One),
    ∑ (usubtt : unit_sub_tt One tt uiso),
      unit_sub_elim One tt ind uiso usubtt.

  Coercion unit_ty_from_unit (Unit : comp_cat_unit) : unit_form := pr1 Unit.

End Unit_For_Comp_Cat.

(** Accessors for comp_cat_unit *)

Definition comp_cat_unit_tt
    {C : comp_cat} {Unit : comp_cat_unit C}
    (Γ : C)
  : comp_cat_tm ((pr1 Unit) Γ)
  := pr12 Unit Γ.

Definition comp_cat_unit_ind
    {C : comp_cat} {Unit : comp_cat_unit C}
    {Γ : C} (Cty : comp_cat_ty (Γ & ((pr1 Unit) Γ)))
    (c : comp_cat_tm (Cty [[ comp_cat_unit_tt Γ ]]))
  : comp_cat_tm Cty
  := pr122 Unit Γ Cty c.

Definition comp_cat_unit_comp
    {C : comp_cat} {Unit : comp_cat_unit C}
    {Γ : C} (Cty : comp_cat_ty (Γ & ((pr1 Unit) Γ)))
    (c : comp_cat_tm (Cty [[ comp_cat_unit_tt Γ ]]))
  : comp_cat_unit_ind Cty c [[ comp_cat_unit_tt Γ ]]tm = c
  := pr1 (pr222 Unit) Γ Cty c.

Definition comp_cat_unit_unique
    {C : comp_cat} {Unit : comp_cat_unit C}
    {Γ : C} (u : comp_cat_tm ((pr1 Unit) Γ))
  : u = comp_cat_unit_tt Γ
  := pr12 (pr222 Unit) Γ u.

Definition comp_cat_unit_sub_iso
    {C : comp_cat} {Unit : comp_cat_unit C}
    {Γ Δ : C} (s : Γ --> Δ)
  : z_iso (C := fiber_category _ _) (((pr1 Unit) Δ) [[ s ]]) ((pr1 Unit) Γ)
  := pr1 (pr22 (pr222 Unit)) Γ Δ s.

Definition comp_cat_unit_sub_tt
    {C : comp_cat} {Unit : comp_cat_unit C}
    {Γ Δ : C} (s : Γ --> Δ)
  : comp_cat_unit_tt Δ [[ s ]]tm · comp_cat_comp_mor (⌈comp_cat_unit_sub_iso s⌉) =
    comp_cat_unit_tt Γ
  := pr1 (pr2 (pr22 (pr222 Unit))) Γ Δ s.

Lemma comp_cat_unit_tt_ext_path
    {C : comp_cat} {Unit : comp_cat_unit C}
    {Γ Δ : C} (s : Γ --> Δ)
  : s · comp_cat_unit_tt Δ =
    comp_cat_unit_tt Γ
    · comp_cat_comp_mor (⌈comp_cat_unit_sub_iso (Unit := Unit) s⌉⁻¹)
    · comp_cat_ext_subst s ((pr1 Unit) Δ).
Proof.
  exact (unit_tt_ext_path C Unit (pr12 Unit)
    (pr1 (pr22 (pr222 Unit)))
    (pr1 (pr2 (pr22 (pr222 Unit)))) s).
Defined.

Definition comp_cat_unit_sub_elim
    {C : comp_cat} {Unit : comp_cat_unit C}
    {Γ Δ : C} (s : Γ --> Δ)
    (Cty : comp_cat_ty (Δ & ((pr1 Unit) Δ)))
    (d : comp_cat_tm (Cty [[ comp_cat_unit_tt Δ ]]))
  : let s1       := comp_cat_comp_mor (⌈comp_cat_unit_sub_iso s⌉⁻¹) ·
                    comp_cat_ext_subst s ((pr1 Unit) Δ) in
    let p        := pathscomp0 (comp_cat_unit_tt_ext_path s)
                      (! assoc (comp_cat_unit_tt Γ) _ _) in
    let icompiso := comp_cat_subst_ty_eq_comp_iso Cty p in
    comp_cat_unit_ind Cty d [[ s1 ]]tm =
      comp_cat_unit_ind (Cty [[ s1 ]]) (d [[ s ]]tm ↑ ⌈icompiso⌉)
  := pr2 (pr2 (pr22 (pr222 Unit))) Γ Δ s Cty d.
