

(** Type Formers in Comprehension Categories. This file contains sigma, pi and unit types.

  This developement follows "From Semantics to Syntax: A Type Theory for Comprehension
  Categories" by Najmaei, Van der Weide, Ahrens, and North

  Identity types can also be added similarly from Figure 3 of "From Semantics to Syntax" but
  this has not been done yet.

  Contents

  1. Sigma Types
  2. Pi Types
  3. Unit Types

 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.

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
      pair Δ (A [[ s ]]) (B [[ (comp_cat_ext_subst s A) ]]) ·
        comp_cat_comp_mor (inv_from_z_iso (σiso _ _ _ _ _)) ·
        comp_cat_ext_subst s (Σty Γ A B)
      = (comp_cat_ext_subst (comp_cat_ext_subst _ _) B) · pair Γ A B .

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
  : comp_cat_sigma_pair (A [[ s ]]) (B [[ (comp_cat_ext_subst s A ) ]]) ·
      comp_cat_comp_mor (inv_from_z_iso (comp_cat_sigma_sub_iso _ _ _ )) ·
      comp_cat_ext_subst s ((pr1 Σ) Γ A B)
    = comp_cat_ext_subst (comp_cat_ext_subst _ _) B
        · comp_cat_sigma_pair A B
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

(** Useful isomorphisms for Sigma  *)


Definition comp_cat_sigma_iso_2
  {C : comp_cat} {Sig : comp_cat_sigma C}
  {Γ : C} {A : comp_cat_ty Γ} {B B' : comp_cat_ty (Γ & A)}
  (i : z_iso ((Γ & A) & B) ((Γ & A) & B'))
  : z_iso (Γ & (pr1 Sig) Γ A B) (Γ & (pr1 Sig) Γ A B')
  := z_iso_comp (comp_cat_sigma_pair_proj_iso A B)
       (z_iso_comp i
          (z_iso_inv (comp_cat_sigma_pair_proj_iso A B'))).

Definition comp_cat_sigma_iso_1
  {C : comp_cat} {Sig : comp_cat_sigma C}
  {Γ : C} {A A' : comp_cat_ty Γ} {B : comp_cat_ty (Γ & A)}
  (i : z_iso (Γ & A) (Γ & A'))
  : z_iso (Γ & (pr1 Sig) Γ A B)
      (Γ & (pr1 Sig) Γ A' (B [[ inv_from_z_iso i ]]))
  := z_iso_comp (comp_cat_sigma_pair_proj_iso A B)
       (z_iso_comp
          (z_iso_inv (comp_cat_ext_subst_z_iso (z_iso_inv i) B))
          (z_iso_inv (comp_cat_sigma_pair_proj_iso A' _))).

Lemma comp_cat_sigma_iso_2_id
  {C : comp_cat} {Sig : comp_cat_sigma C} {Γ : C}
  (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A))
  : comp_cat_sigma_iso_2 (Sig:=Sig) (identity_z_iso ((Γ & A) & B))
    = identity_z_iso (Γ & (pr1 Sig) Γ A B).
Proof.
  use z_iso_eq.
  cbn.
  rewrite id_left.
  apply comp_cat_sigma_eta.
Qed.

Lemma comp_cat_sigma_iso_2_comp
  {C : comp_cat} {Sig : comp_cat_sigma C} {Γ : C}
  {A : comp_cat_ty Γ} {B B' B'' : comp_cat_ty (Γ & A)}
  (i : z_iso ((Γ & A) & B) ((Γ & A) & B'))
  (i' : z_iso ((Γ & A) & B') ((Γ & A) & B''))
  : comp_cat_sigma_iso_2 (Sig:=Sig) (z_iso_comp i i')
    = z_iso_comp (comp_cat_sigma_iso_2 i) (comp_cat_sigma_iso_2 i').
Proof.
  use z_iso_eq.
  cbn.
  rewrite !assoc'.
  do 2 apply maponpaths.
  refine (!_).
  rewrite assoc.
  rewrite comp_cat_sigma_beta.
  apply id_left.
Qed.

Lemma comp_cat_sigma_iso_2_comp'
  {C : comp_cat} {Sig : comp_cat_sigma C} {Γ : C}
  {A : comp_cat_ty Γ} {B B' B'' : comp_cat_ty (Γ & A)}
  (i : z_iso ((Γ & A) & B) ((Γ & A) & B'))
  (i' : z_iso ((Γ & A) & B') ((Γ & A) & B''))
  : morphism_from_z_iso _ _ (comp_cat_sigma_iso_2 (Sig:=Sig) (z_iso_comp i i'))
    = (comp_cat_sigma_iso_2 i) · (comp_cat_sigma_iso_2 i').
Proof.
  rewrite comp_cat_sigma_iso_2_comp.
  apply idpath.
Qed.

Lemma comp_cat_sigma_iso_2_proj
  {C : comp_cat} {Sig : comp_cat_sigma C}
  {Γ : C} {A : comp_cat_ty Γ} {B B' : comp_cat_ty (Γ & A)}
  (i : z_iso ((Γ & A) & B) ((Γ & A) & B'))
  (p : i · π B' = π B)
  : comp_cat_sigma_iso_2 (Sig:=Sig) i · comp_cat_sigma_proj_1 A B'
    = comp_cat_sigma_proj_1 A B.
Proof.
  unfold comp_cat_sigma_proj_1.
  cbn.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  { apply maponpaths.
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2. apply comp_cat_sigma_beta. }
    apply id_left. }
  exact p.
Qed.

Lemma comp_cat_sigma_iso_1_proj
  {C : comp_cat} {Sig : comp_cat_sigma C}
  {Γ : C} {A A' : comp_cat_ty Γ} {B : comp_cat_ty (Γ & A)}
  (i : z_iso (Γ & A) (Γ & A'))
  : comp_cat_sigma_iso_1 (Sig:=Sig) i
      · comp_cat_sigma_proj_1 A' (B [[ inv_from_z_iso i ]])
    = comp_cat_sigma_proj_1 A B · i.
Proof.
  unfold comp_cat_sigma_proj_1.
  cbn.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  { apply maponpaths.
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2. apply comp_cat_sigma_beta. }
    apply id_left. }
  exact (PullbackArrow_PullbackPr2 (comp_cat_pullback _ _) _ _ _ _).
Qed.

Definition comp_cat_sigma_assoc
  {C : comp_cat} {Σ : comp_cat_sigma C} {Γ : C}
  (A : comp_cat_ty Γ)
  (B : comp_cat_ty (Γ & A))
  (D : comp_cat_ty ((Γ & A) & B))
  : z_iso
      (Γ & ((pr1 Σ) Γ ((pr1 Σ) Γ A B) (D [[ comp_cat_sigma_proj A B ]])))
      (Γ & ((pr1 Σ) Γ A ((pr1 Σ) (Γ & A) B D))).
Proof.
  refine (z_iso_comp (comp_cat_sigma_pair_proj_iso _ _) _).
  refine (z_iso_comp (comp_cat_ext_subst_z_iso
                        (comp_cat_sigma_pair_proj_iso A B) D) _).
  refine (z_iso_comp (z_iso_inv (comp_cat_sigma_pair_proj_iso B D)) _).
  exact (z_iso_inv (comp_cat_sigma_pair_proj_iso A _)).
Defined.

Lemma comp_cat_sigma_assoc_proj_1
  {C : comp_cat} {Σ : comp_cat_sigma C} {Γ : C}
  (A : comp_cat_ty Γ) (B : comp_cat_ty (Γ & A)) (D : comp_cat_ty ((Γ & A) & B))
  : comp_cat_sigma_assoc A B D
      · comp_cat_sigma_proj_1 A ((pr1 Σ) (Γ & A) B D)
    = comp_cat_sigma_proj_1 ((pr1 Σ) Γ A B) (D [[ comp_cat_sigma_proj A B ]])
        · comp_cat_sigma_proj_1 A B.
Proof.
  unfold comp_cat_sigma_assoc, comp_cat_sigma_proj_1.
  cbn.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  { do 2 apply maponpaths.
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2. apply comp_cat_sigma_beta. }
    apply id_left. }
  rewrite comp_cat_sigma_pair_π.
  rewrite assoc.
  rewrite comp_cat_ext_subst_commute.
  apply assoc'.
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
      lam Δ (A [[ s ]]) (B [[ (comp_cat_ext_subst s A ) ]]) (b [[ (comp_cat_ext_subst s A ) ]]tm) ↑ inv_from_z_iso (πiso _ _ _ _ _)
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
  (sA := comp_cat_ext_subst s A)
  (i  := comp_cat_pi_sub_iso s A B)
  : comp_cat_pi_lam (b [[ sA ]]tm) ↑ inv_from_z_iso i
    = (comp_cat_pi_lam b) [[ s ]]tm
  := pr2 (pr22 (pr222 Π)) Γ Δ s A B b.


(** * 3. Unit types for comprehension categories *)

Section Unit_For_Comp_Cat.

  Context (C : comp_cat).

  (* Formation: Γ ⊢ 1 type *)
  Definition unit_form : UU :=
    ∏ (Γ : C), comp_cat_ty Γ.

  (* Introduction: Γ ⊢ tt : 1 *)
  Definition unit_intro_data (One : unit_form) : UU :=
    ∏ (Γ : C), comp_cat_tm (One Γ).

  (* Uniqueness of tt *)
  Definition unit_uniqueness
    (One : unit_form)
    (tt  : unit_intro_data One) : UU :=
    ∏ (Γ : C) (u : comp_cat_tm (One Γ)), u = tt Γ.

  (* Stability under reindexing: 1[s] ≃ 1 *)
  Definition unit_sub_iso (One : unit_form) : UU :=
    ∏ (Γ Δ : C) (s : Γ --> Δ),
      z_iso (C := fiber_category _ _) ((One Δ) [[ s ]]) (One Γ).

  Definition comp_cat_unit : UU :=
    ∑ (One    : unit_form),
      ∑ (tt     : unit_intro_data One),
      ∑ (uniq   : unit_uniqueness One tt),
      unit_sub_iso One.

  Coercion unit_ty_from_unit (Unit : comp_cat_unit) : unit_form := pr1 Unit.

End Unit_For_Comp_Cat.

(** Accessors for comp_cat_unit *)

Definition comp_cat_unit_tt
  {C : comp_cat} (Unit : comp_cat_unit C)
  (Γ : C)
  : comp_cat_tm ((pr1 Unit) Γ)
  := pr12 Unit Γ.

Definition comp_cat_unit_unique
  {C : comp_cat} {Unit : comp_cat_unit C}
  {Γ : C} (u : comp_cat_tm ((pr1 Unit) Γ))
  : u = comp_cat_unit_tt _ Γ
  := pr122 Unit Γ u.

Definition comp_cat_unit_sub_iso
  {C : comp_cat} (Unit : comp_cat_unit C)
  {Γ Δ : C} (s : Γ --> Δ)
  : z_iso (C := fiber_category _ _) (((pr1 Unit) Δ) [[ s ]]) ((pr1 Unit) Γ)
  := pr222 Unit Γ Δ s.

(** deriving elimination, computation and stabilities under substitution  *)

Definition comp_cat_tt_is_iso
  {C : comp_cat} {Unit : comp_cat_unit C}
  (Γ : C):
  π _ · comp_cat_unit_tt Unit Γ = identity _.
Proof.
  use comp_cat_mor_into_ext_eq.
  - abstract (rewrite assoc';
              etrans; [ apply maponpaths; apply (pr2 (comp_cat_unit_tt _ Γ)) | ];
              rewrite id_right, id_left;
              apply idpath).
  - use (iscontr_tm_of_iso _ (z_iso_inv (comp_cat_unit_sub_iso _ _))).
    use tpair.
    + exact (comp_cat_unit_tt _ (Γ & (pr1 Unit) Γ)).
    + intro u. exact (comp_cat_unit_unique u).
Qed.

Definition comp_cat_unit_unique_mor
  {C : comp_cat} {Unit : comp_cat_unit C}
  {Γ : C} (u : Γ --> Γ & _)
  ( p : u · π _ = identity _)
  : u = comp_cat_unit_tt Unit Γ
  := maponpaths pr1 (comp_cat_unit_unique (u ,, p)).

Definition comp_cat_unit_ind
  {C : comp_cat} {Unit : comp_cat_unit C}
  {Γ : C} (Cty : comp_cat_ty (Γ & ((pr1 Unit) Γ)))
  (c : comp_cat_tm (Cty [[ comp_cat_unit_tt _ Γ ]]))
  : comp_cat_tm Cty.
Proof.
  use make_comp_cat_tm.
  - exact (π _ · c · comp_cat_ext_subst (comp_cat_unit_tt _ _) Cty).
  - abstract (rewrite assoc';
              rewrite comp_cat_ext_subst_commute;
              rewrite assoc;
              rewrite assoc4;
              etrans; [ apply maponpaths_2; apply maponpaths; apply (pr2 c) | ];
              rewrite id_right;
              apply comp_cat_tt_is_iso).
Defined.

Definition comp_cat_unit_comp
  {C : comp_cat} {Unit : comp_cat_unit C}
  {Γ : C} (Cty : comp_cat_ty (Γ & ((pr1 Unit) Γ)))
  (c : comp_cat_tm (Cty [[ comp_cat_unit_tt _ Γ ]]))
  : comp_cat_unit_ind Cty c [[ comp_cat_unit_tt _ Γ ]]tm = c.
Proof.
  use comp_cat_tm_eq.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback _ _))).
  - unfold comp_cat_unit_ind.
    simpl.
    rewrite !assoc.
    etrans.
    2: { do 2  apply maponpaths_2.
         refine (!_).
         apply (pr2 (comp_cat_unit_tt _ Γ)). }
    rewrite id_left.
    apply idpath.
  - apply (pr2 c).
Qed.

Definition comp_cat_unit_sub_tt
  {C : comp_cat} (Unit : comp_cat_unit C)
  {Γ Δ : C} (s : Γ --> Δ)
  : comp_cat_unit_tt Unit Δ [[ s ]]tm · comp_cat_comp_mor (⌈comp_cat_unit_sub_iso _ s⌉) =
      comp_cat_unit_tt _ Γ.
Proof.
  refine (comp_cat_unit_unique_mor _ _).
  rewrite assoc'.
  rewrite comp_cat_comp_mor_law.
  exact (pr2 ((comp_cat_unit_tt _ Δ) [[s]]tm)).
Qed.

Lemma comp_cat_unit_tt_ext_path
  {C : comp_cat} {Unit : comp_cat_unit C}
  {Γ Δ : C} (s : Γ --> Δ)
  (ttΔ := comp_cat_unit_tt Unit Δ)
  (usubtt := comp_cat_unit_sub_tt Unit s)
  (uiso := comp_cat_unit_sub_iso Unit s)
  : s · comp_cat_unit_tt _ Δ =
      comp_cat_unit_tt _ Γ
        · comp_cat_comp_mor (⌈comp_cat_unit_sub_iso Unit s⌉⁻¹)
        · comp_cat_ext_subst s ((pr1 Unit) Δ).
Proof.
  etrans. { refine (!_). apply (comp_cat_ext_subst_term_commute s _ (ttΔ)). }
  apply cancel_postcomposition.
  rewrite <- usubtt.
  rewrite assoc'.
  etrans. 2 : { refine (!_).
                apply maponpaths. apply (comp_cat_comp_mor_z_iso_inv_after_z_iso uiso). }
        rewrite id_right.
  apply idpath.
Qed.

Definition comp_cat_unit_sub_elim
  {C : comp_cat} {Unit : comp_cat_unit C}
  {Γ Δ : C} (s : Γ --> Δ)
  (Cty : comp_cat_ty (Δ & ((pr1 Unit) Δ)))
  (d : comp_cat_tm (Cty [[ comp_cat_unit_tt _ Δ ]]))
  (s1 := comp_cat_comp_mor (⌈comp_cat_unit_sub_iso _ s⌉⁻¹)
           · comp_cat_ext_subst s ((pr1 Unit) Δ))
  (p := pathscomp0 (comp_cat_unit_tt_ext_path s)
          (! assoc (comp_cat_unit_tt _ Γ) _ _))
  (icompiso := comp_cat_subst_ty_eq_comp_iso Cty p)
  : comp_cat_unit_ind Cty d [[ s1 ]]tm =
      comp_cat_unit_ind (Cty [[ s1 ]]) (d [[ s ]]tm ↑ ⌈icompiso⌉).
Proof.
  unfold comp_cat_unit_ind.
  use comp_cat_tm_eq.
  refine (!_).
  use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback _ _))).
  - cbn -[ "_ [[ _ ]]tm" comp_cat_ext_subst comp_cat_subst_ty_eq_comp_iso].
    unfold s1.
    set (q := comp_cat_comp_mor (⌈comp_cat_unit_sub_iso _ s⌉⁻¹)
                · comp_cat_ext_subst s (pr1 Unit Δ)).
    change (comprehension_functor_mor q
              (mor_disp_of_cartesian_lift _ _ (cleaving_of_types C _ _ q Cty)))
      with (comp_cat_ext_subst q Cty).
    rewrite assoc'.
    rewrite <- (comp_cat_ext_subst_comp' Cty (comp_cat_unit_tt _ Γ) q).
    unfold icompiso.
    assert (h : q · π (pr1 Unit Δ) = π (pr1 Unit Γ) · s).
    { unfold q.
      rewrite assoc'.
      etrans.
      { apply maponpaths. apply comp_cat_ext_subst_commute. }
      refine (assoc _ _ _ @ _).
      apply maponpaths_2.
      apply comp_cat_comp_mor_law. }
    rewrite !assoc.
    etrans.
    2: { do 2 apply maponpaths_2. refine (!_). exact h. }
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ ! comp_cat_extend_subst_subst s (comp_cat_unit_tt _ Δ) d).
    rewrite !assoc.
    rewrite assoc4.
    rewrite <- comp_cat_comp_mor_comp'.
    rewrite comp_cat_subst_ty_eq_comp_iso_comp.
    rewrite comp_cat_comp_mor_comp'.
    rewrite assoc.
    refine (! comp_cat_extend_subst_eq p
              (d [[s]]tm ↑ ⌈comp_cat_subst_ty_comp_iso Cty (comp_cat_unit_tt _ Δ) s⌉)).
  - exact (pr2 (make_comp_cat_tm (π (pr1 Unit Γ) · d [[s ]]tm ↑ ⌈ icompiso ⌉ · comp_cat_ext_subst (comp_cat_unit_tt _ Γ) (Cty [[s1]]))
                  (comp_cat_unit_ind_subproof C Unit Γ (Cty [[s1]]) (d [[s ]]tm ↑ ⌈ icompiso ⌉)))).
Qed.
