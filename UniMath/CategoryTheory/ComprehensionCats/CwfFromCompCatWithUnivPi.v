(** Theorems about the CwF constructed from a comprehension category with a universe
    closed under Σ- and unit types and Π-types.
    Let UnivMod(U) be the constructed CwF.  This file is part 3 of 3.
    We show that UnivMod(U) has Π-types if the starting universe U is closed under Π-types.

    Contents:

    1. Preservation of Π
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Core.Setcategories.

Require Import UniMath.CategoryTheory.DisplayedCats.ComprehensionC.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.

Require Import UniMath.CategoryTheory.ComprehensionCats.CompCats.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatTypeFormers.
Require Import UniMath.CategoryTheory.ComprehensionCats.CompCatUniverse.
Require Import UniMath.CategoryTheory.ComprehensionCats.CwfFromCompCatWithUniv.
Require Import UniMath.CategoryTheory.CategoriesWithFamilies.CatsWithFams.
Require Import UniMath.CategoryTheory.CategoriesWithFamilies.CatsWithFamsTypeFormersWithSections.
Require Import UniMath.CategoryTheory.ComprehensionCats.CwfFromCompCatWithUnivSigma.

Local Open Scope cat.
Local Open Scope comp_cat.


(** * 1. Preservation of Π *)

Section PiPreservation.

  Context (C : comp_cat_with_universe)
    (Sigma : comp_cat_sigma C)
    (SigmaU : comp_cat_universe_closed_sigma C Sigma)
    (Unit : comp_cat_unit C)
    (UnitU : comp_cat_universe_closed_unit C Unit)
    (Pi : comp_cat_pi C)
    (PiU : comp_cat_universe_closed_pi C Pi).

  Definition cwf_pi_form_from_comp_cat_with_u
    : pi_form (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU).
  Proof.
    intros Γ A B.
    refine (comp_cat_pi_code _ _ PiU A _).
    refine (comp_cat_pb_term_univ
              (comp_cat_pb_term_univ B
                 (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso _ _ _ _ _ ⌉⁻¹)))
              _).
    refine (comp_cat_sigma_pair _ _ ).
  Defined.

  Definition cwf_pi_lam_from_comp_cat_with_u
    : pi_lam (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU) cwf_pi_form_from_comp_cat_with_u.
  Proof.
    intros Γ a b t.
    refine (comp_cat_pi_lam _
              ↑ ⌈ comp_cat_pi_el_iso _ _ _ a _⌉⁻¹).
    refine (_ ↑ ⌈ comp_cat_el_iso (comp_cat_sigma_pair _ _) _ ⌉).
    refine (_ [[ comp_cat_sigma_pair _ _ ]]tm).
    refine (_ ↑ ⌈ comp_cat_el_iso _ _ ⌉).
    refine (t [[ comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso _ _ _ _ _ ⌉⁻¹) ]]tm).
  Defined.

  Definition cwf_pi_app_from_comp_cat_with_u
    : pi_app_sections (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)
        cwf_pi_form_from_comp_cat_with_u.
    intros Γ a b t.
    refine (_ ↑ ⌈ comp_cat_subst_ty_id_iso (comp_cat_el b) ⌉⁻¹).
    refine (_ ↑ ⌈ comp_cat_subst_ty_iso _
              (z_iso_after_z_iso_inv
                 (z_iso_comp
                    (z_iso_inv (comp_cat_sigma_pair_proj_iso
                                  _ (comp_cat_el a)))
                    (comp_cat_comp_iso (z_iso_inv (comp_cat_sigma_el_iso _ _ _ _ _))))) ⌉).
    refine (_ ↑ ⌈ comp_cat_subst_ty_comp_iso _
              ((comp_cat_sigma_pair _ (comp_cat_el a) · (comp_cat_comp_mor (⌈ _ ⌉⁻¹))))
              (inv_from_z_iso _) ⌉).
    refine (_ [[ inv_from_z_iso _ ]]tm).
    refine (_ ↑ ⌈ comp_cat_el_iso (_ · _) _ ⌉⁻¹).
    refine (_ ↑ ⌈ comp_cat_el_pb_term_univ_comp _ _ _ ⌉).
    exact (comp_cat_pi_app (t ↑ ⌈ comp_cat_pi_el_iso _ _ _ _ _ ⌉ ) ).
  Defined.

  (* part of the proof of beta to be used later in the proof of eta. *)
  Local Lemma  cwf_pi_beta_eta_lemma_roundtrip
    {Γ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)%cwf}
    (t : comp_cat_tm (comp_cat_el B))
    :   (t
           [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)
               · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)
           ]]tm)
          [[inv_from_z_iso
              (z_iso_comp (z_iso_inv (comp_cat_sigma_pair_proj_iso (comp_cat_el Γ) (comp_cat_el A)))
                 (comp_cat_comp_iso (z_iso_inv (comp_cat_sigma_el_iso C Sigma SigmaU Γ A))))
          ]]tm
          ↑ ⌈ comp_cat_subst_ty_comp_iso (comp_cat_el B)
          (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)
             · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹))
          (inv_from_z_iso
             (z_iso_comp (z_iso_inv (comp_cat_sigma_pair_proj_iso (comp_cat_el Γ) (comp_cat_el A)))
                (comp_cat_comp_iso (z_iso_inv (comp_cat_sigma_el_iso C Sigma SigmaU Γ A)))))
          ⌉
          ↑ ⌈ comp_cat_subst_ty_iso (comp_cat_el B)
          (z_iso_after_z_iso_inv
             (z_iso_comp (z_iso_inv (comp_cat_sigma_pair_proj_iso (comp_cat_el Γ) (comp_cat_el A)))
                (comp_cat_comp_iso (z_iso_inv (comp_cat_sigma_el_iso C Sigma SigmaU Γ A)))))
          ⌉
          ↑ ⌈ comp_cat_subst_ty_id_iso (comp_cat_el B) ⌉⁻¹ = t.
  Proof.
    rewrite <- comp_cat_subst_tm_comp.
    etrans.
    { apply maponpaths.
      refine (comp_cat_subst_tm_eq _ _). }
    rewrite comp_cat_subst_tm_id.
    rewrite comp_cat_comp_coerce_tm.
    unfold "⌈ _ ⌉", "⌈ _  ⌉⁻¹".
    rewrite z_iso_inv_after_z_iso.
    apply comp_cat_id_coerce_tm.
  Qed.

  Definition cwf_pi_beta_from_comp_cat_with_u :
    pi_beta_sections (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)
      cwf_pi_form_from_comp_cat_with_u cwf_pi_lam_from_comp_cat_with_u
      cwf_pi_app_from_comp_cat_with_u.
  Proof.
    unfold pi_beta_sections.
    intros.
    unfold cwf_pi_app_from_comp_cat_with_u, cwf_pi_lam_from_comp_cat_with_u.
    rewrite coerce_tm_after_inv.
    rewrite comp_cat_pi_beta.
    etrans.
    { do 4 apply maponpaths.
      etrans.
      { apply maponpaths.
        apply comp_cat_el_pb_tm_comp. }
      apply coerce_tm_inv_after. }
    apply cwf_pi_beta_eta_lemma_roundtrip.
  Qed.

  Definition cwf_pi_eta_from_comp_cat_with_u
    : pi_eta_sections (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)
        cwf_pi_form_from_comp_cat_with_u
        cwf_pi_lam_from_comp_cat_with_u cwf_pi_app_from_comp_cat_with_u.
  Proof.
    unfold pi_eta_sections.
    intros.
    unfold cwf_pi_app_from_comp_cat_with_u, cwf_pi_lam_from_comp_cat_with_u.
    refine (_ @ maponpaths (λ z, z ↑ ⌈ comp_cat_pi_el_iso C Pi PiU A _ ⌉⁻¹)
              (comp_cat_pi_eta (f ↑ ⌈ comp_cat_pi_el_iso C Pi PiU A _ ⌉))
              @ coerce_tm_inv_after _ f).
    apply maponpaths.
    apply maponpaths.
    apply (coerce_tm_inj (comp_cat_el_pb_term_univ_comp B
                            (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹))
                            (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)))).
    etrans.
    { apply  (comp_cat_el_pb_tm_comp (C:=C)). }
    apply (coerce_tm_inj' (comp_cat_el_iso
                             (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)
                                · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)) B)).
    apply (comp_cat_subst_tm_z_iso_inj
             (z_iso_comp
                (z_iso_inv (comp_cat_sigma_pair_proj_iso (comp_cat_el Γ) (comp_cat_el A)))
                (comp_cat_comp_iso (z_iso_inv (comp_cat_sigma_el_iso C Sigma SigmaU Γ A))))).
    apply (coerce_tm_inj (comp_cat_subst_ty_comp_iso (comp_cat_el B)
                            ((comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)
                                · comp_cat_comp_mor
                                (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹))) _)).
    apply (coerce_tm_inj (comp_cat_subst_ty_iso (comp_cat_el B)
                            (z_iso_after_z_iso_inv (z_iso_comp
                                                      (z_iso_inv
                                                         (comp_cat_sigma_pair_proj_iso (comp_cat_el Γ)
                                                            (comp_cat_el A)))
                                                      (comp_cat_comp_iso
                                                         (z_iso_inv (comp_cat_sigma_el_iso C Sigma SigmaU Γ A))))))).
    apply (coerce_tm_inj' (comp_cat_subst_ty_id_iso (comp_cat_el B))).
    etrans.
    { do 4 apply maponpaths.
      apply coerce_tm_inv_after. }
    apply cwf_pi_beta_eta_lemma_roundtrip.
  Qed.

  Definition cwf_pi_subst_from_comp_cat_with_u
    : pi_subst (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)
        cwf_pi_form_from_comp_cat_with_u.
  Proof.
    (* completely analogous to the proof of sigma *)
    unfold pi_subst.
    intros.
    unfold cwf_subst_ty_from_comp_cat_with_u, cwf_pi_form_from_comp_cat_with_u,
      cwf_ext_con_from_comp_cat_with_u, comp_cat_pb_term_univ.
    refine (comp_cat_univ_pi_subst _ _ PiU s A _ @ _).
    apply maponpaths.
    refine (!_).
    refine (! comp_cat_pb_term_univ_comp3 _ _ _ _ @ _).
    refine (_ @ comp_cat_pb_term_univ_comp3 _ _ _ _).
    apply maponpaths.
    etrans.
    { do 2 apply maponpaths.
      exact (subst_lift_from_comp_cat_with_u_eq _ _ _ _ _ s A). }
    etrans.
    { apply assoc. }
    etrans.
    { exact (sigma_subst_lemma _ _ _ _ _ s A B). }
    apply assoc'.
  Qed.

  Definition cwf_pi_subst_lam_from_comp_cat_with_u
    : pi_subst_lam (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU) cwf_pi_form_from_comp_cat_with_u
        cwf_pi_lam_from_comp_cat_with_u cwf_pi_subst_from_comp_cat_with_u.
  Proof.
    unfold pi_subst_lam.
    intros.
    (* the transport on the right is a coercion along an el_map *)
    refine (_ @ ! transportf_tm_el_map _ _).
    (* on the left, insert the Π-substitution path and its inverse, and use
       the coherence of Π-codes on the first half *)
    refine (comp_cat_coerce_el_map_inv (C:=C)
              (comp_cat_univ_pi_subst C Pi PiU s A
                 (comp_cat_pb_term_univ
                    (comp_cat_pb_term_univ B
                       (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)))
                    (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)))) _ @ _).
    refine (maponpaths
              (λ z, z ↑ comp_cat_el_map
                         (! comp_cat_univ_pi_subst C Pi PiU s A
                              (comp_cat_pb_term_univ
                                 (comp_cat_pb_term_univ B
                                    (comp_cat_comp_mor
                                       (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)))
                                 (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)))))
              (comp_cat_univ_pi_coherent C Pi PiU s A _ _) @ _).
    (* on the right, the body of the λ is the substituted body of the λ on the left *)
    refine (_ @ maponpaths
                  (λ z, comp_cat_pi_lam (Π := Pi) z
                          ↑ ⌈ comp_cat_pi_el_iso C Pi PiU
                                (A [[s ]]tm ↑ ⌈ comp_cat_univ_sub_iso s ⌉) _ ⌉⁻¹
                          ↑ comp_cat_el_map
                              (! cwf_pi_subst_from_comp_cat_with_u Γ Δ s A B))
                  (! bprojpairΔAs_is_bprojpairΓA_subst C Sigma SigmaU Unit UnitU s A B b)).
    (* and the remaining path between the codes may be moved out of the λ *)
    refine (_ @ maponpaths
                  (λ z, z ↑ comp_cat_el_map
                             (! cwf_pi_subst_from_comp_cat_with_u Γ Δ s A B))
                  (! comp_cat_pi_lam_el_map C Pi PiU _
                       (! BprojpairΔAs_is_BprojpairΓA_subst _ _ _ _ _ s A B) _)).
    (* both sides are now the same λ, coerced along el_maps *)
    refine (_ @ ! comp_cat_comp_coerce_tm _ _ _).
    apply comp_cat_coerce_eq.
    refine (_ @ ! comp_cat_el_map_comp _ _).
    apply maponpaths.
    apply comp_cat_tm_isaset.
  Qed.

  Theorem construction_pres_pi
    : (cwf_pi_structure (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)).
  Proof.
    use make_cwf_pi_with_sections.
    - exact cwf_pi_form_from_comp_cat_with_u.
    - exact cwf_pi_lam_from_comp_cat_with_u.
    - exact cwf_pi_app_from_comp_cat_with_u.
    - exact cwf_pi_beta_from_comp_cat_with_u.
    - exact cwf_pi_eta_from_comp_cat_with_u.
    - exact cwf_pi_subst_from_comp_cat_with_u.
    - exact cwf_pi_subst_lam_from_comp_cat_with_u.
  Defined.

End PiPreservation.
