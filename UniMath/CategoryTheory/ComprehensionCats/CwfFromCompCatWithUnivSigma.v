(** Theorems about the CwF constructed from a comprehension category with a universe
    closed under Σ- and unit types (and Π-types).
    Let UnivMod(U) be the constructed CwF.  This file is part 2 of 3.
    We show that UnivMod(U) has Σ-types.  The lemmas of Section 1 are also used for Π-types in part 3.

    Contents:

    1. Lemmas about the resulting CwFs
    2. Preservation of Σ
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

Local Open Scope cat.
Local Open Scope comp_cat.


(** * 1. Lemmas about the resulting CwFs  *)

Section lemmas.
   Context (C : comp_cat_with_universe)
    (Sigma : comp_cat_sigma C)
    (SigmaU : comp_cat_universe_closed_sigma C Sigma)
    (Unit : comp_cat_unit C)
    (UnitU : comp_cat_universe_closed_unit C Unit).

  Lemma subst_tm_comp_from_comp_cat_with_u
    {Γ Δ Θ: cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
    (s' : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Θ, Δ ⟧)
    {A : cwf_ty Γ} (t :(cwf_tm ((A [[s]]) [[s']])%cwf)):
    cwf_subst_tm_comp _ s s' t = t ↑ comp_cat_el_map (! elmaplemmacomp _).
  Proof.
    etrans.
    { apply transportf_tm_el_map. }
    apply comp_cat_coerce_eq.
    apply maponpaths.
    apply comp_cat_tm_isaset.
  Qed.

  (* For the definition of (s.A) in the resulting model. *)
  Definition subst_lift_from_comp_cat_with_u_eq
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
    (A : cwf_ty Γ) :
    cwf_ext_subst_from_comp_cat_with_u Sigma SigmaU Unit UnitU Γ
      (pr1 SigmaU [] Δ (A [[s ]]tm ↑ ⌈ comp_cat_univ_sub_iso s ⌉)) A
      (cwf_proj_from_comp_cat_with_u Sigma SigmaU (A [[s ]]tm ↑ ⌈ comp_cat_univ_sub_iso s ⌉) · s)
      (cwf_subst_tm_comp A s
         (cwf_proj_from_comp_cat_with_u Sigma SigmaU (A [[s ]]tm ↑ ⌈ comp_cat_univ_sub_iso s ⌉))
         (cwf_q_from_comp_cat_with_u Sigma SigmaU (A [[s ]]tm ↑ ⌈ comp_cat_univ_sub_iso s ⌉)))
    = comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso _ _ _ _ _ ⌉)
        · comp_cat_sigma_proj _ _
        · comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹)
        · comp_cat_ext_subst s (comp_cat_el A)
        · comp_cat_sigma_pair _ _
        · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso _ _ _ _ _ ⌉⁻¹).
  Proof.
    unfold cwf_q_from_comp_cat_with_u, cwf_proj_from_comp_cat_with_u,
      cwf_ext_subst_from_comp_cat_with_u.
    do 4 rewrite assoc.
    do 2 apply maponpaths_2.
    etrans. { apply maponpaths.
              etrans; [apply comp_cat_ext_subst_comp |];
                apply maponpaths_2; apply maponpaths.
              apply idpath. }
    do 2 rewrite assoc.
    apply maponpaths_2.
    unfold comp_cat_sigma_proj_1.
    rewrite subst_tm_comp_from_comp_cat_with_u.
    rewrite comp_cat_comp_coerce_tm.
    etrans.
    { apply maponpaths.
      apply (comp_cat_ext_subst_eq _ (assoc _ _ _)). }
    etrans.
    2: { refine (!_).
         apply (comp_cat_ext_subst_coerce _ (⌈comp_cat_el_iso s A⌉⁻¹)). }
    etrans. { apply assoc. }
    apply maponpaths_2.
    unfold comp_cat_tm_from_extend_subst.
    etrans.
    { do 2 apply maponpaths_2.
      apply (comp_cat_comp_mor_to_coerce' _ _ (pr2 _)). }
    etrans.
    { apply maponpaths_2.
      apply (comp_cat_comp_mor_to_coerce' _ _ (pr2 _)). }
    etrans. { apply (comp_cat_comp_mor_to_coerce _ _ (pr2 _)). }
    do 4 rewrite comp_cat_comp_coerce_tm.
    apply maponpaths.
    apply comp_cat_coerce_eq.
    do 3 (etrans; [apply assoc' | ]).
    etrans.
    { do 2 apply maponpaths.
      etrans. { apply assoc. }
      apply maponpaths_2.
      apply comp_cat_el_map_comp. }
    apply maponpaths.
    do 3 (etrans; [ apply assoc |]).
    apply (comp_cat_el_iso_reindex_inv (C:=C)).
  Qed.

  Lemma sigma_subst_lemma
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
    (A : cwf_ty Γ)
    (B : cwf_ty (Γ & A)%cwf)
    : (comp_cat_sigma_pair (comp_cat_el Δ)
         (comp_cat_el (A [[s ]]tm ↑ ⌈ comp_cat_univ_sub_iso s ⌉))
         · comp_cat_comp_mor
         (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ
            (A [[s ]]tm ↑ ⌈ comp_cat_univ_sub_iso s ⌉)
            ⌉⁻¹)
         · (comp_cat_comp_mor
              (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ
                 (A [[s ]]tm ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) s ⌉)
                 ⌉)
              · comp_cat_sigma_proj (comp_cat_el Δ)
              (comp_cat_el (A [[s ]]tm ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) s ⌉))
              · comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹)
              · comp_cat_ext_subst s (comp_cat_el A)
              · comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)
              · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)))
      = comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹)
          · comp_cat_ext_subst s (comp_cat_el A)
          · comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)
          · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹).
  Proof.
    set (u := comp_cat_univ_sub_iso s).
    set (As := A [[s]]tm ↑ ⌈u⌉).
    do 5 rewrite assoc.
    etrans. {
      do 5 apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply comp_cat_comp_mor_z_iso_after_z_iso_inv. }
    rewrite id_right.
    etrans. {
      do 4 apply maponpaths_2.
      apply comp_cat_sigma_beta. }
    rewrite id_left.
    apply idpath.
  Qed.

  Lemma cwf_lift_sigma_pair_eq
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
    (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf)
    : comp_cat_sigma_pair (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf)
        · comp_cat_comp_mor
            (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf ⌉⁻¹)
        · cwf_lift s A
      = comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹)
          · comp_cat_ext_subst s (comp_cat_el A)
          · comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)
          · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹).
  Proof.
    etrans.
    { apply maponpaths.
      apply (subst_lift_from_comp_cat_with_u_eq s A). }
    exact (sigma_subst_lemma s A B).
  Qed.

  (* Lemma for both sigma_subst and pi_subst  *)
  Lemma BprojpairΔAs_is_BprojpairΓA_subst
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
    (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf)
    : (((B [[cwf_lift s A]])%cwf
          [[comp_cat_comp_mor
              (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf ⌉⁻¹)]]tm
          ↑ ⌈ comp_cat_univ_sub_iso
              (comp_cat_comp_mor
                 (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf ⌉⁻¹)) ⌉)
         [[comp_cat_sigma_pair (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf)]]tm
         ↑ ⌈ comp_cat_univ_sub_iso
             (comp_cat_sigma_pair (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf)) ⌉)
      = ((B [[comp_cat_comp_mor
                (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)]]tm
           ↑ ⌈ comp_cat_univ_sub_iso
               (comp_cat_comp_mor
                  (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)) ⌉)
          [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)]]tm
          ↑ ⌈ comp_cat_univ_sub_iso
              (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)) ⌉)
         [[comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹)
             · comp_cat_ext_subst s (comp_cat_el A)]]tm
         ↑ ⌈ comp_cat_univ_sub_iso
             (comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹)
                · comp_cat_ext_subst s (comp_cat_el A)) ⌉.
  Proof.
    refine (! elmaplemmacomp (pr12 C) @ _).
    refine (! elmaplemmacomp (pr12 C) @ _).
    refine (_ @ elmaplemmacomp (pr12 C)).
    refine (_ @ elmaplemmacomp (pr12 C)).
    apply (maponpaths (comp_cat_pb_term_univ B)).
    exact (cwf_lift_sigma_pair_eq s A B).
  Qed.

  Definition comp_cat_sigma_unpack2
    {Γ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (A : cwf_ty Γ)
    (Bcode : comp_cat_tm (comp_cat_U ([] & comp_cat_el ((Γ & A)%cwf))))
    : z_iso ( [] & comp_cat_el (comp_cat_sigma_code C Sigma SigmaU ((Γ & A)%cwf) Bcode))
        ((([] & comp_cat_el Γ) & comp_cat_el A)
         & comp_cat_el (Bcode [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)]]tm
                          ↑ ⌈comp_cat_univ_sub_iso (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A))⌉))
    :=
    z_iso_comp (comp_cat_sigma_unpack C Sigma SigmaU _ Bcode)
      (z_iso_comp
         (comp_cat_comp_iso
            (comp_cat_el_z_iso_from_eq (! (! elmaplemmacomp (pr12 C)
                                             @ (comp_cat_subst_coerce_tm_eq (z_iso_inv_after_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)) (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉) (sub_comp_cat_univ_iso_natural _ (z_iso_inv_after_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A))) _)
                                             @ elmaplemma _))))
         (comp_cat_univ_lift_z_iso (C:=C) (comp_cat_sigma_unpack C Sigma SigmaU _ A) _)).

  (* The key to proving the lemmas for preservation of the resulting type formers under substitution
   is a lemma which gives cwf_lift in the resulting CwF in terms comp_cat_univ_lift in the starting comprehension category. *)

  Lemma cwf_lift_via_univ_lift
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
    (A : comp_cat_tm (comp_cat_U ([] & comp_cat_el Γ)))
    : cwf_lift s A = comp_cat_sigma_unpack C Sigma SigmaU _ _ · comp_cat_univ_lift _ s A
                       · z_iso_inv (comp_cat_sigma_unpack C Sigma SigmaU _ A).
  Proof.
    refine (subst_lift_from_comp_cat_with_u_eq s A @ _).
    refine (!_).
    etrans.
    { apply maponpaths_2.
      apply maponpaths_2.
      apply (comp_cat_sigma_unpack_mor C Sigma SigmaU). }
    etrans.
    { apply maponpaths.
      apply (comp_cat_sigma_unpack_inv_mor C Sigma SigmaU). }
    unfold comp_cat_univ_lift.
    do 2 rewrite assoc.
    apply idpath.
  Qed.

  Lemma cwf_lift_unpack_commute
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
    (A : cwf_ty Γ)
    : inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ (A [[s]])%cwf) · cwf_lift s A
      = comp_cat_univ_lift C s A · inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A).
  Proof.
    rewrite cwf_lift_via_univ_lift.
    unfold comp_cat_sigma_unpack.
    do 2 rewrite assoc.
    etrans.
    { do 2 apply maponpaths_2.
      apply (z_iso_after_z_iso_inv (comp_cat_sigma_unpack C Sigma SigmaU _ (A [[s]])%cwf)). }
    rewrite id_left.
    apply idpath.
  Qed.

  Lemma Bprojpair_is_Bext
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf)
    : (B [[comp_cat_comp_mor (⌈comp_cat_sigma_el_iso C Sigma SigmaU Γ A⌉⁻¹)]]tm ↑
         ⌈ comp_cat_univ_sub_iso _ ⌉)
        [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)]]tm ↑ ⌈ comp_cat_univ_sub_iso _ ⌉
      = B [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)]]tm ↑ ⌈comp_cat_univ_sub_iso _⌉.
  Proof.
    refine (! elmaplemmacomp (pr12 C) @ _).
    use comp_cat_subst_coerce_tm_eq.
    - apply idpath.
    - apply sub_comp_cat_univ_iso_natural.
  Qed.

  Lemma B_is_BprojpairΓA_subst
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf)
    (BprojpairΓA :=
       ((B[[comp_cat_comp_mor
              (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)
           ]]tm
           ↑ ⌈ comp_cat_univ_sub_iso
           (comp_cat_comp_mor
              (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹))
           ⌉)
          [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A) ]]tm
          ↑ ⌈ comp_cat_univ_sub_iso
          (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A))
          ⌉))
    : B = BprojpairΓA [[comp_cat_sigma_unpack C Sigma SigmaU _ A]]tm
            ↑ ⌈comp_cat_univ_sub_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)⌉.
  Proof.
    refine (comp_cat_tm_subst_coerce_inv (z_iso_inv (comp_cat_sigma_unpack C Sigma SigmaU _ A)) B @ _).
    apply (maponpaths (λ z, z [[comp_cat_sigma_unpack C Sigma SigmaU _ A]]tm
                              ↑ ⌈comp_cat_univ_sub_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)⌉)).
    exact (elmaplemmacomp (pr12 C)).
  Qed.

  Lemma cwf_lift_cwf_lift_via_univ_lift
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
    (A : comp_cat_tm (comp_cat_U ([] & comp_cat_el Γ)))
    (Bcode : comp_cat_tm (comp_cat_U ([] & comp_cat_el ((Γ & A)%cwf))))
    : cwf_lift (cwf_lift s A) Bcode
      =  comp_cat_sigma_unpack2 _ _ ·
           comp_cat_comp_mor (comp_cat_el_map (
                                  ( ! elmaplemmacomp (pr12 C) @ (comp_cat_subst_coerce_tm_eq (cwf_lift_unpack_commute _ _)
                                                                   (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉) (sub_comp_cat_univ_iso_natural _ (cwf_lift_unpack_commute _ _)) _) )
                                    @ elmaplemmacomp _ ))
           · comp_cat_univ_lift C (comp_cat_univ_lift C s A) _
           · z_iso_inv (comp_cat_sigma_unpack2 _ _).
  Proof.
    refine (cwf_lift_via_univ_lift (cwf_lift s A) _ @ _).
    unfold comp_cat_sigma_unpack2.
    etrans.
    2:  {
      do 3 apply maponpaths_2.
      apply (idpath ((comp_cat_sigma_unpack C Sigma SigmaU _ _)
                       · ( (comp_cat_comp_iso (comp_cat_el_z_iso_from_eq _ ) ) · (comp_cat_univ_lift_z_iso (C:=C) _ _)))). }
    do 5 rewrite assoc'.
    apply maponpaths.
    do 3 rewrite assoc.
    etrans.
    2 : { apply maponpaths.
          rewrite z_iso_inv_of_z_iso_comp.
          refine (!_).
          etrans.
          {  apply (idpath (
                        (z_iso_inv_from_z_iso _)
                          · (z_iso_inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ Bcode)))). }
          apply maponpaths_2.
          rewrite z_iso_inv_of_z_iso_comp.
          apply (idpath ( _ · _ )). }
    do 2 rewrite assoc.
    apply maponpaths_2.
    rewrite (comp_cat_univ_lift_eq (C:=C) _ _ _ (cwf_lift_via_univ_lift s A)).
    rewrite !(comp_cat_univ_lift_comp (C:=C)).
    etrans.
    { do 2 apply maponpaths.
      apply (comp_cat_univ_lift_inv (C:=C)). }
    (* after the lifts equal *)
    assert (p :comp_cat_comp_mor
                 (comp_cat_el_map (! comp_cat_tm_subst_coerce_inv' (comp_cat_sigma_unpack C Sigma SigmaU _ A) Bcode)) =
                 z_iso_inv_from_z_iso
                   (comp_cat_comp_iso
                      (comp_cat_el_z_iso_from_eq
                         (! (! elmaplemmacomp (pr12 C) @
                               (comp_cat_subst_coerce_tm_eq (z_iso_inv_after_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A))
                                  (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉)
                                  (sub_comp_cat_univ_iso_natural _ (z_iso_inv_after_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A))) Bcode) @
                               elmaplemma (pr12 C)))))). {
      refine (_ @ ! maponpaths pr1 (comp_cat_comp_iso_inv _)).
      simpl.
      apply maponpaths.
      refine (_ @ ! (comp_cat_el_z_iso_from_eq_inv (C:=C)) _).
      apply maponpaths.
      apply comp_cat_tm_isaset.
    }
    etrans. { do 3 apply maponpaths.
              apply p. }
    do 5 rewrite assoc.
    do 3 apply maponpaths_2.
    do 3 rewrite assoc'.
    etrans.
    2: { apply maponpaths.
         refine (comp_cat_univ_lift_el_map_natural (C:=C) ?[i] ?[p]
                  (maponpaths (λ z, z [[ ?i ]]tm ↑ ⌈comp_cat_univ_sub_iso ?i⌉) ?p)). }
    do 3 rewrite assoc.
    apply maponpaths_2.
    rewrite <- !comp_cat_comp_mor_comp'.
    rewrite !comp_cat_el_map_comp.
    etrans.
    2 : {
      refine (!_).
      etrans.
      { refine (!_). apply comp_cat_comp_mor_comp'. }
      apply maponpaths.
      refine ( _ @ comp_cat_el_map_comp _ _).
      apply maponpaths_2.
      apply (coe_comp_cat_el_z_iso_from_eq (C':=C)). }
    apply maponpaths.
    apply maponpaths.
    apply comp_cat_tm_isaset.
  Qed.

  Lemma cwf_tm_eq_to_mor_is_el_map
  {Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
  {a b : cwf_ty Δ} (p : a = b)
  : cwf_tm_eq_to_mor p
    = comp_cat_comp_mor
        (comp_cat_el_map (maponpaths (comp_cat_sigma_code C Sigma SigmaU Δ) p)).
  Proof.
    induction p.
    refine (!_).
    refine (_ @ comp_cat_comp_mor_id).
    apply maponpaths.
    apply (comp_cat_el_map_id _ (idpath _)).
  Qed.

  Lemma bprojpairΔAs_is_bprojpairΓA_subst
  {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
  (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
  (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf) (b : cwf_tm B)
  (L  := comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹)
           · comp_cat_ext_subst s (comp_cat_el A))
  (mΓ := comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹))
  (pΓ := comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A))
  (mΔ := comp_cat_comp_mor
           (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf ⌉⁻¹))
  (pΔ := comp_cat_sigma_pair (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf))
  : (((b [[cwf_lift s A]]tm ↑ ⌈ comp_cat_el_iso (cwf_lift s A) B ⌉)
        [[mΔ]]tm ↑ ⌈ comp_cat_el_iso mΔ _ ⌉)
       [[pΔ]]tm ↑ ⌈ comp_cat_el_iso pΔ _ ⌉)
    = ((((b [[mΓ]]tm ↑ ⌈ comp_cat_el_iso mΓ B ⌉)
           [[pΓ]]tm ↑ ⌈ comp_cat_el_iso pΓ _ ⌉)
          [[L]]tm ↑ ⌈ comp_cat_el_iso L _ ⌉)
         ↑ comp_cat_el_map
         (! BprojpairΔAs_is_BprojpairΓA_subst s A B)).
  Proof.
    (* move the coercion on the right to the left *)
    refine (comp_cat_el_map_move (C:=C)
              (BprojpairΔAs_is_BprojpairΓA_subst s A B) _ _ _ _).
    etrans.
    { exact (maponpaths
               (λ z, z ↑ comp_cat_el_map
                          (BprojpairΔAs_is_BprojpairΓA_subst s A B))
               (comp_cat_el_pb_tm_comp3 (C:=C) B (cwf_lift s A) mΔ pΔ b)). }
    etrans.
    { apply (comp_cat_el_map_merge (C:=C) _ _
               (maponpaths (comp_cat_pb_term_univ B)
                  (assoc _ _ _ @ cwf_lift_sigma_pair_eq s A B
                     @ ! assoc _ _ _)
                @ comp_cat_pb_term_univ_comp3 (C:=C) B mΓ pΓ L)). }
    etrans.
    { refine (! comp_cat_el_map_merge (C:=C)
                  (maponpaths (comp_cat_pb_term_univ B)
                     (assoc _ _ _ @ cwf_lift_sigma_pair_eq s A B
                        @ ! assoc _ _ _))
                  (comp_cat_pb_term_univ_comp3 (C:=C) B mΓ pΓ L) _ _). }
    etrans.
    { exact (maponpaths
               (λ z, z ↑ comp_cat_el_map (comp_cat_pb_term_univ_comp3 (C:=C) B mΓ pΓ L))
               (comp_cat_el_subst_tm_eq (C:=C)
                  (assoc _ _ _ @ cwf_lift_sigma_pair_eq s A B
                     @ ! assoc _ _ _) B b _)). }
    (* and expand the three substitutions on the right again *)
    refine (! comp_cat_el_pb_tm_comp3 (C:=C) B mΓ pΓ L b).
  Qed.

End lemmas.


(** * 2. Preservation of Σ *)
Section SigmaPreservation.

  Context (C : comp_cat_with_universe)
    (Sigma : comp_cat_sigma C)
    (SigmaU : comp_cat_universe_closed_sigma C Sigma)
    (Unit : comp_cat_unit C)
    (UnitU : comp_cat_universe_closed_unit C Unit).

  (* the sigma type of the cwf is given by the sigma code Σ(A,B')
     where B' is B pulled back into the correct context *)
  Definition cwf_sigma_form_from_comp_cat_with_u
    : sigma_form (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU).
  Proof.
    intros Γ A B.
    unfold cwf_ext_con_from_comp_cat_with_u in *.
    refine (comp_cat_sigma_code _ _ SigmaU A _).
    refine (comp_cat_pb_term_univ
              (comp_cat_pb_term_univ B
                 (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso _ _ _ _ _ ⌉⁻¹)))
              _).
    refine (comp_cat_sigma_pair _ _ ).
  Defined.

  Definition cwf_sigma_pair_mor_from_comp_cat_with_u
    :  sigma_pair_mor_sections (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)
         (cwf_sigma_form_from_comp_cat_with_u).
  Proof.
    intros Γ A B.
    refine (comp_cat_comp_mor ( ⌈ comp_cat_sigma_el_iso _ _ _ _ _ ⌉ ) · _).
    refine (_ · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso _ _ _ _ _ ⌉⁻¹ )).
    refine (comp_cat_sigma_iso_1 ( comp_cat_comp_iso ( comp_cat_sigma_el_iso _ _ _ _ _  ))  · _).
    unfold cwf_sigma_form_from_comp_cat_with_u.
    refine (_ · comp_cat_sigma_assoc (Σ := Sigma) (comp_cat_el Γ) (comp_cat_el A)
              (comp_cat_el (comp_cat_pb_term_univ
                              (comp_cat_pb_term_univ B
                                 (comp_cat_comp_mor
                                    (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)))
                              (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A))))
              · _).
    + refine (comp_cat_sigma_iso_2 _).
      refine (comp_cat_comp_iso (z_iso_comp _ (z_iso_inv (comp_cat_el_iso _ _)))).
      refine (z_iso_comp (comp_cat_el_iso _ _) _).
      refine (comp_cat_el_z_iso_from_eq _).
      abstract (
          refine (_ @ ! comp_cat_pb_term_univ_comp _ _ _);
          refine (! comp_cat_pb_term_univ_id _ @ _);
          apply maponpaths;
          refine (!_);
          apply comp_cat_sigma_eta).
    + refine (comp_cat_sigma_iso_2 _).
      refine (z_iso_comp _ (comp_cat_comp_iso (z_iso_inv (comp_cat_sigma_el_iso _ _ _ _ _ )))).
      refine (comp_cat_sigma_iso_2 _).
      apply identity_z_iso.
  Defined.

  Definition cwf_pair_pi_from_comp_cat_with_u
    : sigma_pair_pi_sections (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU) cwf_sigma_form_from_comp_cat_with_u
        cwf_sigma_pair_mor_from_comp_cat_with_u.
  Proof.
    intros Γ A B.
    cbn.
    unfold cwf_sigma_pair_mor_from_comp_cat_with_u.
    do 3 rewrite assoc'.
    etrans.
    { apply assoc. }
    etrans.
    { apply maponpaths_2.
      do 5 ( rewrite assoc'; apply maponpaths).
      apply comp_cat_comp_mor_z_iso_after_z_iso_inv. }
    rewrite id_right.
    do 4 rewrite assoc'.
    refine (!_).
    refine (assoc' _ _ _ @ _).
    apply maponpaths.
    refine (!_).
    etrans.
    { do 3 apply maponpaths.
      apply comp_cat_sigma_iso_2_proj.
      cbn.
      rewrite assoc'.
      rewrite id_left.
      rewrite comp_cat_comp_mor_law.
      rewrite <- id_left.
      apply maponpaths_2.
      apply comp_cat_sigma_eta.
    }
    rewrite comp_cat_sigma_assoc_proj_1.
    do 2 rewrite assoc.
    etrans.
    { apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      apply comp_cat_sigma_iso_2_proj.
      apply comp_cat_comp_mor_law.
    }
    etrans.
    { apply maponpaths_2.
      exact (comp_cat_sigma_iso_1_proj (B:=comp_cat_el B) (comp_cat_comp_iso (comp_cat_sigma_el_iso C Sigma SigmaU Γ A))). }
    unfold cwf_proj_from_comp_cat_with_u.
    rewrite assoc.
    apply idpath.
  Qed.

  Definition cwf_proj_mor_from_comp_cat_with_u
    : sigma_proj_mor_sections (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU) cwf_sigma_form_from_comp_cat_with_u.
  Proof.
    intros Γ A B.
    refine (comp_cat_comp_mor( ⌈ comp_cat_sigma_el_iso _ _ _ _ _ ⌉ ) · _).
    refine (_ · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso _ _ _ _ _ ⌉⁻¹) ).
    unfold cwf_sigma_form_from_comp_cat_with_u.
    unfold cwf_ext_con_from_comp_cat_with_u.
    refine (_
              · z_iso_inv
              ( comp_cat_sigma_iso_1 (comp_cat_comp_iso (comp_cat_sigma_el_iso _ _ _ _ _ ) ) )).
    refine (comp_cat_sigma_iso_2 (comp_cat_comp_iso (comp_cat_sigma_el_iso _ _ _ _ _ ))  · _).
    refine (identity _
              · z_iso_inv (comp_cat_sigma_assoc (Σ := Sigma) (comp_cat_el Γ) (comp_cat_el A) _) · _).
    refine (comp_cat_sigma_iso_2 _).
    refine (comp_cat_comp_iso (z_iso_comp _ (z_iso_inv (comp_cat_el_iso _ _)))).
    refine (z_iso_comp (comp_cat_el_iso _ _) _).
    refine (comp_cat_el_z_iso_from_eq _).
    abstract(
        refine (!_);
        refine (_ @ ! comp_cat_pb_term_univ_comp _ _ _);
        refine (! comp_cat_pb_term_univ_id _ @ _);
        apply maponpaths;
        refine (!_);
        apply comp_cat_sigma_eta).
  Defined.

  Lemma beta_from_comp_cat_lemma
    {Γ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU} (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf)
    :  (comp_cat_sigma_proj _ _ ·
          (comp_cat_comp_mor (inv_from_z_iso (comp_cat_sigma_el_iso _ _ _ _
                                                (comp_cat_pb_term_univ (comp_cat_pb_term_univ B (comp_cat_comp_mor
                                                                                                   (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)))
                                                   (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)))))
             · comp_cat_sigma_pair _ _) = (comp_cat_sigma_iso_2 (Sig := Sigma)
                                             (comp_cat_comp_iso
                                                (z_iso_inv (comp_cat_sigma_el_iso C Sigma SigmaU A _))))).
  Proof.
    apply idpath.
  Qed.

  Local Lemma beta_from_comp_cat_lemma_2
    {Γ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (A : cwf_ty Γ)
    (B : cwf_ty (Γ & A)%cwf)
    :
    z_iso_comp
      (z_iso_comp
         (z_iso_comp
            (comp_cat_el_iso (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)) B)
            (comp_cat_el_z_iso_from_eq (cwf_sigma_pair_mor_from_comp_cat_with_u_subproof Γ A B)))
         (z_iso_inv
            (comp_cat_el_iso (comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A))
               (comp_cat_pb_term_univ
                  (comp_cat_pb_term_univ B
                     (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)))
                  (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A))))))
      (z_iso_comp
         (z_iso_comp
            (comp_cat_el_iso (comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A))
               (comp_cat_pb_term_univ
                  (comp_cat_pb_term_univ B
                     (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)))
                  (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A))))
            (comp_cat_el_z_iso_from_eq (cwf_proj_mor_from_comp_cat_with_u_subproof Γ A B)))
         (z_iso_inv
            (comp_cat_el_iso (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)) B))) = identity_z_iso _.
  Proof.
    use z_iso_eq.
    do 2 refine (assoc' (C:= fiber_category _ _) _ _ _ @ _).
    etrans.
    { do 2 apply maponpaths.
      apply maponpaths.
      refine (assoc' (C:= fiber_category _ _) _ _ _ @ _).
      apply idpath. }
    etrans.
    { do 2 apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply z_iso_after_z_iso_inv. }
    rewrite id_left.
    etrans.
    { apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply comp_cat_el_z_iso_from_eq_comp. }
    rewrite assoc.
    rewrite comp_cat_el_map_id.
    rewrite id_right.
    apply z_iso_inv_after_z_iso.
  Qed.

  Definition cwf_beta_law_from_comp_cat_with_u
    :  sigma_beta_law_sections (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU) cwf_sigma_form_from_comp_cat_with_u
         cwf_sigma_pair_mor_from_comp_cat_with_u cwf_proj_mor_from_comp_cat_with_u.
  Proof.
    unfold sigma_beta_law_sections.
    unfold cwf_sigma_pair_mor_from_comp_cat_with_u.
    unfold cwf_proj_mor_from_comp_cat_with_u.
    intros Γ A B.
    do 7 rewrite assoc'.
    rewrite id_left.
    etrans.
    { do 5 (refine (assoc' (C:=C) _ _ _ @ _);
            apply maponpaths).
      rewrite assoc.
      rewrite comp_cat_comp_mor_z_iso_after_z_iso_inv.
      apply id_left. }
    etrans.
    { do 4 apply maponpaths.
      apply maponpaths_2.
      cbn.
      rewrite id_left.
      rewrite comp_cat_sigma_eta.
      rewrite id_left.
      apply beta_from_comp_cat_lemma. }
    etrans.
    { do 4 apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      cbn.
      do 3 rewrite assoc.
      do 3 rewrite assoc4.
      rewrite (assoc (comp_cat_sigma_pair _ _) _ _).
      rewrite comp_cat_sigma_beta.
      rewrite id_left.
      rewrite <- comp_cat_comp_mor_comp'.
      rewrite z_iso_after_z_iso_inv.
      apply maponpaths_2.
      apply maponpaths.
      apply comp_cat_comp_mor_id. }
    rewrite id_right.
    rewrite comp_cat_sigma_eta.
    rewrite id_left.
    etrans.
    { do 3 apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply z_iso_inv_after_z_iso. }
    rewrite id_left.
    etrans.
    { do 2 apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      rewrite <- comp_cat_sigma_iso_2_comp'.
      do 2 apply maponpaths.
      rewrite comp_cat_comp_iso_comp.
      apply maponpaths.
      apply beta_from_comp_cat_lemma_2. }
    rewrite comp_cat_comp_iso_id.
    rewrite comp_cat_sigma_iso_2_id.
    rewrite id_left.
    do 2 rewrite assoc.
    rewrite assoc4.
    rewrite z_iso_inv_after_z_iso.
    rewrite id_right.
    apply comp_cat_comp_mor_z_iso_inv_after_z_iso.
  Qed.

  Lemma cwf_eta_from_comp_cat_lemma
    {Γ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (A : cwf_ty Γ)
    (B : cwf_ty (Γ & A)%cwf)
    : z_iso_comp
        (z_iso_comp (z_iso_comp (comp_cat_el_iso _ _)
                       (comp_cat_el_z_iso_from_eq (cwf_proj_mor_from_comp_cat_with_u_subproof Γ A B)))
           (z_iso_inv (comp_cat_el_iso _ B)))
        (z_iso_comp (z_iso_comp (comp_cat_el_iso _ B)
                       (comp_cat_el_z_iso_from_eq (cwf_sigma_pair_mor_from_comp_cat_with_u_subproof Γ A B)))
           (z_iso_inv (comp_cat_el_iso _ _)))
      = identity_z_iso _.
  Proof.
    use z_iso_eq.
    rewrite !z_iso_comp_assoc'.
    etrans.
    { do 3 apply maponpaths.
      refine (!z_iso_comp_assoc' _ _ _ @ _).
      apply maponpaths_2.
      apply z_iso_inv_after_z_iso'. }
    etrans.
    { do 3 apply maponpaths.
      rewrite z_iso_id_left.
      apply idpath. }
    etrans. {
      do 2 apply maponpaths.
      refine (!z_iso_comp_assoc' (comp_cat_el_z_iso_from_eq _) _ _ @ _).
      apply maponpaths_2.
      apply comp_cat_el_z_iso_from_eq_comp'. }
    etrans. {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply comp_cat_el_z_iso_from_eq_id'. }
    rewrite z_iso_id_left.
    apply z_iso_inv_after_z_iso.
  Qed.

  Definition cwf_eta_law_from_comp_cat_with_u
    : sigma_eta_law_sections (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU) cwf_sigma_form_from_comp_cat_with_u
        cwf_sigma_pair_mor_from_comp_cat_with_u cwf_proj_mor_from_comp_cat_with_u.
  Proof.
    unfold sigma_beta_law_sections.
    intros Γ A B.
    unfold cwf_sigma_pair_mor_from_comp_cat_with_u.
    unfold cwf_proj_mor_from_comp_cat_with_u.
    rewrite id_left.
    do 6 rewrite assoc'.
    etrans.
    { do 5 (refine (assoc' (C:=C) _ _ _ @ _);
            apply maponpaths).
      rewrite assoc.
      rewrite comp_cat_comp_mor_z_iso_after_z_iso_inv.
      rewrite id_left.
      apply idpath. }
    etrans.
    { do 3 apply maponpaths.
      refine (assoc' (C:=C) _ _ _ @ _).
      apply maponpaths.
      refine (assoc' (C:=C) _ _ _ @ _).
      do 2 apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      apply z_iso_inv_after_z_iso. }
    rewrite id_left.
    etrans.
    { do 8 apply maponpaths.
      apply maponpaths_2.
      rewrite comp_cat_sigma_iso_2_comp'.
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths.
      apply comp_cat_sigma_iso_2_id. }
    etrans.
    { do 8 apply maponpaths.
      apply maponpaths_2.
      apply maponpaths_2.
      apply maponpaths.
      apply comp_cat_sigma_iso_2_id. }
    rewrite id_left.
    etrans.
    { do 3 apply maponpaths.
      do 5 rewrite assoc.
      do 3 apply maponpaths_2.
      unfold comp_cat_sigma_iso_2.
      do 2 rewrite assoc'.
      etrans.
      { do 2 apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply z_iso_after_z_iso_inv. }
      rewrite id_left.
      etrans.
      { apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans. { apply (maponpaths pr1 (comp_cat_comp_iso_comp _ _)). }
        do 2 apply maponpaths.
        apply cwf_eta_from_comp_cat_lemma. }
      rewrite comp_cat_comp_iso_id.
      rewrite id_left.
      apply z_iso_inv_after_z_iso. }
    rewrite id_left.
    etrans.
    { do 2 apply maponpaths.
      do 2 rewrite assoc.
      rewrite z_iso_inv_after_z_iso.
      rewrite id_left.
      apply idpath. }
    do 2 rewrite assoc.
    rewrite assoc4.
    rewrite <- comp_cat_sigma_iso_2_comp'.
    rewrite assoc'.
    etrans.
    { apply maponpaths.
      apply maponpaths_2.
      do 2 apply maponpaths.
      rewrite comp_cat_comp_iso_comp.
      apply maponpaths.
      apply z_iso_inv_after_z_iso'. }
    rewrite comp_cat_comp_iso_id.
    rewrite comp_cat_sigma_iso_2_id.
    rewrite id_left.
    apply comp_cat_comp_mor_z_iso_inv_after_z_iso.
  Qed.

  Section sigma_subst.

  Definition sigma_subst_from_comp_cat_with_u
    : sigma_subst (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU) cwf_sigma_form_from_comp_cat_with_u.
  Proof.
    unfold sigma_subst.
    intros.
    unfold cwf_subst_ty_from_comp_cat_with_u, cwf_sigma_form_from_comp_cat_with_u,
      cwf_ext_con_from_comp_cat_with_u, comp_cat_pb_term_univ.
    refine (comp_cat_univ_sigma_subst _ _ SigmaU s A _ @ _).
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

  End sigma_subst.

  Section pair_subst.

  (** Small lemmas used to cut down the proof of [sigma_pair_sub_lemma_after_lift]. *)

  Lemma comp_assoc_tail6
    {D : category} {x0 x1 x2 x3 x4 x5 x6 x7 : D}
    (X : x0 --> x1) (p1 : x1 --> x2) (p2 : x2 --> x3) (p3 : x3 --> x4)
    (p4 : x4 --> x5) (p5 : x5 --> x6) (p6 : x6 --> x7)
    : (((((X · p1) · p2) · p3) · p4) · p5) · p6
      = X · (((((p1 · p2) · p3) · p4) · p5) · p6).
  Proof.
    rewrite !assoc'.
    apply idpath.
  Qed.

  Lemma comp_cancel_z_iso_tail
    {D : category} {a b c d f : D}
    (Y : a --> c) (z : z_iso b c) (k : c --> d) (i1 : d --> a) (i2 : a --> f)
    (H : (Y · k) · i1 = identity a)
    : (Y · inv_from_z_iso z) · (((z · k) · i1) · i2) = i2.
  Proof.
    rewrite !assoc'.
    rewrite (assoc (inv_from_z_iso z) z _).
    rewrite z_iso_after_z_iso_inv.
    rewrite id_left.
    rewrite !assoc.
    rewrite H.
    rewrite id_left.
    apply idpath.
  Qed.

  Lemma comp_cat_sigma_unpack_el_map
    {Γ' : C} (a : comp_cat_tm (comp_cat_U Γ'))
    {b b' : comp_cat_tm (comp_cat_U (Γ' & comp_cat_el a))}
    (p : b = b')
    : comp_cat_comp_mor (comp_cat_el_map (maponpaths (comp_cat_sigma_code C Sigma SigmaU a) p))
        · comp_cat_sigma_unpack C Sigma SigmaU a b'
        · comp_cat_comp_mor (comp_cat_el_map (! p))
      = comp_cat_sigma_unpack C Sigma SigmaU a b.
  Proof.
    induction p.
    rewrite !comp_cat_el_map_id.
    etrans.
    { apply maponpaths.
      exact comp_cat_comp_mor_id. }
    etrans.
    { do 2 apply maponpaths_2.
      exact comp_cat_comp_mor_id. }
    rewrite id_left, id_right.
    apply idpath.
  Qed.

    Lemma comp_cat_sigma_repack_middle
      {Γ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
      (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf)
      (mΓ := comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹))
      (pΓ := comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A))
      (L := comp_cat_sigma_unpack C Sigma SigmaU Γ A)
      (BprojpairΓA :=
         ((B [[mΓ]]tm ↑ ⌈ comp_cat_univ_sub_iso mΓ ⌉)
            [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A) ]]tm
            ↑ ⌈ comp_cat_univ_sub_iso
                  (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)) ⌉))
      (B' := B [[inv_from_z_iso L ]]tm
               ↑ ⌈ comp_cat_univ_sub_iso (inv_from_z_iso L) ⌉)
      (q : B = B' [[L ]]tm ↑ ⌈ comp_cat_univ_sub_iso L ⌉)
      (r : B' = BprojpairΓA)
      : comp_cat_comp_mor
          (⌈ z_iso_comp
               (z_iso_comp (comp_cat_el_iso mΓ B)
                  (comp_cat_el_z_iso_from_eq
                     (cwf_sigma_pair_mor_from_comp_cat_with_u_subproof Γ A B)))
               (z_iso_inv (comp_cat_el_iso pΓ BprojpairΓA)) ⌉)
          · comp_cat_ext_subst pΓ (comp_cat_el BprojpairΓA)
        = comp_cat_ext_subst mΓ (comp_cat_el B)
            · comp_cat_comp_iso (comp_cat_el_z_iso_from_eq q)
            · comp_cat_univ_lift C L B'
            · comp_cat_comp_mor (comp_cat_el_map r).
    Proof.
      assert (Hp : mΓ · L = pΓ).
      { refine (assoc _ _ _ @ _).
        etrans.
        { apply maponpaths_2.
          apply comp_cat_comp_mor_z_iso_after_z_iso_inv. }
        apply id_left. }
      (* move every coercion on the right to the front *)
      etrans.
      2: { do 2 apply maponpaths_2.
           apply maponpaths.
           refine (! (comp_cat_el_z_iso_from_eq_pr1_comp_mor (C:=C)) q). }
      etrans.
      2: { do 2 apply maponpaths_2.
           apply comp_cat_ext_subst_coercion. }
      unfold comp_cat_univ_lift.
      rewrite assoc.
      etrans.
      2: { do 2 apply maponpaths_2.
           rewrite assoc'.
           apply maponpaths.
           apply comp_cat_ext_subst_coercion. }
      rewrite assoc.
      etrans.
      2: { apply maponpaths_2.
           rewrite assoc'.
           apply maponpaths.
           apply comp_cat_ext_subst_comp'. }
      rewrite assoc.
      etrans.
      2: { apply maponpaths_2.
           apply maponpaths.
           refine (! comp_cat_ext_subst_eq (comp_cat_el B') Hp). }
      rewrite assoc.
      etrans.
      2: { rewrite assoc'.
           apply maponpaths.
           apply comp_cat_ext_subst_coercion. }
      rewrite assoc.
      (* what is left is an identity between coercions *)
      apply maponpaths_2.
      rewrite <- !comp_cat_comp_mor_comp'.
      apply maponpaths.
      use (cancel_z_iso _ _ (comp_cat_el_iso pΓ BprojpairΓA)).
      etrans.
      { exact (idpath (_ · _ · _ · _)). }
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply (z_iso_after_z_iso_inv (comp_cat_el_iso pΓ BprojpairΓA)). }
      rewrite id_right.
      do 4 rewrite assoc'.
      etrans.
      2: { do 4 apply maponpaths.
           exact (comp_cat_el_iso_natural pΓ r
                    (maponpaths (λ z, comp_cat_pb_term_univ z pΓ) r)). }
      etrans.
      2: { do 3 apply maponpaths.
           rewrite assoc.
           apply maponpaths_2.
           exact (comp_cat_el_iso_subst_path Hp B'). }
      rewrite assoc'.
      (* the coherence of the universe *)
      etrans.
      2: { do 2 apply maponpaths.
           rewrite assoc.
           apply maponpaths_2.
           refine (! maponpaths
                       (λ z, ⌈ comp_cat_subst_ty_comp_iso (comp_cat_el B') L mΓ ⌉ · z)
                       (! comp_cat_univ_coherent_comp'' L mΓ B')). }
      do 4 rewrite assoc'.
      etrans.
      2: { do 2 apply maponpaths.
           rewrite assoc.
           apply maponpaths_2.
           refine (! z_iso_inv_after_z_iso
                       (comp_cat_subst_ty_comp_iso (comp_cat_el B') L mΓ)). }
      rewrite id_left.
      etrans.
      2: { apply maponpaths.
           rewrite assoc.
           apply maponpaths_2.
           refine (! comp_cat_reindex_iso_after_inv (C:=C) mΓ (comp_cat_el_iso L B')). }
      rewrite id_left.
      etrans.
      2: { rewrite assoc.
           apply maponpaths_2.
           exact (comp_cat_el_iso_natural mΓ q
                    (maponpaths (λ z, comp_cat_pb_term_univ z mΓ) q)). }
      rewrite assoc'.
      (* both sides are the same el_iso followed by coercions along paths *)
      etrans.
      { apply maponpaths.
        exact (coe_comp_cat_el_z_iso_from_eq
                 (cwf_sigma_pair_mor_from_comp_cat_with_u_subproof Γ A B)). }
      apply maponpaths.
      do 2 rewrite assoc.
      rewrite ?comp_cat_el_map_comp.
      exact (comp_cat_el_map_eq_comp3 (C:=C) _ _ _ _).
    Qed.

    Lemma comp_cat_sigma_repack
    {Γ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf)
    (BprojpairΓA :=
       ((B [[comp_cat_comp_mor (⌈comp_cat_sigma_el_iso C Sigma SigmaU Γ A⌉⁻¹)]]tm
         ↑ ⌈comp_cat_univ_sub_iso
              (comp_cat_comp_mor (⌈comp_cat_sigma_el_iso C Sigma SigmaU Γ A⌉⁻¹))⌉)
        [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)]]tm
        ↑ ⌈comp_cat_univ_sub_iso
             (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A))⌉))
    : comp_cat_comp_mor (⌈comp_cat_sigma_el_iso C Sigma SigmaU (Γ & A)%cwf B⌉)
        · comp_cat_sigma_iso_1
            (comp_cat_comp_iso (comp_cat_sigma_el_iso C Sigma SigmaU Γ A))
        · comp_cat_sigma_iso_2
            (comp_cat_comp_iso
               (z_iso_comp
                  (z_iso_comp
                     (comp_cat_el_iso
                        (comp_cat_comp_mor
                           (⌈comp_cat_sigma_el_iso C Sigma SigmaU Γ A⌉⁻¹)) B)
                     (comp_cat_el_z_iso_from_eq
                        (cwf_sigma_pair_mor_from_comp_cat_with_u_subproof Γ A B)))
                  (z_iso_inv
                     (comp_cat_el_iso
                        (comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A))
                        BprojpairΓA))))
        · comp_cat_sigma_assoc (comp_cat_el Γ) (comp_cat_el A)
            (comp_cat_el BprojpairΓA)
        · comp_cat_sigma_iso_2
            (comp_cat_comp_iso
               (z_iso_inv (comp_cat_sigma_el_iso C Sigma SigmaU A BprojpairΓA)))
        · comp_cat_comp_mor
            (⌈comp_cat_sigma_el_iso C Sigma SigmaU Γ
                (comp_cat_sigma_code C Sigma SigmaU A BprojpairΓA)⌉⁻¹)
      = comp_cat_sigma_unpack2 C Sigma SigmaU Unit UnitU A B
          · comp_cat_comp_mor (comp_cat_el_map (! Bprojpair_is_Bext C Sigma SigmaU Unit UnitU (Δ:=Γ) A B))
          · inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU A BprojpairΓA)
          · inv_from_z_iso
              (comp_cat_sigma_unpack C Sigma SigmaU _
                 (comp_cat_sigma_code C Sigma SigmaU A BprojpairΓA)).
    Proof.
      unfold comp_cat_sigma_iso_1, comp_cat_sigma_iso_2, comp_cat_sigma_unpack2, comp_cat_sigma_unpack.
      unfold comp_cat_sigma_assoc.
      etrans.
      { exact (idpath (_ · (_ · (_ · _)) · (_ · (_ · _)) · (_ · (_ · (_ · _)))
                         · (_ · (_ · _)) · _)). }
      etrans.
      2: { exact (idpath ((_ · _) · (_ · _) · _ · (_ · _) · (_ · _))). }
      do 19 rewrite assoc'.
      etrans.
      { do 3 apply maponpaths.
        rewrite assoc.
        etrans.
        { apply maponpaths_2.
          apply (z_iso_after_z_iso_inv _). }
        apply id_left. }
      etrans.
      { do 4 apply maponpaths.
        rewrite assoc.
        etrans.
        { apply maponpaths_2.
          apply (z_iso_after_z_iso_inv _). }
        apply id_left. }
      etrans.
      { do 6 apply maponpaths.
        rewrite assoc.
        etrans.
        { apply maponpaths_2.
          apply (z_iso_after_z_iso_inv _). }
        apply id_left. }
      do 2 apply maponpaths.
      do 10 rewrite assoc.
      do 4 apply maponpaths_2.
      do 2 rewrite assoc'.
      use z_iso_inv_on_right.
      do 2 rewrite assoc.
      exact (comp_cat_sigma_repack_middle A B _ _).
    Qed.

  Lemma sigma_pair_sub_lemma_after_lift
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf)
    (BprojpairΓA :=
       ((B[[comp_cat_comp_mor
              (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)
           ]]tm
           ↑ ⌈ comp_cat_univ_sub_iso
           (comp_cat_comp_mor
              (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹))
           ⌉)
          [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A) ]]tm
          ↑ ⌈ comp_cat_univ_sub_iso
          (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A))
          ⌉)) :
    comp_cat_comp_mor
      (comp_cat_el_map
         (! comp_cat_sigma_code_eq C Sigma SigmaU A
            (B [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A) ]]tm ↑ ⌈ comp_cat_univ_sub_iso (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)) ⌉)
            ((B [[comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹) ]]tm
                ↑ ⌈ comp_cat_univ_sub_iso (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)) ⌉)
               [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A) ]]tm
               ↑ ⌈ comp_cat_univ_sub_iso (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)) ⌉)
            (! Bprojpair_is_Bext C Sigma SigmaU Unit UnitU (Δ:=Γ) A B)))
      · comp_cat_comp_mor
      (⌈ comp_cat_sigma_el_iso C Sigma SigmaU A
         (B [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A) ]]tm
            ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)) ⌉)
         ⌉)
      · comp_cat_sigma_pair_proj_iso (comp_cat_el A)
      (comp_cat_el
         (B [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A) ]]tm
            ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)) ⌉))
      · z_iso_inv (comp_cat_sigma_unpack2 C Sigma SigmaU Unit UnitU A B) · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU (Γ & A)%cwf B ⌉)
      · comp_cat_sigma_iso_1 (comp_cat_comp_iso (comp_cat_sigma_el_iso C Sigma SigmaU Γ A))
      · comp_cat_sigma_iso_2
      (comp_cat_comp_iso
         (z_iso_comp
            (z_iso_comp (comp_cat_el_iso (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)) B)
               (comp_cat_el_z_iso_from_eq (cwf_sigma_pair_mor_from_comp_cat_with_u_subproof Γ A B)))
            (z_iso_inv (comp_cat_el_iso (comp_cat_sigma_proj (comp_cat_el Γ) (comp_cat_el A)) BprojpairΓA))))
      · comp_cat_sigma_assoc (comp_cat_el Γ) (comp_cat_el A) (comp_cat_el BprojpairΓA)
      · comp_cat_sigma_iso_2 (comp_cat_comp_iso (z_iso_inv (comp_cat_sigma_el_iso C Sigma SigmaU A BprojpairΓA)))
      · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ (comp_cat_sigma_code C Sigma SigmaU A BprojpairΓA) ⌉⁻¹)
    =    (z_iso_inv (comp_cat_sigma_unpack C Sigma SigmaU _ (comp_cat_sigma_code C Sigma SigmaU A BprojpairΓA))).
  Proof.
    (* the last six factors form the composite treated by [comp_cat_sigma_repack] *)
    etrans.
    { apply comp_assoc_tail6. }
    etrans.
    { apply maponpaths.
      apply comp_cat_sigma_repack. }
    (* the inverse of [unpack2] cancels against [unpack2] *)
    apply comp_cancel_z_iso_tail.
    (* the first three factors, followed by the coercion, form [unpack] for the new family *)
    etrans.
    { apply maponpaths_2.
      refine (_ @ comp_cat_sigma_unpack_el_map _
                    (Bprojpair_is_Bext C Sigma SigmaU Unit UnitU (Δ:=Γ) A B)).
      apply maponpaths_2.
      refine (assoc' _ _ _ @ _).
      apply maponpaths_2.
      do 2 apply maponpaths.
      apply comp_cat_tm_isaset. }
    apply z_iso_inv_after_z_iso.
  Qed.

  Lemma sigma_pair_sub_lemma_before_lift
    {Γ Δ : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU}
    (s : cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU ⟦ Δ, Γ ⟧)
    (A : cwf_ty Γ) (B : cwf_ty (Γ & A)%cwf)
    (ΔAs :=  (Δ & (A [[s]]))%cwf)
    (elisoAsBsA := comp_cat_sigma_el_iso C Sigma SigmaU ΔAs (B [[cwf_lift s A]])%cwf  )
    (elisoAsBsA' := ⌈ ( elisoAsBsA ) ⌉ )
    (elisoΔAs := (comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf) )
    (elisoΔAs' := ⌈ elisoΔAs ⌉ )
    (BprojpairΔAs := (((B [[cwf_lift s A]])%cwf
                         [[comp_cat_comp_mor
                             (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf ⌉⁻¹)
                         ]]tm
                         ↑ ⌈ comp_cat_univ_sub_iso
                         (comp_cat_comp_mor
                            (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf ⌉⁻¹))
                         ⌉)
                        [[comp_cat_sigma_pair (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf)
                        ]]tm
                        ↑ ⌈ comp_cat_univ_sub_iso
                        (comp_cat_sigma_pair (comp_cat_el Δ)
                           (comp_cat_el (A [[s]])%cwf))
                        ⌉))
    (projΔAs := (comp_cat_sigma_proj (Σ:=Sigma) (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf)))
    (BsA := (B [[cwf_lift s A]])%cwf)
    (elisoΔAsinv' := ⌈ elisoΔAs ⌉⁻¹ )
    (BprojpairΓA :=
       ((B[[comp_cat_comp_mor
              (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)
           ]]tm
           ↑ ⌈ comp_cat_univ_sub_iso
           (comp_cat_comp_mor
              (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹))
           ⌉)
          [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A) ]]tm
          ↑ ⌈ comp_cat_univ_sub_iso
          (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A))
          ⌉))
    :
    comp_cat_comp_mor elisoAsBsA' · comp_cat_sigma_iso_1 (comp_cat_comp_iso elisoΔAs)
      · comp_cat_sigma_iso_2
      (comp_cat_comp_iso
         (z_iso_comp
            (z_iso_comp (comp_cat_el_iso (comp_cat_comp_mor elisoΔAsinv') BsA)
               (comp_cat_el_z_iso_from_eq (cwf_sigma_pair_mor_from_comp_cat_with_u_subproof Δ (A [[s]])%cwf BsA)))
            (z_iso_inv (comp_cat_el_iso projΔAs BprojpairΔAs))))
      · comp_cat_sigma_assoc (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf) (comp_cat_el BprojpairΔAs)
      · comp_cat_sigma_iso_2 (comp_cat_comp_iso (z_iso_inv (comp_cat_sigma_el_iso C Sigma SigmaU (A [[s]])%cwf BprojpairΔAs)))
      · comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ (comp_cat_sigma_code C Sigma SigmaU (A [[s]])%cwf BprojpairΔAs) ⌉⁻¹)
      · cwf_tm_eq_to_mor (! sigma_subst_from_comp_cat_with_u Γ Δ s A B)
      · comp_cat_sigma_unpack C Sigma SigmaU _ (comp_cat_sigma_code C Sigma SigmaU A BprojpairΓA [[s ]]tm ↑ ⌈ comp_cat_univ_sub_iso s ⌉) =
      comp_cat_sigma_unpack2 C Sigma SigmaU Unit UnitU (A [[s]])%cwf (B [[cwf_lift s A ]]tm ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) (cwf_lift s A) ⌉)
        · comp_cat_comp_mor
        (comp_cat_el_map
           ((! elmaplemmacomp (pr12 C) @ (comp_cat_subst_coerce_tm_eq (cwf_lift_unpack_commute C Sigma SigmaU Unit UnitU s A)
                                            (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉)
                                            (sub_comp_cat_univ_iso_natural _ (cwf_lift_unpack_commute C Sigma SigmaU Unit UnitU s A)) B)) @ elmaplemmacomp (pr12 C)))
        · inv_from_z_iso
        (comp_cat_sigma_pair_proj_iso (comp_cat_el (A [[s ]]tm ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) s ⌉))
           (comp_cat_el
              ((B [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A) ]]tm
                  ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)) ⌉)
                 [[comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹) · comp_cat_ext_subst s (comp_cat_el A) ]]tm
                 ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) (comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹) · comp_cat_ext_subst s (comp_cat_el A))
                 ⌉)))
        · comp_cat_comp_mor
        (⌈ comp_cat_sigma_el_iso C Sigma SigmaU (A [[s ]]tm ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) s ⌉)
           ((B [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A) ]]tm
               ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)) ⌉)
              [[comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹) · comp_cat_ext_subst s (comp_cat_el A) ]]tm
              ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) (comp_cat_comp_mor (⌈ comp_cat_el_iso s A ⌉⁻¹) · comp_cat_ext_subst s (comp_cat_el A))
              ⌉)
           ⌉⁻¹)
        · comp_cat_comp_mor
        (comp_cat_el_map
           (! comp_cat_univ_sigma_subst C Sigma SigmaU s A
              (B [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A) ]]tm
                 ↑ ⌈ sub_comp_cat_univ_iso (pr112 C) (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)) ⌉)))
        · comp_cat_comp_mor
        (comp_cat_el_map
           (maponpaths (coerce_comp_cat_tm (⌈ comp_cat_univ_sub_iso s ⌉))
              (maponpaths (comp_cat_subst_tm s)
                 (comp_cat_sigma_code_eq C Sigma SigmaU A
                    (B [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A) ]]tm
                       ↑ ⌈ comp_cat_univ_sub_iso (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU _ A)) ⌉)
                    ((B [[comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹) ]]tm
                        ↑ ⌈ comp_cat_univ_sub_iso (comp_cat_comp_mor (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)) ⌉)
                       [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A) ]]tm
                       ↑ ⌈ comp_cat_univ_sub_iso (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A)) ⌉)
                    (! Bprojpair_is_Bext C Sigma SigmaU Unit UnitU (Δ:=Γ) A B))))).
  Proof.
    unfold comp_cat_sigma_unpack2.
    etrans.
    { do 2 apply maponpaths_2.
      apply comp_cat_sigma_repack. }
    do 8 rewrite assoc'.
    apply maponpaths.
    do 6 rewrite assoc.
    etrans.
    { apply maponpaths_2.
      apply maponpaths.
      apply (cwf_tm_eq_to_mor_is_el_map C Sigma SigmaU Unit UnitU). }

    set (p₁ := ! sigma_subst_from_comp_cat_with_u Γ Δ s A B).
    assert (p₂ : (((B [[cwf_lift s A]])%cwf
          [[comp_cat_comp_mor (⌈comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf⌉⁻¹)]]tm
          ↑ ⌈comp_cat_univ_sub_iso
               (comp_cat_comp_mor (⌈comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf⌉⁻¹))⌉)
         [[comp_cat_sigma_pair (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf)]]tm
         ↑ ⌈comp_cat_univ_sub_iso
              (comp_cat_sigma_pair (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf))⌉)
       =
       (B [[inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU Γ A)]]tm
        ↑ ⌈comp_cat_univ_sub_iso (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU Γ A))⌉)
       [[comp_cat_comp_mor (⌈comp_cat_el_iso s A⌉⁻¹)
         · comp_cat_ext_subst s (comp_cat_el A)]]tm
       ↑ ⌈comp_cat_univ_sub_iso
            (comp_cat_comp_mor (⌈comp_cat_el_iso s A⌉⁻¹)
               · comp_cat_ext_subst s (comp_cat_el A))⌉).
    { refine (! elmaplemmacomp (pr12 C) @ _).
      refine (_ @ elmaplemmacomp (pr12 C)).
      etrans.
      { do 2 apply maponpaths.
        exact (idpath (B [[ _ ]]tm ↑ _)). }
      rewrite !comp_cat_subst_coerce_tm.
      rewrite <- comp_cat_subst_tm_comp'.
      rewrite !comp_cat_comp_coerce_tm.
      rewrite assoc.
      refine (comp_cat_subst_coerce_tm_eq _ _ _ _ _).
      etrans.
      2: { exact (comp_cat_univ_sub_iso_comp
                (cwf_lift s A)
                (inv_from_z_iso (comp_cat_sigma_unpack C Sigma SigmaU Δ (A [[s]])%cwf))). }
      apply sub_comp_cat_univ_iso_natural. }
    do 6 rewrite assoc'.
    etrans.
    { do 2 apply maponpaths.
      rewrite assoc.
      do 2 apply maponpaths_2.
      etrans. {
        apply maponpaths.
        apply ( comp_cat_sigma_unpack_eq C Sigma SigmaU _ p₁). }
      etrans. {apply  (maponpaths (pr1) (z_iso_inv_of_z_iso_comp _ _ _ _ _ )). }
      etrans. { exact (idpath (inv_from_z_iso _ · inv_from_z_iso _)). }
      etrans. { apply maponpaths. apply  (maponpaths (pr1) (z_iso_inv_of_z_iso_comp _ _ _ _ _ )). }
      apply maponpaths. exact (idpath (inv_from_z_iso _ · inv_from_z_iso _)). }
    do 3 rewrite assoc'.
    etrans. {
      do 3 apply maponpaths.
      do 2 rewrite assoc.
      rewrite assoc4.
      rewrite comp_cat_comp_iso_inv', <- comp_cat_comp_mor_comp'.
      etrans. { apply maponpaths_2. do 2 apply maponpaths.
                rewrite (comp_cat_el_z_iso_from_eq_inv (C:=C)).
                rewrite comp_cat_el_map_comp.
                apply maponpaths.
                apply pathsinv0l. }
      rewrite comp_cat_el_map_id.
      etrans. { apply maponpaths_2. apply maponpaths. apply comp_cat_comp_mor_id. }
      rewrite id_right.
      apply z_iso_after_z_iso_inv. }
    rewrite id_right.
    rewrite <- comp_cat_comp_mor_comp', comp_cat_el_map_comp.
    rewrite comp_cat_comp_iso_inv', (comp_cat_el_z_iso_from_eq_inv (C:=C)).
    etrans.
    { apply maponpaths.
      apply maponpaths_2.
      refine (maponpaths inv_from_z_iso
              (comp_cat_sigma_unpack_eq C Sigma SigmaU (A [[s]])%cwf p₂) @ _).
      etrans. { apply (maponpaths (pr1) (z_iso_inv_of_z_iso_comp _ _ _ _ _)). }
      exact (idpath (inv_from_z_iso _ · (inv_from_z_iso _ · inv_from_z_iso _))). }
    do 5 rewrite assoc.
    etrans.
    { do 2 rewrite assoc'. do 2 apply maponpaths.
      rewrite comp_cat_comp_iso_inv', (comp_cat_el_z_iso_from_eq_inv (C:=C)), <- comp_cat_comp_mor_comp'.
      apply maponpaths.
      apply comp_cat_el_map_comp. }
    rewrite comp_cat_comp_iso_inv', (comp_cat_el_z_iso_from_eq_inv (C:=C)).
    rewrite assoc.
    etrans. {
      do 2 apply maponpaths_2.
      etrans. { refine (!_). apply comp_cat_comp_mor_comp'. }
      apply maponpaths. apply comp_cat_el_map_comp. }
    etrans.
    { do 2 apply maponpaths_2.
      refine (_ : _ =  comp_cat_comp_mor (comp_cat_el_map
                                            ((! elmaplemmacomp (pr12 C)
                                                @ (comp_cat_subst_coerce_tm_eq (cwf_lift_unpack_commute C Sigma SigmaU Unit UnitU s A)
                                                     (⌈comp_cat_univ_sub_iso _⌉) (⌈comp_cat_univ_sub_iso _⌉)
                                                     (sub_comp_cat_univ_iso_natural _ (cwf_lift_unpack_commute C Sigma SigmaU Unit UnitU s A)) B))
                                               @ elmaplemmacomp (pr12 C)))).
      do 2 apply maponpaths.
      apply comp_cat_tm_isaset. }
    unfold comp_cat_sigma_unpack.
    etrans.
    { apply maponpaths_2.
      apply maponpaths.
      etrans. { apply (maponpaths pr1 (z_iso_inv_of_z_iso_comp _ _ _ _ _)). }
      exact (idpath (z_iso_inv _ · z_iso_inv _)). }
    do 4 rewrite assoc'.
    do 5 apply maponpaths.
    apply comp_cat_tm_isaset.
    Unshelve.
    exact (cwf_lift_unpack_commute C Sigma SigmaU Unit UnitU s A).
  Qed.


  (* a helper lemma for reassociating the sigma_pair_sub *)  
  Lemma sigma_pair_sub_assoc
    {D : category}
    {a l1 l2 l3 l4 l5 l6 l7 b c d r1 r2 r3 r4 r5 x1 x2 x3 x4 x5 x6 x7 x8 x9 : D}
    {c0 : a --> l1} {iso1 : l1 --> l2} {iso2 : l2 --> l3} {ass : l3 --> l4}
    {iso2' : l4 --> l5} {cmend : l5 --> l6} {tmeq : l6 --> l7} {Us : l7 --> b}
    {lift : b --> c} {iu : c --> d}
    {u2 : a --> r1} {m1 : r1 --> r2} {ipp : r2 --> r3} {cmE : r3 --> r4}
    {m3 : r4 --> r5} {m4 : r5 --> b}
    {cmem : c --> x1} {cmsel : x1 --> x2} {pp : x2 --> x3} {zu2 : x3 --> x4}
    {cmG : x4 --> x5} {j1 : x5 --> x6} {j2 : x6 --> x7} {j3 : x7 --> x8}
    {j4 : x8 --> x9} {cml : x9 --> d}
    (E1 : c0 · iso1 · iso2 · ass · iso2' · cmend · tmeq · Us
          = u2 · m1 · ipp · cmE · m3 · m4)
    (E2 : cmem · cmsel · pp · zu2 · cmG · j1 · j2 · j3 · j4 · cml = iu)
    : c0 · ((iso1 · ((iso2 · ass) · iso2')) · cmend) · tmeq · ((Us · lift) · iu)
      = u2 · (m1 · (ipp · (cmE · (m3 · (((m4 · lift) · cmem) · (cmsel · pp)))))) · zu2
          · (cmG · ((j1 · ((j2 · j3) · j4)) · cml)).
  Proof.
    assert (H1 : c0 · ((iso1 · ((iso2 · ass) · iso2')) · cmend) · tmeq · ((Us · lift) · iu)
                 = (c0 · iso1 · iso2 · ass · iso2' · cmend · tmeq · Us) · lift · iu).
    { rewrite !assoc'.
      apply idpath. }
    assert (H2 : u2 · (m1 · (ipp · (cmE · (m3 · (((m4 · lift) · cmem) · (cmsel · pp)))))) · zu2
                   · (cmG · ((j1 · ((j2 · j3) · j4)) · cml))
                 = (u2 · m1 · ipp · cmE · m3 · m4) · lift
                     · (cmem · cmsel · pp · zu2 · cmG · j1 · j2 · j3 · j4 · cml)).
    { rewrite !assoc'.
      apply idpath. }
    rewrite H1, H2, E1, E2.
    apply idpath.
  Qed.

  Definition sigma_pair_sub_from_comp_cat_with_u
    : sigma_pair_sub_sections (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU) cwf_sigma_form_from_comp_cat_with_u
        cwf_sigma_pair_mor_from_comp_cat_with_u sigma_subst_from_comp_cat_with_u.
  Proof.
    unfold sigma_pair_sub_sections.
    intros.
    unfold cwf_sigma_pair_mor_from_comp_cat_with_u.
    unfold cwf_subst_ty_from_comp_cat_with_u, cwf_sigma_form_from_comp_cat_with_u,
      cwf_ext_con_from_comp_cat_with_u, comp_cat_pb_term_univ.
    rewrite !comp_cat_sigma_iso_2_id.
    rewrite !z_iso_id_left.

    set (ΔAs :=  (Δ & (A [[s]]))%cwf).
    set (elisoAsBsA := comp_cat_sigma_el_iso C Sigma SigmaU ΔAs (B [[cwf_lift s A]])%cwf  ).
    set (elisoAsBsA' := ⌈ ( elisoAsBsA ) ⌉ ).
    set (elisoΔAs := (comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf) ).
    set (elisoΔAs' := ⌈ elisoΔAs ⌉ ).
    set (elisoΔAsinv' := ⌈ elisoΔAs ⌉⁻¹ ).
    set (BprojpairΓA :=
           ((B[[comp_cat_comp_mor
                  (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹)
               ]]tm
               ↑ ⌈ comp_cat_univ_sub_iso
               (comp_cat_comp_mor
                  (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Γ A ⌉⁻¹))
               ⌉)
              [[comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A) ]]tm
              ↑ ⌈ comp_cat_univ_sub_iso
              (comp_cat_sigma_pair (comp_cat_el Γ) (comp_cat_el A))
              ⌉)).
    set (BprojpairΔAs := (((B [[cwf_lift s A]])%cwf
                             [[comp_cat_comp_mor
                                 (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf ⌉⁻¹)
                             ]]tm
                             ↑ ⌈ comp_cat_univ_sub_iso
                             (comp_cat_comp_mor
                                (⌈ comp_cat_sigma_el_iso C Sigma SigmaU Δ (A [[s]])%cwf ⌉⁻¹))
                             ⌉)
                            [[comp_cat_sigma_pair (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf)
                            ]]tm
                            ↑ ⌈ comp_cat_univ_sub_iso
                            (comp_cat_sigma_pair (comp_cat_el Δ)
                               (comp_cat_el (A [[s]])%cwf))
                            ⌉)).
    set (projΔAs := (comp_cat_sigma_proj (Σ:=Sigma) (comp_cat_el Δ) (comp_cat_el (A [[s]])%cwf))).
    set (As :=  (A [[s]])%cwf).
    set (BsA := (B [[cwf_lift s A]])%cwf).

    (* writing cwf_lift (cwf_lift) in terms of univ_lift *)
    rewrite (cwf_lift_cwf_lift_via_univ_lift C Sigma SigmaU Unit UnitU).
    (* the coherencec of sigma codes *)
    rewrite (comp_cat_univ_sigma_coherent' C Sigma SigmaU).
    (* writing cwf_lift in terms of univ_lift *)
    etrans.
    { apply maponpaths.
      apply (cwf_lift_via_univ_lift C Sigma SigmaU Unit UnitU). }
    fold BsA.

    (* the two lifts are the same *)
    etrans.
    2 : { do 2 apply maponpaths_2.
          do 5 rewrite assoc'.
          do 5 apply maponpaths.
          apply maponpaths_2.
          refine (!_).
          etrans. {
            apply (comp_cat_univ_lift_tm_eq (C:=C) _ _ _ (comp_cat_sigma_code_eq C Sigma SigmaU _ _ _
                                                            (!(Bprojpair_is_Bext C Sigma SigmaU Unit UnitU (Δ:=Γ) _ _ )))). }
          apply maponpaths_2.
          apply maponpaths.
          apply (idpath (comp_cat_univ_lift C s (comp_cat_sigma_code C Sigma SigmaU A _))). }
    exact (sigma_pair_sub_assoc
             (sigma_pair_sub_lemma_before_lift s A B)
             (sigma_pair_sub_lemma_after_lift (Δ:=Γ) A B)).
  Qed.

  Theorem construction_pres_sigma
    : (cwf_sigma_structure (cwf_from_comp_cat_with_u Sigma SigmaU Unit UnitU)).
  Proof.
    use make_cwf_sigma_with_sections.
    - exact cwf_sigma_form_from_comp_cat_with_u.
    - exact cwf_sigma_pair_mor_from_comp_cat_with_u.
    - exact cwf_pair_pi_from_comp_cat_with_u.
    - exact cwf_proj_mor_from_comp_cat_with_u.
    - exact cwf_beta_law_from_comp_cat_with_u.
    - exact cwf_eta_law_from_comp_cat_with_u.
    - exact sigma_subst_from_comp_cat_with_u.
    - exact sigma_pair_sub_from_comp_cat_with_u.
  Defined.

  End pair_subst.

End SigmaPreservation.
