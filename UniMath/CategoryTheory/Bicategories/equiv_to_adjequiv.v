(**
Internal equivalences in bicategories can be refined to adjoint equivalences.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.BicatAliases.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws_2.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.

Definition representable_faithful
           {C : bicat}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g ∘ f)
           (k₁ k₂ : C⟦Z,X⟧)
           (α β : k₁ ==> k₂)
           (Hη : is_invertible_2cell η)
  : f ◅ α = f ◅ β -> α = β.
Proof.
  intros Hαβ.
  rewrite (whisker_l_iso_id₁ η _ _ α Hη).
  rewrite (whisker_l_iso_id₁ η _ _ β Hη).
  rewrite (whisker_l_eq k₁ k₂ α β Hαβ).
  reflexivity.
Qed.

Definition representable_full
           {C : bicat}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g ∘ f)
           (θ : f ∘ g ==> id₁ Y)
           (Hη : is_invertible_2cell η)
           (k₁ k₂ : C⟦Z,X⟧)
           (α : f ∘ k₁ ==> f ∘ k₂)
  : k₁ ==> k₂.
Proof.
  refine (_ o rinvunitor _).
  refine (_ o η ▻ _).
  refine (_ o lassociator _ _ _).
  refine (_ o g ◅ α).
  refine (_ o rassociator _ _ _).
  refine (_ o Hη^-1 ▻ k₂).
  apply runitor.
Defined.

Definition full_spec
           {C : bicat}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g ∘ f)
           (θ : f ∘ g ==> id₁ Y)
           (Hη : is_invertible_2cell η)
           (Hθ : is_invertible_2cell θ)
           (k₁ k₂ : C⟦Z,X⟧)
           (α : f ∘ k₁ ==> f ∘ k₂)
  : f ◅ (representable_full η θ Hη k₁ k₂ α) = α.
Proof.
  refine (representable_faithful (Hθ^-1) (f ∘ k₁) (f ∘ k₂) _ α _ _).
  { is_iso. }
  apply (vcomp_cancel_right (assoc _ _ _) _ _).
  { is_iso. }
  rewrite <- whisker_l_hcomp.
  apply (vcomp_cancel_left (assoc_inv _ _ _) _ _).
  { is_iso. }
  rewrite <- !vcomp_assoc.
  rewrite assoc_right, vcomp_left_identity.
  apply (vcomp_cancel_left (Hη^-1 ▻ k₂) _ _).
  { is_iso. }
  apply (vcomp_cancel_left (runitor k₂) _ _).
  { is_iso. }
  apply (vcomp_cancel_right (η ▻ k₁) _ _).
  { is_iso. }
  apply (vcomp_cancel_right (rinvunitor k₁) _ _).
  { is_iso. }
  rewrite <- !vcomp_assoc.
  unfold twoinverse.
  rewrite <- (whisker_l_iso_id₁ η k₁ k₂ (representable_full η θ Hη k₁ k₂ α) Hη).
  reflexivity.
Qed.

Section EquivToAdjEquiv.
  Context {C : bicat}
          {X Y : C}.
  Variable (Hf : internal_equivalence X Y).

  Local Definition f : C⟦X,Y⟧ := internal_left_adjoint Hf.
  Local Definition g : C⟦Y,X⟧ := internal_right_adjoint Hf.
  Local Definition η : id₁ X ==> g ∘ f := internal_unit Hf.
  Local Definition θ : f ∘ g ==> id₁ Y := internal_counit Hf.
  Local Definition ηiso := internal_unit_iso Hf.
  Local Definition θiso := internal_counit_iso Hf.

  Local Definition ε : f ∘ g ==> id₁ Y.
  Proof.
    refine (representable_full (θiso^-1) (ηiso^-1) _ (f ∘ g) (id₁ Y) _).
    { is_iso. }
    exact ((linvunitor g)
             o runitor g
             o ηiso^-1 ▻ g
             o assoc_inv _ _ _).
  Defined.

  Definition εiso : is_invertible_2cell ε.
  Proof.
    unfold ε, representable_full.
    is_iso.
  Defined.

  Definition equiv_to_adjequiv_d : internal_adjunction_over f (internal_right_adjoint Hf).
  Proof.
    split.
    - exact η.
    - exact ε.
  Defined.

  Local Definition first_triangle_law
    : (lunitor g)
        o g ◅ ε
        o assoc g f g
        o η ▻ g
        o rinvunitor _
      = id₂ g.
  Proof.
    rewrite !vcomp_assoc.
    unfold ε.
    rewrite (full_spec (θiso^-1) (ηiso^-1) _ (iso_inverse _ _) (f ∘ g) (id₁ Y) _).
    rewrite <- !vcomp_assoc.
    rewrite linvunitor_lunitor, vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite !(maponpaths (fun z => _ o (_ o z)) (!(vcomp_assoc _ _ _))).
    rewrite assoc_right, vcomp_left_identity.
    rewrite !(maponpaths (fun z => _ o z) (!(vcomp_assoc _ _ _))).
    rewrite lwhisker_vcomp.
    rewrite vcomp_left_inverse.
    rewrite lwhisker_id2.
    rewrite vcomp_left_identity.
    rewrite rinvunitor_runitor.
    reflexivity.
  Qed.

  Local Definition whisker_ηg_type
    : Type.
  Proof.
    refine (η ▻ g = inv_cell ((lunitor g o g ◅ ε o lassociator g f g) ,, _) o runitor g).
    unfold ε, representable_full.
    is_iso.
  Defined.


  Local Definition whisker_ηg
    : whisker_ηg_type.
  Proof.
    use vcomp_move_L_Mp.
    { cbn.
      is_iso.
      - apply Hf.
      - apply Hf.
    }
    cbn.
    refine (_ @ vcomp_left_identity _).
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    apply first_triangle_law.
  Qed.

  Local Definition η_natural
    : η ▻ (g ∘ f) o rinvunitor (g ∘ f) o η
      =
      (g ∘ f) ◅ η o linvunitor (g ∘ f) o η.
  Proof.
    rewrite !vcomp_assoc.
    rewrite left_unit_inv_natural.
    rewrite linvunitor_natural.
    rewrite <- !vcomp_assoc.
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    rewrite <- !interchange.
    rewrite !vcomp_right_identity, !vcomp_left_identity.
    rewrite lunitor_V_id_is_left_unit_V_id.
    reflexivity.
  Qed.

  Local Definition η_natural_help
    : η ▻ (g ∘ f) o rinvunitor (g ∘ f)
      =
      (g ∘ f) ◅ η o linvunitor (g ∘ f)
    := vcomp_cancel_right η _ _ ηiso η_natural.

  Local Definition η_whisker_l_hcomp
    : (g ∘ f) ◅ η = rassociator (g ∘ f) f g o g ◅ (f ◅ η) o lassociator (id₁ X) f g.
  Proof.
    rewrite !vcomp_assoc.
    use vcomp_move_L_Mp.
    { is_iso. }
    cbn.
    rewrite rwhisker_rwhisker.
    reflexivity.
  Qed.

  Local Definition η_whisker_r_hcomp
    : η ▻ (g ∘ f) = lassociator f g(g ∘ f) o η ▻ g ▻ f o rassociator f g (id₁ X).
  Proof.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite lwhisker_lwhisker.
    reflexivity.
  Qed.

  Local Definition help1
    : lassociator f g (g ∘ f) o (η ▻ g o rinvunitor _) ▻ f
      =
      (rassociator (g ∘ f) f g)
        o g ◅ (f ◅ η)
        o lassociator (id₁ X) f g
        o linvunitor (g ∘ f).
  Proof.
    rewrite <- η_whisker_l_hcomp.
    rewrite <- lwhisker_vcomp.
    rewrite left_unit_inv_assoc.
    unfold assoc_inv.
    rewrite <- !vcomp_assoc.
    rewrite lwhisker_lwhisker.
    rewrite !vcomp_assoc.
    rewrite !(maponpaths (fun z => _ o z) (!(vcomp_assoc _ _ _))).
    rewrite rassociator_lassociator, vcomp_left_identity.
    exact η_natural_help.
  Qed.

  Local Definition help2
    : g ◅ (lassociator f g f o εiso^-1 ▻ f o rinvunitor _)
      =
      g ◅ (f ◅ η o linvunitor f).
  Proof.
    rewrite <- !rwhisker_vcomp.
    rewrite !vcomp_assoc.
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    rewrite <- triangle_l_inv.
    rewrite !(maponpaths (fun z => _ o z) (!(vcomp_assoc _ _ _))).
    unfold assoc.
    rewrite <- !lwhisker_hcomp.
    rewrite <- rwhisker_lwhisker.
    pose help1 as p.
    rewrite whisker_ηg in p.
    cbn in p.
    rewrite !vcomp_assoc in p.
    rewrite rinvunitor_runitor, vcomp_right_identity in p.
    rewrite <- !lwhisker_vcomp in p.
    rewrite linvunitor_assoc in p.
    unfold assoc_inv in p.
    rewrite <- !vcomp_assoc in p.
    rewrite !vcomp_assoc in p.
    rewrite !(maponpaths (fun z => _ o (_ o z)) (!(vcomp_assoc _ _ _))) in p.
    rewrite rassociator_lassociator, vcomp_left_identity in p.
    rewrite <- bc_whisker_l_compose in p.
    rewrite <- !vcomp_assoc in p.
    pose @inverse_pentagon_5 as q.
    unfold assoc_inv, assoc in q.
    rewrite !lwhisker_hcomp in p.
    rewrite q in p ; clear q.
    rewrite !vcomp_assoc in p.
    use (inv_2cell_right_cancellable (rassociator (f · g) f g)).
    { is_iso. }
    rewrite rwhisker_vcomp.
    refine (_ @ p) ; clear p.
    cbn.
    rewrite !vcomp_assoc, !lwhisker_hcomp, !rwhisker_hcomp.
    reflexivity.
  Qed.

  Local Definition help3
    : lassociator f g f o εiso^-1 ▻ f o rinvunitor f
      =
      f ◅ η o linvunitor f.
  Proof.
    use (representable_faithful _ _ _ _ _ _ help2).
    - exact f.
    - exact (εiso^-1).
    - is_iso.
  Qed.

  Definition equiv_to_adjequiv_isadj : is_internal_adjunction equiv_to_adjequiv_d.
  Proof.
    split ; cbn.
    - refine (maponpaths (fun z => ((z • _) • _) • _) (!help3) @ _).
      rewrite !vcomp_assoc.
      rewrite !(maponpaths (fun z => _ o (_ o z)) (!(vcomp_assoc _ _ _))).
      rewrite lassociator_rassociator, vcomp_left_identity.
      rewrite !(maponpaths (fun z => _ o z) (!(vcomp_assoc _ _ _))).
      rewrite lwhisker_vcomp.
      rewrite vcomp_right_inverse.
      rewrite lwhisker_id2.
      rewrite vcomp_left_identity.
      rewrite rinvunitor_runitor.
      reflexivity.
    - rewrite <- !vcomp_assoc.
      exact first_triangle_law.
  Defined.

  Definition equiv_to_adjequiv : internal_adjoint_equivalence X Y.
  Proof.
    refine (f ,, _).
    use tpair.
    - exact (internal_right_adjoint Hf).
    - cbn.
      refine (equiv_to_adjequiv_d ,, _).
      split.
      + split.
        * exact ηiso.
        * exact εiso.
      + exact equiv_to_adjequiv_isadj.
  Defined.
End EquivToAdjEquiv.

Definition comp_adjequiv
           {C : bicat}
           {X Y Z : C}
           (f : internal_adjoint_equivalence X Y)
           (g : internal_adjoint_equivalence Y Z)
  : internal_adjoint_equivalence X Z.
Proof.
  use equiv_to_adjequiv.
  use comp_equiv.
  - exact Y.
  - apply internal_equivalence_from_internal_adjoint_equivalence.
    apply g.
  - apply internal_equivalence_from_internal_adjoint_equivalence.
    apply f.
Defined.