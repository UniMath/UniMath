Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Notations.
Require Import UniMath.CategoryTheory.Bicategories.BicatAliases.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws_2.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.

Ltac is_iso :=
  match goal with
  | [ |- is_invertible_2cell (left_unit _) ] => apply is_invertible_2cell_runitor
  | [ |- is_invertible_2cell (left_unit_inv _) ] => apply is_invertible_2cell_rinvunitor
  | [ |- is_invertible_2cell (right_unit _) ] => apply is_invertible_2cell_lunitor
  | [ |- is_invertible_2cell (right_unit_inv _) ] => apply is_invertible_2cell_linvunitor
  | [ |- is_invertible_2cell (runitor _) ] => apply is_invertible_2cell_runitor
  | [ |- is_invertible_2cell (rinvunitor _) ] => apply is_invertible_2cell_rinvunitor
  | [ |- is_invertible_2cell (lunitor _) ] => apply is_invertible_2cell_lunitor
  | [ |- is_invertible_2cell (linvunitor _) ] => apply is_invertible_2cell_linvunitor
  | [ |- is_invertible_2cell (assoc _ _ _)] => apply assoc_iso
  | [ |- is_invertible_2cell (assoc_inv _ _ _)] => apply assoc_inv_iso
  | [ |- is_invertible_2cell (rassociator _ _ _)] => apply is_invertible_2cell_rassociator
  | [ |- is_invertible_2cell (lassociator _ _ _)] => apply is_invertible_2cell_lassociator
  | [ |- is_invertible_2cell (inv_cell _)] => apply iso_inverse ; is_iso
  | [ |- is_invertible_2cell (_ ^-1)] => apply iso_inverse ; is_iso
  | [ |- is_invertible_2cell (_ • _)] => apply iso_vcomp ; is_iso
  | [ |- is_invertible_2cell (_ ◃ _)] => apply is_invertible_2cell_lwhisker ; is_iso
  | [ |- is_invertible_2cell (_ ▹ _)] => apply is_invertible_2cell_rwhisker ; is_iso
  | [ |- is_invertible_2cell (_ ⋆⋆ _)] => apply hcomp_iso ; is_iso
  | [ |- is_invertible_2cell (_ ⋆ _)] => apply hcomp_iso ; is_iso
  | [ |- is_invertible_2cell (id₂ _)] => apply iso_id₂
  | _ => try assumption
  end.

Section laws.
  Context {C : bicat}.

  Definition lwhisker_hcomp
             {X Y Z : C}
             {f g : C⟦Y,Z⟧}
             (h : C⟦X, Y⟧)
             (α : f ==> g)
    : h ◃ α = id₂ h ⋆ α.
  Proof.
    unfold hcomp.
    rewrite id2_rwhisker.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition rwhisker_hcomp
             {X Y Z : C}
             {f g : C⟦X,Y⟧}
             (h : C⟦Y,Z⟧)
             (α : f ==> g)
    : α ▹ h = α ⋆ id₂ h.
  Proof.
    unfold hcomp.
    rewrite lwhisker_id2.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition inverse_pentagon
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc_inv (k ∘ h) g f o assoc_inv k h (g ∘ f)
      =
      (id₂ f ⋆ assoc_inv k h g) o (assoc_inv k (h ∘ g) f) o (assoc_inv h g f ⋆ id₂ k).
  Proof.
    rewrite <- !inverse_of_assoc.
    rewrite <- (id₂_inverse f).
    rewrite <- (id₂_inverse k).
    rewrite <- !hcomp_inverse.
    rewrite <- !vcomp_inverse.
    apply path_inverse_2cell.
    rewrite <- !vcomp_assoc.
    apply pentagon.
  Qed.

  Definition inverse_pentagon_2
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc_inv k h (g ∘ f) o   (assoc h g f ⋆ id2 k)
      =
      assoc (k ∘ h) g f o (f ◃ assoc_inv k h g) o assoc_inv k (h ∘ g) f.
  Proof.
    rewrite <- !inverse_of_assoc.
    use vcomp_move_R_Mp.
    {
      is_iso.
    }
    rewrite <- vcomp_assoc.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    rewrite <- vcomp_assoc.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    symmetry.
    pose (pentagon k h g f) as p.
    unfold assoc in * ; cbn.
    unfold hcomp in p.
    rewrite id2_rwhisker in p.
    rewrite vcomp_right_identity in p.
    exact p.
  Qed.

  Definition inverse_pentagon_3
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc_inv (k ∘ h) g f o assoc_inv k h (g ∘ f) o (id₂ k ⋆⋆ assoc h g f)
      =
      assoc_inv k h g ⋆⋆ id₂ f o assoc_inv k (h ∘ g) f.
  Proof.
    use vcomp_move_R_pM.
    {
      is_iso.
    }
    cbn.
    apply inverse_pentagon.
  Qed.

  Definition inverse_pentagon_4
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : (assoc k h g ⋆⋆ id₂ f) o assoc_inv (k ∘ h) g f
      =
      assoc_inv k (h ∘ g) f o id₂ k ⋆⋆ assoc_inv h g f o assoc k h (g ∘ f).
  Proof.
    rewrite <- !inverse_of_assoc.
    use vcomp_move_R_pM.
    {
      is_iso.
    }
    rewrite !vcomp_assoc.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vcomp_assoc.
    symmetry ; apply pentagon.
  Qed.

  Definition inverse_pentagon_5
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc (k ∘ h) g f o (assoc_inv k h g ⋆⋆ id₂ f)
      =
      assoc_inv k h (g ∘ f) o (id₂ k ⋆⋆ assoc h g f) o assoc k (h ∘ g) f.
  Proof.
    rewrite <- !inverse_of_assoc.
    use vcomp_move_R_pM.
    {
      is_iso.
    }
    rewrite !vcomp_assoc.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vcomp_assoc.
    apply pentagon.
  Qed.

  Definition inverse_pentagon_6
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc_inv k (h ∘ g) f o id₂ k ⋆⋆ assoc_inv h g f
      =
      assoc k h g ⋆⋆ id₂ f o assoc_inv (k ∘ h) g f o assoc_inv k h (g ∘ f).
  Proof.
    rewrite !vcomp_assoc.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    cbn.
    symmetry.
    rewrite <- !vcomp_assoc.
    apply inverse_pentagon.
  Qed.

  Definition pentagon_2
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc k (h ∘ g) f o assoc k h g ⋆⋆ id₂ f
      =
      id₂ k ⋆⋆ assoc_inv h g f o assoc k h (g ∘ f) o assoc (k ∘ h) g f.
  Proof.
    rewrite <- !inverse_of_assoc.
    rewrite !vcomp_assoc.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vcomp_assoc.
    symmetry ; apply pentagon.
  Qed.

  Definition triangle_r_inv
             {X Y Z : C}
             (g : C ⟦ Y, Z ⟧) (f : C ⟦ X, Y ⟧)
    : right_unit_inv g ⋆⋆ id₂ f
      =
      assoc_inv g (id₁ Y) f o id₂ g ⋆⋆ left_unit_inv f.
  Proof.
    rewrite <- inverse_of_right_unit, <- inverse_of_left_unit.
    rewrite <- inverse_of_assoc.
    rewrite <- (id₂_inverse f).
    rewrite <- (id₂_inverse g).
    rewrite <- !hcomp_inverse.
    rewrite <- vcomp_inverse.
    apply path_inverse_2cell.
    apply triangle_r.
  Qed.

  Definition triangle_l
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit g ⋆⋆ id₂ f o assoc_inv g (id₁ Y) f = id₂ g ⋆⋆ left_unit f.
  Proof.
    rewrite triangle_r.
    rewrite vcomp_assoc.
    rewrite <- inverse_of_assoc.
    rewrite vcomp_right_inverse.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition bc_whisker_r_compose
             {X Y Z : C}
             (f : C⟦X,Y⟧)
             {g₁ g₂ g₃ : C⟦Y,Z⟧}
             (p₁ : g₁ ==> g₂) (p₂ : g₂ ==> g₃)
    : (p₂ o p₁) ▻ f = (p₂ ▻ f) o (p₁ ▻ f).
  Proof.
    symmetry.
    apply lwhisker_vcomp.
  Qed.

  Definition bc_whisker_l_compose
             {X Y Z : C}
             {f₁ f₂ f₃ : C⟦X,Y⟧}
             (g : C⟦Y,Z⟧)
             (p₁ : f₁ ==> f₂) (p₂ : f₂ ==> f₃)
    : g ◅ (p₂ o p₁) = (g ◅ p₂) o (g ◅ p₁).
  Proof.
    symmetry.
    apply rwhisker_vcomp.
  Qed.

  Definition whisker_l_hcomp
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦W,X⟧)
             (α : k₁ ==> k₂)
    : assoc _ _ _ o (g ∘ f ◅ α) = g ◅ (f ◅ α) o assoc _ _ _.
  Proof.
    symmetry.
    apply rwhisker_rwhisker.
  Qed.

  Definition whisker_r_hcomp
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦Z,W⟧)
             (α : k₁ ==> k₂)
    : assoc_inv _ _ _ o (α ▻ g ∘ f) = (α ▻ g) ▻ f o assoc_inv _ _ _.
  Proof.
    use vcomp_move_R_Mp.
    {
      is_iso.
    }
    cbn.
    rewrite <- vcomp_assoc.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    cbn.
    symmetry.
    apply @lwhisker_lwhisker.
  Qed.

  Definition whisker_l_natural
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦X,Y⟧)
             (α : k₁ ==> k₂)
    : k₂ ◅ η o right_unit_inv k₂ o α = α ▻ f o (k₁ ◅ η) o right_unit_inv k₁.
  Proof.
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    rewrite !vcomp_assoc.
    rewrite right_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    apply maponpaths.
    rewrite rwhisker_hcomp.
    rewrite <- !interchange.
    rewrite !vcomp_left_identity, !vcomp_right_identity.
    reflexivity.
  Qed.

  Definition whisker_r_natural
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦Y,X⟧)
             (α : k₁ ==> k₂)
    : η ▻ k₂ o left_unit_inv k₂ o α = (f ◅ α) o (η ▻ k₁) o left_unit_inv k₁.
  Proof.
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    rewrite !vcomp_assoc.
    rewrite left_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    apply maponpaths.
    rewrite lwhisker_hcomp.
    rewrite <- !interchange.
    rewrite !vcomp_left_identity, !vcomp_right_identity.
    reflexivity.
  Qed.

  Definition whisker_l_iso_id₁
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦Y,X⟧)
             (α : k₁ ==> k₂)
             (H : is_invertible_2cell η)
    : α = left_unit k₂ o (inv_cell (η,,H) ▻ k₂) o (f ◅ α) o (η ▻ k₁) o left_unit_inv k₁.
  Proof.
    rewrite !vcomp_assoc.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vcomp_assoc.
    exact (whisker_r_natural η k₁ k₂ α).
  Qed.

  Definition whisker_r_iso_id₁
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦X,Y⟧)
             (α : k₁ ==> k₂)
             (H : is_invertible_2cell η)
    : α = right_unit k₂ o (k₂ ◅ inv_cell (η,,H)) o (α ▻ f) o (k₁ ◅ η) o right_unit_inv k₁.
  Proof.
    rewrite !vcomp_assoc.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    rewrite <- !vcomp_assoc.
    exact (whisker_l_natural η k₁ k₂ α).
  Qed.

  Definition whisker_l_eq
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦W,X⟧)
             (α β : k₁ ==> k₂)
    : f ◅ α = f ◅ β -> (g ∘ f) ◅ α = (g ∘ f) ◅ β.
  Proof.
    intros Hαβ.
    rewrite !rwhisker_hcomp.
    rewrite !rwhisker_hcomp in Hαβ.
    rewrite <- !hcomp_id₂.
    apply (vcomp_cancel_left (assoc _ _ _) _ _).
    {
      is_iso.
    }
    rewrite !assoc_natural.
    rewrite Hαβ.
    reflexivity.
  Qed.

  Definition whisker_r_eq
             {W X Y Z : C}
             {f : C⟦Y,Z⟧} {g : C⟦X,Y⟧}
             (k₁ k₂ : C⟦Z,W⟧)
             (α β : k₁ ==> k₂)
    : α ▻ f = β ▻ f -> α ▻ (f ∘ g) = β ▻ (f ∘ g).
  Proof.
    intros Hαβ.
    rewrite !lwhisker_hcomp.
    rewrite !lwhisker_hcomp in Hαβ.
    rewrite <- !hcomp_id₂.
    apply (vcomp_cancel_right (assoc _ _ _) _ _).
    {
      is_iso.
    }
    rewrite <- !assoc_natural.
    rewrite Hαβ.
    reflexivity.
  Qed.

  Definition left_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (left_unit g) ▻ f = left_unit (g ∘ f) o assoc (id₁ Z) g f.
  Proof.
    rewrite <- runitor_triangle.
    unfold assoc.
    rewrite vcomp_assoc.
    rewrite lassociator_rassociator.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition left_unit_inv_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (left_unit_inv g) ▻ f = assoc_inv (id₁ Z) g f o left_unit_inv (g ∘ f).
  Proof.
    rewrite <- rinvunitor_triangle.
    unfold assoc_inv.
    rewrite <- vcomp_assoc.
    rewrite lassociator_rassociator.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition right_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit (g ∘ f) = g ◅ (right_unit f) o assoc g f (id₁ X).
  Proof.
    symmetry.
    apply lunitor_triangle.
  Qed.


  Definition right_unit_inv_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit_inv (g ∘ f) = assoc_inv g f (id₁ X) o (g ◅ (right_unit_inv f)).
  Proof.
    use vcomp_move_L_pM.
    {
      is_iso.
    }
    cbn.
    use vcomp_move_R_Mp.
    {
      is_iso.
    }
    cbn ; unfold assoc_inv.
    rewrite <- lunitor_triangle.
    rewrite vcomp_assoc.
    rewrite rassociator_lassociator.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition right_unit_id_is_left_unit_id
             (X : C)
    : right_unit (id₁ X) = left_unit (id₁ X).
  Proof.
    apply lunitor_runitor_identity.
  Qed.


  Definition right_unit_V_id_is_left_unit_V_id
             (X : C)
    : right_unit_inv (id₁ X) = left_unit_inv (id₁ X).
  Proof.
    rewrite <- inverse_of_right_unit, <- inverse_of_left_unit.
    apply path_inverse_2cell.
    apply lunitor_runitor_identity.
  Qed.

  Definition left_unit_inv_assoc₂
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : left_unit_inv (g ∘ f) = assoc (id₁ Z) g f o (left_unit_inv g ▻ f).
  Proof.
    rewrite left_unit_inv_assoc.
    rewrite <- !vcomp_assoc.
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition triangle_l_inv
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : assoc g (id₁ Y) f o right_unit_inv g ⋆⋆ id₂ f = id₂ g ⋆⋆ left_unit_inv f.
  Proof.
    use vcomp_move_R_Mp.
    {
      is_iso.
    }
    rewrite <- inverse_of_right_unit, <- inverse_of_left_unit.
    rewrite <- (id₂_inverse f).
    rewrite <- (id₂_inverse g).
    rewrite <- !hcomp_inverse.
    rewrite <- vcomp_inverse.
    apply path_inverse_2cell.
    rewrite <- triangle_l.
    rewrite !vcomp_assoc.
    rewrite assoc_right.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.
End laws.