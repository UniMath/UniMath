Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Notations.
Require Import UniMath.CategoryTheory.Bicategories.BicatAliases.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws_2.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.

Ltac is_iso :=
  match goal with
  | [ |- is_invertible_2cell (runitor _) ] => apply is_invertible_2cell_runitor
  | [ |- is_invertible_2cell (rinvunitor _) ] => apply is_invertible_2cell_rinvunitor
  | [ |- is_invertible_2cell (lunitor _) ] => apply is_invertible_2cell_lunitor
  | [ |- is_invertible_2cell (linvunitor _) ] => apply is_invertible_2cell_linvunitor
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
    : rassociator f g (k ∘ h) o rassociator (g ∘ f) h k
      =
      (id₂ f ⋆ rassociator g h k) o (rassociator f (h ∘ g) k)
                                  o (rassociator f g h ⋆ id₂ k).
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
    : rassociator (g ∘ f) h k o (lassociator f g h ⋆ id2 k)
      =
      lassociator f g (k ∘ h) o (f ◃ rassociator g h k)
                  o rassociator f (h ∘ g) k.
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
    unfold hcomp in p.
    rewrite id2_rwhisker in p.
    rewrite vcomp_right_identity in p.
    exact p.
  Qed.

  Definition inverse_pentagon_3
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : rassociator f g (k ∘ h) o rassociator (g ∘ f) h k o (id₂ k ⋆⋆ lassociator f g h)
      =
      rassociator g h k ⋆⋆ id₂ f o rassociator f (h ∘ g) k.
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
    : (lassociator g h k ⋆⋆ id₂ f) o rassociator f g (k ∘ h)
      =
      rassociator f (h ∘ g) k o id₂ k ⋆⋆ rassociator f g h o lassociator (g ∘ f) h k.
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
    : lassociator f g (k ∘ h) o (rassociator g h k ⋆⋆ id₂ f)
      =
      rassociator (g ∘ f) h k o (id₂ k ⋆⋆ lassociator f g h) o lassociator f (h ∘ g) k.
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
    : rassociator f (h ∘ g) k o id₂ k ⋆⋆ rassociator f g h
      =
      lassociator g h k ⋆⋆ id₂ f o rassociator f g (k ∘ h) o rassociator (g ∘ f) h k.
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
    : lassociator f (h ∘ g) k o lassociator g h k ⋆⋆ id₂ f
      =
      id₂ k ⋆⋆ rassociator f g h o lassociator (g ∘ f) h k o lassociator f g (k ∘ h).
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
    : linvunitor g ⋆⋆ id₂ f
      =
      rassociator _ _ _ o id₂ g ⋆⋆ rinvunitor f.
  Proof.
    rewrite <- inverse_of_lunitor, <- inverse_of_left_unit.
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
    : lunitor g ⋆⋆ id₂ f o rassociator _ _ _ = id₂ g ⋆⋆ runitor f.
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
    : lassociator _ _ _ o (g ∘ f ◅ α) = g ◅ (f ◅ α) o lassociator _ _ _.
  Proof.
    symmetry.
    apply rwhisker_rwhisker.
  Qed.

  Definition whisker_r_hcomp
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦Z,W⟧)
             (α : k₁ ==> k₂)
    : rassociator _ _ _ o (α ▻ g ∘ f) = (α ▻ g) ▻ f o rassociator _ _ _.
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
    : k₂ ◅ η o linvunitor k₂ o α = α ▻ f o (k₁ ◅ η) o linvunitor k₁.
  Proof.
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    rewrite !vcomp_assoc.
    rewrite linvunitor_natural.
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
    : η ▻ k₂ o rinvunitor k₂ o α = (f ◅ α) o (η ▻ k₁) o rinvunitor k₁.
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
    : α = runitor k₂ o (inv_cell (η,,H) ▻ k₂) o (f ◅ α) o (η ▻ k₁) o rinvunitor k₁.
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
    : α = lunitor k₂ o (k₂ ◅ inv_cell (η,,H)) o (α ▻ f) o (k₁ ◅ η) o linvunitor k₁.
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
    apply (vcomp_cancel_left (lassociator _ _ _) _ _).
    {
      is_iso.
    }
    rewrite !hcomp_lassoc.
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
    apply (vcomp_cancel_right (lassociator _ _ _) _ _).
    {
      is_iso.
    }
    rewrite <- !hcomp_lassoc.
    rewrite Hαβ.
    reflexivity.
  Qed.

  Definition left_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (runitor g) ▻ f = runitor (g ∘ f) o lassociator f g (id₁ Z).
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
    : (rinvunitor g) ▻ f = rassociator _ _ _ o rinvunitor (g ∘ f).
  Proof.
    rewrite <- rinvunitor_triangle.
    rewrite <- vcomp_assoc.
    rewrite lassociator_rassociator.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition lunitor_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : lunitor (g ∘ f) = g ◅ (lunitor f) o lassociator (id₁ X) f g.
  Proof.
    symmetry.
    apply lunitor_triangle.
  Qed.


  Definition linvunitor_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : linvunitor (g ∘ f) = rassociator (id₁ X) f g o (g ◅ (linvunitor f)).
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
    cbn. rewrite <- lunitor_triangle.
    rewrite vcomp_assoc.
    rewrite rassociator_lassociator.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition lunitor_id_is_left_unit_id
             (X : C)
    : lunitor (id₁ X) = runitor (id₁ X).
  Proof.
    apply lunitor_runitor_identity.
  Qed.


  Definition lunitor_V_id_is_left_unit_V_id
             (X : C)
    : linvunitor (id₁ X) = rinvunitor (id₁ X).
  Proof.
    rewrite <- inverse_of_lunitor, <- inverse_of_left_unit.
    apply path_inverse_2cell.
    apply lunitor_runitor_identity.
  Qed.

  Definition left_unit_inv_assoc₂
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : rinvunitor (g ∘ f) = lassociator f g (id₁ Z) o (rinvunitor g ▻ f).
  Proof.
    rewrite left_unit_inv_assoc.
    rewrite <- !vcomp_assoc.
    rewrite rassociator_lassociator.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition triangle_l_inv
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : lassociator f (id₁ Y) g o linvunitor g ⋆⋆ id₂ f = id₂ g ⋆⋆ rinvunitor f.
  Proof.
    use vcomp_move_R_Mp.
    {
      is_iso.
    }
    rewrite <- inverse_of_lunitor, <- inverse_of_left_unit.
    rewrite <- (id₂_inverse f).
    rewrite <- (id₂_inverse g).
    rewrite <- !hcomp_inverse.
    rewrite <- vcomp_inverse.
    apply path_inverse_2cell.
    rewrite <- triangle_l.
    rewrite !vcomp_assoc.
    rewrite lassociator_rassociator.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.
End laws.
