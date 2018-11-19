Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Notations.
Require Import UniMath.CategoryTheory.Bicategories.BicatAliases.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws_2.

Section laws.
  Context {C : bicat}.

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
    simple refine (vcomp_move_R_Mp _ _ _ _ _) ; simpl.
    {
      cbn.
      apply assoc_inv_iso.
    }
    rewrite <- vcomp_assoc.
    simple refine (vcomp_move_L_pM _ _ _ _ _).
    {
      cbn.
      apply assoc_inv_iso.
    }
    rewrite <- vcomp_assoc.
    simple refine (vcomp_move_L_pM _ _ _ _ _).
    { cbn.
      apply is_invertible_2cell_lwhisker.
      apply assoc_inv_iso.
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
    simple refine (vcomp_move_R_pM _ _ _ _ _).
    { apply hcomp_iso.
      - apply iso_id₂.
      - apply assoc_iso.
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
    simple refine (vcomp_move_R_pM _ _ _ _ _).
    {
      cbn.
      apply assoc_inv_iso.
    }
    rewrite !vcomp_assoc.
    simple refine (vcomp_move_L_Mp _ _ _ _ _).
    {
      cbn.
      apply assoc_inv_iso.
    }
    simple refine (vcomp_move_L_Mp _ _ _ _ _).
    {
      cbn.
      apply hcomp_iso.
      - apply iso_id₂.
      - apply assoc_inv_iso.
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
    simple refine (vcomp_move_R_pM _ _ _ _ _).
    {
      cbn.
      apply hcomp_iso.
      - apply assoc_inv_iso.
      - apply iso_id₂.
    }
    rewrite !vcomp_assoc.
    simple refine (vcomp_move_L_Mp _ _ _ _ _).
    {
      cbn.
      apply assoc_inv_iso.
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
    simple refine (vcomp_move_L_Mp _ _ _ _ _).
    {
      apply hcomp_iso.
      - apply assoc_iso.
      - apply iso_id₂.
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
    simple refine (vcomp_move_L_Mp _ _ _ _ _).
    {
      cbn.
      apply hcomp_iso.
      - apply iso_id₂.
      - apply assoc_inv_iso.
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

  Definition whisker_l_cancel_id
             {X Y : C}
             {f g : C⟦X,Y⟧}
             (η₁ η₂ : f ==> g)
             (Hη : (id₁ Y) ◅ η₁ = (id₁ Y) ◅ η₂)
    : η₁ = η₂.
  Proof.
    (*
    refine ((vcomp_left_identity η₁)^ @ _ @ vcomp_left_identity η₂).
    rewrite <- !left_unit_left.
    rewrite !vcomp_assoc.
    rewrite (left_unit_inv_natural η₁), (left_unit_inv_natural η₂).
    unfold bc_whisker_l in Hη.
    rewrite Hη.
    reflexivity.
  Qed.
*)
  Admitted.

  Definition whisker_r_cancel_id
             {X Y : C}
             {f g : C⟦X,Y⟧}
             (η₁ η₂ : f ==> g)
             (Hη : η₁ ▻ (id₁ X) = η₂ ▻ (id₁ X))
    : η₁ = η₂.
  Proof.
    (*
    refine ((vcomp_right_identity η₁)^ @ _ @ vcomp_right_identity η₂).
    rewrite <- !right_unit_left.
    rewrite <- !vcomp_assoc.
    rewrite <- (right_unit_natural η₁), <- (right_unit_natural η₂).
    unfold bc_whisker_r in Hη.
    rewrite Hη.
    reflexivity.
  Qed.
     *)
  Admitted.

  Definition whisker_l_id₁
             {X Y : C}
             (f g : C⟦X,Y⟧)
             (α : f ==> g)
    : α = left_unit g o (id₁ Y ◅ α) o left_unit_inv f.
  Proof.
    (*
    rewrite left_unit_natural.
    rewrite !vcomp_assoc.
    rewrite !left_unit_left.
    rewrite vcomp_right_identity.
    reflexivity.
  Defined.
     *)
  Admitted.

  Definition whisker_r_id₁
             {X Y : C}
             (f g : C⟦X,Y⟧)
             (α : f ==> g)
    : α = right_unit g o (α ▻ id₁ X) o right_unit_inv f.
  Proof.
    (*
    rewrite right_unit_natural.
    rewrite !vcomp_assoc.
    rewrite !right_unit_left.
    rewrite vcomp_right_identity.
    reflexivity.
  Defined.
     *)
  Admitted.

  Definition whisker_l_hcomp
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦W,X⟧)
             (α : k₁ ==> k₂)
    : assoc _ _ _ o (g ∘ f ◅ α) = g ◅ (f ◅ α) o assoc _ _ _.
  Proof.
    (*
    unfold bc_whisker_l.
    rewrite <- hcomp_id₂.
    rewrite assoc_natural.
    reflexivity.
  Qed.
     *)
  Admitted.

  Definition whisker_r_hcomp
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦Z,W⟧)
             (α : k₁ ==> k₂)
    : assoc_inv _ _ _ o (α ▻ g ∘ f) = (α ▻ g) ▻ f o assoc_inv _ _ _.
  Proof.
    (*
    unfold bc_whisker_r.
    rewrite <- hcomp_id₂.
    rewrite assoc_inv_natural.
    reflexivity.
  Qed.
     *)
  Admitted.

  Definition whisker_l_natural
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦X,Y⟧)
             (α : k₁ ==> k₂)
    : k₂ ◅ η o right_unit_inv k₂ o α = α ▻ f o (k₁ ◅ η) o right_unit_inv k₁.
  Proof.
    (*
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !vcomp_assoc.
    rewrite right_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite <- !interchange.
    rewrite !vcomp_left_identity, !vcomp_right_identity.
    reflexivity.
  Qed.
     *)
  Admitted.

  Definition whisker_r_natural
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦Y,X⟧)
             (α : k₁ ==> k₂)
    : η ▻ k₂ o left_unit_inv k₂ o α = (f ◅ α) o (η ▻ k₁) o left_unit_inv k₁.
  Proof.
    (*
    unfold bc_whisker_l, bc_whisker_r.
    rewrite !vcomp_assoc.
    rewrite left_unit_inv_natural.
    rewrite <- !vcomp_assoc.
    f_ap.
    rewrite <- !interchange.
    rewrite !vcomp_left_identity, !vcomp_right_identity.
    reflexivity.
  Qed.
     *)
  Admitted.

  Definition whisker_l_iso_id₁
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦Y,X⟧)
             (α : k₁ ==> k₂)
             (H : is_invertible_2cell η)
    : α = left_unit k₂ o (inv_cell (η,,H) ▻ k₂) o (f ◅ α) o (η ▻ k₁) o left_unit_inv k₁.
  Proof.
    (*
    rewrite !vcomp_assoc.
    refine (vcomp_move_L_Mp _ _ _ _).
    refine (vcomp_move_L_Mp _ _ _ _).
    rewrite <- !vcomp_assoc.
    exact (whisker_r_natural η k₁ k₂ α).
  Qed.
     *)
  Admitted.

  Definition whisker_r_iso_id₁
             {X Y : C}
             {f : C⟦X,X⟧}
             (η : id₁ X ==> f)
             (k₁ k₂ : C⟦X,Y⟧)
             (α : k₁ ==> k₂)
             (H : is_invertible_2cell η)
    : α = right_unit k₂ o (k₂ ◅ inv_cell (η,,H)) o (α ▻ f) o (k₁ ◅ η) o right_unit_inv k₁.
  Proof.
    (*
    rewrite !vcomp_assoc.
    refine (vcomp_move_L_Mp _ _ _ _).
    refine (vcomp_move_L_Mp _ _ _ _).
    rewrite <- !vcomp_assoc.
    exact (whisker_l_natural η k₁ k₂ α).
  Qed.
     *)
  Admitted.

  Definition whisker_l_eq
             {W X Y Z : C}
             {f : C⟦X,Y⟧} {g : C⟦Y,Z⟧}
             (k₁ k₂ : C⟦W,X⟧)
             (α β : k₁ ==> k₂)
    : f ◅ α = f ◅ β -> (g ∘ f) ◅ α = (g ∘ f) ◅ β.
  Proof.
    (*
    intros Hαβ.
    unfold bc_whisker_l in ⋆⋆.
    rewrite <- !hcomp_id₂.
    apply (vcomp_cancel_left (assoc _ _ _) _ _).
    rewrite !assoc_natural.
    rewrite Hαβ.
    reflexivity.
  Qed.
     *)
  Admitted.
  Definition whisker_r_eq
             {W X Y Z : C}
             {f : C⟦Y,Z⟧} {g : C⟦X,Y⟧}
             (k₁ k₂ : C⟦Z,W⟧)
             (α β : k₁ ==> k₂)
    : α ▻ f = β ▻ f -> α ▻ (f ∘ g) = β ▻ (f ∘ g).
  Proof.
    (*
    intros Hαβ.
    unfold bc_whisker_r in ⋆⋆.
    rewrite <- !hcomp_id₂.
    apply (vcomp_cancel_right (assoc _ _ _) _ _).
    rewrite <- !assoc_natural.
    rewrite Hαβ.
    reflexivity.
  Qed.
     *)
  Admitted.

  Definition left_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (left_unit g) ▻ f = left_unit (g ∘ f) o assoc (id₁ Z) g f.
  Proof.
    (*
    apply whisker_l_cancel_id.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite <- (vcomp_left_identity (id₂ (id₁ Z))).
    rewrite interchange.
    refine (vcomp_cancel_right (assoc _ _ _) _ _ _).
    refine (vcomp_cancel_right (assoc _ _ _ ⋆⋆ id₂ _) _ _ _).
    rewrite vcomp_left_identity.
    rewrite <- assoc_natural.
    rewrite <- triangle_l.
    rewrite !vcomp_assoc.
    rewrite <- interchange.
    rewrite vcomp_left_identity.
    pose (pentagon (id₁ Z) (id₁ Z) g f) as p.
    rewrite !vcomp_assoc in p.
    rewrite <- p ; clear p.
    rewrite <- !vcomp_assoc.
    rewrite <- triangle_r.
    rewrite !vcomp_assoc.
    rewrite assoc_right.
    rewrite vcomp_right_identity.
    rewrite assoc_natural.
    rewrite hcomp_id₂.
    reflexivity.
  Qed.
     *)
  Admitted.

  Definition left_unit_inv_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (left_unit_inv g) ▻ f = assoc_inv (id₁ Z) g f o left_unit_inv (g ∘ f).
  Proof.
    (*
    unfold bc_whisker_r.
    rewrite <- !inverse_of_left_unit.
    rewrite <- inverse_of_assoc.
    rewrite <- vcomp_inverse.
    rewrite <- id₂_inverse.
    rewrite <- hcomp_inverse.
    apply path_inverse_2cell.
    apply left_unit_assoc.
  Qed.
     *)
  Admitted.

  Definition right_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit (g ∘ f) = g ◅ (right_unit f) o assoc g f (id₁ X).
  Proof.
    (*
    apply whisker_r_cancel_id.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite <- (vcomp_left_identity (id₂ (id₁ X))).
    rewrite interchange.
    refine (vcomp_cancel_left (assoc _ _ _) _ _ _).
    rewrite <- !vcomp_assoc.
    rewrite assoc_natural.
    rewrite triangle_r.
    rewrite <- (vcomp_left_identity (id₂ g)).
    rewrite interchange.
    rewrite !vcomp_assoc.
    pose (pentagon g f (id₁ X) (id₁ X)) as p.
    rewrite !vcomp_assoc in p.
    rewrite <- p ; clear p.
    rewrite vcomp_right_identity.
    rewrite <- !vcomp_assoc.
    rewrite <- assoc_natural.
    rewrite hcomp_id₂.
    rewrite <- triangle_l.
    rewrite !vcomp_assoc.
    rewrite assoc_right.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.
     *)
  Admitted.


  Definition right_unit_inv_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit_inv (g ∘ f) = assoc_inv g f (id₁ X) o (g ◅ (right_unit_inv f)).
  Proof.
    (*
    unfold bc_whisker_l.
    rewrite <- !inverse_of_right_unit.
    rewrite <- inverse_of_assoc.
    rewrite <- id₂_inverse.
    rewrite <- hcomp_inverse.
    rewrite <- vcomp_inverse.
    apply path_inverse_2cell.
    apply right_unit_assoc.
  Qed.
     *)
  Admitted.

  Definition right_unit_id_is_left_unit_id
             (X : C)
    : right_unit (id₁ X) = left_unit (id₁ X).
  Proof.
    (*
    apply whisker_l_cancel_id.
    refine (_ @ vcomp_right_identity _).
    rewrite <- assoc_left.
    rewrite <- vcomp_assoc.
    rewrite <- inverse_of_assoc.
    apply vcomp_move_L_pV.
    rewrite <- triangle_r.
    refine ((vcomp_left_identity _)^ @ _ @ vcomp_left_identity _).
    rewrite <- right_unit_right.
    rewrite !vcomp_assoc.
    apply ap.
    pose @right_unit_assoc as p.
    rewrite <- p ; clear p.
    rewrite (right_unit_natural (right_unit (id₁ X))).
    reflexivity.
  Qed.
     *)
  Admitted.


  Definition right_unit_V_id_is_left_unit_V_id
             (X : C)
    : right_unit_inv (id₁ X) = left_unit_inv (id₁ X).
  Proof.
    (*
    symmetry.
    refine ((vcomp_right_identity _)^ @ _ @ vcomp_left_identity _).
    rewrite <- right_unit_left.
    rewrite <- vcomp_assoc.
    f_ap.
    rewrite right_unit_id_is_left_unit_id.
    apply left_unit_right.
  Qed.
     *)
  Admitted.


  Definition left_unit_inv_assoc₂
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : left_unit_inv (g ∘ f) = assoc (id₁ Z) g f o (left_unit_inv g ▻ f).
  Proof.
    (*
    rewrite left_unit_inv_assoc.
    rewrite <- !vcomp_assoc.
    rewrite assoc_left.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.
     *)
  Admitted.


  Definition triangle_l_inv
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : assoc g (id₁ Y) f o right_unit_inv g ⋆⋆ id₂ f = id₂ g ⋆⋆ left_unit_inv f.
  Proof.
    (*
    refine (vcomp_move_R_Mp _ _ _ _).
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
     *)
  Admitted.

End laws.