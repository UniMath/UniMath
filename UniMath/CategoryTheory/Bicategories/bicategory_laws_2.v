Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Notations.
Require Import UniMath.CategoryTheory.Bicategories.BicatAliases.


Notation "'BiCategory'" := bicat.

Definition vcomp_assoc
           {C : BiCategory}
           {X Y : C}
           {f g h k : C⟦X,Y⟧}
           (η₃ : h ==> k)
           (η₂ : g ==> h)
           (η₁ : f ==> g)
  : (η₃ o η₂) o η₁ = η₃ o (η₂ o η₁).
Proof.
  apply vassocr.
Defined.


Definition vcomp_left_identity
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (η : f ==> g)
  : id₂ g o η = η
  := id2_right _ .

Definition vcomp_right_identity
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (η : f ==> g)
  : η o id₂ f = η
  := id2_left _ .

Definition interchange
           {C : BiCategory}
           {X Y Z : C}
           {f₁ g₁ h₁ : C⟦Y,Z⟧}
           {f₂ g₂ h₂ : C⟦X,Y⟧}
           (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
           (ε₁ : g₁ ==> h₁) (ε₂ : g₂ ==> h₂)
  : (ε₁ o η₁) ⋆⋆ (ε₂ o η₂) = (ε₁ ⋆⋆ ε₂) o (η₁ ⋆⋆ η₂).
Proof.
  apply hcomp_vcomp.
Qed.

Definition hcomp_id₂
           {C : BiCategory}
           {X Y Z : C}
           (f₂ : C⟦Y, Z⟧) (f₁ : C⟦X,Y⟧)
  : id₂ f₂ ⋆⋆ id₂ f₁ = id₂ (f₂ ∘ f₁).
Proof.
  apply hcomp_identity.
Defined.

(* see lunitor_natural *)

Definition left_unit_natural
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X, Y⟧}
           (η : f ==> g)
  : runitor g o (id₂ (id₁ Y) ⋆⋆ η) = η o runitor f.
Proof.
  apply runitor_natural.
Qed.


Definition left_unit_inv_natural
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X, Y⟧}
           (η : f ==> g)
  : rinvunitor g o η = (id₂ (id₁ Y) ⋆⋆ η) o rinvunitor f.
Proof.
Admitted.

Definition left_unit_left
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : runitor f o rinvunitor f = id₂ f.
Proof.
  apply rinvunitor_runitor.
Qed.

Definition left_unit_right
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : rinvunitor f o runitor f = id₂ (id₁ Y ∘ f).
Proof.
  apply runitor_rinvunitor.
Qed.

Definition lunitor_natural
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X, Y⟧}
           (η : f ==> g)
  : lunitor g o (η ⋆⋆ id₂ (id₁ X)) = η o lunitor f.
Proof.
  apply lunitor_natural.
Qed.

Definition linvunitor_natural
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X, Y⟧}
           (η : f ==> g)
  : linvunitor g o η = (η ⋆⋆ id₂ (id₁ X)) o linvunitor f.
Proof.
Admitted.

Definition lunitor_left
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : lunitor f o linvunitor f = id₂ f.
Proof.
  apply linvunitor_lunitor.
Qed.

Definition lunitor_right
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : linvunitor f o lunitor f = id₂ (f ∘ id₁ X).
Proof.
  apply lunitor_linvunitor.
Qed.

Definition Build_is_invertible_2cell
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           {α : f ==> g}
           (α_inv : g ==> f)
           (sect : α_inv o α = id₂ f)
           (retr : α o α_inv = id₂ g)
  : is_invertible_2cell α.
Proof.
  repeat (use tpair).
  - exact α_inv.
  - exact sect.
  - exact retr.
Defined.

(**** Two-cells that are isomorphisms **)
(*** Inverse of a two-cell **)
Definition twoinverse
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (η : f ==> g)
           (H : is_invertible_2cell η)
  : g ==> f
  := inv_cell (η,,H).

Notation "H ^-1" := (twoinverse _ H) (at level 20) : bicategory_scope.
Delimit Scope bicategory_scope with bicategory.
Bind Scope bicategory_scope with bicat.
Open Scope bicategory_scope.

Definition vcomp_left_inverse
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (η : f ==> g)
           (H : is_invertible_2cell η)
  :  H ^-1 o η = id₂ f.
Proof.
  apply (invertible_2cell_after_inv_cell ( _ ,, H)).
Defined.

Definition vcomp_right_inverse
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (η : f ==> g)
           (H : is_invertible_2cell η)
  : η o H ^-1 = id₂ g.
Proof.
  apply (inv_cell_after_invertible_2cell ( _ ,, H)).
Defined.

Definition iso_id₂
         {C : BiCategory}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (id₂ f).
Proof.
  exists (id2 _).
  split; apply id2_left.
Defined.

Definition iso_inverse
         {C : BiCategory}
         {X Y : C}
         {f g : C⟦X,Y⟧}
         (α : f ==> g)
         (H : is_invertible_2cell α)
  : is_invertible_2cell (H^-1).
Proof.
  apply inv_invertible_2cell.
Defined.

Definition iso_vcomp
         {C : BiCategory}
         {X Y : C}
         {f g h : C⟦X,Y⟧}
         (α : f ==> g)
         (β : g ==> h)
         (Hα : is_invertible_2cell α)
         (Hβ : is_invertible_2cell β)
  : is_invertible_2cell (β o α).
Proof.
  apply is_invertible_2cell_composite;
    assumption.
Defined.

Definition left_unit_iso
         {C : BiCategory}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (runitor f).
Proof.
  apply is_invertible_2cell_runitor.
Defined.

Definition left_unit_inv_iso
         {C : BiCategory}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (rinvunitor f).
Proof.
  apply is_invertible_2cell_rinvunitor.
Defined.

Definition lunitor_iso
         {C : BiCategory}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (lunitor f).
Proof.
  apply is_invertible_2cell_lunitor.
Defined.

Definition lunitor_inv_iso
         {C : BiCategory}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (linvunitor f).
Proof.
  apply is_invertible_2cell_linvunitor.
Defined.

Definition triangle_r
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧)
           (f : C⟦X,Y⟧)
  : lunitor g ⋆⋆ id₂ f = (id₂ g ⋆⋆ runitor f) o lassociator f (id₁ Y) g.
Proof.
  cbn.
  apply pathsinv0.
  unfold hcomp.
  etrans.
  { apply maponpaths.
    etrans. { apply maponpaths.
              apply lwhisker_id2. }
            apply id2_right. }
  etrans. apply runitor_rwhisker.
  apply pathsinv0.
  etrans. { apply maponpaths_2. apply id2_rwhisker. }
          apply id2_left.
Qed.

Definition pentagon
           {C : BiCategory}
           {V W X Y Z : C}
           (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧) (g : C⟦W,X⟧) (f : C⟦V,W⟧)
  : (lassociator (g ∘ f) h k o lassociator f g (k ∘ h))
    =
    (id₂ k ⋆⋆ lassociator f g h) o lassociator f (h ∘ g) k o
                                 (lassociator g h k ⋆⋆ id₂ f).
Proof.
  unfold assoc.
  unfold hcomp.
  apply pathsinv0.
  rewrite id2_rwhisker.
  rewrite id2_left.
  rewrite lwhisker_id2.
  rewrite id2_right.
  rewrite vassocr.
  apply lassociator_lassociator.
Qed.


Definition hcomp_iso
       {C : BiCategory}
       {X Y Z : C}
       {f₁ g₁ : C⟦Y,Z⟧} {f₂ g₂ : C⟦X,Y⟧}
       (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
       (Hη₁ : is_invertible_2cell η₁)
       (Hη₂ : is_invertible_2cell η₂)
  : is_invertible_2cell (η₁ ⋆⋆ η₂).
Proof.
  use Build_is_invertible_2cell.
  - exact (Hη₁^-1 ⋆⋆ Hη₂^-1).
  - rewrite <- interchange.
    rewrite !vcomp_left_inverse.
    apply hcomp_id₂.
  - rewrite <- interchange.
    rewrite !vcomp_right_inverse.
    apply hcomp_id₂.
Defined.

Definition bc_whisker_l
           {C : BiCategory}
           {X Y Z : C}
           {f₁ : C⟦X,Y⟧} {f₂ : C⟦X,Y⟧}
           (g : C⟦Y,Z⟧)
           (α : f₁ ==> f₂)
  : (g ∘ f₁) ==> (g ∘ f₂)
  := id₂ g ⋆⋆ α.

(* Notation "g '◅' α" := (bc_whisker_l g α) (at level 40) : bicategory_scope. *)

Definition bc_whisker_l_id₂
           {C : BiCategory}
           {X Y Z : C}
           (f : C⟦X,Y⟧)
           (g : C⟦Y,Z⟧)
  : g ◅ (id₂ f) = id₂ (g ∘ f).
Proof.
  apply id2_rwhisker.
Qed.

Definition bc_whisker_r
           {C : BiCategory}
           {X Y Z : C}
           {g₁ : C⟦Y,Z⟧} {g₂ : C⟦Y,Z⟧}
           (β : g₁ ==> g₂)
           (f : C⟦X,Y⟧)
  : (g₁ ∘ f) ==> (g₂ ∘ f)
  := β ⋆⋆ id₂ f.

(* Notation "β '▻' f" := (bc_whisker_r β f) (at level 40) : bicategory_scope. *)

Definition bc_whisker_r_id₂
           {C : BiCategory}
           {X Y Z : C}
           (f : C⟦X,Y⟧)
           (g : C⟦Y,Z⟧)
  : (id₂ g) ▻ f = id₂ (g ∘ f).
Proof.
  apply lwhisker_id2.
Qed.

Definition inverse_of_assoc
           {C : BiCategory}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : (is_invertible_2cell_lassociator f g h)^-1 = rassociator f g h.
Proof.
  apply idpath.
Qed.

Definition inverse_of_left_unit
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (left_unit_iso f)^-1 = rinvunitor f
  := idpath _ .

Definition inverse_of_lunitor
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (lunitor_iso f)^-1 = linvunitor f
  := idpath _.

(**** Properties of isomorphisms ***)

Definition id₂_inverse
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (iso_id₂ f)^-1 = id₂ f
  := idpath _.

Definition vcomp_inverse
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : g ==> h)
           (Hη₁ : is_invertible_2cell η₁)
           (Hη₂ : is_invertible_2cell η₂)
  : (iso_vcomp _ _ Hη₁ Hη₂)^-1 = Hη₁^-1 o Hη₂^-1
  := idpath _ .

Definition hcomp_inverse
           {C : BiCategory}
           {X Y Z : C}
           {f₁ g₁ : C⟦Y,Z⟧} {f₂ g₂ : C⟦X,Y⟧}
           (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
           (Hη₁ : is_invertible_2cell η₁)
           (Hη₂ : is_invertible_2cell η₂)
  : (hcomp_iso _ _ Hη₁ Hη₂)^-1 = Hη₁^-1 ⋆⋆ Hη₂^-1
  := idpath _ .

Definition vcomp_cancel_left
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (ε : g ==> h)
           (η₁ η₂ : f ==> g)
           (Hε : is_invertible_2cell ε)
  : ε o η₁ = ε o η₂ -> η₁ = η₂.
Proof.
  intros Hhf.
  simple refine (!(vcomp_left_identity _) @ _ @ vcomp_left_identity _).
  rewrite <- (vcomp_left_inverse ε Hε).
  rewrite !vcomp_assoc.
  rewrite Hhf.
  reflexivity.
Defined.

Definition vcomp_cancel_right
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (ε : f ==> g) (η₁ η₂ : g ==> h)
           (Hε : is_invertible_2cell ε)
  : η₁ o ε = η₂ o ε -> η₁ = η₂.
Proof.
(*
  intros Hhf.
  refine (!(vcomp_right_identity _) @ _ @ vcomp_right_identity _).
  rewrite <- (vcomp_right_inverse ε Hε).
  rewrite <- !vcomp_assoc.
  rewrite Hhf.
  reflexivity.
Defined.
 *)
  Admitted.

Definition vcomp_move_L_Vp
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : f ==> h) (ε : g ==> h)
           (Hε : is_invertible_2cell ε)
  : ε o η₁ = η₂ -> η₁ = Hε^-1 o η₂.
Proof.
  intros ?.
  rewrite <- (vcomp_left_identity η₁).
  rewrite <- (vcomp_left_inverse ε Hε).
  rewrite vcomp_assoc.
  apply maponpaths_2.
  assumption.
Qed.

Definition vcomp_move_L_pV
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : g ==> h) (η₂ : f ==> h) (ε : f ==> g)
           (Hε : is_invertible_2cell ε)
  : η₁ o ε = η₂ -> η₁ = η₂ o Hε^-1.
Proof.
  intros Hη.
  rewrite <- (vcomp_right_identity η₁).
  rewrite <- (vcomp_right_inverse ε Hε).
  rewrite <- vcomp_assoc.
  rewrite Hη.
  reflexivity.
Qed.

Definition vcomp_move_R_Mp
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : f ==> h) (ε : g ==> h)
           (Hε : is_invertible_2cell ε)
  : η₁ = Hε^-1 o η₂ -> ε o η₁ = η₂.
Proof.
  intros ?.
  rewrite <- (vcomp_left_identity η₂).
  rewrite <- (vcomp_right_inverse ε Hε).
  rewrite vcomp_assoc.
  apply maponpaths_2.
  assumption.
Qed.

Definition vcomp_move_R_pM
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : g ==> h) (η₂ : f ==> h) (ε : f ==> g)
           (Hε : is_invertible_2cell ε)
  : η₁ = η₂ o Hε^-1 -> η₁ o ε = η₂.
Proof.
  intros Hη.
  rewrite <- (vcomp_right_identity η₂).
  rewrite <- (vcomp_left_inverse ε Hε).
  rewrite <- vcomp_assoc.
  rewrite Hη.
  reflexivity.
Qed.

Definition vcomp_move_L_Mp
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> h) (η₂ : f ==> g) (ε : g ==> h)
           (Hε : is_invertible_2cell ε)
  : Hε^-1 o η₁ = η₂ -> η₁ = ε o η₂.
Proof.
  intros ?.
  rewrite <- (vcomp_left_identity η₁).
  rewrite <- (vcomp_right_inverse ε Hε).
  rewrite vcomp_assoc.
  apply maponpaths_2.
  assumption.
Qed.

Definition vcomp_move_L_pM
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> h) (η₂ : g ==> h) (ε : f ==> g)
           (Hε : is_invertible_2cell ε)
  : η₁ o Hε^-1 = η₂ -> η₁ = η₂ o ε.
Proof.
  intros Hη.
  rewrite <- (vcomp_right_identity η₁).
  rewrite <- (vcomp_left_inverse ε Hε).
  rewrite <- vcomp_assoc.
  rewrite Hη.
  reflexivity.
Qed.

Definition path_inverse_2cell
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (η₁ η₂ : f ==> g)
           {Hη₁ : is_invertible_2cell η₁}
           {Hη₂ : is_invertible_2cell η₂}
  : η₁ = η₂ -> Hη₁^-1 = Hη₂^-1.
Proof.
  intros p.
  rewrite <- (vcomp_right_identity (Hη₁^-1)).
  rewrite <- (vcomp_left_identity (Hη₂^-1)).
  rewrite <- (vcomp_right_inverse η₂ Hη₂).
  rewrite <- vcomp_assoc.
  apply maponpaths.
  rewrite <- p.
  apply vcomp_left_inverse.
Defined.
