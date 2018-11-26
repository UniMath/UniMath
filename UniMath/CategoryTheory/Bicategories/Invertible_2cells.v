Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Notations.

Local Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** * Inverse 2cell of a composition                                                   *)
(* ----------------------------------------------------------------------------------- *)

Lemma is_invertible_2cell_vcomp {C : prebicat} {a b : C} {f g h: C ⟦a, b⟧}
      (x : f ==> g) (y : g ==> h)
      (inv_x : is_invertible_2cell x) (inv_y : is_invertible_2cell y)
  : is_invertible_2cell (x • y).
Proof.
  exists (inv_y^-1 • inv_x^-1).
  split.
  - abstract (
        repeat rewrite vassocl;
        etrans; [apply vassoc4|];
        etrans; [ apply maponpaths_2, maponpaths;
                  apply (vcomp_rinv inv_y) |];
        rewrite id2_right;
        apply  (vcomp_rinv inv_x)
      ).
  - abstract (
        repeat rewrite vassocl;
        etrans; [apply vassoc4|];
        etrans; [ apply maponpaths_2, maponpaths;
                  apply (vcomp_lid inv_x) |];
        rewrite id2_right;
        apply  (vcomp_lid inv_y)
      ).
Defined.

Lemma inv_cell_of_composite {C : prebicat} {a b : C} {f g h: C ⟦a, b⟧}
      (x : f ==> g) (y : g ==> h)
      (inv_x : is_invertible_2cell x) (inv_y : is_invertible_2cell y)
  : is_invertible_2cell_vcomp _ _ inv_x inv_y ^-1 =
    inv_y^-1 • inv_x^-1.
Proof.
  cbn. apply idpath.
Defined.

Lemma is_invertible_2cell_lwhisker {C : prebicat} {a b c : C} (f : a --> b) {g1 g2 : b --> c}
      {x : g1 ==> g2} (inv_x : is_invertible_2cell x)
  : is_invertible_2cell (f ◃ x).
Proof.
  exists (f ◃ inv_x^-1).
  split.
  - abstract (
        etrans; [ apply lwhisker_vcomp |];
        etrans; [ apply maponpaths; apply (vcomp_rinv inv_x) |];
        apply lwhisker_id2).
  - abstract (
        etrans; [ apply lwhisker_vcomp |];
        etrans; [ apply maponpaths; apply (vcomp_lid inv_x) |];
        apply lwhisker_id2).
Defined.

Lemma is_invertible_2cell_rwhisker {C : prebicat} {a b c : C} {f1 f2 : a --> b} (g : b --> c)
      {x : f1 ==> f2} (inv_x : is_invertible_2cell x)
  : is_invertible_2cell (x ▹ g).
Proof.
  exists (inv_x^-1 ▹ g).
  split.
  - abstract (
        etrans; [ apply rwhisker_vcomp |];
        etrans; [ apply maponpaths; apply (vcomp_rinv inv_x) |];
        apply id2_rwhisker).
  - abstract (
        etrans; [ apply rwhisker_vcomp |];
        etrans; [ apply maponpaths; apply (vcomp_lid inv_x) |];
        apply id2_rwhisker).
Defined.

(** ** Two-cells that are isomorphisms **)

Definition iso_id₂
         {C : bicat}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (id₂ f).
Proof.
  exists (id2 _).
  split; apply id2_left.
Defined.

Definition left_unit_iso
         {C : bicat}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (runitor f).
Proof.
  apply is_invertible_2cell_runitor.
Defined.

Definition left_unit_inv_iso
         {C : bicat}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (rinvunitor f).
Proof.
  apply is_invertible_2cell_rinvunitor.
Defined.

Definition lunitor_iso
         {C : bicat}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (lunitor f).
Proof.
  apply is_invertible_2cell_lunitor.
Defined.

Definition lunitor_inv_iso
         {C : bicat}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : is_invertible_2cell (linvunitor f).
Proof.
  apply is_invertible_2cell_linvunitor.
Defined.


Definition pentagon
           {C : bicat}
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
       {C : bicat}
       {X Y Z : C}
       {f₁ g₁ : C⟦Y,Z⟧} {f₂ g₂ : C⟦X,Y⟧}
       (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
       (Hη₁ : is_invertible_2cell η₁)
       (Hη₂ : is_invertible_2cell η₂)
  : is_invertible_2cell (η₁ ⋆⋆ η₂).
Proof.
  use mk_is_invertible_2cell.
  - exact (Hη₁^-1 ⋆⋆ Hη₂^-1).
  - rewrite <- hcomp_vcomp.
    rewrite !vcomp_rinv.
    apply hcomp_identity.
  - rewrite <- hcomp_vcomp.
    rewrite !vcomp_lid.
    apply hcomp_identity.
Defined.

Definition bc_whisker_l
           {C : bicat}
           {X Y Z : C}
           {f₁ : C⟦X,Y⟧} {f₂ : C⟦X,Y⟧}
           (g : C⟦Y,Z⟧)
           (α : f₁ ==> f₂)
  : (g ∘ f₁) ==> (g ∘ f₂)
  := id₂ g ⋆⋆ α.

(* Notation "g '◅' α" := (bc_whisker_l g α) (at level 40) : bicategory_scope. *)

Definition bc_whisker_l_id₂
           {C : bicat}
           {X Y Z : C}
           (f : C⟦X,Y⟧)
           (g : C⟦Y,Z⟧)
  : g ◅ (id₂ f) = id₂ (g ∘ f).
Proof.
  apply id2_rwhisker.
Qed.

Definition bc_whisker_r
           {C : bicat}
           {X Y Z : C}
           {g₁ : C⟦Y,Z⟧} {g₂ : C⟦Y,Z⟧}
           (β : g₁ ==> g₂)
           (f : C⟦X,Y⟧)
  : (g₁ ∘ f) ==> (g₂ ∘ f)
  := β ⋆⋆ id₂ f.

(* Notation "β '▻' f" := (bc_whisker_r β f) (at level 40) : bicategory_scope. *)

Definition bc_whisker_r_id₂
           {C : bicat}
           {X Y Z : C}
           (f : C⟦X,Y⟧)
           (g : C⟦Y,Z⟧)
  : (id₂ g) ▻ f = id₂ (g ∘ f).
Proof.
  apply lwhisker_id2.
Qed.

Definition inverse_of_assoc
           {C : bicat}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : (is_invertible_2cell_lassociator f g h)^-1 = rassociator f g h.
Proof.
  apply idpath.
Qed.

Definition inverse_of_left_unit
           {C : bicat}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (left_unit_iso f)^-1 = rinvunitor f
  := idpath _ .

Definition inverse_of_lunitor
           {C : bicat}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (lunitor_iso f)^-1 = linvunitor f
  := idpath _.

(**** Properties of isomorphisms ***)

Definition id₂_inverse
           {C : bicat}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (iso_id₂ f)^-1 = id₂ f
  := idpath _.

Definition vcomp_inverse
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : g ==> h)
           (Hη₁ : is_invertible_2cell η₁)
           (Hη₂ : is_invertible_2cell η₂)
  : (is_invertible_2cell_vcomp _ _ Hη₁ Hη₂)^-1 = Hη₁^-1 o Hη₂^-1
  := idpath _ .

Definition hcomp_inverse
           {C : bicat}
           {X Y Z : C}
           {f₁ g₁ : C⟦Y,Z⟧} {f₂ g₂ : C⟦X,Y⟧}
           (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
           (Hη₁ : is_invertible_2cell η₁)
           (Hη₂ : is_invertible_2cell η₂)
  : (hcomp_iso _ _ Hη₁ Hη₂)^-1 = Hη₁^-1 ⋆⋆ Hη₂^-1
  := idpath _ .

Definition vcomp_cancel_left
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (ε : g ==> h)
           (η₁ η₂ : f ==> g)
           (Hε : is_invertible_2cell ε)
  : ε o η₁ = ε o η₂ -> η₁ = η₂.
Proof.
  intros Hhf.
  simple refine (!(id2_right _) @ _ @ id2_right _).
  rewrite <- (vcomp_rinv Hε).
  rewrite !vassocr.
  rewrite Hhf.
  reflexivity.
Qed.

Definition vcomp_cancel_right
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (ε : f ==> g) (η₁ η₂ : g ==> h)
           (Hε : is_invertible_2cell ε)
  : η₁ o ε = η₂ o ε -> η₁ = η₂.
Proof.
  intros Hhf.
  refine (!(id2_left _) @ _ @ id2_left _).
  rewrite <- (vcomp_lid Hε).
  rewrite <- !vassocr.
  rewrite Hhf.
  reflexivity.
Qed.

Definition vcomp_move_L_Vp
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : f ==> h) (ε : g ==> h)
           (Hε : is_invertible_2cell ε)
  : ε o η₁ = η₂ -> η₁ = Hε^-1 o η₂.
Proof.
  intros ?.
  rewrite <- (id2_right η₁).
  rewrite <- (vcomp_rinv Hε).
  rewrite vassocr.
  apply maponpaths_2.
  assumption.
Qed.

Definition vcomp_move_L_pV
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : g ==> h) (η₂ : f ==> h) (ε : f ==> g)
           (Hε : is_invertible_2cell ε)
  : η₁ o ε = η₂ -> η₁ = η₂ o Hε^-1.
Proof.
  intros Hη.
  rewrite <- (id2_left η₁).
  rewrite <- (vcomp_lid Hε).
  rewrite <- vassocr.
  rewrite Hη.
  reflexivity.
Qed.

Definition vcomp_move_R_Mp
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : f ==> h) (ε : g ==> h)
           (Hε : is_invertible_2cell ε)
  : η₁ = Hε^-1 o η₂ -> ε o η₁ = η₂.
Proof.
  intros ?.
  rewrite <- (id2_right η₂).
  rewrite <- (vcomp_lid Hε).
  rewrite vassocr.
  apply maponpaths_2.
  assumption.
Qed.

Definition vcomp_move_R_pM
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : g ==> h) (η₂ : f ==> h) (ε : f ==> g)
           (Hε : is_invertible_2cell ε)
  : η₁ = η₂ o Hε^-1 -> η₁ o ε = η₂.
Proof.
  intros Hη.
  rewrite <- (id2_left η₂).
  rewrite <- (vcomp_rinv Hε).
  rewrite <- vassocr.
  rewrite Hη.
  reflexivity.
Qed.

Definition vcomp_move_L_Mp
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> h) (η₂ : f ==> g) (ε : g ==> h)
           (Hε : is_invertible_2cell ε)
  : Hε^-1 o η₁ = η₂ -> η₁ = ε o η₂.
Proof.
  intros ?.
  rewrite <- (id2_right η₁).
  rewrite <- (vcomp_lid Hε).
  rewrite vassocr.
  apply maponpaths_2.
  assumption.
Qed.

Definition vcomp_move_L_pM
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> h) (η₂ : g ==> h) (ε : f ==> g)
           (Hε : is_invertible_2cell ε)
  : η₁ o Hε^-1 = η₂ -> η₁ = η₂ o ε.
Proof.
  intros Hη.
  rewrite <- (id2_left η₁).
  rewrite <- (vcomp_rinv Hε).
  rewrite <- vassocr.
  rewrite Hη.
  reflexivity.
Qed.

Definition path_inverse_2cell
           {C : bicat}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (η₁ η₂ : f ==> g)
           {Hη₁ : is_invertible_2cell η₁}
           {Hη₂ : is_invertible_2cell η₂}
  : η₁ = η₂ -> Hη₁^-1 = Hη₂^-1.
Proof.
  intros p.
  rewrite <- (id2_left (Hη₁^-1)).
  rewrite <- (id2_right (Hη₂^-1)).
  rewrite <- (vcomp_lid Hη₂).
  rewrite <- vassocr.
  apply maponpaths.
  rewrite <- p.
  apply vcomp_rinv.
Defined.


Ltac is_iso :=
  match goal with
  | [ |- is_invertible_2cell (runitor _) ] => apply is_invertible_2cell_runitor
  | [ |- is_invertible_2cell (rinvunitor _) ] => apply is_invertible_2cell_rinvunitor
  | [ |- is_invertible_2cell (lunitor _) ] => apply is_invertible_2cell_lunitor
  | [ |- is_invertible_2cell (linvunitor _) ] => apply is_invertible_2cell_linvunitor
  | [ |- is_invertible_2cell (rassociator _ _ _)] => apply is_invertible_2cell_rassociator
  | [ |- is_invertible_2cell (lassociator _ _ _)] => apply is_invertible_2cell_lassociator
  | [ |- is_invertible_2cell (_ ^-1)] => apply is_invertible_2cell_inv ; is_iso
  | [ |- is_invertible_2cell (_ • _)] => apply is_invertible_2cell_vcomp ; is_iso
  | [ |- is_invertible_2cell (_ ◃ _)] => apply is_invertible_2cell_lwhisker ; is_iso
  | [ |- is_invertible_2cell (_ ▹ _)] => apply is_invertible_2cell_rwhisker ; is_iso
  | [ |- is_invertible_2cell (_ ⋆⋆ _)] => apply hcomp_iso ; is_iso
  | [ |- is_invertible_2cell (_ ⋆ _)] => apply hcomp_iso ; is_iso
  | [ |- is_invertible_2cell (id₂ _)] => apply iso_id₂
  | _ => try assumption
  end.
