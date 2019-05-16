(* *********************************************************************************** *)
(** * More on invertible 2cells                                                        *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Notations.

Local Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Inverse 2cell of a composition                                                  *)
(* ----------------------------------------------------------------------------------- *)

Lemma is_invertible_2cell_vcomp {C : prebicat} {a b : C} {f g h: C ⟦a, b⟧}
      {x : f ==> g} (inv_x : is_invertible_2cell x)
      {y : g ==> h} (inv_y : is_invertible_2cell y)
  : is_invertible_2cell (x • y).
Proof.
  use make_is_invertible_2cell.
  - exact (inv_y^-1 • inv_x^-1).
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

Lemma is_invertible_2cell_lwhisker {C : prebicat} {a b c : C}
      (f : a --> b) {g1 g2 : b --> c}
      {x : g1 ==> g2} (inv_x : is_invertible_2cell x)
  : is_invertible_2cell (f ◃ x).
Proof.
  use make_is_invertible_2cell.
  - exact (f ◃ inv_x^-1).
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
  use make_is_invertible_2cell.
  - exact (inv_x^-1 ▹ g).
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

Definition is_invertible_2cell_hcomp
       {C : bicat}
       {X Y Z : C}
       {f₁ g₁ : C⟦Y,Z⟧} {f₂ g₂ : C⟦X,Y⟧}
       (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
       (inv_η₁ : is_invertible_2cell η₁)
       (inv_η₂ : is_invertible_2cell η₂)
  : is_invertible_2cell (η₁ ⋆⋆ η₂).
Proof.
  use make_is_invertible_2cell.
  - exact (inv_η₁^-1 ⋆⋆ inv_η₂^-1).
  - abstract (rewrite <- hcomp_vcomp, !vcomp_rinv; apply hcomp_identity).
  - abstract (rewrite <- hcomp_vcomp, !vcomp_lid; apply hcomp_identity).
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

(**** Properties of isomorphisms ***)

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
           {inv_η₁ : is_invertible_2cell η₁}
           {inv_η₂ : is_invertible_2cell η₂}
  : η₁ = η₂ -> inv_η₁^-1 = inv_η₂^-1.
Proof.
  intros p.
  rewrite <- (id2_left (inv_η₁^-1)).
  rewrite <- (id2_right (inv_η₂^-1)).
  rewrite <- (vcomp_lid inv_η₂).
  rewrite <- vassocr.
  apply maponpaths.
  rewrite <- p.
  apply vcomp_rinv.
Defined.

Definition isaset_invertible_2cell
           {C : bicat}
           {X Y : C}
           (f g : X --> Y)
  : isaset (invertible_2cell f g).
Proof.
  use isaset_total2.
  - apply C.
  - intro.
    apply isasetaprop.
    apply isaprop_is_invertible_2cell.
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
  | [ |- is_invertible_2cell (_ ⋆⋆ _)] => apply is_invertible_2cell_hcomp ; is_iso
  | [ |- is_invertible_2cell (_ ⋆ _)] => apply is_invertible_2cell_hcomp ; is_iso
  | [ |- is_invertible_2cell (id₂ _)] => apply is_invertible_2cell_id₂
  | _ => try assumption
  end.

Definition inv_of_invertible_2cell
           {C : bicat}
           {X Y : C}
           {f g : X --> Y}
  : invertible_2cell f g → invertible_2cell g f.
Proof.
  intro α.
  use make_invertible_2cell.
  - exact (α^-1).
  - is_iso.
Defined.

Definition comp_of_invertible_2cell
           {C : bicat}
           {X Y : C}
           {f g h : X --> Y}
  : invertible_2cell f g → invertible_2cell g h → invertible_2cell f h.
Proof.
  intros α β.
  use make_invertible_2cell.
  - exact (α • β).
  - is_iso.
    + apply α.
    + apply β.
Defined.