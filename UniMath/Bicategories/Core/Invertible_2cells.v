(* *********************************************************************************** *)
(** * More on invertible 2cells                                                        *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

Local Open Scope cat.

Definition eq_is_invertible_2cell
           {B : bicat}
           {a b : B}
           {f g : a --> b}
           {α β : f ==> g}
           (p : α = β)
           (Hα : is_invertible_2cell α)
  : is_invertible_2cell β.
Proof.
  use make_is_invertible_2cell.
  - exact (Hα^-1).
  - abstract
      (rewrite <- p ;
       apply vcomp_rinv).
  - abstract
      (rewrite <- p ;
       apply vcomp_linv).
Defined.

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
                  apply (vcomp_linv inv_x) |];
        rewrite id2_right;
        apply  (vcomp_linv inv_y)
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
        etrans; [ apply maponpaths; apply (vcomp_linv inv_x) |];
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
        etrans; [ apply maponpaths; apply (vcomp_linv inv_x) |];
        apply id2_rwhisker).
Defined.

(** ** Two-cells that are isomorphisms **)

Lemma pentagon
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
  - abstract (rewrite <- hcomp_vcomp, !vcomp_linv; apply hcomp_identity).
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

Lemma bc_whisker_l_id₂
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

Lemma bc_whisker_r_id₂
           {C : bicat}
           {X Y Z : C}
           (f : C⟦X,Y⟧)
           (g : C⟦Y,Z⟧)
  : (id₂ g) ▻ f = id₂ (g ∘ f).
Proof.
  apply lwhisker_id2.
Qed.

Lemma inverse_of_assoc
           {C : bicat}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : (is_invertible_2cell_lassociator f g h)^-1 = rassociator f g h.
Proof.
  apply idpath.
Qed.

(**** Properties of isomorphisms ***)

Lemma vcomp_move_L_Vp
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : f ==> h) (ε : g ==> h)
           (Hε : is_invertible_2cell ε)
  : ε o η₁ = η₂ -> η₁ = Hε^-1 o η₂.
Proof.
  intro.
  rewrite <- (id2_right η₁).
  rewrite <- (vcomp_rinv Hε).
  rewrite vassocr.
  apply maponpaths_2.
  assumption.
Qed.

Lemma vcomp_move_L_pV
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : g ==> h) (η₂ : f ==> h) (ε : f ==> g)
           (Hε : is_invertible_2cell ε)
  : η₁ o ε = η₂ -> η₁ = η₂ o Hε^-1.
Proof.
  intros Hη.
  rewrite <- (id2_left η₁).
  rewrite <- (vcomp_linv Hε).
  rewrite <- vassocr.
  apply maponpaths.
  exact Hη.
Qed.

Lemma vcomp_move_R_Mp
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : f ==> h) (ε : g ==> h)
           (Hε : is_invertible_2cell ε)
  : η₁ = Hε^-1 o η₂ -> ε o η₁ = η₂.
Proof.
  intro.
  rewrite <- (id2_right η₂).
  rewrite <- (vcomp_linv Hε).
  rewrite vassocr.
  apply maponpaths_2.
  assumption.
Qed.

Lemma vcomp_move_R_pM
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
  apply maponpaths.
  apply Hη.
Qed.

Lemma vcomp_move_L_Mp
           {C : bicat}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> h) (η₂ : f ==> g) (ε : g ==> h)
           (Hε : is_invertible_2cell ε)
  : Hε^-1 o η₁ = η₂ -> η₁ = ε o η₂.
Proof.
  intros.
  rewrite <- (id2_right η₁).
  rewrite <- (vcomp_linv Hε).
  rewrite vassocr.
  apply maponpaths_2.
  assumption.
Qed.

Lemma vcomp_move_L_pM
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
  apply maponpaths.
  apply Hη.
Qed.

Lemma path_inverse_2cell
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
  rewrite <- (vcomp_linv inv_η₂).
  rewrite <- vassocr.
  apply maponpaths.
  rewrite <- p.
  apply vcomp_rinv.
Qed.

Lemma isaset_invertible_2cell
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
Qed.

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

Definition lwhisker_of_invertible_2cell
           {B : bicat}
           {x y z : B}
           (f : x --> y)
           {g₁ g₂ : y --> z}
           (α : invertible_2cell g₁ g₂)
  : invertible_2cell (f · g₁) (f · g₂).
Proof.
  use make_invertible_2cell.
  - exact (f ◃ α).
  - is_iso.
    apply α.
Defined.

Definition rwhisker_of_invertible_2cell
           {B : bicat}
           {x y z : B}
           {f₁ f₂ : x --> y}
           (g : y --> z)
           (α : invertible_2cell f₁ f₂)
  : invertible_2cell (f₁ · g) (f₂ · g).
Proof.
  use make_invertible_2cell.
  - exact (α ▹ g).
  - is_iso.
    apply α.
Defined.

Definition lunitor_invertible_2cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : invertible_2cell (id₁ a · f) f.
Proof.
  use make_invertible_2cell.
  - exact (lunitor f).
  - is_iso.
Defined.

Definition linvunitor_invertible_2cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : invertible_2cell f (id₁ a · f).
Proof.
  use make_invertible_2cell.
  - exact (linvunitor f).
  - is_iso.
Defined.

Definition runitor_invertible_2cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : invertible_2cell (f · id₁ b) f.
Proof.
  use make_invertible_2cell.
  - exact (runitor f).
  - is_iso.
Defined.

Definition rinvunitor_invertible_2cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : invertible_2cell f (f · id₁ b).
Proof.
  use make_invertible_2cell.
  - exact (rinvunitor f).
  - is_iso.
Defined.

Definition lassociator_invertible_2cell
           {B : bicat}
           {a b c d : B}
           (f : a --> b)
           (g : b --> c)
           (h : c --> d)
  : invertible_2cell (f · (g · h)) (f · g · h).
Proof.
  use make_invertible_2cell.
  - exact (lassociator f g h).
  - is_iso.
Defined.

Definition rassociator_invertible_2cell
           {B : bicat}
           {a b c d : B}
           (f : a --> b)
           (g : b --> c)
           (h : c --> d)
  : invertible_2cell (f · g · h) (f · (g · h)).
Proof.
  use make_invertible_2cell.
  - exact (rassociator f g h).
  - is_iso.
Defined.

(**
 Invertible 2-cells are the same as isos in the hom category
 *)
Section InvertibleIsIso.
  Context {B : bicat}.

  Definition is_inv2cell_to_is_z_iso
             {a b : B}
             {f g : hom a b}
             (α : f ==> g)
             (Hα : is_invertible_2cell α)
    : is_z_isomorphism α.
  Proof.
    exists (Hα^-1).
    abstract (split ; [ apply vcomp_rinv | apply vcomp_linv]).
  Defined.

  Definition inv2cell_to_z_iso
             {a b : B}
             {f g : hom a b}
             (α : invertible_2cell f g)
    : z_iso f g.
  Proof.
    use make_z_iso'.
    - apply α.
    - apply is_inv2cell_to_is_z_iso.
      apply property_from_invertible_2cell.
  Defined.

  Definition is_z_iso_to_is_inv2cell
             {a b : B}
             {f g : hom a b}
             (α : f ==> g)
             (Hα : is_z_isomorphism α)
    : is_invertible_2cell α.
  Proof.
    use make_is_invertible_2cell.
    - exact (inv_from_z_iso (α ,, Hα)).
    - exact (z_iso_inv_after_z_iso (α ,, Hα)).
    - exact (z_iso_after_z_iso_inv (α ,, Hα)).
  Defined.

  Definition z_iso_to_inv2cell
             {a b : B}
             {f g : hom a b}
             (α : z_iso f g)
    : invertible_2cell f g.
  Proof.
    use make_invertible_2cell.
    - exact (pr1 α).
    - exact (is_z_iso_to_is_inv2cell _ (pr2 α)).
  Defined.

  Definition inv2cell_to_z_iso_isweq
             {a b : B}
             (f g : hom a b)
    : isweq (@inv2cell_to_z_iso _ _ f g).
  Proof.
    use isweq_iso.
    - exact z_iso_to_inv2cell.
    - abstract
        (intro i ;
         apply cell_from_invertible_2cell_eq ;
         apply idpath).
    - abstract
        (intro i ;
         apply z_iso_eq ;
         apply idpath).
  Defined.

  Definition inv2cell_to_z_iso_weq
             {a b : B}
             (f g : hom a b)
    : invertible_2cell f g ≃ z_iso f g.
  Proof.
    use make_weq.
    - exact (λ α, inv2cell_to_z_iso α).
    - exact (inv2cell_to_z_iso_isweq f g).
  Defined.
End InvertibleIsIso.
