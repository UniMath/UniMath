(* ******************************************************************************* *)
(** * Pseudofunctors on bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

    Modified by: Dan Frumin, Niels van der Weide
    Based on https://github.com/nmvdw/groupoids
 ********************************************************************************* *)

(** * Pseudo functors. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.

Local Open Scope bicategory_scope.
Local Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Pseudo-functors                                                                 *)
(* ----------------------------------------------------------------------------------- *)

Definition psfunctor
           (C D : bicat)
  : UU
  := psfunctor_bicat C D.

Definition mk_psfunctor_data
           {C D : bicat}
           (F₀ : C → D)
           (F₁ : ∏ {a b : C}, C⟦a,b⟧ → D⟦F₀ a, F₀ b⟧)
           (F₂ : ∏ {a b : C} {f g : C⟦a,b⟧}, f ==> g → F₁ f ==> F₁ g)
           (Fid : ∏ (a : C), identity (F₀ a) ==> F₁ (identity a))
           (Fcomp : (∏ (a b c : C) (f : a --> b) (g : b --> c),
                     F₁ f · F₁ g ==> F₁ (f · g)))
  : psfunctor_data C D.
Proof.
  exact ((F₀ ,, F₁) ,, (F₂ ,, Fid ,, Fcomp)).
Defined.

Definition mk_psfunctor
           {C D : bicat}
           (F : psfunctor_data C D)
           (HF : psfunctor_laws F)
           (Fcells : invertible_cells F)
  : psfunctor C D
  := (F ,, (HF ,, Fcells)).

Coercion psfunctor_to_psfunctor_data
         {C D : bicat}
         (F : psfunctor C D)
  : psfunctor_data C D
  := pr1 F.

Definition psfunctor_on_cells
           {C D : bicat}
           (F : psfunctor C D)
           {a b : C}
           {f g : a --> b}
           (x : f ==> g)
  : #F f ==> #F g
  := pr12 (pr1 F) a b f g x.

Definition psfunctor_id
           {C D : bicat}
           (F : psfunctor C D)
           (a : C)
  : invertible_2cell (identity (F a)) (#F (identity a)).
Proof.
  refine (pr122 (pr1 F) a ,, _).
  apply F.
Defined.

Definition psfunctor_comp
           {C D : bicat}
           (F : psfunctor C D)
           {a b c : C}
           (f : a --> b)
           (g : b --> c)
  : invertible_2cell (#F f · #F g) (#F (f · g)).
Proof.
  refine (pr222 (pr1 F) a b c f g ,, _).
  apply F.
Defined.

Local Notation "'##'" := (psfunctor_on_cells).

Section Projection.
  Context {C D : bicat}.
  Variable (F : psfunctor C D).

  Definition psfunctor_id2
    : ∏ {a b : C} (f : a --> b), ##F (id2 f) = id2 (#F f)
    := pr1(pr12 F).

  Definition psfunctor_vcomp
    : ∏ {a b : C} {f g h : C⟦a, b⟧} (η : f ==> g) (φ : g ==> h),
      ##F (η • φ) = ##F η • ##F φ
    := pr12(pr12 F).

  Definition psfunctor_lunitor
    : ∏ {a b : C} (f : C⟦a, b⟧),
      lunitor (#F f)
      =
      (psfunctor_id F a ▹ #F f)
        • psfunctor_comp F (identity a) f
        • ##F (lunitor f)
    := pr122(pr12 F).

  Definition psfunctor_runitor
    : ∏ {a b : C} (f : C⟦a, b⟧),
      runitor (#F f)
      =
      (#F f ◃ psfunctor_id F b)
        • psfunctor_comp F f (identity b)
        • ##F (runitor f)
    := pr1(pr222(pr12 F)).

  Definition psfunctor_lassociator
    : ∏ {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧) ,
      (#F f ◃ psfunctor_comp F g h)
        • psfunctor_comp F f (g · h)
        • ##F (lassociator f g h)
      =
      (lassociator (#F f) (#F g) (#F h))
        • (psfunctor_comp F f g ▹ #F h)
        • psfunctor_comp F (f · g) h
    := pr12(pr222(pr12 F)).

  Definition psfunctor_lwhisker
    : ∏ {a b c : C} (f : C⟦a, b⟧) {g₁ g₂ : C⟦b, c⟧} (η : g₁ ==> g₂),
      psfunctor_comp F f g₁ • ##F (f ◃ η)
      =
      #F f ◃ ##F η • psfunctor_comp F f g₂
    := pr122(pr222(pr12 F)).

  Definition psfunctor_rwhisker
    : ∏ {a b c : C} {f₁ f₂ : C⟦a, b⟧} (g : C⟦b, c⟧) (η : f₁ ==> f₂),
      psfunctor_comp F f₁ g • ##F (η ▹ g)
      =
      ##F η ▹ #F g • psfunctor_comp F f₂ g
    := pr222(pr222(pr12 F)).
End Projection.

(** Isos are preserved *)
Definition psfunctor_is_iso
           {C D : bicat}
           (F : psfunctor C D)
           {a b : C}
           {f g : C⟦a,b⟧}
           (α : invertible_2cell f g)
  : is_invertible_2cell (##F α).
Proof.
  use tpair.
  - exact (##F (α^-1)).
  - split ; cbn
    ; rewrite <- psfunctor_vcomp, <- psfunctor_id2 ; apply maponpaths.
    + apply vcomp_rinv.
    + apply vcomp_lid.
Defined.

Section PseudoFunctorDerivedLaws.
  Context {C D : bicat}.
  Variable (F : psfunctor C D).

  Definition psfunctor_linvunitor
             {a b : C}
             (f : C⟦a, b⟧)
  : ##F (linvunitor f)
    =
    (linvunitor (#F f))
      • ((psfunctor_id F a) ▹ #F f)
      • (psfunctor_comp F _ _).
  Proof.
    rewrite !vassocl.
    cbn.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (psfunctor_is_iso F (linvunitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite psfunctor_lunitor ; cbn.
    rewrite <- !vassocr.
    reflexivity.
  Qed.

  Definition psfunctor_rinvunitor
             (a b : C)
             (f : C⟦a, b⟧)
    : ##F (rinvunitor f)
      =
      (rinvunitor (#F f))
        • (#F f ◃ psfunctor_id F b)
        • psfunctor_comp F _ _.
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (psfunctor_is_iso F (rinvunitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite psfunctor_runitor ; cbn.
    rewrite <- !vassocr.
    reflexivity.
  Qed.

  Definition psfunctor_rassociator
             {a b c d : C}
             (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
    : (psfunctor_comp F f g ▹ #F h)
        • psfunctor_comp F (f · g) h
        • ##F (rassociator f g h)
      =
      (rassociator (#F f) (#F g) (#F h))
        • (#F f ◃ psfunctor_comp F g h)
        • psfunctor_comp F f (g · h).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    use vcomp_move_R_Mp.
    { refine (psfunctor_is_iso F (rassociator f g h ,, _)).
      is_iso.
    }
    cbn.
    symmetry.
    exact (psfunctor_lassociator F f g h).
  Qed.

  Definition psfunctor_comp_natural
             {a b c : C}
             {g₁ g₂ : C⟦b,c⟧} {f₁ f₂ : C⟦a,b⟧}
             (ηg : g₁ ==> g₂) (ηf : f₁ ==> f₂)
    : psfunctor_comp F f₁ g₁ • ##F (ηf ⋆ ηg)
      =
      (##F ηf) ⋆ (##F ηg) • psfunctor_comp F f₂ g₂.
  Proof.
    unfold hcomp.
    rewrite !psfunctor_vcomp.
    rewrite !vassocr.
    rewrite !psfunctor_rwhisker.
    rewrite !vassocl.
    rewrite psfunctor_lwhisker.
    reflexivity.
  Qed.

  Definition psfunctor_F_lunitor
             {a b : C}
             (f : C⟦a, b⟧)
    : ##F (lunitor f)
      =
      ((psfunctor_comp F (identity a) f)^-1)
        • ((psfunctor_id F a)^-1 ▹ #F f)
        • lunitor (#F f).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    exact (!(psfunctor_lunitor F f)).
  Qed.

  Definition psfunctor_F_runitor
             {a b : C}
             (f : C⟦a,b⟧)
    : ##F (runitor f)
      =
      ((psfunctor_comp F f (identity b))^-1)
        • (#F f ◃ (psfunctor_id F b)^-1)
        • runitor (#F f).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    exact (!(psfunctor_runitor F f)).
  Qed.
End PseudoFunctorDerivedLaws.

Module Notations.
  Notation "'##'" := (psfunctor_on_cells).
End Notations.
