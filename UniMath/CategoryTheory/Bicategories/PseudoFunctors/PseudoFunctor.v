(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

    Modified by: Dan Frumin, Niels van der Weide
    Based on https://github.com/nmvdw/groupoids
 ********************************************************************************* *)

(** * Pseudo functors. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.

Local Open Scope bicategory_scope.
Local Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Pseudo-functors                                                                 *)
(* ----------------------------------------------------------------------------------- *)

Definition laxfunctor_ob_mor_cell (C C' : prebicat_data) : UU
  := ∑ F : functor_data C C',
     ∏ a b (f g : a --> b), f ==> g → #F f ==> #F g.

Coercion functor_data_from_bifunctor_ob_mor_cell {C C' : prebicat_data}
         (F : laxfunctor_ob_mor_cell C C')
  : functor_data C C' := pr1 F.

Definition laxfunctor_on_cells {C C' : prebicat_data}
           (F : laxfunctor_ob_mor_cell C C')
           {a b : C} {f g : a --> b} (x : f ==> g)
  : #F f ==> #F g
  := pr2 F a b f g x.

Local Notation "'##'" := (laxfunctor_on_cells).

Definition laxfunctor_cell_data {C C' : prebicat_data} (F : laxfunctor_ob_mor_cell C C')
  : UU
  :=   (∏ (a : C), identity (F a) ==> #F (identity a))
     × (∏ (a b c : C) (f : a --> b) (g : b --> c),
        #F f · #F g ==> #F (f · g)).

Definition laxfunctor_data (C C' : prebicat_data) : UU
  := ∑ F : laxfunctor_ob_mor_cell C C', laxfunctor_cell_data F.

Coercion laxfunctor_ob_mor_cell_from_bifunctor_data {C C' : prebicat_data}
         (F : laxfunctor_data C C')
  : laxfunctor_ob_mor_cell _ _
  := pr1 F.

Definition laxfunctor_id {C C' : prebicat_data} (F : laxfunctor_data C C') (a : C)
  : identity (F a) ==> #F (identity a)
  := pr1 (pr2 F) a.

Definition laxfunctor_comp {C C' : prebicat_data} (F : laxfunctor_data C C')
           {a b c : C} (f : a --> b) (g : b --> c)
  : #F f · #F g ==> #F (f · g)
  := pr2 (pr2 F) a b c f g.

(** A builder function for lax functor data. *)
Definition build_laxfunctor_data
           {C C' : prebicat_data}
           (F₀ : C → C')
           (F₁ : ∏ {a b : C}, C⟦a,b⟧ → C'⟦F₀ a, F₀ b⟧)
           (F₂ : ∏ {a b : C} {f g : C⟦a,b⟧}, f ==> g → F₁ f ==> F₁ g)
           (Fid : ∏ (a : C), identity (F₀ a) ==> F₁ (identity a))
           (Fcomp : (∏ (a b c : C) (f : a --> b) (g : b --> c),
                     F₁ f · F₁ g ==> F₁ (f · g)))
  : laxfunctor_data C C'.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * exact F₀.
      * exact F₁.
    + exact F₂.
  - split.
    + exact Fid.
    + exact Fcomp.
Defined.

Section laxfunctor_laws.

Context {C C' : prebicat_data} (F : laxfunctor_data C C').

Definition laxfunctor_id2_law : UU
  := ∏ (a b : C) (f : a --> b), ##F (id2 f) = id2 _.

Definition laxfunctor_vcomp2_law : UU
  := ∏ (a b : C) (f g h: C⟦a, b⟧) (η : f ==> g) (φ : g ==> h),
     ##F (η • φ) = ##F η • ##F φ.

Definition laxfunctor_lunitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
     lunitor (#F f)
     =
     (laxfunctor_id F a ▹ #F f)
       • laxfunctor_comp F (identity a) f
       • ##F (lunitor f).

Definition laxfunctor_runitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
     runitor (#F f)
     =
     (#F f ◃ laxfunctor_id F b)
       • laxfunctor_comp F f (identity b)
       • ##F (runitor f).

Definition laxfunctor_lassociator_law : UU
  := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
     (#F f ◃ laxfunctor_comp F g h)
       • laxfunctor_comp F f (g · h)
       • ##F (lassociator f g h)
     =
     (lassociator (#F f) (#F g) (#F h))
       • (laxfunctor_comp F f g ▹ #F h)
       • laxfunctor_comp F (f · g) h.

Definition laxfunctor_lwhisker_law : UU
  := ∏ (a b c : C) (f : C⟦a, b⟧) (g₁ g₂ : C⟦b, c⟧) (η : g₁ ==> g₂),
     laxfunctor_comp F f g₁ • ##F (f ◃ η)
     =
     #F f ◃ ##F η • laxfunctor_comp F f g₂.

Definition laxfunctor_rwhisker_law : UU
  := ∏ (a b c : C) (f₁ f₂ : C⟦a, b⟧) (g : C⟦b, c⟧) (η : f₁ ==> f₂),
     laxfunctor_comp F f₁ g • ##F (η ▹ g)
     =
     ##F η ▹ #F g • laxfunctor_comp F f₂ g.

Definition laxfunctor_laws : UU
  :=   laxfunctor_id2_law
     × laxfunctor_vcomp2_law
     × laxfunctor_lunitor_law
     × laxfunctor_runitor_law
     × laxfunctor_lassociator_law
     × laxfunctor_lwhisker_law
     × laxfunctor_rwhisker_law.
End laxfunctor_laws.

Definition laxfunctor (C C' : prebicat_data)
  : UU
  := ∑ F : laxfunctor_data C C', laxfunctor_laws F.

Coercion laxfunctor_to_laxfunctor_data
         {C C' : prebicat_data}
         (F : laxfunctor C C')
  := pr1 F.

Section Projection.
  Context {C C' : prebicat_data}.
  Variable (F : laxfunctor C C').

  Definition laxfunctor_id2
    : ∏ {a b : C} (f : a --> b), ##F (id2 f) = id2 (#F f)
    := pr1(pr2 F).

  Definition laxfunctor_vcomp
    : ∏ {a b : C} {f g h : C⟦a, b⟧} (η : f ==> g) (φ : g ==> h),
      ##F (η • φ) = ##F η • ##F φ
    := pr1(pr2(pr2 F)).

  Definition laxfunctor_lunitor
    : ∏ {a b : C} (f : C⟦a, b⟧),
      lunitor (#F f)
      =
      (laxfunctor_id F a ▹ #F f)
        • laxfunctor_comp F (identity a) f
        • ##F (lunitor f)
    := pr1(pr2(pr2(pr2 F))).

  Definition laxfunctor_runitor
    : ∏ {a b : C} (f : C⟦a, b⟧),
      runitor (#F f)
      =
      (#F f ◃ laxfunctor_id F b)
        • laxfunctor_comp F f (identity b)
        • ##F (runitor f)
    := pr1(pr2(pr2(pr2(pr2 F)))).

  Definition laxfunctor_lassociator
    : ∏ {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧) ,
      (#F f ◃ laxfunctor_comp F g h)
        • laxfunctor_comp F f (g · h)
        • ##F (lassociator f g h)
      =
      (lassociator (#F f) (#F g) (#F h))
        • (laxfunctor_comp F f g ▹ #F h)
        • laxfunctor_comp F (f · g) h
    := pr1(pr2(pr2(pr2(pr2(pr2 F))))).

  Definition laxfunctor_lwhisker
    : ∏ {a b c : C} (f : C⟦a, b⟧) {g₁ g₂ : C⟦b, c⟧} (η : g₁ ==> g₂),
      laxfunctor_comp F f g₁ • ##F (f ◃ η)
      =
      #F f ◃ ##F η • laxfunctor_comp F f g₂
    := pr1(pr2(pr2(pr2(pr2(pr2(pr2 F)))))).

  Definition laxfunctor_rwhisker
    : ∏ {a b c : C} {f₁ f₂ : C⟦a, b⟧} (g : C⟦b, c⟧) (η : f₁ ==> f₂),
      laxfunctor_comp F f₁ g • ##F (η ▹ g)
      =
      ##F η ▹ #F g • laxfunctor_comp F f₂ g
    := pr2(pr2(pr2(pr2(pr2(pr2(pr2 F)))))).
End Projection.

(** Isos are preserved *)
Definition laxfunctor_is_iso
           {C C' : prebicat_data}
           (F : laxfunctor C C')
           {a b : C}
           {f g : C⟦a,b⟧}
           (α : invertible_2cell f g)
  : is_invertible_2cell (##F α).
Proof.
  use tpair.
  - exact (##F (α^-1)).
  - split ; cbn
    ; rewrite <- laxfunctor_vcomp, <- laxfunctor_id2 ; apply maponpaths.
    + apply vcomp_rinv.
    + apply vcomp_lid.
Defined.

Section LaxFunctorDerivedLaws.
  Context {C C' : bicat}.
  Variable (F : laxfunctor C C').

  Definition laxfunctor_linvunitor
             {a b : C}
             (f : C⟦a, b⟧)
  : ##F (linvunitor f)
    =
    (linvunitor (#F f))
      • ((laxfunctor_id F a) ▹ #F f)
      • (laxfunctor_comp F _ _).
  Proof.
    rewrite !vassocl.
    cbn.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (laxfunctor_is_iso F (linvunitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite laxfunctor_lunitor ; cbn.
    rewrite <- !vassocr.
    reflexivity.
  Qed.

  Definition psfunctor_rinvunitor
             (a b : C)
             (f : C⟦a, b⟧)
    : ##F (rinvunitor f)
      =
      (rinvunitor (#F f))
        • (#F f ◃ laxfunctor_id F b)
        • laxfunctor_comp F _ _.
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (laxfunctor_is_iso F (rinvunitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite laxfunctor_runitor ; cbn.
    rewrite <- !vassocr.
    reflexivity.
  Qed.

  Definition laxfunctor_rassociator
             {a b c d : C}
             (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
    : (laxfunctor_comp F f g ▹ #F h)
        • laxfunctor_comp F (f · g) h
        • ##F (rassociator f g h)
      =
      (rassociator (#F f) (#F g) (#F h))
        • (#F f ◃ laxfunctor_comp F g h)
        • laxfunctor_comp F f (g · h).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    use vcomp_move_R_Mp.
    { refine (laxfunctor_is_iso F (rassociator f g h ,, _)).
      is_iso.
    }
    cbn.
    symmetry.
    exact (laxfunctor_lassociator F f g h).
  Qed.

  Definition laxfunctor_comp_natural
             {a b c : C}
             {g₁ g₂ : C⟦b,c⟧} {f₁ f₂ : C⟦a,b⟧}
             (ηg : g₁ ==> g₂) (ηf : f₁ ==> f₂)
    : laxfunctor_comp F f₁ g₁ • ##F (ηf ⋆ ηg)
      =
      (##F ηf) ⋆ (##F ηg) • laxfunctor_comp F f₂ g₂.
  Proof.
    unfold hcomp.
    rewrite !laxfunctor_vcomp.
    rewrite !vassocr.
    rewrite laxfunctor_rwhisker.
    rewrite !vassocl.
    rewrite laxfunctor_lwhisker.
    reflexivity.
  Qed.
End LaxFunctorDerivedLaws.

Definition is_pseudofunctor
           {C C' : prebicat_data}
           (F : laxfunctor C C')
  : UU
  := (∏ (a : C), is_invertible_2cell (laxfunctor_id F a))
     ×
     (∏ {a b c : C} (f : a --> b) (g : b --> c), is_invertible_2cell (laxfunctor_comp F f g)).

Definition psfunctor
           (C C' : prebicat_data)
  := ∑ (F : laxfunctor C C'), is_pseudofunctor F.

Coercion pseudofunctor_to_laxfunctor
         {C C' : prebicat_data}
         (F : psfunctor C C')
  := pr1 F.

Definition psfunctor_id
           {C C' : prebicat_data}
           (F : psfunctor C C')
           (a : C)
  : invertible_2cell (identity (F a)) (#F (identity a))
  := (_ ,, pr1 (pr2 F) a).

Definition psfunctor_comp
           {C C' : prebicat_data}
           (F : psfunctor C C')
           {a b c : C}
           (f : a --> b) (g : b --> c)
  : invertible_2cell (#F f · #F g) (#F (f · g))
  := (_ ,, pr2(pr2 F) a b c f g).

Section PseudoFunctorDerivedLaws.
  Context {C C' : bicat}.
  Variable (F : psfunctor C C').

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
    exact (!(laxfunctor_lunitor F f)).
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
    exact (!(laxfunctor_runitor F f)).
  Qed.
End PseudoFunctorDerivedLaws.

Module Notations.
  Notation "'##'" := (laxfunctor_on_cells).
End Notations.
