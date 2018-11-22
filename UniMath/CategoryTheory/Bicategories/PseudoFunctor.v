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
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws.
Require Import UniMath.CategoryTheory.Bicategories.bicategory_laws_2.

Open Scope cat.

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
  :=   (∏ (a : C), #F (identity a) ==> identity _)
     × (∏ (a b c : C) (f : a --> b) (g : b --> c),
        #F (f · g) ==> #F f · #F g).

Definition laxfunctor_data (C C' : prebicat_data) : UU
  := ∑ F : laxfunctor_ob_mor_cell C C', laxfunctor_cell_data F.

Coercion laxfunctor_ob_mor_cell_from_bifunctor_data {C C' : prebicat_data}
         (F : laxfunctor_data C C')
  : laxfunctor_ob_mor_cell _ _
  := pr1 F.

Definition laxfunctor_id {C C' : prebicat_data} (F : laxfunctor_data C C') (a : C)
  : #F (identity a) ==> identity _
  := pr1 (pr2 F) a.

Definition laxfunctor_comp {C C' : prebicat_data} (F : laxfunctor_data C C')
           {a b c : C} (f : a --> b) (g : b --> c)
  : #F (f · g) ==> #F f · #F g
  := pr2 (pr2 F) a b c f g.

(** A builder function for lax functor data. *)
Definition build_laxfunctor_data
           {C C' : prebicat_data}
           (F₀ : C → C')
           (F₁ : ∏ {a b : C}, C⟦a,b⟧ → C'⟦F₀ a, F₀ b⟧)
           (F₂ : ∏ {a b : C} {f g : C⟦a,b⟧}, f ==> g → F₁ f ==> F₁ g)
           (Fid : ∏ (a : C), F₁ (identity a) ==> identity _)
           (Fcomp : (∏ (a b c : C) (f : a --> b) (g : b --> c),
                     F₁ (f · g) ==> F₁ f · F₁ g))
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
       ##F (lunitor f)
     =   laxfunctor_comp F (identity a) f
       • (laxfunctor_id _ _ ▹ #F f)
       • lunitor (#F f).

Definition laxfunctor_runitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (runitor f)
     =   laxfunctor_comp F f (identity b)
       • (#F f ◃ laxfunctor_id _ _)
       • runitor (#F f).

Definition laxfunctor_lassociator_law : UU
  := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧) ,
       ##F (lassociator f g h)
       • (laxfunctor_comp F _ _)
       • ((laxfunctor_comp F _ _) ▹ #F _)
     =   laxfunctor_comp F _ _
       • (#F f ◃ laxfunctor_comp F _ _)
       • lassociator (#F f) (#F g) (#F h).

Definition laxfunctor_lwhisker_law : UU
  := ∏ (a b c : C) (f : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧) (η : g1 ==> g2),
       ##F (f ◃ η)
       • laxfunctor_comp F _ _
     =   laxfunctor_comp F _ _
       • (#F f ◃ ##F η).

Definition laxfunctor_rwhisker_law : UU
  := ∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g : C⟦b, c⟧) (η : f1 ==> f2),
       ##F (η ▹ g)
       • laxfunctor_comp F _ _
     =   laxfunctor_comp F _ _
       • (##F η ▹ #F g).

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
    : ∏ (a b : C) (f : a --> b), ##F (id2 f) = id2 (#F f)
    := pr1(pr2 F).

  Definition laxfunctor_vcomp
    : ∏ (a b : C) (f g h: C⟦a, b⟧) (η : f ==> g) (φ : g ==> h),
      ##F (η • φ) = ##F η • ##F φ
    := pr1(pr2(pr2 F)).

  Definition laxfunctor_lunitor
    : ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (lunitor f)
     =   laxfunctor_comp F (identity a) f
       • (laxfunctor_id _ _ ▹ #F f)
       • lunitor (#F f)
    := pr1(pr2(pr2(pr2 F))).

  Definition laxfunctor_runitor
    : ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (runitor f)
     =   laxfunctor_comp F f (identity b)
       • (#F f ◃ laxfunctor_id _ _)
       • runitor (#F f)
    := pr1(pr2(pr2(pr2(pr2 F)))).

  Definition laxfunctor_lassociator
    : ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧) ,
       ##F (lassociator f g h)
       • (laxfunctor_comp F _ _)
       • ((laxfunctor_comp F _ _) ▹ #F _)
     =   laxfunctor_comp F _ _
       • (#F f ◃ laxfunctor_comp F _ _)
       • lassociator (#F f) (#F g) (#F h)
    := pr1(pr2(pr2(pr2(pr2(pr2 F))))).

  Definition laxfunctor_lwhisker
    : ∏ (a b c : C) (f : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧) (η : g1 ==> g2),
       ##F (f ◃ η)
       • laxfunctor_comp F _ _
     =   laxfunctor_comp F _ _
       • (#F f ◃ ##F η)
    := pr1(pr2(pr2(pr2(pr2(pr2(pr2 F)))))).

  Definition laxfunctor_rwhisker
    : ∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g : C⟦b, c⟧) (η : f1 ==> f2),
       ##F (η ▹ g)
       • laxfunctor_comp F _ _
     =   laxfunctor_comp F _ _
       • (##F η ▹ #F g)
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
  - exact (##F (inv_cell α)).
  - split ; cbn
    ; rewrite <- laxfunctor_vcomp, <- laxfunctor_id2 ; apply maponpaths.
    + apply invertible_2cell_after_inv_cell.
    + apply inv_cell_after_invertible_2cell.
Defined.

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
  : invertible_2cell (#F (identity a)) (identity _)
  := (_ ,, pr1 (pr2 F) a).

Definition psfunctor_comp
           {C C' : prebicat_data}
           (F : psfunctor C C')
           {a b c : C}
           (f : a --> b) (g : b --> c)
  : invertible_2cell (#F (f · g)) (#F f · #F g)
  := (_ ,, pr2(pr2 F) a b c f g).

Section PseudoFunctorDerivedLaws.
  Context {C C' : bicat}.
  Variable (F : psfunctor C C').

  Definition psfunctor_linvunitor
             {a b : C}
             (f : C⟦a, b⟧)
    : ##F (linvunitor f)
      =   linvunitor (#F f)
        • (inv_cell (psfunctor_id F a) ▹ #F f)
        • inv_cell (psfunctor_comp F _ _).
  Proof.
    rewrite <- !vcomp_assoc.
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
    rewrite <- !vcomp_assoc.
    rewrite !(maponpaths (λ z, _ • z) (vcomp_assoc _ _ _)).
    rewrite inv_cell_after_invertible_2cell.
    rewrite vcomp_right_identity.
    rewrite !vcomp_assoc.
    rewrite rwhisker_vcomp.
    rewrite inv_cell_after_invertible_2cell.
    rewrite id2_rwhisker.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition psfunctor_rinvunitor
             (a b : C)
             (f : C⟦a, b⟧)
    : ##F (rinvunitor f)
      =   rinvunitor (#F f)
        • (#F f ◃ inv_cell (psfunctor_id F b))
        • inv_cell (psfunctor_comp F _ _).
  Proof.
    rewrite <- !vcomp_assoc.
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
    rewrite <- !vcomp_assoc.
    rewrite !(maponpaths (λ z, _ • z) (vcomp_assoc _ _ _)).
    rewrite inv_cell_after_invertible_2cell.
    rewrite vcomp_right_identity.
    rewrite !vcomp_assoc.
    rewrite lwhisker_vcomp.
    rewrite inv_cell_after_invertible_2cell.
    rewrite lwhisker_id2.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition psfunctor_rassociator
             {a b c d : C}
             (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
    : ##F (rassociator f g h)
      =   psfunctor_comp F _ _
        • (psfunctor_comp F _ _ ▹ #F h)
        • rassociator (#F f) (#F g) (#F h)
        • (#F f ◃ inv_cell (psfunctor_comp F _ _))
        • inv_cell (psfunctor_comp F _ _).
  Proof.
    use vcomp_move_L_Mp.
    { is_iso. }
    cbn.
    use vcomp_move_L_Mp.
    { is_iso. }
    cbn.
    rewrite <- !vcomp_assoc.
    use vcomp_move_R_pM.
    {
      refine (laxfunctor_is_iso F (rassociator f g h ,, _)).
      is_iso.
    }
    cbn.
    rewrite !vcomp_assoc.
    use vcomp_move_L_Mp.
    {
      is_iso.
    }
    cbn.
    symmetry.
    apply laxfunctor_lassociator.
  Qed.
End PseudoFunctorDerivedLaws.

Module Notations.
  Notation "'##'" := (laxfunctor_on_cells).
End Notations.