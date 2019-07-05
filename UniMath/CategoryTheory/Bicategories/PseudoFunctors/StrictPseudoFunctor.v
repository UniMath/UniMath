(* ******************************************************************************* *)
(** * Strict seudofunctors on bicategories
 ********************************************************************************* *)

(** * Pseudo functors. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.StrictIdentitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.StrictCompositor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.

Local Open Scope bicategory_scope.
Local Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Pseudo-functors                                                                 *)
(* ----------------------------------------------------------------------------------- *)

Definition strict_psfunctor
           (C D : bicat)
  : UU
  := strict_psfunctor_bicat C D.

Definition make_strict_psfunctor_data
           {C D : bicat}
           (F₀ : C → D)
           (F₁ : ∏ {a b : C}, C⟦a,b⟧ → D⟦F₀ a, F₀ b⟧)
           (F₂ : ∏ {a b : C} {f g : C⟦a,b⟧}, f ==> g → F₁ f ==> F₁ g)
           (Fid : ∏ (a : C), identity (F₀ a) = F₁ (identity a))
           (Fcomp : (∏ (a b c : C) (f : a --> b) (g : b --> c),
                     F₁ f · F₁ g = F₁ (f · g)))
  : strict_psfunctor_data C D.
Proof.
  exact ((F₀ ,, F₁) ,, (F₂ ,, Fid ,, Fcomp)).
Defined.

Definition make_strict_psfunctor
           {C D : bicat}
           (F : strict_psfunctor_data C D)
           (HF : is_strict_psfunctor F)
  : strict_psfunctor C D
  := (F ,, HF).

Coercion strict_psfunctor_to_strict_psfunctor_data
         {C D : bicat}
         (F : strict_psfunctor C D)
  : strict_psfunctor_data C D
  := pr1 F.

Definition strict_psfunctor_on_cells
           {C D : bicat}
           (F : strict_psfunctor C D)
           {a b : C}
           {f g : a --> b}
           (x : f ==> g)
  : #F f ==> #F g
  := pr12 (pr1 F) a b f g x.

Definition strict_psfunctor_id
           {C D : bicat}
           (F : strict_psfunctor C D)
           (a : C)
  : identity (F a) = #F (identity a)
  := pr1 (pr221 F) a.

Definition strict_psfunctor_comp
           {C D : bicat}
           (F : strict_psfunctor C D)
           {a b c : C}
           (f : a --> b)
           (g : b --> c)
  : #F f · #F g = #F (f · g)
  := pr2 (pr221 F) _ _ _ f g.

Definition strict_psfunctor_id_cell
           {C D : bicat}
           (F : strict_psfunctor C D)
           (a : C)
  : invertible_2cell (identity (F a)) (#F (identity a))
  := idtoiso_2_1 _ _ (strict_psfunctor_id F a).

Definition strict_psfunctor_comp_cell
           {C D : bicat}
           (F : strict_psfunctor C D)
           {a b c : C}
           (f : a --> b)
           (g : b --> c)
  : invertible_2cell (#F f · #F g) (#F (f · g))
  := idtoiso_2_1 _ _ (strict_psfunctor_comp F f g).

Local Notation "'##'" := (strict_psfunctor_on_cells).

Section StrictProjection.
  Context {C D : bicat}.
  Variable (F : strict_psfunctor C D).

  Definition strict_psfunctor_id2
    : ∏ {a b : C} (f : a --> b), ##F (id2 f) = id2 (#F f)
    := pr1(pr2 F).

  Definition strict_psfunctor_vcomp
    : ∏ {a b : C} {f g h : C⟦a, b⟧} (η : f ==> g) (φ : g ==> h),
      ##F (η • φ) = ##F η • ##F φ
    := pr12(pr2 F).

  Definition strict_psfunctor_lunitor
    : ∏ {a b : C} (f : C⟦a, b⟧),
      lunitor (#F f)
      =
      (strict_psfunctor_id_cell F a ▹ #F f)
        • strict_psfunctor_comp_cell F (identity a) f
        • ##F (lunitor f)
    := pr122(pr2 F).

  Definition strict_psfunctor_runitor
    : ∏ {a b : C} (f : C⟦a, b⟧),
      runitor (#F f)
      =
      (#F f ◃ strict_psfunctor_id_cell F b)
        • strict_psfunctor_comp_cell F f (identity b)
        • ##F (runitor f)
    := pr1(pr222(pr2 F)).

  Definition strict_psfunctor_lassociator
    : ∏ {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧) ,
      (#F f ◃ strict_psfunctor_comp_cell F g h)
        • strict_psfunctor_comp_cell F f (g · h)
        • ##F (lassociator f g h)
      =
      (lassociator (#F f) (#F g) (#F h))
        • (strict_psfunctor_comp_cell F f g ▹ #F h)
        • strict_psfunctor_comp_cell F (f · g) h
    := pr12(pr222(pr2 F)).

  Definition strict_psfunctor_lwhisker
    : ∏ {a b c : C} (f : C⟦a, b⟧) {g₁ g₂ : C⟦b, c⟧} (η : g₁ ==> g₂),
      strict_psfunctor_comp_cell F f g₁ • ##F (f ◃ η)
      =
      #F f ◃ ##F η • strict_psfunctor_comp_cell F f g₂
    := pr122(pr222(pr2 F)).

  Definition strict_psfunctor_rwhisker
    : ∏ {a b c : C} {f₁ f₂ : C⟦a, b⟧} (g : C⟦b, c⟧) (η : f₁ ==> f₂),
      strict_psfunctor_comp_cell F f₁ g • ##F (η ▹ g)
      =
      ##F η ▹ #F g • strict_psfunctor_comp_cell F f₂ g
    := pr222(pr222(pr2 F)).
End StrictProjection.

(** Isos are preserved *)
Definition strict_psfunctor_is_iso
           {C D : bicat}
           (F : strict_psfunctor C D)
           {a b : C}
           {f g : C⟦a,b⟧}
           (α : invertible_2cell f g)
  : is_invertible_2cell (##F α).
Proof.
  use tpair.
  - exact (##F (α^-1)).
  - split ; cbn
    ; rewrite <- strict_psfunctor_vcomp, <- strict_psfunctor_id2 ; apply maponpaths.
    + apply vcomp_rinv.
    + apply vcomp_lid.
Defined.

Section StrictPseudoFunctorDerivedLaws.
  Context {C D : bicat}.
  Variable (F : strict_psfunctor C D).

  Definition strict_psfunctor_linvunitor
             {a b : C}
             (f : C⟦a, b⟧)
    : ##F (linvunitor f)
      =
      (linvunitor (#F f))
        • ((strict_psfunctor_id_cell F a) ▹ #F f)
        • (strict_psfunctor_comp_cell F _ _).
  Proof.
    rewrite !vassocl.
    cbn.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (strict_psfunctor_is_iso F (linvunitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite strict_psfunctor_lunitor ; cbn.
    rewrite <- !vassocr.
    reflexivity.
  Qed.

  Definition strict_psfunctor_rinvunitor
             {a b : C}
             (f : C⟦a, b⟧)
    : ##F (rinvunitor f)
      =
      (rinvunitor (#F f))
        • (#F f ◃ strict_psfunctor_id_cell F b)
        • strict_psfunctor_comp_cell F _ _.
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (strict_psfunctor_is_iso F (rinvunitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite strict_psfunctor_runitor ; cbn.
    rewrite <- !vassocr.
    reflexivity.
  Qed.

  Definition strict_psfunctor_rassociator
             {a b c d : C}
             (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
    : (strict_psfunctor_comp_cell F f g ▹ #F h)
        • strict_psfunctor_comp_cell F (f · g) h
        • ##F (rassociator f g h)
      =
      (rassociator (#F f) (#F g) (#F h))
        • (#F f ◃ strict_psfunctor_comp_cell F g h)
        • strict_psfunctor_comp_cell F f (g · h).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    use vcomp_move_R_Mp.
    { refine (strict_psfunctor_is_iso F (rassociator f g h ,, _)).
      is_iso.
    }
    cbn.
    symmetry.
    exact (strict_psfunctor_lassociator F f g h).
  Qed.

  Definition strict_psfunctor_comp_natural
             {a b c : C}
             {g₁ g₂ : C⟦b,c⟧} {f₁ f₂ : C⟦a,b⟧}
             (ηg : g₁ ==> g₂) (ηf : f₁ ==> f₂)
    : strict_psfunctor_comp_cell F f₁ g₁ • ##F (ηf ⋆ ηg)
      =
      (##F ηf) ⋆ (##F ηg) • strict_psfunctor_comp_cell F f₂ g₂.
  Proof.
    unfold hcomp.
    rewrite !strict_psfunctor_vcomp.
    rewrite !vassocr.
    rewrite !strict_psfunctor_rwhisker.
    rewrite !vassocl.
    rewrite strict_psfunctor_lwhisker.
    reflexivity.
  Qed.

  Definition strict_psfunctor_F_lunitor
             {a b : C}
             (f : C⟦a, b⟧)
    : ##F (lunitor f)
      =
      ((strict_psfunctor_comp_cell F (identity a) f)^-1)
        • ((strict_psfunctor_id_cell F a)^-1 ▹ #F f)
        • lunitor (#F f).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    exact (!(strict_psfunctor_lunitor F f)).
  Qed.

  Definition strict_psfunctor_F_runitor
             {a b : C}
             (f : C⟦a,b⟧)
    : ##F (runitor f)
      =
      ((strict_psfunctor_comp_cell F f (identity b))^-1)
        • (#F f ◃ (strict_psfunctor_id_cell F b)^-1)
        • runitor (#F f).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    exact (!(strict_psfunctor_runitor F f)).
  Qed.
End StrictPseudoFunctorDerivedLaws.

Definition strict_pstrans_data
           {C D : bicat}
           (F G : strict_psfunctor C D)
  : UU.
Proof.
  refine (map1cells C D⟦_,_⟧).
  - apply F.
  - apply G.
Defined.

Definition is_strict_pstrans
           {C D : bicat}
           {F G : strict_psfunctor C D}
           (η : strict_pstrans_data F G)
  : UU
  := (∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
      (pr1 η X ◃ ##G α)
        • pr2 η _ _ g
      =
      (pr2 η _ _ f)
        • (##F α ▹ pr1 η Y))
       ×
       (∏ (X : C),
        (pr1 η X ◃ strict_psfunctor_id_cell G X)
          • pr2 η _ _ (id₁ X)
        =
        (runitor (pr1 η X))
          • linvunitor (pr1 η X)
          • (strict_psfunctor_id_cell F X ▹ pr1 η X))
       ×
       (∏ (X Y Z : C) (f : X --> Y) (g : Y --> Z),
        (pr1 η X ◃ strict_psfunctor_comp_cell G f g)
          • pr2 η _ _ (f · g)
        =
        (lassociator (pr1 η X) (#G f) (#G g))
          • (pr2 η _ _ f ▹ (#G g))
          • rassociator (#F f) (pr1 η Y) (#G g)
          • (#F f ◃ pr2 η _ _ g)
          • lassociator (#F f) (#F g) (pr1 η Z)
          • (strict_psfunctor_comp_cell F f g ▹ pr1 η Z)).

Definition make_strict_pstrans
           {C D : bicat}
           {F G : strict_psfunctor C D}
           (η : strict_pstrans_data F G)
           (Hη : is_strict_pstrans η)
  : F --> G.
Proof.
  refine ((η ,, _) ,, tt).
  repeat split ; cbn ; intros ; apply Hη.
Defined.

Definition strict_modification_eq
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           {m m' : σ ==> τ}
           (p : ∏ (X : B), pr111 m X = pr111 m' X)
  : m = m'.
Proof.
  use subtypePath.
  { intro. simpl.
    exact isapropunit.
  }
  use subtypePath.
  { intro. simpl.
    repeat (apply isapropdirprod) ; apply isapropunit.
  }
  use subtypePath.
  { intro. simpl.
    repeat (apply impred ; intro).
    apply B'.
  }
  use funextsec.
  exact p.
Qed.

Definition is_strict_modification
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           (m : ∏ (X : B), pr111 σ X ==> pr111 τ X)
  : UU
  := ∏ (X Y : B) (f : X --> Y),
     pr211 σ _ _ f • (m Y ▻ #F f)
     =
     #G f ◅ m X • pr211 τ _ _ f.

Definition make_strict_modification
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           (m : ∏ (X : B), pr111 σ X ==> pr111 τ X)
           (Hm : is_strict_modification m)
  : σ ==> τ
  := (((m ,, Hm) ,, (tt ,, tt ,, tt)),, tt).

Definition make_is_invertible_strict_modification_inv_is_modification
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           (m : σ ==> τ)
           (Hm : ∏ (X : B), is_invertible_2cell (pr111 m X))
  : ∏ (X Y : B) (f : B ⟦ X, Y ⟧),
    (pr211 τ) X Y f • (# F f ◃ (Hm Y) ^-1) = ((Hm X) ^-1 ▹ # G f) • (pr211 σ) X Y f.
Proof.
  intros X Y f.
  simpl.
  use vcomp_move_R_Mp.
  { is_iso. }
  simpl.
  rewrite <- vassocr.
  use vcomp_move_L_pM.
  { is_iso. }
  symmetry.
  simpl.
  exact (pr211 m X Y f).
Qed.

Definition inv_modification
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           (m : σ ==> τ)
           (Hm : ∏ (X : B), is_invertible_2cell (pr111 m X))
  : τ ==> σ.
Proof.
  use make_strict_modification.
  - exact (λ X, (Hm X)^-1).
  - exact (make_is_invertible_strict_modification_inv_is_modification m Hm).
Defined.

Definition modification_inv_modification
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           (m : σ ==> τ)
           (Hm : ∏ (X : B), is_invertible_2cell (pr111 m X))
  : m • inv_modification m Hm = id₂ σ.
Proof.
  use strict_modification_eq.
  intro X.
  cbn.
  exact (vcomp_rinv (Hm X)).
Qed.

Definition inv_modification_modification
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           (m : σ ==> τ)
           (Hm : ∏ (X : B), is_invertible_2cell (pr111 m X))
  : inv_modification m Hm • m = id₂ τ.
Proof.
  use strict_modification_eq.
  intro X.
  cbn.
  exact (vcomp_lid (Hm X)).
Qed.

Definition make_is_invertible_strict_modification
           {B B' : bicat}
           {F G : strict_psfunctor B B'}
           {σ τ : F --> G}
           (m : σ ==> τ)
           (Hm : ∏ (X : B), is_invertible_2cell (pr111 m X))
  : is_invertible_2cell m.
Proof.
  use make_is_invertible_2cell.
  - exact (inv_modification m Hm).
  - exact (modification_inv_modification m Hm).
  - exact (inv_modification_modification m Hm).
Defined.

Module Notations.
  Notation "'##'" := (strict_psfunctor_on_cells).
End Notations.
