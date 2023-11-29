Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.StrictTwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.StrictDoubleCatBasics.
Require Import UniMath.Bicategories.DoubleCategories.CatOfStrictDoubleCats.

Local Open Scope cat.

Declare Scope strict_double_cat.

Local Open Scope strict_double_cat.

(** * 1. Strict double categories *)
Definition strict_double_cat
  : UU
  := ob univalent_cat_of_strict_double_cat.

(** * 2. Accessors for double categories *)

(** ** 2.1. The vertical category *)
Definition ob_strict_double_cat
           (C : strict_double_cat)
  : setcategory
  := pr111 C.

Coercion ob_strict_double_cat : strict_double_cat >-> setcategory.

Definition isaset_ob_ob_strict_double_cat
           (C : strict_double_cat)
  : isaset C.
Proof.
  apply isaset_ob.
Defined.

Definition ver_mor_strict_double_cat
           {C : strict_double_cat}
           (x y : C)
  : UU
  := x --> y.

Notation "x -->v y" := (ver_mor_strict_double_cat x y) (at level 55) : strict_double_cat.

Proposition isaset_ver_mor_strict_double_cat
            {C : strict_double_cat}
            (x y : C)
  : isaset (x -->v y).
Proof.
  apply homset_property.
Defined.

Definition s_identity_v
           {C : strict_double_cat}
           (x : C)
  : x -->v x
  := identity _.

Definition ver_comp_strict_double_cat
           {C : strict_double_cat}
           {x y z : C}
           (f : x -->v y)
           (g : y -->v z)
  : x -->v z
  := f · g.

Notation "f ·v g" := (ver_comp_strict_double_cat f g) (at level 60) : strict_double_cat.

Proposition s_id_v_left
            {C : strict_double_cat}
            {x y : C}
            (f : x -->v y)
  : s_identity_v x · f = f.
Proof.
  apply id_left.
Defined.

Proposition s_id_v_right
            {C : strict_double_cat}
            {x y : C}
            (f : x -->v y)
  : f ·v s_identity_v y = f.
Proof.
  apply id_right.
Defined.

Proposition s_assocl_v
            {C : strict_double_cat}
            {w x y z : C}
            (f : w -->v x)
            (g : x -->v y)
            (h : y -->v z)
  : f ·v (g ·v h) = (f ·v g) ·v h.
Proof.
  apply assoc.
Defined.

Proposition s_assocr_v
            {C : strict_double_cat}
            {w x y z : C}
            (f : w -->v x)
            (g : x -->v y)
            (h : y -->v z)
  : (f ·v g) ·v h = f ·v (g ·v h).
Proof.
  apply assoc'.
Defined.

Proposition isaset_ver_mor_strict
            {C : strict_double_cat}
            (x y : C)
  : isaset (x -->v y).
Proof.
  apply homset_property.
Qed.

(** ** 2.2. Horizontal morphisms *)
Definition strict_hor_mor
           (C : strict_double_cat)
  : strict_twosided_disp_cat C C
  := pr211 C.

Notation "x -->h y" := (strict_hor_mor _ x y) (at level 55) : strict_double_cat.

Proposition isaset_hor_mor_strict_double_cat
            {C : strict_double_cat}
            (x y : C)
  : isaset (x -->h y).
Proof.
  apply is_strict_strict_twosided_disp_cat.
Defined.

Definition hor_id_strict_double_cat
           (C : strict_double_cat)
  : hor_id (strict_hor_mor C)
  := pr121 C.

Definition s_identity_h
           {C : strict_double_cat}
           (x : C)
  : x -->h x
  := double_id (hor_id_strict_double_cat C) x.

Definition hor_comp_strict_double_cat
           (C : strict_double_cat)
  : hor_comp (strict_hor_mor C)
  := pr221 C.

Definition hor_mor_comp_strict_double_cat
           {C : strict_double_cat}
           {x y z : C}
           (f : x -->h y)
           (g : y -->h z)
  : x -->h z
  := double_hor_comp (hor_comp_strict_double_cat C) f g.

Notation "f ·h g" := (hor_mor_comp_strict_double_cat f g) (at level 60) : strict_double_cat.

(** ** 2.3. Squares *)
Definition s_square
           {C : strict_double_cat}
           {x₁ x₂ y₁ y₂ : C}
           (v₁ : x₁ -->v y₁)
           (v₂ : x₂ -->v y₂)
           (h₁ : x₁ -->h x₂)
           (h₂ : y₁ -->h y₂)
  : UU
  := h₁ -->[ v₁ ][ v₂ ] h₂.

Proposition isaset_s_square
            {C : strict_double_cat}
            {x₁ x₂ y₁ y₂ : C}
            (v₁ : x₁ -->v y₁)
            (v₂ : x₂ -->v y₂)
            (h₁ : x₁ -->h x₂)
            (h₂ : y₁ -->h y₂)
  : isaset (s_square v₁ v₂ h₁ h₂).
Proof.
  apply isaset_disp_mor.
Defined.

Definition s_id_v_square
           {C : strict_double_cat}
           {x y : C}
           (h : x -->h y)
  : s_square (s_identity_v x) (s_identity_v y) h h
  := id_two_disp _.

Definition s_comp_v_square
           {C : strict_double_cat}
           {x₁ x₂ y₁ y₂ z₁ z₂ : C}
           {v₁ : x₁ -->v y₁} {v₁' : y₁ --> z₁}
           {v₂ : x₂ -->v y₂} {v₂' : y₂ --> z₂}
           {h₁ : x₁ -->h x₂}
           {h₂ : y₁ -->h y₂}
           {h₃ : z₁ -->h z₂}
           (s₁ : s_square v₁ v₂ h₁ h₂)
           (s₂ : s_square v₁' v₂' h₂ h₃)
  : s_square (v₁ ·v v₁') (v₂ ·v v₂') h₁ h₃
  := s₁ ;;2 s₂.

Notation "s₁ ⋆v s₂" := (s_comp_v_square s₁ s₂) (at level 40, left associativity)
    : strict_double_cat.

Definition transportf_s_square
           {C : strict_double_cat}
           {x₁ x₂ y₁ y₂ : C}
           {v₁ v₁' : x₁ -->v y₁}
           {v₂ v₂' : x₂ -->v y₂}
           {h₁ h₁' : x₁ -->h x₂}
           {h₂ h₂' : y₁ -->h y₂}
           (s : s_square v₁ v₂ h₁ h₂)
           (p₁ : v₁ = v₁')
           (p₂ : v₂ = v₂')
           (p₃ : h₁ = h₁')
           (p₄ : h₂ = h₂')
  : s_square v₁' v₂' h₁' h₂'
  := transportf_disp_mor2 p₁ p₂ (transportf_hor_mor p₃ p₄ s).

Definition transportb_s_square
           {C : strict_double_cat}
           {x₁ x₂ y₁ y₂ : C}
           {v₁ v₁' : x₁ -->v y₁}
           {v₂ v₂' : x₂ -->v y₂}
           {h₁ h₁' : x₁ -->h x₂}
           {h₂ h₂' : y₁ -->h y₂}
           (s : s_square v₁' v₂' h₁' h₂')
           (p₁ : v₁ = v₁')
           (p₂ : v₂ = v₂')
           (p₃ : h₁ = h₁')
           (p₄ : h₂ = h₂')
  : s_square v₁ v₂ h₁ h₂
  := transportb_disp_mor2 p₁ p₂ (transportb_hor_mor p₃ p₄ s).

Proposition s_square_id_left_v
            {C : strict_double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : s_square v₁ v₂ h₁ h₂)
  : s_id_v_square h₁ ⋆v s
    =
    transportb_s_square s (id_left _) (id_left _) (idpath _) (idpath _).
Proof.
  apply id_two_disp_left.
Defined.

Proposition s_square_id_right_v
            {C : strict_double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v y₁}
            {v₂ : x₂ -->v y₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            (s : s_square v₁ v₂ h₁ h₂)
  : s ⋆v s_id_v_square h₂
    =
    transportb_s_square s (id_right _) (id_right _) (idpath _) (idpath _).
Proof.
  apply id_two_disp_right.
Defined.

Proposition s_square_assoc_v
            {C : strict_double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {v₁ : w₁ -->v x₁} {v₁' : x₁ -->v y₁} {v₁'' : y₁ -->v z₁}
            {v₂ : w₂ -->v x₂} {v₂' : x₂ -->v y₂} {v₂'' : y₂ -->v z₂}
            {h₁ : w₁ -->h w₂}
            {h₂ : x₁ -->h x₂}
            {h₃ : y₁ -->h y₂}
            {h₄ : z₁ -->h z₂}
            (s₁ : s_square v₁ v₂ h₁ h₂)
            (s₂ : s_square v₁' v₂' h₂ h₃)
            (s₃ : s_square v₁'' v₂'' h₃ h₄)
  : s₁ ⋆v (s₂ ⋆v s₃)
    =
    transportb_s_square
      ((s₁ ⋆v s₂) ⋆v s₃)
      (assoc _ _ _) (assoc _ _ _)
      (idpath _) (idpath _).
Proof.
  exact (assoc_two_disp s₁ s₂ s₃).
Defined.

(** ** 2.4. Functoriality of horizontal identities *)
Definition s_id_h_square
           {C : strict_double_cat}
           {x y : C}
           (v : x -->v y)
  : s_square v v (s_identity_h x) (s_identity_h y)
  := double_id_mor (hor_id_strict_double_cat C) v.

Proposition s_id_h_square_id
            {C : strict_double_cat}
            (x : C)
  : s_id_h_square (s_identity_v x) = s_id_v_square (s_identity_h x).
Proof.
  apply double_id_mor_id.
Defined.

Proposition s_id_h_square_comp
            {C : strict_double_cat}
            {x y z : C}
            (v₁ : x -->v y)
            (v₂ : y -->v z)
  : s_id_h_square (v₁ ·v v₂)
    =
    s_id_h_square v₁ ⋆v s_id_h_square v₂.
Proof.
  apply double_id_mor_id_comp.
Defined.

(** ** 2.5. Functoriality of horizontal composition *)
Definition s_comp_h_square
           {C : strict_double_cat}
           {x₁ x₂ y₁ y₂ z₁ z₂ : C}
           {v₁ : x₁ -->v x₂}
           {v₂ : y₁ -->v y₂}
           {v₃ : z₁ -->v z₂}
           {h₁ : x₁ -->h y₁}
           {h₂ : y₁ -->h z₁}
           {k₁ : x₂ -->h y₂}
           {k₂ : y₂ -->h z₂}
           (s₁ : s_square v₁ v₂ h₁ k₁)
           (s₂ : s_square v₂ v₃ h₂ k₂)
  : s_square v₁ v₃ (h₁ ·h h₂) (k₁ ·h k₂)
  := double_hor_comp_mor (hor_comp_strict_double_cat C) s₁ s₂.

Notation "s₁ ⋆h s₂" := (s_comp_h_square s₁ s₂) (at level 40, left associativity)
    : strict_double_cat.

Proposition s_comp_h_square_id
            {C : strict_double_cat}
            {x y z : C}
            (h₁ : x -->h y)
            (h₂ : y -->h z)
  : s_id_v_square h₁ ⋆h s_id_v_square h₂ = s_id_v_square (h₁ ·h h₂).
Proof.
  apply double_hor_comp_mor_id.
Defined.

Proposition comp_h_square_comp
            {C : strict_double_cat}
            {x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : C}
            {v₁ : x₁ -->v x₂} {v₁' : x₂ -->v x₃}
            {v₂ : y₁ -->v y₂} {v₂' : y₂ -->v y₃}
            {v₃ : z₁ -->v z₂} {v₃' : z₂ -->v z₃}
            {h₁ : x₁ -->h y₁} {h₂ : y₁ -->h z₁}
            {k₁ : x₂ -->h y₂} {k₂ : y₂ -->h z₂}
            {l₁ : x₃ -->h y₃} {l₂ : y₃ -->h z₃}
            (s₁ : s_square v₁ v₂ h₁ k₁)
            (s₁' : s_square v₁' v₂' k₁ l₁)
            (s₂ : s_square v₂ v₃ h₂ k₂)
            (s₂' : s_square v₂' v₃' k₂ l₂)
  : (s₁ ⋆v s₁') ⋆h (s₂ ⋆v s₂') = (s₁ ⋆h s₂) ⋆v (s₁' ⋆h s₂').
Proof.
  apply double_hor_comp_mor_comp.
Defined.

(** ** 2.6. Laws for horizontal composition *)
Proposition s_id_h_left
            {C : strict_double_cat}
            {x y : C}
            (h : x -->h y)
  : s_identity_h x ·h h = h.
Proof.
  exact (pr12 C x y h).
Defined.

Proposition s_id_h_right
            {C : strict_double_cat}
            {x y : C}
            (h : x -->h y)
  : h ·h s_identity_h y = h.
Proof.
  exact (pr122 C x y h).
Defined.

Proposition s_assocl_h
            {C : strict_double_cat}
            {w x y z : C}
            (h₁ : w -->h x)
            (h₂ : x -->h y)
            (h₃ : y -->h z)
  : h₁ ·h (h₂ ·h h₃) = (h₁ ·h h₂) ·h h₃.
Proof.
  exact (pr1 (pr222 C) w x y z h₁ h₂ h₃).
Defined.

Proposition strict_square_id_left
            {C : strict_double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h : x₁ -->h y₁}
            {k : x₂ -->h y₂}
            (s : s_square v₁ v₂ h k)
  : s_id_h_square v₁ ⋆h s
    =
    transportb_s_square
      s
      (idpath _) (idpath _)
      (s_id_h_left _)
      (s_id_h_left _).
Proof.
  exact (pr12 (pr222 C) x₁ x₂ y₁ y₂ v₁ v₂ h k s).
Defined.

Proposition strict_square_id_right
            {C : strict_double_cat}
            {x₁ x₂ y₁ y₂ : C}
            {v₁ : x₁ -->v x₂}
            {v₂ : y₁ -->v y₂}
            {h : x₁ -->h y₁}
            {k : x₂ -->h y₂}
            (s : s_square v₁ v₂ h k)
  : s ⋆h s_id_h_square v₂
    =
    transportb_s_square
      s
      (idpath _) (idpath _)
      (s_id_h_right _)
      (s_id_h_right _).
Proof.
  exact (pr122 (pr222 C) x₁ x₂ y₁ y₂ v₁ v₂ h k s).
Defined.

Proposition strict_square_assoc
            {C : strict_double_cat}
            {w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ : C}
            {vw : w₁ -->v w₂}
            {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂}
            {vz : z₁ -->v z₂}
            {h₁ : w₁ -->h x₁} {h₂ : x₁ -->h y₁} {h₃ : y₁ -->h z₁}
            {k₁ : w₂ -->h x₂} {k₂ : x₂ -->h y₂} {k₃ : y₂ -->h z₂}
            (s₁ : s_square vw vx h₁ k₁)
            (s₂ : s_square vx vy h₂ k₂)
            (s₃ : s_square vy vz h₃ k₃)
  : s₁ ⋆h (s₂ ⋆h s₃)
    =
    transportb_s_square
      ((s₁ ⋆h s₂) ⋆h s₃)
      (idpath _) (idpath _)
      (s_assocl_h _ _ _)
      (s_assocl_h _ _ _).
Proof.
  apply (pr222 (pr222 C) w₁ w₂ x₁ x₂ y₁ y₂ z₁ z₂ vw vx vy vz h₁ h₂ h₃ k₁ k₂ k₃ s₁ s₂ s₃).
Defined.

Definition id_h_to_s_square
           {C : strict_double_cat}
           {x y : C}
           {h₁ h₂ : x -->h y}
           (p : h₁ = h₂)
  : s_square (s_identity_v x) (s_identity_v y) h₁ h₂
  := pr1 (idtoiso_twosided_disp (idpath _) (idpath _) p).

(** * 3. Builder for strict double categories *)
Definition make_strict_double_cat
           (C : setcategory)
           (D : twosided_disp_cat C C)
           (HD : is_strict_twosided_disp_cat D)
           (I : hor_id D)
           (Cm : hor_comp D)
           (idl : strict_double_cat_id_left I Cm)
           (idr : strict_double_cat_id_right I Cm)
           (assoc : strict_double_cat_assoc Cm)
           (s_idl : strict_double_cat_id_left_square idl)
           (s_idr : strict_double_cat_id_right_square idr)
           (s_assoc : strict_double_cat_assoc_square assoc)
  : strict_double_cat
  := ((C ,, (D ,, HD)) ,, (I ,, Cm)) ,, (idl ,, idr ,, assoc ,, s_idl ,,s_idr ,, s_assoc).

(** * 4. Strict functors for strict double categories *)
Definition strict_double_functor
           (C₁ C₂ : strict_double_cat)
  : UU
  := C₁ --> C₂.

Definition id_strict_double_functor
           (C : strict_double_cat)
  : strict_double_functor C C
  := identity _.

Definition comp_strict_double_functor
           {C₁ C₂ C₃ : strict_double_cat}
           (F : strict_double_functor C₁ C₂)
           (G : strict_double_functor C₂ C₃)
  : strict_double_functor C₁ C₃
  := F · G.

(** * 5. Accessors for strict double functors *)
Definition strict_double_functor_ver
           {C₁ C₂ : strict_double_cat}
           (F : strict_double_functor C₁ C₂)
  : C₁ ⟶ C₂
  := pr111 F.

Coercion strict_double_functor_ver : strict_double_functor >-> functor.

Definition strict_double_functor_ver_mor
           {C₁ C₂ : strict_double_cat}
           (F : strict_double_functor C₁ C₂)
           {x y : C₁}
           (f : x -->v y)
  : F x -->v F y
  := #(strict_double_functor_ver F) f.

Notation "'#v' F f" := (strict_double_functor_ver_mor F f)
                         (at level 10, F at next level, f at next level) : strict_double_cat.

Proposition strict_double_functor_id_v
            {C₁ C₂ : strict_double_cat}
            (F : strict_double_functor C₁ C₂)
            (x : C₁)
  : #v F (s_identity_v x) = s_identity_v _.
Proof.
  apply functor_id.
Defined.

Proposition strict_double_functor_comp_v
            {C₁ C₂ : strict_double_cat}
            (F : strict_double_functor C₁ C₂)
            {x y z : C₁}
            (f : x -->v y)
            (g : y -->v z)
  : #v F (f ·v g) = #v F f ·v #v F g.
Proof.
  apply functor_comp.
Defined.

Definition strict_double_functor_hor_mor
           {C₁ C₂ : strict_double_cat}
           (F : strict_double_functor C₁ C₂)
  : twosided_disp_functor F F (strict_hor_mor C₁) (strict_hor_mor C₂)
  := pr211 F.

Notation "'#h' F f" := (strict_double_functor_hor_mor F _ _ f)
                         (at level 10, F at next level, f at next level) : strict_double_cat.
Notation "'#s' F s" := (#2 (strict_double_functor_hor_mor F) s)
                         (at level 10, F at next level, s at next level) : strict_double_cat.

Proposition strict_double_functor_id_square
            {C₁ C₂ : strict_double_cat}
            (F : strict_double_functor C₁ C₂)
            {x y : C₁}
            (h : x -->h y)
  : #s F (s_id_v_square h)
    =
    transportb_s_square
      (s_id_v_square _)
      (strict_double_functor_id_v _ _)
      (strict_double_functor_id_v _ _)
      (idpath _) (idpath _).
Proof.
  exact (twosided_disp_functor_id _ _ _ _ (strict_double_functor_hor_mor F) h).
Qed.

Proposition lax_double_functor_comp_v_square
            {C₁ C₂ : strict_double_cat}
            (F : strict_double_functor C₁ C₂)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C₁}
            {v₁ : x₁ -->v y₁} {v₁' : y₁ --> z₁}
            {v₂ : x₂ -->v y₂} {v₂' : y₂ --> z₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            {h₃ : z₁ -->h z₂}
            (s₁ : s_square v₁ v₂ h₁ h₂)
            (s₂ : s_square v₁' v₂' h₂ h₃)
  : #s F (s₁ ⋆v s₂)
    =
    transportb_s_square
      (#s F s₁ ⋆v #s F s₂)
      (strict_double_functor_comp_v _ _ _)
      (strict_double_functor_comp_v _ _ _)
      (idpath _) (idpath _).
Proof.
  apply (twosided_disp_functor_comp _ _ _ _ (strict_double_functor_hor_mor F)).
Qed.

Definition strict_double_functor_preserves_hor_id
           {C₁ C₂ : strict_double_cat}
           (F : strict_double_functor C₁ C₂)
  : preserves_hor_id
      (hor_id_strict_double_cat C₁)
      (hor_id_strict_double_cat C₂)
      (strict_double_functor_hor_mor F)
  := pr121 F.

Proposition strict_double_functor_hor_id
            {C₁ C₂ : strict_double_cat}
            (F : strict_double_functor C₁ C₂)
            (x : C₁)
  : #h F (s_identity_h x) = s_identity_h (F x).
Proof.
  exact (strict_double_functor_preserves_hor_id F x).
Defined.

Proposition strict_double_functor_hor_id_mor
            {C₁ C₂ : strict_double_cat}
            (F : strict_double_functor C₁ C₂)
            {x y : C₁}
            (f : x --> y)
  : #s F (s_id_h_square f) ⋆v id_h_to_s_square (strict_double_functor_hor_id F y)
    =
    transportf_s_square
      (id_h_to_s_square (strict_double_functor_hor_id F x) ⋆v s_id_h_square (#F f))
      (s_id_v_left _ @ !(s_id_v_right _))
      (s_id_v_left _ @ !(s_id_v_right _))
      (idpath _) (idpath _).
Proof.
  exact (is_natural_preserves_hor_id (strict_double_functor_preserves_hor_id F) f).
Defined.

Definition strict_double_functor_preserves_hor_comp
           {C₁ C₂ : strict_double_cat}
           (F : strict_double_functor C₁ C₂)
  : preserves_hor_comp
      (hor_comp_strict_double_cat C₁)
      (hor_comp_strict_double_cat C₂)
      (strict_double_functor_hor_mor F)
  := pr221 F.

Proposition strict_double_functor_hor_comp
            {C₁ C₂ : strict_double_cat}
            (F : strict_double_functor C₁ C₂)
            {x y z : C₁}
            (h : x -->h y)
            (k : y -->h z)
  : #h F (h ·h k) = #h F h ·h #h F k.
Proof.
  exact (strict_double_functor_preserves_hor_comp F _ _ _ h k).
Defined.

Proposition strict_double_functor_hor_comp_mor
            {C₁ C₂ : strict_double_cat}
            (F : strict_double_functor C₁ C₂)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C₁}
            {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂}
            {vz : z₁ -->v z₂}
            {h₁ : x₁ -->h y₁}
            {k₁ : y₁ -->h z₁}
            {h₂ : x₂ -->h y₂}
            {k₂ : y₂ -->h z₂}
            (s₁ : s_square vx vy h₁ h₂)
            (s₂ : s_square vy vz k₁ k₂)
  : #s F (s₁ ⋆h s₂) ⋆v id_h_to_s_square (strict_double_functor_hor_comp F h₂ k₂)
    =
    transportf_s_square
      (id_h_to_s_square (strict_double_functor_hor_comp F h₁ k₁) ⋆v (#s F s₁ ⋆h #s F s₂))
      (s_id_v_left _ @ !(s_id_v_right _))
      (s_id_v_left _ @ !(s_id_v_right _))
      (idpath _) (idpath _).
Proof.
  exact (is_natural_preserves_hor_comp
           (strict_double_functor_preserves_hor_comp F)
           s₁ s₂).
Qed.

(** * 6. Builder for strict double functors *)
Definition make_strict_double_functor
           {C₁ C₂ : strict_double_cat}
           (F : C₁ ⟶ C₂)
           (FF : twosided_disp_functor F F (strict_hor_mor C₁) (strict_hor_mor C₂))
           (FFI : preserves_hor_id
                    (hor_id_strict_double_cat C₁)
                    (hor_id_strict_double_cat C₂)
                    FF)
           (FFC : preserves_hor_comp
                    (hor_comp_strict_double_cat C₁)
                    (hor_comp_strict_double_cat C₂)
                    FF)
  : strict_double_functor C₁ C₂
  := ((F ,, FF) ,, (FFI ,, FFC)) ,, tt.
