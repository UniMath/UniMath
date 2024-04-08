(**********************************************************************************

 Univalent double categories

 In this file, we provide an interface for the bicategory of double categories.
 More specifically, we give definitions and notations for accessors of double
 categories, double functors, and double transformations. We also give builders
 for each of them.

 Contents
 1. Double categories
 2. Accessors for double categories
 3. Builder for double categories
 4. Lax functors for double categories
 5. Accessors for lax functors
 6. Builder for lax functors
 7. Strong double functors
 8. Double transformations
 9. Accessors for double transformations
 10. Builder for double transformations

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedNatTrans.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfTwoSidedDispCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleFunctor.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleTransformation.
Require Import UniMath.Bicategories.DoubleCategories.Core.BicatOfDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.

Local Open Scope cat.

Declare Scope double_cat.

Local Open Scope double_cat.

(** * 1. Univalent double categories *)
Definition univalent_double_cat
  : UU
  := ob bicat_of_double_cats.

(** * 2. Accessors for univalent double categories *)
Coercion univalent_double_cat_to_double_cat
         (C : univalent_double_cat)
  : double_cat
  := make_double_cat
       _
       _
       _
       _
       _
       _
       _
       (pr12 C)
       (pr22 C).

Proposition is_univalent_vertical_cat
            (C : univalent_double_cat)
  : is_univalent C.
Proof.
  exact (pr21 (pr111 C)).
Qed.

Proposition is_univalent_twosided_disp_cat_hor_mor
            (C : univalent_double_cat)
  : is_univalent_twosided_disp_cat (hor_mor C).
Proof.
  exact (pr22 (pr111 C)).
Qed.

Definition globular_iso_square_to_path
           {C : univalent_double_cat}
           {x y : C}
           {h₁ h₂ : x -->h y}
           (s : globular_iso_square h₁ h₂)
  : h₁ = h₂.
Proof.
  exact (isotoid_twosided_disp
           (is_univalent_twosided_disp_cat_hor_mor C)
           (idpath _) (idpath _)
           s).
Defined.

(** * 3. Builder for double categories *)
Definition is_univalent_double_cat
           (C : double_cat)
  : UU
  := is_univalent C
     ×
     is_univalent_twosided_disp_cat (hor_mor C).

Definition make_univalent_double_cat
           (C : double_cat)
           (HC : is_univalent_double_cat C)
  : univalent_double_cat.
Proof.
  simple refine ((((_ ,, _) ,, _) ,, _) ,, _).
  - exact (_ ,, pr1 HC).
  - exact (hor_mor C ,, pr2 HC).
  - exact (hor_id_double_cat C ,, hor_comp_double_cat C).
  - exact (double_cat_double_lunitor C
           ,,
           double_cat_double_runitor C
           ,,
           double_cat_double_associator C).
  - exact (@double_triangle C ,, @double_pentagon C).
Defined.

(** * 4. Lax functors for double categories *)
Definition lax_double_functor
           (C₁ C₂ : univalent_double_cat)
  : UU
  := C₁ --> C₂.

Definition id_lax_double_functor
           (C : univalent_double_cat)
  : lax_double_functor C C
  := identity _.

Definition comp_lax_double_functor
           {C₁ C₂ C₃ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
           (G : lax_double_functor C₂ C₃)
  : lax_double_functor C₁ C₃
  := F · G.

(** * 5. Accessors for lax functors *)
Definition lax_double_functor_ver
           {C₁ C₂ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
  : C₁ ⟶ C₂
  := pr1 (pr111 F).

Coercion lax_double_functor_ver : lax_double_functor >-> functor.

Definition lax_double_functor_ver_mor
           {C₁ C₂ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
           {x y : C₁}
           (f : x -->v y)
  : F x -->v F y
  := pr211 (pr111 F) x y f.

Notation "'#v' F f" := (lax_double_functor_ver_mor F f)
                         (at level 10, F at next level, f at next level) : double_cat.

Proposition lax_double_functor_id_v
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
            (x : C₁)
  : #v F (identity_v x) = identity_v _.
Proof.
  apply functor_id.
Defined.

Proposition lax_double_functor_comp_v
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y z : C₁}
            (f : x -->v y)
            (g : y -->v z)
  : #v F (f ·v g) = #v F f ·v #v F g.
Proof.
  apply functor_comp.
Defined.

Definition lax_double_functor_hor_mor
           {C₁ C₂ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
  : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂)
  := pr2 (pr111 F).

Notation "'#h' F f" := (lax_double_functor_hor_mor F _ _ f)
                         (at level 10, F at next level, f at next level) : double_cat.
Notation "'#s' F s" := (#2 (lax_double_functor_hor_mor F) s)
                         (at level 10, F at next level, s at next level) : double_cat.

Proposition lax_double_functor_id_square
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y : C₁}
            (h : x -->h y)
  : #s F (id_v_square h)
    =
    transportb_square
      (lax_double_functor_id_v _ _)
      (lax_double_functor_id_v _ _)
      (id_v_square _).
Proof.
  exact (twosided_disp_functor_id _ _ _ _ (lax_double_functor_hor_mor F) h).
Qed.

Proposition lax_double_functor_comp_v_square
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C₁}
            {v₁ : x₁ -->v y₁} {v₁' : y₁ --> z₁}
            {v₂ : x₂ -->v y₂} {v₂' : y₂ --> z₂}
            {h₁ : x₁ -->h x₂}
            {h₂ : y₁ -->h y₂}
            {h₃ : z₁ -->h z₂}
            (s₁ : square v₁ v₂ h₁ h₂)
            (s₂ : square v₁' v₂' h₂ h₃)
  : #s F (s₁ ⋆v s₂)
    =
    transportb_square
      (lax_double_functor_comp_v _ _ _)
      (lax_double_functor_comp_v _ _ _)
      (#s F s₁ ⋆v #s F s₂).
Proof.
  apply (twosided_disp_functor_comp _ _ _ _ (lax_double_functor_hor_mor F)).
Qed.

Definition lax_double_functor_hor_id
           {C₁ C₂ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
  : double_functor_hor_id
      (lax_double_functor_hor_mor F)
      (hor_id_double_cat C₁)
      (hor_id_double_cat C₂)
  := pr1 (pr211 F).

Definition lax_double_functor_id_h
           {C₁ C₂ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
           (x : C₁)
  : square (identity_v _) (identity_v (F x)) (identity_h _) (#h F (identity_h _)).
Proof.
  exact (pr11 (pr211 F) x).
Defined.

Proposition lax_double_functor_id_h_mor
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y : C₁}
            (f : x -->v y)
  : id_h_square (#v F f) ⋆v lax_double_functor_id_h F y
    =
    transportb_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (lax_double_functor_id_h F x ⋆v #s F (id_h_square f)).
Proof.
  exact (pr21 (pr211 F) x y f).
Qed.

Definition lax_double_functor_hor_comp
           {C₁ C₂ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
  : double_functor_hor_comp
      (lax_double_functor_hor_mor F)
      (hor_comp_double_cat C₁)
      (hor_comp_double_cat C₂)
  := pr2 (pr211 F).

Definition lax_double_functor_comp_h
           {C₁ C₂ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
           {x y z : C₁}
           (h : x -->h y)
           (k : y -->h z)
  : square (identity _) (identity _) (#h F h ·h #h F k) (#h F (h ·h k))
  := pr12 (pr211 F) x y z h k.

Proposition lax_double_functor_comp_h_mor
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
            {x₁ x₂ y₁ y₂ z₁ z₂ : C₁}
            {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂}
            {vz : z₁ -->v z₂}
            {h₁ : x₁ -->h y₁} {h₂ : x₂ -->h y₂}
            {k₁ : y₁ -->h z₁} {k₂ : y₂ -->h z₂}
            (sh : square vx vy h₁ h₂)
            (sk : square vy vz k₁ k₂)
  : (#s F sh ⋆h #s F sk) ⋆v lax_double_functor_comp_h F h₂ k₂
    =
    transportb_square
      (id_v_right _ @ !(id_v_left _))
      (id_v_right _ @ !(id_v_left _))
      (lax_double_functor_comp_h F h₁ k₁ ⋆v #s F (sh ⋆h sk)).
Proof.
  exact (pr22 (pr211 F) x₁ x₂ y₁ y₂ z₁ z₂ vx vy vz h₁ h₂ k₁ k₂ sh sk).
Qed.

Proposition lax_double_functor_lunitor_h
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y : C₁}
            (f : x -->h y)
  : lunitor_h (#h F f)
    =
    transportf_square
      (assocr_v _ _ _ @ id_v_left _ @ id_v_left _ @ lax_double_functor_id_v _ _)
      (assocr_v _ _ _ @ id_v_left _ @ id_v_left _ @ lax_double_functor_id_v _ _)
      ((lax_double_functor_id_h F _ ⋆h id_v_square _)
       ⋆v lax_double_functor_comp_h F _ _
       ⋆v #s F (lunitor_h f)).
Proof.
  exact (pr121 F x y f).
Qed.

Proposition lax_double_functor_runitor_h
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
            {x y : C₁}
            (f : x -->h y)
  : runitor_h (#h F f)
    =
    transportf_square
      (assocr_v _ _ _ @ id_v_left _ @ id_v_left _ @ lax_double_functor_id_v _ _)
      (assocr_v _ _ _ @ id_v_left _ @ id_v_left _ @ lax_double_functor_id_v _ _)
      ((id_v_square _ ⋆h lax_double_functor_id_h F _)
       ⋆v lax_double_functor_comp_h F _ _
       ⋆v #s F (runitor_h f)).
Proof.
  exact (pr1 (pr221 F) x y f).
Qed.

Proposition lax_double_functor_lassociator_h
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
            {w x y z : C₁}
            (f : w -->h x)
            (g : x -->h y)
            (h : y -->h z)
  : lassociator_h (#h F f) (#h F g) (#h F h)
    ⋆v (lax_double_functor_comp_h F f g ⋆h id_v_square _)
    ⋆v lax_double_functor_comp_h F (f ·h g) h
    =
    transportf_square
      (maponpaths _ (lax_double_functor_id_v _ _))
      (maponpaths _ (lax_double_functor_id_v _ _))
      ((id_v_square _ ⋆h lax_double_functor_comp_h F g h)
       ⋆v lax_double_functor_comp_h F f (g ·h h)
       ⋆v #s F (lassociator_h f g h)).
Proof.
  exact (pr2 (pr221 F) w x y z f g h).
Qed.

(** * 6. Builder for lax functors *)
Definition make_lax_double_functor
           {C₁ C₂ : univalent_double_cat}
           (F : C₁ ⟶ C₂)
           (FF : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂))
           (FI : double_functor_hor_id
                   FF
                   (hor_id_double_cat C₁)
                   (hor_id_double_cat C₂))
           (FC : double_functor_hor_comp
                   FF
                   (hor_comp_double_cat C₁)
                   (hor_comp_double_cat C₂))
           (Fl : double_functor_lunitor
                   (double_cat_double_lunitor C₁)
                   (double_cat_double_lunitor C₂)
                   FI FC)
           (Fr : double_functor_runitor
                   (double_cat_double_runitor C₁)
                   (double_cat_double_runitor C₂)
                   FI FC)
           (Fa : double_functor_associator
                   (double_cat_double_associator C₁)
                   (double_cat_double_associator C₂)
                   FC)
  : lax_double_functor C₁ C₂.
Proof.
  simple refine ((((F ,, FF) ,, _) ,, _) ,, tt).
  - split ; cbn.
    + exact FI.
    + exact FC.
  - repeat split ; cbn.
    + exact Fl.
    + exact Fr.
    + exact Fa.
Defined.

(** The following builders incorporate the notation for double categories *)
Definition twosided_disp_functor_double_cat_data
           (C₁ C₂ : univalent_double_cat)
           (F : C₁ ⟶ C₂)
  : UU
  := ∑ (FF : ∏ (x y : C₁), x -->h y → F x -->h F y),
     ∏ (x₁ x₂ y₁ y₂ : C₁)
       (h : x₁ -->h y₁)
       (k : x₂ -->h y₂)
       (v : x₁ -->v x₂)
       (w : y₁ -->v y₂)
       (s : square v w h k),
     square (#F v) (#F w) (FF _ _ h) (FF _ _ k).

Definition twosided_disp_functor_double_cat_data_hor
           {C₁ C₂ : univalent_double_cat}
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor_double_cat_data C₁ C₂ F)
           {x y : C₁}
           (h : x -->h y)
  : F x -->h F y
  := pr1 FF x y h.

Coercion twosided_disp_functor_double_cat_data_hor
  : twosided_disp_functor_double_cat_data >-> Funclass.

Definition twosided_disp_functor_double_cat_data_square
           {C₁ C₂ : univalent_double_cat}
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor_double_cat_data C₁ C₂ F)
           {x₁ x₂ y₁ y₂ : C₁}
           {h : x₁ -->h y₁}
           {k : x₂ -->h y₂}
           {v : x₁ -->v x₂}
           {w : y₁ -->v y₂}
           (s : square v w h k)
  : square (#F v) (#F w) (FF _ _ h) (FF _ _ k)
  := pr2 FF _ _ _ _ _ _ _ _ s.

Definition twosided_disp_functor_double_cat_laws
           {C₁ C₂ : univalent_double_cat}
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor_double_cat_data C₁ C₂ F)
  : UU
  := (∏ (x y : C₁)
        (h : x -->h y),
      twosided_disp_functor_double_cat_data_square FF (id_v_square h)
      =
      transportb_square
        (functor_id _ _)
        (functor_id _ _)
        (id_v_square (FF _ _ h)))
     ×
     (∏ (x₁ x₂ x₃ y₁ y₂ y₃ : C₁)
        (h₁ : x₁ -->h y₁)
        (h₂ : x₂ -->h y₂)
        (h₃ : x₃ -->h y₃)
        (vx₁ : x₁ -->v x₂)
        (vy₁ : y₁ -->v y₂)
        (s₁ : square vx₁ vy₁ h₁ h₂)
        (vx₂ : x₂ -->v x₃)
        (vy₂ : y₂ -->v y₃)
        (s₂ : square vx₂ vy₂ h₂ h₃),
      twosided_disp_functor_double_cat_data_square FF (s₁ ⋆v s₂)
      =
      transportb_square
        (functor_comp _ _ _)
        (functor_comp _ _ _)
        (twosided_disp_functor_double_cat_data_square FF s₁
         ⋆v
         twosided_disp_functor_double_cat_data_square FF s₂)).

Definition make_twosided_disp_functor_double_cat
           (C₁ C₂ : univalent_double_cat)
           {F : C₁ ⟶ C₂}
           (FF : twosided_disp_functor_double_cat_data C₁ C₂ F)
           (HFF : twosided_disp_functor_double_cat_laws FF)
  : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂)
  := FF ,, HFF.

Definition make_double_functor_hor_id_double_cat
           {C₁ C₂ : univalent_double_cat}
           (F : C₁ ⟶ C₂)
           (FF : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂))
           (FFi : ∏ (x : C₁),
                  square
                    (identity_v (F x))
                    (identity_v (F x))
                    (identity_h (F x))
                    (FF x x (identity_h x)))
           (HFFi : ∏ (x y : C₁)
                     (v : x -->v y),
                   id_h_square (#F v) ⋆v FFi y
                   =
                   transportb_square
                     (id_v_right _ @ !(id_v_left _))
                     (id_v_right _ @ !(id_v_left _))
                     (FFi x ⋆v #2 FF (id_h_square v)))
  : double_functor_hor_id
      FF
      (hor_id_double_cat C₁)
      (hor_id_double_cat C₂)
  := FFi ,, HFFi.

Definition make_double_functor_hor_comp_double_cat
           {C₁ C₂ : univalent_double_cat}
           (F : C₁ ⟶ C₂)
           (FF : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂))
           (FFc : ∏ (x y z : C₁)
                    (h : x -->h y)
                    (k : y -->h z),
                  square
                    (identity_v _)
                    (identity_v _)
                    (FF _ _ h ·h FF _ _ k)
                    (FF _ _ (h ·h k)))
           (HFFc : ∏ (x₁ x₂ y₁ y₂ z₁ z₂ : C₁)
                     (v₁ : x₁ -->v x₂)
                     (v₂ : y₁ -->v y₂)
                     (v₃ : z₁ -->v z₂)
                     (h₁ : x₁ -->h y₁) (h₂ : x₂ -->h y₂)
                     (k₁ : y₁ -->h z₁) (k₂ : y₂ -->h z₂)
                     (s₁ : square v₁ v₂ h₁ h₂)
                     (s₂ : square v₂ v₃ k₁ k₂),
                   (#2 FF s₁ ⋆h #2 FF s₂) ⋆v FFc _ _ _ h₂ k₂
                   =
                   transportb_square
                     (id_v_right _ @ !(id_v_left _))
                     (id_v_right _ @ !(id_v_left _))
                     (FFc _ _ _ h₁ k₁ ⋆v #2 FF (s₁ ⋆h s₂)))
  : double_functor_hor_comp
      FF
      (hor_comp_double_cat C₁)
      (hor_comp_double_cat C₂)
  := FFc ,, HFFc.

Definition make_double_functor_lunitor_double_cat
           {C₁ C₂ : univalent_double_cat}
           (F : C₁ ⟶ C₂)
           (FF : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂))
           (FI : double_functor_hor_id
                   FF
                   (hor_id_double_cat C₁)
                   (hor_id_double_cat C₂))
           (FC : double_functor_hor_comp
                   FF
                   (hor_comp_double_cat C₁)
                   (hor_comp_double_cat C₂))
           (H : ∏ (x y : C₁)
                  (h : x -->h y),
                lunitor_h (FF x y h)
                =
                transportf_square
                  (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id _ _)
                  (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id _ _)
                  ((functor_double_id_cell FI x ⋆h id_v_square _)
                   ⋆v functor_double_comp_cell FC _ _
                   ⋆v #2 FF (lunitor_h h)))
  : double_functor_lunitor
      (double_cat_double_lunitor C₁)
      (double_cat_double_lunitor C₂)
      FI FC.
Proof.
  exact H.
Qed.

Definition make_double_functor_runitor_double_cat
           {C₁ C₂ : univalent_double_cat}
           (F : C₁ ⟶ C₂)
           (FF : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂))
           (FI : double_functor_hor_id
                   FF
                   (hor_id_double_cat C₁)
                   (hor_id_double_cat C₂))
           (FC : double_functor_hor_comp
                   FF
                   (hor_comp_double_cat C₁)
                   (hor_comp_double_cat C₂))
           (H : ∏ (x y : C₁)
                  (h : x -->h y),
                runitor_h (FF x y h)
                =
                transportf_square
                  (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id _ _)
                  (assoc' _ _ _ @ id_left _ @ id_left _ @ functor_id _ _)
                  ((id_v_square _ ⋆h functor_double_id_cell FI y)
                   ⋆v functor_double_comp_cell FC _ _
                   ⋆v #2 FF (runitor_h h)))
  : double_functor_runitor
      (double_cat_double_runitor C₁)
      (double_cat_double_runitor C₂)
      FI FC.
Proof.
  exact H.
Qed.

Definition make_double_functor_associator_double_cat
           {C₁ C₂ : univalent_double_cat}
           (F : C₁ ⟶ C₂)
           (FF : twosided_disp_functor F F (hor_mor C₁) (hor_mor C₂))
           (FC : double_functor_hor_comp
                   FF
                   (hor_comp_double_cat C₁)
                   (hor_comp_double_cat C₂))
           (H : ∏ (w x y z : C₁)
                  (h₁ : w -->h x)
                  (h₂ : x -->h y)
                  (h₃ : y -->h z),
                lassociator_h (FF _ _ h₁) (FF _ _ h₂) (FF _ _ h₃)
                ⋆v (functor_double_comp_cell FC h₁ h₂ ⋆h id_v_square _)
                ⋆v functor_double_comp_cell FC (h₁ ·h h₂) h₃
                =
                transportf_square
                  (maponpaths _ (functor_id _ _))
                  (maponpaths _ (functor_id _ _))
                  ((id_v_square _ ⋆h functor_double_comp_cell FC h₂ h₃)
                   ⋆v functor_double_comp_cell FC h₁ (h₂ ·h h₃)
                   ⋆v #2 FF (lassociator_h h₁ h₂ h₃)))
  : double_functor_associator
      (double_cat_double_associator C₁)
      (double_cat_double_associator C₂)
      FC.
Proof.
  exact H.
Qed.

(** * 7. Strong double functors *)
Definition is_strong_double_functor
           {C₁ C₂ : univalent_double_cat}
           (F : lax_double_functor C₁ C₂)
  : UU
  := (∏ (x : C₁),
      is_iso_twosided_disp
        (identity_is_z_iso _)
        (identity_is_z_iso _)
        (lax_double_functor_id_h F x))
     ×
     (∏ (x y z : C₁)
        (h : x -->h y)
        (k : y -->h z),
      is_iso_twosided_disp
        (identity_is_z_iso _)
        (identity_is_z_iso _)
        (lax_double_functor_comp_h F h k)).

Proposition isaprop_is_strong_double_functor
            {C₁ C₂ : univalent_double_cat}
            (F : lax_double_functor C₁ C₂)
  : isaprop (is_strong_double_functor F).
Proof.
  use isapropdirprod ; repeat (use impred ; intro) ; apply isaprop_is_iso_twosided_disp.
Qed.

Definition is_iso_strong_double_functor_id_h
           {C₁ C₂ : univalent_double_cat}
           {F : lax_double_functor C₁ C₂}
           (HF : is_strong_double_functor F)
           (x : C₁)
  : is_iso_twosided_disp
      (identity_is_z_iso _)
      (identity_is_z_iso _)
      (lax_double_functor_id_h F x)
  := pr1 HF x.

Definition is_iso_strong_double_functor_comp_h
           {C₁ C₂ : univalent_double_cat}
           {F : lax_double_functor C₁ C₂}
           (HF : is_strong_double_functor F)
           {x y z : C₁}
           (h : x -->h y)
           (k : y -->h z)
  : is_iso_twosided_disp
      (identity_is_z_iso _)
      (identity_is_z_iso _)
      (lax_double_functor_comp_h F h k)
  := pr2 HF x y z h k.

Proposition is_strong_double_functor_id
            (C : univalent_double_cat)
  : is_strong_double_functor (id₁ C).
Proof.
  split.
  - intro x.
    apply id_is_iso_twosided_disp.
  - intros.
    apply id_is_iso_twosided_disp.
Defined.

Definition strong_double_functor
           (C₁ C₂ : univalent_double_cat)
  : UU
  := ∑ (F : lax_double_functor C₁ C₂), is_strong_double_functor F.

Coercion strong_double_functor_to_lax
         {C₁ C₂ : univalent_double_cat}
         (F : strong_double_functor C₁ C₂)
  : lax_double_functor C₁ C₂
  := pr1 F.

Coercion strong_double_functor_to_strong
         {C₁ C₂ : univalent_double_cat}
         (F : strong_double_functor C₁ C₂)
  : is_strong_double_functor F
  := pr2 F.

(** * 8. Double transformations *)
Definition double_transformation
           {C₁ C₂ : univalent_double_cat}
           (F G : lax_double_functor C₁ C₂)
  : UU
  := F ==> G.

(** * 9. Accessors for double transformations *)
Definition double_transformation_to_nat_trans
           {C₁ C₂ : univalent_double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : double_transformation F G)
  : F ⟹ G
  := pr1 (pr111 τ).

Coercion double_transformation_to_nat_trans : double_transformation >-> nat_trans.

Proposition double_transformation_ver_mor
            {C₁ C₂ : univalent_double_cat}
            {F G : lax_double_functor C₁ C₂}
            (τ : double_transformation F G)
            {x y : C₁}
            (f : x -->v y)
  : #v F f ·v τ y = τ x ·v #v G f.
Proof.
  exact (nat_trans_ax τ x y f).
Defined.

Definition double_transformation_hor_mor
           {C₁ C₂ : univalent_double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : double_transformation F G)
           {x y : C₁}
           (f : x -->h y)
  : square (τ x) (τ y) (#h F f) (#h G f)
  := pr12 (pr111 τ) x y f.

Proposition double_transformation_square
            {C₁ C₂ : univalent_double_cat}
            {F G : lax_double_functor C₁ C₂}
            (τ : double_transformation F G)
            {x₁ x₂ y₁ y₂ : C₁}
            {vx : x₁ -->v x₂}
            {vy : y₁ -->v y₂}
            {h : x₁ -->h y₁}
            {k : x₂ -->h y₂}
            (s : square vx vy h k)
  : #s F s ⋆v double_transformation_hor_mor τ k
    =
    transportb_square
      (double_transformation_ver_mor _ _)
      (double_transformation_ver_mor _ _)
      (double_transformation_hor_mor τ h ⋆v #s G s).
Proof.
  exact (pr22 (pr111 τ) x₁ x₂ y₁ y₂ vx vy h k s).
Qed.

Proposition double_transformation_id_h
            {C₁ C₂ : univalent_double_cat}
            {F G : lax_double_functor C₁ C₂}
            (τ : double_transformation F G)
            (x : C₁)
  : lax_double_functor_id_h F x ⋆v double_transformation_hor_mor τ (identity_h x)
    =
    transportb_square
      (id_v_left _ @ !(id_v_right _))
      (id_v_left _ @ !(id_v_right _))
      (id_h_square (τ x) ⋆v lax_double_functor_id_h G x).
Proof.
  exact (pr1 (pr211 τ) x).
Qed.

Proposition double_transformation_comp_h
            {C₁ C₂ : univalent_double_cat}
            {F G : lax_double_functor C₁ C₂}
            (τ : double_transformation F G)
            {x y z : C₁}
            (h : x -->h y)
            (k : y -->h z)
  : lax_double_functor_comp_h F h k
    ⋆v double_transformation_hor_mor τ (h ·h k)
    =
    transportb_square
      (id_v_left _ @ !(id_v_right _))
      (id_v_left _ @ !(id_v_right _))
      ((double_transformation_hor_mor τ h ⋆h double_transformation_hor_mor τ k)
       ⋆v lax_double_functor_comp_h G h k).
Proof.
  exact (pr2 (pr211 τ) x y z h k).
Qed.

Proposition double_transformation_eq
            {C₁ C₂ : univalent_double_cat}
            {F G : lax_double_functor C₁ C₂}
            {τ θ : double_transformation F G}
            (p : ∏ (x : C₁), τ x = θ x)
            (pp : ∏ (x y : C₁)
                    (f : x -->h y),
                double_transformation_hor_mor τ f
                =
                transportb_square (p x) (p y) (double_transformation_hor_mor θ f))
  : τ = θ.
Proof.
  use subtypePath.
  {
    intro.
    apply isapropunit.
  }
  use subtypePath.
  {
    intro.
    repeat (use isapropdirprod) ; apply isapropunit.
  }
  use subtypePath.
  {
    intro.
    use isapropdirprod ; [ apply isaprop_double_nat_trans_hor_id | ].
    apply isaprop_double_nat_trans_hor_comp.
  }
  use total2_paths_b.
  - use nat_trans_eq.
    {
      apply homset_property.
    }
    exact p.
  - use eq_twosided_disp_nat_trans.
    intros x y f.
    refine (!_).
    etrans.
    {
      apply transportb_prebicat_twosided_disp_cat.
    }
    refine (_ @ !(pp x y f)).
    use transportb_disp_mor2_eq.
    apply idpath.
Qed.

Proposition double_transformation_eq_ob
            {C₁ C₂ : univalent_double_cat}
            {F G : lax_double_functor C₁ C₂}
            {τ θ : double_transformation F G}
            (p : τ = θ)
            (x : C₁)
  : τ x = θ x.
Proof.
  induction p.
  apply idpath.
Defined.

Proposition double_transformation_eq_hor_mor
            {C₁ C₂ : univalent_double_cat}
            {F G : lax_double_functor C₁ C₂}
            {τ θ : double_transformation F G}
            (p : τ = θ)
            {x y : C₁}
            (f : x -->h y)
  : double_transformation_hor_mor τ f
    =
    transportb_square
      (double_transformation_eq_ob p x)
      (double_transformation_eq_ob p y)
      (double_transformation_hor_mor θ f).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

#[global] Opaque double_transformation_eq_ob.

(** * 10. Builder for double transformations *)
Definition make_double_transformation
           {C₁ C₂ : univalent_double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : F ⟹ G)
           (ττ : twosided_disp_nat_trans
                   τ τ
                   (lax_double_functor_hor_mor F)
                   (lax_double_functor_hor_mor G))
           (τI : double_nat_trans_hor_id
                   ττ
                   (lax_double_functor_hor_id F)
                   (lax_double_functor_hor_id G))
           (τC : double_nat_trans_hor_comp
                   ττ
                   (lax_double_functor_hor_comp F)
                   (lax_double_functor_hor_comp G))
  : double_transformation F G.
Proof.
  simple refine ((((_ ,, _) ,, _) ,, (tt ,, tt ,, tt)) ,, tt).
  - exact τ.
  - exact ττ.
  - split ; cbn.
    + exact τI.
    + exact τC.
Defined.

(** The following builders incorporate the notation for double categories *)
Definition twosided_disp_nat_trans_double_cat_data
           {C₁ C₂ : univalent_double_cat}
           (F G : lax_double_functor C₁ C₂)
           (τ : F ⟹ G)
  : UU
  := ∏ (x y : C₁)
       (h : x -->h y),
     square (τ x) (τ y) (#h F h) (#h G h).

Definition twosided_disp_nat_trans_double_cat_laws
           {C₁ C₂ : univalent_double_cat}
           {F G : lax_double_functor C₁ C₂}
           {τ : F ⟹ G}
           (ττ : twosided_disp_nat_trans_double_cat_data F G τ)
  : UU
  := ∏ (x₁ x₂ y₁ y₂ : C₁)
       (v : x₁ -->v x₂)
       (w : y₁ -->v y₂)
       (h : x₁ -->h y₁)
       (k : x₂ -->h y₂)
       (s : square v w h k),
     #s F s ⋆v ττ _ _ k
     =
     transportb_square
       (nat_trans_ax _ _ _ _)
       (nat_trans_ax _ _ _ _)
       (ττ _ _ h ⋆v #s G s).

Definition make_twosided_disp_nat_trans_double_cat
           {C₁ C₂ : univalent_double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : F ⟹ G)
           (ττ : twosided_disp_nat_trans_double_cat_data F G τ)
           (Hττ : twosided_disp_nat_trans_double_cat_laws ττ)
  : twosided_disp_nat_trans
      τ τ
      (lax_double_functor_hor_mor F)
      (lax_double_functor_hor_mor G)
  := ττ ,, Hττ.

Definition make_double_nat_trans_hor_id
           {C₁ C₂ : univalent_double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : F ⟹ G)
           (ττ : twosided_disp_nat_trans
                   τ τ
                   (lax_double_functor_hor_mor F)
                   (lax_double_functor_hor_mor G))
           (H : ∏ (x : C₁),
                lax_double_functor_id_h F x ⋆v ττ x x (identity_h x)
                =
                transportb_square
                  (id_left _ @ !(id_right _))
                  (id_left _ @ !(id_right _))
                  (id_h_square (τ x) ⋆v lax_double_functor_id_h G x))
  : double_nat_trans_hor_id
      ττ
      (lax_double_functor_hor_id F)
      (lax_double_functor_hor_id G).
Proof.
  exact H.
Qed.

Definition make_double_nat_trans_hor_comp
           {C₁ C₂ : univalent_double_cat}
           {F G : lax_double_functor C₁ C₂}
           (τ : F ⟹ G)
           (ττ : twosided_disp_nat_trans
                   τ τ
                   (lax_double_functor_hor_mor F)
                   (lax_double_functor_hor_mor G))
           (H : ∏ (x y z : C₁)
                  (h : x -->h y)
                  (k : y -->h z),
                lax_double_functor_comp_h F h k ⋆v ττ _ _ (h ·h k)
                =
                transportb_disp_mor2
                  (id_left _ @ !(id_right _))
                  (id_left _ @ !(id_right _))
                  ((ττ _ _ h ⋆h ττ _ _ k) ⋆v lax_double_functor_comp_h G h k))
  : double_nat_trans_hor_comp
      ττ
      (lax_double_functor_hor_comp F)
      (lax_double_functor_hor_comp G).
Proof.
  exact H.
Qed.
