(**********************************************************

 Extensive bicategories

 Contents:
 1. Disjoint coproducts
 2. Universal coproducts

 **********************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.
Require Import UniMath.Bicategories.Limits.CommaObjects.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Import PullbackFunctions.Notations.

Local Open Scope cat.

(**
 1. Disjoint coproducts
 *)

(*******************************************

 the initial object gives a comma cone on

 x --> z <-- y

 *******************************************)
Definition biinitial_comma_cone
           {B : bicat_with_biinitial}
           {x y z : B}
           (f : x --> z)
           (g : y --> z)
  : comma_cone f g.
Proof.
  use make_comma_cone.
  - exact (pr1 (biinitial_of B)).
  - exact (is_biinitial_1cell_property (pr2 (biinitial_of B)) _).
  - exact (is_biinitial_1cell_property (pr2 (biinitial_of B)) _).
  - exact (is_biinitial_2cell_property (pr2 (biinitial_of B)) _ _ _).
Defined.

Definition is_disjoint_coproduct
           {B : bicat_with_biinitial}
           {x p y : B}
           (ι₁ : x --> p)
           (ι₂ : y --> p)
  : UU
  := fully_faithful_1cell ι₁
     ×
     fully_faithful_1cell ι₂
     ×
     has_comma_ump (biinitial_comma_cone ι₁ ι₂)
     ×
     has_comma_ump (biinitial_comma_cone ι₂ ι₁).

Definition is_disjoint_coproduct_cone
           {B : bicat_with_biinitial}
           {x y : B}
           (p : bincoprod_cocone x y)
  : UU
  := is_disjoint_coproduct
       (bincoprod_cocone_inl p)
       (bincoprod_cocone_inr p).

(**
 2. Universal coproducts
 *)

(*******************************************

 Given

       z

       |
       V

 x --> p <-- y

 we have pullbacks


 v --> z <-- w

 |     |     |
 V     V     V

 x --> p <-- y

 such that z is the coproduct of v and w

 *******************************************)
Definition is_universal_coproduct
           {B : bicat}
           {x p y : B}
           (ι₁ : x --> p)
           (ι₂ : y --> p)
  : UU
  := ∏ (z : B)
       (h : z --> p),
     ∑ (v w : B)
       (f₁ : v --> x)
       (f₂ : w --> y)
       (g₁ : v --> z)
       (g₂ : w --> z)
       (γ₁ : invertible_2cell (f₁ · ι₁) (g₁ · h))
       (γ₂ : invertible_2cell (f₂ · ι₂) (g₂ · h))
       (H₁ : has_pb_ump (make_pb_cone _ f₁ g₁ γ₁))
       (H₂ : has_pb_ump (make_pb_cone w f₂ g₂ γ₂)),
     has_bincoprod_ump (make_bincoprod_cocone _ g₁ g₂).

Definition is_universal_coproduct_cone
           {B : bicat}
           {x y : B}
           (p : bincoprod_cocone x y)
  : UU
  := is_universal_coproduct
       (bincoprod_cocone_inl p)
       (bincoprod_cocone_inr p).

Definition bicat_with_pb_is_universal_coproduct
           {B : bicat_with_pb}
           {x p y : B}
           (ι₁ : x --> p)
           (ι₂ : y --> p)
  : UU
  := ∏ (z : B)
       (h : z --> p),
     has_bincoprod_ump
       (make_bincoprod_cocone
          z
          (pb_pr2 ι₁ h)
          (pb_pr2 ι₂ h)).

Definition is_universal_from_pb
           {B : bicat_with_pb}
           {x p y : B}
           (ι₁ : x --> p)
           (ι₂ : y --> p)
           (H : bicat_with_pb_is_universal_coproduct ι₁ ι₂)
  : is_universal_coproduct ι₁ ι₂
  := λ z h,
     ι₁ /≃ h
     ,,
     ι₂ /≃ h
     ,,
     π₁
     ,,
     π₁
     ,,
     π₂
     ,,
     π₂
     ,,
     pb_cell ι₁ h
     ,,
     pb_cell ι₂ h
     ,,
     pb_obj_has_pb_ump ι₁ h
     ,,
     pb_obj_has_pb_ump ι₂ h
     ,,
     H z h.

Definition is_universal_from_pb_alt
           {B : bicat}
           (HB : has_pb B)
           {x p y : B}
           (ι₁ : x --> p)
           (ι₂ : y --> p)
           (H : @bicat_with_pb_is_universal_coproduct (B ,, HB) _ _ _ ι₁ ι₂)
  : is_universal_coproduct ι₁ ι₂
  := is_universal_from_pb _ _ H.

(**
 3. Extensive bicategory
 *)
Definition bicat_with_biinitial_bincoprod
  : UU
  := ∑ (B : bicat),
     biinitial_obj B
     ×
     has_bincoprod B.

Coercion bicat_with_biinitial_bincoprod_to_bicat_with_biinitial
         (B : bicat_with_biinitial_bincoprod)
  : bicat_with_biinitial
  := pr1 B ,, pr12 B.

Coercion bicat_with_biinitial_bincoprod_to_bicat_with_bincoprod
         (B : bicat_with_biinitial_bincoprod)
  : bicat_with_bincoprod
  := pr1 B ,, pr22 B.

Definition is_extensive
           (B : bicat_with_biinitial_bincoprod)
  : UU
  := ∏ (x y : B),
     @is_disjoint_coproduct_cone B x y (pr1 (bincoprod_of B x y))
     ×
     @is_universal_coproduct_cone B x y (pr1 (bincoprod_of B x y)).
