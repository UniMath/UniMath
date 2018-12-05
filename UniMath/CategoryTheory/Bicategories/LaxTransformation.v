Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor. Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.TwoType.

Local Open Scope cat.

Definition laxtrans_data
           {C D : bicat}
           (F G : laxfunctor C D)
  : UU
  := ∑ (η : ∏ (X : C), F X --> G X),
     ∏ (X Y : C) (f : X --> Y), η X · #G f ==> #F f · η Y.

Definition laxcomponent_of
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : laxtrans_data F G)
  : ∏ (X : C), F X --> G X
  := pr1 η.

Coercion laxcomponent_of : laxtrans_data >-> Funclass.

Definition laxnaturality_of
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : laxtrans_data F G)
  : ∏ {X Y : C} (f : X --> Y), η X · #G f ==> #F f · η Y
  := pr2 η.

Definition mk_laxtrans_data
           {C D : bicat}
           {F G : laxfunctor C D}
           (η₁ : ∏ (X : C), F X --> G X)
           (η₂ : ∏ (X Y : C) (f : X --> Y), η₁ X · #G f ==> #F f · η₁ Y)
  : laxtrans_data F G
  := (η₁ ,, η₂).

Definition is_laxtrans
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : laxtrans_data F G)
  : UU
  := (∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
      (laxnaturality_of η f)
        • (##F α ▹ η Y)
      =
      (η X ◃ ##G α)
        • laxnaturality_of η g)
     ×
     (∏ (X : C),
      (η X ◃ laxfunctor_id G X)
        • laxnaturality_of η (id₁ X)
      =
      (runitor (η X))
        • linvunitor (η X)
        • (laxfunctor_id F X ▹ η X))
     ×
     (∏ (X Y Z : C) (f : X --> Y) (g : Y --> Z),
      (η X ◃ laxfunctor_comp G f g)
        • laxnaturality_of η (f · g)
      =
      (lassociator (η X) (#G f) (#G g))
        • (laxnaturality_of η f ▹ (#G g))
        • rassociator (#F f) (η Y) (#G g)
        • (#F f ◃ laxnaturality_of η g)
        • lassociator (#F f) (#F g) (η Z)
        • (laxfunctor_comp F f g ▹ η Z)).

Definition laxtrans
           {C D : bicat}
           (F G : laxfunctor C D)
  : UU
  := ∑ (η : laxtrans_data F G), is_laxtrans η.

Definition mk_laxtrans
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : laxtrans_data F G)
           (Hη : is_laxtrans η)
  : laxtrans F G
  := (η ,, Hη).

Coercion laxtrans_to_data
         {C D : bicat}
         {F G : laxfunctor C D}
         (η : laxtrans F G)
  : laxtrans_data F G
  := pr1 η.

Definition laxnaturality_natural
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : laxtrans F G)
  : ∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
      (laxnaturality_of η f)
        • (##F α ▹ η Y)
      =
      (η X ◃ ##G α)
        • laxnaturality_of η g
  := pr1(pr2 η).

Definition laxtrans_id
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : laxtrans F G)
  : ∏ (X : C),
    (η X ◃ laxfunctor_id G X)
      • laxnaturality_of η (id₁ X)
    =
    (runitor (η X))
      • linvunitor (η X)
      • (laxfunctor_id F X ▹ η X)
  := pr1(pr2(pr2 η)).

Definition laxtrans_comp
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : laxtrans F G)
  : ∏ {X Y Z : C} (f : X --> Y) (g : Y --> Z),
    (η X ◃ laxfunctor_comp G f g)
      • laxnaturality_of η (f · g)
    =
    (lassociator (η X) (#G f) (#G g))
      • (laxnaturality_of η f ▹ (#G g))
      • rassociator (#F f) (η Y) (#G g)
      • (#F f ◃ laxnaturality_of η g)
      • lassociator (#F f) (#F g) (η Z)
      • (laxfunctor_comp F f g ▹ η Z)
  := pr2(pr2(pr2 η)).

Definition laxtrans_id_alt
           {C D : bicat}
           {F G : psfunctor C D}
           (η : laxtrans F G)
  : ∏ (X : C),
    laxnaturality_of η (id₁ X)
    =
    (η X ◃ (psfunctor_id G X)^-1)
      • runitor (η X)
      • linvunitor (η X)
      • (laxfunctor_id F X ▹ η X).
Proof.
  intros X.
  rewrite !vassocl.
  use vcomp_move_L_pM.
  { is_iso. }
  cbn.
  rewrite !vassocr.
  exact (laxtrans_id η X).
Qed.

Definition laxtrans_comp_alt
           {C D : bicat}
           {F G : psfunctor C D}
           (η : laxtrans F G)
  : ∏ {X Y Z : C} (f : X --> Y) (g : Y --> Z),
    laxnaturality_of η (f · g)
    =
    (η X ◃ (psfunctor_comp G f g)^-1)
      • lassociator (η X) (#G f) (#G g)
      • (laxnaturality_of η f ▹ (#G g))
      • rassociator (#F f) (η Y) (#G g)
      • (#F f ◃ laxnaturality_of η g)
      • lassociator (#F f) (#F g) (η Z)
      • (laxfunctor_comp F f g ▹ η Z).
Proof.
  intros X Y Z f g.
  rewrite !vassocl.
  use vcomp_move_L_pM.
  { is_iso. }
  cbn.
  rewrite !vassocr.
  exact (laxtrans_comp η f g).
Qed.

Definition is_pseudo_trans
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : laxtrans F G)
  : UU
  := ∏ (X Y : C) (f : X --> Y), is_invertible_2cell (laxnaturality_of η f).

Definition pstrans
           {C D : bicat}
           (F G : laxfunctor C D)
  : UU
  := ∑ (η : laxtrans F G), is_pseudo_trans η.

Coercion pstrans_to_laxtrans
         {C D : bicat}
         {F G : laxfunctor C D}
         (η : pstrans F G)
  := pr1 η.

Definition mk_pstrans
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : laxtrans F G)
           (Hη : is_pseudo_trans η)
  : pstrans F G
  := (η ,, Hη).

Definition laxnaturality_of_iso
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : pstrans F G)
  : ∏ {X Y : C} (f : X --> Y), invertible_2cell (η X · #G f) (#F f · η Y)
  := λ X Y f, (laxnaturality_of η f ,, pr2 η X Y f).

Definition laxnaturality_of_inv
           {C D : bicat}
           {F G : laxfunctor C D}
           (η : pstrans F G)
  : ∏ {X Y : C} (f : X --> Y), #F f · η Y ==> η X · #G f
  := λ X Y f, (laxnaturality_of_iso η f)^-1.