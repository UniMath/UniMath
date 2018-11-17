(* ******************************************************************************* *)
(** * Bicategories

Definition of aliases for the names defined in Bicategories/Bicat

 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.

Open Scope cat.

(* -----------------------------------------------------------------------------------*)
(** ** Notations.                                                                     *)
(* -----------------------------------------------------------------------------------*)


Definition assoc_inv
           {C : bicat}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : h ∘ (g ∘ f) ==> (h ∘ g) ∘ f
  := rassociator f g h .

Definition assoc
           {C : bicat}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : (h ∘ g) ∘ f ==> h ∘ (g ∘ f)
  := lassociator f g h .

Notation "'right_unit'" := lunitor.
Notation "'left_unit'" := runitor.
Notation "'right_unit_inv'" := linvunitor.
Notation "'left_unit_inv'" := rinvunitor.
Notation "'id₁'" := identity.
Notation "'id₂'" := id2.
Notation " b ⋆⋆ a" := (a ⋆ b) (at level 30).