(**************************************************************************************************

  The construction of a  displayed category with structure on objects and a proposition on morphisms

  The full machinery of displayed categories allows for arbitrary complexity on both objects and
  morphisms (any category can be considered a displayed category over the unit category). However,
  in most practical cases, a displayed category is given by some additional structure on the
  objects, and for the morphisms a proposition, stating that they preserve the structure. This class
  of displayed categories is slightly easier to construct, because there are less axioms to verify.
  Note that often, one can prove univalence for such a category using `SIP.v`.
  This construction is inspired by the Structure Identity Principle of the HoTT book (Section 9.8).

  Contents
  1. A displayed category from structure on objects and compatibility on morphisms [disp_struct]

 **************************************************************************************************)
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Local Open Scope cat.

(** * 1. Displayed category from structure on objects and compatibility on morphisms *)

Section struct_hom.

Variable C : category.
Variable P : ob C -> UU.
Variable H : ∏ (x y : C), P x → P y → C⟦x,y⟧ → UU.
Arguments H {_ _} _ _ _ .
Variable Hisprop : ∏ x y a b (f : C⟦x,y⟧), isaprop (H a b f).
Variable Hid : ∏ (x : C) (a : P x), H a a (identity _ ).
Variable Hcomp : ∏ (x y z : C) a b c (f : C⟦x,y⟧) (g : C⟦y,z⟧),
                 H a b f → H b c g → H a c (f · g).

Definition disp_struct_ob_mor : disp_cat_ob_mor C.
Proof.
  exists P.
  intros ? ? f a b; exact (H f a b ).
Defined.

Definition disp_struct_id_comp : disp_cat_id_comp _ disp_struct_ob_mor.
Proof.
  split; cbn; intros.
  - apply Hid.
  - eapply Hcomp. apply X. apply X0.
Qed.

Definition disp_struct_data : disp_cat_data C := _ ,, disp_struct_id_comp.

Definition disp_struct : disp_cat C.
Proof.
  use make_disp_cat_locally_prop.
  - exact disp_struct_data.
  - intro; intros; apply Hisprop.
Defined.

End struct_hom.
