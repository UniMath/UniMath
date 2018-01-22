
(** * The Structure Identity Principle

A short proof of the SIP (HoTT book, chapter 9.8)

*)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope mor_disp_scope.

(** * The Structure Identity Principle *)

Section SIP.

(** ** The data and properties according to HoTT book, chapter 9.8 *)

Variable C : category.
Variable univC : is_univalent C.
Variable P : ob C -> UU.
Variable Pisset : ∏ x, isaset (P x).
Variable H : ∏ (x y : C), P x → P y → C⟦x,y⟧ → UU.
Arguments H {_ _} _ _ _ .
Variable Hisprop : ∏ x y a b (f : C⟦x,y⟧), isaprop (H a b f).
Variable Hid : ∏ (x : C) (a : P x), H a a (identity _ ).
Variable Hcomp : ∏ (x y z : C) a b c (f : C⟦x,y⟧) (g : C⟦y,z⟧),
                 H a b f → H b c g → H a c (f · g).
Variable Hstandard : ∏ (x : C) (a a' : P x),
                     H a a' (identity _ ) → H a' a (identity _ ) → a = a'.

(** ** A displayed precategory from the data *)

Definition disp_cat_from_SIP_data : disp_cat C
  := disp_struct C P (@H) Hisprop Hid Hcomp.

(** ** Displayed category from SIP data is univalent *)

Lemma is_univalent_disp_from_SIP_data : is_univalent_disp disp_cat_from_SIP_data.
Proof.
  apply is_univalent_disp_from_fibers.
  intros x a b.
  apply isweqimplimpl.
  - intro i. apply Hstandard.
    * apply i.
    * apply (inv_mor_disp_from_iso i).
  - apply Pisset.
  - apply isofhleveltotal2.
    + apply Hisprop.
    + intro. apply (@isaprop_is_iso_disp _ disp_cat_from_SIP_data).
Defined.

(** ** The conclusion of SIP: total category is univalent *)

Definition SIP : is_univalent (total_category disp_cat_from_SIP_data).
Proof.
  apply is_univalent_total_category.
  - apply univC.
  - apply is_univalent_disp_from_SIP_data.
Defined.

End SIP.

(** TODO: add some examples *)