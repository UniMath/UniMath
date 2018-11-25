(**
Some laws on transporting along families of 2-cells.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Local Open Scope bicategory_scope.

Definition transport_one_cell_FlFr
           {C : bicat}
           {A : Type}
           (f g : A -> C)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (h : C⟦f a₁,g a₁⟧)
  : (transportf (λ (z : A), C⟦f z,g z⟧) p h)
      ==>
      internal_left_adjoint (idtoiso_2_0 _ _ (maponpaths g p))
      ∘ h
      ∘ internal_left_adjoint (idtoiso_2_0 _ _ (maponpaths f (!p))).
Proof.
  induction p ; cbn.
  unfold idfun.
  exact (linvunitor _ o rinvunitor _).
Defined.

Definition transport_one_cell_FlFr_inv
           {C : bicat}
           {A : Type}
           (f g : A -> C)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (h : C⟦f a₁,g a₁⟧)
  : (internal_left_adjoint (idtoiso_2_0 _ _ (maponpaths g p)))
      ∘ h
      ∘ internal_left_adjoint (idtoiso_2_0 _ _ (maponpaths f (!p)))
      ==>
      (transportf (λ (z : A), C⟦f z,g z⟧) p h).
Proof.
  induction p ; cbn.
  unfold idfun.
  exact (runitor _ o lunitor _).
Defined.

Definition transport_one_cell_FlFr_iso
           {C : bicat}
           {A : Type}
           (f g : A -> C)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (h : C⟦f a₁,g a₁⟧)
  : is_invertible_2cell (transport_one_cell_FlFr f g p h).
Proof.
  refine (transport_one_cell_FlFr_inv f g p h ,, _).
  split ; cbn.
  - induction p ; cbn.
    unfold idfun.
    rewrite <- !vassocr.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite linvunitor_lunitor, id2_left.
    apply rinvunitor_runitor.
  - induction p ; cbn.
    unfold idfun.
    rewrite <- !vassocr.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite runitor_rinvunitor, id2_left.
    apply lunitor_linvunitor.
Defined.

Definition idtoiso_2_1_rwhisker
           {C : bicat}
           {X Y Z : C}
           (g : C⟦Y,Z⟧)
           {f₁ f₂ : C⟦X,Y⟧}
           (q : f₁ = f₂)
  : g ◅ (idtoiso_2_1 _ _ q) = idtoiso_2_1 _ _ (maponpaths (λ z, z · g) q).
Proof.
  induction q ; cbn.
  apply id2_rwhisker.
Defined.

Definition idtoiso_2_1_lwhisker
           {C : bicat}
           {X Y Z : C}
           (g : C⟦X,Y⟧)
           {f₁ f₂ : C⟦Y,Z⟧}
           (q : f₁ = f₂)
  : (idtoiso_2_1 _ _ q) ▻ g = idtoiso_2_1 _ _ (maponpaths (λ z, g · z) q).
Proof.
  induction q ; cbn.
  apply lwhisker_id2.
Defined.

Definition transport_two_cell_FlFr
           {C : bicat}
           {A : Type}
           {X Y : C}
           (F G : A -> C⟦X,Y⟧)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (α : F a₁ ==> G a₁)
  : transportf (λ z, F z ==> G z) p α
    =
    idtoiso_2_1 _ _ (maponpaths G p) o α o (idtoiso_2_1 _ _ (maponpaths F p))^-1.
Proof.
  induction p ; cbn.
  rewrite id2_right, id2_left.
  reflexivity.
Qed.