(**
Some laws on transporting along families of 2-cells.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Local Open Scope cat.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.

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
      (idtoiso_2_0 _ _ (maponpaths g p))
      ∘ h
      ∘ (idtoiso_2_0 _ _ (maponpaths f (!p))).
Proof.
  induction p ; cbn.
  exact (linvunitor _ o rinvunitor _).
Defined.

Definition transport_one_cell_FlFr_inv
           {C : bicat}
           {A : Type}
           (f g : A -> C)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (h : C⟦f a₁,g a₁⟧)
  : ((idtoiso_2_0 _ _ (maponpaths g p)))
      ∘ h
      ∘ (idtoiso_2_0 _ _ (maponpaths f (!p)))
      ==>
      (transportf (λ (z : A), C⟦f z,g z⟧) p h).
Proof.
  induction p ; cbn.
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
    rewrite <- !vassocr.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite linvunitor_lunitor, id2_left.
    apply rinvunitor_runitor.
  - induction p ; cbn.
    rewrite <- !vassocr.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite runitor_rinvunitor, id2_left.
    apply lunitor_linvunitor.
Defined.

Definition idtoiso_2_0_inv
           {B : bicat}
           {b₁ b₂ : B}
           (p : b₁ = b₂)
  : pr1 (idtoiso_2_0 _ _ (!p))
    =
    left_adjoint_right_adjoint (idtoiso_2_0 _ _ p).
Proof.
  induction p.
  apply idpath.
Qed.

Lemma idtoiso_2_1_inv
           {C : bicat}
           {a b : C}
           {f g : a --> b}
           (p : f = g)
  : idtoiso_2_1 _ _ (!p)
    =
    inv_of_invertible_2cell (idtoiso_2_1 _ _ p).
Proof.
  induction p.
  apply idpath.
Qed.

Lemma idtoiso_2_1_concat
           {C : bicat}
           {a b : C}
           {f₁ f₂ f₃ : a --> b}
           (p : f₁ = f₂) (q : f₂ = f₃)
  : idtoiso_2_1 _ _ (p @ q)
    =
    comp_of_invertible_2cell
      (idtoiso_2_1 _ _ p)
      (idtoiso_2_1 _ _ q).
Proof.
  induction p ; induction q ; cbn.
  use subtypePath.
  { intro ; apply isaprop_is_invertible_2cell. }
  exact (!(id2_left _)).
Qed.

Lemma idtoiso_2_1_rwhisker
           {C : bicat}
           {X Y Z : C}
           (g : C⟦Y,Z⟧)
           {f₁ f₂ : C⟦X,Y⟧}
           (q : f₁ = f₂)
  : g ◅ (idtoiso_2_1 _ _ q) = idtoiso_2_1 _ _ (maponpaths (λ z, z · g) q).
Proof.
  induction q ; cbn.
  apply id2_rwhisker.
Qed.

Lemma idtoiso_2_1_lwhisker
           {C : bicat}
           {X Y Z : C}
           (g : C⟦X,Y⟧)
           {f₁ f₂ : C⟦Y,Z⟧}
           (q : f₁ = f₂)
  : (idtoiso_2_1 _ _ q) ▻ g = idtoiso_2_1 _ _ (maponpaths (λ z, g · z) q).
Proof.
  induction q ; cbn.
  apply lwhisker_id2.
Qed.

Lemma transport_two_cell_FlFr
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
  apply idpath.
Qed.

Lemma isotoid_2_1_id
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {a b : B}
           (f : a --> b)
  : idpath f = isotoid_2_1 HB (id2_invertible_2cell f).
Proof.
  use (invmaponpathsincl (idtoiso_2_1 _ _)).
  - apply isinclweq.
    exact (HB _ _ _ _).
  - rewrite idtoiso_2_1_isotoid_2_1.
    apply idpath.
Qed.

Lemma isotoid_2_1_lwhisker
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {a b c : B}
           (f : a --> b)
           {g₁ g₂ : b --> c}
           (α : invertible_2cell g₁ g₂)
  : maponpaths
      (λ z : b --> c, f · z)
      (isotoid_2_1 HB α)
    =
    isotoid_2_1 HB (f ◃ α ,, is_invertible_2cell_lwhisker _ (pr2 α)).
Proof.
  use (invmaponpathsincl (idtoiso_2_1 _ _)).
  - apply isinclweq.
    exact (HB _ _ _ _).
  - use subtypePath.
    { intro ; apply isaprop_is_invertible_2cell. }
    etrans.
    {
      refine (!_).
      apply idtoiso_2_1_lwhisker.
    }
    rewrite !idtoiso_2_1_isotoid_2_1.
    apply idpath.
Qed.

Lemma isotoid_2_1_rwhisker
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {a b c : B}
           {f₁ f₂ : a --> b}
           (α : invertible_2cell f₁ f₂)
           (g : b --> c)
  : maponpaths
      (λ z : a --> b, z · g)
      (isotoid_2_1 HB α)
    =
    isotoid_2_1 HB (α ▹ g ,, is_invertible_2cell_rwhisker _ (pr2 α)).
Proof.
  use (invmaponpathsincl (idtoiso_2_1 _ _)).
  - apply isinclweq.
    exact (HB _ _ _ _).
  - use subtypePath.
    { intro ; apply isaprop_is_invertible_2cell. }
    etrans.
    {
      refine (!_).
      apply idtoiso_2_1_rwhisker.
    }
    rewrite !idtoiso_2_1_isotoid_2_1.
    apply idpath.
Qed.

Lemma isotoid_2_1_vcomp
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {a b : B}
           {f₁ f₂ f₃ : a --> b}
           (α : invertible_2cell f₁ f₂)
           (β : invertible_2cell f₂ f₃)
  : isotoid_2_1 HB α @ isotoid_2_1 HB β
    =
    isotoid_2_1 HB (α • β ,, is_invertible_2cell_vcomp (pr2 α) (pr2 β)).
Proof.
  use (invmaponpathsincl (idtoiso_2_1 _ _)).
  - apply isinclweq.
    exact (HB _ _ _ _).
  - etrans.
    {
      apply idtoiso_2_1_concat.
    }
    use subtypePath.
    { intro ; apply isaprop_is_invertible_2cell. }
    rewrite !idtoiso_2_1_isotoid_2_1.
    apply idpath.
Qed.
