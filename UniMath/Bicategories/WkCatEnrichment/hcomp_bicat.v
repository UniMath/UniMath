Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Bicategories.WkCatEnrichment.prebicategory.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.BicategoryLaws.

Local Open Scope cat.

Definition hcomp_bicat_data
  : UU
  := ∑ (ob : UU)
       (mor : ob → ob → UU)
       (cell : ∏ (x y : ob), mor x y → mor x y → UU)
       (id1 : ∏ (x : ob), mor x x)
       (comp1 : ∏ (x y z : ob), mor x y → mor y z → mor x z),
     (∏ (x y : ob) (f : mor x y), cell _ _ f f)
     × (∏ (x y : ob) (f g h : mor x y),
        cell _ _ f g → cell _ _ g h → cell _ _ f h)
     × (∏ (x y : ob) (f : mor x y),
        cell _ _ (comp1 _ _ _ f (id1 y)) f)
     × (∏ (x y : ob) (f : mor x y),
        cell _ _ f (comp1 _ _ _ f (id1 y)))
     × (∏ (x y : ob) (f : mor x y),
        cell _ _ (comp1 _ _ _ (id1 x) f) f)
     × (∏ (x y : ob) (f : mor x y),
        cell _ _ f (comp1 _ _ _ (id1 x) f))
     × (∏ (w x y z : ob) (f : mor w x) (g : mor x y) (h : mor y z),
        cell _ _
             (comp1 _ _ _ (comp1 _ _ _ f g) h)
             (comp1 _ _ _ f (comp1 _ _ _ g h)))
     × (∏ (w x y z : ob) (f : mor w x) (g : mor x y) (h : mor y z),
        cell _ _
             (comp1 _ _ _ f (comp1 _ _ _ g h))
             (comp1 _ _ _ (comp1 _ _ _ f g) h))
     × (∏ (x y z : ob) (f₁ f₂ : mor x y) (g₁ g₂ : mor y z),
        cell _ _ f₁ f₂
        → cell _ _ g₁ g₂
        → cell _ _ (comp1 _ _ _ f₁ g₁) (comp1 _ _ _ f₂ g₂)).

Coercion hcomp_bicat_ob
         (B : hcomp_bicat_data)
  : UU
  := pr1 B.

Definition hb_mor
           {B : hcomp_bicat_data}
           (b₁ b₂ : B)
  : UU
  := pr12 B b₁ b₂.

Definition hb_cell
           {B : hcomp_bicat_data}
           {b₁ b₂ : B}
           (f g : hb_mor b₁ b₂)
  : UU
  := pr122 B _ _ f g.

Definition hb_id1
           {B : hcomp_bicat_data}
           (b : B)
  : hb_mor b b
  := pr1 (pr222 B) b .

Definition hb_comp1
           {B : hcomp_bicat_data}
           {b₁ b₂ b₃ : B}
           (f : hb_mor b₁ b₂)
           (g : hb_mor b₂ b₃)
  : hb_mor b₁ b₃
  := pr12 (pr222 B) _ _ _ f g.

Definition hb_id2
           {B : hcomp_bicat_data}
           {b₁ b₂ : B}
           (f : hb_mor b₁ b₂)
  : hb_cell f f
  := pr122 (pr222 B) _ _ f.

Definition hb_vcomp
           {B : hcomp_bicat_data}
           {b₁ b₂ : B}
           {f g h : hb_mor b₁ b₂}
           (α : hb_cell f g)
           (β : hb_cell g h)
  : hb_cell f h
  := pr1 (pr222 (pr222 B)) _ _ _ _ _ α β.

Definition hb_runit
           {B : hcomp_bicat_data}
           {b₁ b₂ : B}
           (f : hb_mor b₁ b₂)
  : hb_cell (hb_comp1 f (hb_id1 b₂)) f
  := pr12 (pr222 (pr222 B)) _ _ f.

Definition hb_rinvunit
           {B : hcomp_bicat_data}
           {b₁ b₂ : B}
           (f : hb_mor b₁ b₂)
  : hb_cell f (hb_comp1 f (hb_id1 b₂))
  := pr122 (pr222 (pr222 B)) _ _ f.

Definition hb_lunit
           {B : hcomp_bicat_data}
           {b₁ b₂ : B}
           (f : hb_mor b₁ b₂)
  : hb_cell (hb_comp1 (hb_id1 b₁) f) f
  := pr1 (pr222 (pr222 (pr222 B))) _ _ f.

Definition hb_linvunit
           {B : hcomp_bicat_data}
           {b₁ b₂ : B}
           (f : hb_mor b₁ b₂)
  : hb_cell f (hb_comp1 (hb_id1 b₁) f)
  := pr12 (pr222 (pr222 (pr222 B))) _ _ f.

Definition hb_lassoc
           {B : hcomp_bicat_data}
           {b₁ b₂ b₃ b₄ : B}
           (f : hb_mor b₁ b₂)
           (g : hb_mor b₂ b₃)
           (h : hb_mor b₃ b₄)
  : hb_cell (hb_comp1 (hb_comp1 f g) h) (hb_comp1 f (hb_comp1 g h))
  := pr122 (pr222 (pr222 (pr222 B))) _ _ _ _ f g h.

Definition hb_rassoc
           {B : hcomp_bicat_data}
           {b₁ b₂ b₃ b₄ : B}
           (f : hb_mor b₁ b₂)
           (g : hb_mor b₂ b₃)
           (h : hb_mor b₃ b₄)
  : hb_cell (hb_comp1 f (hb_comp1 g h)) (hb_comp1 (hb_comp1 f g) h)
  := pr1 (pr222 (pr222 (pr222 (pr222 B)))) _ _ _ _ f g h.

Definition hb_hcomp
           {B : hcomp_bicat_data}
           {b₁ b₂ b₃ : B}
           {f₁ f₂ : hb_mor b₁ b₂}
           {g₁ g₂ : hb_mor b₂ b₃}
           (α : hb_cell f₁ f₂)
           (β : hb_cell g₁ g₂)
  : hb_cell (hb_comp1 f₁ g₁) (hb_comp1 f₂ g₂)
  := pr2 (pr222 (pr222 (pr222 (pr222 B)))) _ _ _ _ _ _ _ α β.

Definition hcomp_bicat_laws
           (B : hcomp_bicat_data)
  : UU
  := (∏ (b₁ b₂ : B)
        (f g : hb_mor b₁ b₂)
        (α : hb_cell f g),
      hb_vcomp (hb_id2 _) α = α)
       × (∏ (b₁ b₂ : B)
            (f g : hb_mor b₁ b₂)
            (α : hb_cell f g),
          hb_vcomp α (hb_id2 _) = α)
       × (∏ (b₁ b₂ : B)
            (f₁ f₂ f₃ f₄ : hb_mor b₁ b₂)
            (α : hb_cell f₁ f₂)
            (β : hb_cell f₂ f₃)
            (γ : hb_cell f₃ f₄),
          hb_vcomp α (hb_vcomp β γ) = hb_vcomp (hb_vcomp α β) γ)
       × (∏ (b₁ b₂ : B)
            (f₁ f₂ f₃ f₄ : hb_mor b₁ b₂)
            (α : hb_cell f₁ f₂)
            (β : hb_cell f₂ f₃)
            (γ : hb_cell f₃ f₄),
          hb_vcomp (hb_vcomp α β) γ = hb_vcomp α (hb_vcomp β γ))
       × (∏ (b₁ b₂ : B)
            (f g : hb_mor b₁ b₂),
          isaset (hb_cell f g))
       × (∏ (b₁ b₂ b₃ : B)
            (f : hb_mor b₁ b₂)
            (g : hb_mor b₂ b₃),
          hb_hcomp (hb_id2 f) (hb_id2 g)
          =
          hb_id2 (hb_comp1 f g))
       × (∏ (b₁ b₂ b₃ : B)
            (f₁ g₁ h₁ : hb_mor b₁ b₂)
            (f₂ g₂ h₂ : hb_mor b₂ b₃)
            (α₁ : hb_cell f₁ g₁)
            (α₂ : hb_cell f₂ g₂)
            (β₁ : hb_cell g₁ h₁)
            (β₂ : hb_cell g₂ h₂),
          hb_hcomp (hb_vcomp α₁ β₁) (hb_vcomp α₂ β₂)
          =
          hb_vcomp (hb_hcomp α₁ α₂) (hb_hcomp β₁ β₂))
       × (∏ (a b c d : B)
            (f₁ f₂ : hb_mor a b)
            (g₁ g₂ : hb_mor b c)
            (h₁ h₂ : hb_mor c d)
            (α₁ : hb_cell f₁ f₂)
            (α₂ : hb_cell g₁ g₂)
            (α₃ : hb_cell h₁ h₂),
          hb_vcomp
            (hb_hcomp α₁ (hb_hcomp α₂ α₃))
            (hb_rassoc _ _ _)
          =
          hb_vcomp
            (hb_rassoc _ _ _)
            (hb_hcomp (hb_hcomp α₁ α₂) α₃))
       × (∏ (a b : B)
            (f₁ f₂ : hb_mor a b)
            (α : hb_cell f₁ f₂),
          hb_vcomp (hb_hcomp (hb_id2 (hb_id1 a)) α) (hb_lunit f₂)
          =
          hb_vcomp (hb_lunit f₁) α)
       × (∏ (a b : B)
            (f₁ f₂ : hb_mor a b)
            (α : hb_cell f₁ f₂),
          hb_vcomp (hb_hcomp α (hb_id2 (hb_id1 b))) (hb_runit f₂)
          =
          hb_vcomp (hb_runit f₁) α)
       × (∏ (b₁ b₂ b₃ b₄ : B)
            (f : hb_mor b₁ b₂)
            (g : hb_mor b₂ b₃)
            (h : hb_mor b₃ b₄),
          hb_vcomp
            (hb_rassoc f g h)
            (hb_lassoc f g h)
          =
          hb_id2 _)
       × (∏ (b₁ b₂ b₃ b₄ : B)
            (f : hb_mor b₁ b₂)
            (g : hb_mor b₂ b₃)
            (h : hb_mor b₃ b₄),
          hb_vcomp
            (hb_lassoc f g h)
            (hb_rassoc f g h)
          =
          hb_id2 _)
       × (∏ (b₁ b₂ : B)
            (f : hb_mor b₁ b₂),
          hb_vcomp
            (hb_lunit f)
            (hb_linvunit f)
          =
          hb_id2 _)
       × (∏ (b₁ b₂ : B)
            (f : hb_mor b₁ b₂),
          hb_vcomp
            (hb_linvunit f)
            (hb_lunit f)
          =
          hb_id2 _)
       × (∏ (b₁ b₂ : B)
            (f : hb_mor b₁ b₂),
          hb_vcomp
            (hb_runit f)
            (hb_rinvunit f)
          =
          hb_id2 _)
       × (∏ (b₁ b₂ : B)
            (f : hb_mor b₁ b₂),
          hb_vcomp
            (hb_rinvunit f)
            (hb_runit f)
          =
          hb_id2 _)
       × (∏ (a b c d e : B)
            (k : hb_mor a b)
            (h : hb_mor b c)
            (g : hb_mor c d)
            (f : hb_mor d e),
          hb_vcomp
            (hb_rassoc k h (hb_comp1 g f))
            (hb_rassoc (hb_comp1 k h) g f)
          =
          hb_vcomp
            (hb_vcomp
               (hb_hcomp (hb_id2 k) (hb_rassoc h g f))
               (hb_rassoc k (hb_comp1 h g) f))
            (hb_hcomp (hb_rassoc k h g) (hb_id2 f)))
       × (∏ (a b c : B)
            (f : hb_mor a b)
            (g : hb_mor b c),
          hb_hcomp (hb_id2 f) (hb_lunit g)
          =
          hb_vcomp
            (hb_rassoc f (hb_id1 b) g)
            (hb_hcomp (hb_runit f) (hb_id2 g))).

Lemma isaprop_hcomp_prebicat_laws
      (B : hcomp_bicat_data)
      (H : ∏ (a b : B) (f g : hb_mor a b), isaset (hb_cell f g))
  : isaprop (hcomp_bicat_laws B).
Proof.
  repeat (apply isapropdirprod)
  ; try (repeat (apply impred ; intro)
         ; apply H).
  do 4 (apply impred ; intro).
  apply isapropisaset.
Qed.

Definition hcomp_bicat
  : UU
  := ∑ (B : hcomp_bicat_data), hcomp_bicat_laws B.

Coercion hcomp_bicat_to_data
         (B : hcomp_bicat)
  : hcomp_bicat_data
  := pr1 B.

Definition hcomp_bicat_hom_cat
           (B : hcomp_bicat)
           (b₁ b₂ : B)
  : category.
Proof.
  use make_category.
  - use make_precategory.
    + use make_precategory_data.
      * use make_precategory_ob_mor.
        ** exact (hb_mor b₁ b₂).
        ** exact (λ f g, hb_cell f g).
      * exact (λ f, hb_id2 f).
      * exact (λ _ _ _ f g, hb_vcomp f g).
    + repeat split ; simpl ; cbn.
      * exact (pr12 B b₁ b₂).
      * exact (pr122 B b₁ b₂).
      * exact (pr1 (pr222 B) b₁ b₂).
      * exact (pr12 (pr222 B) b₁ b₂).
  - exact (pr122 (pr222 B) b₁ b₂).
Defined.

Definition hcomp_bicat_hcomp
           (B : hcomp_bicat)
           (b₁ b₂ b₃ : pr11 B)
  : precategory_binproduct_data
      (hcomp_bicat_hom_cat B b₁ b₂)
      (hcomp_bicat_hom_cat B b₂ b₃)
    ⟶
    hcomp_bicat_hom_cat B b₁ b₃.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (λ fg, hb_comp1 (pr1 fg) (pr2 fg)).
    + exact (λ fg fg' α, hb_hcomp (pr1 α) (pr2 α)).
  - split.
    + intros f ; cbn in *.
      exact (pr1 (pr222 (pr222 B)) b₁ b₂ b₃ (pr1 f) (pr2 f)).
    + intros f g h α β ; cbn in *.
      exact (pr12 (pr222 (pr222 B)) b₁ b₂ b₃ _ _ _ _ _ _ (pr1 α) (pr2 α) (pr1 β) (pr2 β)).
Defined.

Definition hcomp_bicat_to_prebicategory_ob_hom
           (B : hcomp_bicat)
  : prebicategory_ob_hom.
Proof.
  simple refine (_ ,, _).
  - exact B.
  - exact (hcomp_bicat_hom_cat B).
Defined.

Definition hcomp_bicat_to_prebicategory_id_comp
           (B : hcomp_bicat)
  : prebicategory_id_comp.
Proof.
  simple refine (_ ,, _ ,, _).
  - exact (hcomp_bicat_to_prebicategory_ob_hom B).
  - exact (λ a, hb_id1 a).
  - exact (hcomp_bicat_hcomp B).
Defined.

Definition hcomp_bicat_associator
           (B : hcomp_bicat)
           (a b c d : hcomp_bicat_to_prebicategory_id_comp B)
  : associator_trans_type a b c d.
Proof.
  use make_nat_trans.
  - exact (λ f, hb_rassoc (pr1 f) (pr12 f) (pr22 f)).
  - intros f₁ f₂ α.
    apply (pr122 (pr222 (pr222 B))).
Defined.

Definition hcomp_bicat_lunitor
           (B : hcomp_bicat)
           (a b : hcomp_bicat_to_prebicategory_id_comp B)
  : left_unitor_trans_type a b.
Proof.
  use make_nat_trans.
  - exact (λ f, hb_lunit f).
  - intros f₁ f₂ α.
    apply (pr1 (pr222 (pr222 (pr222 B)))).
Defined.

Definition hcomp_bicat_runitor
           (B : hcomp_bicat)
           (a b : hcomp_bicat_to_prebicategory_id_comp B)
  : right_unitor_trans_type a b.
Proof.
  use make_nat_trans.
  - exact (λ f, hb_runit f).
  - intros f₁ f₂ α.
    apply (pr2 (pr222 (pr222 (pr222 B)))).
Defined.

Definition hcomp_bicat_to_prebicategory_data
           (B : hcomp_bicat)
  : prebicategory_data.
Proof.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (hcomp_bicat_to_prebicategory_id_comp B).
  - exact (hcomp_bicat_associator B).
  - exact (hcomp_bicat_lunitor B).
  - exact (hcomp_bicat_runitor B).
Defined.

Definition hcomp_bicat_is_prebicategory
           (B : hcomp_bicat)
  : is_prebicategory (hcomp_bicat_to_prebicategory_data B).
Proof.
  repeat split.
  - intros b₁ b₂ b₃ b₄ f g h ; cbn in *.
    use make_is_z_isomorphism.
    + exact (hb_lassoc f g h).
    + split ; apply (pr2 B).
  - intros b₁ b₂ f ; cbn in *.
    use make_is_z_isomorphism.
    + exact (hb_linvunit f).
    + split ; apply (pr2 B).
  - intros b₁ b₂ f ; cbn in *.
    use make_is_z_isomorphism.
    + exact (hb_rinvunit f).
    + split ; apply (pr2 B).
  - apply (pr2 B).
  - apply (pr2 B).
Defined.

Definition hcomp_bicat_to_prebicategory
           (B : hcomp_bicat)
  : prebicategory.
Proof.
  simple refine (_ ,, _).
  - exact (hcomp_bicat_to_prebicategory_data B).
  - exact (hcomp_bicat_is_prebicategory B).
Defined.

Definition prebicategory_to_hcomp_bicat_data
           (B : prebicategory)
  : hcomp_bicat_data.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
  - exact (pr1 (pr111 B)).
  - intros b₁ b₂.
    exact (pr2 (pr111 B) b₁ b₂).
  - intros b₁ b₂ f g.
    exact (f --> g).
  - exact (pr1 (pr211 B)).
  - intros b₁ b₂ b₃ f g.
    exact (pr2 (pr211 B) b₁ b₂ b₃ (f ,, g)).
  - intros ; simpl.
    apply identity.
  - exact (λ _ _ _ _ _ α β, α · β).
  - cbn in *.
    intros b₁ b₂ f.
    exact (pr1 (pr2 (pr221 B) b₁ b₂) f).
  - intros a b f.
    apply (pr2 (pr212 B) _ _ f).
  - cbn in *.
    intros b₁ b₂ f.
    exact (pr1 (pr1 (pr221 B) b₁ b₂) f).
  - intros a b f.
    apply (pr1 (pr212 B) _ _ f).
  - intros b₁ b₂ b₃ b₄ f g h ; cbn in *.
    apply ((pr112 B) _ _ _ _ f g h).
  - intros b₁ b₂ b₃ b₄ f g h ; cbn in *.
    exact (pr1 ((pr121 B) _ _ _ _) (f ,, g ,, h)).
  - intros b₁ b₂ b₃ f₁ f₂ g₁ g₂ α β ; simpl in *.
    apply (#(pr2 (pr211 B) b₁ b₂ b₃)).
    exact (α ,, β).
Defined.

Definition prebicategory_to_hcomp_bicat
           (B : prebicategory)
  : hcomp_bicat.
Proof.
  simple refine (_ ,, _).
  - exact (prebicategory_to_hcomp_bicat_data B).
  - repeat split ; cbn ; intros.
    + apply id_left.
    + apply id_right.
    + apply assoc.
    + apply assoc'.
    + apply homset_property.
    + apply (functor_id ((pr221 (pr1 B)) b₁ b₂ b₃)).
    + apply (@functor_comp
               _ _
               ((pr221 (pr1 B)) b₁ b₂ b₃)
               (_ ,, _) (_ ,, _) (_ ,, _)
               (_ ,, _) (_ ,, _)).
    + apply (@nat_trans_ax
               _ _ _ _
               ((pr121 B) a b c d)
               (_ ,, (_ ,, _))
               (_ ,, (_ ,, _))
               (_ ,, (_ ,, _))).
    + apply (nat_trans_ax ((pr122 (pr1 B)) a b)).
    + apply (nat_trans_ax ((pr222 (pr1 B)) a b)).
    + apply (z_iso_inv_after_z_iso (make_z_iso _ _ ((pr112 B) b₁ b₂ b₃ b₄ f g h))).
    + apply (z_iso_after_z_iso_inv (make_z_iso _ _ ((pr112 B) b₁ b₂ b₃ b₄ f g h))).
    + apply (z_iso_inv_after_z_iso (make_z_iso _ _ ((pr121 (pr2 B)) b₁ b₂ f))).
    + apply (z_iso_after_z_iso_inv (make_z_iso _ _ ((pr121 (pr2 B)) b₁ b₂ f))).
    + apply (z_iso_inv_after_z_iso (make_z_iso _ _ ((pr221 (pr2 B)) b₁ b₂ f))).
    + apply (z_iso_after_z_iso_inv (make_z_iso _ _ ((pr221 (pr2 B)) b₁ b₂ f))).
    + apply B.
    + apply B.
Defined.

Definition hcomp_bicat_weq_prebicategory
  : hcomp_bicat ≃ prebicategory.
Proof.
  use make_weq.
  - exact hcomp_bicat_to_prebicategory.
  - use isweq_iso.
    + exact prebicategory_to_hcomp_bicat.
    + intros b.
      apply idpath.
    + intros b.
      apply idpath.
Defined.


Definition hcomp_bicat_to_precategory_ob_mor
           (B : hcomp_bicat)
  : precategory_ob_mor.
Proof.
  simple refine (_ ,, _).
  - exact B.
  - exact (λ b₁ b₂, hb_mor b₁ b₂).
Defined.

Definition hcomp_bicat_to_precategory_id_comp
           (B : hcomp_bicat)
  : precategory_id_comp (hcomp_bicat_to_precategory_ob_mor B).
Proof.
  simple refine (_ ,, _).
  - exact (λ x, hb_id1 _).
  - exact (λ _ _ _ f g, hb_comp1 f g).
Defined.

Definition hcomp_bicat_to_precategory_data
           (B : hcomp_bicat)
  : precategory_data.
Proof.
  simple refine (_ ,, _).
  - exact (hcomp_bicat_to_precategory_ob_mor B).
  - exact (hcomp_bicat_to_precategory_id_comp B).
Defined.

Definition hcomp_bicat_to_prebicat_1_id_comp_cells
           (B : hcomp_bicat)
  : prebicat_1_id_comp_cells.
Proof.
  simple refine (_ ,, _).
  - exact (hcomp_bicat_to_precategory_data B).
  - exact (λ x y f g, hb_cell f g).
Defined.

Definition hcomp_bicat_to_prebicat_2_id_comp_struct
           (B : hcomp_bicat)
  : prebicat_2_id_comp_struct (hcomp_bicat_to_prebicat_1_id_comp_cells B).
Proof.
  repeat split ; cbn.
  - intros.
    apply hb_id2.
  - intros.
    apply hb_lunit.
  - intros.
    apply hb_runit.
  - intros.
    apply hb_linvunit.
  - intros.
    apply hb_rinvunit.
  - intros.
    apply hb_lassoc.
  - intros.
    apply hb_rassoc.
  - intros ? ? ? ? ? α β.
    exact (hb_vcomp α β).
  - intros ? ? ? f ? ? α.
    exact (hb_hcomp (hb_id2 _) α).
  - intros ? ? ? f ? ? α.
    exact (hb_hcomp α (hb_id2 _)).
Defined.

Definition hcomp_bicat_to_prebicat_data
           (B : hcomp_bicat)
  : prebicat_data.
Proof.
  simple refine (_ ,, _).
  - exact (hcomp_bicat_to_prebicat_1_id_comp_cells B).
  - exact (hcomp_bicat_to_prebicat_2_id_comp_struct B).
Defined.

Definition hcomp_bicat_to_prebicat_laws
           (B : hcomp_bicat)
  : prebicat_laws (hcomp_bicat_to_prebicat_data B).
Proof.
  repeat split ; try (intros ; apply (pr2 B)).
  - intros ; cbn.
    etrans.
    {
      refine (!_).
      apply (pr12 (pr222 (pr222 B))).
    }
    apply maponpaths_2.
    apply B.
  - intros ; cbn.
    etrans.
    {
      refine (!_).
      apply (pr12 (pr222 (pr222 B))).
    }
    apply maponpaths.
    apply B.
  - intros ; cbn.
    etrans.
    {
      apply (pr122 (pr222 ((pr222 B)))).
    }
    apply maponpaths.
    apply maponpaths_2.
    apply B.
  - intros a b c d f₁ f₂ g h α ; cbn.
    pose (pr122 (pr222 ((pr222 B))) a b c d f₁ f₂ g g h h α (hb_id2 _) (hb_id2 _)) as p.
    cbn in p.
    etrans.
    {
      exact (!p).
    }
    apply maponpaths_2.
    apply maponpaths.
    apply B.
  - intros a b c f₁ f₂ g h α β ; cbn.
    etrans.
    {
      refine (!_).
      apply (pr12 (pr222 (pr222 B))).
    }
    refine (!_).
    etrans.
    {
      refine (!_).
      apply (pr12 (pr222 (pr222 B))).
    }
    etrans.
    {
      apply maponpaths.
      apply B.
    }
    etrans.
    {
      apply maponpaths_2.
      apply B.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply B.
    }
    apply maponpaths_2.
    apply B.
  - intros ; cbn.
    refine (!_).
    apply B.
  - intros ; cbn.
    refine (!_).
    apply B.
Qed.

Definition hcomp_bicat_to_prebicat
           (B : hcomp_bicat)
  : prebicat.
Proof.
  simple refine (_ ,, _).
  - exact (hcomp_bicat_to_prebicat_data B).
  - exact (hcomp_bicat_to_prebicat_laws B).
Defined.

Definition hcomp_bicat_to_bicat
           (B : hcomp_bicat)
  : bicat.
Proof.
  simple refine (_ ,, _).
  - exact (hcomp_bicat_to_prebicat B).
  - simpl.
    intro ; intros.
    apply (pr122 (pr222 B)).
Defined.

Definition bicat_to_hcomp_bicat_data
           (B : bicat)
  : hcomp_bicat_data.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
  - exact B.
  - exact (λ x y, x --> y).
  - exact (λ _ _ f g, f ==> g).
  - exact (λ x, id₁ _).
  - exact (λ _ _ _ f g, f · g).
  - exact (λ _ _ f, id2 f).
  - exact (λ _ _ _ _ _ α β, α • β).
  - exact (λ _ _ f, runitor f).
  - exact (λ _ _ f, rinvunitor f).
  - exact (λ _ _ f, lunitor f).
  - exact (λ _ _ f, linvunitor f).
  - exact (λ _ _ _ _ f g h, rassociator f g h).
  - exact (λ _ _ _ _ f g h, lassociator f g h).
  - exact (λ _ _ _ _ _ _ _ α β, β ⋆⋆ α).
Defined.

Definition bicat_to_hcomp_bicat_laws
           (B : bicat)
  : hcomp_bicat_laws (bicat_to_hcomp_bicat_data B).
Proof.
  repeat split ; cbn ; intros.
  - apply id2_left.
  - apply id2_right.
  - apply vassocr.
  - apply vassocl.
  - apply cellset_property.
  - apply hcomp_identity.
  - apply interchange.
  - apply hcomp_lassoc.
  - apply lunitor_natural.
  - apply runitor_natural.
  - apply lassociator_rassociator.
  - apply rassociator_lassociator.
  - apply lunitor_linvunitor.
  - apply linvunitor_lunitor.
  - apply runitor_rinvunitor.
  - apply rinvunitor_runitor.
  - rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
    refine (!_).
    apply lassociator_lassociator.
  - rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
    rewrite <- lunitor_lwhisker.
    rewrite !vassocr.
    rewrite lassociator_rassociator.
    rewrite id2_left.
    apply idpath.
Qed.

Definition bicat_to_hcomp_bicat
           (B : bicat)
  : hcomp_bicat.
Proof.
  simple refine (_ ,, _).
  - exact (bicat_to_hcomp_bicat_data B).
  - exact (bicat_to_hcomp_bicat_laws B).
Defined.

Definition hcomp_bicat_to_bicat_to_hcomp_bicat
           (B : hcomp_bicat)
  : bicat_to_hcomp_bicat (hcomp_bicat_to_bicat B) = B.
Proof.
  use total2_paths_f.
  - do 13 (use total2_paths_f ; [ apply idpath | ] ; cbn).
    use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro z.
    use funextsec ; intro f₁.
    use funextsec ; intro f₂.
    use funextsec ; intro g₁.
    use funextsec ; intro g₂.
    use funextsec ; intro α.
    use funextsec ; intro β.
    cbn.
    etrans.
    {
      refine (!_).
      apply (pr12 (pr222 (pr222 B))).
    }
    etrans.
    {
      apply maponpaths.
      apply (pr12 B).
    }
    etrans.
    {
      apply maponpaths_2.
      apply (pr122 B).
    }
    apply idpath.
  - apply isaprop_hcomp_prebicat_laws.
    apply B.
Qed.

Definition bicat_to_hcomp_bicat_to_bicat
           (B : bicat)
  : hcomp_bicat_to_bicat (bicat_to_hcomp_bicat B) = B.
Proof.
  use subtypePath.
  {
    intro.
    do 4 (use impred ; intro).
    apply isapropisaset.
  }
  use total2_paths_f.
  - use total2_paths_f.
    + apply idpath.
    + repeat (use pathsdirprod) ; cbn.
      * apply idpath.
      * apply idpath.
      * apply idpath.
      * apply idpath.
      * apply idpath.
      * apply idpath.
      * apply idpath.
      * apply idpath.
      * repeat (use funextsec ; intro).
        rewrite <- lwhisker_hcomp.
        apply idpath.
      * repeat (use funextsec ; intro).
        rewrite <- rwhisker_hcomp.
        apply idpath.
  - apply isaprop_prebicat_laws.
    intros.
    apply cellset_property.
Qed.


Definition hcomp_bicat_weq_bicat
  : hcomp_bicat ≃ bicat.
Proof.
  use make_weq.
  - exact hcomp_bicat_to_bicat.
  - use isweq_iso.
    + exact bicat_to_hcomp_bicat.
    + exact hcomp_bicat_to_bicat_to_hcomp_bicat.
    + exact bicat_to_hcomp_bicat_to_bicat.
Defined.

Definition weq_bicat_prebicategory : bicat ≃ prebicategory.
Proof.
  eapply weqcomp.
  apply (invweq hcomp_bicat_weq_bicat).
  apply hcomp_bicat_weq_prebicategory.
Defined.
