(*******************************************************************

 Sums of categories

 We discuss sums of categories and their universal property

 Contents:
 1. Definition of sums of categories
 2. Universal property for functors
 3. Universal property for natural transformations
 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(** MOVE??? *)
Definition inv_equality_by_case_equality_by_case
           {A B : UU}
           {x y : A ⨿ B}
           (p : x = y)
  : @inv_equality_by_case A B x y (equality_by_case p) = p.
Proof.
  induction x, y, p ; apply idpath.
Defined.

Definition inl_eq_weq
           {A B : UU}
           (a₁ a₂ : A)
  : @inl A B a₁ = inl a₂ ≃ a₁ = a₂.
Proof.
  use make_weq.
  - apply ii1_injectivity.
  -  use gradth.
     + exact (maponpaths inl).
     + abstract
         (intro p ;
          exact (@inv_equality_by_case_equality_by_case A B (inl a₁) (inl a₂) p)).
     + abstract
         (intro p ;
          induction p ;
          apply idpath).
Defined.

Definition inr_eq_weq
           {A B : UU}
           (b₁ b₂ : B)
  : @inr A B b₁ = inr b₂ ≃ b₁ = b₂.
Proof.
  use make_weq.
  - apply ii2_injectivity.
  -  use gradth.
     + exact (maponpaths inr).
     + abstract
         (intro p ;
          exact (@inv_equality_by_case_equality_by_case A B (inr b₁) (inr b₂) p)).
     + abstract
         (intro p ;
          induction p ;
          apply idpath).
Defined.
(**)

(**
 1. Definition of sums of categories
 *)
Definition bincoprod_of_precategory_ob_mor
           (C₁ C₂ : category)
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (C₁ ⨿ C₂).
  - intros z₁ z₂.
    induction z₁ as [ x₁ | y₁ ], z₂ as [ x₂ | y₂ ].
    + exact (x₁ --> x₂).
    + exact ∅.
    + exact ∅.
    + exact (y₁ --> y₂).
Defined.

Definition bincoprod_of_precategory_data
           (C₁ C₂ : category)
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact (bincoprod_of_precategory_ob_mor C₁ C₂).
  - intro z ; induction z as [ x | y ].
    + exact (identity x).
    + exact (identity y).
  - intros z₁ z₂ z₃ f g ;
    induction z₁ as [ x₁ | y₁ ] ;
    induction z₂ as [ x₂ | y₂ ] ;
    induction z₃ as [ x₃ | y₃ ] ; cbn in *.
    + exact (f · g).
    + exact (fromempty g).
    + exact (fromempty g).
    + exact (fromempty f).
    + exact (fromempty f).
    + exact (fromempty f).
    + exact (fromempty g).
    + exact (f · g).
Defined.

Definition bincoprod_of_is_precategory
           (C₁ C₂ : category)
  : is_precategory (bincoprod_of_precategory_data C₁ C₂).
Proof.
  use make_is_precategory.
  - intros z₁ z₂ f.
    induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
    + apply id_left.
    + exact (fromempty f).
    + exact (fromempty f).
    + apply id_left.
  - intros z₁ z₂ f.
    induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
    + apply id_right.
    + exact (fromempty f).
    + exact (fromempty f).
    + apply id_right.
  - intros z₁ z₂ z₃ z₄ f g h ;
    induction z₁ as [ x₁ | y₁ ] ;
    induction z₂ as [ x₂ | y₂ ] ;
    induction z₃ as [ x₃ | y₃ ] ;
    induction z₄ as [ x₄ | y₄ ] ; cbn in * ;
    try (apply (fromempty f)) ; try (apply (fromempty g)) ; try (apply (fromempty h)).
    + apply assoc.
    + apply assoc.
  - intros z₁ z₂ z₃ z₄ f g h ;
    induction z₁ as [ x₁ | y₁ ] ;
    induction z₂ as [ x₂ | y₂ ] ;
    induction z₃ as [ x₃ | y₃ ] ;
    induction z₄ as [ x₄ | y₄ ] ; cbn in * ;
    try (apply (fromempty f)) ; try (apply (fromempty g)) ; try (apply (fromempty h)).
    + apply assoc'.
    + apply assoc'.
Qed.

Definition bincoprod_of_precategory
           (C₁ C₂ : category)
  : precategory.
Proof.
  use make_precategory.
  - exact (bincoprod_of_precategory_data C₁ C₂).
  - exact (bincoprod_of_is_precategory C₁ C₂).
Defined.

Definition bincoprod_of_category_has_homsets
           (C₁ C₂ : category)
  : has_homsets (bincoprod_of_precategory_ob_mor C₁ C₂).
Proof.
  intros z₁ z₂.
  induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
  - apply homset_property.
  - apply isasetempty.
  - apply isasetempty.
  - apply homset_property.
Defined.

Definition bincoprod_of_category
           (C₁ C₂ : category)
  : category.
Proof.
  use make_category.
  - exact (bincoprod_of_precategory C₁ C₂).
  - exact (bincoprod_of_category_has_homsets C₁ C₂).
Defined.

Definition inl_iso_map
           {C₁ C₂ : category}
           {x₁ x₂ : C₁}
           (f : iso x₁ x₂)
  : @iso (bincoprod_of_category C₁ C₂) (inl x₁) (inl x₂).
Proof.
  use make_iso.
  - exact f.
  - use is_iso_qinv.
    + exact (inv_from_iso f).
    + split.
      * exact (iso_inv_after_iso f).
      * exact (iso_after_iso_inv f).
Defined.

Definition inl_iso_inv
           {C₁ C₂ : category}
           {x₁ x₂ : C₁}
           (f : @iso (bincoprod_of_category C₁ C₂) (inl x₁) (inl x₂))
  : iso x₁ x₂.
Proof.
  use make_iso.
  - exact f.
  - use is_iso_qinv.
    + exact (inv_from_iso f).
    + split.
      * exact (iso_inv_after_iso f).
      * exact (iso_after_iso_inv f).
Defined.

Definition inl_iso
           {C₁ C₂ : category}
           (x₁ x₂ : C₁)
  : iso x₁ x₂ ≃ @iso (bincoprod_of_category C₁ C₂) (inl x₁) (inl x₂).
Proof.
  use make_weq.
  - exact inl_iso_map.
  - use gradth.
    + exact inl_iso_inv.
    + abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso | ] ;
         apply idpath).
    + abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso | ] ;
         apply idpath).
Defined.

Definition inr_iso_map
           {C₁ C₂ : category}
           {x₁ x₂ : C₂}
           (f : iso x₁ x₂)
  : @iso (bincoprod_of_category C₁ C₂) (inr x₁) (inr x₂).
Proof.
  use make_iso.
  - exact f.
  - use is_iso_qinv.
    + exact (inv_from_iso f).
    + split.
      * exact (iso_inv_after_iso f).
      * exact (iso_after_iso_inv f).
Defined.

Definition inr_iso_inv
           {C₁ C₂ : category}
           {x₁ x₂ : C₂}
           (f : @iso (bincoprod_of_category C₁ C₂) (inr x₁) (inr x₂))
  : iso x₁ x₂.
Proof.
  use make_iso.
  - exact f.
  - use is_iso_qinv.
    + exact (inv_from_iso f).
    + split.
      * exact (iso_inv_after_iso f).
      * exact (iso_after_iso_inv f).
Defined.

Definition inr_iso
           {C₁ C₂ : category}
           (x₁ x₂ : C₂)
  : iso x₁ x₂ ≃ @iso (bincoprod_of_category C₁ C₂) (inr x₁) (inr x₂).
Proof.
  use make_weq.
  - exact inr_iso_map.
  - use gradth.
    + exact inr_iso_inv.
    + abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso | ] ;
         apply idpath).
    + abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_iso | ] ;
         apply idpath).
Defined.

Definition idtoiso_in_bincoprod_inl
           {C₁ C₂ : category}
           {x₁ x₂ : C₁}
           (p : x₁ = x₂)
  : pr1 (idtoiso p)
    =
    pr1 (@idtoiso
           (bincoprod_of_category C₁ C₂)
           (inl x₁)
           (inl x₂)
           (maponpaths inl p)).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Definition idtoiso_in_bincoprod_inr
           {C₁ C₂ : category}
           {x₁ x₂ : C₂}
           (p : x₁ = x₂)
  : pr1 (idtoiso p)
    =
    pr1 (@idtoiso
           (bincoprod_of_category C₁ C₂)
           (inr x₁)
           (inr x₂)
           (maponpaths inr p)).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Definition is_univalent_bincoprod_of_category
           {C₁ C₂ : category}
           (HC₁ : is_univalent C₁)
           (HC₂ : is_univalent C₂)
  : is_univalent (bincoprod_of_category C₁ C₂).
Proof.
  intros z₁ z₂.
  induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
  - use weqhomot.
    + exact (inl_iso x₁ x₂
             ∘ make_weq _ (HC₁ x₁ x₂)
             ∘ inl_eq_weq x₁ x₂)%weq.
    + abstract
        (intro p ;
         use subtypePath ; [ intro ; apply isaprop_is_iso | ] ;
         cbn -[equality_by_case] ;
         refine (@idtoiso_in_bincoprod_inl C₁ C₂ _ _ (ii1_injectivity x₁ x₂ p) @ _) ;
         do 2 apply maponpaths ;
         apply (@inv_equality_by_case_equality_by_case C₁ C₂ (inl x₁) (inl x₂) p)).
  - use gradth.
    + exact (λ f, fromempty (pr1 f)).
    + intro p ; cbn.
      exact (fromempty (negpathsii1ii2 _ _ p)).
    + intro p ; cbn.
      exact (fromempty (pr1 p)).
  - use gradth.
    + exact (λ f, fromempty (pr1 f)).
    + intro p ; cbn.
      exact (fromempty (negpathsii2ii1 _ _ p)).
    + intro p ; cbn.
      exact (fromempty (pr1 p)).
  - use weqhomot.
    + exact (inr_iso y₁ y₂
             ∘ make_weq _ (HC₂ y₁ y₂)
             ∘ inr_eq_weq y₁ y₂)%weq.
    + abstract
        (intro p ;
         use subtypePath ; [ intro ; apply isaprop_is_iso | ] ;
         cbn -[equality_by_case] ;
         refine (@idtoiso_in_bincoprod_inr C₁ C₂ _ _ (ii2_injectivity y₁ y₂ p) @ _) ;
         do 2 apply maponpaths ;
         apply (@inv_equality_by_case_equality_by_case C₁ C₂ (inr y₁) (inr y₂) p)).
Defined.

Definition bincoprod_of_univalent_category
           (C₁ C₂ : univalent_category)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (bincoprod_of_category C₁ C₂).
  - use is_univalent_bincoprod_of_category.
    + apply C₁.
    + apply C₂.
Defined.

(**
 2. Universal property for functors
 *)
Definition inl_functor_data
           (C₁ C₂ : category)
  : functor_data C₁ (bincoprod_of_category C₁ C₂).
Proof.
  use make_functor_data.
  - exact (λ x, inl x).
  - exact (λ _ _ f, f).
Defined.

Definition inl_is_functor
           (C₁ C₂ : category)
  : is_functor (inl_functor_data C₁ C₂).
Proof.
  split ; intro ; intros ; cbn.
  - apply idpath.
  - apply idpath.
Qed.

Definition inl_functor
           (C₁ C₂ : category)
  : C₁ ⟶ bincoprod_of_category C₁ C₂.
Proof.
  use make_functor.
  - exact (inl_functor_data C₁ C₂).
  - exact (inl_is_functor C₁ C₂).
Defined.

Definition inr_functor_data
           (C₁ C₂ : category)
  : functor_data C₂ (bincoprod_of_category C₁ C₂).
Proof.
  use make_functor_data.
  - exact (λ x, inr x).
  - exact (λ _ _ f, f).
Defined.

Definition inr_is_functor
           (C₁ C₂ : category)
  : is_functor (inr_functor_data C₁ C₂).
Proof.
  split ; intro ; intros ; cbn.
  - apply idpath.
  - apply idpath.
Qed.

Definition inr_functor
           (C₁ C₂ : category)
  : C₂ ⟶ bincoprod_of_category C₁ C₂.
Proof.
  use make_functor.
  - exact (inr_functor_data C₁ C₂).
  - exact (inr_is_functor C₁ C₂).
Defined.

Definition sum_of_functors_data
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : functor_data (bincoprod_of_category C₁ C₂) Q.
Proof.
  use make_functor_data.
  - intro z.
    induction z as [ x | y ].
    + exact (F x).
    + exact (G y).
  - intros z₁ z₂ f.
    induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
    + exact (#F f).
    + exact (fromempty f).
    + exact (fromempty f).
    + exact (#G f).
Defined.

Definition sum_of_functors_is_functor
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : is_functor (sum_of_functors_data F G).
Proof.
  split.
  - intro z.
    induction z as [ x | y ] ; cbn.
    + apply functor_id.
    + apply functor_id.
  - intros z₁ z₂ z₃ f g.
    induction z₁ as [ x₁ | y₁ ] ;
    induction z₂ as [ x₂ | y₂ ] ;
    induction z₃ as [ x₃ | y₃ ] ; cbn ;
    try (apply (fromempty f)) ; try (apply (fromempty g)).
    + apply functor_comp.
    + apply functor_comp.
Qed.

Definition sum_of_functors
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : bincoprod_of_category C₁ C₂ ⟶ Q.
Proof.
  use make_functor.
  - exact (sum_of_functors_data F G).
  - exact (sum_of_functors_is_functor F G).
Defined.

Definition sum_of_functor_inl
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : inl_functor C₁ C₂ ∙ sum_of_functors F G ⟹ F.
Proof.
  use make_nat_trans.
  - exact (λ z, identity _).
  - abstract
      (intros x₁ x₂ f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition sum_of_functor_inl_is_nat_iso
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : is_nat_iso (sum_of_functor_inl F G).
Proof.
  intro.
  apply identity_is_iso.
Defined.

Definition sum_of_functor_inl_nat_iso
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : nat_iso
      (inl_functor C₁ C₂ ∙ sum_of_functors F G)
      F.
Proof.
  use make_nat_iso.
  - exact (sum_of_functor_inl F G).
  - exact (sum_of_functor_inl_is_nat_iso F G).
Defined.

Definition sum_of_functor_inr
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : inr_functor C₁ C₂ ∙ sum_of_functors F G ⟹ G.
Proof.
  use make_nat_trans.
  - exact (λ z, identity _).
  - abstract
      (intros x₁ x₂ f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition sum_of_functor_inr_is_nat_iso
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : is_nat_iso (sum_of_functor_inr F G).
Proof.
  intro.
  apply identity_is_iso.
Defined.

Definition sum_of_functor_inr_nat_iso
           {Q C₁ C₂ : category}
           (F : C₁ ⟶ Q)
           (G : C₂ ⟶ Q)
  : nat_iso
      (inr_functor C₁ C₂ ∙ sum_of_functors F G)
      G.
Proof.
  use make_nat_iso.
  - exact (sum_of_functor_inr F G).
  - exact (sum_of_functor_inr_is_nat_iso F G).
Defined.

(**
 3. Universal property for natural transformations
 *)
Definition sum_of_nat_trans_data
           {Q C₁ C₂ : category}
           {F G : bincoprod_of_category C₁ C₂ ⟶ Q}
           (α : inl_functor C₁ C₂ ∙ F ⟹ inl_functor C₁ C₂ ∙ G)
           (β : inr_functor C₁ C₂ ∙ F ⟹ inr_functor C₁ C₂ ∙ G)
  : nat_trans_data F G.
Proof.
  intros z.
  induction z as [ x | y ].
  - exact (α x).
  - exact (β y).
Defined.

Definition sum_of_nat_trans_is_nat_trans
           {Q C₁ C₂ : category}
           {F G : bincoprod_of_category C₁ C₂ ⟶ Q}
           (α : inl_functor C₁ C₂ ∙ F ⟹ inl_functor C₁ C₂ ∙ G)
           (β : inr_functor C₁ C₂ ∙ F ⟹ inr_functor C₁ C₂ ∙ G)
  : is_nat_trans _ _ (sum_of_nat_trans_data α β).
Proof.
  intros z₁ z₂ f.
  induction z₁ as [ x₁ | y₁ ] ; induction z₂ as [ x₂ | y₂ ] ; cbn.
  - exact (nat_trans_ax α _ _ f).
  - exact (fromempty f).
  - exact (fromempty f).
  - exact (nat_trans_ax β _ _ f).
Qed.

Definition sum_of_nat_trans
           {Q C₁ C₂ : category}
           {F G : bincoprod_of_category C₁ C₂ ⟶ Q}
           (α : inl_functor C₁ C₂ ∙ F ⟹ inl_functor C₁ C₂ ∙ G)
           (β : inr_functor C₁ C₂ ∙ F ⟹ inr_functor C₁ C₂ ∙ G)
  : F ⟹ G.
Proof.
  use make_nat_trans.
  - exact (sum_of_nat_trans_data α β).
  - exact (sum_of_nat_trans_is_nat_trans α β).
Defined.

Definition sum_of_nat_trans_inl
           {Q C₁ C₂ : category}
           {F G : bincoprod_of_category C₁ C₂ ⟶ Q}
           (α : inl_functor C₁ C₂ ∙ F ⟹ inl_functor C₁ C₂ ∙ G)
           (β : inr_functor C₁ C₂ ∙ F ⟹ inr_functor C₁ C₂ ∙ G)
  : pre_whisker (inl_functor_data _ _) (sum_of_nat_trans α β) = α.
Proof.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro.
  apply idpath.
Qed.

Definition sum_of_nat_trans_inr
           {Q C₁ C₂ : category}
           {F G : bincoprod_of_category C₁ C₂ ⟶ Q}
           (α : inl_functor C₁ C₂ ∙ F ⟹ inl_functor C₁ C₂ ∙ G)
           (β : inr_functor C₁ C₂ ∙ F ⟹ inr_functor C₁ C₂ ∙ G)
  : pre_whisker (inr_functor_data _ _) (sum_of_nat_trans α β) = β.
Proof.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro.
  apply idpath.
Qed.
