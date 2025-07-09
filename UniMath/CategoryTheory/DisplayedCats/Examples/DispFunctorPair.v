(*********************************************************************************

 Displayed functors over pairs

 In this file, we look at displayed functor over the pair of identity functors.
 More specifically, suppose that we have two displayed category `D₁` and `D₂` over
 the category `C × C`, then we could consider
 - Displayed functors over the identity on `C × C`
 - Displayed functors over the pairing of the identity on `C` with itself.
 These two notions are equivalent and we construct an equivalence between them.

 Content
 1. The maps back and forth
 2. The equivalence

 *********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.

(** * 1. The maps back and forth *)
Definition disp_functor_over_pair_data
           {C : category}
           {D₁ D₂ : disp_cat (category_binproduct C C)}
           (F : disp_functor
                  (functor_identity (category_binproduct C C))
                  D₁ D₂)
  : disp_functor_data
      (pair_functor (functor_identity C) (functor_identity C))
      D₁ D₂.
Proof.
  simple refine (_ ,, _).
  - exact (λ x xx, F x xx).
  - exact (λ x y xx yy f ff, ♯F ff)%mor_disp.
Defined.

Proposition disp_functor_over_pair_laws
            {C : category}
            {D₁ D₂ : disp_cat (category_binproduct C C)}
            (F : disp_functor
                   (functor_identity (category_binproduct C C))
                   D₁ D₂)
  : disp_functor_axioms (disp_functor_over_pair_data F).
Proof.
  split.
  - intros x xx ; cbn.
    refine (disp_functor_id F xx @ _).
    apply maponpaths_2.
    apply homset_property.
  - intros x y z xx yy zz f g ff gg ; cbn.
    refine (disp_functor_comp F ff gg @ _).
    apply maponpaths_2.
    apply homset_property.
Qed.

Definition disp_functor_over_pair
           {C : category}
           {D₁ D₂ : disp_cat (category_binproduct C C)}
           (F : disp_functor
                  (functor_identity (category_binproduct C C))
                  D₁ D₂)
  : disp_functor
      (pair_functor (functor_identity C) (functor_identity C))
      D₁ D₂.
Proof.
  simple refine (_ ,, _).
  - exact (disp_functor_over_pair_data F).
  - exact (disp_functor_over_pair_laws F).
Defined.

Definition disp_functor_over_pair_inv_data
           {C : category}
           {D₁ D₂ : disp_cat (category_binproduct C C)}
           (F : disp_functor
                  (pair_functor (functor_identity C) (functor_identity C))
                  D₁ D₂)
  : disp_functor_data
      (functor_identity (category_binproduct C C))
      D₁ D₂.
Proof.
  simple refine (_ ,, _).
  - exact (λ x xx, F x xx).
  - exact (λ x y f xx yy ff, ♯F ff)%mor_disp.
Defined.

Proposition disp_functor_over_pair_inv_laws
            {C : category}
            {D₁ D₂ : disp_cat (category_binproduct C C)}
            (F : disp_functor
                   (pair_functor (functor_identity C) (functor_identity C))
                   D₁ D₂)
  : disp_functor_axioms (disp_functor_over_pair_inv_data F).
Proof.
  split.
  - intros x xx ; cbn.
    refine (disp_functor_id F xx @ _).
    apply transportf_set.
    apply homset_property.
  - intros x y z xx yy zz f g ff gg ; cbn.
    refine (disp_functor_comp F ff gg @ _).
    apply transportf_set.
    apply homset_property.
Qed.

Definition disp_functor_over_pair_inv
           {C : category}
           {D₁ D₂ : disp_cat (category_binproduct C C)}
           (F : disp_functor
                  (pair_functor (functor_identity C) (functor_identity C))
                  D₁ D₂)
  : disp_functor
      (functor_identity (category_binproduct C C))
      D₁ D₂.
Proof.
  simple refine (_ ,, _).
  - exact (disp_functor_over_pair_inv_data F).
  - exact (disp_functor_over_pair_inv_laws F).
Defined.

(** * 2. The equivalence *)
Definition disp_functor_over_pair_weq
           {C : category}
           (D₁ D₂ : disp_cat (category_binproduct C C))
  : disp_functor
      (functor_identity (category_binproduct C C))
      D₁ D₂
    ≃
    disp_functor
      (pair_functor (functor_identity C) (functor_identity C))
      D₁ D₂.
Proof.
  use weq_iso.
  - exact disp_functor_over_pair.
  - exact disp_functor_over_pair_inv.
  - abstract
      (intro F ;
       use subtypePath ; [ intro ; apply isaprop_disp_functor_axioms | ] ;
       apply idpath).
  - abstract
      (intro F ;
       use subtypePath ; [ intro ; apply isaprop_disp_functor_axioms | ] ;
       apply idpath).
Defined.
