(*************************************************************************

 Indexed categories

 A category indexed on `C` is the same as a pseudofunctor from `C^op` to
 the bicategory of categories. However, one can also formulate this
 definition without referring to bicategories and pseudofunctors, and that
 is what we define in this file.

 Compared to the definition of a pseudofunctor into `Cat`, the definition
 in this file has the following simplifications:
 - Some of the laws hold by default. This is because `C^op` is a discrete
   bicategory and the laws that quantify over all 2-cells (preservation
   of vertical and horizontal composition) then can be proven using path
   induction.
 - The laws are formulated as pointwise equalities of natural
   transformations rather than equality of natural transformations.

 It is worthwhile to note that `indexed_cat C` represents a pseudofunctor
 from `C` to the bicategory of univalent categories and not a
 pseudofunctor from `C^op`.

 Contents
 1. The data of an indexed category
 2. The laws of indexed categories
 3. Indexed categories

 *************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Local Open Scope cat.

(**
 1. The data of an indexed category
 *)
Definition indexed_cat_data
           (C : category)
  : UU
  := ∑ (F₀ : C → univalent_category)
       (F₁ : ∏ (x y : C), x --> y → F₀ x ⟶ F₀ y),
     (∏ (x : C), functor_identity _ ⟹ F₁ x x (identity x))
     ×
     (∏ (x y z : C)
        (f : x --> y)
        (g : y --> z),
       F₁ x y f ∙ F₁ y z g ⟹ F₁ x z (f · g)).

Definition make_indexed_cat_data
           {C : category}
           (F₀ : C → univalent_category)
           (F₁ : ∏ (x y : C), x --> y → F₀ x ⟶ F₀ y)
           (Fid : ∏ (x : C), functor_identity _ ⟹ F₁ x x (identity x))
           (Fcomp : ∏ (x y z : C)
                      (f : x --> y)
                      (g : y --> z),
                    F₁ x y f ∙ F₁ y z g ⟹ F₁ x z (f · g))
  : indexed_cat_data C
  := F₀ ,, F₁ ,, Fid ,, Fcomp.

Definition indexed_cat_on_ob
           {C : category}
           (F : indexed_cat_data C)
           (x : C)
  : univalent_category
  := pr1 F x.

Coercion indexed_cat_on_ob : indexed_cat_data >-> Funclass.

Definition indexed_cat_on_mor
           {C : category}
           (F : indexed_cat_data C)
           {x y : C}
           (f : x --> y)
  : F x ⟶ F y
  := pr12 F x y f.

Notation "F $ f" := (indexed_cat_on_mor F f) (at level 60).

Definition indexed_cat_id
           {C : category}
           (F : indexed_cat_data C)
           (x : C)
  : functor_identity _ ⟹ (F $ identity x)
  := pr122 F x.

Definition indexed_cat_comp
           {C : category}
           (F : indexed_cat_data C)
           {x y z : C}
           (f : x --> y)
           (g : y --> z)
  : (F $ f) ∙ (F $ g) ⟹ (F $ (f · g))
  := pr222 F x y z f g.

Definition indexed_cat_isos
           {C : category}
           (F : indexed_cat_data C)
  : UU
  := (∏ (x : C) (xx : F x),
      is_z_isomorphism (indexed_cat_id F x xx))
     ×
     (∏ (x y z : C)
        (f : x --> y)
        (g : y --> z)
        (xx : F x),
      is_z_isomorphism (indexed_cat_comp F f g xx)).

(**
 2. The laws of indexed categories
 *)
Definition indexed_cat_laws
           {C : category}
           (F : indexed_cat_data C)
  : UU
  := (∏ (x y : C)
        (f : x --> y)
        (xx : F x),
      identity ((F $ f) xx)
      =
      # (F $ f) (indexed_cat_id F x xx)
      · indexed_cat_comp F (identity x) f xx
      · idtoiso (maponpaths (λ g, (F $ g) xx) (id_left f)))
     ×
     (∏ (x y : C)
        (f : x --> y)
        (xx : F x),
      identity ((F $ f) xx)
      =
      indexed_cat_id F y ((F $ f) xx)
      · indexed_cat_comp F f (identity y) xx
      · idtoiso (maponpaths (λ g, (F $ g) xx) (id_right f)))
     ×
     (∏ (w x y z : C)
        (f : w --> x)
        (g : x --> y)
        (h : y --> z)
        (ww : F w),
      indexed_cat_comp F g h ((F $ f) ww)
      · indexed_cat_comp F f (g · h) ww
      · idtoiso (maponpaths (λ k, (F $ k) ww) (assoc f g h))
      =
      # (F $ h) (indexed_cat_comp F f g ww)
      · indexed_cat_comp F (f · g) h ww).

(**
 3. Indexed categories
 *)
Definition indexed_cat
           (C : category)
  : UU
  := ∑ (F : indexed_cat_data C),
     indexed_cat_isos F
     ×
     indexed_cat_laws F.

Definition make_indexed_cat
           {C : category}
           (F : indexed_cat_data C)
           (HF₁ : indexed_cat_isos F)
           (HF₂ : indexed_cat_laws F)
  : indexed_cat C
  := F ,, HF₁ ,, HF₂.

Coercion indexed_cat_to_data
         {C : category}
         (F : indexed_cat C)
  : indexed_cat_data C
  := pr1 F.

Section IndexedCatLaws.
  Context {C : category}
          (Φ : indexed_cat C).

  Definition is_z_isomorphism_indexed_cat_id
             {x : C}
             (xx : Φ x)
    : is_z_isomorphism (indexed_cat_id Φ x xx).
  Proof.
    exact (pr112 Φ x xx).
  Defined.

  Definition is_z_isomorphism_indexed_cat_comp
             {x y z : C}
             (f : x --> y)
             (g : y --> z)
             (xx : Φ x)
    : is_z_isomorphism (indexed_cat_comp Φ f g xx).
  Proof.
    exact (pr212 Φ x y z f g xx).
  Defined.

  Proposition indexed_cat_lunitor
              {x y : C}
              (f : x --> y)
              (xx : Φ x)
    : identity ((Φ $ f) xx)
      =
      # (Φ $ f) (indexed_cat_id Φ x xx)
      · indexed_cat_comp Φ (identity x) f xx
      · idtoiso (maponpaths (λ g, (Φ $ g) xx) (id_left f)).
  Proof.
    exact (pr122 Φ x y f xx).
  Qed.

  Proposition indexed_cat_runitor
              {x y : C}
              (f : x --> y)
              (xx : Φ x)
    : identity ((Φ $ f) xx)
      =
      indexed_cat_id Φ y ((Φ $ f) xx)
      · indexed_cat_comp Φ f (identity y) xx
      · idtoiso (maponpaths (λ g, (Φ $ g) xx) (id_right f)).
  Proof.
    exact (pr1 (pr222 Φ) x y f xx).
  Qed.

  Proposition indexed_cat_lassociator
              {w x y z : C}
              (f : w --> x)
              (g : x --> y)
              (h : y --> z)
              (ww : Φ w)
    : indexed_cat_comp Φ g h ((Φ $ f) ww)
      · indexed_cat_comp Φ f (g · h) ww
      · idtoiso (maponpaths (λ k, (Φ $ k) ww) (assoc f g h))
      =
      # (Φ $ h) (indexed_cat_comp Φ f g ww)
      · indexed_cat_comp Φ (f · g) h ww.
  Proof.
    exact (pr2 (pr222 Φ) w x y z f g h ww).
  Qed.
End IndexedCatLaws.
