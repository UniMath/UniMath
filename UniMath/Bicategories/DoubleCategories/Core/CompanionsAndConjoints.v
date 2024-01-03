(*****************************************************************************************

 Companion pairs and conjoints in double categories

 In this file, we define companion pairs and conjoints in pseudo double categories. Note
 that this file only contains definitions and accessors for them. General properties for
 companion pairs and conjoints are proven for Verity double bicategories instead.

 Contents
 1. Companion pairs
 2. Conjoints

 *****************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.DerivedLaws.TransportLaws.
Require Import UniMath.Bicategories.DoubleCategories.Underlying.HorizontalBicategory.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Companion pairs *)
Definition double_cat_are_companions
           {C : double_cat}
           {x y : C}
           (h : x -->h y)
           (v : x -->v y)
  : UU
  := ∑ (φ : square v (identity_v y) h (identity_h y))
       (ψ : square (identity_v x) v (identity_h x) h),
     (transportf_square
        (id_v_right _)
        (id_v_right _)
        (transportf_square
           (id_v_left _)
           (id_v_left _)
           (linvunitor_h h ⋆v (ψ ⋆h φ))
         ⋆v runitor_h h)
      =
      id_v_square h)
     ×
     (transportf_square
        (idpath _)
        (id_right _)
        (transportf_square
           (id_left _)
           (idpath _)
           (ψ ⋆v φ))
      =
      id_h_square v).

Definition make_double_cat_are_companions
           {C : double_cat}
           {x y : C}
           {h : x -->h y}
           {v : x -->v y}
           (φ : square v (identity_v y) h (identity_h y))
           (ψ : square (identity_v x) v (identity_h x) h)
           (p : transportf_square
                  (id_v_right _)
                  (id_v_right _)
                  (transportf_square
                     (id_v_left _)
                     (id_v_left _)
                     (linvunitor_h h ⋆v (ψ ⋆h φ))
                   ⋆v runitor_h h)
                =
                id_v_square h)
           (q : transportf_square
                  (idpath _)
                  (id_right _)
                  (transportf_square
                     (id_left _)
                     (idpath _)
                     (ψ ⋆v φ))
                =
                id_h_square v)
  : double_cat_are_companions h v
  := φ ,, ψ ,, p ,, q.

Definition make_double_cat_are_companions'
           {C : double_cat}
           {x y : C}
           {h : x -->h y}
           {v : x -->v y}
           (φ : square v (identity_v y) h (identity_h y))
           (ψ : square (identity_v x) v (identity_h x) h)
           (p : transportf_square
                  (id_v_right _ @ id_v_right _)
                  (id_v_right _ @ id_v_right _)
                  ((linvunitor_h h ⋆v (ψ ⋆h φ)) ⋆v runitor_h h)
                =
                id_v_square h)
           (q : transportf_square
                  (id_left _)
                  (id_right _)
                  (ψ ⋆v φ)
                =
                id_h_square v)
  : double_cat_are_companions h v.
Proof.
  refine (φ ,, ψ ,, _ ,, _).
  - abstract
      (rewrite transportf_square_prewhisker ;
       rewrite transportf_f_square ;
       refine (_ @ p) ;
       use transportf_square_eq ;
       apply idpath).
  - abstract
      (refine (_ @ q) ;
       rewrite transportf_f_square ;
       use transportf_square_eq ;
       apply idpath).
Defined.

Definition unit_double_cat_are_companions
           {C : double_cat}
           {x y : C}
           {h : x -->h y}
           {v : x -->v y}
           (c : double_cat_are_companions h v)
  : square v (identity_v y) h (identity_h y)
  := pr1 c.

Definition counit_double_cat_are_companions
           {C : double_cat}
           {x y : C}
           {h : x -->h y}
           {v : x -->v y}
           (c : double_cat_are_companions h v)
  : square (identity_v x) v (identity_h x) h
  := pr12 c.

Proposition double_cat_are_companions_left
            {C : double_cat}
            {x y : C}
            {h : x -->h y}
            {v : x -->v y}
            (c : double_cat_are_companions h v)
  : transportf_square
      (id_v_right _)
      (id_v_right _)
      (transportf_square
         (id_v_left _)
         (id_v_left _)
         (linvunitor_h h
          ⋆v
          (counit_double_cat_are_companions c
           ⋆h
           unit_double_cat_are_companions c))
       ⋆v runitor_h h)
    =
    id_v_square h.
Proof.
  exact (pr122 c).
Defined.

Proposition double_cat_are_companions_right
            {C : double_cat}
            {x y : C}
            {h : x -->h y}
            {v : x -->v y}
            (c : double_cat_are_companions h v)
  : transportf_square
      (idpath _)
      (id_right _)
      (transportf_square
         (id_left _)
         (idpath _)
         (counit_double_cat_are_companions c
          ⋆v
          unit_double_cat_are_companions c))
    =
    id_h_square v.
Proof.
  exact (pr222 c).
Defined.

Definition all_companions_double_cat
           (C : double_cat)
  : UU
  := ∏ (x y : C)
       (v : x -->v y),
     ∑ (h : x -->h y), double_cat_are_companions h v.

(** * 2. Conjoints *)
Definition double_cat_are_conjoints
           {C : double_cat}
           {x y : C}
           (h : y -->h x)
           (v : x -->v y)
  : UU
  := ∑ (η : square v (identity_v x) (identity_h x) h)
       (ε : square (identity_v y) v h (identity_h y)),
     (transportf_square
        (id_v_left _)
        (id_v_left _)
        (rinvunitor_h h
         ⋆v transportf_square
              (id_v_right _)
              (id_v_right _)
              ((ε ⋆h η) ⋆v lunitor_h h))
      =
      id_v_square h)
     ×
     (transportf_square
        (idpath _)
        (id_v_left _)
        (transportf_square
           (id_v_right _)
           (idpath _)
           (η ⋆v ε))
      =
      id_h_square v).

Definition make_double_cat_are_conjoints
           {C : double_cat}
           {x y : C}
           {h : y -->h x}
           {v : x -->v y}
           (η : square v (identity_v x) (identity_h x) h)
           (ε : square (identity_v y) v h (identity_h y))
           (p : transportf_square
                  (id_v_left _)
                  (id_v_left _)
                  (rinvunitor_h h
                   ⋆v transportf_square
                        (id_v_right _)
                        (id_v_right _)
                        ((ε ⋆h η) ⋆v lunitor_h h))
                =
                id_v_square h)
           (q : transportf_square
                  (idpath _)
                  (id_v_left _)
                  (transportf_square
                     (id_v_right _)
                     (idpath _)
                     (η ⋆v ε))
                =
                id_h_square v)
  : double_cat_are_conjoints h v
  := η ,, ε ,, p ,, q.

Definition make_double_cat_are_conjoints'
           {C : double_cat}
           {x y : C}
           {h : y -->h x}
           {v : x -->v y}
           (η : square v (identity_v x) (identity_h x) h)
           (ε : square (identity_v y) v h (identity_h y))
           (p : transportf_square
                  (id_v_left _ @ id_v_left _)
                  (id_v_left _ @ id_v_left _)
                  (rinvunitor_h h ⋆v ((ε ⋆h η) ⋆v lunitor_h h))
                =
                id_v_square h)
           (q : transportf_square
                  (id_v_right _)
                  (id_v_left _)
                  (η ⋆v ε)
                =
                id_h_square v)
  : double_cat_are_conjoints h v.
Proof.
  refine (η ,, ε ,, _ ,, _).
  - abstract
      (rewrite transportf_square_postwhisker ;
       rewrite transportf_f_square ;
       refine (_ @ p) ;
       use transportf_square_eq ;
       apply idpath).
  - abstract
      (rewrite transportf_f_square ;
       refine (_ @ q) ;
       use transportf_square_eq ;
       apply idpath).
Defined.

Definition unit_double_cat_are_conjoints
           {C : double_cat}
           {x y : C}
           {h : y -->h x}
           {v : x -->v y}
           (c : double_cat_are_conjoints h v)
  : square v (identity_v x) (identity_h x) h
  := pr1 c.

Definition counit_double_cat_are_conjoints
           {C : double_cat}
           {x y : C}
           {h : y -->h x}
           {v : x -->v y}
           (c : double_cat_are_conjoints h v)
  : square (identity_v y) v h (identity_h y)
  := pr12 c.

Proposition double_cat_are_conjoints_left
            {C : double_cat}
            {x y : C}
            {h : y -->h x}
            {v : x -->v y}
            (c : double_cat_are_conjoints h v)
  : transportf_square
      (id_v_left _)
      (id_v_left _)
      (rinvunitor_h h
       ⋆v transportf_square
            (id_v_right _)
            (id_v_right _)
            ((counit_double_cat_are_conjoints c
              ⋆h
              unit_double_cat_are_conjoints c)
             ⋆v lunitor_h h))
    =
    id_v_square h.
Proof.
  exact (pr122 c).
Defined.

Proposition double_cat_are_conjoints_right
            {C : double_cat}
            {x y : C}
            {h : y -->h x}
            {v : x -->v y}
            (c : double_cat_are_conjoints h v)
  : transportf_square
      (idpath _)
      (id_v_left _)
      (transportf_square
         (id_v_right _)
         (idpath _)
         (unit_double_cat_are_conjoints c
          ⋆v
          counit_double_cat_are_conjoints c))
    =
    id_h_square v.
Proof.
  exact (pr222 c).
Defined.

Definition all_conjoints_double_cat
           (C : double_cat)
  : UU
  := ∏ (x y : C)
       (v : x -->v y),
     ∑ (h : y -->h x), double_cat_are_conjoints h v.
