(* ******************************************************************************* *)
(** * 2-categories
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

(*
change the category to data and add the category laws to two_cat_laws (including that the 2-cells are a set)
there should be a coercion from 2-category data to category data
 *)

Definition two_cat_data
  : UU
  := ∑ (C : precategory_data)
       (cells_C : ∏ (x y : C), x --> y → x --> y → UU),
     (∏ (x y : C) (f : x --> y), cells_C _ _ f f)
     × (∏ (x y : C) (f g h : x --> y),
        cells_C _ _ f g → cells_C _ _ g h → cells_C _ _ f h)
     × (∏ (x y z : C)
          (f : x --> y)
          (g1 g2 : y --> z),
        cells_C _ _ g1 g2 → cells_C _ _ (f · g1) (f · g2))
     × (∏ (x y z : C)
          (f1 f2 : x --> y)
          (g : y --> z),
        cells_C _ _ f1 f2 → cells_C _ _ (f1 · g) (f2 · g)).

Coercion precategory_from_two_cat_data (C : two_cat_data)
  : precategory_data
  := pr1 C.

Definition two_cat_cells
           (C : two_cat_data)
           {a b : C}
           (f g : C⟦a, b⟧)
  : UU
  := pr12 C a b f g.

Local Notation "f '==>' g" := (two_cat_cells _ f g) (at level 60).
Local Notation "f '<==' g" := (two_cat_cells _ g f) (at level 60, only parsing).

(* ----------------------------------------------------------------------------------- *)
(** Data projections.                                                                  *)
(* ----------------------------------------------------------------------------------- *)

Definition id2 {C : two_cat_data} {a b : C} (f : C⟦a, b⟧) : f ==> f
  := pr122 C a b f.

Definition vcomp2 {C : two_cat_data} {a b : C} {f g h : C⟦a, b⟧}
  : f ==> g → g ==> h → f ==> h
  := λ x y, pr1 (pr222 C) _ _ _ _ _ x y.

Definition lwhisker {C : two_cat_data} {a b c : C} (f : C⟦a, b⟧) {g1 g2 : C⟦b, c⟧}
  : g1 ==> g2 → f · g1 ==> f · g2
  := λ x, pr12 (pr222 C) _ _ _ _ _ _ x.

Definition rwhisker {C : two_cat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} (g : C⟦b, c⟧)
  : f1 ==> f2 → f1 · g ==> f2 · g
  := λ x, pr22 (pr222 C) _ _ _ _ _ _ x.

Local Notation "x • y" := (vcomp2 x y) (at level 60).
Local Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
Local Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)

Definition hcomp {C : two_cat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2
  := λ x y, (x ▹ g1) • (f2 ◃ y).

Definition hcomp' {C : two_cat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2
  := λ x y, (f1 ◃ y) • (x ▹ g2).

Local Notation "x ⋆ y" := (hcomp x y) (at level 50, left associativity).

Definition idto2mor
           {C : two_cat_data}
           {x y : pr1 C}
           {f g : x --> y}
           (p : f = g)
  : f ==> g.
Proof.
  induction p.
  apply id2.
Defined.

Check is_precategory.

(* ----------------------------------------------------------------------------------- *)
(** ** Laws                                                                            *)
(* ----------------------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------------------- *)
(** The numbers in the following laws refer to the list of axioms given in ncatlab
    (Section "Definition / Details")
    https://ncatlab.org/nlab/show/bicategory#detailedDefn
    version of October 7, 2015 10:35:36                                                *)
(* ----------------------------------------------------------------------------------- *)

Definition two_cat_category
  : UU
  := ∑ (C : two_cat_data), is_precategory C × has_homsets C.

Definition category_from_two_cat_data (C : two_cat_category)
  : category.
Proof.
  use make_category.
  - use make_precategory.
    + apply (pr1 C).
    + exact (pr12 C).
  - exact (pr22 C).
Defined.

Coercion category_from_two_cat_data : two_cat_category >-> category.

Definition two_cat_laws (C : two_cat_category)
  : UU
  :=   (** 1a id2_left *)
       (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), id2 f • x = x)
     × (** 1b id2_right *)
       (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), x • id2 g = x)
     × (** 2 vassocr *)
       (∏ (a b : C) (f g h k : C⟦a, b⟧) (x : f ==> g) (y : g ==> h) (z : h ==> k),
        x • (y • z) = (x • y) • z)
     × (** 3a lwhisker_id2 *)
       (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), f ◃ id2 g = id2 _)
     × (** 3b id2_rwhisker *)
       (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), id2 f ▹ g = id2 _)
     × (** 4 lwhisker_vcomp *)
       (∏ (a b c : C) (f : C⟦a, b⟧) (g h i : C⟦b, c⟧) (x : g ==> h) (y : h ==> i),
        (f ◃ x) • (f ◃ y) = f ◃ (x • y))
     × (** 5 rwhisker_vcomp *)
       (∏ (a b c : C) (f g h : C⟦a, b⟧) (i : C⟦b, c⟧) (x : f ==> g) (y : g ==> h),
        (x ▹ i) • (y ▹ i) = (x • y) ▹ i)
     × (** 6 vcomp_whisker *)
       (∏ (a b c : C) (f g : C⟦a, b⟧) (h i : C⟦b, c⟧) (x : f ==> g) (y : h ==> i),
        (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i))
     × (** 7 naturality of left whiskering *)
       (∏ (a b :  C) (f g : C⟦a, b⟧) (x : f ==> g),
        (identity a ◃ x) • idto2mor (id_left g) = idto2mor (id_left f) • x).

(*
law 6 in ncatlab
also laws 9-11
*)

Definition two_precat : UU := ∑ C : two_cat_category, two_cat_laws C.

Coercion two_cat_category_from_two_cat (C : two_precat) : two_cat_category := pr1 C.
Coercion two_cat_laws_from_two_cat (C : two_precat) : two_cat_laws C := pr2 C.

(* ----------------------------------------------------------------------------------- *)
(** Laws projections.                                                                  *)
(* ----------------------------------------------------------------------------------- *)

Section two_cat_law_projections.

Context {C : two_precat}.

(** 1a id2_left *)
Definition id2_left {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : id2 f • x = x
  := pr1 (pr2 C) _ _ _ _ x.

(** 1b id2_right *)
Definition id2_right {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : x • id2 g = x
  := pr1 (pr2 (pr2 C)) _ _ _ _ x.

(** 2 vassocr *)
Definition vassocr {a b : C} {f g h k : C⟦a, b⟧}
           (x : f ==> g) (y : g ==> h) (z : h ==> k)
  : x • (y • z) = (x • y) • z
  := pr1 (pr2 (pr2 (pr2 C))) _ _ _ _ _ _ x y z.

(** 3a lwhisker_id2 *)
Definition lwhisker_id2 {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : f ◃ id2 g = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 C)))) _ _ _ f g.

(** 3b id2_rwhisker *)
Definition id2_rwhisker {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : id2 f ▹ g = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C))))) _ _ _ f g.

(** 4 lwhisker_vcomp *)
Definition lwhisker_vcomp {a b c : C} (f : C⟦a, b⟧) {g h i : C⟦b, c⟧}
           (x : g ==> h) (y : h ==> i)
  : (f ◃ x) • (f ◃ y) = f ◃ (x • y)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))) _ _ _ f _ _ _ x y.

(** 5 rwhisker_vcomp *)
Definition rwhisker_vcomp {a b c : C} {f g h : C⟦a, b⟧}
           (i : C⟦b, c⟧) (x : f ==> g) (y : g ==> h)
  : (x ▹ i) • (y ▹ i) = (x • y) ▹ i
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))) _ _ _ _ _ _ i x y.


(** 6 vcomp_whisker *)
Definition vcomp_whisker {a b c : C} {f g : C⟦a, b⟧} {h i : C⟦b, c⟧}
           (x : f ==> g) (y : h ==> i)
  : (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))) _ _ _ _ _ _ i x y.
End two_cat_law_projections.

(* ----------------------------------------------------------------------------------- *)
(** ** Bicategories                                                                    *)
(* ----------------------------------------------------------------------------------- *)

Definition isaset_cells (C : two_precat) : UU
  := ∏ (a b : C) (f g : a --> b), isaset (f ==> g).

Definition two_cat : UU
  := ∑ C : two_precat, isaset_cells C.
