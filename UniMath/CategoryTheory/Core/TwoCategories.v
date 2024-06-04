(******************************************************************************************

 2-categories

 In this file, we define 2-categories. The notion of 2-category is based on the notion of
 a category enriched in the monoidal category of setcategories. Concretely, a 2-category
 consists of a category together with 2-cells together with the appropriate composition
 and unitality operations. This definition also suggests how to define 2-setcategories and
 univalent 2-categories. The former is given by a setcategory enriched in setcategories,
 whereas the latter is given by a univalent category enriched in setcategories.

 We also define locally univalent 2-categories. This might seem strange at first, but, in
 certain contexts, it makes sense. The perspective to take here is that a 2-category is
 a structure that generalizes categories, categories enriched over posets, and so on.
 Categories enriched over posets gives rise to a locally univalent 2-category.

 Contents
 1. Definition of 2-categories
 2. Accessors for the data
 3. Laws
 4. Projections of the laws
 5. 2-categories
 6. Derived laws
 7. 2-setcategories
 8. Univalent 2-categories
 9. Hom-categories

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Core.Univalence.

Local Open Scope cat.

(** * 1. Definition of 2-categories *)
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

Definition make_two_cat_data
           (C : precategory_data)
           (cellsC : ∏ (x y : C), x --> y → x --> y → UU)
           (id : ∏ (x y : C) (f : x --> y), cellsC _ _ f f)
           (vC : ∏ (x y : C)
                   (f g h : x --> y),
                 cellsC _ _ f g → cellsC _ _ g h → cellsC _ _ f h)
           (lW : ∏ (x y z : C)
                   (f : x --> y)
                   (g1 g2 : y --> z),
                 cellsC _ _ g1 g2 → cellsC _ _ (f · g1) (f · g2))
           (rW : ∏ (x y z : C)
                   (f1 f2 : x --> y)
                   (g : y --> z),
                 cellsC _ _ f1 f2 → cellsC _ _ (f1 · g) (f2 · g))
  : two_cat_data
  := C ,, cellsC ,, id ,, vC ,, lW ,, rW.

#[reversible=no] Coercion precategory_from_two_cat_data (C : two_cat_data)
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

(** * 2. Accessors for the data *)
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
           {x y : C}
           {f g : x --> y}
           (p : f = g)
  : f ==> g.
Proof.
  induction p.
  apply id2.
Defined.

(** 3. Laws *)

(* ----------------------------------------------------------------------------------- *)
(** The numbers in the following laws refer to the list of axioms given in ncatlab
    (Section "Definition / Details")
    https://ncatlab.org/nlab/show/bicategory#detailedDefn
    version of October 7, 2015 10:35:36                                                *)
(* ----------------------------------------------------------------------------------- *)

Definition two_cat_category
  : UU
  := ∑ (C : two_cat_data), is_precategory C × has_homsets C.

Definition make_two_cat_category
           (C : two_cat_data)
           (HC₁ : is_precategory C)
           (HC₂ : has_homsets C)
  : two_cat_category
  := C ,, HC₁ ,, HC₂.

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
       (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
        (identity a ◃ x) • idto2mor (id_left g) = idto2mor (id_left f) • x)
     × (** 8 naturality of right whiskering *)
       (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
        (x ▹ identity b) • idto2mor (id_right g) = idto2mor (id_right f) • x)
     × (** 9 left whisker of left whisker *)
       (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h i : C⟦c, d⟧) (x : h ==> i),
        (f ◃ (g ◃ x)) • idto2mor (assoc f g i) = idto2mor (assoc f g h) • (f · g ◃ x))
     × (** 10 right whisker of left whisker *)
       (∏ (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : C⟦c, d⟧) (x : g ==> h),
        (f ◃ (x ▹ i) • idto2mor (assoc f h i) = idto2mor (assoc f g i) • ((f ◃ x) ▹ i)))
     × (** 11 right whisker of right whisker *)
       (∏ (a b c d : C) (f g : C⟦a, b⟧) (h : C⟦b, c⟧) (i : C⟦c, d⟧) (x : f ==> g),
        idto2mor (assoc f h i) • (x ▹ h ▹ i) = (x ▹ h · i) • idto2mor (assoc g h i)).

Definition two_precat : UU := ∑ C : two_cat_category, two_cat_laws C.

Definition make_two_precat
           (C : two_cat_category)
           (HC : two_cat_laws C)
  : two_precat
  := C ,, HC.

#[reversible=no] Coercion two_cat_category_from_two_cat (C : two_precat)
  : two_cat_category
  := pr1 C.
#[reversible=no] Coercion two_cat_laws_from_two_cat (C : two_precat)
  : two_cat_laws C
  := pr2 C.

(** * 4. Projections of the laws *)
Definition two_cat_lunitor
           {C : two_precat}
           {x y : C}
           (f : x --> y)
  : identity _ · f ==> f
  := idto2mor (id_left f).

Definition two_cat_linvunitor
           {C : two_precat}
           {x y : C}
           (f : x --> y)
  : f ==> identity _ · f
  := idto2mor (!(id_left f)).

Definition two_cat_runitor
           {C : two_precat}
           {x y : C}
           (f : x --> y)
  : f · identity _ ==> f
  := idto2mor (id_right f).

Definition two_cat_rinvunitor
           {C : two_precat}
           {x y : C}
           (f : x --> y)
  : f ==> f · identity _
  := idto2mor (!(id_right f)).

Definition two_cat_lassociator
           {C : two_precat}
           {w x y z : C}
           (f : w --> x)
           (g : x --> y)
           (h : y --> z)
  : f · (g · h) ==> (f · g) · h
  := idto2mor (assoc f g h).

Definition two_cat_rassociator
           {C : two_precat}
           {w x y z : C}
           (f : w --> x)
           (g : x --> y)
           (h : y --> z)
  : (f · g) · h ==> f · (g · h)
  := idto2mor (!(assoc f g h)).

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

Definition vassocl {a b : C} {f g h k : C⟦a, b⟧}
           (x : f ==> g) (y : g ==> h) (z : h ==> k)
  : (x • y) • z = x • (y • z)
  := !(vassocr _ _ _).

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

(** 7 vcomp_lunitor *)
Definition vcomp_lunitor {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : (identity a ◃ x) • two_cat_lunitor g = two_cat_lunitor f • x
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ _ _ x.

(** 8 vcomp_runitor *)
Definition vcomp_runitor {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : (x ▹ identity b) • two_cat_runitor g = two_cat_runitor f • x
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))) _ _ _ _ x.

(** 9 lwhisker_lwhisker *)
Definition lwhisker_lwhisker {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) {h i : C⟦c, d⟧} (x : h ==> i)
  : (f ◃ (g ◃ x)) • two_cat_lassociator f g i = two_cat_lassociator f g h • (f · g ◃ x)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))) _ _ _ _ _ _ _ _ x.

(** 10 rwhisker_lwhisker *)
Definition rwhisker_lwhisker {a b c d : C} (f : C⟦a, b⟧) {g h : C⟦b, c⟧} (i : C⟦c, d⟧) (x : g ==> h)
  : (f ◃ (x ▹ i) • two_cat_lassociator f h i = two_cat_lassociator f g i • ((f ◃ x) ▹ i))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))) _ _ _ _ _ _ _ _ x.

(** 11 rwhisker_rwhisker *)
Definition rwhisker_rwhisker {a b c d : C} {f g : C⟦a, b⟧} (h : C⟦b, c⟧) (i : C⟦c, d⟧) (x : f ==> g)
  : two_cat_lassociator f h i • (x ▹ h ▹ i) = (x ▹ h · i) • two_cat_lassociator g h i
  := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))) _ _ _ _ _ _ _ _ x.
End two_cat_law_projections.

(** * 5. 2-categories *)
Definition isaset_cells (C : two_precat) : UU
  := ∏ (a b : C) (f g : a --> b), isaset (f ==> g).

Definition two_cat : UU
  := ∑ C : two_precat, isaset_cells C.

Definition make_two_cat
           (C : two_precat)
           (HC : isaset_cells C)
  : two_cat
  := C ,, HC.

#[reversible=no] Coercion two_cat_to_two_precat
         (C : two_cat)
  : two_precat
  := pr1 C.

Proposition isaset_two_cat_cells
            {C : two_cat}
            {a b : C}
            (f g : a --> b)
  : isaset (f ==> g).
Proof.
  apply (pr2 C).
Defined.

Definition isaprop_two_cat_laws
           (C : two_cat)
  : isaprop (two_cat_laws C).
Proof.
  unfold two_cat_laws.
  repeat (apply isapropdirprod)
  ; repeat (use impred ; intro)
  ; apply C.
Qed.

(** * 6. Derived laws *)
Section IdTo2MorLaws.
  Context {C : two_precat}.

  Definition idto2mor_id
             {x y : C}
             {f : x --> y}
             (p : f = f)
    : idto2mor p = id2 _.
  Proof.
    assert (p = idpath _) as r.
    {
      apply homset_property.
    }
    rewrite r.
    apply idpath.
  Qed.

  Definition idto2mor_comp
             {x y : C}
             {f g h : x --> y}
             (p : f = g)
             (q : g = h)
    : idto2mor p • idto2mor q = idto2mor (p @ q).
  Proof.
    induction p, q ; cbn.
    apply id2_left.
  Qed.

  Definition idto2mor_lwhisker
             {x y z : C}
             (f : x --> y)
             {g h : y --> z}
             (p : g = h)
    : f ◃ idto2mor p
      =
      idto2mor (maponpaths (λ q, f · q) p).
  Proof.
    induction p ; cbn.
    apply lwhisker_id2.
  Qed.

  Definition idto2mor_rwhisker
             {x y z : C}
             {f g : x --> y}
             (h : y --> z)
             (p : f = g)
    : idto2mor p ▹ h
      =
      idto2mor (maponpaths (λ q, q · h) p).
  Proof.
    induction p ; cbn.
    apply id2_rwhisker.
  Qed.

  Definition two_cat_lunitor_linvunitor
             {x y : C}
             (f : x --> y)
    : two_cat_lunitor f • two_cat_linvunitor f = id2 _.
  Proof.
    unfold two_cat_lunitor, two_cat_linvunitor.
    rewrite idto2mor_comp.
    rewrite pathsinv0r.
    apply idpath.
  Qed.

  Definition two_cat_linvunitor_lunitor
             {x y : C}
             (f : x --> y)
    : two_cat_linvunitor f • two_cat_lunitor f = id2 _.
  Proof.
    unfold two_cat_lunitor, two_cat_linvunitor.
    rewrite idto2mor_comp.
    rewrite pathsinv0l.
    apply idpath.
  Qed.

  Definition two_cat_runitor_rinvunitor
             {x y : C}
             (f : x --> y)
    : two_cat_runitor f • two_cat_rinvunitor f = id2 _.
  Proof.
    unfold two_cat_runitor, two_cat_rinvunitor.
    rewrite idto2mor_comp.
    rewrite pathsinv0r.
    apply idpath.
  Qed.

  Definition two_cat_rinvunitor_runitor
             {x y : C}
             (f : x --> y)
    : two_cat_rinvunitor f • two_cat_runitor f = id2 _.
  Proof.
    unfold two_cat_runitor, two_cat_rinvunitor.
    rewrite idto2mor_comp.
    rewrite pathsinv0l.
    apply idpath.
  Qed.

  Definition two_cat_lassociator_rassociator
             {w x y z : C}
             (f : w --> x)
             (g : x --> y)
             (h : y --> z)
    : two_cat_lassociator f g h • two_cat_rassociator f g h = id2 _.
  Proof.
    unfold two_cat_lassociator, two_cat_rassociator.
    rewrite idto2mor_comp.
    rewrite pathsinv0r.
    apply idpath.
  Qed.

  Definition two_cat_rassociator_lassociator
             {w x y z : C}
             (f : w --> x)
             (g : x --> y)
             (h : y --> z)
    : two_cat_rassociator f g h • two_cat_lassociator f g h = id2 _.
  Proof.
    unfold two_cat_lassociator, two_cat_rassociator.
    rewrite idto2mor_comp.
    rewrite pathsinv0l.
    apply idpath.
  Qed.

  Definition id1_lwhisker {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
    : (identity a ◃ x) = two_cat_lunitor f • x • two_cat_linvunitor g.
  Proof.
    rewrite <- vcomp_lunitor.
    rewrite !vassocl.
    rewrite two_cat_lunitor_linvunitor.
    rewrite id2_right.
    apply idpath.
  Qed.

  Definition rwhisker_id1 {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
    : (x ▹ identity b) = two_cat_runitor f • x • two_cat_rinvunitor g.
  Proof.
    rewrite <- vcomp_runitor.
    rewrite !vassocl.
    rewrite two_cat_runitor_rinvunitor.
    rewrite id2_right.
    apply idpath.
  Qed.

  Definition lwhisker_lwhisker_mor
             {a b c d : C}
             (f : a --> b)
             (g : b --> c)
             {h i : c --> d}
             (τ : h ==> i)
    : f ◃ (g ◃ τ)
      =
      two_cat_lassociator _ _ _
      • (f · g ◃ τ)
      • two_cat_rassociator _ _ _.
  Proof.
    rewrite <- lwhisker_lwhisker.
    rewrite !vassocl.
    rewrite two_cat_lassociator_rassociator.
    rewrite id2_right.
    apply idpath.
  Qed.

  Definition lwhisker_comp_mor
             {a b c d : C}
             (f : a --> b)
             (g : b --> c)
             {h i : c --> d}
             (τ : h ==> i)
    : f · g ◃ τ
      =
      two_cat_rassociator _ _ _
      • (f ◃ (g ◃ τ))
      • two_cat_lassociator _ _ _.
  Proof.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply lwhisker_lwhisker.
    }
    rewrite !vassocr.
    rewrite two_cat_rassociator_lassociator.
    rewrite id2_left.
    apply idpath.
  Qed.

  Definition rwhisker_lwhisker_mor
             {a b c d : C}
             (f : a --> b)
             {g h : b --> c}
             (τ : g ==> h)
             (i : c --> d)
    : f ◃ (τ ▹ i)
      =
      two_cat_lassociator _ _ _
      • ((f ◃ τ) ▹ i)
      • two_cat_rassociator _ _ _.
  Proof.
    rewrite <- rwhisker_lwhisker.
    rewrite !vassocl.
    rewrite two_cat_lassociator_rassociator.
    rewrite id2_right.
    apply idpath.
  Qed.

  Definition lwhisker_rwhisker_mor
             {a b c d : C}
             (f : a --> b)
             {g h : b --> c}
             (τ : g ==> h)
             (i : c --> d)
    : (f ◃ τ) ▹ i
      =
      two_cat_rassociator _ _ _
      • (f ◃ (τ ▹ i))
      • two_cat_lassociator _ _ _.
  Proof.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply rwhisker_lwhisker.
    }
    rewrite !vassocr.
    rewrite two_cat_rassociator_lassociator.
    rewrite id2_left.
    apply idpath.
  Qed.

  Definition rwhisker_rwhisker_mor
             {a b c d : C}
             {f g : a --> b}
             (τ : f ==> g)
             (h : b --> c)
             (i : c --> d)
    : τ ▹ h ▹ i
      =
      two_cat_rassociator _ _ _
      • (τ ▹ h · i)
      • two_cat_lassociator _ _ _.
  Proof.
    rewrite !vassocl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply rwhisker_rwhisker.
    }
    rewrite !vassocr.
    rewrite two_cat_rassociator_lassociator.
    rewrite id2_left.
    apply idpath.
  Qed.

  Definition rwhisker_comp_mor
             {a b c d : C}
             {f g : a --> b}
             (τ : f ==> g)
             (h : b --> c)
             (i : c --> d)
    : τ ▹ h · i
      =
      two_cat_lassociator _ _ _
      • (τ ▹ h ▹ i)
      • two_cat_rassociator _ _ _.
  Proof.
    rewrite rwhisker_rwhisker.
    rewrite !vassocl.
    rewrite two_cat_lassociator_rassociator.
    rewrite id2_right.
    apply idpath.
  Qed.

  Proposition idto2mor_left
              {a b : C}
              {f f' g : a --> b}
              (p p' : f = f')
              {τ τ' : f' ==> g}
              (r : τ = τ')
    : idto2mor p • τ
      =
      idto2mor p' • τ'.
  Proof.
    assert (p = p') as s.
    {
      apply homset_property.
    }
    induction s.
    induction r.
    apply idpath.
  Qed.

  Proposition idto2mor_right
              {a b : C}
              {f g g' : a --> b}
              (p p' : g = g')
              {τ τ' : f ==> g}
              (r : τ = τ')
    : τ • idto2mor p
      =
      τ' • idto2mor p'.
  Proof.
    assert (p = p') as s.
    {
      apply homset_property.
    }
    induction s.
    induction r.
    apply idpath.
  Qed.

  Definition arr_idto2mor_eq
             {a b : C}
             {f f' g g' : a --> b}
             (p p' : f = f')
             {τ τ' : f' ==> g}
             (q q' : g = g')
             (r : τ = τ')
    : idto2mor p • τ • idto2mor q
      =
      idto2mor p' • τ' • idto2mor q'.
  Proof.
    assert (p = p') as s.
    {
      apply homset_property.
    }
    induction s.
    assert (q = q') as s.
    {
      apply homset_property.
    }
    induction s.
    induction r.
    apply idpath.
  Qed.

  Definition arr_idto2mor_eq2
             {a b : C}
             {f f' g g' h h' : a --> b}
             (p p' : f = f')
             {τ τ' : f' ==> g}
             (q q' : g = g')
             {θ θ' : g' ==> h}
             (r r' : h = h')
             (H₁ : τ = τ')
             (H₂ : θ = θ')
    : idto2mor p • τ • idto2mor q • θ • idto2mor r
      =
      idto2mor p' • τ' • idto2mor q' • θ' • idto2mor r'.
  Proof.
    induction H₁, H₂.
    use idto2mor_right.
    apply maponpaths_2.
    use idto2mor_right.
    apply maponpaths_2.
    apply maponpaths.
    apply (homset_property C).
  Qed.

  Definition arr_idto2mor_eq3
             {a b : C}
             {f f' g g' h h' k k' : a --> b}
             (p p' : f = f')
             {τ τ' : f' ==> g}
             (q q' : g = g')
             {θ θ' : g' ==> h}
             (r r' : h = h')
             {ξ ξ' : h' ==> k}
             (s s' : k = k')
             (H₁ : τ = τ')
             (H₂ : θ = θ')
             (H₃ : ξ = ξ')
    : idto2mor p • τ • idto2mor q • θ • idto2mor r • ξ • idto2mor s
      =
      idto2mor p' • τ' • idto2mor q' • θ' • idto2mor r' • ξ' • idto2mor s'.
  Proof.
    induction H₁, H₂, H₃.
    use idto2mor_right.
    apply maponpaths_2.
    use idto2mor_right.
    apply maponpaths_2.
    use idto2mor_right.
    apply maponpaths_2.
    apply maponpaths.
    apply (homset_property C).
  Qed.
End IdTo2MorLaws.

(** * 7. 2-setcategories *)
Definition is_two_setcat
           (C : two_cat)
  : UU
  := isaset C.

Definition two_setcat
  : UU
  := ∑ (C : two_cat), is_two_setcat C.

Definition make_two_setcat
           (C : two_cat)
           (HC : is_two_setcat C)
  : two_setcat
  := C ,, HC.

#[reversible=no] Coercion two_setcat_to_two_cat
         (C : two_setcat)
  : two_cat
  := pr1 C.

Proposition is_two_setcat_two_setcat
            (C : two_setcat)
  : isaset C.
Proof.
  exact (pr2 C).
Qed.

Proposition is_setcategory_two_setcat
            (C : two_setcat)
  : is_setcategory C.
Proof.
  split.
  - exact (is_two_setcat_two_setcat C).
  - apply homset_property.
Qed.

(** * 8. Univalent 2-categories *)
Definition univalent_two_cat
  : UU
  := ∑ (C : two_cat), is_univalent (category_from_two_cat_data C).

Definition make_univalent_two_cat
           (C : two_cat)
           (HC : is_univalent (category_from_two_cat_data C))
  : univalent_two_cat
  := C ,, HC.

#[reversible=no] Coercion univalent_two_cat_to_two_cat
         (C : univalent_two_cat)
  : two_cat
  := pr1 C.

Proposition is_univalent_univalent_two_cat
            (C : univalent_two_cat)
  : is_univalent (category_from_two_cat_data C).
Proof.
  exact (pr2 C).
Qed.

(** * 9. Hom-categories *)
Definition hom_precat_ob_mor
           {C : two_cat}
           (x y : C)
  : precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (x --> y).
  - exact (λ f g, f ==> g).
Defined.

Definition hom_precat_data
           {C : two_cat}
           (x y : C)
  : precategory_data.
Proof.
  use make_precategory_data.
  - exact (hom_precat_ob_mor x y).
  - exact (λ (f : x --> y), id2 f).
  - exact (λ (f g h : x --> y) (τ : f ==> g) (θ : g ==> h), τ • θ).
Defined.

Proposition hom_precat_laws
            {C : two_cat}
            (x y : C)
  : is_precategory (hom_precat_data x y).
Proof.
  use is_precategory_one_assoc_to_two.
  repeat split ; cbn.
  - intros f g τ.
    apply id2_left.
  - intros f g τ.
    apply id2_right.
  - intros f g h k τ₁ τ₂ τ₃.
    apply vassocr.
Qed.

Definition hom_precat
           {C : two_cat}
           (x y : C)
  : precategory.
Proof.
  use make_precategory.
  - exact (hom_precat_data x y).
  - exact (hom_precat_laws x y).
Defined.

Definition hom_cat
           {C : two_cat}
           (x y : C)
  : category.
Proof.
  use make_category.
  - exact (hom_precat x y).
  - abstract
      (intros f g ;
       apply isaset_two_cat_cells).
Defined.

Definition locally_univalent_two_cat
           (C : two_cat)
  : UU
  := ∏ (x y : C), is_univalent (hom_cat x y).

Module Notations.

  Notation "f '==>' g" := (two_cat_cells _ f g) (at level 60).
  Notation "f '<==' g" := (two_cat_cells _ g f) (at level 60, only parsing).
  Notation "x • y" := (vcomp2 x y) (at level 60).
  Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
  Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)
  Notation "x ⋆ y" := (hcomp x y) (at level 50, left associativity).

End Notations.
