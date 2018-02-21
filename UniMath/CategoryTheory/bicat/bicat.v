Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.


Open Scope cat.


(** * Definition of bicategory *)

Definition prebicat_cell_struct (C : precategory_ob_mor) : UU :=
  ∏ (a b: C), C⟦a, b⟧ → C⟦a, b⟧ → UU.

Definition prebicat_1_id_comp_cells : UU := ∑ (C : precategory_data), prebicat_cell_struct C.
Coercion precat_data_from_prebicat_1_id_comp_cells (C : prebicat_1_id_comp_cells)
  : precategory_data
  := pr1 C.

Definition prebicat_cells (C : prebicat_1_id_comp_cells) {a b : C} (f g : C⟦a, b⟧) : UU :=
  pr2 C a b f g.

Notation "f '==>' g" := (prebicat_cells _ f g) (at level 60).
Notation "f '<==' g" := (prebicat_cells _ g f) (at level 60, only parsing).

Definition prebicat_2_id_comp_struct (C : prebicat_1_id_comp_cells) : UU
  :=
    (* 2-unit *)
    (∏ (a b : C) (f : C⟦a, b⟧), f ==> f)
      ×
    (* left unitor *)
    (∏ (a b : C) (f : C⟦a, b⟧), identity _ · f ==> f)
      ×
    (* right unitor *)
    (∏ (a b : C) (f : C⟦a, b⟧), f · identity _  ==> f)
      ×
    (* left inverse unitor *)
    (∏ (a b : C) (f : C⟦a, b⟧), identity _ · f <== f)
      ×
    (* right inverse unitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), f · identity _  <== f)
      ×
    (* right associator *)
    (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
     (f · g) · h ==> f · (g · h))
          ×
    (* left associator *)
    (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
       f · (g · h) ==> (f · g) · h)
      ×
    (* vertical composition *)
    (∏ (a b : C) (f g h : C⟦a, b⟧), f ==> g -> g ==> h -> f ==> h)
    ×
    (* left whiskering *)
    (∏ (a b c : C) (f : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧),
     g1 ==> g2 → f · g1 ==> f · g2)
    ×
    (* right whiskering *)
    (∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g : C⟦b, c⟧),
     f1 ==> f2 → f1 · g ==> f2 · g).



Definition prebicat_data : UU := ∑ C, prebicat_2_id_comp_struct C.

Coercion prebicat_cells_1_id_comp_from_prebicat_data (C : prebicat_data) : prebicat_1_id_comp_cells
  := pr1 C.

Definition id2 {C : prebicat_data} {a b : C} (f : C⟦a, b⟧) : f ==> f
  := pr1 (pr2 C) a b f.
Check (λ (C : prebicat_data) , pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (C))))))) ))).


Definition lunitor {C : prebicat_data} {a b : C} (f : C⟦a, b⟧)
  : identity _ · f ==> f
  := pr1 (pr2 (pr2 C)) a b f.

Definition runitor {C : prebicat_data} {a b : C} (f : C⟦a, b⟧)
  : f · identity _ ==> f
  := pr1 (pr2 (pr2 (pr2 C))) a b f.

Definition linvunitor {C : prebicat_data} {a b : C} (f : C⟦a, b⟧)
  : identity _ · f <== f
  := pr1 (pr2 (pr2 (pr2 (pr2 C)))) a b f.

Definition rinvunitor {C : prebicat_data} {a b : C} (f : C⟦a, b⟧)
  : f · identity _ <== f
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C))))) a b f.

Definition rassociator {C : prebicat_data} {a b c d : C}
           (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
  : (f · g) · h ==> f · (g · h)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))) a b c d f g h.

Definition lassociator {C : prebicat_data} {a b c d : C}
           (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
  : f · (g · h) ==> (f · g) · h
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))) a b c d f g h.

Definition vcomp2 {C : prebicat_data} {a b : C} {f g h: C⟦a, b⟧}
  : f ==> g → g ==> h → f ==> h
  := λ x y, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))) _ _ _ _ _  x y.

Definition lwhisker {C : prebicat_data} {a b c : C} (f : C⟦a, b⟧) {g1 g2 : C⟦b, c⟧}
  : g1 ==> g2 → f · g1 ==> f · g2
  := λ x, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ _ _ _ _ x.

Definition rwhisker {C : prebicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} (g : C⟦b, c⟧)
  : f1 ==> f2 → f1 · g ==> f2 · g
  := λ x, pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ _ _ _ _ x.


Notation "x • y" := (vcomp2 x y) (at level 60).
Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)

Definition hcomp {C : prebicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2.
Proof.
  intros x y.
  set (xg1 := x ▹ g1).
  set (f2y := f2 ◃ y).
  exact (xg1 • f2y).
Defined.

Definition hcomp' {C : prebicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2.
Proof.
  intros x y.
  set (f1y := f1 ◃ y).
  set (xg2 := x ▹ g2).
  exact (f1y • xg2).
Defined.

Notation "x ⋆ y" := (hcomp x y) (at level 50).

Definition prebicat_laws (C : prebicat_data) : UU
  :=  (* 1a id2_left *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), id2 f • x = x)
        ×
      (* 1b id2_right *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), x • id2 g = x)
      ×
      (* 2 vassocr *)
      (∏ (a b : C) (f g h k : C⟦a, b⟧) (x : f ==> g) (y : g ==> h) (z : h ==> k),
       x • (y • z) = (x • y) • z)
      ×
      (* 3a lwhisker_id2 *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), f ◃ id2 g = id2 _ )
      ×
      (* 3b id2_rwhisker *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), id2 f ▹ g = id2 _ )
      ×
      (* 4 lwhisker_vcomp *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g h i : C⟦b, c⟧) (x : g ==> h) (y : h ==> i),
       (f ◃ x) • (f ◃ y) = f ◃ (x • y))
      ×
      (* 5 rwhisker_vcomp *)
      (∏ (a b c : C) (f g h : C⟦a, b⟧) (i : C⟦b, c⟧) (x : f ==> g) (y : g ==> h),
       (x ▹ i) • (y ▹ i) = (x • y) ▹ i)
      ×
      (* 6  vcomp_lunitor *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
       (identity _ ◃ x) • lunitor g = lunitor f • x )
      ×
      (* 7 vcomp_runitor *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
       (x ▹ identity _ ) • runitor g = runitor f • x )
      ×
      (* 8 lwhisker_lwhisker *)
      (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h i : c --> d) (x : h ==> i),
       f ◃ (g ◃ x) • lassociator _ _ _ = lassociator _ _ _ • (f · g ◃ x))
      ×
      (* 9 rwhisker_lwhisker *)
      (∏ (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : c --> d) (x : g ==> h),
       (f ◃ (x ▹ i)) • lassociator _ _ _ = lassociator _ _ _ • ((f ◃ x) ▹ i))
      ×
      (* 10 rwhisker_rwhisker *)
      (∏ (a b c d : C) (f g : C⟦a, b⟧) (h : C⟦b, c⟧) (i : c --> d) (x : f ==> g),
       lassociator _ _ _ • ((x ▹ h) ▹ i) = (x ▹ h · i) • lassociator _ _ _ )
      ×
      (* 11 vcomp_whisker *)
      (∏ (a b c : C) (f g : C⟦a, b⟧) (h i : C⟦b, c⟧) (x : f ==> g) (y : h ==> i),
       (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i))
      ×
      (* 12a lunitor_linvunitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), lunitor f • linvunitor _ = id2 _ )
      ×
      (* 12b linvunitor_lunitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), linvunitor f • lunitor _ = id2 _ )
      ×
      (* 13a runitor_rinvunitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), runitor f • rinvunitor _ = id2 _ )
      ×
      (* 13b rinvunitor_runitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), rinvunitor f • runitor _ = id2 _ )
      ×
      (* 14a lassociator_rassociator *)
      (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d),
       lassociator f g h • rassociator _ _ _ = id2 _ )
      ×
      (* 14b rassociator_lassociator *)
      (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d),
       rassociator f g h • lassociator _ _ _ = id2 _ )
      ×
      (* 15 runitor_rwhisker *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧),
       lassociator _ _ _ • (runitor f ▹ g) = f ◃ lunitor g )
      ×
      (* 16  lassociator_lassociator *)
      (∏ (a b c d e: C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d) (i : C⟦d, e⟧),
       (f ◃ lassociator g h i) • lassociator _ _ _  • (lassociator _ _ _ ▹ i) =
       lassociator f g _  • lassociator _ _ _
      ).

Definition prebicat : UU := ∑ C : prebicat_data, prebicat_laws C.

Coercion prebicat_data_from_bicat (C : prebicat) : prebicat_data := pr1 C.
Coercion prebicat_laws_from_bicat (C : prebicat) : prebicat_laws C := pr2 C.


Section prebicat_law_projections.

Context {C : prebicat}.

Definition id2_left
           (* 1a id2_left *)
           {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : id2 f • x = x
  := pr1 (pr2 C) _ _ _ _ x.

Definition id2_right
           (* 1b id2_right *)
           {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : x • id2 g = x
  := pr1 (pr2 (pr2 C)) _ _ _ _ x.

Definition vassocr
           (* 2 vassocr *)
           {a b : C} {f g h k : C⟦a, b⟧} (x : f ==> g) (y : g ==> h) (z : h ==> k)
  : x • (y • z) = (x • y) • z
  := pr1 (pr2 (pr2 (pr2 C))) _ _ _ _ _ _ x y z.

Definition lwhisker_id2
           (* 3a lwhisker_id2 *)
           {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : f ◃ id2 g = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 C)))) _ _ _ f g.

Definition id2_rwhisker
           (* 3b id2_rwhisker *)
           {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : id2 f ▹ g = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C))))) _ _ _ f g.

Definition lwhisker_vcomp
           (* 4 lwhisker_vcomp *)
           {a b c : C} (f : C⟦a, b⟧) {g h i : C⟦b, c⟧}
           (x : g ==> h) (y : h ==> i)
  : (f ◃ x) • (f ◃ y) = f ◃ (x • y)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))) _ _ _ f _ _ _ x y.

Definition rwhisker_vcomp
           (* 5 rwhisker_vcomp *)
           {a b c : C} {f g h : C⟦a, b⟧} (i : C⟦b, c⟧) (x : f ==> g) (y : g ==> h)
  : (x ▹ i) • (y ▹ i) = (x • y) ▹ i
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))) _ _ _ _ _ _ i x y.

Definition vcomp_lunitor
           (* 6  vcomp_lunitor *)
           {a b : C} (f g : C⟦a, b⟧) (x : f ==> g)
  : (identity _ ◃ x) • lunitor g = lunitor f • x
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))) _ _ f g x.

Definition vcomp_runitor
           (* 7 vcomp_runitor *)
           {a b : C} (f g : C⟦a, b⟧) (x : f ==> g)
  : (x ▹ identity _ ) • runitor g = runitor f • x
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ f g x.

Definition lwhisker_lwhisker
           (* 8 lwhisker_lwhisker *)
           {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) {h i : c --> d} (x : h ==> i)
  : f ◃ (g ◃ x) • lassociator _ _ _ = lassociator _ _ _ • (f · g ◃ x)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))) _ _ _ _ f g _ _ x.

Definition rwhisker_lwhisker
           (* 9 rwhisker_lwhisker *)
           {a b c d : C} (f : C⟦a, b⟧) {g h : C⟦b, c⟧} (i : c --> d) (x : g ==> h)
  : (f ◃ (x ▹ i)) • lassociator _ _ _ = lassociator _ _ _ • ((f ◃ x) ▹ i)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))) _ _ _ _ f _ _ i x.

Definition rwhisker_rwhisker
           (* 10 rwhisker_rwhisker *)
           {a b c d : C} {f g : C⟦a, b⟧} (h : C⟦b, c⟧) (i : c --> d) (x : f ==> g)
  : lassociator _ _ _ • ((x ▹ h) ▹ i) = (x ▹ h · i) • lassociator _ _ _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))) _ _ _ _ _ _ h i x.

Definition vcomp_whisker
           (* 11 vcomp_whisker *)
           {a b c : C} {f g : C⟦a, b⟧} {h i : C⟦b, c⟧} (x : f ==> g) (y : h ==> i)
  : (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))) _ _ _ _ _ _ _ x y.

Definition lunitor_linvunitor
           (* 12a lunitor_linvunitor *)
           {a b : C} (f : C⟦a, b⟧)
  : lunitor f • linvunitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))) _ _ f.

Definition linvunitor_lunitor
           (* 12b linvunitor_lunitor *)
           {a b : C} (f : C⟦a, b⟧)
  : linvunitor f • lunitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))))) _ _ f.

Definition runitor_rinvunitor
           (* 13a runitor_rinvunitor *)
           {a b : C} (f : C⟦a, b⟧)
  : runitor f • rinvunitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))) _ _ f.

Definition rinvunitor_runitor
           (* 13b rinvunitor_runitor *)
           {a b : C} (f : C⟦a, b⟧)
  : rinvunitor f • runitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))))))) _ _ f.

Definition lassociator_rassociator
           (* 14a lassociator_rassociator *)
           {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d)
  : lassociator f g h • rassociator _ _ _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))))) _ _ _ _ f g h.

Definition rassociator_lassociator
           (* 14b rassociator_lassociator *)
           {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d)
  : rassociator f g h • lassociator _ _ _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))))))))) _ _ _ _ f g h.

Definition runitor_rwhisker
           (* 15 runitor_rwhisker *)
           {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : lassociator _ _ _ • (runitor f ▹ g) = f ◃ lunitor g
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))))))) _ _ _ f g .

Definition lassociator_lassociator
           (* 16  lassociator_lassociator *)
           {a b c d e: C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d) (i : C⟦d, e⟧)
  : (f ◃ lassociator g h i) • lassociator _ _ _  • (lassociator _ _ _ ▹ i) =
    lassociator f g _  • lassociator _ _ _

  := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))))))) _ _ _ _ _ f g h i.


End prebicat_law_projections.


(* ----------------------------------------------------------------------------------- *)
(** ** Derived laws *)

Section Derived_laws.

Context {C : prebicat}.

Lemma hcomp_hcomp' {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
      (η : f1 ==> f2) (φ : g1 ==> g2)
  : hcomp η φ = hcomp' η φ.
Proof.
  apply vcomp_whisker.
Defined.

Lemma hcomp_lassoc {a b c d : C}
      {f1 g1 : C ⟦ a, b ⟧} {f2 g2 : C ⟦ b, c ⟧} {f3 g3 : C ⟦ c, d ⟧}
      (x1 : f1 ==> g1) (x2 : f2 ==> g2) (x3 : f3 ==> g3)
  : x1 ⋆ (x2 ⋆ x3) • lassociator g1 g2 g3 =
    lassociator f1 f2 f3 • (x1 ⋆ x2) ⋆ x3.
Proof.
  unfold hcomp.
  rewrite <- lwhisker_vcomp.
  repeat rewrite <- vassocr.
  rewrite lwhisker_lwhisker.
  repeat rewrite vassocr.
  apply maponpaths_2.
  rewrite <- vassocr.
  rewrite rwhisker_lwhisker.
  rewrite vassocr.
  rewrite <- rwhisker_rwhisker.
  rewrite <- vassocr.
  apply maponpaths.
  apply rwhisker_vcomp.
Defined.

Lemma lassociator_to_rassociator_post {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      (x : k ==> (f · g) · h)
      (y : k ==> f · (g · h))
  : x = y • lassociator f g h → x • rassociator f g h = y.
Proof.
  intros p.
  rewrite p.
  rewrite <- vassocr.
  rewrite lassociator_rassociator.
  apply id2_right.
Defined.

Lemma lassociator_to_rassociator_pre {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      (x : f · (g · h) ==> k)
      (y : (f · g) · h ==> k) :
  x = lassociator f g h • y → rassociator f g h • x = y.
Proof.
  intros p.
  rewrite p.
  rewrite vassocr.
  rewrite rassociator_lassociator.
  apply id2_left.
Defined.

Lemma hcomp_rassoc {a b c d : C}
      (f1 g1 : C ⟦ a, b ⟧) (f2 g2 : C ⟦ b, c ⟧) (f3 g3 : C ⟦ c, d ⟧)
      (x1 : f1 ==> g1) (x2 : f2 ==> g2) (x3 : f3 ==> g3)
  : (x1 ⋆ x2) ⋆ x3 • rassociator g1 g2 g3 =
    rassociator f1 f2 f3 • x1 ⋆ (x2 ⋆ x3).
Proof.
  apply lassociator_to_rassociator_post.
  apply pathsinv0.
  repeat rewrite <- vassocr.
  apply lassociator_to_rassociator_pre.
  apply hcomp_lassoc.
Defined.

Lemma hcomp_identity {a b c : C} (f1 : C ⟦ a, b ⟧) (f2 : C ⟦ b, c ⟧)
  : id2 f1 ⋆ id2 f2 = id2 (f1 · f2).
Proof.
  unfold hcomp.
  rewrite id2_rwhisker.
  rewrite id2_left.
  apply lwhisker_id2.
Defined.

(** * Interchange law *)

Lemma hcomp_vcomp {a b c : C}
      (f1 g1 h1 : C ⟦ a, b ⟧)
      (f2 g2 h2 : C ⟦ b, c ⟧)
      (x1 : f1 ==> g1)
      (x2 : f2 ==> g2)
      (y1 : g1 ==> h1)
      (y2 : g2 ==> h2)
  : (x1 • y1) ⋆ (x2 • y2) = (x1 ⋆ x2) • (y1 ⋆ y2).
Proof.
  unfold hcomp at 2 3.
  rewrite vassocr.
  rewrite vcomp_whisker.
  transitivity (((f1 ◃ x2) • ((x1 ▹ g2) • (y1 ▹ g2))) • (h1 ◃ y2)).
  2: repeat rewrite vassocr; reflexivity.
  rewrite rwhisker_vcomp.
  rewrite <- vcomp_whisker.
  rewrite <- vassocr.
  rewrite lwhisker_vcomp.
  unfold hcomp.
  reflexivity.
Defined.

End Derived_laws.

(* ----------------------------------------------------------------------------------- *)
(** ** bicategories. *)

Definition isaset_cells (C : prebicat) : UU
  := ∏ (a b : C) (f g : a --> b), isaset (f ==> g).

Definition bicat : UU := ∑ C : prebicat, isaset_cells C.

Coercion prebicat_of_bicat (C : bicat) : prebicat := pr1 C.

Definition cellset_property {C : bicat} {a b : C} (f g : a --> b)
  : isaset (f ==> g)
  := pr2 C a b f g.

(* ----------------------------------------------------------------------------------- *)
(** ** Homs are categories. *)

Section Hom_Spaces.

Context {C : prebicat} (a b : C).

Definition hom_ob_mor : precategory_ob_mor.
Proof.
  exists (C ⟦a, b⟧). exact (λ f g, f ==> g).
Defined.

Definition hom_data : precategory_data.
Proof.
  exists hom_ob_mor. split.
  - exact id2.
  - exact (λ f g h x y, x • y).
Defined.

Lemma is_precategory_hom : is_precategory hom_data.
Proof.
  repeat split; simpl.
  - intros f g. apply id2_left.
  - intros f g. apply id2_right.
  - intros f g h i. apply vassocr.
Defined.

Definition hom : precategory.
Proof.
  exists hom_data.
  exact is_precategory_hom.
Defined.

End Hom_Spaces.

(* ----------------------------------------------------------------------------------- *)
(** Functor structure on horizontal composition. *)

Section hcomp_functor.

Context {C : prebicat} {a b c : C}.

Definition hcomp_functor_data
  : functor_data (precategory_binproduct (hom a b) (hom b c)) (hom a c).
Proof.
  exists (λ p : (a-->b) × (b-->c), pr1 p · pr2 p).
  unfold hom_ob_mor. simpl. intros (f1, f2) (g1, g2).
  unfold precategory_binproduct_mor. simpl.
  intros (x, y). apply hcomp; assumption.
Defined.

Lemma is_functor_hcomp : is_functor hcomp_functor_data.
Proof.
  split; red; simpl.
  - intros (f1, f2). simpl. apply hcomp_identity.
  - intros (f1, f2) (g1, g2) (h1, h2).
    unfold precategory_binproduct_mor. simpl.
    intros (x1, x2) (y1, y2). cbn. apply hcomp_vcomp.
Defined.

Definition hcomp_functor : precategory_binproduct (hom a b) (hom b c) ⟶ hom a c.
Proof.
  exists hcomp_functor_data. exact is_functor_hcomp.
Defined.

End hcomp_functor.


(** Equivalences *)

Section equivalences.

Context {C : prebicat_data}.

Definition is_equivalence {a b : C} {f g : a --> b} (η : f ==> g)
  : UU
  := ∑ φ : g ==> f, η • φ = id2 _ × φ • η = id2 _ .

Definition equivalence {a b : C} (f g : a --> b) : UU
  := ∑ η : f ==> g, is_equivalence η.

Coercion cell_from_equivalence {a b : C} {f g : a --> b} (η : equivalence f g) : f ==> g := pr1 η.

Definition inv_cell {a b : C} {f g : a --> b} (η : equivalence f g)
  : g ==> f
  := pr1 (pr2 η).

Definition equivalence_after_inv_cell {a b : C} {f g : a --> b} (η : equivalence f g)
  : η • inv_cell η = id2 _
  := pr1 (pr2 (pr2 η)).

Definition inv_cell_after_equivalence {a b : C} {f g : a --> b} (η : equivalence f g)
  : inv_cell η • η = id2 _
  := pr2 (pr2 (pr2 η)).

Definition inv_equivalence {a b : C} {f g : a --> b} (η : equivalence f g)
  : equivalence g f
  := (inv_cell η ,, cell_from_equivalence η ,, inv_cell_after_equivalence η ,, equivalence_after_inv_cell η ).


(* requires cell types to be sets
Lemma isaprop_isequivalence
*)

End equivalences.

Definition id2_equivalence {C : prebicat} {a b : C} (f : a --> b) : equivalence f f.
Proof.
  repeat (use tpair).
  - apply (id2 _ ).
  - apply (id2 _ ).
  - apply id2_left.
  - apply id2_left.
Defined.


(** TODO:
    construct a prebicategory (see CT/bicategories) from a bicat
    Bonus:
    Equivalence of types between these two
 *)
(** TODO:
    define saturation/univalence for bicats
 *)


(** Chaotic bicat *)

Section chaotic_bicat.

Variable C : precategory.

Definition chaotic_prebicat_data : prebicat_data.
Proof.
  use tpair.
  - use tpair.
    + exact C.
    + cbn. intros a b f g. exact unit.
  - cbn; repeat (use tpair).
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + cbn. intros. exact tt.
Defined.

Definition chaotic_prebicat_laws : prebicat_laws chaotic_prebicat_data.
Proof.
  repeat (use tpair); cbn; intros;
    apply isProofIrrelevantUnit.
Qed.

End chaotic_bicat.


Section discrete_bicat.

Variable C : category.

Definition discrete_prebicat_data : prebicat_data.
Proof.
  use tpair.
  - use tpair.
    + exact C.
    + cbn. intros a b f g. exact (f = g).
  - cbn; repeat (use tpair); cbn.
    + intros. apply idpath.
    + intros. apply id_left.
    + intros. apply id_right.
    + intros. apply (!id_left _).
    + intros. apply (!id_right _).
    + intros. apply (! assoc _ _ _ ).
    + intros. apply assoc.
    + intros a b f g h r s. apply (r @ s).
    + intros. apply (maponpaths). assumption.
    + intros. apply (maponpaths_2). assumption.
Defined.

Definition discrete_prebicat_laws : prebicat_laws discrete_prebicat_data.
Proof.
  repeat (use tpair); cbn.
  - intros. apply idpath.
  - intros. apply pathscomp0rid.
  - intros. apply path_assoc.
  - intros. apply idpath.
  - intros. apply idpath.
  - intros. apply pathsinv0. apply maponpathscomp0.
  - intros. unfold maponpaths_2.
    apply pathsinv0. apply (@maponpathscomp0  _ _ _ _ _ (λ x0 : C ⟦ a, b ⟧, x0 · i)).
  - intros. induction x. simpl. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x. simpl. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x. simpl. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x; simpl. apply (pathscomp0rid).
  - intros. induction x; induction y; simpl. apply idpath.
  - intros. apply pathsinv0r.
  - intros. apply pathsinv0l.
  - intros. apply pathsinv0r.
  - intros. apply pathsinv0l.
  - intros. apply pathsinv0r.
  - intros. apply pathsinv0l.
  - intros. apply homset_property.
  - intros. apply homset_property.
Qed.

End discrete_bicat.


Definition psfunctor_ob_mor_cell (C C' : prebicat_data) : UU
  := ∑ F : functor_data C C',
           ∏ a b (f g : a --> b), f ==> g → #F f ==> #F g.

Coercion functor_data_from_bifunctor_ob_mor_cell C C' (F : psfunctor_ob_mor_cell C C')
  : functor_data C C' := pr1 F.

Definition psfunctor_on_cells {C C' : prebicat_data} (F : psfunctor_ob_mor_cell C C')
           {a b : C} {f g : a --> b} (x : f ==> g)
  : #F f ==> #F g
  := pr2 F a b f g x.

Notation "'##'" := (psfunctor_on_cells).

Definition psfunctor_cell_data {C C' : prebicat_data} (F : psfunctor_ob_mor_cell C C') : UU
  :=
    (∏ (a : C), equivalence (#F (identity a)) (identity _) )
      ×
    (∏ (a b c : C) (f : a --> b) (g : b --> c),
     equivalence (#F (f · g)) (#F f · #F g)).

Definition psfunctor_data (C C' : prebicat_data) : UU
  := ∑ F : psfunctor_ob_mor_cell C C', psfunctor_cell_data F.

Coercion psfunctor_ob_mor_cell_from_bifunctor_data C C' (F : psfunctor_data C C')
  : psfunctor_ob_mor_cell _ _ := pr1 F.




Definition psfunctor_id {C C' : prebicat_data} (F : psfunctor_data C C') (a : C)
  : equivalence (#F (identity a)) (identity _)
  := pr1 (pr2 F) a.
Definition psfunctor_comp {C C' : prebicat_data} (F : psfunctor_data C C') {a b c : C}
           (f : a --> b) (g : b --> c)
  : equivalence (#F (f · g)) (#F f · #F g)
  := pr2 (pr2 F) a b c f g.

(* ----------------------------------------------------------------------------------- *)
(** Associators and unitors are isos. *)

Section Associators_Unitors_Iso.

Context {C : prebicat}.

Lemma lassociator_iso {a b c d : C} (f : hom a b) (g : hom b c) (h : hom c d)
  : is_iso (lassociator f g h : (hom a d) ⟦ f · (g · h), (f · g) · h ⟧).
Proof.
  apply is_iso_from_is_z_iso.
  exists (rassociator f g h).
  split.
  - apply lassociator_rassociator.
  - apply rassociator_lassociator.
Defined.

Lemma lunitor_iso {a b : C} (f : hom a b)
  : is_iso (lunitor f : (hom a b) ⟦ identity a · f, f ⟧).
Proof.
  apply is_iso_from_is_z_iso.
  exists (linvunitor f).
  split.
  - apply lunitor_linvunitor.
  - apply linvunitor_lunitor.
Defined.

Lemma runitor_iso {a b : C} (f : hom a b)
  : is_iso (runitor f : (hom a b) ⟦ f · identity b, f ⟧).
Proof.
  apply is_iso_from_is_z_iso.
  exists (rinvunitor f).
  split.
  - apply runitor_rinvunitor.
  - apply rinvunitor_runitor.
Defined.

End Associators_Unitors_Iso.

(* ----------------------------------------------------------------------------------- *)
(** Functor structure on associators and unitors. *)

Section Associators_Unitors_Natural.

Context {C : prebicat}.

(** Left unitor *)

Lemma lunitor_natural (a b : C) (f g : C ⟦ a, b ⟧) (x : f ==> g)
  : id2 (identity a) ⋆ x • lunitor g = lunitor f • x.
Proof.
  unfold hcomp.
  rewrite <- vassocr. rewrite vcomp_lunitor.
  rewrite vassocr. apply maponpaths_2.
  rewrite id2_rwhisker. apply id2_left.
Defined.

Definition lunitor_transf (a b : C)
  : bindelta_pair_functor
      (constant_functor (hom a b) (hom a a) (identity a))
      (functor_identity (hom a b)) ∙
    hcomp_functor
    ⟹
    functor_identity (hom a b).
Proof.
  exists lunitor. red. apply lunitor_natural.
Defined.

(** Right unitor *)

Lemma runitor_natural (a b : C)
      (f g : C ⟦ a, b ⟧)
      (x : f ==> g)
  : x ⋆ id2 (identity b) • runitor g = runitor f • x.
Proof.
  rewrite hcomp_hcomp'. unfold hcomp'.
  rewrite <- vassocr.
  rewrite vcomp_runitor.
  rewrite vassocr. apply maponpaths_2.
  rewrite lwhisker_id2. apply id2_left.
Defined.

Definition runitor_transf (a b : C)
  : bindelta_pair_functor
       (functor_identity (hom a b))
       (constant_functor (hom a b) (hom b b) (identity b)) ∙
    hcomp_functor
    ⟹
    functor_identity (hom a b).
Proof.
  exists runitor. red. apply runitor_natural.
Defined.

(** Left associator. *)

Definition lassociator_fun {a b c d : C}
           (x : C ⟦ a, b ⟧ × C ⟦ b, c ⟧ × C ⟦ c, d ⟧)
  :  pr1 x · (pr12 x · pr22 x) ==> (pr1 x · pr12 x) · pr22 x
  := lassociator (pr1 x) (pr12 x) (pr22 x).

Lemma lassociator_fun_natural {a b c d : C}
  : is_nat_trans
      (pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor)
      (precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
       pair_functor hcomp_functor (functor_identity (hom c d)) ∙
       hcomp_functor)
      lassociator_fun.
Proof.
  red; cbn. intros (f1, (f2, f3)) (g1, (g2, g3)).
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  intros (x1, (x2, x3)). simpl.
  unfold lassociator_fun. simpl.
  apply hcomp_lassoc.
Defined.

Definition lassociator_transf (a b c d : C)
  : pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor
    ⟹
    precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
    pair_functor hcomp_functor (functor_identity (hom c d)) ∙
    hcomp_functor.
Proof.
  exists lassociator_fun. exact lassociator_fun_natural.
Defined.

(** Right associator. *)

Definition rassociator_fun {a b c d : C}
           (x : C ⟦ a, b ⟧ × C ⟦ b, c ⟧ × C ⟦ c, d ⟧)
  : (pr1 x · pr12 x) · pr22 x ==> pr1 x · (pr12 x · pr22 x)
  := rassociator (pr1 x) (pr12 x) (pr22 x).

Lemma rassociator_fun_natural {a b c d : C}
  : is_nat_trans
      (precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
       pair_functor hcomp_functor (functor_identity (hom c d)) ∙
       hcomp_functor)
      (pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor)
      rassociator_fun.
Proof.
  red; cbn. intros (f1, (f2, f3)) (g1, (g2, g3)).
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  intros (x1, (x2, x3)). simpl.
  unfold rassociator_fun. simpl.
  apply hcomp_rassoc.
Defined.

Definition rassociator_transf (a b c d : C)
  : precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
    pair_functor hcomp_functor (functor_identity (hom c d)) ∙
    hcomp_functor
    ⟹
    pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor.
Proof.
  exists rassociator_fun. exact rassociator_fun_natural.
Defined.

End Associators_Unitors_Natural.
