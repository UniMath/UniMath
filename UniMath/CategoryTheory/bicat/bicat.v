Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.

Open Scope cat.

Definition bicat_cell_struct (C : precategory_ob_mor) : UU :=
  ∏ (a b: C), C⟦a, b⟧ → C⟦a, b⟧ → UU.

Definition bicat_ob_mor_cells : UU := ∑ (C : precategory_ob_mor), bicat_cell_struct C.

Coercion precat_ob_mor_from_bicat_ob_mor_cells (T : bicat_ob_mor_cells)
  : precategory_ob_mor := pr1 T.

Definition bicat_cells (C : bicat_ob_mor_cells) {a b : C} (f g : C⟦a, b⟧) : UU :=
  pr2 C a b f g.

Notation "f '==>' g" := (bicat_cells _ f g) (at level 60).
Notation "f '<==' g" := (bicat_cells _ g f) (at level 60, only parsing).

Definition bicat_cells_1_id_comp : UU := ∑ C : bicat_ob_mor_cells, precategory_id_comp C.

Coercion precat_data_from_bicat_cells_1_id_comp (C : bicat_cells_1_id_comp) : precategory_data.
Proof.
  exists (pr1 C).
  exact (pr2 C).
Defined.

Check (fun (C : bicat_cells_1_id_comp) (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) => f · g).




Definition bicat_2_id_comp_struct (C : bicat_cells_1_id_comp) : UU
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




(* Horizontal composition, to be derived from whiskering
    ( ∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧),
           f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2).
*)

Definition bicat_data : UU := ∑ C, bicat_2_id_comp_struct C.

Coercion bicat_cells_1_id_comp_from_bicat_data (C : bicat_data) : bicat_cells_1_id_comp
  := pr1 C.

Definition id2 {C : bicat_data} {a b : C} (f : C⟦a, b⟧) : f ==> f
  := pr1 (pr2 C) a b f.
Check (λ (C : bicat_data) , pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (C))))))) ))).


Definition lunitor {C : bicat_data} {a b : C} (f : C⟦a, b⟧)
  : identity _ · f ==> f
  := pr1 (pr2 (pr2 C)) a b f.

Definition runitor {C : bicat_data} {a b : C} (f : C⟦a, b⟧)
  : f · identity _ ==> f
  := pr1 (pr2 (pr2 (pr2 C))) a b f.

Definition linvunitor {C : bicat_data} {a b : C} (f : C⟦a, b⟧)
  : identity _ · f <== f
  := pr1 (pr2 (pr2 (pr2 (pr2 C)))) a b f.

Definition rinvunitor {C : bicat_data} {a b : C} (f : C⟦a, b⟧)
  : f · identity _ <== f
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C))))) a b f.

Definition rassociator {C : bicat_data} {a b c d : C}
           (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
  : (f · g) · h ==> f · (g · h)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))) a b c d f g h.

Definition lassociator {C : bicat_data} {a b c d : C}
           (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
  : f · (g · h) ==> (f · g) · h
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))) a b c d f g h.

Definition vcomp2 {C : bicat_data} {a b : C} {f g h: C⟦a, b⟧}
  : f ==> g → g ==> h → f ==> h
  := λ x y, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))) _ _ _ _ _  x y.

Definition lwhisker {C : bicat_data} {a b c : C} (f : C⟦a, b⟧) {g1 g2 : C⟦b, c⟧}
  : g1 ==> g2 → f · g1 ==> f · g2
  := λ x, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ _ _ _ _ x.

Definition rwhisker {C : bicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} (g : C⟦b, c⟧)
  : f1 ==> f2 → f1 · g ==> f2 · g
  := λ x, pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ _ _ _ _ x.


Notation "x • y" := (vcomp2 x y) (at level 50).
Notation "f ◃ x" := (lwhisker f x) (at level 50). (* \tw *)
Notation "y ▹ g" := (rwhisker g y) (at level 50). (* \tw nr 2 *)

Definition hcomp1 {C : bicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2.
Proof.
  intros x y.
  set (xg1 := x ▹ g1).
  set (f2y := f2 ◃ y).
  exact (xg1 • f2y).
Defined.

Definition hcomp2 {C : bicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2.
Proof.
  intros x y.
  set (f1y := f1 ◃ y).
  set (xg2 := x ▹ g2).
  exact (f1y • xg2).
Defined.

(*
Notation "x ⋆ y" := (hcomp2 x y) (at level 50).
 *)

Definition bicat_laws (C : bicat_data) : UU
  :=  (* 1a *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), id2 f • x = x)
        ×
      (* 1b *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), x • id2 g = x)
      ×
      (* 2 *)
      (∏ (a b : C) (f g h k : C⟦a, b⟧) (x : f ==> g) (y : g ==> h) (z : h ==> k),
       x • (y • z) = (x • y) • z)
      ×
      (* 3a *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), f ◃ id2 g = id2 _ )
      ×
      (* 3b *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), id2 f ▹ g = id2 _ )
      ×
      (* 4 *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g h i : C⟦b, c⟧) (x : g ==> h) (y : h ==> i),
       (f ◃ x) • (f ◃ y) = f ◃ (x • y))
      ×
      (* 5 *)
      (∏ (a b c : C) (f g h : C⟦a, b⟧) (i : C⟦b, c⟧) (x : f ==> g) (y : g ==> h),
       (x ▹ i) • (y ▹ i) = (x • y) ▹ i)
      ×
      (* 6 *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
       (identity _ ◃ x) • lunitor g = lunitor f • x )
      ×
      (* 7 *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
       (x ▹ identity _ ) • runitor g = runitor f • x )
      ×
      (* 8 *)
      (unit).