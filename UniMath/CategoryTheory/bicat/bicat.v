Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.

Open Scope cat.

Definition bicat_cell_struct (C : precategory_ob_mor) : UU :=
  ∏ (a b: C), C⟦a, b⟧ → C⟦a, b⟧ → UU.

(*
Definition bicat_ob_mor_cells : UU := ∑ (C : precategory_ob_mor), bicat_cell_struct C.

Coercion precat_ob_mor_from_bicat_ob_mor_cells (T : bicat_ob_mor_cells)
  : precategory_ob_mor := pr1 T.

Definition bicat_cells (C : bicat_ob_mor_cells) {a b : C} (f g : C⟦a, b⟧) : UU :=
  pr2 C a b f g.
 *)

Definition bicat_1_id_comp_cells : UU := ∑ (C : precategory_data), bicat_cell_struct C.
Coercion precat_data_from_bicat_1_id_comp_cells (C : bicat_1_id_comp_cells)
  : precategory_data
  := pr1 C.

Definition bicat_cells (C : bicat_1_id_comp_cells) {a b : C} (f g : C⟦a, b⟧) : UU :=
  pr2 C a b f g.


Notation "f '==>' g" := (bicat_cells _ f g) (at level 60).
Notation "f '<==' g" := (bicat_cells _ g f) (at level 60, only parsing).
(*
Definition bicat_cells_1_id_comp : UU := ∑ C : bicat_ob_mor_cells, precategory_id_comp C.

Coercion precat_data_from_bicat_cells_1_id_comp (C : bicat_cells_1_id_comp) : precategory_data.
Proof.
  exists (pr1 C).
  exact (pr2 C).
Defined.

Check (fun (C : bicat_cells_1_id_comp) (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) => f · g).
*)



Definition bicat_2_id_comp_struct (C : bicat_1_id_comp_cells) : UU
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

Coercion bicat_cells_1_id_comp_from_bicat_data (C : bicat_data) : bicat_1_id_comp_cells
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


Notation "x • y" := (vcomp2 x y) (at level 60).
Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)

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

Definition bicat : UU := ∑ C : bicat_data, bicat_laws C.

Coercion bicat_data_from_bicat (C : bicat) : bicat_data := pr1 C.
Coercion bicat_laws_from_bicat (C : bicat) : bicat_laws C := pr2 C.


Section bicat_law_projections.

Context {C : bicat}.

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

(** TODO: there is an analog to law nr 8 for right associator.
          can it be derived from 8 plus l being inverse to r associator?

 (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h i : c --> d) (x : h ==> i),
         (f · g) ◃ x • rassociator _ _ _ = rassociator _ _ _ • (f ◃ (g ◃ x))

*)

End bicat_law_projections.


Lemma hcomp1_hcomp2 {C : bicat} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
      (η : f1 ==> f2) (φ : g1 ==> g2)
  : hcomp1 η φ = hcomp2 η φ.
Proof.
  unfold hcomp1.
  unfold hcomp2.
  apply vcomp_whisker.
Defined.



(** TODO:
    construct a prebicategory (see CT/bicategories) from a bicat
    Bonus:
    Equivalence of types between these two
 *)
(** TODO:
    define saturation/univalence for bicats
 *)
(** TODO:
    trivial bicat structures on a (pre)category
    - discrete bicat
    - chaotic bicat
 *)


(** Chaotic bicat *)

Section chaotic_bicat.

Variable C : precategory.

Definition chaotic_bicat_data : bicat_data.
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

Definition chaotic_bicat_laws : bicat_laws chaotic_bicat_data.
Proof.
  repeat (use tpair); cbn; intros;
    apply isProofIrrelevantUnit.
Qed.

End chaotic_bicat.


Section discrete_bicat.

Variable C : category.

Definition discrete_bicat_data : bicat_data.
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

Definition discrete_bicat_laws : bicat_laws discrete_bicat_data.
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
