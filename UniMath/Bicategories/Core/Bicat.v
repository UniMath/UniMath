(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Definition of prebicategory                                                     *)
(*                                                                                     *)
(** *** Data                                                                           *)
(* ----------------------------------------------------------------------------------- *)

Definition prebicat_2cell_struct (C : precategory_ob_mor)
  : UU
  := ∏ (a b: C), C⟦a, b⟧ → C⟦a, b⟧ → UU.

Definition prebicat_1_id_comp_cells : UU
  := ∑ (C : precategory_data), prebicat_2cell_struct C.

Coercion precat_data_from_prebicat_1_id_comp_cells (C : prebicat_1_id_comp_cells)
  : precategory_data
  := pr1 C.

Definition prebicat_cells (C : prebicat_1_id_comp_cells) {a b : C} (f g : C⟦a, b⟧)
  : UU
  := pr2 C a b f g.

Local Notation "f '==>' g" := (prebicat_cells _ f g) (at level 60).
Local Notation "f '<==' g" := (prebicat_cells _ g f) (at level 60, only parsing).

Definition prebicat_2_id_comp_struct (C : prebicat_1_id_comp_cells) : UU
  :=
       (* 2-unit *)
       (∏ (a b : C) (f : C⟦a, b⟧), f ==> f)
     × (* left unitor *)
       (∏ (a b : C) (f : C⟦a, b⟧), identity _ · f ==> f)
     × (* right unitor *)
       (∏ (a b : C) (f : C⟦a, b⟧), f · identity _  ==> f)
     × (* left inverse unitor *)
       (∏ (a b : C) (f : C⟦a, b⟧), identity _ · f <== f)
     × (* right inverse unitor *)
       (∏ (a b : C) (f : C⟦a, b⟧), f · identity _  <== f)
     × (* right associator *)
       (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
        (f · g) · h ==> f · (g · h))
     × (* left associator *)
       (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
        f · (g · h) ==> (f · g) · h)
     × (* vertical composition *)
       (∏ (a b : C) (f g h : C⟦a, b⟧), f ==> g -> g ==> h -> f ==> h)
     × (* left whiskering *)
       (∏ (a b c : C) (f : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧),
        g1 ==> g2 → f · g1 ==> f · g2)
     × (* right whiskering *)
       (∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g : C⟦b, c⟧),
        f1 ==> f2 → f1 · g ==> f2 · g).

Definition prebicat_data : UU := ∑ C, prebicat_2_id_comp_struct C.

Definition make_prebicat_data C (str : prebicat_2_id_comp_struct C)
  : prebicat_data
  := C,, str.

(* ----------------------------------------------------------------------------------- *)
(** Data projections.                                                                  *)
(* ----------------------------------------------------------------------------------- *)

Coercion prebicat_cells_1_id_comp_from_prebicat_data (C : prebicat_data)
  : prebicat_1_id_comp_cells
  := pr1 C.

Definition id2 {C : prebicat_data} {a b : C} (f : C⟦a, b⟧) : f ==> f
  := pr1 (pr2 C) a b f.

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
  := λ x y, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))) _ _ _ _ _ x y.

Definition lwhisker {C : prebicat_data} {a b c : C} (f : C⟦a, b⟧) {g1 g2 : C⟦b, c⟧}
  : g1 ==> g2 → f · g1 ==> f · g2
  := λ x, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ _ _ _ _ x.

Definition rwhisker {C : prebicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} (g : C⟦b, c⟧)
  : f1 ==> f2 → f1 · g ==> f2 · g
  := λ x, pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ _ _ _ _ x.

Local Notation "x • y" := (vcomp2 x y) (at level 60).
Local Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
Local Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)

Definition hcomp {C : prebicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2
  := λ x y, (x ▹ g1) • (f2 ◃ y).

Definition hcomp' {C : prebicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2
  := λ x y, (f1 ◃ y) • (x ▹ g2).

Local Notation "x ⋆ y" := (hcomp x y) (at level 50, left associativity).

(* ----------------------------------------------------------------------------------- *)
(** ** Laws                                                                            *)
(* ----------------------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------------------- *)
(** The numbers in the following laws refer to the list of axioms given in ncatlab
    (Section "Definition / Details")
    https://ncatlab.org/nlab/show/bicategory#detailedDefn
    version of October 7, 2015 10:35:36                                                *)
(* ----------------------------------------------------------------------------------- *)

Definition prebicat_laws (C : prebicat_data)
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
     × (** 6  vcomp_lunitor *)
       (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
        (identity _ ◃ x) • lunitor g = lunitor f • x)
     × (** 7 vcomp_runitor *)
       (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
        (x ▹ identity _) • runitor g = runitor f • x)
     × (** 8 lwhisker_lwhisker *)
       (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h i : c --> d) (x : h ==> i),
        f ◃ (g ◃ x) • lassociator _ _ _ = lassociator _ _ _ • (f · g ◃ x))
     × (** 9 rwhisker_lwhisker *)
       (∏ (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : c --> d) (x : g ==> h),
        (f ◃ (x ▹ i)) • lassociator _ _ _ = lassociator _ _ _ • ((f ◃ x) ▹ i))
     × (** 10 rwhisker_rwhisker *)
       (∏ (a b c d : C) (f g : C⟦a, b⟧) (h : C⟦b, c⟧) (i : c --> d) (x : f ==> g),
        lassociator _ _ _ • ((x ▹ h) ▹ i) = (x ▹ h · i) • lassociator _ _ _)
     × (** 11 vcomp_whisker *)
       (∏ (a b c : C) (f g : C⟦a, b⟧) (h i : C⟦b, c⟧) (x : f ==> g) (y : h ==> i),
        (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i))
     × (** 12a lunitor_linvunitor *)
       (∏ (a b : C) (f : C⟦a, b⟧), lunitor f • linvunitor _ = id2 _)
     × (** 12b linvunitor_lunitor *)
       (∏ (a b : C) (f : C⟦a, b⟧), linvunitor f • lunitor _ = id2 _)
     × (** 13a runitor_rinvunitor *)
       (∏ (a b : C) (f : C⟦a, b⟧), runitor f • rinvunitor _ = id2 _)
     × (** 13b rinvunitor_runitor *)
     (∏ (a b : C) (f : C⟦a, b⟧), rinvunitor f • runitor _ = id2 _)
     × (** 14a lassociator_rassociator *)
       (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d),
        lassociator f g h • rassociator _ _ _ = id2 _)
     × (** 14b rassociator_lassociator *)
       (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d),
        rassociator f g h • lassociator _ _ _ = id2 _)
     × (** 15 runitor_rwhisker *)
       (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧),
        lassociator _ _ _ • (runitor f ▹ g) = f ◃ lunitor g)
     × (** 16  lassociator_lassociator *)
       (∏ (a b c d e: C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d) (i : C⟦d, e⟧),
        (f ◃ lassociator g h i) • lassociator _ _ _  • (lassociator _ _ _ ▹ i) =
        lassociator f g _  • lassociator _ _ _).

Definition prebicat : UU := ∑ C : prebicat_data, prebicat_laws C.

Coercion prebicat_data_from_bicat (C : prebicat) : prebicat_data := pr1 C.
Coercion prebicat_laws_from_bicat (C : prebicat) : prebicat_laws C := pr2 C.

(* ----------------------------------------------------------------------------------- *)
(** Laws projections.                                                                  *)
(* ----------------------------------------------------------------------------------- *)

Section prebicat_law_projections.

Context {C : prebicat}.

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

(** 6  vcomp_lunitor *)
Definition vcomp_lunitor {a b : C} (f g : C⟦a, b⟧) (x : f ==> g)
  : (identity _ ◃ x) • lunitor g = lunitor f • x
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))) _ _ f g x.

(** 7 vcomp_runitor *)
Definition vcomp_runitor {a b : C} (f g : C⟦a, b⟧) (x : f ==> g)
  : (x ▹ identity _) • runitor g = runitor f • x
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ f g x.

(** 8 lwhisker_lwhisker *)
Definition lwhisker_lwhisker {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
           {h i : c --> d} (x : h ==> i)
  : f ◃ (g ◃ x) • lassociator _ _ _ = lassociator _ _ _ • (f · g ◃ x)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))) _ _ _ _ f g _ _ x.

(** 9 rwhisker_lwhisker *)
Definition rwhisker_lwhisker {a b c d : C} (f : C⟦a, b⟧) {g h : C⟦b, c⟧}
           (i : c --> d) (x : g ==> h)
  : (f ◃ (x ▹ i)) • lassociator _ _ _ = lassociator _ _ _ • ((f ◃ x) ▹ i)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 C))))))))))) _ _ _ _ f _ _ i x.

(** 10 rwhisker_rwhisker *)
Definition rwhisker_rwhisker {a b c d : C} {f g : C⟦a, b⟧} (h : C⟦b, c⟧)
           (i : c --> d) (x : f ==> g)
  : lassociator _ _ _ • ((x ▹ h) ▹ i) = (x ▹ h · i) • lassociator _ _ _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))) _ _ _ _ _ _ h i x.

(** 11 vcomp_whisker *)
Definition vcomp_whisker {a b c : C} {f g : C⟦a, b⟧} {h i : C⟦b, c⟧}
           (x : f ==> g) (y : h ==> i)
  : (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))) _ _ _ _ _ _ _ x y.

(** 12a lunitor_linvunitor *)
Definition lunitor_linvunitor {a b : C} (f : C⟦a, b⟧)
  : lunitor f • linvunitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))) _ _ f.

(** 12b linvunitor_lunitor *)
Definition linvunitor_lunitor {a b : C} (f : C⟦a, b⟧)
  : linvunitor f • lunitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))))) _ _ f.

(** 13a runitor_rinvunitor *)
Definition runitor_rinvunitor {a b : C} (f : C⟦a, b⟧)
  : runitor f • rinvunitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))) _ _ f.

(** 13b rinvunitor_runitor *)
Definition rinvunitor_runitor {a b : C} (f : C⟦a, b⟧)
  : rinvunitor f • runitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))))))) _ _ f.

(** 14a lassociator_rassociator *)
Definition lassociator_rassociator {a b c d : C}
           (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d)
  : lassociator f g h • rassociator _ _ _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))))) _ _ _ _ f g h.

(** 14b rassociator_lassociator *)
Definition rassociator_lassociator {a b c d : C}
           (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d)
  : rassociator f g h • lassociator _ _ _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))))))))) _ _ _ _ f g h.

(** 15 runitor_rwhisker *)
Definition runitor_rwhisker {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : lassociator _ _ _ • (runitor f ▹ g) = f ◃ lunitor g
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
      (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))))))) _ _ _ f g .

(** 16  lassociator_lassociator *)
Definition lassociator_lassociator {a b c d e: C}
           (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d) (i : C⟦d, e⟧)
  : (f ◃ lassociator g h i) • lassociator _ _ _  • (lassociator _ _ _ ▹ i) =
    lassociator f g _  • lassociator _ _ _
  := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
       (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))))))) _ _ _ _ _ f g h i.

End prebicat_law_projections.

(* ----------------------------------------------------------------------------------- *)
(** ** Bicategories                                                                    *)
(* ----------------------------------------------------------------------------------- *)

Definition isaset_cells (C : prebicat) : UU
  := ∏ (a b : C) (f g : a --> b), isaset (f ==> g).

Definition bicat : UU
  := ∑ C : prebicat, isaset_cells C.

Definition build_bicategory
           (C : prebicat_data)
           (HC1 : prebicat_laws C)
           (HC2 : isaset_cells (tpair _ C HC1))
  : bicat
  := tpair _ (tpair _ C HC1) HC2.

Definition build_prebicat_data
           (ob : UU)
           (mor : ob -> ob -> UU)
           (cell : ∏ {X Y : ob}, mor X Y -> mor X Y -> UU)
           (id₁ : ∏ (X : ob), mor X X)
           (comp : ∏ {X Y Z : ob}, mor X Y -> mor Y Z -> mor X Z)
           (id₂ : ∏ {X Y : ob} (f : mor X Y), cell f f)
           (vcomp : ∏ {X Y : ob} {f g h : mor X Y}, cell f g -> cell g h -> cell f h)
           (lwhisk : ∏ {X Y Z : ob} (f : mor X Y) {g h : mor Y Z},
                     cell g h -> cell (comp f g) (comp f h))
           (rwhisk : ∏ {X Y Z : ob} {g h : mor X Y} (f : mor Y Z),
                     cell g h -> cell (comp g f) (comp h f))
           (lunitor : ∏ {X Y : ob} (f : mor X Y),
                      cell (comp (id₁ X) f) f)
           (lunitor_inv : ∏ {X Y : ob} (f : mor X Y),
                          cell f (comp (id₁ X) f))
           (runitor : ∏ {X Y : ob} (f : mor X Y),
                      cell (comp f (id₁ Y)) f)
           (runitor_inv : ∏ {X Y : ob} (f : mor X Y),
                          cell f (comp f (id₁ Y)))
           (lassocor : ∏ {W X Y Z : ob} (f : mor W X) (g : mor X Y) (h : mor Y Z),
                       cell (comp f (comp g h)) (comp (comp f g) h))
           (rassocor : ∏ {W X Y Z : ob} (f : mor W X) (g : mor X Y) (h : mor Y Z),
                       cell (comp (comp f g) h) (comp f (comp g h)))
  : prebicat_data.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * use tpair.
        ** exact ob.
        ** exact mor.
      * use tpair.
        ** exact id₁.
        ** exact comp.
    + exact cell.
  - use tpair.
    + exact id₂.
    + repeat (use tpair) ; simpl.
      * exact lunitor.
      * exact runitor.
      * exact lunitor_inv.
      * exact runitor_inv.
      * exact rassocor.
      * exact lassocor.
      * exact vcomp.
      * exact lwhisk.
      * exact rwhisk.
Defined.

Coercion prebicat_of_bicat (C : bicat)
  : prebicat
  := pr1 C.

Definition cellset_property {C : bicat} {a b : C} (f g : a --> b)
  : isaset (f ==> g)
  := pr2 C a b f g.

(* ----------------------------------------------------------------------------------- *)
(** ** Invertible 2-cells                                                              *)
(* ----------------------------------------------------------------------------------- *)

Definition is_invertible_2cell {C : prebicat_data}
           {a b : C} {f g : a --> b} (η : f ==> g)
  : UU
  := ∑ φ : g ==> f, η • φ = id2 f × φ • η = id2 g.

Definition make_is_invertible_2cell {C : prebicat_data}
           {a b : C} {f g : a --> b}
           {η : f ==> g}
           {φ : g ==> f}
           (ηφ : η • φ = id2 f)
           (φη : φ • η = id2 g)
  : is_invertible_2cell η
  := φ,, make_dirprod ηφ φη.

Definition inv_cell {C : prebicat_data} {a b : C} {f g : a --> b} {η : f ==> g}
  : is_invertible_2cell η → g ==> f
  := pr1.

(* TODO: Reorganize notations. *)
(* Declare Scope bicategory_scope. *)
Notation "inv_η ^-1" := (inv_cell inv_η) : bicategory_scope.
Delimit Scope bicategory_scope with bicategory.
Bind Scope bicategory_scope with bicat.
Local Open Scope bicategory_scope.

Definition vcomp_rinv {C : prebicat_data} {a b : C} {f g : a --> b}
           {η : f ==> g} (inv_η : is_invertible_2cell η)
  : η • inv_η^-1 = id2 f
  := pr1 (pr2 inv_η).

Definition vcomp_lid {C : prebicat_data} {a b : C} {f g : a --> b}
           {η : f ==> g} (inv_η : is_invertible_2cell η)
  : inv_η^-1 • η = id2 g
  := pr2 (pr2 inv_η).

Definition is_invertible_2cell_inv {C : prebicat_data} {a b : C} {f g : a --> b}
           {η : f ==> g} (inv_η : is_invertible_2cell η)
  : is_invertible_2cell (inv_η^-1)
  := make_is_invertible_2cell (vcomp_lid inv_η) (vcomp_rinv inv_η).

Definition is_invertible_2cell_id₂ {C : prebicat} {a b : C} (f : a --> b)
  : is_invertible_2cell (id2 f)
  := make_is_invertible_2cell (id2_left (id2 f)) (id2_left (id2 f)).

Lemma isaprop_is_invertible_2cell {C : bicat}
      {a b : C} {f g : C ⟦a, b⟧} (x : f ==> g)
  : isaprop (is_invertible_2cell x).
Proof.
  apply invproofirrelevance.
  intros p q.
  apply subtypePath.
  { intro. apply isapropdirprod; apply cellset_property. }
  set (Hz1 := pr12 q).
  set (Hy2 := pr22 p).
  set (y := pr1 p).
  set (z := pr1 q).
  cbn in *.
  intermediate_path (y • (x • z)).
  - apply pathsinv0.
    etrans. { apply maponpaths. apply Hz1. }
    apply id2_right.
  - etrans. { apply vassocr. }
    etrans. { apply maponpaths_2. apply Hy2. }
    apply id2_left.
Qed.

Lemma isPredicate_is_invertible_2cell {C : bicat}
      {a b : C} {f g: C⟦a,b⟧}
  : isPredicate (is_invertible_2cell (f := f) (g := g)).
Proof.
  intro x. apply isaprop_is_invertible_2cell.
Qed.


Lemma vcomp_rcancel {C : prebicat} {a b : C} {f g : C⟦a, b⟧}
      (x : f ==> g) (inv_x : is_invertible_2cell x)
      {e : C⟦a, b⟧} {y z : e ==> f}
  : y • x = z • x -> y = z.
Proof.
  intro R.
  transitivity ((y • x) • inv_x^-1).
  - rewrite <- vassocr, vcomp_rinv. apply (!id2_right _).
  - rewrite R, <- vassocr, vcomp_rinv. apply id2_right.
Qed.

Lemma vcomp_lcancel  {C : prebicat} {a b : C} {f g : C⟦a, b⟧}
      (x : f ==> g) (inv_x : is_invertible_2cell x)
      {h : C⟦a, b⟧} {y z : g ==> h}
  : x • y = x • z -> y = z.
Proof.
  intro R.
  transitivity (inv_x^-1 • (x • y)).
  - rewrite vassocr, vcomp_lid. apply (!id2_left _).
  - rewrite R, vassocr, vcomp_lid. apply id2_left.
Qed.

Lemma inv_cell_eq {C : bicat} {a b : C} {f g : C ⟦a, b⟧} (x y : f ==> g)
      (inv_x : is_invertible_2cell x) (inv_y : is_invertible_2cell y)
      (p : inv_x^-1 = inv_y^-1)
  : x = y.
Proof.
  apply (vcomp_rcancel _ (is_invertible_2cell_inv inv_x)).
  rewrite vcomp_rinv, p.
  apply (!vcomp_rinv _).
Qed.

(* ------------------------------------------------------------------------- *)
(* invertible_2cell                                                          *)
(* ------------------------------------------------------------------------- *)

Definition invertible_2cell {C : prebicat_data}
           {a b : C} (f g : a --> b) : UU
  := ∑ η : f ==> g, is_invertible_2cell η.

Definition make_invertible_2cell {C : prebicat_data}
         {a b : C} {f g : C⟦a,b⟧}
         {η : f ==> g} (inv_η : is_invertible_2cell η)
  : invertible_2cell f g
  := η,, inv_η.

Coercion cell_from_invertible_2cell {C : prebicat_data}
         {a b : C} {f g : a --> b} (η : invertible_2cell f g)
  : f ==> g
  := pr1 η.

Coercion property_from_invertible_2cell {C : prebicat_data}
         {a b : C} {f g : a --> b}
         (η : invertible_2cell f g)
  : is_invertible_2cell η
  := pr2 η.

Definition id2_invertible_2cell {C : prebicat} {a b : C} (f : a --> b)
  : invertible_2cell f f
  := make_invertible_2cell (is_invertible_2cell_id₂ f).

Lemma cell_from_invertible_2cell_eq {C : bicat}
      {a b : C} {f g : C⟦a,b⟧} {x y : invertible_2cell f g}
      (p : cell_from_invertible_2cell x = cell_from_invertible_2cell y)
  : x = y.
Proof.
  unfold cell_from_invertible_2cell.
  apply subtypePath.
  - intro. apply isPredicate_is_invertible_2cell.
  - apply p.
Defined.

(* ----------------------------------------------------------------------------------- *)
(** ** Derived laws                                                                    *)
(* ----------------------------------------------------------------------------------- *)

Section Derived_laws.

Context {C : prebicat}.

Definition vassocl {a b : C} {f g h k : C⟦a, b⟧}
           (x : f ==> g) (y : g ==> h) (z : h ==> k)
  : (x • y) • z = x • (y • z)
  := !vassocr x y z.

Lemma vassoc4 {a b : C} {f g h i j: C ⟦a, b⟧}
      (w : f ==> g) (x : g ==> h) (y : h ==> i) (z : i ==> j)
  : w • (x • (y • z)) = w • (x • y) • z.
Proof.
  repeat rewrite vassocr.
  apply idpath.
Qed.

Lemma is_invertible_2cell_rassociator {a b c d : C}
      (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : C⟦c,d⟧)
  : is_invertible_2cell (rassociator f g h).
Proof.
  exists (lassociator f g h).
  split; [ apply rassociator_lassociator | apply lassociator_rassociator ].
Defined.

Lemma is_invertible_2cell_lassociator {a b c d : C}
      (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : C⟦c,d⟧)
  : is_invertible_2cell (lassociator f g h).
Proof.
  exists (rassociator f g h).
  split; [ apply lassociator_rassociator | apply rassociator_lassociator ].
Defined.

Lemma lhs_right_invert_cell {a b : C} {f g h : a --> b}
      (x : f ==> g) (y : g ==> h) (z : f ==> h) (inv_y : is_invertible_2cell y)
  : x = z • inv_y^-1 -> x • y = z.
Proof.
  intro H1.
  etrans. apply maponpaths_2. apply H1.
  etrans. apply vassocl.
  etrans. apply maponpaths. apply (vcomp_lid inv_y).
  apply id2_right.
Qed.

Lemma lhs_left_invert_cell {a b : C} {f g h : a --> b}
      (x : f ==> g) (y : g ==> h) (z : f ==> h) (inv_x : is_invertible_2cell x)
  : y = inv_x^-1 • z -> x • y = z.
Proof.
  intro H1.
  etrans. apply maponpaths. apply H1.
  etrans. apply vassocr.
  etrans. apply maponpaths_2. apply (vcomp_rinv inv_x).
  apply id2_left.
Qed.

Lemma rhs_right_inv_cell {a b : C} {f g h : a --> b}
      (x : f ==> g) (y : g ==> h) (z : f ==> h) (inv_y : is_invertible_2cell y)
  : x • y = z -> x = z • inv_y^-1.
Proof.
  intro H1.
  apply (vcomp_rcancel _ inv_y).
  etrans. { apply H1. }
  etrans. 2: apply vassocr.
  apply pathsinv0.
  etrans. apply maponpaths.
  apply vcomp_lid.
  apply id2_right.
Qed.

Lemma rhs_left_inv_cell {a b : C} {f g h : a --> b}
      (x : g ==> h) (y : f ==> g) (z : f ==> h) (inv_y : is_invertible_2cell y)
  : y • x = z -> x = inv_y^-1 • z.
Proof.
  intro H1.
  apply (vcomp_lcancel _ inv_y).
  etrans. { apply H1. }
  etrans. 2: apply vassocl.
  apply pathsinv0.
  etrans. apply maponpaths_2.
  apply (vcomp_rinv inv_y).
  apply id2_left.
Qed.

Lemma rassociator_to_lassociator_post {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      (x : k ==> (f · g) · h)
      (y : k ==> f · (g · h))
      (p : x • rassociator f g h = y)
  : x = y • lassociator f g h.
Proof.
  apply pathsinv0.
  use lhs_right_invert_cell.
  - apply is_invertible_2cell_lassociator.
  - cbn. exact (!p).
Qed.

Lemma lassociator_to_rassociator_post {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      (x : k ==> (f · g) · h)
      (y : k ==> f · (g · h))
      (p : x = y • lassociator f g h)
  : x • rassociator f g h = y.
Proof.
  use lhs_right_invert_cell.
  - apply is_invertible_2cell_rassociator.
  - exact p.
Qed.

Lemma lassociator_to_rassociator_pre {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      (x : f · (g · h) ==> k)
      (y : (f · g) · h ==> k)
      (p : x = lassociator f g h • y)
  : rassociator f g h • x = y.
Proof.
  use lhs_left_invert_cell.
  - apply is_invertible_2cell_rassociator.
  - exact p.
Qed.

Lemma rassociator_to_lassociator_pre {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      (x : f · (g · h) ==> k)
      (y : (f · g) · h ==> k)
      (p : rassociator f g h • x = y)
  : x = lassociator f g h • y.
Proof.
  apply pathsinv0.
  use lhs_left_invert_cell.
  - apply is_invertible_2cell_lassociator.
  - exact (!p).
Qed.

Lemma lunitor_lwhisker {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : rassociator _ _ _ • (f ◃ lunitor g) = runitor f ▹ g.
Proof.
  use lhs_left_invert_cell.
  apply is_invertible_2cell_rassociator.
  cbn.
  apply pathsinv0.
  apply runitor_rwhisker.
Qed.

Corollary unit_triangle {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : rassociator f (identity b) g • id2 f ⋆ lunitor g = runitor f ⋆ id2 g.
Proof.
  unfold hcomp.
  rewrite id2_rwhisker.
  rewrite lwhisker_id2.
  rewrite id2_right.
  rewrite id2_left.
  apply lunitor_lwhisker.
Qed.

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

Lemma is_invertible_2cell_lunitor {a b : C} (f : C ⟦ a, b ⟧)
  : is_invertible_2cell (lunitor f).
Proof.
  exists (linvunitor f).
  abstract (apply (lunitor_linvunitor _ ,, linvunitor_lunitor _)).
Defined.

Lemma is_invertible_2cell_linvunitor {a b : C} (f : C ⟦ a, b ⟧)
  : is_invertible_2cell (linvunitor f).
Proof.
  exists (lunitor f).
  abstract (apply (linvunitor_lunitor _ ,, lunitor_linvunitor _)).
Defined.

Lemma is_invertible_2cell_runitor {a b : C} (f : C ⟦ a, b ⟧)
  : is_invertible_2cell (runitor f).
Proof.
  exists (rinvunitor f).
  abstract (apply (runitor_rinvunitor _ ,, rinvunitor_runitor _)).
Defined.

Lemma is_invertible_2cell_rinvunitor {a b : C} (f : C ⟦ a, b ⟧)
  : is_invertible_2cell (rinvunitor f).
Proof.
  exists (runitor f).
  abstract (apply (rinvunitor_runitor _ ,, runitor_rinvunitor _)).
Defined.

Lemma hcomp_rassoc {a b c d : C}
      (f1 g1 : C ⟦ a, b ⟧) (f2 g2 : C ⟦ b, c ⟧) (f3 g3 : C ⟦ c, d ⟧)
      (x1 : f1 ==> g1) (x2 : f2 ==> g2) (x3 : f3 ==> g3)
  : (x1 ⋆ x2) ⋆ x3 • rassociator g1 g2 g3 =
    rassociator f1 f2 f3 • x1 ⋆ (x2 ⋆ x3).
Proof.
  use lhs_right_invert_cell.
  apply is_invertible_2cell_rassociator.
  etrans; [ | apply vassocr ].
  apply pathsinv0.
  use lhs_left_invert_cell.
  apply is_invertible_2cell_rassociator.
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


(* ----------------------------------------------------------------------------------- *)
(** ** Interchange law                                                                 *)
(* ----------------------------------------------------------------------------------- *)

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


Lemma rwhisker_lwhisker_rassociator
      (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : c --> d) (x : g ==> h)
  : rassociator _ _ _ • (f ◃ (x ▹ i)) = ((f ◃ x) ▹ i) • rassociator _ _ _ .
Proof.
  apply (vcomp_lcancel (lassociator f g i)).
  { apply  is_invertible_2cell_lassociator. }
  etrans. etrans. apply vassocr. apply maponpaths_2. apply lassociator_rassociator.
  etrans. apply id2_left.

  apply (vcomp_rcancel (lassociator f h i)).
  { apply  is_invertible_2cell_lassociator. }
  apply pathsinv0.
  etrans. apply vassocl.
  etrans. apply maponpaths. apply vassocl.
  etrans. do 2 apply maponpaths. apply  rassociator_lassociator.
  etrans. apply maponpaths. apply id2_right.
  apply pathsinv0, rwhisker_lwhisker.
Qed.

(** Analog to law 8, lwhisker_lwhisker *)
Lemma lwhisker_lwhisker_rassociator (a b c d : C) (f : C⟦a, b⟧)
      (g : C⟦b, c⟧) (h i : c --> d) (x : h ==> i)
  : rassociator f g h  • (f ◃ (g ◃ x)) = (f · g ◃ x) • rassociator _ _ _ .
Proof.
  apply (vcomp_lcancel (lassociator f g h)).
  { apply  is_invertible_2cell_lassociator. }
  etrans. etrans. apply vassocr. apply maponpaths_2. apply lassociator_rassociator.
  etrans. apply id2_left.

  apply (vcomp_rcancel (lassociator f g i)).
  { apply  is_invertible_2cell_lassociator. }
  apply pathsinv0.
  etrans. apply vassocl.
  etrans. apply maponpaths. apply vassocl.
  etrans. do 2 apply maponpaths. apply  rassociator_lassociator.
  etrans. apply maponpaths. apply id2_right.
  apply pathsinv0, lwhisker_lwhisker.
Qed.

(** Analog to [rwhisker_rwhisker]. *)
Lemma rwhisker_rwhisker_alt {a b c d : C}
      (f : C ⟦ b, a ⟧) (g : C ⟦ c, b ⟧) {h i : C ⟦ d, c ⟧} (x : h ==> i)
  : ((x ▹ g) ▹ f) • rassociator i g f = rassociator h g f • (x ▹ g · f).
Proof.
  apply (vcomp_lcancel (lassociator h g f)).
  { apply is_invertible_2cell_lassociator. }
  etrans. { apply vassocr. }
  etrans. { apply maponpaths_2, rwhisker_rwhisker. }
  etrans. { apply vassocl. }
  etrans. { apply maponpaths, lassociator_rassociator. }
  apply pathsinv0.
  etrans. { apply vassocr. }
  etrans. { apply maponpaths_2, lassociator_rassociator. }
  etrans.
  - apply id2_left.
  - apply pathsinv0, id2_right.
Qed.

Lemma rassociator_rassociator {a b c d e : C}
      (f : C ⟦ a, b ⟧) (g : C ⟦ b, c ⟧) (h : C ⟦ c, d ⟧) (i : C ⟦ d, e ⟧)
  : ((rassociator f g h ▹ i) • rassociator f (g · h) i) • (f ◃ rassociator g h i) =
    rassociator (f · g) h i • rassociator f g (h · i).
Proof.
  apply (vcomp_lcancel (lassociator (f · g) h i)).
  { apply is_invertible_2cell_lassociator. }
  apply (vcomp_lcancel (lassociator f g (h · i))).
  { apply is_invertible_2cell_lassociator. }
  etrans. { apply vassocr. }
  etrans.
  { apply maponpaths_2, pathsinv0.
    apply lassociator_lassociator. }
  etrans. { apply vassocl. }
  etrans.
  { apply maponpaths.
    etrans.
    { apply maponpaths, vassocl. }
    etrans. { apply vassocr. }
    apply maponpaths_2.
    etrans. { apply rwhisker_vcomp. }
    apply maponpaths, lassociator_rassociator.
  }
  apply pathsinv0.
  etrans.
  { apply maponpaths.
    etrans. { apply vassocr. }
    etrans. { apply maponpaths_2, lassociator_rassociator. }
    apply id2_left. }
  etrans.
  apply lassociator_rassociator.
  apply pathsinv0.
  etrans.
  { apply maponpaths.
    etrans.
    { apply vassocr. }
    apply maponpaths_2.
    etrans. { apply maponpaths_2, id2_rwhisker. }
    apply id2_left.
  }
  etrans.
  apply vassocl.
  etrans.
  apply maponpaths.
  etrans.
  apply vassocr.
  etrans.
  apply maponpaths_2.
  apply lassociator_rassociator.
  apply id2_left.
  etrans.
  apply lwhisker_vcomp.
  etrans.
  apply maponpaths.
  apply lassociator_rassociator.
  apply lwhisker_id2.
Qed.

Corollary associativity_pentagon {a b c d e : C}
  (f : C ⟦ a, b ⟧) (g : C ⟦ b, c ⟧) (h : C ⟦ c, d ⟧) (i : C ⟦ d, e ⟧)
  : (rassociator f g h ⋆ id2 i • rassociator f (g · h) i) • id2  f ⋆ rassociator g h i =
    rassociator (f · g) h i • rassociator f g (h · i).
Proof.
  unfold hcomp.
  rewrite id2_rwhisker.
  rewrite lwhisker_id2.
  rewrite id2_right.
  rewrite id2_left.
  apply rassociator_rassociator.
Qed.

End Derived_laws.

(* ----------------------------------------------------------------------------------- *)
(** ** Homs are categories                                                             *)
(* ----------------------------------------------------------------------------------- *)

Section Hom_Spaces.

Context {C : prebicat} (a b : C).

Definition hom_ob_mor
  : precategory_ob_mor
  := make_precategory_ob_mor (C⟦a,b⟧) (λ (f g : C⟦a,b⟧), f ==> g).

Definition hom_data
  : precategory_data
  := make_precategory_data hom_ob_mor id2 (λ f g h x y, x • y).

Lemma is_precategory_hom : is_precategory hom_data.
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat split; cbn.
  - intros f g. apply id2_left.
  - intros f g. apply id2_right.
  - intros f g h i. apply vassocr.
Defined.

Definition hom
  : precategory
  := make_precategory hom_data is_precategory_hom.

End Hom_Spaces.

(* ----------------------------------------------------------------------------------- *)
(** ** Functor structure on horizontal composition.                                    *)
(* ----------------------------------------------------------------------------------- *)

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
  split; red; cbn.
  - intros (f1, f2). cbn. apply hcomp_identity.
  - intros (f1, f2) (g1, g2) (h1, h2).
    unfold precategory_binproduct_mor. cbn.
    intros (x1, x2) (y1, y2). cbn. apply hcomp_vcomp.
Qed.

Definition hcomp_functor
  : precategory_binproduct (hom a b) (hom b c) ⟶ hom a c
  := make_functor hcomp_functor_data is_functor_hcomp.

End hcomp_functor.

(* ----------------------------------------------------------------------------------- *)
(** ** Chaotic bicat                                                                   *)
(* ----------------------------------------------------------------------------------- *)

Section chaotic_bicat.

Variable C : precategory.

Definition chaotic_prebicat_data : prebicat_data.
Proof.
  use tpair.
  - use tpair.
    + exact C.
    + cbn. intros a b f g. exact unit.
  - cbn; repeat (use tpair); cbn; intros; exact tt.
Defined.

Definition chaotic_prebicat_laws : prebicat_laws chaotic_prebicat_data.
Proof.
  repeat apply make_dirprod; intros; apply isProofIrrelevantUnit.
Qed.

Definition chaotic_prebicat : prebicat
  := chaotic_prebicat_data,, chaotic_prebicat_laws.

Lemma isaset_chaotic_cells : isaset_cells chaotic_prebicat.
Proof.
  red. cbn. intros. exact isasetunit.
Qed.

Definition chaotic_bicat : bicat
  := chaotic_prebicat,, isaset_chaotic_cells.

End chaotic_bicat.

(* ----------------------------------------------------------------------------------- *)
(** ** Discrete bicat                                                                  *)
(* ----------------------------------------------------------------------------------- *)

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
    + intros. apply (! assoc _ _ _).
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
  - intros. induction x. cbn. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x. cbn. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x. cbn. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x; cbn. apply (pathscomp0rid).
  - intros. induction x; induction y; cbn. apply idpath.
  - intros. apply pathsinv0r.
  - intros. apply pathsinv0l.
  - intros. apply pathsinv0r.
  - intros. apply pathsinv0l.
  - intros. apply pathsinv0r.
  - intros. apply pathsinv0l.
  - intros. apply homset_property.
  - intros. apply homset_property.
Qed.

Definition discrete_prebicat : prebicat := _ ,, discrete_prebicat_laws.

End discrete_bicat.

Definition id2toequiv {C : prebicat} {a b : C} {f g : a --> b}
  : f = g -> f ==> g.
Proof.
  intro e. induction e. apply id2.
Defined.

Definition is_discrete_prebicat (C : prebicat) : UU
  := ∏ (a b : C) (f g : a --> b), isweq (λ e : f = g, id2toequiv e).

Lemma is_discrete_discrete_prebicat (C : category)
  : is_discrete_prebicat (discrete_prebicat C).
Proof.
  intros a b f g.
  use weqhomot.
  - exact (idweq _).
  - intro e. induction e. apply idpath.
Qed.

(* ----------------------------------------------------------------------------------- *)
(** ** Associators and unitors are isos.                                               *)
(* ----------------------------------------------------------------------------------- *)

Section Associators_Unitors_Iso.

Context {C : prebicat}.

Lemma is_iso_lassociator {a b c d : C} (f : hom a b) (g : hom b c) (h : hom c d)
  : is_iso (lassociator f g h : (hom a d) ⟦ f · (g · h), (f · g) · h ⟧).
Proof.
  apply is_iso_from_is_z_iso.
  exists (rassociator f g h).
  split.
  - apply lassociator_rassociator.
  - apply rassociator_lassociator.
Defined.

Lemma is_iso_rassociator {a b c d : C} (f : hom a b) (g : hom b c) (h : hom c d)
  : is_iso (rassociator f g h : (hom a d) ⟦ (f · g) · h, f · (g · h) ⟧).
Proof.
  apply is_iso_from_is_z_iso.
  exists (lassociator f g h).
  split.
  - apply rassociator_lassociator.
  - apply lassociator_rassociator.
Defined.

Lemma is_iso_lunitor {a b : C} (f : hom a b)
  : is_iso (lunitor f : (hom a b) ⟦ identity a · f, f ⟧).
Proof.
  apply is_iso_from_is_z_iso.
  exists (linvunitor f).
  split.
  - apply lunitor_linvunitor.
  - apply linvunitor_lunitor.
Defined.

Lemma is_iso_runitor {a b : C} (f : hom a b)
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
(** ** Functor structure on associators and unitors.                                   *)
(* ----------------------------------------------------------------------------------- *)

Section Associators_Unitors_Natural.

Context {C : prebicat}.

(* -----------------------------------------------------------------------------------*)
(** Left unitor                                                                       *)
(* -----------------------------------------------------------------------------------*)

Lemma lunitor_natural (a b : C) (f g : C ⟦ a, b ⟧) (x : f ==> g)
  : id2 (identity a) ⋆ x • lunitor g = lunitor f • x.
Proof.
  unfold hcomp.
  rewrite <- vassocr. rewrite vcomp_lunitor.
  rewrite vassocr. apply maponpaths_2.
  rewrite id2_rwhisker. apply id2_left.
Qed.

Definition lunitor_transf (a b : C)
  : bindelta_pair_functor
      (constant_functor (hom a b) (hom a a) (identity a))
      (functor_identity (hom a b)) ∙
    hcomp_functor
    ⟹
    functor_identity (hom a b)
  := lunitor,, lunitor_natural a b.

(* -----------------------------------------------------------------------------------*)
(** Right unitor                                                                      *)
(* -----------------------------------------------------------------------------------*)

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
Qed.

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

(* -----------------------------------------------------------------------------------*)
(** Left associator.                                                                  *)
(* -----------------------------------------------------------------------------------*)

Definition lassociator_fun {a b c d : C}
           (x : C⟦a,b⟧ × C⟦b,c⟧ × C⟦c,d⟧)
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
  unfold precategory_binproduct_mor, hom_ob_mor. cbn.
  unfold precategory_binproduct_mor, hom_ob_mor. cbn.
  intros (x1, (x2, x3)). cbn.
  unfold lassociator_fun. cbn.
  apply hcomp_lassoc.
Qed.

Definition lassociator_transf (a b c d : C)
  : pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor
    ⟹
    precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
    pair_functor hcomp_functor (functor_identity (hom c d)) ∙
    hcomp_functor
  := lassociator_fun,, lassociator_fun_natural.

(* -----------------------------------------------------------------------------------*)
(** Right associator.                                                                 *)
(* -----------------------------------------------------------------------------------*)

Definition rassociator_fun {a b c d : C}
           (x : C⟦a,b⟧ × C⟦b,c⟧ × C⟦c,d⟧)
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
  unfold precategory_binproduct_mor, hom_ob_mor. cbn.
  unfold precategory_binproduct_mor, hom_ob_mor. cbn.
  intros (x1, (x2, x3)). cbn.
  unfold rassociator_fun. cbn.
  apply hcomp_rassoc.
Qed.

Definition rassociator_transf (a b c d : C)
  : precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
    pair_functor hcomp_functor (functor_identity (hom c d)) ∙
    hcomp_functor
    ⟹
    pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor
  := rassociator_fun,, rassociator_fun_natural.

Definition rassociator_fun' {a b c d : C}
           (x : (C⟦a,b⟧ × C⟦b,c⟧) × C⟦c,d⟧)
  : (pr11 x · pr21 x) · pr2 x ==> pr11 x · (pr21 x · pr2 x)
  := rassociator (pr11 x) (pr21 x) (pr2 x).

Lemma rassociator_fun'_natural {a b c d : C}
  : is_nat_trans
      (pair_functor hcomp_functor (functor_identity (hom c d)) ∙ hcomp_functor)
      (precategory_binproduct_unassoc (hom a b) (hom b c) (hom c d) ∙
       pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor)
      rassociator_fun'.
Proof.
  red; cbn. intros ((f1, f2), f3) ((g1, g2), g3).
  unfold precategory_binproduct_mor, hom_ob_mor. cbn.
  unfold precategory_binproduct_mor, hom_ob_mor. cbn.
  intros ((x1, x2), x3). cbn.
  unfold rassociator_fun. cbn.
  apply hcomp_rassoc.
Qed.

Definition rassociator_transf' (a b c d : C)
  : pair_functor hcomp_functor (functor_identity (hom c d)) ∙
    hcomp_functor
    ⟹
    precategory_binproduct_unassoc (hom a b) (hom b c) (hom c d) ∙
    pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor
  := rassociator_fun',, rassociator_fun'_natural.

End Associators_Unitors_Natural.

(* -----------------------------------------------------------------------------------*)
(** ** Notations.                                                                     *)
(* -----------------------------------------------------------------------------------*)

Module Notations.

Notation "f '==>' g" := (prebicat_cells _ f g) (at level 60).
Notation "f '<==' g" := (prebicat_cells _ g f) (at level 60, only parsing).
Notation "x • y" := (vcomp2 x y) (at level 60).
Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)
Notation "f ◅ x" := (rwhisker f x) (at level 60, only parsing). (* \tw nr 5*)
Notation "y ▻ g" := (lwhisker g y) (at level 60, only parsing). (* \tw nr 6 *)
Notation "x ⋆ y" := (hcomp x y) (at level 50, left associativity).
Notation "x 'o' y" := (y • x) (at level 67, only parsing, left associativity).
Notation "'id₁'" := identity.
Notation "'id₂'" := id2.
Notation " b ⋆⋆ a" := (a ⋆ b) (at level 30).
Open Scope bicategory_scope.

End Notations.
