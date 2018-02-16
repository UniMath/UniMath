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

Notation "f '-2->' g" := (bicat_cells _ f g) (at level 60).

Definition bicat_cells_1_id_comp : UU := ∑ C : bicat_ob_mor_cells, precategory_id_comp C.

Coercion precat_data_from_bicat_cells_1_id_comp (C : bicat_cells_1_id_comp) : precategory_data.
Proof.
  exists (pr1 C).
  exact (pr2 C).
Defined.

Check (fun (C : bicat_cells_1_id_comp) (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) => f · g).