Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.bicat.bicat.

Open Scope cat.
Open Scope mor_disp_scope.

Section disp_bicat.

Context (C : bicat).

Definition disp_cell_struct (D : disp_cat_ob_mor C) : UU
  := ∏ (c c' : C) (f g : C⟦c, c'⟧) (x : f ==> g)
       (d : D c) (d' : D c') (f' : d -->[f] d') (g' : d -->[g] d'), UU.

Definition disp_bicat_ob_mor_cells : UU
  := ∑ D : disp_cat_ob_mor C, disp_cell_struct D.

Coercion disp_cat_ob_mor_from_disp_bicat_ob_mor_cells (C : disp_bicat_ob_mor_cells)
  : disp_cat_ob_mor _ := pr1 C.

Definition disp_cells {D : disp_bicat_ob_mor_cells}
           {c c' : C} {f g : C⟦c, c'⟧} (x : f ==> g)
           {d : D c} {d' : D c'} (f' : d -->[f] d') (g' : d -->[g] d')
  : UU
  := pr2 D c c' f g x d d' f' g'.

Notation "f' ==>[ x ] g'" := (disp_cells x f' g') (at level 60).
Notation "f' <==[ x ] g'" := (disp_cells x g' f') (at level 60, only parsing).

Definition disp_bicat_ob_mor_cells_1_id_comp : UU := ∑ D : disp_bicat_ob_mor_cells, disp_cat_id_comp _ D.

Coercion disp_cat_data_from_disp_bicat_cells_1_id_comp (D : disp_bicat_ob_mor_cells_1_id_comp)
  : disp_cat_data C.
Proof.
  exists (pr1 D).
  exact (pr2 D).
Defined.



(*
Check (fun (C : category) (D : disp_cat C) a b (f : C⟦a, b⟧)
           x y (ff : x -->[f] y) =>  id_disp _ ;; ff = transportf _ _ ff).
*)

Definition disp_bicat_ops (D : disp_bicat_ob_mor_cells_1_id_comp) : UU
  :=
    (∏ (a b : C) (f : C⟦a, b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
     f' ==>[id2 _ ] f')
      ×
    (∏ (a b : C) (f : C⟦a, b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
     id_disp x ;; f' ==>[lunitor _ ] f')
    ×
    (∏ (a b : C) (f : C⟦a, b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
     f' ;; id_disp y ==>[runitor _ ] f')
    ×
    (∏ (a b : C) (f : C⟦a, b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
     id_disp x ;; f' <==[linvunitor _ ] f')
    ×
    (∏ (a b : C) (f : C⟦a, b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
     f' ;; id_disp y <==[rinvunitor _ ] f')
    ×
    (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z),
     (ff ;; gg) ;; hh ==>[ rassociator _ _ _  ] ff ;; (gg ;; hh))
    ×
    (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z),
     ff ;; (gg ;; hh) ==>[ lassociator _ _ _  ] (ff ;; gg) ;; hh)
    ×
    (∏ (a b : C) (f g h : C⟦a, b⟧)
       (r : f ==> g) (s : g ==> h)
       (x : D a) (y : D b)
       (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y),
     ff ==>[r] gg  →  gg ==>[s] hh  →  ff ==>[ r • s ] hh)
    ×
    (∏ (a b c : C) (f : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧)
         (r : g1 ==> g2)
         (x : D a) (y : D b) (z : D c)
         (ff : x -->[f] y) (gg1 : y -->[g1] z) (gg2 : y -->[g2] z),
     gg1 ==>[r] gg2  →  ff ;; gg1  ==>[f ◃ r] ff ;; gg2)
    ×
    (∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g : C⟦b, c⟧)
       (r : f1 ==> f2)
       (x : D a) (y : D b) (z : D c)
       (ff1 : x -->[f1] y) (ff2 : x -->[f2] y) (gg : y -->[g] z),
     ff1 ==>[r] ff2 → ff1 ;; gg ==>[ r ▹ g ] ff2 ;; gg).


Section disp_bicat_ops_projections.

Context (D : disp_bicat_ob_mor_cells_1_id_comp)
        (T : disp_bicat_ops D).

Definition id2_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ==>[id2 _ ] f'
  := pr1 T a b f x y f'.

Definition lunitor_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : id_disp x ;; f' ==>[lunitor _ ] f'
  := pr1 (pr2 T) a b f x y f'.

Definition runitor_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ;; id_disp y ==>[runitor _ ] f'
  := pr1 (pr2 (pr2 T)) _ _ f _ _ f'.

Definition linvunitor_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : id_disp x ;; f' <==[linvunitor _ ] f'
  := pr1 (pr2 (pr2 (pr2 T))) _ _ f _ _ f'.

Definition rinvunitor_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ;; id_disp y <==[rinvunitor _ ] f'
  := pr1 (pr2 (pr2 (pr2 (pr2 T)))) _ _ f _ _ f'.

Definition rassociator_disp
           {a b c d : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧} {h : C⟦c, d⟧}
       {w : D a} {x : D b} {y : D c} {z : D d}
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : (ff ;; gg) ;; hh ==>[ rassociator _ _ _  ] ff ;; (gg ;; hh)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 T))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.

Definition lassociator_disp
           {a b c d : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧} {h : C⟦c, d⟧}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : ff ;; (gg ;; hh) ==>[ lassociator _ _ _  ] (ff ;; gg) ;; hh
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 T)))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.

Definition vcomp2_disp
           {a b : C} {f g h : C⟦a, b⟧}
           {r : f ==> g} {s : g ==> h}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y}
  : ff ==>[r] gg  →  gg ==>[s] hh  →  ff ==>[ r • s ] hh
  := λ rr ss,  pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 T))))))) _ _ _ _ _ _ _ _ _ _ _ _ rr ss.

Definition lwhisker_disp
           {a b c : C} {f : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
           {r : g1 ==> g2}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) {gg1 : y -->[g1] z} {gg2 : y -->[g2] z}
  : gg1 ==>[r] gg2  →  ff ;; gg1  ==>[f ◃ r] ff ;; gg2
  := λ rr, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 T)))))))) _ _ _ _ _ _ _ _ _ _ _ _ _ rr.

Definition rwhisker_disp
           {a b c : C} {f1 f2 : C⟦a, b⟧} {g : C⟦b, c⟧}
           {r : f1 ==> f2}
           {x : D a} {y : D b} {z : D c}
           {ff1 : x -->[f1] y} {ff2 : x -->[f2] y} (gg : y -->[g] z)
  : ff1 ==>[r] ff2 → ff1 ;; gg ==>[ r ▹ g ] ff2 ;; gg
  := λ rr, pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 T)))))))) _ _ _ _ _ _ _ _ _ _ _ _ _ rr.

End disp_bicat_ops_projections.



End disp_bicat.