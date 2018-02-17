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


Definition disp_bicat_data : UU
  := ∑ D : disp_bicat_ob_mor_cells_1_id_comp,
           disp_bicat_ops D.

Coercion disp_bicat_ob_mor_cells_1_id_comp_from_disp_bicat_data
         (D : disp_bicat_data)
  : disp_bicat_ob_mor_cells_1_id_comp
  := pr1 D.
Coercion disp_bicat_ops_from_disp_bicat_data (D : disp_bicat_data)
  : disp_bicat_ops D
  := pr2 D.


Section disp_bicat_ops_projections.

Context {D : disp_bicat_data}.

Definition id2_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ==>[id2 _ ] f'
  := pr1 (pr2 D) a b f x y f'.

Definition lunitor_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : id_disp x ;; f' ==>[lunitor _ ] f'
  := pr1 (pr2 (pr2 D)) a b f x y f'.

Definition runitor_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ;; id_disp y ==>[runitor _ ] f'
  := pr1 (pr2 (pr2 (pr2 D))) _ _ f _ _ f'.

Definition linvunitor_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : id_disp x ;; f' <==[linvunitor _ ] f'
  := pr1 (pr2 (pr2 (pr2 (pr2 D)))) _ _ f _ _ f'.

Definition rinvunitor_disp
           {a b : C} {f : C⟦a, b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ;; id_disp y <==[rinvunitor _ ] f'
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 D))))) _ _ f _ _ f'.

Definition rassociator_disp
           {a b c d : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧} {h : C⟦c, d⟧}
       {w : D a} {x : D b} {y : D c} {z : D d}
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : (ff ;; gg) ;; hh ==>[ rassociator _ _ _  ] ff ;; (gg ;; hh)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.

Definition lassociator_disp
           {a b c d : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧} {h : C⟦c, d⟧}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : ff ;; (gg ;; hh) ==>[ lassociator _ _ _  ] (ff ;; gg) ;; hh
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.

Definition vcomp2_disp
           {a b : C} {f g h : C⟦a, b⟧}
           {r : f ==> g} {s : g ==> h}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y}
  : ff ==>[r] gg  →  gg ==>[s] hh  →  ff ==>[ r • s ] hh
  := λ rr ss,  pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))) _ _ _ _ _ _ _ _ _ _ _ _ rr ss.

Definition lwhisker_disp
           {a b c : C} {f : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
           {r : g1 ==> g2}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) {gg1 : y -->[g1] z} {gg2 : y -->[g2] z}
  : gg1 ==>[r] gg2  →  ff ;; gg1  ==>[f ◃ r] ff ;; gg2
  := λ rr, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))) _ _ _ _ _ _ _ _ _ _ _ _ _ rr.

Definition rwhisker_disp
           {a b c : C} {f1 f2 : C⟦a, b⟧} {g : C⟦b, c⟧}
           {r : f1 ==> f2}
           {x : D a} {y : D b} {z : D c}
           {ff1 : x -->[f1] y} {ff2 : x -->[f2] y} (gg : y -->[g] z)
  : ff1 ==>[r] ff2 → ff1 ;; gg ==>[ r ▹ g ] ff2 ;; gg
  := λ rr, pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))) _ _ _ _ _ _ _ _ _ _ _ _ _ rr.

End disp_bicat_ops_projections.

Notation "rr •• ss" := (vcomp2_disp rr ss) (at level 60).
Notation "ff ◃◃ rr" := (lwhisker_disp ff rr) (at level 60).
Notation "rr ▹▹ gg" := (rwhisker_disp gg rr) (at level 60).

Section disp_bicat_laws.

Context (D : disp_bicat_data).

Definition id2_disp_left_law
           {a b : C} {f g : C⟦a, b⟧} (η : f ==> g)
           (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
           (ηη : ff ==>[η] gg)
  : UU
  := id2_disp _ •• ηη = transportb (fun x' => _ ==>[x'] _ ) (id2_left _) ηη.

Definition id2_disp_right_law
           {a b : C} {f g : C⟦a, b⟧} (η : f ==> g)
           (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
           (ηη : ff ==>[η] gg)
  : UU
  := ηη •• id2_disp _ = transportb (λ x', _ ==>[x'] _ ) (id2_right _) ηη.

Definition vassocr_disp_law
           {a b : C} {f g h k : C⟦a, b⟧} (η : f ==> g) (φ : g ==> h) (ψ : h ==> k)
           (x : D a) (y : D b)
           (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y) (kk : x -->[k] y)
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk)
  : UU
  := ηη •• (φφ •• ψψ) = transportb (λ x', _ ==>[x'] _ ) (vassocr _ _ _ ) ((ηη •• φφ) •• ψψ).


Definition lwhisker_id2_disp_law
           {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
           (x : D a) (y : D b) (z : D c) (ff : x -->[f] y) (gg : y -->[g] z)
  : UU
  := ff ◃◃ id2_disp gg = transportb (λ x', _ ==>[x'] _) (lwhisker_id2 _ _) (id2_disp (ff ;; gg)).

Definition id2_rwhisker_disp_law
           {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
           (x : D a) (y : D b) (z : D c) (ff : x -->[f] y) (gg : y -->[g] z)
  : UU
  := id2_disp ff ▹▹ gg = transportb (λ x', _ ==>[x'] _) (id2_rwhisker _ _) (id2_disp (ff ;; gg)).

Definition lwhisker_vcomp_disp_law
           {a b c : C} (f : C⟦a, b⟧) {g h i : C⟦b, c⟧}
           (η : g ==> h) (φ : h ==> i)
           (x : D a) (y : D b) (z : D c) (ff : x -->[f] y)
           (gg : y -->[g] z) (hh : y -->[h] z) (ii : y -->[i] z)
           (ηη : gg ==>[η] hh) (φφ : hh ==>[φ] ii)
  : UU
  := (ff ◃◃ ηη) •• (ff ◃◃ φφ) = transportb (λ x', _ ==>[x'] _) (lwhisker_vcomp _ _ _ ) (ff ◃◃ (ηη •• φφ)).

Definition rwhisker_vcomp_disp_law
           {a b c : C} {f g h : C⟦a, b⟧} (i : C⟦b, c⟧) (η : f ==> g) (φ : g ==> h)
           (x : D a) (y : D b) (z : D c)
           (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y)
           (ii : y -->[i] z)
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh)
  : UU
  :=
    (ηη ▹▹ ii) •• (φφ ▹▹ ii) = transportb (λ x', _ ==>[x'] _) (rwhisker_vcomp _ _ _ ) ((ηη •• φφ) ▹▹ ii).

Definition vcomp_lunitor_disp_law
           {a b : C} (f g : C⟦a, b⟧) (η : f ==> g)
           (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
           (ηη : ff ==>[η] gg)
  : UU
  := (id_disp _ ◃◃ ηη) •• lunitor_disp gg =
     transportb (λ x', _ ==>[x'] _) (vcomp_lunitor _ _ _ ) (lunitor_disp ff •• ηη).

Definition vcomp_runitor_disp_law
           {a b : C} (f g : C⟦a, b⟧) (η : f ==> g)
           (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
           (ηη : ff ==>[η] gg)
  : UU
  := (ηη ▹▹ id_disp _) •• runitor_disp gg =
     transportb (λ x', _ ==>[x'] _) (vcomp_runitor _ _ _ ) (runitor_disp ff •• ηη).

Definition lwhisker_lwhisker_disp_law
           {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) {h i : c --> d} (η : h ==> i)
           (w : D a) (x : D b) (y : D c) (z : D d)
           (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z) (ii : y -->[i] z)
           (ηη : hh ==>[η] ii)
  : UU
  := ff ◃◃ (gg ◃◃ ηη) •• lassociator_disp _ _ _ =
     transportb (λ x', _ ==>[x'] _) (lwhisker_lwhisker _ _ _ )
                (lassociator_disp _ _ _ •• (ff ;; gg ◃◃ ηη)).

Definition rwhisker_lwhisker_disp_law
           {a b c d : C} (f : C⟦a, b⟧) {g h : C⟦b, c⟧} (i : c --> d) (η : g ==> h)
           (w : D a) (x : D b) (y : D c) (z : D d)
           (ff : w -->[f] x) (gg : x -->[g] y) (hh : x -->[h] y) (ii : y -->[i] z)
           (ηη : gg ==>[η] hh)
  : UU
  := (ff ◃◃ (ηη ▹▹ ii)) •• lassociator_disp _ _ _ =
     transportb (λ x', _ ==>[x'] _) (rwhisker_lwhisker _ _ _)
                (lassociator_disp _ _ _ •• ((ff ◃◃ ηη) ▹▹ ii)).

Definition rwhisker_rwhisker_disp_law
           {a b c d : C} {f g : C⟦a, b⟧} (h : C⟦b, c⟧) (i : c --> d) (η : f ==> g)
           (w : D a) (x : D b) (y : D c) (z : D d)
           (ff : w -->[f] x) (gg : w -->[g] x) (hh : x -->[h] y) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg)
  : UU
  := lassociator_disp _ _ _ •• ((ηη ▹▹ hh) ▹▹ ii) =
     transportb (λ x', _ ==>[x'] _) (rwhisker_rwhisker _ _ _ ) ((ηη ▹▹ hh ;; ii) •• lassociator_disp _ _ _ ).

Definition vcomp_whisker_disp_law
           {a b c : C} {f g : C⟦a, b⟧} {h i : C⟦b, c⟧}
           (η : f ==> g) (φ : h ==> i)
           (x : D a) (y : D b) (z : D c)
           (ff : x -->[f] y) (gg : x -->[g] y)
           (hh : y -->[h] z) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg) (φφ : hh ==>[φ] ii)
  : UU
  := (ηη ▹▹ hh) •• (gg ◃◃ φφ) =
     transportb (λ x', _ ==>[x'] _) (vcomp_whisker _ _ ) ((ff ◃◃ φφ) •• (ηη ▹▹ ii)).
Print lunitor_linvunitor.

Definition lunitor_linvunitor_disp_law
           {a b : C} (f : C⟦a, b⟧)
           (x : D a) (y : D b) (ff : x -->[f] y)
  : UU
  := lunitor_disp ff •• linvunitor_disp _ =
     transportb (λ x', _ ==>[x'] _) (lunitor_linvunitor _ ) (id2_disp (id_disp _ ;; ff)).

Definition linvunitor_lunitor_disp_law
           {a b : C} (f : C⟦a, b⟧)
           (x : D a) (y : D b) (ff : x -->[f] y)
  : UU
  := linvunitor_disp ff •• lunitor_disp _ =
     transportb (λ x', _ ==>[x'] _) (linvunitor_lunitor _ ) (id2_disp _).

Definition runitor_rinvunitor_disp_law
           {a b : C} (f : C⟦a, b⟧)
           (x : D a) (y : D b) (ff : x -->[f] y)
  : UU
  := runitor_disp ff •• rinvunitor_disp _ =
     transportb (λ x', _ ==>[x'] _) (runitor_rinvunitor _ ) (id2_disp _ ).

Definition rinvunitor_runitor_disp_law
           {a b : C} (f : C⟦a, b⟧)
           (x : D a) (y : D b) (ff : x -->[f] y)
  : UU
  := rinvunitor_disp ff •• runitor_disp _ =
     transportb (λ x', _ ==>[x'] _) (rinvunitor_runitor _ ) (id2_disp _).

Definition lassociator_rassociator_disp_law
           {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d)
           (w : D a) (x : D b) (y : D c) (z : D d)
           (ff : w -->[f] x) (gg : x -->[g] y)
           (hh : y -->[h] z)
  : UU
  := lassociator_disp ff gg hh •• rassociator_disp _ _ _ =
     transportb (λ x', _ ==>[x'] _) (lassociator_rassociator _ _ _  ) (id2_disp  _ ).

End disp_bicat_laws.

End disp_bicat.