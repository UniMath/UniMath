(* ******************************************************************************* *)
(** * Displayed bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

  This file develops displayed bicategories analogous to
  displayed (1-)categories as presented in
  Benedikt Ahrens and Peter LeFanu Lumsdaine, Displayed categories
  http://dx.doi.org/10.4230/LIPIcs.FSCD.2017.5


 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor.

Open Scope cat.
Open Scope mor_disp_scope.

(* =================================================================================== *)
(** ** Miscellanea.                                                                    *)
(* =================================================================================== *)

Definition transportf_transpose_alt {X : UU} {P : X → UU}
           {x x' : X} {e : x = x'} {y : P x} {y' : P x'} {p : y = transportb P e y'}
  : transportf P e y = y'
  := !transportf_transpose _ _ _ (!p).

(* =================================================================================== *)
(** ** Definition of displayed bicategories.                                           *)
(* =================================================================================== *)

Section disp_bicat.

Context {C : prebicat}.

Definition disp_2cell_struct (D : disp_cat_ob_mor C) : UU
  := ∏ (c c' : C) (f g : C⟦c, c'⟧) (x : f ==> g)
       (d : D c) (d' : D c') (f' : d -->[f] d') (g' : d -->[g] d'), UU.

Definition disp_prebicat_1_id_comp_cells : UU := ∑ D : disp_cat_data C, disp_2cell_struct D.
Coercion disp_cat_data_from_disp_prebicat_1_id_comp_cells (C : disp_prebicat_1_id_comp_cells)
  : disp_cat_data _ := pr1 C.

Definition disp_2cells {D : disp_prebicat_1_id_comp_cells}
           {c c' : C} {f g : C⟦c, c'⟧} (x : f ==> g)
           {d : D c} {d' : D c'} (f' : d -->[f] d') (g' : d -->[g] d')
  : UU
  := pr2 D c c' f g x d d' f' g'.

Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).


Definition disp_prebicat_ops (D : disp_prebicat_1_id_comp_cells) : UU
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


Definition disp_prebicat_data : UU
  := ∑ D : disp_prebicat_1_id_comp_cells,
           disp_prebicat_ops D.

Coercion disp_prebicat_ob_mor_cells_1_id_comp_from_disp_prebicat_data
         (D : disp_prebicat_data)
  : disp_prebicat_1_id_comp_cells
  := pr1 D.
Coercion disp_prebicat_ops_from_disp_prebicat_data (D : disp_prebicat_data)
  : disp_prebicat_ops D
  := pr2 D.


Section disp_prebicat_ops_projections.

Context {D : disp_prebicat_data}.

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

End disp_prebicat_ops_projections.

Notation "rr •• ss" := (vcomp2_disp rr ss) (at level 60).
Notation "ff ◃◃ rr" := (lwhisker_disp ff rr) (at level 60).
Notation "rr ▹▹ gg" := (rwhisker_disp gg rr) (at level 60).

Section disp_prebicat_laws.

Context (D : disp_prebicat_data).

Definition id2_disp_left_law : UU
  := ∏ (a b : C) (f g : C⟦a, b⟧) (η : f ==> g)
      (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
      (ηη : ff ==>[η] gg),
      id2_disp _ •• ηη = transportb (fun x' => _ ==>[x'] _ ) (id2_left _) ηη.

Definition id2_disp_right_law : UU
  := ∏ (a b : C) (f g : C⟦a, b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
       ηη •• id2_disp _ = transportb (λ x', _ ==>[x'] _ ) (id2_right _) ηη.

Definition vassocr_disp_law : UU
  := ∏ (a b : C) (f g h k : C⟦a, b⟧) (η : f ==> g) (φ : g ==> h) (ψ : h ==> k)
      (x : D a) (y : D b)
      (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y) (kk : x -->[k] y)
      (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk),
     ηη •• (φφ •• ψψ) = transportb (λ x', _ ==>[x'] _ ) (vassocr _ _ _ ) ((ηη •• φφ) •• ψψ).


Definition lwhisker_id2_disp_law : UU
  := ∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧)
       (x : D a) (y : D b) (z : D c) (ff : x -->[f] y) (gg : y -->[g] z),
     ff ◃◃ id2_disp gg = transportb (λ x', _ ==>[x'] _) (lwhisker_id2 _ _) (id2_disp (ff ;; gg)).

Definition id2_rwhisker_disp_law : UU
  := ∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧)
       (x : D a) (y : D b) (z : D c) (ff : x -->[f] y) (gg : y -->[g] z),
     id2_disp ff ▹▹ gg = transportb (λ x', _ ==>[x'] _) (id2_rwhisker _ _) (id2_disp (ff ;; gg)).

Definition lwhisker_vcomp_disp_law : UU
  := ∏ (a b c : C) (f : C⟦a, b⟧) (g h i : C⟦b, c⟧)
      (η : g ==> h) (φ : h ==> i)
      (x : D a) (y : D b) (z : D c) (ff : x -->[f] y)
      (gg : y -->[g] z) (hh : y -->[h] z) (ii : y -->[i] z)
      (ηη : gg ==>[η] hh) (φφ : hh ==>[φ] ii),
     (ff ◃◃ ηη) •• (ff ◃◃ φφ) = transportb (λ x', _ ==>[x'] _) (lwhisker_vcomp _ _ _ ) (ff ◃◃ (ηη •• φφ)).

Definition rwhisker_vcomp_disp_law : UU
  := ∏ (a b c : C) (f g h : C⟦a, b⟧) (i : C⟦b, c⟧) (η : f ==> g) (φ : g ==> h)
       (x : D a) (y : D b) (z : D c)
       (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y)
       (ii : y -->[i] z)
       (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh),
     (ηη ▹▹ ii) •• (φφ ▹▹ ii) = transportb (λ x', _ ==>[x'] _) (rwhisker_vcomp _ _ _ ) ((ηη •• φφ) ▹▹ ii).

Definition vcomp_lunitor_disp_law : UU
  := ∏ (a b : C) (f g : C⟦a, b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     (id_disp _ ◃◃ ηη) •• lunitor_disp gg =
     transportb (λ x', _ ==>[x'] _) (vcomp_lunitor _ _ _ ) (lunitor_disp ff •• ηη).

Definition vcomp_runitor_disp_law : UU
  := ∏ (a b : C) (f g : C⟦a, b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     (ηη ▹▹ id_disp _) •• runitor_disp gg =
     transportb (λ x', _ ==>[x'] _) (vcomp_runitor _ _ _ ) (runitor_disp ff •• ηη).

Definition lwhisker_lwhisker_disp_law : UU
  := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h i : c --> d) (η : h ==> i)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z) (ii : y -->[i] z)
       (ηη : hh ==>[η] ii),
     ff ◃◃ (gg ◃◃ ηη) •• lassociator_disp _ _ _ =
     transportb (λ x', _ ==>[x'] _) (lwhisker_lwhisker _ _ _ )
                (lassociator_disp _ _ _ •• (ff ;; gg ◃◃ ηη)).

Definition rwhisker_lwhisker_disp_law : UU
  := ∏ (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : c --> d) (η : g ==> h)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : x -->[h] y) (ii : y -->[i] z)
       (ηη : gg ==>[η] hh),
     (ff ◃◃ (ηη ▹▹ ii)) •• lassociator_disp _ _ _ =
     transportb (λ x', _ ==>[x'] _) (rwhisker_lwhisker _ _ _)
                (lassociator_disp _ _ _ •• ((ff ◃◃ ηη) ▹▹ ii)).

Definition rwhisker_rwhisker_disp_law : UU
  := ∏ (a b c d : C) (f g : C⟦a, b⟧) (h : C⟦b, c⟧) (i : c --> d) (η : f ==> g)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : w -->[g] x) (hh : x -->[h] y) (ii : y -->[i] z)
       (ηη : ff ==>[η] gg),
     lassociator_disp _ _ _ •• ((ηη ▹▹ hh) ▹▹ ii) =
     transportb (λ x', _ ==>[x'] _) (rwhisker_rwhisker _ _ _ ) ((ηη ▹▹ hh ;; ii) •• lassociator_disp _ _ _ ).

Definition vcomp_whisker_disp_law : UU
  := ∏ (a b c : C) (f g : C⟦a, b⟧) (h i : C⟦b, c⟧)
       (η : f ==> g) (φ : h ==> i)
       (x : D a) (y : D b) (z : D c)
       (ff : x -->[f] y) (gg : x -->[g] y)
       (hh : y -->[h] z) (ii : y -->[i] z)
       (ηη : ff ==>[η] gg) (φφ : hh ==>[φ] ii),
     (ηη ▹▹ hh) •• (gg ◃◃ φφ) =
     transportb (λ x', _ ==>[x'] _) (vcomp_whisker _ _ ) ((ff ◃◃ φφ) •• (ηη ▹▹ ii)).

Definition lunitor_linvunitor_disp_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     lunitor_disp ff •• linvunitor_disp _ =
     transportb (λ x', _ ==>[x'] _) (lunitor_linvunitor _ ) (id2_disp (id_disp _ ;; ff)).

Definition linvunitor_lunitor_disp_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     linvunitor_disp ff •• lunitor_disp _ =
     transportb (λ x', _ ==>[x'] _) (linvunitor_lunitor _ ) (id2_disp _).

Definition runitor_rinvunitor_disp_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     runitor_disp ff •• rinvunitor_disp _ =
     transportb (λ x', _ ==>[x'] _) (runitor_rinvunitor _ ) (id2_disp _ ).

Definition rinvunitor_runitor_disp_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     rinvunitor_disp ff •• runitor_disp _ =
     transportb (λ x', _ ==>[x'] _) (rinvunitor_runitor _ ) (id2_disp _).

Definition lassociator_rassociator_disp_law : UU
  := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y)
       (hh : y -->[h] z),
     lassociator_disp ff gg hh •• rassociator_disp _ _ _ =
     transportb (λ x', _ ==>[x'] _) (lassociator_rassociator _ _ _  ) (id2_disp  _ ).

Definition rassociator_lassociator_disp_law : UU
  := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y)
       (hh : y -->[h] z),
     rassociator_disp ff gg hh •• lassociator_disp _ _ _ =
     transportb (λ x', _ ==>[x'] _) (rassociator_lassociator _ _ _  ) (id2_disp _).

Definition runitor_rwhisker_disp_law : UU
  := ∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧)
       (x : D a) (y : D b) (z : D c)
       (ff : x -->[f] y) (gg : y -->[g] z),
     lassociator_disp _ _ _ •• (runitor_disp ff ▹▹ gg) =
     transportb (λ x', _ ==>[x'] _) (runitor_rwhisker _ _ ) (ff ◃◃ lunitor_disp gg).

Definition lassociator_lassociator_disp_law : UU
  := ∏ (a b c d e: C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d) (i : C⟦d, e⟧)
       (v : D a) (w : D b) (x : D c) (y : D d) (z : D e)
       (ff : v -->[f] w) (gg : w -->[g] x)
       (hh : x -->[h] y) (ii : y -->[i] z),

     (ff ◃◃ lassociator_disp gg hh ii) •• lassociator_disp _ _ _ •• (lassociator_disp _ _ _ ▹▹ ii) =
     transportb (λ x', _ ==>[x'] _) (lassociator_lassociator _ _ _ _ )
                (lassociator_disp ff gg _ •• lassociator_disp _ _ _).


Definition disp_prebicat_laws : UU
  :=
    id2_disp_left_law
      × id2_disp_right_law
      × vassocr_disp_law
      × lwhisker_id2_disp_law
      × id2_rwhisker_disp_law
      × lwhisker_vcomp_disp_law
      × rwhisker_vcomp_disp_law
      × vcomp_lunitor_disp_law
      × vcomp_runitor_disp_law
      × lwhisker_lwhisker_disp_law
      × rwhisker_lwhisker_disp_law
      × rwhisker_rwhisker_disp_law
      × vcomp_whisker_disp_law
      × lunitor_linvunitor_disp_law
      × linvunitor_lunitor_disp_law
      × runitor_rinvunitor_disp_law
      × rinvunitor_runitor_disp_law
      × lassociator_rassociator_disp_law
      × rassociator_lassociator_disp_law
      × runitor_rwhisker_disp_law
      × lassociator_lassociator_disp_law.

End disp_prebicat_laws.

Definition disp_prebicat : UU := ∑ D : disp_prebicat_data, disp_prebicat_laws D.
Coercion disp_prebicat_data_from_disp_prebicat (D : disp_prebicat) : disp_prebicat_data := pr1 D.

Section disp_prebicat_law_projections.

Context {D : disp_prebicat}.

Definition id2_disp_left
           {a b : C} {f g : C⟦a, b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : id2_disp _ •• ηη = transportb (fun x' => _ ==>[x'] _ ) (id2_left _) ηη
  := pr1 (pr2 D) _ _ _ _ _ x y ff gg ηη.

Definition id2_disp_right
           {a b : C} {f g : C⟦a, b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : ηη •• id2_disp _ = transportb (λ x', _ ==>[x'] _ ) (id2_right _) ηη
  := pr1 (pr2 (pr2 D)) _ _ _ _ _ _ _ _ _ ηη.

Definition vassocr_disp
           {a b : C} {f g h k : C⟦a, b⟧} {η : f ==> g} {φ : g ==> h} {ψ : h ==> k}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {kk : x -->[k] y}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk)
  : ηη •• (φφ •• ψψ) = transportb (λ x', _ ==>[x'] _ ) (vassocr _ _ _ ) ((ηη •• φφ) •• ψψ)
  := pr1 (pr2 (pr2 (pr2 D))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ ψψ .

Definition vassocr'_disp
           {a b : C} {f g h k : C⟦a, b⟧} {η : f ==> g} {φ : g ==> h} {ψ : h ==> k}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {kk : x -->[k] y}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk)
  : transportf (λ x', _ ==>[x'] _ ) (vassocr _ _ _ ) (ηη •• (φφ •• ψψ)) =
    ((ηη •• φφ) •• ψψ).
Proof.
  use (transportf_transpose_alt (P := λ x' : f ==> k, ff ==>[ x'] kk)).
  apply vassocr_disp.
Defined.

Definition lwhisker_id2_disp
           {a b c : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧}
           {x : D a} {y : D b} {z : D c} (ff : x -->[f] y) (gg : y -->[g] z)
  : ff ◃◃ id2_disp gg = transportb (λ x', _ ==>[x'] _) (lwhisker_id2 _ _) (id2_disp (ff ;; gg))
  := pr1 (pr2 (pr2 (pr2 (pr2 D)))) _ _ _ _ _ _ _ _ ff gg.

Definition id2_rwhisker_disp
           {a b c : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) (gg : y -->[g] z)
  : id2_disp ff ▹▹ gg = transportb (λ x', _ ==>[x'] _) (id2_rwhisker _ _) (id2_disp (ff ;; gg))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 D))))) _ _ _ _ _ _ _ _ ff gg.

Definition lwhisker_vcomp_disp
           {a b c : C} {f : C⟦a, b⟧} {g h i : C⟦b, c⟧}
           {η : g ==> h} {φ : h ==> i}
           {x : D a} {y : D b} {z : D c} {ff : x -->[f] y}
           {gg : y -->[g] z} {hh : y -->[h] z} {ii : y -->[i] z}
           (ηη : gg ==>[η] hh) (φφ : hh ==>[φ] ii)
  : (ff ◃◃ ηη) •• (ff ◃◃ φφ) = transportb (λ x', _ ==>[x'] _) (lwhisker_vcomp _ _ _ ) (ff ◃◃ (ηη •• φφ))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ.

Definition rwhisker_vcomp_disp
           {a b c : C} {f g h : C⟦a, b⟧} {i : C⟦b, c⟧} {η : f ==> g} {φ : g ==> h}
           {x : D a} {y : D b} {z : D c}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y}
           {ii : y -->[i] z}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh)
  : (ηη ▹▹ ii) •• (φφ ▹▹ ii) = transportb (λ x', _ ==>[x'] _) (rwhisker_vcomp _ _ _ ) ((ηη •• φφ) ▹▹ ii)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ.

Definition vcomp_lunitor_disp
           {a b : C} {f g : C⟦a, b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : (id_disp _ ◃◃ ηη) •• lunitor_disp gg =
    transportb (λ x', _ ==>[x'] _) (vcomp_lunitor _ _ _ ) (lunitor_disp ff •• ηη)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))) _ _ _ _ _ _ _ _ _  ηη.

Definition vcomp_runitor_disp
           {a b : C} {f g : C⟦a, b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : (ηη ▹▹ id_disp _) •• runitor_disp gg =
    transportb (λ x', _ ==>[x'] _) (vcomp_runitor _ _ _ ) (runitor_disp ff •• ηη)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))) _ _ _ _ _ _ _ _ _  ηη.

Definition lwhisker_lwhisker_disp
           {a b c d : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧} {h i : c --> d} {η : h ==> i}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y) {hh : y -->[h] z} {ii : y -->[i] z}
           (ηη : hh ==>[η] ii)
  : ff ◃◃ (gg ◃◃ ηη) •• lassociator_disp _ _ _ =
    transportb (λ x', _ ==>[x'] _) (lwhisker_lwhisker _ _ _ )
               (lassociator_disp _ _ _ •• (ff ;; gg ◃◃ ηη))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))) _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ ηη.

Definition rwhisker_lwhisker_disp
           {a b c d : C} {f : C⟦a, b⟧} {g h : C⟦b, c⟧} {i : c --> d} {η : g ==> h}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) {gg : x -->[g] y} {hh : x -->[h] y} (ii : y -->[i] z)
           (ηη : gg ==>[η] hh)
  : (ff ◃◃ (ηη ▹▹ ii)) •• lassociator_disp _ _ _ =
    transportb (λ x', _ ==>[x'] _) (rwhisker_lwhisker _ _ _)
               (lassociator_disp _ _ _ •• ((ff ◃◃ ηη) ▹▹ ii))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))) _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ ηη.


Definition rwhisker_rwhisker_disp
           {a b c d : C} {f g : C⟦a, b⟧} {h : C⟦b, c⟧} (i : c --> d) (η : f ==> g)
           {w : D a} {x : D b} {y : D c} {z : D d}
           {ff : w -->[f] x} {gg : w -->[g] x} (hh : x -->[h] y) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg)
  : lassociator_disp _ _ _ •• ((ηη ▹▹ hh) ▹▹ ii) =
    transportb (λ x', _ ==>[x'] _) (rwhisker_rwhisker _ _ _ ) ((ηη ▹▹ hh ;; ii) •• lassociator_disp _ _ _ )
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))) _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ ηη.


Definition vcomp_whisker_disp
           {a b c : C} {f g : C⟦a, b⟧} {h i : C⟦b, c⟧}
           (η : f ==> g) (φ : h ==> i)
           (x : D a) (y : D b) (z : D c)
           (ff : x -->[f] y) (gg : x -->[g] y)
           (hh : y -->[h] z) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg) (φφ : hh ==>[φ] ii)
  : (ηη ▹▹ hh) •• (gg ◃◃ φφ) =
    transportb (λ x', _ ==>[x'] _) (vcomp_whisker _ _ ) ((ff ◃◃ φφ) •• (ηη ▹▹ ii))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ.


Definition lunitor_linvunitor_disp
           {a b : C} {f : C⟦a, b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : lunitor_disp ff •• linvunitor_disp _ =
    transportb (λ x', _ ==>[x'] _) (lunitor_linvunitor _ ) (id2_disp (id_disp _ ;; ff))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))) _ _ _ _ _ ff.

Definition linvunitor_lunitor_disp
           {a b : C} {f : C⟦a, b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : linvunitor_disp ff •• lunitor_disp _ =
    transportb (λ x', _ ==>[x'] _) (linvunitor_lunitor _ ) (id2_disp _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))) _ _ _ _ _ ff.


Definition runitor_rinvunitor_disp
           {a b : C} {f : C⟦a, b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : runitor_disp ff •• rinvunitor_disp _ =
    transportb (λ x', _ ==>[x'] _) (runitor_rinvunitor _ ) (id2_disp _ )
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))))) _ _ _ _ _ ff.


Definition rinvunitor_runitor_disp
           {a b : C} {f : C⟦a, b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : rinvunitor_disp ff •• runitor_disp _ =
    transportb (λ x', _ ==>[x'] _) (rinvunitor_runitor _ ) (id2_disp _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))) _ _ _ _ _ ff.


Definition lassociator_rassociator_disp
           {a b c d : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧} {h : c --> d}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y)
           (hh : y -->[h] z)
  : lassociator_disp ff gg hh •• rassociator_disp _ _ _ =
    transportb (λ x', _ ==>[x'] _) (lassociator_rassociator _ _ _  ) (id2_disp  _ )
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))))))) _ _ _ _ _ _ _ _ _ _ _ ff gg hh.

Definition rassociator_lassociator_disp
           {a b c d : C} (f : C⟦a, b⟧) {g : C⟦b, c⟧} {h : c --> d}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y)
           (hh : y -->[h] z)
  : rassociator_disp ff gg hh •• lassociator_disp _ _ _ =
    transportb (λ x', _ ==>[x'] _) (rassociator_lassociator _ _ _  ) (id2_disp _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))))) _ _ _ _ _ _ _ _ _ _ _ ff gg hh.

Definition runitor_rwhisker_disp
           {a b c : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) (gg : y -->[g] z)
  : lassociator_disp _ _ _ •• (runitor_disp ff ▹▹ gg) =
    transportb (λ x', _ ==>[x'] _) (runitor_rwhisker _ _ ) (ff ◃◃ lunitor_disp gg)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))))))))) _ _ _ _ _ _ _ _ ff gg.


Definition lassociator_lassociator_disp
           {a b c d e: C} {f : C⟦a, b⟧} {g : C⟦b, c⟧} {h : c --> d} {i : C⟦d, e⟧}
           {v : D a} {w : D b} {x : D c} {y : D d} {z : D e}
           (ff : v -->[f] w) (gg : w -->[g] x)
           (hh : x -->[h] y) (ii : y -->[i] z)
  : (ff ◃◃ lassociator_disp gg hh ii) •• lassociator_disp _ _ _ •• (lassociator_disp _ _ _ ▹▹ ii) =
     transportb (λ x', _ ==>[x'] _) (lassociator_lassociator _ _ _ _ )
                (lassociator_disp ff gg _ •• lassociator_disp _ _ _)
  := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))))))))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff gg hh ii.

End disp_prebicat_law_projections.

Lemma vassocl_disp {D : disp_prebicat}
      {a b : C} {f g h k : C⟦a, b⟧} {η : f ==> g} {φ : g ==> h} {ψ : h ==> k}
      {x : D a} {y : D b}
      {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {kk : x -->[k] y}
      (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk)
  : (ηη •• φφ) •• ψψ = transportb (λ x', _ ==>[x'] _ ) (vassocl _ _ _ ) (ηη •• (φφ •• ψψ)).
Proof.
  apply (transportf_transpose (P := λ x', _ ==>[x'] _ )).
  apply pathsinv0.
  etrans.
  apply vassocr_disp.
  apply maponpaths_2.
  unfold vassocl.
  apply pathsinv0, pathsinv0inv0.
Qed.


  Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
  Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).
  Notation "rr •• ss" := (vcomp2_disp rr ss) (at level 60).

Section Display_Invertible_2cell.
  Context {D : disp_prebicat}.

  Section Def_inv_2cell.

  Context {c c' : C} {f f' : C⟦c,c'⟧}
          {d : D c} {d' : D c'}.

  Definition is_disp_invertible_2cell'
             {α : invertible_2cell f f'}
             {ff : d -->[f] d'} {ff' : d -->[f'] d'}
             (x : ff ==>[α] ff')
    : UU
    := ∑ (y : ff' ==>[inv_invertible_2cell α] ff),
       (x •• y =
        transportb (λ x', _ ==>[x'] _) (invertible_2cell_after_inv_cell α)  (id2_disp ff)) ×
       (y •• x =
        transportb (λ x', _ ==>[x'] _) (inv_cell_after_invertible_2cell α)  (id2_disp ff')).

  Definition is_disp_invertible_2cell
             {α : f ==> f'}
             (Hα : is_invertible_2cell α)
             {ff : d -->[f] d'} {ff' : d -->[f'] d'}
             (x : ff ==>[α] ff')
    : UU
    := ∑ (y : ff' ==>[inv_invertible_2cell (α,,Hα)] ff),
       (x •• y =
        transportb (λ x', _ ==>[x'] _) (invertible_2cell_after_inv_cell (α,,Hα))  (id2_disp ff)) ×
       (y •• x =
        transportb (λ x', _ ==>[x'] _) (inv_cell_after_invertible_2cell (α,,Hα))  (id2_disp ff')).

  Definition disp_invertible_2cell (α : invertible_2cell f f')
             (ff : d -->[f] d') (ff' : d -->[f'] d')
    : UU
    := ∑ (x : ff ==>[α] ff'), is_disp_invertible_2cell (pr2 α) x.

  Coercion disp_cell_from_invertible_2cell {α : invertible_2cell f f'}
           {ff : d -->[f] d'} {ff' : d -->[f'] d'}
           (e : disp_invertible_2cell α ff ff')
    : ff ==>[α] ff'
    := pr1 e.

  Definition inv_disp_cell {α : invertible_2cell f f'}
             {ff : d -->[f] d'} {ff' : d -->[f'] d'}
             (e : disp_invertible_2cell α ff ff')
    : ff' ==>[inv_cell α] ff
    := pr1 (pr2 e).

  Definition inv_cell_after_disp_invertible_2cell {α : invertible_2cell f f'}
             {ff : d -->[f] d'} {ff' : d -->[f'] d'}
             (e : disp_invertible_2cell α ff ff')
    : e •• inv_disp_cell e =
      transportb (λ x', _ ==>[x'] _) (invertible_2cell_after_inv_cell α)  (id2_disp ff)
    := pr1 (pr2 (pr2 e)).

  Definition disp_invertible_2cell_after_inv_cell {α : invertible_2cell f f'}
             {ff : d -->[f] d'} {ff' : d -->[f'] d'}
             (e : disp_invertible_2cell α ff ff')
    : inv_disp_cell e •• e =
      transportb (λ x', _ ==>[x'] _) (inv_cell_after_invertible_2cell α)  (id2_disp ff')
    := pr2 (pr2 (pr2 e)).

  End Def_inv_2cell.

  Lemma mor_disp_transportf_postwhisker_disp (a b : C)
        {x y z : C⟦a,b⟧} {f f' : x ==> y} (ef : f = f') {g : y ==> z}
        {aa : D a} {bb : D b}
        {xx : aa -->[x] bb} {yy} {zz} (ff : xx ==>[f] yy) (gg : yy ==>[g] zz)
    : (transportf (λ x, _ ==>[x] _) ef ff) •• gg
      = transportf (λ x, _ ==>[x] _) (maponpaths (λ h, h • g) ef) (ff •• gg).
  Proof.
    destruct ef; apply idpath.
  Qed.

  Lemma mor_disp_transportf_prewhisker_disp (a b : C)
        {x y z : C⟦a,b⟧} {f : x ==> y} {g g' : y ==> z} (ef : g = g')
        {aa : D a} {bb : D b}
        {xx : aa -->[x] bb} {yy} {zz} (ff : xx ==>[f] yy) (gg : yy ==>[g] zz)
    : ff •• (transportf (λ x, _ ==>[x] _) ef gg)
      = transportf (λ x, _ ==>[x] _) (maponpaths (λ h, f • h) ef) (ff •• gg).
  Proof.
    destruct ef; apply idpath.
  Qed.

  Lemma disp_cell_to_inv_cell_post' {a b : C} {f g h : a --> b}
        {x : f ==> g} {y : invertible_2cell g h} {z : f ==> h}
        {p : x = z • inv_cell y}
        {aa : D a} {bb : D b}
        {ff : aa -->[f] bb}
        {gg : aa -->[g] bb}
        {hh : aa -->[h] bb}
        (xx : ff ==>[x] gg)
        (yy : gg ==>[y] hh)
        (zz : ff ==>[z] hh)
        (H : is_disp_invertible_2cell y yy)
        (q := cell_to_inv_cell_post _ _ _ _ p)
        (pp : xx = transportb (λ x, _ ==>[x] _) p (zz •• inv_disp_cell (yy,,H)))
    : xx •• yy = transportb (λ x, _ ==>[x] _) q zz.
  Proof.
    set (yy' := (yy,,H) : disp_invertible_2cell _ _ _).
    etrans. apply maponpaths_2. apply pp.
    etrans. apply mor_disp_transportf_postwhisker_disp.
    etrans. apply maponpaths. apply vassocl_disp.
    etrans. unfold transportb. apply (transport_f_f (λ x' : f ==> h, ff ==>[ x'] hh)).
    etrans. apply maponpaths. apply maponpaths.
    apply disp_invertible_2cell_after_inv_cell.
    etrans. apply maponpaths.
    apply mor_disp_transportf_prewhisker_disp.
    etrans. unfold transportb. apply (transport_f_f (λ x' : f ==> h, ff ==>[ x'] hh)).
    etrans. apply maponpaths.
    apply id2_disp_right.
    etrans. unfold transportb. apply (transport_f_f (λ x' : f ==> h, ff ==>[ x'] hh)).
    unfold transportb.
    apply maponpaths_2.
    admit.  (* Todo: remove this admit using homcells. *)
  Admitted.

  Lemma disp_cell_to_inv_cell_post {a b : C} {f g h : a --> b}
        {x : f ==> g} {y : g ==> h} {z : f ==> h}
        (Hy : is_invertible_2cell y)
        {aa : D a} {bb : D b}
        {ff : aa -->[f] bb}
        {gg : aa -->[g] bb}
        {hh : aa -->[h] bb}
        (xx : ff ==>[x] gg)
        (yy : gg ==>[y] hh)
        (zz : ff ==>[z] hh)
        (H : is_disp_invertible_2cell Hy yy)
        (q : x • y = z)
        (p  := rhs_inv_cell_right _ _ _ Hy q : x = z • inv_cell (y,,Hy) )
        (pp : xx = transportb (λ x, _ ==>[x] _) p (zz •• inv_disp_cell ((yy,,H):disp_invertible_2cell (y,,Hy) gg hh)))
    : xx •• yy = transportb (λ x, _ ==>[x] _) q zz.
  Proof.
    etrans.
    use (disp_cell_to_inv_cell_post' _ _ _ _ pp).
    apply maponpaths_2.
    admit.
  Admitted.

  (*
  Lemma inv_cell_to_cell_post {a b : C} {f g h : a --> b} (x : f ==> g) (y : g ==> h)
        (z : f ==> h)
        (H : is_invertible_2cell x)
    : y = inv_cell (x,,H) • z -> x • y = z.
  Proof.
    intro H1.
    etrans. apply maponpaths. apply H1.
    etrans. apply ( vassocr _ _ _ ).
    etrans. apply maponpaths_2. apply (invertible_2cell_after_inv_cell (x,,H)).
    apply id2_left.
  Qed.
  *)

  Lemma disp_inv_cell_to_cell_post {a b : C} {f g h : a --> b}
        {x : f ==> g} {y : g ==> h} {z : f ==> h} {H : is_invertible_2cell x}
        {aa : D a} {bb : D b}
        {ff : aa -->[f] bb}
        {gg : aa -->[g] bb}
        {hh : aa -->[h] bb}
        (xx : ff ==>[x] gg)
        (yy : gg ==>[y] hh)
        (zz : ff ==>[z] hh)
        (HH : is_disp_invertible_2cell H xx)
        (q :  x • y = z)
        (p := rhs_inv_cell_left _ _ _ H q : y = inv_cell (x,,H) • z)
        (pp : yy = transportb
                     (λ x, _ ==>[x] _) p
                     (inv_disp_cell ((xx,,HH):disp_invertible_2cell (x,,H) ff gg) •• zz))
    : xx •• yy = transportb (λ x, _ ==>[x] _) q zz.
  Proof.
    etrans. apply maponpaths. apply pp.
    etrans.
    apply mor_disp_transportf_prewhisker_disp.
    etrans. apply maponpaths.
    apply vassocr_disp.
    etrans. apply (transport_f_f (λ x, _ ==>[x] _)).
    etrans. apply maponpaths.
    apply maponpaths_2.
    apply (inv_cell_after_disp_invertible_2cell ((xx,,HH):disp_invertible_2cell (x,,H) _ _)).
    etrans. apply maponpaths. apply mor_disp_transportf_postwhisker_disp.
    etrans. unfold transportb. apply (transport_f_f (λ x, _ ==>[x] _)).
    etrans. apply maponpaths. apply id2_disp_left.
    etrans. unfold transportb. apply (transport_f_f (λ x, _ ==>[x] _)).
    unfold transportb.
    apply maponpaths_2. admit.
  Admitted.

End Display_Invertible_2cell.

Section Derived_Laws.

Context {D : disp_prebicat}.

Definition is_disp_invertible_2cell_lassociator {a b c d : C}
           {f1 : C ⟦ a, b ⟧} {f2 : C ⟦ b, c ⟧} {f3 : C ⟦ c, d ⟧}
           {aa : D a} {bb : D b} {cc : D c} {dd : D d}
           (ff1 : aa -->[f1] bb)
           (ff2 : bb -->[f2] cc)
           (ff3 : cc -->[f3] dd)
  : is_disp_invertible_2cell (is_invertible_2cell_lassociator _ _ _)
                             (lassociator_disp ff1 ff2 ff3).
Proof.
  exists (rassociator_disp ff1 ff2 ff3).
  split.
  - apply lassociator_rassociator_disp.
  - apply rassociator_lassociator_disp.
Defined.

Definition is_disp_invertible_2cell_rassociator {a b c d : C}
           {f1 : C ⟦ a, b ⟧} {f2 : C ⟦ b, c ⟧} {f3 : C ⟦ c, d ⟧}
           {aa : D a} {bb : D b} {cc : D c} {dd : D d}
           (ff1 : aa -->[f1] bb)
           (ff2 : bb -->[f2] cc)
           (ff3 : cc -->[f3] dd)
  : is_disp_invertible_2cell (is_invertible_2cell_rassociator _ _ _)
                             (rassociator_disp ff1 ff2 ff3).
Proof.
  exists (lassociator_disp ff1 ff2 ff3).
  split.
  - apply rassociator_lassociator_disp.
  - apply lassociator_rassociator_disp.
Defined.


(*
Lemma lassociator_to_rassociator_post {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      (x : k ==> (f · g) · h)
      (y : k ==> f · (g · h))
      (p : x = y • lassociator f g h)
  : x • rassociator f g h = y.
  *)

Lemma lassociator_to_rassociator_post_disp' {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      {x : k ==> (f · g) · h}
      {y : k ==> f · (g · h)}
      (p : x = y • lassociator f g h)
      {aa : D a} {bb : D b} {cc : D c} {dd : D d}
      {ff : aa -->[f] bb}
      {gg : bb -->[g] cc}
      {hh : cc -->[h] dd}
      {kk : aa -->[k] dd}
      (xx : kk ==>[x] (ff ;; gg) ;; hh)
      (yy : kk ==>[y] ff ;; (gg ;; hh))
      (q := lassociator_to_rassociator_post x y p)
      (pp : xx = transportb (λ x, _ ==>[x] _) p (yy •• lassociator_disp ff gg hh))
  : xx •• rassociator_disp ff gg hh = transportb (λ x, _ ==>[x] _) q (yy).
Proof.
  etrans.
  use disp_cell_to_inv_cell_post.
  - exact y.
  - apply is_invertible_2cell_rassociator.
  - exact yy.
  - apply is_disp_invertible_2cell_rassociator.
  - apply lassociator_to_rassociator_post. exact p.
  - cbn. etrans. apply pp.
    apply maponpaths_2.
    admit.
Admitted.

Search (_ • lassociator _ _ _) rassociator.

Lemma lassociator_to_rassociator_post_disp {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      {x : k ==> (f · g) · h}
      {y : k ==> f · (g · h)}
      {aa : D a} {bb : D b} {cc : D c} {dd : D d}
      {ff : aa -->[f] bb}
      {gg : bb -->[g] cc}
      {hh : cc -->[h] dd}
      {kk : aa -->[k] dd}
      (xx : kk ==>[x] (ff ;; gg) ;; hh)
      (yy : kk ==>[y] ff ;; (gg ;; hh))
      (q : x • rassociator f g h = y)
      (p := rassociator_to_lassociator_post _ _ q : x = y • lassociator f g h)
      (pp : xx = transportb (λ x, _ ==>[x] _) p (yy •• lassociator_disp ff gg hh))
  : xx •• rassociator_disp ff gg hh = transportb (λ x, _ ==>[x] _) q (yy).
Proof.
  etrans.
  use lassociator_to_rassociator_post_disp'.
  - exact y.
  - exact p.
  - exact yy.
  - exact pp.
  - apply maponpaths_2. admit.
Admitted.

Lemma lassociator_to_rassociator_pre_disp {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      {x : f · (g · h) ==> k}
      {y : (f · g) · h ==> k}
      {aa : D a} {bb : D b} {cc : D c} {dd : D d}
      {ff : aa -->[f] bb}
      {gg : bb -->[g] cc}
      {hh : cc -->[h] dd}
      {kk : aa -->[k] dd}
      (xx : ff ;; (gg ;; hh) ==>[x] kk)
      (yy : (ff ;; gg) ;; hh ==>[y] kk)
      (q : rassociator f g h • x = y)
      (p := rassociator_to_lassociator_pre _ _ q : x = lassociator f g h • y)
      (pp : xx = transportb (λ x, _ ==>[x] _) p (lassociator_disp ff gg hh •• yy))
  : rassociator_disp ff gg hh •• xx = transportb (λ x, _ ==>[x] _) q (yy).
Proof.
  etrans.
  Search (_ •• _ = _) (inv_disp_cell _).
  use disp_cell_to_inv_cell_post.
  - exact x.
  - apply is_invertible_2cell_lassociator.
  - exact yy.
  - apply is_disp_invertible_2cell_rassociator.
  - apply lassociator_to_rassociator_post. exact p.
  - cbn. etrans. apply pp.
    apply maponpaths_2.
    admit.
Admitted.

Proof.
  use inv_cell_to_cell_post.
  - apply is_invertible_rassociator.
  - exact p.
Defined.


*)

Lemma lunitor_lwhisker_disp {a b c : C} {f : C⟦a, b⟧} {g : C⟦b, c⟧}
      {aa : D a} {bb : D b} {cc : D c}
      (ff : aa -->[f] bb)
      (gg : bb -->[g] cc)
  : (rassociator_disp _ _ _ •• (ff ◃◃ lunitor_disp gg)) =
    transportb (λ x', _ ==>[x'] _)
               (lunitor_lwhisker _ _)
               (runitor_disp ff ▹▹ gg).
Proof.
  etrans.
  use lassociator_to_rassociator_pre_disp.
  apply pathsinv0.
  apply runitor_rwhisker.
Qed.
 *)

End Derived_Laws.

Section total_bicat.

Variable D : disp_prebicat.

(** TODO : think how to unify with total_category_ob_mor

    possible once https://github.com/UniMath/UniMath/pull/902
    is merged

*)
Definition total_prebicat_ob_mor : precategory_ob_mor.
Proof.
  exists (∑ x:C, D x).
  intros xx yy.
  exact (∑ (f : pr1 xx --> pr1 yy), pr2 xx -->[f] pr2 yy).
Defined.

Definition total_category_id_comp : precategory_id_comp (total_prebicat_ob_mor).
Proof.
  apply tpair; simpl.
  - intros.
    exists (identity _ ).
    apply id_disp.
  - intros xx yy zz ff gg.
    exists (pr1 ff · pr1 gg).
    exact (pr2 ff ;; pr2 gg).
Defined.

Definition total_prebicat_1_data : precategory_data := _ ,, total_category_id_comp.

Definition total_prebicat_cell_struct : prebicat_2cell_struct total_prebicat_ob_mor
  := λ a b f g, ∑ η : pr1 f ==> pr1 g, pr2 f ==>[η] pr2 g.

Definition total_prebicat_1_id_comp_cells : prebicat_1_id_comp_cells
  := (total_prebicat_1_data,, total_prebicat_cell_struct).

Definition total_prebicat_2_id_comp_struct : prebicat_2_id_comp_struct total_prebicat_1_id_comp_cells.
Proof.
  repeat split; cbn; unfold total_prebicat_cell_struct.
  - intros. exists (id2 _ ). exact (id2_disp _ ).
  - intros. exists (lunitor _ ). exact (lunitor_disp _ ).
  - intros. exists (runitor _ ). exact (runitor_disp _ ).
  - intros. exists (linvunitor _ ). exact (linvunitor_disp _ ).
  - intros. exists (rinvunitor _ ). exact (rinvunitor_disp _ ).
  - intros. exists (rassociator _ _ _ ).
    exact (rassociator_disp _ _ _ ).
  - intros. exists (lassociator _ _ _ ).
    exact (lassociator_disp _ _ _ ).
  - intros a b f g h r s. exists (pr1 r • pr1 s).
    exact (pr2 r •• pr2 s).
  - intros a b d f g1 g2 r. exists (pr1 f ◃ pr1 r).
    exact (pr2 f ◃◃ pr2 r).
  - intros a b c f1 f2 g r. exists (pr1 r ▹ pr1 g).
    exact (pr2 r ▹▹ pr2 g).
Defined.

Definition total_prebicat_data : prebicat_data := _ ,, total_prebicat_2_id_comp_struct.

Lemma total_prebicat_laws : prebicat_laws total_prebicat_data.
Proof.
  repeat split; intros.
  - use total2_paths_b.
    + apply id2_left.
    + apply id2_disp_left.
  - use total2_paths_b.
    + apply id2_right.
    + apply id2_disp_right.
  - use total2_paths_b.
    + apply vassocr.
    + apply vassocr_disp.
  - use total2_paths_b.
    + apply lwhisker_id2.
    + apply lwhisker_id2_disp.
  - use total2_paths_b.
    + apply id2_rwhisker.
    + apply id2_rwhisker_disp.
  - use total2_paths_b.
    + apply lwhisker_vcomp.
    + apply lwhisker_vcomp_disp.
  - use total2_paths_b.
    + apply rwhisker_vcomp.
    + apply rwhisker_vcomp_disp.
  - use total2_paths_b.
    + apply vcomp_lunitor.
    + apply vcomp_lunitor_disp.
  - use total2_paths_b.
    + apply vcomp_runitor.
    + apply vcomp_runitor_disp.
  - use total2_paths_b.
    + apply lwhisker_lwhisker.
    + apply lwhisker_lwhisker_disp.
  - use total2_paths_b.
    + apply rwhisker_lwhisker.
    + apply rwhisker_lwhisker_disp.
  - use total2_paths_b.
    + apply rwhisker_rwhisker.
    + apply rwhisker_rwhisker_disp.
  - use total2_paths_b.
    + apply vcomp_whisker.
    + apply vcomp_whisker_disp.
  - use total2_paths_b.
    + apply lunitor_linvunitor.
    + apply lunitor_linvunitor_disp.
  - use total2_paths_b.
    + apply linvunitor_lunitor.
    + apply linvunitor_lunitor_disp.
  - use total2_paths_b.
    + apply runitor_rinvunitor.
    + apply runitor_rinvunitor_disp.
  - use total2_paths_b.
    + apply rinvunitor_runitor.
    + apply rinvunitor_runitor_disp.
  - use total2_paths_b.
    + apply lassociator_rassociator.
    + apply lassociator_rassociator_disp.
  - use total2_paths_b.
    + apply rassociator_lassociator.
    + apply rassociator_lassociator_disp.
  - use total2_paths_b.
    + apply runitor_rwhisker.
    + apply runitor_rwhisker_disp.
  - use total2_paths_b.
    + apply lassociator_lassociator.
    + apply lassociator_lassociator_disp.
Defined.

Definition total_bicat : prebicat := _ ,, total_prebicat_laws.

Definition pr1_psfunctor_ob_mor_cell : psfunctor_ob_mor_cell total_prebicat_data C.
Proof.
  use tpair.
  - use tpair.
    + exact pr1.
    + intros a b. exact pr1.
  - intros a b f g. exact pr1.
Defined.

Definition pr1_psfunctor_cell_data : psfunctor_cell_data pr1_psfunctor_ob_mor_cell.
Proof.
  use tpair.
  - intro a. cbn.
    apply id2_invertible_2cell.
  - cbn. intros a b c f g.
    apply id2_invertible_2cell.
Defined.

Definition pr1_psfunctor_data : psfunctor_data total_prebicat_data C := _ ,, pr1_psfunctor_cell_data.

Definition pr1_psfunctor_laws : psfunctor_laws pr1_psfunctor_data.
Proof.
  repeat split; intro a; intros; cbn.
  - rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite id2_left.
    apply idpath.
  - rewrite lwhisker_id2.
    rewrite id2_left.
    rewrite id2_left.
    apply idpath.
  - rewrite id2_rwhisker.
    rewrite id2_right.
    rewrite id2_right.
    apply idpath.
  - rewrite lwhisker_id2.
    rewrite id2_right.
    rewrite id2_right.
    apply idpath.
  - rewrite id2_right.
    rewrite id2_left.
    rewrite id2_rwhisker.
    rewrite id2_left.
    rewrite lwhisker_id2.
    rewrite id2_right.
    apply idpath.
  - rewrite id2_right.
    rewrite id2_left.
    rewrite id2_rwhisker.
    rewrite lwhisker_id2.
    rewrite id2_left.
    rewrite id2_right.
    apply idpath.
  - rewrite id2_right.
    rewrite id2_left.
    apply idpath.
  - rewrite id2_left.
    rewrite id2_right.
    apply idpath.
Qed.

End total_bicat.

End disp_bicat.

Arguments disp_prebicat_1_id_comp_cells _ : clear implicits.
Arguments disp_prebicat_data _ : clear implicits.
Arguments disp_prebicat _ : clear implicits.
