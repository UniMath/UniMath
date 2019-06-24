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
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(* =================================================================================== *)
(** ** Displayed bicategories.                                                         *)
(* =================================================================================== *)

(* ----------------------------------------------------------------------------------- *)
(** ** Miscellanea.                                                                    *)
(* ----------------------------------------------------------------------------------- *)

Definition transportf_transpose_alt {X : UU} {P : X → UU}
           {x x' : X} {e : x = x'} {y : P x} {y' : P x'} {p : y = transportb P e y'}
  : transportf P e y = y'
  := !transportf_transpose _ _ _ (!p).

(* ----------------------------------------------------------------------------------- *)
(** ** Transport of displayed cells.

    Transport of displayed cells is used pervasively, to make the code more terse
    and ease certain proofs we define some ad hoc functions and theorems.

    TODO: These definitions are not used yet.                                          *)
(* ----------------------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------------------- *)
(** ** Definition of displayed bicategories.                                           *)
(* ----------------------------------------------------------------------------------- *)

Definition disp_2cell_struct {C : prebicat_1_id_comp_cells} (D : disp_cat_ob_mor C) : UU
  := ∏ (c c' : C) (f g : C⟦c,c'⟧) (x : f ==> g)
       (d : D c) (d' : D c') (f' : d -->[f] d') (g' : d -->[g] d'), UU.

Definition disp_prebicat_1_id_comp_cells (C : prebicat_1_id_comp_cells) : UU
  := ∑ D : disp_cat_data C, disp_2cell_struct D.

Coercion disp_cat_data_from_disp_prebicat_1_id_comp_cells
         {C : prebicat_1_id_comp_cells} (D : disp_prebicat_1_id_comp_cells C)
  : disp_cat_data C
  := pr1 D.

Definition disp_2cells {C : prebicat_1_id_comp_cells}
           {D : disp_prebicat_1_id_comp_cells C}
           {c c' : C} {f g : C⟦c,c'⟧} (x : f ==> g)
           {d : D c} {d' : D c'} (f' : d -->[f] d') (g' : d -->[g] d')
  : UU
  := pr2 D c c' f g x d d' f' g'.

Section Cell_Transport.

Context {C : bicat} {D : disp_prebicat_1_id_comp_cells C}.

Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).

Definition cell_transportf
           {a b : C} {f g : C⟦a,b⟧}
           {α β : f ==> g}
           (e : α = β)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : aa -->[g] bb}
           (αα : ff ==>[α] gg)
  : ff ==>[β] gg
  := transportf (λ x : f ==> g, ff ==>[x] gg) e αα.

Definition cell_transportb
           {a b : C} {f g : C⟦a,b⟧}
           {α β : f ==> g}
           (e : α = β)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : aa -->[g] bb}
           (ββ : ff ==>[β] gg)
  : ff ==>[α] gg
  := transportb (λ x : f ==> g, ff ==>[x] gg) e ββ.

Lemma cell_transportf_pathsinv0
      {a b : C} {f g : C⟦a,b⟧}
      {α β : f ==> g}
      (e : α = β)
      {aa : D a} {bb : D b}
      {ff : aa -->[f] bb}
      {gg : aa -->[g] bb}
      {αα : ff ==>[α] gg}
      {ββ : ff ==>[β] gg}
      (ee : cell_transportf (!e) ββ = αα)
  : cell_transportf e αα = ββ.
Proof.
  unfold cell_transportf.
  apply (transportf_pathsinv0 (λ x : f ==> g, ff ==>[x] gg)).
  exact ee.
Defined.

Lemma cell_transportb_to_f
      {a b : C} {f g : C⟦a,b⟧}
      {α β : f ==> g}
      {e : α = β}
      {aa : D a} {bb : D b}
      {ff : aa -->[f] bb}
      {gg : aa -->[g] bb}
      {αα : ff ==>[α] gg}
      {ββ : ff ==>[β] gg}
      (ee : αα = cell_transportb e ββ)
  : cell_transportf e αα = ββ.
Proof.
  apply cell_transportf_pathsinv0.
  apply pathsinv0.
  exact ee.
Defined.

Lemma cell_transportf_to_b
      {a b : C} {f g : C⟦a,b⟧}
      {α β : f ==> g}
      {e : α = β}
      {aa : D a} {bb : D b}
      {ff : aa -->[f] bb}
      {gg : aa -->[g] bb}
      {αα : ff ==>[α] gg}
      {ββ : ff ==>[β] gg}
      (ee : cell_transportf e αα = ββ)
  :  αα = cell_transportb e ββ.
Proof.
  apply pathsinv0.
  apply (transportf_pathsinv0 (λ x : f ==> g, ff ==>[ x] gg)).
  etrans.
  { apply maponpaths_2.
    apply pathsinv0inv0. }
  exact ee.
Defined.

End Cell_Transport.

(* ----------------------------------------------------------------------------------- *)
(** ** Operations on bicategories                                                      *)
(* ----------------------------------------------------------------------------------- *)

Section disp_prebicat.

Context {C : bicat}.

Local Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
Local Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).

Definition disp_prebicat_ops (D : disp_prebicat_1_id_comp_cells C) : UU
  :=   (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        f' ==>[id2 _] f')
     × (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        id_disp x ;; f' ==>[lunitor _] f')
     × (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        f' ;; id_disp y ==>[runitor _] f')
     × (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        id_disp x ;; f' <==[linvunitor _] f')
     × (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        f' ;; id_disp y <==[rinvunitor _] f')
     × (∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : C⟦c,d⟧)
          (w : D a) (x : D b) (y : D c) (z : D d)
          (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z),
        (ff ;; gg) ;; hh ==>[rassociator _ _ _] ff ;; (gg ;; hh))
     × (∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : C⟦c,d⟧)
          (w : D a) (x : D b) (y : D c) (z : D d)
          (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z),
        ff ;; (gg ;; hh) ==>[lassociator _ _ _] (ff ;; gg) ;; hh)
     × (∏ (a b : C) (f g h : C⟦a,b⟧) (r : f ==> g) (s : g ==> h)
          (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y),
        ff ==>[r] gg  →  gg ==>[s] hh  →  ff ==>[r • s] hh)
     × (∏ (a b c : C) (f : C⟦a,b⟧) (g1 g2 : C⟦b,c⟧)
          (r : g1 ==> g2) (x : D a) (y : D b) (z : D c)
          (ff : x -->[f] y) (gg1 : y -->[g1] z) (gg2 : y -->[g2] z),
        gg1 ==>[r] gg2  →  ff ;; gg1  ==>[f ◃ r] ff ;; gg2)
     × (∏ (a b c : C) (f1 f2 : C⟦a,b⟧) (g : C⟦b,c⟧)
          (r : f1 ==> f2) (x : D a) (y : D b) (z : D c)
          (ff1 : x -->[f1] y) (ff2 : x -->[f2] y) (gg : y -->[g] z),
        ff1 ==>[r] ff2 → ff1 ;; gg ==>[r ▹ g] ff2 ;; gg).

Definition disp_prebicat_data : UU
  := ∑ D : disp_prebicat_1_id_comp_cells C, disp_prebicat_ops D.

Coercion disp_prebicat_ob_mor_cells_1_id_comp_from_disp_prebicat_data
         (D : disp_prebicat_data)
  : disp_prebicat_1_id_comp_cells C
  := pr1 D.

Coercion disp_prebicat_ops_from_disp_prebicat_data (D : disp_prebicat_data)
  : disp_prebicat_ops D
  := pr2 D.

(* ----------------------------------------------------------------------------------- *)
(** ** Data projections                                                                *)
(* ----------------------------------------------------------------------------------- *)

Section disp_prebicat_ops_projections.

Context {D : disp_prebicat_data}.

Definition disp_id2 {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ==>[id2 _] f'
  := pr1 (pr2 D) a b f x y f'.

Definition disp_lunitor {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : id_disp x ;; f' ==>[lunitor _] f'
  := pr1 (pr2 (pr2 D)) a b f x y f'.

Definition disp_runitor {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ;; id_disp y ==>[runitor _] f'
  := pr1 (pr2 (pr2 (pr2 D))) _ _ f _ _ f'.

Definition disp_linvunitor
           {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : id_disp x ;; f' <==[linvunitor _] f'
  := pr1 (pr2 (pr2 (pr2 (pr2 D)))) _ _ f _ _ f'.

Definition disp_rinvunitor
           {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ;; id_disp y <==[rinvunitor _] f'
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 D))))) _ _ f _ _ f'.

Definition disp_rassociator
           {a b c d : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧} {h : C⟦c,d⟧}
       {w : D a} {x : D b} {y : D c} {z : D d}
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : (ff ;; gg) ;; hh ==>[rassociator _ _ _] ff ;; (gg ;; hh)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.

Definition disp_lassociator
           {a b c d : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧} {h : C⟦c,d⟧}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : ff ;; (gg ;; hh) ==>[lassociator _ _ _] (ff ;; gg) ;; hh
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.

Definition disp_vcomp2
           {a b : C} {f g h : C⟦a,b⟧}
           {r : f ==> g} {s : g ==> h}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y}
  : ff ==>[r] gg  →  gg ==>[s] hh  →  ff ==>[r • s] hh
  := λ rr ss,  pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))
                   _ _ _ _ _ _ _ _ _ _ _ _ rr ss.

Definition disp_lwhisker
           {a b c : C} {f : C⟦a,b⟧} {g1 g2 : C⟦b,c⟧}
           {r : g1 ==> g2}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) {gg1 : y -->[g1] z} {gg2 : y -->[g2] z}
  : gg1 ==>[r] gg2  →  ff ;; gg1  ==>[f ◃ r] ff ;; gg2
  := λ rr, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))
               _ _ _ _ _ _ _ _ _ _ _ _ _ rr.

Definition disp_rwhisker
           {a b c : C} {f1 f2 : C⟦a,b⟧} {g : C⟦b,c⟧}
           {r : f1 ==> f2}
           {x : D a} {y : D b} {z : D c}
           {ff1 : x -->[f1] y} {ff2 : x -->[f2] y} (gg : y -->[g] z)
  : ff1 ==>[r] ff2 → ff1 ;; gg ==>[r ▹ g] ff2 ;; gg
  := λ rr, pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))
               _ _ _ _ _ _ _ _ _ _ _ _ _ rr.

End disp_prebicat_ops_projections.

Local Notation "rr •• ss" := (disp_vcomp2 rr ss) (at level 60).
Local Notation "ff ◃◃ rr" := (disp_lwhisker ff rr) (at level 60).
Local Notation "rr ▹▹ gg" := (disp_rwhisker gg rr) (at level 60).

Section disp_prebicat_laws.

Context (D : disp_prebicat_data).

Definition disp_id2_left_law : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     disp_id2 _ •• ηη = transportb (λ α, _ ==>[α] _) (id2_left _) ηη.

Definition disp_id2_right_law : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     ηη •• disp_id2 _ = transportb (λ α, _ ==>[α] _) (id2_right _) ηη.

Definition disp_vassocr_law : UU
  := ∏ (a b : C) (f g h k : C⟦a,b⟧) (η : f ==> g) (φ : g ==> h) (ψ : h ==> k)
       (x : D a) (y : D b)
       (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y) (kk : x -->[k] y)
       (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk),
     ηη •• (φφ •• ψψ) =
     transportb (λ α, _ ==>[α] _) (vassocr _ _ _) ((ηη •• φφ) •• ψψ).

Definition disp_lwhisker_id2_law : UU
  := ∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
       (x : D a) (y : D b) (z : D c) (ff : x -->[f] y) (gg : y -->[g] z),
     ff ◃◃ disp_id2 gg =
     transportb (λ α, _ ==>[α] _) (lwhisker_id2 _ _) (disp_id2 (ff ;; gg)).

Definition disp_id2_rwhisker_law : UU
  := ∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
       (x : D a) (y : D b) (z : D c) (ff : x -->[f] y) (gg : y -->[g] z),
     disp_id2 ff ▹▹ gg =
     transportb (λ α, _ ==>[α] _) (id2_rwhisker _ _) (disp_id2 (ff ;; gg)).

Definition disp_lwhisker_vcomp_law : UU
  := ∏ (a b c : C) (f : C⟦a,b⟧) (g h i : C⟦b,c⟧)
      (η : g ==> h) (φ : h ==> i)
      (x : D a) (y : D b) (z : D c) (ff : x -->[f] y)
      (gg : y -->[g] z) (hh : y -->[h] z) (ii : y -->[i] z)
      (ηη : gg ==>[η] hh) (φφ : hh ==>[φ] ii),
     (ff ◃◃ ηη) •• (ff ◃◃ φφ) =
     transportb (λ α, _ ==>[α] _) (lwhisker_vcomp _ _ _) (ff ◃◃ (ηη •• φφ)).

Definition disp_rwhisker_vcomp_law : UU
  := ∏ (a b c : C) (f g h : C⟦a,b⟧) (i : C⟦b,c⟧) (η : f ==> g) (φ : g ==> h)
       (x : D a) (y : D b) (z : D c)
       (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y)
       (ii : y -->[i] z)
       (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh),
     (ηη ▹▹ ii) •• (φφ ▹▹ ii) =
     transportb (λ α, _ ==>[α] _) (rwhisker_vcomp _ _ _) ((ηη •• φφ) ▹▹ ii).

Definition disp_vcomp_lunitor_law : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     (id_disp _ ◃◃ ηη) •• disp_lunitor gg =
     transportb (λ α, _ ==>[α] _) (vcomp_lunitor _ _ _) (disp_lunitor ff •• ηη).

Definition disp_vcomp_runitor_law : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     (ηη ▹▹ id_disp _) •• disp_runitor gg =
     transportb (λ α, _ ==>[α] _) (vcomp_runitor _ _ _) (disp_runitor ff •• ηη).

Definition disp_lwhisker_lwhisker_law : UU
  := ∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h i : c --> d) (η : h ==> i)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z) (ii : y -->[i] z)
       (ηη : hh ==>[η] ii),
     ff ◃◃ (gg ◃◃ ηη) •• disp_lassociator _ _ _ =
     transportb (λ α, _ ==>[α] _) (lwhisker_lwhisker _ _ _)
                (disp_lassociator _ _ _ •• (ff ;; gg ◃◃ ηη)).

Definition disp_rwhisker_lwhisker_law : UU
  := ∏ (a b c d : C) (f : C⟦a,b⟧) (g h : C⟦b,c⟧) (i : c --> d) (η : g ==> h)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : x -->[h] y) (ii : y -->[i] z)
       (ηη : gg ==>[η] hh),
     (ff ◃◃ (ηη ▹▹ ii)) •• disp_lassociator _ _ _ =
     transportb (λ α, _ ==>[α] _) (rwhisker_lwhisker _ _ _)
                (disp_lassociator _ _ _ •• ((ff ◃◃ ηη) ▹▹ ii)).

Definition disp_rwhisker_rwhisker_law : UU
  := ∏ (a b c d : C) (f g : C⟦a,b⟧) (h : C⟦b,c⟧) (i : c --> d) (η : f ==> g)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : w -->[g] x) (hh : x -->[h] y) (ii : y -->[i] z)
       (ηη : ff ==>[η] gg),
     disp_lassociator _ _ _ •• ((ηη ▹▹ hh) ▹▹ ii) =
     transportb (λ α, _ ==>[α] _) (rwhisker_rwhisker _ _ _)
                ((ηη ▹▹ hh ;; ii) •• disp_lassociator _ _ _).

Definition disp_vcomp_whisker_law : UU
  := ∏ (a b c : C) (f g : C⟦a,b⟧) (h i : C⟦b,c⟧)
       (η : f ==> g) (φ : h ==> i)
       (x : D a) (y : D b) (z : D c)
       (ff : x -->[f] y) (gg : x -->[g] y)
       (hh : y -->[h] z) (ii : y -->[i] z)
       (ηη : ff ==>[η] gg) (φφ : hh ==>[φ] ii),
     (ηη ▹▹ hh) •• (gg ◃◃ φφ) =
     transportb (λ α, _ ==>[α] _) (vcomp_whisker _ _) ((ff ◃◃ φφ) •• (ηη ▹▹ ii)).

Definition disp_lunitor_linvunitor_law : UU
  := ∏ (a b : C) (f : C⟦a,b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     disp_lunitor ff •• disp_linvunitor _ =
     transportb (λ α, _ ==>[α] _) (lunitor_linvunitor _) (disp_id2 (id_disp _ ;; ff)).

Definition disp_linvunitor_lunitor_law : UU
  := ∏ (a b : C) (f : C⟦a,b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     disp_linvunitor ff •• disp_lunitor _ =
     transportb (λ α, _ ==>[α] _) (linvunitor_lunitor _) (disp_id2 _).

Definition disp_runitor_rinvunitor_law : UU
  := ∏ (a b : C) (f : C⟦a,b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     disp_runitor ff •• disp_rinvunitor _ =
     transportb (λ α, _ ==>[α] _) (runitor_rinvunitor _) (disp_id2 _).

Definition disp_rinvunitor_runitor_law : UU
  := ∏ (a b : C) (f : C⟦a,b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     disp_rinvunitor ff •• disp_runitor _ =
     transportb (λ α, _ ==>[α] _) (rinvunitor_runitor _) (disp_id2 _).

Definition disp_lassociator_rassociator_law : UU
  := ∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : c --> d)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y)
       (hh : y -->[h] z),
     disp_lassociator ff gg hh •• disp_rassociator _ _ _ =
     transportb (λ α, _ ==>[α] _) (lassociator_rassociator _ _ _ ) (disp_id2  _).

Definition disp_rassociator_lassociator_law : UU
  := ∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : c --> d)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y)
       (hh : y -->[h] z),
     disp_rassociator ff gg hh •• disp_lassociator _ _ _ =
     transportb (λ α, _ ==>[α] _) (rassociator_lassociator _ _ _ ) (disp_id2 _).

Definition disp_runitor_rwhisker_law : UU
  := ∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
       (x : D a) (y : D b) (z : D c)
       (ff : x -->[f] y) (gg : y -->[g] z),
     disp_lassociator _ _ _ •• (disp_runitor ff ▹▹ gg) =
     transportb (λ α, _ ==>[α] _) (runitor_rwhisker _ _) (ff ◃◃ disp_lunitor gg).

Definition disp_lassociator_lassociator_law : UU
  := ∏ (a b c d e: C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : c --> d) (i : C⟦d,e⟧)
       (v : D a) (w : D b) (x : D c) (y : D d) (z : D e)
       (ff : v -->[f] w) (gg : w -->[g] x)
       (hh : x -->[h] y) (ii : y -->[i] z),

     (ff ◃◃ disp_lassociator gg hh ii) •• disp_lassociator _ _ _ ••
     (disp_lassociator _ _ _ ▹▹ ii) =
     transportb (λ α, _ ==>[α] _) (lassociator_lassociator _ _ _ _)
                (disp_lassociator ff gg _ •• disp_lassociator _ _ _).

(* ----------------------------------------------------------------------------------- *)
(** ** Laws                                                                            *)
(* ----------------------------------------------------------------------------------- *)

Definition disp_prebicat_laws : UU
  :=   disp_id2_left_law
     × disp_id2_right_law
     × disp_vassocr_law
     × disp_lwhisker_id2_law
     × disp_id2_rwhisker_law
     × disp_lwhisker_vcomp_law
     × disp_rwhisker_vcomp_law
     × disp_vcomp_lunitor_law
     × disp_vcomp_runitor_law
     × disp_lwhisker_lwhisker_law
     × disp_rwhisker_lwhisker_law
     × disp_rwhisker_rwhisker_law
     × disp_vcomp_whisker_law
     × disp_lunitor_linvunitor_law
     × disp_linvunitor_lunitor_law
     × disp_runitor_rinvunitor_law
     × disp_rinvunitor_runitor_law
     × disp_lassociator_rassociator_law
     × disp_rassociator_lassociator_law
     × disp_runitor_rwhisker_law
     × disp_lassociator_lassociator_law.

End disp_prebicat_laws.

(* ----------------------------------------------------------------------------------- *)
(** Laws projections                                                                   *)
(* ----------------------------------------------------------------------------------- *)

Definition disp_prebicat : UU
  := ∑ D : disp_prebicat_data, disp_prebicat_laws D.

Coercion disp_prebicat_data_from_disp_prebicat (D : disp_prebicat)
  : disp_prebicat_data
  := pr1 D.

Section disp_prebicat_law_projections.

Context {D : disp_prebicat}.

Definition disp_id2_left {a b : C} {f g : C⟦a,b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : disp_id2 _ •• ηη = transportb (λ α, _ ==>[α] _) (id2_left _) ηη
  := pr1 (pr2 D) _ _ _ _ _ x y ff gg ηη.

Definition disp_id2_right {a b : C} {f g : C⟦a,b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : ηη •• disp_id2 _ = transportb (λ α, _ ==>[α] _) (id2_right _) ηη
  := pr1 (pr2 (pr2 D)) _ _ _ _ _ _ _ _ _ ηη.

Definition disp_vassocr {a b : C} {f g h k : C⟦a,b⟧}
           {η : f ==> g} {φ : g ==> h} {ψ : h ==> k}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {kk : x -->[k] y}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk)
  : ηη •• (φφ •• ψψ) =
    transportb (λ α, _ ==>[α] _) (vassocr _ _ _) ((ηη •• φφ) •• ψψ)
  := pr1 (pr2 (pr2 (pr2 D))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ ψψ .

Definition disp_vassocr' {a b : C} {f g h k : C⟦a,b⟧}
           {η : f ==> g} {φ : g ==> h} {ψ : h ==> k}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {kk : x -->[k] y}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk)
  : transportf (λ α, _ ==>[α] _) (vassocr _ _ _) (ηη •• (φφ •• ψψ)) =
    ((ηη •• φφ) •• ψψ).
Proof.
  use (transportf_transpose_alt (P := λ x' : f ==> k, ff ==>[x'] kk)).
  apply disp_vassocr.
Defined.

Definition disp_lwhisker_id2 {a b c : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {x : D a} {y : D b} {z : D c} (ff : x -->[f] y) (gg : y -->[g] z)
  : ff ◃◃ disp_id2 gg =
    transportb (λ α, _ ==>[α] _) (lwhisker_id2 _ _) (disp_id2 (ff ;; gg))
  := pr1 (pr2 (pr2 (pr2 (pr2 D)))) _ _ _ _ _ _ _ _ ff gg.

Definition disp_id2_rwhisker {a b c : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) (gg : y -->[g] z)
  : disp_id2 ff ▹▹ gg =
    transportb (λ α, _ ==>[α] _) (id2_rwhisker _ _) (disp_id2 (ff ;; gg))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 D))))) _ _ _ _ _ _ _ _ ff gg.

Definition disp_lwhisker_vcomp {a b c : C} {f : C⟦a,b⟧} {g h i : C⟦b,c⟧}
           {η : g ==> h} {φ : h ==> i}
           {x : D a} {y : D b} {z : D c} {ff : x -->[f] y}
           {gg : y -->[g] z} {hh : y -->[h] z} {ii : y -->[i] z}
           (ηη : gg ==>[η] hh) (φφ : hh ==>[φ] ii)
  : (ff ◃◃ ηη) •• (ff ◃◃ φφ) =
    transportb (λ α, _ ==>[α] _) (lwhisker_vcomp _ _ _) (ff ◃◃ (ηη •• φφ))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ.

Definition disp_rwhisker_vcomp {a b c : C} {f g h : C⟦a,b⟧} {i : C⟦b,c⟧}
           {η : f ==> g} {φ : g ==> h}
           {x : D a} {y : D b} {z : D c}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {ii : y -->[i] z}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh)
  : (ηη ▹▹ ii) •• (φφ ▹▹ ii) =
    transportb (λ α, _ ==>[α] _) (rwhisker_vcomp _ _ _) ((ηη •• φφ) ▹▹ ii)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ.

Definition disp_vcomp_lunitor {a b : C} {f g : C⟦a,b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : (id_disp _ ◃◃ ηη) •• disp_lunitor gg =
    transportb (λ α, _ ==>[α] _) (vcomp_lunitor _ _ _) (disp_lunitor ff •• ηη)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))) _ _ _ _ _ _ _ _ _  ηη.

Definition disp_vcomp_runitor {a b : C} {f g : C⟦a,b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : (ηη ▹▹ id_disp _) •• disp_runitor gg =
    transportb (λ α, _ ==>[α] _) (vcomp_runitor _ _ _) (disp_runitor ff •• ηη)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))) _ _ _ _ _ _ _ _ _  ηη.

Definition disp_lwhisker_lwhisker {a b c d : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {h i : c --> d} {η : h ==> i}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y) {hh : y -->[h] z} {ii : y -->[i] z}
           (ηη : hh ==>[η] ii)
  : ff ◃◃ (gg ◃◃ ηη) •• disp_lassociator _ _ _ =
    transportb (λ α, _ ==>[α] _) (lwhisker_lwhisker _ _ _)
               (disp_lassociator _ _ _ •• (ff ;; gg ◃◃ ηη))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))
         _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ ηη.

Definition disp_rwhisker_lwhisker {a b c d : C} {f : C⟦a,b⟧} {g h : C⟦b,c⟧}
           {i : c --> d} {η : g ==> h}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) {gg : x -->[g] y} {hh : x -->[h] y} (ii : y -->[i] z)
           (ηη : gg ==>[η] hh)
  : (ff ◃◃ (ηη ▹▹ ii)) •• disp_lassociator _ _ _ =
    transportb (λ α, _ ==>[α] _) (rwhisker_lwhisker _ _ _)
               (disp_lassociator _ _ _ •• ((ff ◃◃ ηη) ▹▹ ii))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))
         _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ ηη.

Definition disp_rwhisker_rwhisker {a b c d : C} {f g : C⟦a,b⟧} {h : C⟦b,c⟧}
           (i : c --> d) (η : f ==> g)
           {w : D a} {x : D b} {y : D c} {z : D d}
           {ff : w -->[f] x} {gg : w -->[g] x} (hh : x -->[h] y) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg)
  : disp_lassociator _ _ _ •• ((ηη ▹▹ hh) ▹▹ ii) =
    transportb (λ α, _ ==>[α] _) (rwhisker_rwhisker _ _ _)
               ((ηη ▹▹ hh ;; ii) •• disp_lassociator _ _ _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))
         _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ ηη.

Definition disp_vcomp_whisker {a b c : C} {f g : C⟦a,b⟧} {h i : C⟦b,c⟧}
           (η : f ==> g) (φ : h ==> i)
           (x : D a) (y : D b) (z : D c)
           (ff : x -->[f] y) (gg : x -->[g] y) (hh : y -->[h] z) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg) (φφ : hh ==>[φ] ii)
  : (ηη ▹▹ hh) •• (gg ◃◃ φφ) =
    transportb (λ α, _ ==>[α] _) (vcomp_whisker _ _) ((ff ◃◃ φφ) •• (ηη ▹▹ ii))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ.

Definition disp_lunitor_linvunitor {a b : C} {f : C⟦a,b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : disp_lunitor ff •• disp_linvunitor _ =
    transportb (λ α, _ ==>[α] _) (lunitor_linvunitor _) (disp_id2 (id_disp _ ;; ff))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))
         _ _ _ _ _ ff.

Definition disp_linvunitor_lunitor {a b : C} {f : C⟦a,b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : disp_linvunitor ff •• disp_lunitor _ =
    transportb (λ α, _ ==>[α] _) (linvunitor_lunitor _) (disp_id2 _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))) _ _ _ _ _ ff.

Definition disp_runitor_rinvunitor {a b : C} {f : C⟦a,b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : disp_runitor ff •• disp_rinvunitor _ =
    transportb (λ α, _ ==>[α] _) (runitor_rinvunitor _) (disp_id2 _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))))) _ _ _ _ _ ff.

Definition disp_rinvunitor_runitor {a b : C} {f : C⟦a,b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : disp_rinvunitor ff •• disp_runitor _ =
    transportb (λ α, _ ==>[α] _) (rinvunitor_runitor _) (disp_id2 _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))) _ _ _ _ _ ff.

Definition disp_lassociator_rassociator {a b c d : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {h : c --> d} {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : disp_lassociator ff gg hh •• disp_rassociator _ _ _ =
    transportb (λ α, _ ==>[α] _) (lassociator_rassociator _ _ _ ) (disp_id2  _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))))
         _ _ _ _ _ _ _ _ _ _ _ ff gg hh.

Definition disp_rassociator_lassociator
           {a b c d : C} (f : C⟦a,b⟧) {g : C⟦b,c⟧} {h : c --> d}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y)
           (hh : y -->[h] z)
  : disp_rassociator ff gg hh •• disp_lassociator _ _ _ =
    transportb (λ α, _ ==>[α] _) (rassociator_lassociator _ _ _ ) (disp_id2 _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))))))))
         _ _ _ _ _ _ _ _ _ _ _ ff gg hh.

Definition disp_runitor_rwhisker {a b c : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {x : D a} {y : D b} {z : D c} (ff : x -->[f] y) (gg : y -->[g] z)
  : disp_lassociator _ _ _ •• (disp_runitor ff ▹▹ gg) =
    transportb (λ α, _ ==>[α] _) (runitor_rwhisker _ _) (ff ◃◃ disp_lunitor gg)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))))))
         _ _ _ _ _ _ _ _ ff gg.

Definition disp_lassociator_lassociator {a b c d e: C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {h : c --> d} {i : C⟦d,e⟧}
           {v : D a} {w : D b} {x : D c} {y : D d} {z : D e}
           (ff : v -->[f] w) (gg : w -->[g] x) (hh : x -->[h] y) (ii : y -->[i] z)
  : (ff ◃◃ disp_lassociator gg hh ii) •• disp_lassociator _ _ _ ••
    (disp_lassociator _ _ _ ▹▹ ii) =
    transportb (λ α, _ ==>[α] _) (lassociator_lassociator _ _ _ _)
               (disp_lassociator ff gg _ •• disp_lassociator _ _ _)
  := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))))))
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff gg hh ii.

End disp_prebicat_law_projections.

(* ----------------------------------------------------------------------------------- *)
(** ** Invertible displayed 2-cells.                                                   *)
(* ----------------------------------------------------------------------------------- *)

Lemma disp_vassocl {D : disp_prebicat} {a b : C} {f g h k : C⟦a,b⟧}
      {η : f ==> g} {φ : g ==> h} {ψ : h ==> k} {x : D a} {y : D b}
      {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {kk : x -->[k] y}
      (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk)
  : (ηη •• φφ) •• ψψ
    = transportb (λ α, _ ==>[α] _) (vassocl _ _ _) (ηη •• (φφ •• ψψ)).
Proof.
  apply (transportf_transpose (P := λ x', _ ==>[x'] _)).
  apply pathsinv0.
  etrans.
  apply disp_vassocr.
  apply maponpaths_2.
  unfold vassocl.
  apply pathsinv0, pathsinv0inv0.
Qed.

Section Display_Invertible_2cell.
  Context {D : disp_prebicat}.

  Section Def_inv_2cell.

  Context {c c' : C} {f f' : C⟦c,c'⟧} {d : D c} {d' : D c'}.

  Definition is_disp_invertible_2cell' {α : invertible_2cell f f'}
             {ff : d -->[f] d'} {ff' : d -->[f'] d'} (x : ff ==>[α] ff')
    : UU
    := ∑ (y : ff' ==>[α^-1] ff),
         (x •• y =
          transportb (λ α, _ ==>[α] _) (vcomp_rinv α)
                     (disp_id2 ff))
       × (y •• x =
          transportb (λ α, _ ==>[α] _) (vcomp_lid α)
                     (disp_id2 ff')).

  Definition is_disp_invertible_2cell {α : f ==> f'} (inv_α : is_invertible_2cell α)
             {ff : d -->[f] d'} {ff' : d -->[f'] d'} (x : ff ==>[α] ff')
    : UU
    := ∑ (y : ff' ==>[inv_α^-1] ff),
         (x •• y =
          transportb (λ α, _ ==>[α] _) (vcomp_rinv inv_α)
                     (disp_id2 ff))
       × (y •• x =
          transportb (λ α, _ ==>[α] _) (vcomp_lid inv_α)
                     (disp_id2 ff')).

  Definition disp_invertible_2cell (α : invertible_2cell f f')
             (ff : d -->[f] d') (ff' : d -->[f'] d')
    : UU
    := ∑ (x : ff ==>[α] ff'), is_disp_invertible_2cell α x.

  Coercion disp_cell_from_invertible_2cell {α : invertible_2cell f f'}
           {ff : d -->[f] d'} {ff' : d -->[f'] d'}
           (e : disp_invertible_2cell α ff ff')
    : ff ==>[α] ff'
    := pr1 e.

  Definition disp_inv_cell {α : invertible_2cell f f'}
             {ff : d -->[f] d'} {ff' : d -->[f'] d'}
             (e : disp_invertible_2cell α ff ff')
    : ff' ==>[α^-1] ff
    := pr1 (pr2 e).

  Definition disp_vcomp_rinv {α : invertible_2cell f f'}
             {ff : d -->[f] d'} {ff' : d -->[f'] d'}
             (e : disp_invertible_2cell α ff ff')
    : e •• disp_inv_cell e =
      transportb (λ α, _ ==>[α] _) (vcomp_rinv α) (disp_id2 ff)
    := pr1 (pr2 (pr2 e)).

  Definition disp_vcomp_linv {α : invertible_2cell f f'}
             {ff : d -->[f] d'} {ff' : d -->[f'] d'}
             (e : disp_invertible_2cell α ff ff')
    : disp_inv_cell e •• e =
      transportb (λ α, _ ==>[α] _) (vcomp_lid α) (disp_id2 ff')
    := pr2 (pr2 (pr2 e)).

  End Def_inv_2cell.

  Lemma disp_mor_transportf_postwhisker (a b : C) {x y z : C⟦a,b⟧} {f f' : x ==> y}
        (ef : f = f') {g : y ==> z} {aa : D a} {bb : D b}
        {xx : aa -->[x] bb} {yy} {zz} (ff : xx ==>[f] yy) (gg : yy ==>[g] zz)
    : (transportf (λ x, _ ==>[x] _) ef ff) •• gg
      = transportf (λ x, _ ==>[x] _) (maponpaths (λ h, h • g) ef) (ff •• gg).
  Proof.
    induction ef; apply idpath.
  Qed.

  Lemma disp_mor_transportf_prewhisker (a b : C) {x y z : C⟦a,b⟧}
        {f : x ==> y} {g g' : y ==> z} (ef : g = g')
        {aa : D a} {bb : D b}
        {xx : aa -->[x] bb} {yy} {zz} (ff : xx ==>[f] yy) (gg : yy ==>[g] zz)
    : ff •• (transportf (λ x, _ ==>[x] _) ef gg)
      = transportf (λ x, _ ==>[x] _) (maponpaths (λ h, f • h) ef) (ff •• gg).
  Proof.
    induction ef; apply idpath.
  Qed.

  Lemma disp_mor_transportf_prewhisker_gen (a b : C) {x y z : C⟦a,b⟧} {f : x ==> y}
        {A : UU} {t : A → y ==> z} {g g' : A} (ef : g = g')
        {aa : D a} {bb : D b}
        {xx : aa -->[x] bb} {yy} {zz} (ff : xx ==>[f] yy) (gg : yy ==>[t g] zz)
    : ff •• (transportf (λ x, _ ==>[t x] _) ef gg)
      = transportf (λ x, _ ==>[x] _) (maponpaths (λ h, f • t h) ef) (ff •• gg).
  Proof.
    induction ef; apply idpath.
  Qed.

  Lemma disp_lhs_right_invert_cell' {a b : C} {f g h : a --> b}
        {x : f ==> g} {y : invertible_2cell g h} {z : f ==> h}
        {p : x = z • y^-1}
        {aa : D a} {bb : D b}
        {ff : aa -->[f] bb}
        {gg : aa -->[g] bb}
        {hh : aa -->[h] bb}
        (xx : ff ==>[x] gg)
        (yy : gg ==>[y] hh)
        (zz : ff ==>[z] hh)
        (H : is_disp_invertible_2cell y yy)
        (q := lhs_right_invert_cell _ _ _ _ p)
        (pp : xx = transportb (λ x, _ ==>[x] _) p (zz •• disp_inv_cell (yy,,H)))
    : xx •• yy = transportb (λ x, _ ==>[x] _) q zz.
  Proof.
    set (yy' := (yy,,H) : disp_invertible_2cell _ _ _).
    etrans. apply maponpaths_2. apply pp.
    etrans. apply disp_mor_transportf_postwhisker.
    etrans. apply maponpaths. apply disp_vassocl.
    etrans. unfold transportb. apply (transport_f_f (λ x' : f ==> h, ff ==>[x'] hh)).
    etrans. apply maponpaths. apply maponpaths.
    apply disp_vcomp_linv.
    etrans. apply maponpaths.
    apply disp_mor_transportf_prewhisker.
    etrans. unfold transportb. apply (transport_f_f (λ x' : f ==> h, ff ==>[x'] hh)).
    etrans. apply maponpaths.
    apply disp_id2_right.
    etrans. unfold transportb. apply (transport_f_f (λ x' : f ==> h, ff ==>[x'] hh)).
    unfold transportb.
    apply maponpaths_2.
    apply cellset_property.
  Qed.

  Lemma disp_lhs_right_invert_cell {a b : C} {f g h : a --> b}
        {x : f ==> g} {y : g ==> h} {z : f ==> h}
        (inv_y : is_invertible_2cell y)
        {aa : D a} {bb : D b}
        {ff : aa -->[f] bb}
        {gg : aa -->[g] bb}
        {hh : aa -->[h] bb}
        (xx : ff ==>[x] gg)
        (yy : gg ==>[y] hh)
        (zz : ff ==>[z] hh)
        (H : is_disp_invertible_2cell inv_y yy)
        (q : x • y = z)
        (p  := rhs_right_inv_cell _ _ _ inv_y q : x = z • inv_y^-1)
        (pp : xx =
              transportb
                (λ x, _ ==>[x] _) p
                (zz •• disp_inv_cell ((yy,,H):disp_invertible_2cell (y,,inv_y) gg hh)))
    : xx •• yy = transportb (λ x, _ ==>[x] _) q zz.
  Proof.
    etrans.
    use (disp_lhs_right_invert_cell' _ _ _ _ pp).
    apply maponpaths_2.
    apply cellset_property.
  Qed.

  Lemma disp_lhs_left_invert_cell {a b : C} {f g h : a --> b}
        {x : f ==> g} {y : g ==> h} {z : f ==> h} {inv_x : is_invertible_2cell x}
        {aa : D a} {bb : D b}
        {ff : aa -->[f] bb}
        {gg : aa -->[g] bb}
        {hh : aa -->[h] bb}
        (xx : ff ==>[x] gg)
        (yy : gg ==>[y] hh)
        (zz : ff ==>[z] hh)
        (inv_xx : is_disp_invertible_2cell inv_x xx)
        (q :  x • y = z)
        (p := rhs_left_inv_cell _ _ _ inv_x q : y = inv_x^-1 • z)
        (pp : yy =
              transportb
                (λ x, _ ==>[x] _) p
                (disp_inv_cell ((xx,,inv_xx):disp_invertible_2cell (x,,inv_x) ff gg) •• zz))
    : xx •• yy = transportb (λ x, _ ==>[x] _) q zz.
  Proof.
    etrans. apply maponpaths. apply pp.
    etrans.
    apply disp_mor_transportf_prewhisker.
    etrans. apply maponpaths.
    apply disp_vassocr.
    etrans. apply (transport_f_f (λ x, _ ==>[x] _)).
    etrans. apply maponpaths.
    apply maponpaths_2.
    apply (disp_vcomp_rinv
             ((xx,,inv_xx):disp_invertible_2cell (x,,inv_x) _ _)).
    etrans. apply maponpaths. apply disp_mor_transportf_postwhisker.
    etrans. unfold transportb. apply (transport_f_f (λ x, _ ==>[x] _)).
    etrans. apply maponpaths. apply disp_id2_left.
    etrans. unfold transportb. apply (transport_f_f (λ x, _ ==>[x] _)).
    unfold transportb.
    apply maponpaths_2. apply cellset_property.
  Qed.

End Display_Invertible_2cell.

(* ----------------------------------------------------------------------------------- *)
(** ** Derived laws                                                                    *)
(* ----------------------------------------------------------------------------------- *)

Section Derived_Laws.

Context {D : disp_prebicat}.

Definition is_disp_invertible_2cell_lassociator {a b c d : C}
           {f1 : C⟦a,b⟧} {f2 : C⟦b,c⟧} {f3 : C⟦c,d⟧}
           {aa : D a} {bb : D b} {cc : D c} {dd : D d}
           (ff1 : aa -->[f1] bb)
           (ff2 : bb -->[f2] cc)
           (ff3 : cc -->[f3] dd)
  : is_disp_invertible_2cell (is_invertible_2cell_lassociator _ _ _)
                             (disp_lassociator ff1 ff2 ff3).
Proof.
  exists (disp_rassociator ff1 ff2 ff3).
  split.
  - apply disp_lassociator_rassociator.
  - apply disp_rassociator_lassociator.
Defined.

Definition is_disp_invertible_2cell_rassociator {a b c d : C}
           {f1 : C⟦a,b⟧} {f2 : C⟦b,c⟧} {f3 : C⟦c,d⟧}
           {aa : D a} {bb : D b} {cc : D c} {dd : D d}
           (ff1 : aa -->[f1] bb)
           (ff2 : bb -->[f2] cc)
           (ff3 : cc -->[f3] dd)
  : is_disp_invertible_2cell (is_invertible_2cell_rassociator _ _ _)
                             (disp_rassociator ff1 ff2 ff3).
Proof.
  exists (disp_lassociator ff1 ff2 ff3).
  split.
  - apply disp_rassociator_lassociator.
  - apply disp_lassociator_rassociator.
Defined.

Lemma disp_lassociator_to_rassociator_post' {a b c d : C}
      {f : C⟦a,b⟧} {g : C⟦b,c⟧} {h : C⟦c,d⟧} {k : C⟦a,d⟧}
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
      (pp : xx = transportb (λ x, _ ==>[x] _) p (yy •• disp_lassociator ff gg hh))
  : xx •• disp_rassociator ff gg hh = transportb (λ x, _ ==>[x] _) q (yy).
Proof.
  etrans.
  use disp_lhs_right_invert_cell.
  - exact y.
  - apply is_invertible_2cell_rassociator.
  - exact yy.
  - apply is_disp_invertible_2cell_rassociator.
  - apply lassociator_to_rassociator_post. exact p.
  - cbn. etrans. apply pp.
    apply maponpaths_2.
    apply cellset_property.
  - apply maponpaths_2. apply cellset_property.
Qed.

Lemma disp_lassociator_to_rassociator_post {a b c d : C}
      {f : C⟦a,b⟧} {g : C⟦b,c⟧} {h : C⟦c,d⟧} {k : C⟦a,d⟧}
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
      (pp : xx = transportb (λ x, _ ==>[x] _) p (yy •• disp_lassociator ff gg hh))
  : xx •• disp_rassociator ff gg hh = transportb (λ x, _ ==>[x] _) q (yy).
Proof.
  etrans.
  use disp_lassociator_to_rassociator_post'.
  - exact y.
  - exact p.
  - exact yy.
  - exact pp.
  - apply maponpaths_2. apply cellset_property.
Qed.

Lemma disp_lassociator_to_rassociator_pre {a b c d : C}
      {f : C⟦a,b⟧} {g : C⟦b,c⟧} {h : C⟦c, d⟧} {k : C⟦a,d⟧}
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
      (pp : xx = transportb (λ x, _ ==>[x] _) p (disp_lassociator ff gg hh •• yy))
  : disp_rassociator ff gg hh •• xx = transportb (λ x, _ ==>[x] _) q (yy).
Proof.
  etrans.
  use disp_lhs_left_invert_cell.
  - exact y.
  - apply is_invertible_2cell_rassociator.
  - exact yy.
  - apply is_disp_invertible_2cell_rassociator.
  - apply lassociator_to_rassociator_pre. exact p.
  - cbn. etrans. apply pp.
    apply maponpaths_2.
    apply cellset_property.
  - apply maponpaths_2.
    apply cellset_property.
Qed.

Lemma disp_lunitor_lwhisker {a b c : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
      {aa : D a} {bb : D b} {cc : D c}
      (ff : aa -->[f] bb)
      (gg : bb -->[g] cc)
  : (disp_rassociator _ _ _ •• (ff ◃◃ disp_lunitor gg)) =
    transportb (λ α, _ ==>[α] _) (lunitor_lwhisker _ _)
               (disp_runitor ff ▹▹ gg).
Proof.
  etrans.
  use disp_lassociator_to_rassociator_pre.
  - exact (runitor f ▹ g).
  - exact (disp_runitor ff ▹▹ gg).
  - apply lunitor_lwhisker.
  - apply pathsinv0.
    etrans.
    apply maponpaths. apply disp_runitor_rwhisker.
    etrans.
    apply (transport_f_f (λ α, _ ==>[α] _)).
    apply (transportf_set (λ α, _ ==>[α] _)).
    apply cellset_property.
  - apply maponpaths_2, cellset_property.
Qed.


Lemma disp_rwhisker_transport_left {a b c : C}
      {f1 f2 : C⟦a,b⟧} {g : C⟦b,c⟧}
      {x x' : f1 ==> f2} (p : x = x')
      {aa : D a} {bb : D b} {cc : D c}
      {ff1 : aa -->[f1] bb}
      {ff2 : aa -->[f2] bb}
      (xx : ff1 ==>[x] ff2)
      (gg : bb -->[g] cc)
  : (transportf (λ x, _ ==>[x] _) p xx) ▹▹ gg =
    transportf (λ x, _ ==>[x ▹ g] _) p (xx ▹▹ gg).
Proof.
  induction p. apply idpath.
Defined.

Lemma disp_rwhisker_transport_left_new {a b c : C}
      {f1 f2 : C⟦a,b⟧} {g : C⟦b,c⟧}
      {x x' : f1 ==> f2} (p : x = x')
      {aa : D a} {bb : D b} {cc : D c}
      {ff1 : aa -->[f1] bb}
      {ff2 : aa -->[f2] bb}
      (xx : ff1 ==>[x] ff2)
      (gg : bb -->[g] cc)
  : (transportf (λ x, _ ==>[x] _) p xx) ▹▹ gg =
    transportf (λ x, _ ==>[x] _) (maponpaths (λ x, x ▹ g) p) (xx ▹▹ gg).
Proof.
  induction p. apply idpath.
Defined.

Lemma disp_rwhisker_transport_right {a b c : C}
      {f : C⟦a,b⟧} {g1 g2 : C⟦b,c⟧}
      {x x' : g1 ==> g2} (p : x = x')
      {aa : D a} {bb : D b} {cc : D c}
      {ff : aa -->[f] bb}
      (gg1 : bb -->[g1] cc)
      (gg2 : bb -->[g2] cc)
      (xx : gg1 ==>[x] gg2)
  : ff ◃◃ (transportf (λ x, _ ==>[x] _) p xx) =
    transportf (λ x, _ ==>[x] _) (maponpaths (λ x, f ◃ x) p) (ff ◃◃ xx).
Proof.
  induction p. apply idpath.
Defined.


Definition disp_lwhisker_vcomp_alt
           {a b c : C} {f : C⟦a,b⟧} {g h i : C⟦b,c⟧}
           {η : g ==> h} {φ : h ==> i}
           {x : D a} {y : D b} {z : D c} {ff : x -->[f] y}
           {gg : y -->[g] z} {hh : y -->[h] z} {ii : y -->[i] z}
           (ηη : gg ==>[η] hh) (φφ : hh ==>[φ] ii)
  : ff ◃◃ (ηη •• φφ)
    =
    transportf (λ α, _ ==>[α] _) (lwhisker_vcomp _ _ _) ((ff ◃◃ ηη) •• (ff ◃◃ φφ)).
Proof.
  refine (!_).
  apply (@transportf_transpose_alt _ (λ α, _ ==>[α] _)).
  apply disp_lwhisker_vcomp.
Qed.

Definition disp_rwhisker_vcomp_alt
           {a b c : C} {f g h : C⟦a,b⟧} {i : C⟦b,c⟧}
           {η : f ==> g} {φ : g ==> h}
           {x : D a} {y : D b} {z : D c}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {ii : y -->[i] z}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh)
  : (ηη •• φφ) ▹▹ ii
    =
    transportf (λ α, _ ==>[α] _) (rwhisker_vcomp _ _ _) ((ηη ▹▹ ii) •• (φφ ▹▹ ii)).
Proof.
  refine (!_).
  apply (@transportf_transpose_alt _ (λ α, _ ==>[α] _)).
  apply disp_rwhisker_vcomp.
Qed.

Definition disp_vcomp_whisker_alt
           {a b c : C} {f g : C⟦a,b⟧} {h i : C⟦b,c⟧}
           (η : f ==> g) (φ : h ==> i)
           (x : D a) (y : D b) (z : D c)
           (ff : x -->[f] y) (gg : x -->[g] y) (hh : y -->[h] z) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg) (φφ : hh ==>[φ] ii)
  : (ff ◃◃ φφ) •• (ηη ▹▹ ii)
    =
    transportf (λ α, _ ==>[α] _) (vcomp_whisker _ _) ((ηη ▹▹ hh) •• (gg ◃◃ φφ)).
Proof.
  refine (!_).
  apply (@transportf_transpose_alt _ (λ α, _ ==>[α] _)).
  apply disp_vcomp_whisker.
Qed.

Definition disp_id2_rwhisker_alt
           {a b c : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) (gg : y -->[g] z)
  : transportf (λ α, _ ==>[α] _) (id2_rwhisker _ _) (disp_id2 ff ▹▹ gg)
    =
    disp_id2 (ff ;; gg).
Proof.
  apply (@transportf_transpose_alt _ (λ α, _ ==>[α] _)).
  apply disp_id2_rwhisker.
Qed.

End Derived_Laws.

(* ----------------------------------------------------------------------------------- *)
(** ** Total bicategory of a displayed bicategory                                      *)
(* ----------------------------------------------------------------------------------- *)

Section total_prebicat.

Variable D : disp_prebicat.

Definition total_prebicat_1_data : precategory_data
  := total_category_ob_mor D ,, total_category_id_comp D.

Definition total_prebicat_cell_struct : prebicat_2cell_struct (total_category_ob_mor D)
  := λ a b f g, ∑ η : pr1 f ==> pr1 g, pr2 f ==>[η] pr2 g.

Definition total_prebicat_1_id_comp_cells : prebicat_1_id_comp_cells
  := (total_prebicat_1_data,, total_prebicat_cell_struct).

Definition total_prebicat_2_id_comp_struct
  : prebicat_2_id_comp_struct total_prebicat_1_id_comp_cells.
Proof.
  repeat split; cbn; unfold total_prebicat_cell_struct.
  - intros. exists (id2 _). exact (disp_id2 _).
  - intros. exists (lunitor _). exact (disp_lunitor _).
  - intros. exists (runitor _). exact (disp_runitor _).
  - intros. exists (linvunitor _). exact (disp_linvunitor _).
  - intros. exists (rinvunitor _). exact (disp_rinvunitor _).
  - intros. exists (rassociator _ _ _).
    exact (disp_rassociator _ _ _).
  - intros. exists (lassociator _ _ _).
    exact (disp_lassociator _ _ _).
  - intros a b f g h r s. exists (pr1 r • pr1 s).
    exact (pr2 r •• pr2 s).
  - intros a b d f g1 g2 r. exists (pr1 f ◃ pr1 r).
    exact (pr2 f ◃◃ pr2 r).
  - intros a b c f1 f2 g r. exists (pr1 r ▹ pr1 g).
    exact (pr2 r ▹▹ pr2 g).
Defined.

Definition total_prebicat_data : prebicat_data
  := _ ,, total_prebicat_2_id_comp_struct.

Lemma total_prebicat_laws : prebicat_laws total_prebicat_data.
Proof.
  repeat split; intros.
  - use total2_paths_b.
    + apply id2_left.
    + apply disp_id2_left.
  - use total2_paths_b.
    + apply id2_right.
    + apply disp_id2_right.
  - use total2_paths_b.
    + apply vassocr.
    + apply disp_vassocr.
  - use total2_paths_b.
    + apply lwhisker_id2.
    + apply disp_lwhisker_id2.
  - use total2_paths_b.
    + apply id2_rwhisker.
    + apply disp_id2_rwhisker.
  - use total2_paths_b.
    + apply lwhisker_vcomp.
    + apply disp_lwhisker_vcomp.
  - use total2_paths_b.
    + apply rwhisker_vcomp.
    + apply disp_rwhisker_vcomp.
  - use total2_paths_b.
    + apply vcomp_lunitor.
    + apply disp_vcomp_lunitor.
  - use total2_paths_b.
    + apply vcomp_runitor.
    + apply disp_vcomp_runitor.
  - use total2_paths_b.
    + apply lwhisker_lwhisker.
    + apply disp_lwhisker_lwhisker.
  - use total2_paths_b.
    + apply rwhisker_lwhisker.
    + apply disp_rwhisker_lwhisker.
  - use total2_paths_b.
    + apply rwhisker_rwhisker.
    + apply disp_rwhisker_rwhisker.
  - use total2_paths_b.
    + apply vcomp_whisker.
    + apply disp_vcomp_whisker.
  - use total2_paths_b.
    + apply lunitor_linvunitor.
    + apply disp_lunitor_linvunitor.
  - use total2_paths_b.
    + apply linvunitor_lunitor.
    + apply disp_linvunitor_lunitor.
  - use total2_paths_b.
    + apply runitor_rinvunitor.
    + apply disp_runitor_rinvunitor.
  - use total2_paths_b.
    + apply rinvunitor_runitor.
    + apply disp_rinvunitor_runitor.
  - use total2_paths_b.
    + apply lassociator_rassociator.
    + apply disp_lassociator_rassociator.
  - use total2_paths_b.
    + apply rassociator_lassociator.
    + apply disp_rassociator_lassociator.
  - use total2_paths_b.
    + apply runitor_rwhisker.
    + apply disp_runitor_rwhisker.
  - use total2_paths_b.
    + apply lassociator_lassociator.
    + apply disp_lassociator_lassociator.
Defined.

Definition total_prebicat : prebicat := _ ,, total_prebicat_laws.
End total_prebicat.

Definition has_disp_cellset (D : disp_prebicat) : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧) (x : f ==> g)
       (aa : D a) (bb : D b)
       (ff : aa -->[f] bb)
       (gg : aa -->[g] bb),
     isaset (ff ==>[x] gg).

Definition disp_bicat : UU
  := ∑ D : disp_prebicat, has_disp_cellset D.

Coercion disp_prebicat_of_disp_bicat (D : disp_bicat)
  : disp_prebicat
  := pr1 D.

Definition disp_cellset_property (D : disp_bicat)
  : has_disp_cellset D
  := pr2 D.

Lemma isaset_cells_total_prebicat (D : disp_bicat)
  : isaset_cells (total_prebicat D).
Proof.
red.
cbn.
intros.
unfold total_prebicat_cell_struct.
apply isaset_total2.
apply cellset_property.
intros.
apply disp_cellset_property.
Qed.

Definition total_bicat (D : disp_bicat) : bicat
  := total_prebicat D,, isaset_cells_total_prebicat D.

End disp_prebicat.

Arguments disp_prebicat_1_id_comp_cells _ : clear implicits.
Arguments disp_prebicat_data _ : clear implicits.
Arguments disp_prebicat _ : clear implicits.
Arguments disp_bicat _ : clear implicits.

(* ----------------------------------------------------------------------------------- *)
(** ** Displayed left and right unitors coincide on the identity                       *)
(* ----------------------------------------------------------------------------------- *)

Theorem disp_lunitor_runitor_identity {C : bicat} {D : disp_bicat C} (a : C) (aa : D a)
  : disp_lunitor (id_disp aa) =
    cell_transportb (lunitor_runitor_identity a) (disp_runitor (id_disp aa)).
Proof.
  set (TT := fiber_paths (lunitor_runitor_identity (C := total_bicat D) (a ,, aa))).
  cbn in TT.
  apply cell_transportf_to_b.
  etrans.
  2: now apply TT.
  unfold cell_transportf.
  apply maponpaths_2.
  apply cellset_property.
Qed.

Theorem disp_runitor_lunitor_identity {C : bicat} {D : disp_bicat C} {a : C} (aa : D a)
  : disp_runitor (id_disp aa) =
    transportb (λ x, disp_2cells x _ _) (runitor_lunitor_identity a)
               (disp_lunitor (id_disp aa)).
Proof.
  apply (transportf_transpose (P := (λ x, disp_2cells x _ _))).
  apply pathsinv0.
  etrans.
  1: now apply disp_lunitor_runitor_identity.
  unfold cell_transportb.
  apply maponpaths_2, cellset_property.
Qed.



(* ----------------------------------------------------------------------------------- *)
(** ** Notations.                                                                      *)
(* ----------------------------------------------------------------------------------- *)

Module Notations.

Export Bicat.Notations.

Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).
Notation "rr •• ss" := (disp_vcomp2 rr ss) (at level 60).
Notation "ff ◃◃ rr" := (disp_lwhisker ff rr) (at level 60).
Notation "rr ▹▹ gg" := (disp_rwhisker gg rr) (at level 60).

End Notations.
