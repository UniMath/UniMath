(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018
 ********************************************************************************* *)

(** * Pseudo functors. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.

Open Scope cat.

(* ----------------------------------------------------------------------------------- *)
(** ** Pseudo-functors                                                                 *)
(* ----------------------------------------------------------------------------------- *)

Definition psfunctor_ob_mor_cell (C C' : prebicat_data) : UU
  := ∑ F : functor_data C C',
     ∏ a b (f g : a --> b), f ==> g → #F f ==> #F g.

Coercion functor_data_from_bifunctor_ob_mor_cell {C C' : prebicat_data}
         (F : psfunctor_ob_mor_cell C C')
  : functor_data C C' := pr1 F.

Definition psfunctor_on_cells {C C' : prebicat_data}
           (F : psfunctor_ob_mor_cell C C')
           {a b : C} {f g : a --> b} (x : f ==> g)
  : #F f ==> #F g
  := pr2 F a b f g x.

Local Notation "'##'" := (psfunctor_on_cells).

Definition psfunctor_cell_data {C C' : prebicat_data} (F : psfunctor_ob_mor_cell C C')
  : UU
  :=   (∏ (a : C), invertible_2cell (#F (identity a)) (identity _))
     × (∏ (a b c : C) (f : a --> b) (g : b --> c),
        invertible_2cell (#F (f · g)) (#F f · #F g)).

Definition psfunctor_data (C C' : prebicat_data) : UU
  := ∑ F : psfunctor_ob_mor_cell C C', psfunctor_cell_data F.

Coercion psfunctor_ob_mor_cell_from_bifunctor_data {C C' : prebicat_data}
         (F : psfunctor_data C C')
  : psfunctor_ob_mor_cell _ _
  := pr1 F.

Definition psfunctor_id {C C' : prebicat_data} (F : psfunctor_data C C') (a : C)
  : invertible_2cell (#F (identity a)) (identity _)
  := pr1 (pr2 F) a.

Definition psfunctor_comp {C C' : prebicat_data} (F : psfunctor_data C C')
           {a b c : C} (f : a --> b) (g : b --> c)
  : invertible_2cell (#F (f · g)) (#F f · #F g)
  := pr2 (pr2 F) a b c f g.


Section psfunctor_laws.

Context {C C' : prebicat_data} (F : psfunctor_data C C').

Definition psfunctor_id2_law : UU
  := ∏ (a b : C) (f : a --> b), ##F (id2 f) = id2 _.

Definition psfunctor_lunitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (lunitor f)
     =   psfunctor_comp F (identity a) f
       • (psfunctor_id _ _ ▹ #F f)
       • lunitor (#F f).

Definition psfunctor_runitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (runitor f)
     =   psfunctor_comp F f (identity b)
       • (#F f ◃ psfunctor_id _ _)
       • runitor (#F f).

Definition psfunctor_linvunitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (linvunitor f)
     =   linvunitor (#F f)
       • (inv_invertible_2cell (psfunctor_id F a) ▹ #F f)
       • inv_invertible_2cell (psfunctor_comp F _ _).

Definition psfunctor_rinvunitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (rinvunitor f)
     =   rinvunitor (#F f)
       • (#F f ◃ inv_invertible_2cell (psfunctor_id F b))
       • inv_invertible_2cell (psfunctor_comp F _ _).

Definition psfunctor_rassociator_law : UU
  := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
       ##F (rassociator f g h)
     =   psfunctor_comp F _ _
       • (psfunctor_comp F _ _ ▹ #F h)
       • rassociator (#F f) (#F g) (#F h)
       • (#F f ◃ inv_invertible_2cell (psfunctor_comp F _ _))
       • inv_invertible_2cell (psfunctor_comp F _ _).

Definition psfunctor_lassociator_law : UU
  := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧) ,
       ##F (lassociator f g h)
     =   psfunctor_comp F _ _
       • (#F f ◃ psfunctor_comp F _ _)
       • lassociator (#F f) (#F g) (#F h)
       • (inv_invertible_2cell (psfunctor_comp F _ _) ▹ #F _)
       • inv_invertible_2cell (psfunctor_comp F _ _).

Definition psfunctor_vcomp2_law : UU
  := ∏ (a b : C) (f g h: C⟦a, b⟧) (η : f ==> g) (φ : g ==> h),
     ##F (η • φ) = ##F η • ##F φ.

Definition psfunctor_lwhisker_law : UU
  := ∏ (a b c : C) (f : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧) (η : g1 ==> g2),
       ##F (f ◃ η)
     =   psfunctor_comp F _ _
       • (#F f ◃ ##F η)
       • inv_invertible_2cell (psfunctor_comp F _ _).

Definition psfunctor_rwhisker_law : UU
  := ∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g : C⟦b, c⟧) (η : f1 ==> f2),
       ##F (η ▹ g)
     =   psfunctor_comp F _ _
       • (##F η ▹ #F g)
       • inv_invertible_2cell (psfunctor_comp F _ _).

Definition psfunctor_laws : UU
  :=   psfunctor_id2_law
     × psfunctor_lunitor_law
     × psfunctor_runitor_law
     × psfunctor_linvunitor_law
     × psfunctor_rinvunitor_law
     × psfunctor_rassociator_law
     × psfunctor_lassociator_law
     × psfunctor_vcomp2_law
     × psfunctor_lwhisker_law
     × psfunctor_rwhisker_law.

End psfunctor_laws.


Notation "'##'" := (psfunctor_on_cells).