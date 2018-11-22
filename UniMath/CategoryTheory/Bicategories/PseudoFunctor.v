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

Definition laxfunctor_ob_mor_cell (C C' : prebicat_data) : UU
  := ∑ F : functor_data C C',
     ∏ a b (f g : a --> b), f ==> g → #F f ==> #F g.

Coercion functor_data_from_bifunctor_ob_mor_cell {C C' : prebicat_data}
         (F : laxfunctor_ob_mor_cell C C')
  : functor_data C C' := pr1 F.

Definition laxfunctor_on_cells {C C' : prebicat_data}
           (F : laxfunctor_ob_mor_cell C C')
           {a b : C} {f g : a --> b} (x : f ==> g)
  : #F f ==> #F g
  := pr2 F a b f g x.

Local Notation "'##'" := (laxfunctor_on_cells).

Definition laxfunctor_cell_data {C C' : prebicat_data} (F : laxfunctor_ob_mor_cell C C')
  : UU
  :=   (∏ (a : C), #F (identity a) ==> identity _)
     × (∏ (a b c : C) (f : a --> b) (g : b --> c),
        #F (f · g) ==> #F f · #F g).

Definition laxfunctor_data (C C' : prebicat_data) : UU
  := ∑ F : laxfunctor_ob_mor_cell C C', laxfunctor_cell_data F.

Coercion laxfunctor_ob_mor_cell_from_bifunctor_data {C C' : prebicat_data}
         (F : laxfunctor_data C C')
  : laxfunctor_ob_mor_cell _ _
  := pr1 F.

Definition laxfunctor_id {C C' : prebicat_data} (F : laxfunctor_data C C') (a : C)
  : #F (identity a) ==> identity _
  := pr1 (pr2 F) a.

Definition laxfunctor_comp {C C' : prebicat_data} (F : laxfunctor_data C C')
           {a b c : C} (f : a --> b) (g : b --> c)
  : #F (f · g) ==> #F f · #F g
  := pr2 (pr2 F) a b c f g.


Section laxfunctor_laws.

Context {C C' : prebicat_data} (F : laxfunctor_data C C').

Definition laxfunctor_id2_law : UU
  := ∏ (a b : C) (f : a --> b), ##F (id2 f) = id2 _.

Definition laxfunctor_vcomp2_law : UU
  := ∏ (a b : C) (f g h: C⟦a, b⟧) (η : f ==> g) (φ : g ==> h),
     ##F (η • φ) = ##F η • ##F φ.

Definition laxfunctor_lunitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (lunitor f)
     =   laxfunctor_comp F (identity a) f
       • (laxfunctor_id _ _ ▹ #F f)
       • lunitor (#F f).

Definition laxfunctor_runitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (runitor f)
     =   laxfunctor_comp F f (identity b)
       • (#F f ◃ laxfunctor_id _ _)
       • runitor (#F f).

Definition laxfunctor_lassociator_law : UU
  := ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧) ,
       ##F (lassociator f g h)
       • (laxfunctor_comp F _ _)
       • ((laxfunctor_comp F _ _) ▹ #F _)
     =   laxfunctor_comp F _ _
       • (#F f ◃ laxfunctor_comp F _ _)
       • lassociator (#F f) (#F g) (#F h).

Definition laxfunctor_lwhisker_law : UU
  := ∏ (a b c : C) (f : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧) (η : g1 ==> g2),
       ##F (f ◃ η)
       • laxfunctor_comp F _ _
     =   laxfunctor_comp F _ _
       • (#F f ◃ ##F η).

Definition laxfunctor_rwhisker_law : UU
  := ∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g : C⟦b, c⟧) (η : f1 ==> f2),
       ##F (η ▹ g)
       • laxfunctor_comp F _ _
     =   laxfunctor_comp F _ _
       • (##F η ▹ #F g).

Definition laxfunctor_laws : UU
  :=   laxfunctor_id2_law
     × laxfunctor_vcomp2_law
     × laxfunctor_lunitor_law
     × laxfunctor_runitor_law
     × laxfunctor_lassociator_law
     × laxfunctor_lwhisker_law
     × laxfunctor_rwhisker_law.
End laxfunctor_laws.

Definition laxfunctor (C C' : prebicat_data)
  : UU
  := ∑ F : laxfunctor_data C C', laxfunctor_laws F.

Coercion laxfunctor_to_laxfunctor_data
         {C C' : prebicat_data}
         (F : laxfunctor C C')
  := pr1 F.

Section Projection.
  Context {C C' : prebicat_data}.
  Variable (F : laxfunctor C C').

  Definition laxfunctor_id2
    : ∏ (a b : C) (f : a --> b), ##F (id2 f) = id2 (#F f)
    := pr1(pr2 F).

  Definition laxfunctor_vcomp
    : ∏ (a b : C) (f g h: C⟦a, b⟧) (η : f ==> g) (φ : g ==> h),
      ##F (η • φ) = ##F η • ##F φ
    := pr1(pr2(pr2 F)).

  Definition laxfunctor_lunitor
    : ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (lunitor f)
     =   laxfunctor_comp F (identity a) f
       • (laxfunctor_id _ _ ▹ #F f)
       • lunitor (#F f)
    := pr1(pr2(pr2(pr2 F))).

  Definition laxfunctor_runitor
    : ∏ (a b : C) (f : C⟦a, b⟧),
       ##F (runitor f)
     =   laxfunctor_comp F f (identity b)
       • (#F f ◃ laxfunctor_id _ _)
       • runitor (#F f)
    := pr1(pr2(pr2(pr2(pr2 F)))).

  Definition laxfunctor_lassociator
    : ∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧) ,
       ##F (lassociator f g h)
       • (laxfunctor_comp F _ _)
       • ((laxfunctor_comp F _ _) ▹ #F _)
     =   laxfunctor_comp F _ _
       • (#F f ◃ laxfunctor_comp F _ _)
       • lassociator (#F f) (#F g) (#F h)
    := pr1(pr2(pr2(pr2(pr2(pr2 F))))).

  Definition laxfunctor_lwhisker
    : ∏ (a b c : C) (f : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧) (η : g1 ==> g2),
       ##F (f ◃ η)
       • laxfunctor_comp F _ _
     =   laxfunctor_comp F _ _
       • (#F f ◃ ##F η)
    := pr1(pr2(pr2(pr2(pr2(pr2(pr2 F)))))).

  Definition laxfunctor_rwhisker
    : ∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g : C⟦b, c⟧) (η : f1 ==> f2),
       ##F (η ▹ g)
       • laxfunctor_comp F _ _
     =   laxfunctor_comp F _ _
       • (##F η ▹ #F g)
    := pr2(pr2(pr2(pr2(pr2(pr2(pr2 F)))))).
End Projection.

Definition is_pseudofunctor
           {C C' : prebicat_data}
           (F : laxfunctor C C')
  : UU
  := (∏ (a : C), is_invertible_2cell (laxfunctor_id F a))
     ×
     (∏ {a b c : C} (f : a --> b) (g : b --> c), is_invertible_2cell (laxfunctor_comp F f g)).

Definition psfunctor
           (C C' : prebicat_data)
  := ∑ (F : laxfunctor C C'), is_pseudofunctor F.

Coercion pseudofunctor_to_laxfunctor
         {C C' : prebicat_data}
         (F : psfunctor C C')
  := pr1 F.

Module Notations.
  Notation "'##'" := (laxfunctor_on_cells).
End Notations.